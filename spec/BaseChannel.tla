----- MODULE BaseChannel -----

EXTENDS
  Naturals,
  Sequences,
  FiniteSets,
  BaseChannelVars,
  BaseChannelConst

Utils == INSTANCE Utils

\* @type: Set(CHANNEL_ID);
AllChannelIds == InitChannelIds \union OpenTryChannelIds

\* @type: (CHAIN_ID, CHANNEL_ID) => CHANNEL_STATE;
ChannelState(chain_id, channel_id) ==
  all_channel_states[chain_id, channel_id]

\* @type: (CHAIN_ID, CHANNEL_ID) => Str;
HandshakeState(chain_id, channel_id) ==
  ChannelState(chain_id, channel_id).handshake_state

CounterpartyChainId(chain_id, channel_id) ==
  ChannelState(chain_id, channel_id).counterparty_chain_id

\* @type: (CHAIN_ID, CHANNEL_ID) => Bool;
HasChannel(chain_id, channel_id) ==
  Utils!HasKey(all_channel_states, << chain_id, channel_id >>)

ChannelsConnected(
  chain_id,
  channel_id,
  counterparty_chain_id,
  counterparty_channel_id
) ==
    { << chain_id, channel_id >>, << counterparty_chain_id, counterparty_channel_id >> }
    \in
    connected_channels

\* @type: (CHAIN_ID, CHANNEL_ID) => Bool;
ChannelIsOpen(chain_id, channel_id) ==
  /\  HasChannel(chain_id, channel_id)
  /\  HandshakeState(chain_id, channel_id) = ChanOpenState

Init ==
  /\  all_channel_states = Utils!EmptyRecord([
        handshake_state
          |-> "",
        counterparty_chain_id
          |-> NullChainId,
        counterparty_channel_id
          |-> NullChannelId,
        versions
          |-> <<>>
      ])
  /\  connected_channels = {}

ValidVersions(versions) ==
  /\  Len(versions) = 1
  /\  Head(versions) \in BaseVersions

ChannelStatesUnchanged == UNCHANGED <<
    all_channel_states
  , connected_channels
>>

\* @type: (CHAIN_ID, CHAIN_ID, CHANNEL_ID, Seq(Str)) => Bool;
OnChanOpenInit(
  chain_id,
  counterparty_chain_id,
  channel_id,
  versions_acc
) ==
    /\  ~HasChannel(chain_id, channel_id)
    /\  UNCHANGED << connected_channels >>
    /\  \E version \in BaseVersions:
        LET
          \* @type: CHANNEL_STATE;
          channel_state == [
            handshake_state
              |-> ChanInitState,
            counterparty_chain_id
              |-> counterparty_chain_id,
            counterparty_channel_id
              |-> NullChannelId,
            versions
              |-> Utils!Concat(versions_acc, << version >>)
          ]
        IN
          all_channel_states' =
            Utils!AddEntry(
              all_channel_states,
              << chain_id, channel_id >>,
              channel_state
            )

\* @type: (CHAIN_ID, CHAIN_ID, CHANNEL_ID, CHANNEL_ID, Seq(Str), Seq(Str)) => Bool;
OnChanOpenTry(chain_id, counterparty_chain_id, channel_id, counterparty_channel_id, versions, versions_acc) ==
  /\  ValidVersions(versions)
  /\  ~HasChannel(chain_id, channel_id)
  /\  HasChannel(counterparty_chain_id, counterparty_channel_id)
  /\  ChannelState(counterparty_chain_id, counterparty_channel_id).handshake_state = ChanInitState
  /\  UNCHANGED connected_channels
  /\  LET
        channel_state == [
          handshake_state
            |-> ChanTryOpenState,
          counterparty_chain_id
            |-> counterparty_chain_id,
          counterparty_channel_id
            |-> counterparty_channel_id,
          versions
            |-> Utils!Concat(versions_acc, versions)
        ]
      IN
        all_channel_states' = Utils!AddEntry(
          all_channel_states,
          << chain_id, channel_id >>,
          channel_state
        )

\* @type: (CHAIN_ID, CHANNEL_ID, CHANNEL_ID, Seq(Str)) => Bool;
OnChanOpenAck(chain_id, channel_id, counterparty_channel_id, versions) ==
  LET
    channel_state == ChannelState(chain_id, channel_id)
    counterparty_chain_id == channel_state.counterparty_chain_id
    counterparty_channel_state == ChannelState(counterparty_chain_id, counterparty_channel_id)
  IN
    /\  ValidVersions(versions)
    /\  channel_state.handshake_state = ChanInitState
    /\  counterparty_channel_state.handshake_state = ChanTryOpenState
    /\  counterparty_channel_state.counterparty_chain_id = chain_id
    /\  counterparty_channel_state.counterparty_channel_id = channel_id
    /\  UNCHANGED connected_channels
    /\  LET
          new_channel_state == [
            channel_state EXCEPT
            !["handshake_state"] = ChanOpenState,
            !["counterparty_channel_id"] = counterparty_channel_id
          ]
        IN
          all_channel_states' = Utils!UpdateEntry(
            all_channel_states,
            << chain_id, channel_id >>,
            new_channel_state
          )

\* @type: (CHAIN_ID, CHANNEL_ID) => Bool;
OnChanOpenConfirm(chain_id, channel_id) ==
  LET
    channel_state == ChannelState(chain_id, channel_id)
    counterparty_chain_id == channel_state.counterparty_chain_id
    counterparty_channel_id == channel_state.counterparty_channel_id
    counterparty_channel_state == ChannelState(counterparty_chain_id, counterparty_channel_id)
  IN
    /\  channel_state.handshake_state = ChanTryOpenState
    /\  counterparty_channel_state.handshake_state = ChanOpenState
    /\  counterparty_channel_state.counterparty_chain_id = chain_id
    /\  counterparty_channel_state.counterparty_channel_id = channel_id
    /\  LET
          new_channel_state == [
            channel_state EXCEPT
            !["handshake_state"] = ChanOpenState
          ]
        IN
        /\  all_channel_states' = Utils!UpdateEntry(
              all_channel_states,
              << chain_id, channel_id >>,
              new_channel_state
            )

        /\  connected_channels' = connected_channels \union
              { { << chain_id, channel_id >>,
                  << counterparty_chain_id, counterparty_channel_id >>
                } }

AnyChanOpenInit(on_chan_open_init(_, _, _, _)) ==
  \E chain_id \in InitChainIds:
  \E counterparty_chain_id \in CounterpartyChainIds:
  \E channel_id \in InitChannelIds:
    on_chan_open_init(
      chain_id,
      counterparty_chain_id,
      channel_id,
      << >>
    )

AnyChanOpenTry(on_chan_open_try(_, _, _, _, _, _)) ==
  \E chain_id \in InitChainIds:
  \E channel_id \in InitChannelIds:
    /\  HasChannel(chain_id, channel_id)
    /\  HandshakeState(chain_id, channel_id) = ChanInitState
    /\  \E counterparty_channel_id \in OpenTryChannelIds:
          on_chan_open_try(
            CounterpartyChainId(chain_id, channel_id),
            chain_id,
            counterparty_channel_id,
            channel_id,
            ChannelState(chain_id, channel_id).versions,
            << >>
          )

AnyChanOpenAck(on_chan_open_ack(_, _, _, _)) ==
  \E chain_id \in AllChainIds:
  \E channel_id \in AllChannelIds:
    /\  HasChannel(chain_id, channel_id)
    /\  HandshakeState(chain_id, channel_id) = ChanTryOpenState
    /\  LET
          channel_state == ChannelState(chain_id, channel_id)
        IN
          on_chan_open_ack(
            channel_state.counterparty_chain_id,
            channel_state.counterparty_channel_id,
            channel_id,
            channel_state.versions
          )

AnyChanOpenConfirm(on_chan_open_confirm(_, _)) ==
  \E chain_id \in AllChainIds:
  \E channel_id \in AllChannelIds:
    /\  HasChannel(chain_id, channel_id)
    /\  HandshakeState(chain_id, channel_id) = ChanOpenState
    /\  LET
          channel_state == ChannelState(chain_id, channel_id)
          counterparty_chain_id == channel_state.counterparty_chain_id
          counterparty_channel_id == channel_state.counterparty_channel_id
        IN
        /\  HasChannel(counterparty_chain_id, counterparty_channel_id)
        /\  ChannelState(counterparty_chain_id, counterparty_channel_id).handshake_state = ChanTryOpenState
        /\  on_chan_open_confirm(
              counterparty_chain_id,
              counterparty_channel_id
            )

Next ==
  \/  AnyChanOpenInit(OnChanOpenInit)
  \/  AnyChanOpenTry(OnChanOpenTry)
  \/  AnyChanOpenAck(OnChanOpenAck)
  \/  AnyChanOpenConfirm(OnChanOpenConfirm)

Unchanged ==
  /\  ChannelStatesUnchanged

=====
