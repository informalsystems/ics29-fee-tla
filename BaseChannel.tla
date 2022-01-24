----- MODULE BaseChannel -----

EXTENDS Naturals, Sequences, FiniteSets

CONSTANT
  Null,
  AllChainIds,
  AllChannelIds,
  ChanInitState,
  ChanOpenState,
  ChanTryOpenState

LOCAL Utils == INSTANCE Utils

VARIABLES
  all_channel_states,
  init_channel_ids

HandshakeState(chain_id, channel_id) ==
  all_channel_states[chain_id][channel_id].handshake_state

CounterpartyChainId(chain_id, channel_id) ==
  all_channel_states[chain_id][channel_id].counterparty_chain_id

HasChannel(chain_id, channel_id) ==
  Utils!HasKey(all_channel_states[chain_id], channel_id)

TotalChannels(chain_id) ==
  Cardinality(DOMAIN all_channel_states[chain_id])

\* Choose a smaller subset of channel IDs from AllChannelIds
\* that can be used for ChanOpenInit. This is to ensure that
\* we can keep AllChannelIds small while also do not exhaust
\* all IDs for ChanOpenInit and have none left for ChanOpenTry.
LOCAL InitChannelIds ==
  LET
    all_channels_count == Cardinality(AllChannelIds)
  IN
  \E subset_channels \in SUBSET AllChannelIds:
    LET
      subset_channels_count == Cardinality(subset_channels)
    IN
      /\ subset_channels_count < all_channels_count
      /\ subset_channels_count > 0
      /\ init_channel_ids = subset_channels

Init ==
  /\  all_channel_states =
      [ c \in AllChainIds |->
        Utils!EmptyRecord
      ]
  /\ InitChannelIds

LOCAL DoChanOpenInit(chain_id, counterparty_chain_id) ==
  LET
    channel_states == all_channel_states[chain_id]
  IN
  \E channel_id \in init_channel_ids:
    /\  ~Utils!HasKey(channel_states, channel_id)
    /\  LET
          channel_state == [
            handshake_state
              |-> ChanInitState,
            counterparty_chain_id
              |-> counterparty_chain_id,
            counterparty_channel_id
              |-> Null
          ]

          new_channel_states == Utils!AddEntry(
            channel_states,
            channel_id,
            channel_state
          )
        IN
          all_channel_states' =
            Utils!UpdateEntry(
              all_channel_states,
              chain_id,
              new_channel_states
            )

LOCAL DoChanOpenTry(chain_id, counterparty_chain_id, channel_id, counterparty_channel_id) ==
  LET
    channel_states == all_channel_states[chain_id]
    counterparty_channel_states == all_channel_states[counterparty_chain_id]
  IN
    /\  counterparty_channel_states[counterparty_channel_id].handshake_state = ChanInitState
    /\  LET
          channel_state == [
            handshake_state
              |-> ChanTryOpenState,
            counterparty_chain_id
              |-> counterparty_chain_id,
            counterparty_channel_id
              |-> counterparty_channel_id
          ]

          new_channel_states == Utils!AddEntry(
            channel_states,
            channel_id,
            channel_state
          )
        IN
          all_channel_states' = Utils!UpdateEntry(
            all_channel_states,
            chain_id,
            new_channel_states
          )

LOCAL DoChannelOpenAck(chain_id, channel_id, counterparty_channel_id) ==
  LET
    channel_states == all_channel_states[chain_id]
    channel_state == channel_states[channel_id]
    counterparty_chain_id == channel_state.counterparty_chain_id
    counterparty_channel_states == all_channel_states[counterparty_chain_id]
    counterparty_channel_state == counterparty_channel_states[counterparty_channel_id]
  IN
    /\  channel_state.handshake_state = ChanInitState
    /\  counterparty_channel_state.handshake_state = ChanTryOpenState
    /\  counterparty_channel_state.counterparty_chain_id = chain_id
    /\  counterparty_channel_state.counterparty_channel_id = channel_id
    /\  LET
          new_channel_state == [
            handshake_state
              |-> ChanOpenState,
            counterparty_chain_id
              |-> counterparty_chain_id,
            counterparty_channel_id
              |-> counterparty_channel_id
          ]

          new_channel_states == Utils!UpdateEntry(
            channel_states,
            channel_id,
            new_channel_state
          )
        IN
          all_channel_states' = Utils!UpdateEntry(
            all_channel_states,
            chain_id,
            new_channel_states
          )

LOCAL DoChannelOpenConfirm(chain_id, channel_id) ==
  LET
    channel_states == all_channel_states[chain_id]
    channel_state == channel_states[channel_id]
    counterparty_chain_id == channel_state.counterparty_chain_id
    counterparty_channel_id == channel_state.counterparty_channel_id
    counterparty_channel_state == all_channel_states[counterparty_chain_id][counterparty_channel_id]
  IN
    /\  channel_state.handshake_state = ChanTryOpenState
    /\  counterparty_channel_state.handshake_state = ChanOpenState
    /\  counterparty_channel_state.counterparty_chain_id = chain_id
    /\  counterparty_channel_state.counterparty_channel_id = channel_id
    /\  LET
          new_channel_state == Utils!UpdateEntry(
            channel_state,
            "handshake_state",
            ChanOpenState
          )

          new_channel_states == Utils!UpdateEntry(
            channel_states,
            channel_id,
            new_channel_state
          )
        IN
          all_channel_states' = Utils!UpdateEntry(
            all_channel_states,
            chain_id,
            new_channel_states
          )

LOCAL DoAnyChanOpenInit ==
  \E chain_id \in AllChainIds:
  \E counterparty_chain_id \in AllChainIds:
    DoChanOpenInit(chain_id, counterparty_chain_id)

LOCAL DoAnyChanOpenTry ==
  \E chain_id \in AllChainIds:
  \E channel_id \in AllChannelIds:
    /\  HasChannel(chain_id, channel_id)
    /\  HandshakeState(chain_id, channel_id) = ChanInitState
    /\  \E counterparty_channel_id \in AllChannelIds:
          DoChanOpenTry(
            CounterpartyChainId(chain_id, channel_id),
            chain_id,
            counterparty_channel_id,
            channel_id
          )

LOCAL DoAnyChanOpenAck ==
  \E chain_id \in AllChainIds:
  \E channel_id \in AllChannelIds:
    /\  HasChannel(chain_id, channel_id)
    /\  HandshakeState(chain_id, channel_id) = ChanTryOpenState
    /\  LET
          channel_state == all_channel_states[chain_id][channel_id]
        IN
          DoChannelOpenAck(
            channel_state.counterparty_chain_id,
            channel_state.counterparty_channel_id,
            channel_id
          )

LOCAL DoAnyChanOpenConfirm ==
  \E chain_id \in AllChainIds:
  \E channel_id \in AllChannelIds:
    /\  HasChannel(chain_id, channel_id)
    /\  HandshakeState(chain_id, channel_id) = ChanOpenState
    /\  LET
          channel_state == all_channel_states[chain_id][channel_id]
        IN
          DoChannelOpenConfirm(
            channel_state.counterparty_chain_id,
            channel_state.counterparty_channel_id
          )

Next ==
  /\  UNCHANGED init_channel_ids
  /\  \/  DoAnyChanOpenInit
      \/  DoAnyChanOpenTry
      \/  DoAnyChanOpenAck
      \/  DoAnyChanOpenConfirm


Unchanged == UNCHANGED << all_channel_states, init_channel_ids >>

ChannelStateEquals(chain_id, channel_id, counterparty_chain_id, handshake_state) ==
  LET
    channel_state == all_channel_states[chain_id][channel_id]
  IN
    /\  channel_state.counterparty_chain_id = counterparty_chain_id
    /\  channel_state.handshake_state = handshake_state

=====
