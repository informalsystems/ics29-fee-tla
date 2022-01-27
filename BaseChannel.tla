----- MODULE BaseChannel -----

EXTENDS
    Naturals
  , Sequences
  , FiniteSets
  , BaseChannelParams

LOCAL Utils == INSTANCE Utils

AllChannelIds == InitChannelIds \union OpenTryChannelIds

HandshakeState(chain_id, channel_id) ==
  all_channel_states[chain_id, channel_id].handshake_state

CounterpartyChainId(chain_id, channel_id) ==
  all_channel_states[chain_id, channel_id].counterparty_chain_id

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

ChannelIsOpen(chain_id, channel_id) ==
  /\  HasChannel(chain_id, channel_id)
  /\  HandshakeState(chain_id, channel_id) = ChanOpenState

Init ==
  /\  all_channel_states = Utils!EmptyRecord
  /\  connected_channels = {}
  /\  send_commitments = {}
  /\  ack_commitments = {}
  /\  relayed_packets = Utils!EmptyRecord

ValidVersions(versions) ==
  /\  Len(versions) = 1
  /\  Head(versions) \in BaseVersions

ChannelStatesUnchanged == UNCHANGED <<
    all_channel_states
  , connected_channels
>>

PacketStatesUnchanged == UNCHANGED <<
    send_commitments
  , ack_commitments
  , relayed_packets
>>

OnChanOpenInit(chain_id, counterparty_chain_id, channel_id, versions_acc) ==
    /\  ~HasChannel(chain_id, channel_id)
    /\  UNCHANGED << connected_channels >>
    /\  PacketStatesUnchanged
    /\  \E version \in BaseVersions:
        LET
          channel_state == [
            handshake_state
              |-> ChanInitState,
            counterparty_chain_id
              |-> counterparty_chain_id,
            counterparty_channel_id
              |-> Null,
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

OnChanOpenTry(chain_id, counterparty_chain_id, channel_id, counterparty_channel_id, versions, versions_acc) ==
  /\  ValidVersions(versions)
  /\  ~HasChannel(chain_id, channel_id)
  /\  HasChannel(counterparty_chain_id, counterparty_channel_id)
  /\  all_channel_states[counterparty_chain_id, counterparty_channel_id].handshake_state = ChanInitState
  /\  UNCHANGED connected_channels
  /\  PacketStatesUnchanged
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

OnChanOpenAck(chain_id, channel_id, counterparty_channel_id, versions) ==
  LET
    channel_state == all_channel_states[chain_id, channel_id]
    counterparty_chain_id == channel_state.counterparty_chain_id
    counterparty_channel_state == all_channel_states[counterparty_chain_id, counterparty_channel_id]
  IN
    /\  ValidVersions(versions)
    /\  channel_state.handshake_state = ChanInitState
    /\  counterparty_channel_state.handshake_state = ChanTryOpenState
    /\  counterparty_channel_state.counterparty_chain_id = chain_id
    /\  counterparty_channel_state.counterparty_channel_id = channel_id
    /\  UNCHANGED connected_channels
    /\  PacketStatesUnchanged
    /\  LET
          new_channel_state == Utils!UpdateEntry2(
            channel_state,
            "handshake_state",
            ChanOpenState,
            "counterparty_channel_id",
            counterparty_channel_id
          )
        IN
          all_channel_states' = Utils!UpdateEntry(
            all_channel_states,
            << chain_id, channel_id >>,
            new_channel_state
          )

OnChanOpenConfirm(chain_id, channel_id) ==
  LET
    channel_state == all_channel_states[chain_id, channel_id]
    counterparty_chain_id == channel_state.counterparty_chain_id
    counterparty_channel_id == channel_state.counterparty_channel_id
    counterparty_channel_state == all_channel_states[counterparty_chain_id, counterparty_channel_id]
  IN
    /\  channel_state.handshake_state = ChanTryOpenState
    /\  counterparty_channel_state.handshake_state = ChanOpenState
    /\  counterparty_channel_state.counterparty_chain_id = chain_id
    /\  counterparty_channel_state.counterparty_channel_id = channel_id
    /\  PacketStatesUnchanged
    /\  LET
          new_channel_state == Utils!UpdateEntry(
            channel_state,
            "handshake_state",
            ChanOpenState
          )
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
  \E chain_id \in AllChainIds:
  \E channel_id \in InitChannelIds:
  \E counterparty_chain_id \in AllChainIds:
    on_chan_open_init(
      chain_id,
      counterparty_chain_id,
      channel_id,
      << >>
    )

AnyChanOpenTry(on_chan_open_try(_, _, _, _, _, _)) ==
  \E chain_id \in AllChainIds:
  \E channel_id \in AllChannelIds:
    /\  HasChannel(chain_id, channel_id)
    /\  HandshakeState(chain_id, channel_id) = ChanInitState
    /\  \E counterparty_channel_id \in OpenTryChannelIds:
          on_chan_open_try(
            CounterpartyChainId(chain_id, channel_id),
            chain_id,
            counterparty_channel_id,
            channel_id,
            all_channel_states[chain_id, channel_id].versions,
            << >>
          )

AnyChanOpenAck(on_chan_open_ack(_, _, _, _)) ==
  \E chain_id \in AllChainIds:
  \E channel_id \in AllChannelIds:
    /\  HasChannel(chain_id, channel_id)
    /\  HandshakeState(chain_id, channel_id) = ChanTryOpenState
    /\  LET
          channel_state == all_channel_states[chain_id, channel_id]
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
          channel_state == all_channel_states[chain_id, channel_id]
          counterparty_chain_id == channel_state.counterparty_chain_id
          counterparty_channel_id == channel_state.counterparty_channel_id
        IN
        /\  HasChannel(counterparty_chain_id, counterparty_channel_id)
        /\  all_channel_states[counterparty_chain_id, counterparty_channel_id].handshake_state = ChanTryOpenState
        /\  on_chan_open_confirm(
              counterparty_chain_id,
              counterparty_channel_id
            )

NextChannelAction ==
  \/  AnyChanOpenInit(OnChanOpenInit)
  \/  AnyChanOpenTry(OnChanOpenTry)
  \/  AnyChanOpenAck(OnChanOpenAck)
  \/  AnyChanOpenConfirm(OnChanOpenConfirm)

PacketKey(chain_id, channel_id, packet_id) ==
  << chain_id, channel_id, packet_id >>

SendPacket(chain_id, channel_id, packet) ==
      \* It is enough to being able to send packet when only one end
      \* of the channels is Open, while the other is still in TryOpen
  /\  ChannelIsOpen(chain_id, channel_id)
  /\  ChannelStatesUnchanged
  /\  LET packet_key == PacketKey(chain_id, channel_id, packet)
      IN
      \* The packet must be unsent even though if it is already sent,
      \* there is no effect on the update. However having the predicate
      \* false will back track the whole state transition when using
      \* SendPacket together with other atomic steps in fees middleware
      /\  ~(PacketKey(chain_id, channel_id, packet) \in send_commitments)
      /\  send_commitments' = { packet_key } \union send_commitments
      /\  UNCHANGED << ack_commitments, relayed_packets >>

ReceivePacket(chain_id, channel_id, packet) ==
  /\  ChannelIsOpen(chain_id, channel_id)
  /\  HasChannel(chain_id, channel_id)
  /\  LET
        channel_state == all_channel_states[chain_id, channel_id]
        counterparty_chain_id == channel_state.counterparty_chain_id
        counterparty_channel_id == channel_state.counterparty_channel_id
        packet_key == PacketKey(chain_id, channel_id, packet)
        counterparty_packet_key == PacketKey(counterparty_chain_id, counterparty_channel_id, packet)
      IN
      /\  counterparty_packet_key \in send_commitments
      /\  ~(packet_key \in ack_commitments)
      /\  ack_commitments' = { packet_key } \union ack_commitments
      /\  UNCHANGED << send_commitments, relayed_packets >>
      /\  ChannelStatesUnchanged

SendAnyPacket(send_packet(_, _, _)) ==
  \* Choose a channel in Open state, regardless of the counterparty state
  \E channel_entry \in DOMAIN all_channel_states:
    /\  all_channel_states[channel_entry].handshake_state = ChanOpenState
    /\  \E packet \in BaseSendPayloads:
          send_packet(channel_entry[1], channel_entry[2], packet)

ReceiveAnyPacket(receive_packet(_, _, _)) ==
  \E packet_key \in send_commitments:
  LET
    chain_id == packet_key[1]
    channel_id == packet_key[2]
    packet == packet_key[3]
    channel_state == all_channel_states[chain_id, channel_id]
  IN
  receive_packet(
    channel_state.counterparty_chain_id,
    channel_state.counterparty_channel_id,
    packet
  )

NextPacketAction ==
  \/  SendAnyPacket(SendPacket)
  \/  ReceiveAnyPacket(ReceivePacket)

Next ==
  \/  NextChannelAction
  \/  NextPacketAction

Unchanged ==
  /\  ChannelStatesUnchanged
  /\  PacketStatesUnchanged

=====
