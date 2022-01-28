----- MODULE BasePacket -----

EXTENDS
    Naturals
  , Sequences
  , FiniteSets
  , BaseChannelParams
  , BasePacketParams

LOCAL Utils == INSTANCE Utils

LOCAL Channel == INSTANCE BaseChannel

Unchanged == UNCHANGED <<
    send_commitments
  , ack_commitments
  , committed_packets
>>

Init ==
  /\  send_commitments = Utils!EmptyRecord
  /\  ack_commitments = Utils!EmptyRecord
  /\  committed_packets = {}

CreatePacket(
  chain_id,
  counterparty_chain_id,
  source_channel_id,
  destination_channel_id,
  sequence,
  payload
) ==
  [ source_chain_id
      |-> chain_id
  , destination_chain_id
      |-> counterparty_chain_id
  , source_channel_id
      |-> source_channel_id
  , destination_channel_id
      |-> destination_channel_id
  , sequence
      |-> sequence
  , payload
      |-> payload
  ]

SourcePacketKey(packet) ==
  << packet.source_chain_id, packet.source_channel_id, packet.sequence >>

DestinationPacketKey(packet) ==
  << packet.destination_chain_id, packet.destination_channel_id, packet.sequence >>

SendPacket(chain_id, channel_id, sequence, payload) ==
      \* It is enough to being able to send packet when only one end
      \* of the channels is Open, while the other is still in TryOpen
  /\  Channel!ChannelIsOpen(chain_id, channel_id)
  /\  LET
        channel_state == Channel!ChannelState(chain_id, channel_id)
        packet == CreatePacket(
          chain_id,
          channel_state.counterparty_chain_id,
          channel_id,
          channel_state.counterparty_channel_id,
          sequence,
          payload
        )
        packet_key == SourcePacketKey(packet)
      IN
      \* The packet must be unsent even though if it is already sent,
      \* there is no effect on the update. However having the predicate
      \* false will back track the whole state transition when using
      \* SendPacket together with other atomic steps in fees middleware
      /\  ~(packet_key \in DOMAIN send_commitments)
      /\  send_commitments' = Utils!AddEntry(
            send_commitments,
            packet_key,
            packet
          )
      /\  UNCHANGED << ack_commitments, committed_packets >>

ReceivePacket(packet, ack_acc) ==
  LET
    chain_id == packet.destination_chain_id
    channel_id == packet.destination_channel_id
  IN
  /\  Channel!ChannelIsOpen(chain_id, channel_id)
  /\  Channel!HasChannel(chain_id, channel_id)
  /\  LET
        channel_state == Channel!ChannelState(chain_id, channel_id)
        counterparty_chain_id == channel_state.counterparty_chain_id
        counterparty_channel_id == channel_state.counterparty_channel_id
        packet_key == DestinationPacketKey(packet)
        counterparty_packet_key == SourcePacketKey(packet)
      IN
      /\  packet.source_chain_id = channel_state.counterparty_chain_id
      /\  packet.source_channel_id = channel_state.counterparty_channel_id
      /\  counterparty_packet_key \in DOMAIN send_commitments
      /\  send_commitments[counterparty_packet_key] = packet
      /\  ~(packet_key \in DOMAIN ack_commitments)
      /\  \E ack \in BaseAcks:
            ack_commitments' = Utils!AddEntry(
              ack_commitments,
              packet_key,
              Utils!Concat(ack_acc, << ack >>)
            )
      /\  UNCHANGED << send_commitments, committed_packets >>

ConfirmPacket(chain_id, channel_id, sequence, acks) ==
  /\  Channel!ChannelIsOpen(chain_id, channel_id)
  /\  Channel!HasChannel(chain_id, channel_id)
  /\  LET
        packet_key == << chain_id, channel_id, sequence >>
        channel_state == Channel!ChannelState(chain_id, channel_id)
        counterparty_chain_id == channel_state.counterparty_chain_id
        counterparty_channel_id == channel_state.counterparty_channel_id
        counterparty_channel_state == Channel!ChannelState(counterparty_chain_id, counterparty_channel_id)
        counterparty_packet_key == << counterparty_chain_id, counterparty_channel_id, sequence >>
      IN
      /\  packet_key \in DOMAIN send_commitments
      /\  counterparty_packet_key \in DOMAIN ack_commitments
      /\  ~(packet_key \in committed_packets)
      /\  ack_commitments[counterparty_packet_key] = acks
      /\  Len(acks) = 1
      /\  acks[1] \in BaseAcks
      /\  committed_packets' = committed_packets \union { packet_key }
      /\  UNCHANGED << send_commitments, ack_commitments >>

SendAnyPacket(send_packet(_, _, _, _)) ==
  \* Choose a channel in Open state, regardless of the counterparty state
  \E channel_key \in DOMAIN all_channel_states:
    LET
      chain_id == channel_key[1]
      channel_id == channel_key[2]
      channel_state == all_channel_states[channel_key]
    IN
    /\  channel_state.handshake_state = ChanOpenState
    /\  \E sequence \in AllSequences:
        \E payload \in BasePayloads:
          send_packet(chain_id, channel_id, sequence, payload)

ReceiveAnyPacket(receive_packet(_, _)) ==
  \E packet_key \in DOMAIN send_commitments:
  LET
    packet == send_commitments[packet_key]
  IN
  receive_packet(packet, << >>)

ConfirmAnyPacket(confirm_packet(_, _, _, _)) ==
  \E packet_key \in DOMAIN ack_commitments:
  LET
    acks == ack_commitments[packet_key]
    chain_id == packet_key[1]
    channel_id == packet_key[2]
    sequence == packet_key[3]
    channel_state == Channel!ChannelState(chain_id, channel_id)
  IN
  confirm_packet(
    channel_state.counterparty_chain_id,
    channel_state.counterparty_channel_id,
    sequence,
    acks
  )

Next ==
  \/  SendAnyPacket(SendPacket)
  \/  ReceiveAnyPacket(ReceivePacket)
  \/  ConfirmAnyPacket(ConfirmPacket)

=====
