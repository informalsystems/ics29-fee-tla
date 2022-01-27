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
  , relayed_packets
>>

Init ==
  /\  all_channel_states = Utils!EmptyRecord
  /\  connected_channels = {}
  /\  send_commitments = {}
  /\  ack_commitments = {}
  /\  relayed_packets = Utils!EmptyRecord

PacketKey(chain_id, channel_id, packet_id) ==
  << chain_id, channel_id, packet_id >>

SendPacket(chain_id, channel_id, packet) ==
      \* It is enough to being able to send packet when only one end
      \* of the channels is Open, while the other is still in TryOpen
  /\  Channel!ChannelIsOpen(chain_id, channel_id)
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
  /\  Channel!ChannelIsOpen(chain_id, channel_id)
  /\  Channel!HasChannel(chain_id, channel_id)
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

Next ==
  \/  SendAnyPacket(SendPacket)
  \/  ReceiveAnyPacket(ReceivePacket)

=====
