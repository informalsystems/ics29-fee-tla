----- MODULE BasePacket -----

EXTENDS
    Naturals
  , Sequences
  , FiniteSets
  , BasePacketParams

Utils == INSTANCE Utils

Channel == INSTANCE BaseChannel

Unchanged == UNCHANGED <<
    send_commitments
  , ack_commitments
  , committed_packets
  , timed_out_packets
  , committed_timed_out_packets
>>

\* @type: (CHAIN_ID, CHAIN_ID, CHANNEL_ID, CHANNEL_ID, Str, Str) => PACKET;
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

\* @type: PACKET_KEY -> PACKET;
InitSendCommitments ==
  LET
    \* @type: PACKET;
    packet == CreatePacket(NullChainId, NullChainId, NullChannelId, NullChannelId, "", "")
  IN
  Utils!EmptyRecord(packet)

\* @type: PACKET_KEY -> Seq(Str);
InitAckCommitments ==
  LET
    \* @type: Seq(Str);
    ack == <<>>
  IN
  Utils!EmptyRecord(ack)

Init ==
  /\  send_commitments = InitSendCommitments
  /\  ack_commitments = InitAckCommitments
  /\  committed_packets = {}
  /\  timed_out_packets = {}
  /\  committed_timed_out_packets = {}

\* @type: PACKET => PACKET_KEY;
SourcePacketKey(packet) ==
  << packet.source_chain_id, packet.source_channel_id, packet.sequence >>

\* @type: PACKET => PACKET_KEY;
DestinationPacketKey(packet) ==
  << packet.destination_chain_id, packet.destination_channel_id, packet.sequence >>

\* @type: (CHAIN_ID, CHANNEL_ID, Str, Str) => Bool;
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
      /\  UNCHANGED <<
            ack_commitments
          , committed_packets
          , timed_out_packets
          , committed_timed_out_packets
          >>

\* @type: (PACKET, Seq(Str)) => Bool;
ReceivePacket(packet, ack_acc) ==
  LET
    \* @type: CHAIN_ID;
    chain_id == packet.destination_chain_id

    \* @type: CHANNEL_ID;
    channel_id == packet.destination_channel_id

    \* @type: PACKET_KEY;
    packet_key == DestinationPacketKey(packet)

    \* @type: Set(PACKET_KEY);
    ack_keys == DOMAIN ack_commitments
  IN
  /\  Channel!ChannelIsOpen(chain_id, channel_id)
  /\  Channel!HasChannel(chain_id, channel_id)
  /\  ~(packet_key \in timed_out_packets)
  /\  ~(packet_key \in DOMAIN ack_commitments)
  /\  LET
        channel_state == Channel!ChannelState(chain_id, channel_id)
        counterparty_chain_id == channel_state.counterparty_chain_id
        counterparty_channel_id == channel_state.counterparty_channel_id
        counterparty_packet_key == SourcePacketKey(packet)
      IN
      /\  packet.source_chain_id = channel_state.counterparty_chain_id
      /\  packet.source_channel_id = channel_state.counterparty_channel_id
      /\  counterparty_packet_key \in DOMAIN send_commitments
      /\  send_commitments[counterparty_packet_key] = packet
      /\  \E ack \in BaseAcks:
            ack_commitments' = Utils!AddEntry(
              ack_commitments,
              packet_key,
              Utils!Concat(ack_acc, << ack >>)
            )
      /\  UNCHANGED <<
            send_commitments
          , committed_packets
          , timed_out_packets
          , committed_timed_out_packets
          >>

\* @type: PACKET => Bool;
TimeoutPacket(packet) ==
  LET
    packet_key == DestinationPacketKey(packet)
  IN
  /\  ~(packet_key \in DOMAIN ack_commitments)
  /\  ~(packet_key \in timed_out_packets)
  /\  timed_out_packets' = timed_out_packets \union { packet_key }
  /\  UNCHANGED <<
        send_commitments
      , committed_packets
      , ack_commitments
      , committed_timed_out_packets
      >>

\* @type: (CHAIN_ID, CHANNEL_ID, Str, Seq(Str)) => Bool;
ConfirmPacket(chain_id, channel_id, sequence, acks) ==
  /\  Channel!ChannelIsOpen(chain_id, channel_id)
  /\  Channel!HasChannel(chain_id, channel_id)
  /\  LET
        \* @type: PACKET_KEY;
        packet_key == << chain_id, channel_id, sequence >>

        channel_state == Channel!ChannelState(chain_id, channel_id)
        counterparty_chain_id == channel_state.counterparty_chain_id
        counterparty_channel_id == channel_state.counterparty_channel_id
        counterparty_channel_state == Channel!ChannelState(counterparty_chain_id, counterparty_channel_id)

        \* @type: PACKET_KEY;
        counterparty_packet_key == << counterparty_chain_id, counterparty_channel_id, sequence >>
      IN
      /\  packet_key \in DOMAIN send_commitments
      /\  counterparty_packet_key \in DOMAIN ack_commitments
      /\  ~(packet_key \in committed_packets)
      /\  Len(acks) = 1
      /\  acks[1] \in BaseAcks
      /\  committed_packets' = committed_packets \union { packet_key }
      /\  UNCHANGED <<
            send_commitments
          , ack_commitments
          , timed_out_packets
          , committed_timed_out_packets
          >>

\* @type: (CHAIN_ID, CHANNEL_ID, Str) => Bool;
ConfirmTimeoutPacket(chain_id, channel_id, sequence) ==
  /\  Channel!ChannelIsOpen(chain_id, channel_id)
  /\  Channel!HasChannel(chain_id, channel_id)
  /\  LET
        \* @type: PACKET_KEY;
        packet_key == << chain_id, channel_id, sequence >>
        channel_state == Channel!ChannelState(chain_id, channel_id)
        counterparty_chain_id == channel_state.counterparty_chain_id
        counterparty_channel_id == channel_state.counterparty_channel_id
        counterparty_channel_state == Channel!ChannelState(counterparty_chain_id, counterparty_channel_id)
        \* @type: PACKET_KEY;
        counterparty_packet_key == << counterparty_chain_id, counterparty_channel_id, sequence >>
      IN
      /\  ~(packet_key \in committed_packets)
      /\  ~(packet_key \in committed_timed_out_packets)
      /\  counterparty_packet_key \in timed_out_packets
      /\  committed_timed_out_packets' = committed_timed_out_packets \union { packet_key }
      /\  UNCHANGED <<
            send_commitments
          , ack_commitments
          , committed_packets
          , timed_out_packets
          >>

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

\* @type: ((PACKET, Seq(Str)) => Bool) => Bool;
ReceiveAnyPacket(receive_packet(_, _)) ==
  \E packet_key \in DOMAIN send_commitments:
  LET
    \* @type: PACKET;
    packet == send_commitments[packet_key]

    \* @type: Seq(Str);
    acks == << >>
  IN
  receive_packet(packet, acks)

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

TimeoutAnyPacket(timeout_packet(_)) ==
  \E packet_key \in DOMAIN send_commitments:
    LET
      packet == send_commitments[packet_key]
    IN
    timeout_packet(packet)

ConfirmAnyTimeoutPacket(confirm_timeout_packet(_, _, _)) ==
  \E packet_key \in DOMAIN send_commitments:
    LET
      packet == send_commitments[packet_key]
    IN
    confirm_timeout_packet(
      packet.source_chain_id
    , packet.source_channel_id
    , packet.sequence
  )

Next ==
  \/  SendAnyPacket(SendPacket)
  \/  ReceiveAnyPacket(ReceivePacket)
  \/  ConfirmAnyPacket(ConfirmPacket)
  \/  TimeoutAnyPacket(TimeoutPacket)
  \/  ConfirmAnyTimeoutPacket(ConfirmTimeoutPacket)

=====
