----- MODULE BasePacketParams -----

EXTENDS BaseChannelParams, Types

CONSTANTS
  \* @type: Set(ADDRESS);
  AllUsers,

  \* @type: Set(Str);
  AllSequences,

  \* @type: Set(Str);
  BasePayloads,

  \* @type: Set(Str);
  BaseAcks

VARIABLES
  \* @type: PACKET_KEY -> PACKET;
  send_commitments,

  \* @type: PACKET_KEY -> Seq(Str);
  ack_commitments,

  \* @type: Set(PACKET_KEY);
  committed_packets,

  \* @type: Set(PACKET_KEY);
  timed_out_packets,

  \* @type: Set(PACKET_KEY);
  committed_timed_out_packets

=====
