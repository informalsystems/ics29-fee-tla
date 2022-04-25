----- MODULE BasePacketVars -----

EXTENDS
  Types,
  BaseChannelVars

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
