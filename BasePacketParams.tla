----- MODULE BasePacketParams -----

EXTENDS BaseChannelParams

CONSTANTS
    AllUsers
  , AllSequences
  , BasePayloads
  , BaseAcks

VARIABLES
    send_commitments
  , ack_commitments
  , committed_packets
  , timed_out_packets
  , committed_timed_out_packets

=====
