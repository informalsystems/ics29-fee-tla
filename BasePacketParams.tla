----- MODULE BasePacketParams -----

CONSTANTS
    AllUsers
  , AllSequences
  , BasePayloads
  , BaseAcks

VARIABLES
    send_commitments
  , ack_commitments
  , committed_packets

=====
