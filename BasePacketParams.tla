----- MODULE BasePacketParams -----

CONSTANTS
    AllUsers
  , AllSequences
  , BasePayloads
  , BaseAcks

VARIABLES
    send_commitments
  , ack_commitments
  , relayed_packets

=====
