----- MODULE BaseChannelParams -----

CONSTANTS
    Null
  , AllChainIds
  , InitChannelIds
  , OpenTryChannelIds
  , ChanInitState
  , ChanOpenState
  , ChanTryOpenState
  , BaseVersions
  , AllPackets
  , AllUsers

  \*  All acknowledgements that can be returned by the base IBC module
  , BaseAcks

VARIABLES
    all_channel_states
  , connected_channels
  , sent_packets
  , received_packets
  , acked_packets

=====
