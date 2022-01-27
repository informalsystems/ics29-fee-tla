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
  , AllPacketIds
  , AllUsers
  , BaseSendPayloads

VARIABLES
    all_channel_states
  , connected_channels
  , send_commitments
  , ack_commitments
  , relayed_packets

=====
