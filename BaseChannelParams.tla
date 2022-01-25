----- MODULE BaseChannelParams -----

CONSTANTS
  Null,
  AllChainIds,
  InitChannelIds,
  OpenTryChannelIds,
  ChanInitState,
  ChanOpenState,
  ChanTryOpenState,
  BaseVersions,
  MergeVersions(_, _)

VARIABLES
  all_channel_states,
  connected_channels

=====
