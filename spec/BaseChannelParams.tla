----- MODULE BaseChannelParams -----

EXTENDS Types

CONSTANTS
  \* @type: Set(CHAIN_ID);
  AllChainIds,

  \* @type: Set(CHANNEL_ID);
  InitChannelIds,

  \* @type: Set(CHANNEL_ID);
  OpenTryChannelIds,

  \* @type: Str;
  ChanInitState,

  \* @type: Str;
  ChanOpenState,

  \* @type: Str;
  ChanTryOpenState,

  \* @type: Set(Str);
  BaseVersions

VARIABLES
  \* @type: << CHAIN_ID, CHANNEL_ID >> -> CHANNEL_STATE;
  all_channel_states,

  \* @type: Set(Set(<< CHAIN_ID, CHANNEL_ID >>));
  connected_channels

=====
