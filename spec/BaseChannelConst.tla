----- MODULE BaseChannelConst -----

EXTENDS Types

CONSTANTS
  \* @type: Set(CHAIN_ID);
  AllChainIds,

  \* @type: Set(CHAIN_ID);
  InitChainIds,

  \* @type: Set(CHAIN_ID);
  CounterpartyChainIds,

  \* @type: CHAIN_ID;
  NullChainId,

  \* @type: Set(CHANNEL_ID);
  InitChannelIds,

  \* @type: Set(CHANNEL_ID);
  OpenTryChannelIds,

  \* @type: CHANNEL_ID;
  NullChannelId,

  \* @type: Str;
  ChanInitState,

  \* @type: Str;
  ChanOpenState,

  \* @type: Str;
  ChanTryOpenState,

  \* @type: Set(Str);
  BaseVersions

=====
