---- MODULE MainParams ----

EXTENDS
  Types,
  Apalache,
  BankVars,
  BaseChannelVars,
  BasePacketVars,
  FeeSupportedChannelVars,
  FeeSupportedPacketVars

\* @typeAlias: CHAIN_ID = Str;
\* @typeAlias: CHANNEL_ID = Str;
\* @typeAlias: SEQUENCE = Str;
MainAliases == TRUE

\* @type: Set(CHAIN_ID);
InitChainIds ==
  { "chain-1"
  , "chain-2"
  \* , "3_OF_CHAIN_ID"
  }

\* @type: Set(CHAIN_ID);
CounterpartyChainIds ==
  { "chain-9"
  , "chain-8"
  \* , "7_OF_CHAIN_ID"
  }

\* @type: CHAIN_ID;
NullChainId == "chain-null"

AllChainIds == InitChainIds \union CounterpartyChainIds

\* @type: Set(CHANNEL_ID);
InitChannelIds ==
  { "channel-1"
  , "channel-2"
  \* , "channel-3"
}

\* @type: Set(CHANNEL_ID);
OpenTryChannelIds ==
  { "channel-9"
  , "channel-8"
  \* , "channel-7"
  }

\* @type: CHANNEL_ID;
NullChannelId == "channel-null"

\* @type: Set(ADDRESS);
RegularUsers ==
  { "user-1"
  \* , "user-2"
  }

\* @type: Set(ADDRESS);
Relayers ==
  { "relayer-1"
  \* , "relayer-2"
  }

\* @type: Set(ADDRESS);
AllUsers ==
  RegularUsers \union Relayers

\* @type: ADDRESS;
InvalidAddress ==
  "invalid-address"

\* @type: ADDRESS;
FeeModuleAccount ==
  "fee-module"

AllModules ==
  { FeeModuleAccount
  }

ChanInitState == "Init"
ChanOpenState == "Open"
ChanTryOpenState == "TryOpen"

BaseVersions == { "ics20-1" }
VersionFees == "fee_v1"

InitialBalancePerUser == 1000

AllChannelIds == InitChannelIds \union OpenTryChannelIds

\* @type: Set(SEQUENCE);
AllSequences ==
  { "sequence-1"
  , "sequence-2"
  , "sequence-3"
  , "sequence-4"
  , "sequence-5"
  }

\* @type: SEQUENCE;
NullSequence == "sequence-null"

BasePayloads ==
  { "token-transfer"
  }

BaseAcks ==
  { "ack-ok"
  }

AllFees ==
  { 0
  , 10
  , 20
\*   , 30
  }

RecordHistory == TRUE

====
