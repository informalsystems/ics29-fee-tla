---- MODULE MainParams ----

EXTENDS
  Types,
  Apalache,
  BankVars,
  BaseChannelVars,
  BasePacketVars,
  FeeSupportedChannelVars,
  FeeSupportedPacketVars

\* @type: Set(CHAIN_ID);
InitChainIds ==
  { "1_OF_CHAIN_ID"
  \* , "2_OF_CHAIN_ID"
  \* , "3_OF_CHAIN_ID"
  }

\* @type: Set(CHAIN_ID);
CounterpartyChainIds ==
  { "9_OF_CHAIN_ID"
  \* , "8_OF_CHAIN_ID"
  \* , "7_OF_CHAIN_ID"
  }

\* @type: CHAIN_ID;
NullChainId == "null_OF_CHAIN_ID"

AllChainIds == InitChainIds \union CounterpartyChainIds

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

\* @type: Set(CHANNEL_ID);
InitChannelIds ==
  { "1_OF_CHANNEL_ID"
  \* , "2_OF_CHANNEL_ID"
  \* , "3_OF_CHANNEL_ID"
}

\* @type: Set(CHANNEL_ID);
OpenTryChannelIds ==
  { "9_OF_CHANNEL_ID"
  \* , "8_OF_CHANNEL_ID"
  \* , "7_OF_CHANNEL_ID"
  }

\* @type: CHANNEL_ID;
NullChannelId == "null_OF_CHANNEL_ID"

ChanInitState == "Init"
ChanOpenState == "Open"
ChanTryOpenState == "TryOpen"

BaseVersions == { "ics20-1" }
VersionFees == "fee_v1"

InitialBalancePerUser == 1000

AllChannelIds == InitChannelIds \union OpenTryChannelIds

\* @type: Set(SEQUENCE);
AllSequences ==
  { "1_OF_SEQUENCE"
  , "2_OF_SEQUENCE"
  , "3_OF_SEQUENCE"
  }

\* @type: SEQUENCE;
NullSequence == "null_OF_SEQUENCE"

BasePayloads ==
  { "token-transfer"
  }

BaseAcks ==
  { "ack-ok"
  }

AllFees ==
  { 0
  , 10
\*   , 20
\*   , 30
  }

RecordHistory == FALSE

====
