---- MODULE MainParams ----

EXTENDS Apalache, Types

VARIABLES
  \* @type: BANK_BALANCES;
  bank_balances,

  \* @type: Seq(TRANSFER);
  transfer_history,

  \* @type: << CHAIN_ID, CHANNEL_ID >> -> CHANNEL_STATE;
  all_channel_states,

  \* @type: CHAIN_ID -> Bool;
  fees_supported_table,

  \* @type: << CHAIN_ID, CHANNEL_ID >> -> Bool;
  fees_enabled_table,

  \* @type: Set(Set(<< CHAIN_ID, CHANNEL_ID >>));
  connected_channels,

  \* @type: PACKET_KEY -> PACKET;
  send_commitments,

  \* @type: PACKET_KEY -> Seq(Str);
  ack_commitments,

  \* @type: Set(PACKET_KEY);
  committed_packets,

  \* @type: Set(PACKET_KEY);
  timed_out_packets,

  \* @type: PACKET_KEY -> ESCROW;
  fee_escrows,

  \* @type: Set(PACKET_KEY);
  completed_escrows,

  \* @type: Seq(RELAY);
  relay_history,

  \* @type: Set(PACKET_KEY);
  committed_timed_out_packets

\* @type: Set(CHAIN_ID);
InitChainIds ==
  { "1_OF_CHAIN_ID"
  \* , "chain-b"
  \* , "chain-c"
  }

\* @type: Set(CHAIN_ID);
CounterpartyChainIds ==
  { "9_OF_CHAIN_ID"
  \* , "chain-y"
  \* , "chain-z"
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
  \* , "channel-2"
  \* , "channel-3"
  \* , "channel-4"
}

\* @type: Set(CHANNEL_ID);
OpenTryChannelIds ==
  { "9_OF_CHANNEL_ID"
  \* , "channel-8"
  \* , "channel-7"
  \* , "channel-6"
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

AllSequences ==
  { "sequence-1"
  \* , "sequence-2"
\*   , "sequence-3"
  }

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

====
