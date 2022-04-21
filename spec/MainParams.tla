---- MODULE MainParams ----

EXTENDS Types

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

AllChainIds ==
  { "chain-a"
\*   , "chain-b"
  \* , "chain-c"
  }

RegularUsers ==
  { "user-1"
\*   , "user-2"
  }

Relayers ==
  { "relayer-1"
\*   , "relayer-2"
  }

AllUsers ==
  RegularUsers \union Relayers

InvalidAddress ==
  "invalid-address"

FeeModuleAccount ==
  "fee-middleware"

AllModules ==
  { FeeModuleAccount
  }

InitChannelIds ==
  { "channel-1"
\*   , "channel-2"
  \* , "channel-3"
  \* , "channel-4"
}

OpenTryChannelIds ==
  { "channel-9"
\*   , "channel-8"
  \* , "channel-7"
  \* , "channel-6"
  }

ChanInitState == "Init"
ChanOpenState == "Open"
ChanTryOpenState == "TryOpen"

BaseVersions == { "ics20-1" }
VersionFees == "fee_v1"

InitialBalancePerUser == 1000

AllChannelIds == InitChannelIds \union OpenTryChannelIds

AllSequences ==
  { "sequence-1"
\*   , "sequence-2"
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
