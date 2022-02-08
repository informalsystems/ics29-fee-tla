---- MODULE MainParams ----

VARIABLES
    bank_balances
  , transfer_history
  , all_channel_states
  , fees_supported_table
  , fees_enabled_table
  , connected_channels
  , send_commitments
  , ack_commitments
  , committed_packets
  , fee_escrows
  , completed_escrows
  , relay_history

Null == "NULL"

AllChainIds ==
  { "chain-a"
  , "chain-b"
  \* , "chain-c"
  }

RegularUsers ==
  { "user-1"
  , "user-2"
  }

Relayers ==
  { "relayer-1"
  , "relayer-2"
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
  \* , "channel-2"
  \* , "channel-3"
  \* , "channel-4"
}

OpenTryChannelIds ==
  { "channel-9"
  \* , "channel-8"
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
  , "sequence-2"
  , "sequence-3"
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
  , 20
  , 30
  }

====
