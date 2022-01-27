---- MODULE MainParams ----

VARIABLES
    bank_balances
  , all_channel_states
  , fees_supported_table
  , fees_enabled_table
  , connected_channels
  , send_commitments
  , ack_commitments
  , relayed_packets

Null == "NULL"

AllChainIds ==
  { "chain-a"
  , "chain-b"
  \* , "chain-c"
  }

AllUsers ==
  { "user-1"
  , "user-2"
  , "relayer-1"
  , "relayer-2"
  }

AllModules ==
  { "fee-middleware"
  }

InitChannelIds ==
  { "channel-1"
  , "channel-2"
  \* , "channel-3"
  \* , "channel-4"
}

OpenTryChannelIds ==
  { "channel-9"
  , "channel-8"
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

AllPacketIds ==
  { "packet-1"
  , "packet-2"
  , "packet-3"
  }

BaseSendPayloads ==
  { "token-transfer"
  }

====
