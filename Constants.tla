---- MODULE Constants ----

AllChainIds == {
    "chain-a"
  , "chain-b"
\*   , "chain-c"
}

AllUsers == {
  "user-1",
  "user-2",
  "relayer-1",
  "relayer-2"
}

AllModules == {
  "fee-middleware"
}

InitChannelIds == {
    "channel-1"
  , "channel-2"
  \* , "channel-3"
  \* , "channel-4"
}

OpenTryChannelIds == {
    "channel-9"
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

Null == "NULL"

====
