----- MODULE Fee -----

EXTENDS Naturals, Sequences, FiniteSets,  TLC

LOCAL Utils == INSTANCE Utils

VARIABLES
  bank_balances,
  all_channel_states,
  fees_supported_table,
  fees_enabled_table

AllChainIds == {
    "chain-a"
  , "chain-b"
  , "chain-c"
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

InitialBalancePerUser == 1000

AllChannelIds == InitChannelIds \union OpenTryChannelIds

Null == "NULL"

LOCAL Channel == INSTANCE ChannelWithFee

LOCAL Bank == INSTANCE Bank

Init ==
  /\ Bank!Init
  /\ Channel!Init

Next ==
  \/  /\  Channel!Next
      /\  Bank!Unchanged

NULL == ""

Invariant ==
  /\ Bank!Invariant

WantedState ==
  /\  \E channel_id \in AllChannelIds:
        Channel!ChainsConnected("chain-a", "chain-b", channel_id)
  \* /\  \E channel_id \in AllChannelIds:
  \*       Channel!ChainsConnected("chain-b", "chain-c", channel_id)

WantedStateInvariant ==
  /\  ~WantedState

======
