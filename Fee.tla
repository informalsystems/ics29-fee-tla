----- MODULE Fee -----

EXTENDS Naturals, Sequences, FiniteSets,  TLC

LOCAL Utils == INSTANCE Utils

VARIABLES
  bank_balances,
  all_channel_states,
  init_channel_ids

AllChainIds == { "chain-a", "chain-b" }

AllUsers == {
  "user-1",
  "user-2",
  "relayer-1",
  "relayer-2"
}

AllModules == {
  "fee-middleware"
}

AllChannelIds == {
  "channel-1", "channel-2", "channel-3"
}

ChanOpenInitState == "CHAN_OPEN_INIT"
ChanOpenTryState == "CHAN_OPEN_TRY"

InitialBalancePerUser == 1000

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
  /\  Channel!HasChannel("chain-b", "channel-2")
  /\  Channel!HasChannel("chain-a", "channel-1")
  /\  Channel!ChannelStateEquals("chain-a", "channel-1", "chain-b", ChanOpenInitState)
  /\  Channel!ChannelStateEquals("chain-b", "channel-2", "chain-a", ChanOpenTryState)

WantedStateInvariant ==
  /\  ~WantedState

======
