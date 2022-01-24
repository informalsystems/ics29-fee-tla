----- MODULE Fee -----

EXTENDS Naturals, Sequences, FiniteSets,    TLC

LOCAL Utils == INSTANCE Utils

VARIABLES
    bank_balances,
    all_channel_states

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
    "channel-1", "channel-2"
}

ChanOpenInitState == "CHAN_OPEN_INIT"

InitialBalancePerUser == 1000

LOCAL Channel == INSTANCE ChannelWithFee

LOCAL Bank == INSTANCE Bank

Init ==
    /\ Bank!Init
    /\ Channel!Init

Next ==
    \/  /\ Channel!Next
        /\ Bank!Unchanged

NULL == ""

Invariant ==
    /\ Bank!Invariant

WantedState ==
    /\ Channel!HasChannel("chain-b", "channel-2")
    /\ Channel!HasChannel("chain-a", "channel-1")
    /\ Channel!ChannelStateEquals("chain-a", "channel-1", "chain-b", ChanOpenInitState)
    /\ Channel!ChannelStateEquals("chain-b", "channel-2", "chain-a", ChanOpenInitState)

WantedStateInvariant ==
    /\  ~WantedState

======
