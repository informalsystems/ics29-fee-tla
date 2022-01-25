----- MODULE Fee -----

EXTENDS
    Constants
  , Variables

LOCAL Utils == INSTANCE Utils

LOCAL Channel == INSTANCE ChannelWithFee

LOCAL Bank == INSTANCE Bank

Init ==
  /\ Bank!Init
  /\ Channel!Init

Next ==
  \/  /\  Channel!Next
      /\  Bank!Unchanged

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
