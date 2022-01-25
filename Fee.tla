----- MODULE Fee -----

EXTENDS
    Constants
  , Variables
  , Sequences

LOCAL Utils == INSTANCE Utils

LOCAL Channel == INSTANCE ChannelWithFee WITH
  MergeVersions <- \o

LOCAL Bank == INSTANCE Bank

Init ==
  /\ Bank!Init
  /\ Channel!Init

Next ==
  \/  /\  Channel!Next
      /\  Bank!Unchanged

Invariant ==
  /\  Bank!Invariant
  /\  Channel!Invariant

WantedState ==
  \E chain_a, chain_b \in AllChainIds:
  \E channel_id_a, channel_id_b \in AllChannelIds:
    \* /\  Channel!FeesSupported(chain_a)
    \* /\  Channel!FeesSupported(chain_b)
    /\  Channel!ChannelsConnected(chain_a, channel_id_a, chain_b, channel_id_b)
    \* /\  Channel!ChainsConnected(chain_a, chain_b, channel_id_a)

WantedStateInvariant ==
  /\  ~WantedState

======
