----- MODULE Main -----

EXTENDS
    Sequences
  , MainParams

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

\* Find a trace where there are a pair of connected channels
\* with fees enabled
FindConnectChannelsWithFeeEnabled ==
  \E chain_a, chain_b \in AllChainIds:
  \E channel_id_a, channel_id_b \in AllChannelIds:
    /\  chain_a /= chain_b
    /\  Channel!FeesSupported(chain_a)
    /\  Channel!FeesSupported(chain_b)
    /\  Channel!FeesEnabled(chain_a, channel_id_a)
    /\  Channel!FeesEnabled(chain_b, channel_id_b)
    /\  Channel!ChannelsConnected(chain_a, channel_id_a, chain_b, channel_id_b)

WantedState ==
  FindConnectChannelsWithFeeEnabled

WantedStateInvariant ==
  /\  ~WantedState
  \* TRUE

======