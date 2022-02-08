----- MODULE Main -----

EXTENDS
    FiniteSets
  , Sequences
  , Naturals
  , MainParams

LOCAL Utils == INSTANCE Utils

LOCAL Channel == INSTANCE FeeSupportedChannel

LOCAL Packet == INSTANCE FeeSupportedPacket

LOCAL Bank == INSTANCE Bank

Init ==
  /\  Bank!Init
  /\  Channel!Init
  /\  Packet!Init

Next ==
  \/  /\  Channel!Next
      /\  Bank!Unchanged
      /\  Packet!Unchanged
  \/  /\  Packet!Next
      /\  Channel!Unchanged
  \* \/  /\  \E chain_id \in AllChainIds:
  \*         \E sender, receiver \in AllUsers:
  \*         \E fee \in AllFees:
  \*            Bank!Transfer(chain_id, sender, receiver, fee)
  \*     /\  Channel!Unchanged
  \*     /\  Packet!Unchanged

Invariant ==
  /\  Bank!Invariant
  /\  Channel!Invariant

\* Find a trace where there are a pair of connected channels
\* with fees enabled
FindConnectChannelsWithFeeEnabled ==
  /\  \E chain_a, chain_b \in AllChainIds:
      \E channel_id_a, channel_id_b \in AllChannelIds:
        /\  chain_a /= chain_b
        /\  Channel!FeesSupported(chain_a)
        /\  Channel!FeesSupported(chain_b)
        /\  Channel!FeesEnabled(chain_a, channel_id_a)
        /\  Channel!FeesEnabled(chain_b, channel_id_b)
        /\  Channel!ChannelsConnected(chain_a, channel_id_a, chain_b, channel_id_b)
  /\  \A key \in DOMAIN fees_enabled_table:
        fees_enabled_table[key] = TRUE
  \* /\  \E packet \in DOMAIN send_commitments: TRUE
  /\  Cardinality(DOMAIN ack_commitments) > 0
  /\  Cardinality(committed_packets) > 0
  \* /\  Cardinality(DOMAIN fee_escrows) > 0
  /\  Cardinality(completed_escrows) >= 4
  \* /\  \E chain_id \in AllChainIds:
  \*     \E user \in RegularUsers:
  \*       Bank!AccountBalance(chain_id, user) > 1000

WantedState ==
  FindConnectChannelsWithFeeEnabled

WantedStateInvariant ==
  /\  ~WantedState
  \* TRUE

======
