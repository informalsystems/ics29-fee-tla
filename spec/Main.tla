----- MODULE Main -----

EXTENDS
    FiniteSets
  , Sequences
  , Naturals
  , MainParams

Utils == INSTANCE Utils

\* Channel == INSTANCE FeeSupportedChannel
Channel == INSTANCE FixedChannel

Packet == INSTANCE FeeSupportedPacket

Bank == INSTANCE Bank

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

Invariant ==
  /\  Bank!Invariant
  /\  Channel!Invariant

FeeModulesHasZeroBalance ==
  /\  \A chain_id \in AllChainIds:
        Bank!AccountBalance(chain_id, FeeModuleAccount) = 0

FeeModuleHasNegativeBalance ==
  /\  \E chain_id \in AllChainIds:
        Bank!AccountBalance(chain_id, FeeModuleAccount) < 0

AllRelayersNotPaid ==
  /\  \A chain_id \in AllChainIds:
      \A relayer \in Relayers:
        Bank!AccountBalance(chain_id, relayer) = 1000

HasConnectedChannelWithFee ==
  /\  \E chain_a, chain_b \in AllChainIds:
      \E channel_id_a, channel_id_b \in AllChannelIds:
        /\  chain_a /= chain_b
        /\  Channel!FeesSupported(chain_a)
        /\  Channel!FeesSupported(chain_b)
        /\  Channel!FeesEnabled(chain_a, channel_id_a)
        /\  Channel!FeesEnabled(chain_b, channel_id_b)
        /\  Channel!ChannelsConnected(chain_a, channel_id_a, chain_b, channel_id_b)

HasRelayedPackets ==
  /\  Cardinality(DOMAIN ack_commitments) > 0
  /\  Cardinality(committed_packets) > 0
  /\  Cardinality(committed_timed_out_packets) > 0

HasCompletedEscrows(count) ==
  /\  \E key \in DOMAIN fees_enabled_table:
        fees_enabled_table[key] = TRUE
  /\  Cardinality(DOMAIN fee_escrows) > 0
  /\  Cardinality(completed_escrows) > count

WantedState ==
  /\  HasCompletedEscrows(2)
  /\  FeeModulesHasZeroBalance

WantedStateInvariant ==
  /\  ~WantedState

======
