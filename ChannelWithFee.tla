---- MODULE ChannelWithFee -----

EXTENDS Sequences

CONSTANT
  Null,
  AllChainIds,
  InitChannelIds,
  OpenTryChannelIds,
  ChanInitState,
  ChanOpenState,
  ChanTryOpenState,
  BaseVersions,
  VersionFees

VARIABLES
  all_channel_states,
  fees_supported_table,
  fees_enabled_table


LOCAL Utils == INSTANCE Utils
LOCAL BaseChannel == INSTANCE BaseChannel WITH
  MergeVersions <- \o

Init ==
  /\  BaseChannel!Init
  /\  \E table \in [ AllChainIds -> BOOLEAN ]:
        fees_supported_table = table
  /\  fees_enabled_table = [ chain_id \in AllChainIds |-> Utils!EmptyRecord ]

Unchanged ==
  /\  BaseChannel!Unchanged
  /\  UNCHANGED << fees_supported_table, fees_enabled_table >>

OnChanOpenInit(chain_id, counterparty_chain_id, channel_id, versions_acc) ==
  /\  ~Utils!HasKey(fees_enabled_table[chain_id], channel_id)
  /\  IF fees_supported_table[chain_id]
      THEN
        \E enabled \in BOOLEAN:
          LET
            new_fees_enabled == Utils!AddEntry(
              fees_enabled_table[chain_id],
              channel_id,
              enabled
            )

            new_versions_acc == IF enabled
              THEN Append(<<VersionFees>>, versions_acc)
              ELSE versions_acc
          IN
          /\  fees_enabled_table' = Utils!UpdateEntry(
                fees_enabled_table,
                chain_id,
                new_fees_enabled
              )
          /\  BaseChannel!OnChanOpenInit(chain_id, counterparty_chain_id, channel_id, new_versions_acc)
      ELSE
        /\  UNCHANGED << fees_enabled_table >>
        /\  BaseChannel!OnChanOpenInit(chain_id, counterparty_chain_id, channel_id, versions_acc)

Next ==
  /\  BaseChannel!Next
  /\  UNCHANGED << fees_supported_table, fees_enabled_table >>

HasChannel(chain_id, channel_id) ==
  BaseChannel!HasChannel(chain_id, channel_id)

TotalChannels(chain_id) ==
  BaseChannel!TotalChannels(chain_id)

ChainsConnected(chain_id, counterparty_chain_id, channel_id) ==
  BaseChannel!ChainsConnected(chain_id, counterparty_chain_id, channel_id)

=====
