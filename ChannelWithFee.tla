---- MODULE ChannelWithFee -----

CONSTANT
  Null,
  AllChainIds,
  InitChannelIds,
  OpenTryChannelIds,
  ChanInitState,
  ChanOpenState,
  ChanTryOpenState

VARIABLES
  all_channel_states,
  fees_supported_table,
  fees_enabled_table

LOCAL Utils == INSTANCE Utils
LOCAL BaseChannel == INSTANCE BaseChannel

Init ==
  /\  BaseChannel!Init
  /\  \E table \in [ AllChainIds -> { TRUE, FALSE } ]:
        fees_supported_table = table
  /\  fees_enabled_table = [ chain_id \in AllChainIds |-> Utils!EmptyRecord ]

Unchanged ==
  /\  BaseChannel!Unchanged
  /\  UNCHANGED << fees_supported_table, fees_enabled_table >>

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
