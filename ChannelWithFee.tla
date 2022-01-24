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
  all_channel_states

LOCAL BaseChannel == INSTANCE BaseChannel

Init == BaseChannel!Init

Next == BaseChannel!Next

Unchanged == BaseChannel!Unchanged

HasChannel(chain_id, channel_id) ==
  BaseChannel!HasChannel(chain_id, channel_id)

TotalChannels(chain_id) ==
  BaseChannel!TotalChannels(chain_id)

ChainsConnected(chain_id, counterparty_chain_id, channel_id) ==
  BaseChannel!ChainsConnected(chain_id, counterparty_chain_id, channel_id)

=====
