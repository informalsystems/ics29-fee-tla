---- MODULE ChannelWithFee -----

CONSTANT
  Null,
  AllChainIds,
  AllChannelIds,
  ChanInitState,
  ChanOpenState,
  ChanTryOpenState

VARIABLES
  all_channel_states,
  init_channel_ids

LOCAL BaseChannel == INSTANCE BaseChannel

Init == BaseChannel!Init

Next == BaseChannel!Next

Unchanged == BaseChannel!Unchanged

HasChannel(chain_id, channel_id) ==
  BaseChannel!HasChannel(chain_id, channel_id)

TotalChannels(chain_id) ==
  BaseChannel!TotalChannels(chain_id)

ChannelStateEquals(chain_id, channel_id, counterparty_chain_id, handshake_state) ==
  BaseChannel!ChannelStateEquals(chain_id, channel_id, counterparty_chain_id, handshake_state)

=====
