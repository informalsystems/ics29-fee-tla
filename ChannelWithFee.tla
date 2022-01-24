---- MODULE ChannelWithFee -----

CONSTANT
    AllChainIds,
    AllChannelIds,
    ChanOpenInitState

VARIABLES
    all_channel_states

LOCAL BaseChannel == INSTANCE BaseChannel

Init == BaseChannel!Init

Next == BaseChannel!Next

Unchanged == BaseChannel!Unchanged

HasChannel(chain_id, channel_id) ==
    BaseChannel!HasChannel(chain_id, channel_id)

ChannelStateEquals(chain_id, channel_id, counterparty_chain_id, handshake_state) ==
    BaseChannel!ChannelStateEquals(chain_id, channel_id, counterparty_chain_id, handshake_state)

=====
