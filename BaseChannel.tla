----- MODULE BaseChannel -----

CONSTANT
    AllChainIds,
    AllChannelIds,
    ChanOpenInitState

LOCAL Utils == INSTANCE Utils

VARIABLES
    all_channel_states

Init ==
    /\  all_channel_states =
            [ c \in AllChainIds |->
                Utils!EmptyRecord
            ]

LOCAL DoChanOpenInit(chain_id, counterparty_chain_id) ==
    LET
        channel_states == all_channel_states[chain_id]
    IN
    \E channel_id \in AllChannelIds:
        /\ ~Utils!HasKey(channel_states, channel_id)
        /\ all_channel_states' =
            [ all_channel_states EXCEPT ![chain_id] =
                Utils!AddEntry(
                    channel_states,
                    channel_id,
                    [   handshake_state |-> ChanOpenInitState,
                        counterparty_chain_id |-> counterparty_chain_id
                    ]
                )
            ]

LOCAL DoAnyChanOpenInit ==
    \E chain_id \in AllChainIds:
    \E counterparty_chain_id \in AllChainIds:
        DoChanOpenInit(chain_id, counterparty_chain_id)

Next ==
    \/  DoAnyChanOpenInit

Unchanged == UNCHANGED all_channel_states

HasChannel(chain_id, channel_id) ==
    Utils!HasKey(all_channel_states[chain_id], channel_id)

ChannelStateEquals(chain_id, channel_id, counterparty_chain_id, handshake_state) ==
    all_channel_states[chain_id][channel_id] =
        [   counterparty_chain_id |-> counterparty_chain_id,
            handshake_state |-> handshake_state
        ]

=====
