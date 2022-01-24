----- MODULE fee -----

EXTENDS Naturals, Sequences, TLC

VARIABLES
    x,
    y,
    balances,
    channel_states,
    next_channel_ids,
    fee_supported_on_chain

Chains == { "chain_a", "chain_b" }

UserWallets == { "user_1", "user_2", "relayer_1", "relayer_2" }

Channels == { "channel_1", "channel_2", "channel_3", "channel_4" }

InitialBalances ==
    [ chain \in Chains |->
        [ wallet \in UserWallets |-> 1000 ] @@ [ fee_module |-> 0 ]
    ]

\* InitialChannelStates ==
\*     [ channel \in Channels |->
\*         [   chain |-> 0
\*         ,   counterparty_chain |-> 0
\*         ,   state |-> "uninitialized"
\*         ,   fee_supported |-> FALSE
\*         ]
\*     ]

EmptyRecord == [ a \in {} |-> "a" ]

InitialChannelStates ==
    [ c \in Chains |->
        EmptyRecord
    ]

FeeSupportedOnChain ==
    [ Chains -> { TRUE, FALSE } ]

UnchangedStates ==
    << balances, fee_supported_on_chain >>

CHAN_OPEN_INIT == "chan_open_init"

ChainIdStr(id) == "channel-" \o ToString(id)

AddEntry(record, key, value) ==
    key :> value @@ record

DoChanOpenInit(chain_id) ==
    /\ next_channel_ids' =
        [ next_channel_ids EXCEPT ![chain_id] = next_channel_ids[chain_id] + 1 ]
    /\ channel_states' =
        [ channel_states EXCEPT ![chain_id] =
            AddEntry(
                channel_states[chain_id],
                ChainIdStr(next_channel_ids[chain_id]),
                CHAN_OPEN_INIT
            )
        ]

Init ==
    /\ x = 0
    /\ y = 0
    /\ balances = InitialBalances
    /\ channel_states = InitialChannelStates
    /\ fee_supported_on_chain = FeeSupportedOnChain
    /\ next_channel_ids = [ c \in Chains |-> 1 ]

Next ==
    \/  /\ x < 10
        /\ x' = x + 1
        /\ UNCHANGED << y, channel_states, next_channel_ids >>
        /\ UNCHANGED UnchangedStates
    \/  /\ y < 10
        /\ y' = y + 1
        /\ UNCHANGED << x, channel_states, next_channel_ids >>
        /\ UNCHANGED UnchangedStates
    \/  /\  \E chain \in Chains:
            DoChanOpenInit(chain)
        /\ UNCHANGED << x, y >>
        /\ UNCHANGED UnchangedStates

NULL == ""

EntryEquals(record, key, value) ==
    /\ key \in DOMAIN record
    /\ record[key] = value

WantedState ==
    /\ x = 8
    /\ y = 6
    /\ EntryEquals(channel_states.chain_b, "channel-2", "chan_open_init")
    /\ EntryEquals(channel_states.chain_a, "channel-1", "chan_open_init")

Invariant ==
    ~WantedState

======
