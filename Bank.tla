----- MODULE Bank ----

EXTENDS Naturals, TLC, Functions, FiniteSets

CONSTANT
    AllChainIds,
    AllUsers,
    AllModules,
    InitialBalancePerUser

VARIABLES
    bank_balances

LOCAL InitialUserBalances ==
    [ user \in AllUsers |-> InitialBalancePerUser ]

LOCAL InitialModuleBalances ==
    [ module \in AllModules |-> 0 ]

LOCAL InitialBankBalances ==
    InitialUserBalances @@ InitialModuleBalances

LOCAL TotalSupply == Cardinality(AllUsers) * InitialBalancePerUser

LOCAL TotalBalanceOnChain(chain_balances) ==
    FoldFunction(
        +,
        0,
        chain_balances
    )

Init ==
    /\  bank_balances =
            [ chain_id \in AllChainIds |->
                InitialBankBalances ]

Unchanged == UNCHANGED bank_balances

ChainInvariant(chain_balances) ==
    /\  TotalBalanceOnChain(chain_balances) = TotalSupply
    /\  \A account \in DOMAIN chain_balances:
            chain_balances[account] >= 0

Invariant ==
    /\  \A chain_id \in AllChainIds:
            ChainInvariant(bank_balances[chain_id])


=====
