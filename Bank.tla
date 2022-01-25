----- MODULE Bank ----

EXTENDS Naturals, TLC, Functions, FiniteSets

CONSTANT
  AllChainIds,
  AllUsers,
  AllModules,
  InitialBalancePerUser

VARIABLES
  bank_balances

LOCAL Utils == INSTANCE Utils

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

Transfer(chain_id, sender_account, receiver_account, amount) ==
  LET
    chain_balances == bank_balances[chain_id]
    sender_balance == chain_balances[sender_account]
  IN
  /\  amount > 0
  /\  sender_balance >= amount
  /\  LET
        new_sender_balance == sender_balance - amount
        new_chain_balances_1 == Utils!UpdateEntry(
          chain_balances,
          sender_account,
          new_sender_balance
        )

        \* Get the receiver balance after updating the chain balance,
        \* in case if the sender and receiver are the same.
        receiver_balance == new_chain_balances_1[receiver_account]
        new_receiver_balance == receiver_balance + amount
        new_chain_balances_2 == Utils!UpdateEntry(
          new_chain_balances_1,
          receiver_account,
          new_receiver_balance
        )
      IN
      bank_balances' = Utils!UpdateEntry(
        bank_balances,
        chain_id,
        new_chain_balances_2
      )

AccountBalance(chain_id, account) ==
  bank_balances[chain_id][account]

=====
