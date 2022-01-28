----- MODULE Bank ----

EXTENDS
    Naturals
  , TLC
  , Functions
  , FiniteSets
  , BankParams

LOCAL Utils == INSTANCE Utils

LOCAL InitialUserBalances ==
  [ key \in (AllChainIds \X AllUsers) |->
    InitialBalancePerUser ]

LOCAL InitialModuleBalances ==
  [ key \in  (AllChainIds \X AllModules) |-> 0 ]

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
  /\  bank_balances = InitialBankBalances

Unchanged == UNCHANGED bank_balances

\* ChainInvariant(chain_balances) ==
\*   /\  TotalBalanceOnChain(chain_balances) = TotalSupply
\*   /\  \A account \in DOMAIN chain_balances:
\*       chain_balances[account] >= 0

Invariant ==
  /\  TRUE
  \* /\  \A chain_id \in AllChainIds:
  \*     ChainInvariant(bank_balances[chain_id])

Transfer(chain_id, sender_account, receiver_account, amount) ==
  LET
    sender_balance == bank_balances[chain_id, sender_account]
  IN
  \* /\  amount > 0
  \* /\  sender_balance >= amount
  /\  LET
        new_sender_balance == sender_balance - amount
        temp_balances == Utils!UpdateEntry(
          bank_balances,
          << chain_id, sender_account >>,
          new_sender_balance
        )

        \* Get the receiver balance after updating the chain balance,
        \* in case if the sender and receiver are the same.
        receiver_balance == temp_balances[chain_id, receiver_account]
        new_receiver_balance == receiver_balance + amount
      IN
      bank_balances' = Utils!UpdateEntry(
        temp_balances,
        << chain_id, receiver_account >>,
        new_receiver_balance
      )

AccountBalance(chain_id, account) ==
  bank_balances[chain_id, account]

=====
