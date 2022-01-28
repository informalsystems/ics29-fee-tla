----- MODULE Bank ----

EXTENDS
    Naturals
  , TLC
  \* , Functions
  , FiniteSets
  , SequencesExt
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

LOCAL TotalBalanceOnChain(chain_balances, chain_id) ==
  FoldLeft(
    LAMBDA total, account:
      IF account[1] = chain_id
      THEN
        total + chain_balances[account]
      ELSE
        total
  , 0
  , SetToSeq(DOMAIN chain_balances)
  )

Init ==
  /\  bank_balances = InitialBankBalances

Unchanged == UNCHANGED bank_balances

Invariant ==
  /\  \A chain_id \in AllChainIds:
        TotalBalanceOnChain(bank_balances, chain_id) = TotalSupply
  /\  \A account \in DOMAIN bank_balances:
        bank_balances[account] >= 0

Transfer(chain_id, sender_account, receiver_account, amount) ==
  LET
    sender_balance == bank_balances[chain_id, sender_account]
  IN
  /\  amount > 0
  /\  sender_balance >= amount
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

HasAccount(chain_id, account) ==
  << chain_id, account >> \in bank_balances

AccountBalance(chain_id, account) ==
  bank_balances[chain_id, account]

=====
