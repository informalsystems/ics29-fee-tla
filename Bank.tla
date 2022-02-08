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
  /\  transfer_history = << >>

Unchanged == UNCHANGED << bank_balances, transfer_history >>

Invariant ==
  /\  \A chain_id \in AllChainIds:
        TotalBalanceOnChain(bank_balances, chain_id) = TotalSupply
  /\  \A account \in DOMAIN bank_balances:
        bank_balances[account] >= 0

CreateTransfer(chain_id, sender, receiver, amount) ==
  [ chain_id
      |-> chain_id
  , sender
      |-> sender
  , receiver
      |-> receiver
  , amount
      |-> amount
  ]

TransferInvariantStateless(balances, transfer) ==
  LET
    sender_balance == balances[transfer.chain_id, transfer.sender]
  IN
  /\  transfer.amount > 0
  \* /\  sender_balance >= amount

TransferStateless(balances, transfer) ==
  LET
    sender_balance == balances[transfer.chain_id, transfer.sender]
    new_sender_balance == sender_balance - transfer.amount
    temp_balances == Utils!UpdateEntry(
        balances,
        << transfer.chain_id, transfer.sender >>,
        new_sender_balance
    )

    \* Get the receiver balance after updating the chain balance,
    \* in case if the sender and receiver are the same.
    receiver_balance == temp_balances[transfer.chain_id, transfer.receiver]
    new_receiver_balance == receiver_balance + transfer.amount

    new_balances == Utils!UpdateEntry(
      temp_balances,
      << transfer.chain_id, transfer.receiver >>,
      new_receiver_balance
    )
  IN
  new_balances

SingleTransfer(transfer) ==
  /\  TransferInvariantStateless(bank_balances, transfer)
  /\  bank_balances' = TransferStateless(bank_balances, transfer)
  /\  transfer_history' = Utils!Concat(transfer_history, << transfer >>)

MultiTransfer(transfers) ==
  /\  FoldLeft(
        LAMBDA invariant_satisfied, transfer:
          /\  invariant_satisfied
          /\  TransferInvariantStateless(
                bank_balances
              , transfer
              )
      , TRUE
      , transfers
      )
  /\  bank_balances' = FoldLeft(
        LAMBDA balances, transfer:
          TransferStateless(
            balances
          , transfer
          )
      , bank_balances
      , transfers
      )
  /\  transfer_history' = Utils!Concat(transfer_history, transfers)

HasAccount(chain_id, account) ==
  << chain_id, account >> \in DOMAIN bank_balances

AccountBalance(chain_id, account) ==
  bank_balances[chain_id, account]

=====
