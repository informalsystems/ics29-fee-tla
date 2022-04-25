----- MODULE Bank ----

EXTENDS
    Naturals
  , Apalache
  , TLC
  , FiniteSets
  , SequencesExt
  , BankConst
  , BankVars

LOCAL Utils == INSTANCE Utils

LOCAL InitialUserBalances ==
  [ key \in (AllChainIds \X AllUsers) |->
    InitialBalancePerUser ]

LOCAL InitialModuleBalances ==
  [ key \in  (AllChainIds \X AllModules) |-> 0 ]

LOCAL InitialBankBalances ==
  InitialUserBalances @@ InitialModuleBalances

LOCAL TotalSupply == Cardinality(AllUsers) * InitialBalancePerUser

\* @type: (BANK_BALANCES, BALANCE_KEY) => Int;
account_balance(chain_balances, account) ==
  chain_balances[account]

\* @type: << CHAIN_ID, ADDRESS >> => CHAIN_ID;
account_chain_id(account) ==
    LET
      \* @type: CHAIN_ID;
      chain_id == account[1]
    IN
    chain_id

\* @type: (BANK_BALANCES, CHAIN_ID) => Int;
TotalBalanceOnChain(chain_balances, chain_id) ==
  LET
    \* @type: (Int, BALANCE_KEY) => Int;
    balance_folder(total, account) ==
      IF account_chain_id(account) = chain_id
      THEN
        total + account_balance(chain_balances, account)
      ELSE
        total
  IN
  ApaFoldSet(
    balance_folder
  , 0
  , DOMAIN chain_balances
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

\* @type: (BANK_BALANCES, TRANSFER) => Bool;
TransferInvariantStateless(balances, transfer) ==
  LET
    \* @type: Int;
    sender_balance == balances[transfer.chain_id, transfer.sender]
  IN
  /\  transfer.amount >= 0
  \* /\  sender_balance >= amount

\* @type: (BANK_BALANCES, TRANSFER) => BANK_BALANCES;
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

\* @type: Seq(TRANSFER) => Bool;
AddTransferHistory(transfers) ==
  IF RecordHistory
  THEN
    transfer_history' = Utils!Concat(transfer_history, transfers)
  ELSE
    UNCHANGED transfer_history

\* @type: TRANSFER => Bool;
AddSingleTransferHistory(transfer) ==
  LET
    \* @type: Seq(TRANSFER);
    transfers == << transfer >>
  IN
  AddTransferHistory(transfers)

\* @type: TRANSFER => Bool;
SingleTransfer(transfer) ==
  /\  TransferInvariantStateless(bank_balances, transfer)
  /\  bank_balances' = TransferStateless(bank_balances, transfer)
  /\  AddSingleTransferHistory(transfer)

\* @type: Seq(TRANSFER) => Bool;
MultiTransfer(transfers) ==
  /\  ApaFoldSeqLeft(
        LAMBDA invariant_satisfied, transfer:
          /\  invariant_satisfied
          /\  TransferInvariantStateless(
                bank_balances
              , transfer
              )
      , TRUE
      , transfers
      )
  /\  bank_balances' = ApaFoldSeqLeft(
        TransferStateless
      , bank_balances
      , transfers
      )
  /\  AddTransferHistory(transfers)

HasAccount(chain_id, account) ==
  << chain_id, account >> \in DOMAIN bank_balances

AccountBalance(chain_id, account) ==
  bank_balances[chain_id, account]

=====
