----- MODULE BankTest -----

EXTENDS
    FiniteSets
  , Sequences
  , Naturals

\* @typeAlias: CHAIN = Str;
\* @typeAlias: ADDRESS = Str;
\* @typeAlias: TRANSFER = [
\*    chain_id: CHAIN,
\*    sender: ADDRESS,
\*    receiver: ADDRESS,
\*    amount: Int
\* ];
\* @typeAlias: BALANCE_KEY = << CHAIN, ADDRESS >>;
\* @typeAlias: BANK_BALANCES = (BALANCE_KEY -> Int);

VARIABLES
  \* @type: Seq(TRANSFER);
  transfer_history,

  \* @type: BANK_BALANCES;
  bank_balances

AllChainIds ==
  { "chain-a"
  , "chain-b"
  }

AllUsers ==
  { "user-1"
  , "user-2"
  }

AllModules ==
  { "fee-middleware"
  }

InitialBalancePerUser == 1000

AllFees ==
  { 0
  , 10
  }

Bank == INSTANCE Bank

Init ==
  /\  Bank!Init

Next ==
  \/  /\  \E chain_id \in AllChainIds:
          \E sender, receiver \in AllUsers:
          \E fee \in AllFees:
             Bank!SingleTransfer(Bank!CreateTransfer(chain_id, sender, receiver, fee))

Invariant ==
  /\  Bank!Invariant

WantedState ==
  /\  \E chain_id \in AllChainIds:
      \E user \in AllUsers:
        Bank!AccountBalance(chain_id, user) > 1000

WantedStateInvariant ==
  /\  ~WantedState

=====
