----- MODULE BankParams ----

CONSTANTS
  \* @type: Set(CHAIN);
  AllChainIds,

  \* @type: Set(ADDRESS);
  AllUsers,

  \* @type: Set(ADDRESS);
  AllModules,

  \* @type: Int;
  InitialBalancePerUser

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
Aliases == TRUE

VARIABLES
  \* @type: BANK_BALANCES;
  bank_balances,

  \* @type: Seq(TRANSFER);
  transfer_history

====
