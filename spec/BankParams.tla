----- MODULE BankParams ----

EXTENDS Types

CONSTANTS
  \* @type: Set(CHAIN_ID);
  AllChainIds,

  \* @type: Set(ADDRESS);
  AllUsers,

  \* @type: Set(ADDRESS);
  AllModules,

  \* @type: Int;
  InitialBalancePerUser

VARIABLES
  \* @type: BANK_BALANCES;
  bank_balances,

  \* @type: Seq(TRANSFER);
  transfer_history

====
