----- MODULE BankConst ----

EXTENDS Types

CONSTANTS
  \* @type: Set(CHAIN_ID);
  AllChainIds,

  \* @type: Set(ADDRESS);
  AllUsers,

  \* @type: Set(ADDRESS);
  AllModules,

  \* @type: Int;
  InitialBalancePerUser,

  \* @type: Bool;
  RecordHistory

====
