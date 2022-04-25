----- MODULE FeeSupportedPacketConst -----

EXTENDS
  BasePacketConst,
  FeeSupportedChannelConst

CONSTANTS
  \* @type: Set(ADDRESS);
  Relayers,

  \* @type: Set(ADDRESS);
  RegularUsers,

  \* @type: Set(Int);
  AllFees,

  \* @type: ADDRESS;
  FeeModuleAccount,

  \* @type: ADDRESS;
  InvalidAddress,

  \* @type: Bool;
  RecordHistory,

  \* @type: Set(ADDRESS);
  AllModules,

  \* @type: Int;
  InitialBalancePerUser

=====
