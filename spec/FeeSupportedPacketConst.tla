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

  \* @type: Set(ADDRESS);
  AllModules,

  \* @type: Int;
  InitialBalancePerUser,

  \* @type: ADDRESS;
  FeeModuleAccount,

  \* @type: ADDRESS;
  InvalidAddress

=====
