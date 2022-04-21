----- MODULE FeeSupportedPacketParams -----

EXTENDS
    BasePacketParams
  , FeeSupportedChannelParams

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

VARIABLES
  \* @type: PACKET_KEY -> ESCROW;
  fee_escrows,

  \* @type: Set(PACKET_KEY);
  completed_escrows,

  \* @type: BANK_BALANCES;
  bank_balances,

  \* @type: Seq(TRANSFER);
  transfer_history,

  \* @type: Seq(RELAY);
  relay_history

=====
