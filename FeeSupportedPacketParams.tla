----- MODULE FeeSupportedPacketParams -----

EXTENDS
    BasePacketParams
  , FeeSupportedChannelParams

CONSTANTS
    Relayers
  , RegularUsers
  , AllFees
  , AllModules
  , InitialBalancePerUser
  , FeeModuleAccount

VARIABLES
    fee_escrows
  , completed_escrows
  , bank_balances

=====
