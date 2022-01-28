----- MODULE FeeSupportedPacketParams -----

EXTENDS
    BasePacketParams
  , FeeSupportedChannelParams

CONSTANTS
    Relayers
  , AllFees
  , AllModules
  , InitialBalancePerUser
  , FeeModuleAccount

VARIABLES
    fee_escrows
  , bank_balances

=====
