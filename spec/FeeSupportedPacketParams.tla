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
  , InvalidAddress

VARIABLES
    fee_escrows
  , completed_escrows
  , bank_balances
  , transfer_history
  , relay_history

=====
