----- MODULE FeeSupportedPacketVars -----

EXTENDS
  BasePacketVars,
  FeeSupportedChannelVars,
  BankVars

VARIABLES
  \* @type: PACKET_KEY -> ESCROW;
  fee_escrows,

  \* @type: Set(PACKET_KEY);
  completed_escrows,

  \* @type: Seq(RELAY);
  relay_history

=====
