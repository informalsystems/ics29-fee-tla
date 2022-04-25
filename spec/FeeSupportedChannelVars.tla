---- MODULE FeeSupportedChannelVars -----

EXTENDS
  BaseChannelVars

VARIABLES
  \* @type: CHAIN_ID -> Bool;
  fees_supported_table,

  \* @type: << CHAIN_ID, CHANNEL_ID >> -> Bool;
  fees_enabled_table

====
