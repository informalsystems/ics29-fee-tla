----- MODULE BaseChannelVars -----

EXTENDS Types

VARIABLES
  \* @type: << CHAIN_ID, CHANNEL_ID >> -> CHANNEL_STATE;
  all_channel_states,

  \* @type: Set(Set(<< CHAIN_ID, CHANNEL_ID >>));
  connected_channels

=====
