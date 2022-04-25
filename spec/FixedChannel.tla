----- MODULE FixedChannel -----

EXTENDS
  Apalache,
  Types,
  BaseChannelVars,
  BaseChannelConst,
  FeeSupportedChannelVars,
  FeeSupportedChannelConst

Channel == INSTANCE FeeSupportedChannel

FeesSupported(chain_id) ==
  Channel!FeesSupported(chain_id)

FeesEnabled(chain_id, channel_id) ==
  Channel!FeesEnabled(chain_id, channel_id)

HasChannel(chain_id, channel_id) ==
  Channel!HasChannel(chain_id, channel_id)

ChannelsConnected(chain_id, channel_id, counterparty_chain_id, counterparty_channel_id) ==
  Channel!ChannelsConnected(chain_id, channel_id, counterparty_chain_id, counterparty_channel_id)

Unchanged == Channel!Unchanged
Invariant == Channel!Invariant

\* @type: << CHAIN_ID, CHANNEL_ID >> -> CHANNEL_STATE;
InitChannelStates == SetAsFun({
  <<  << "1_OF_CHAIN_ID", "1_OF_CHANNEL_ID" >>,
      [ handshake_state |-> "Open"
      , counterparty_chain_id |-> "9_OF_CHAIN_ID"
      , counterparty_channel_id |-> "9_OF_CHANNEL_ID"
      , versions |-> << "fee_v1", "ics20-1" >>
      ]
  >>,
  <<
      << "9_OF_CHAIN_ID", "9_OF_CHANNEL_ID" >>,
      [ handshake_state |-> "Open"
      , counterparty_chain_id |-> "1_OF_CHAIN_ID"
      , counterparty_channel_id |-> "1_OF_CHANNEL_ID"
      , versions |-> << "fee_v1", "ics20-1" >>
      ]
  >>
})

\* @type: Set(Set(<< CHAIN_ID, CHANNEL_ID >>));
InitConnectedChannels == {
  { << "1_OF_CHAIN_ID", "1_OF_CHANNEL_ID" >>,
    << "9_OF_CHAIN_ID", "9_OF_CHANNEL_ID" >>
  }
}

\* @type: CHAIN_ID -> Bool;
InitFeesSupportedTable == SetAsFun({
  << "1_OF_CHAIN_ID", TRUE >>,
  << "9_OF_CHAIN_ID", TRUE >>
})

\* @type: << CHAIN_ID, CHANNEL_ID >> -> Bool;
InitFeesEnabledTable == SetAsFun({
  <<  << "1_OF_CHAIN_ID", "1_OF_CHANNEL_ID" >>,
      TRUE
  >>,
  <<  << "9_OF_CHAIN_ID", "9_OF_CHANNEL_ID" >>,
      TRUE
  >>
})

Init ==
  /\ all_channel_states = InitChannelStates
  /\ connected_channels = InitConnectedChannels
  /\ fees_supported_table = InitFeesSupportedTable
  /\ fees_enabled_table = InitFeesEnabledTable

Next == Unchanged

=====
