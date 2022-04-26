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
  <<  << "chain-1", "channel-1" >>,
      [ handshake_state |-> "Open"
      , counterparty_chain_id |-> "chain-9"
      , counterparty_channel_id |-> "channel-9"
      , versions |-> << "fee_v1", "ics20-1" >>
      ]
  >>,
  <<
      << "chain-9", "channel-9" >>,
      [ handshake_state |-> "Open"
      , counterparty_chain_id |-> "chain-1"
      , counterparty_channel_id |-> "channel-1"
      , versions |-> << "fee_v1", "ics20-1" >>
      ]
  >>,
  <<  << "chain-2", "channel-2" >>,
      [ handshake_state |-> "Open"
      , counterparty_chain_id |-> "chain-8"
      , counterparty_channel_id |-> "channel-8"
      , versions |-> << "fee_v1", "ics20-1" >>
      ]
  >>,
  <<
      << "chain-8", "channel-8" >>,
      [ handshake_state |-> "Open"
      , counterparty_chain_id |-> "chain-2"
      , counterparty_channel_id |-> "channel-2"
      , versions |-> << "fee_v1", "ics20-1" >>
      ]
  >>
})

\* @type: Set(Set(<< CHAIN_ID, CHANNEL_ID >>));
InitConnectedChannels == {
  { << "chain-1", "channel-1" >>,
    << "chain-9", "channel-9" >>
  },
  { << "chain-2", "channel-2" >>,
    << "chain-8", "channel-8" >>
  }
}

\* @type: CHAIN_ID -> Bool;
InitFeesSupportedTable == SetAsFun({
  << "chain-1", TRUE >>,
  << "chain-9", TRUE >>,
  << "chain-2", TRUE >>,
  << "chain-8", TRUE >>
})

\* @type: << CHAIN_ID, CHANNEL_ID >> -> Bool;
InitFeesEnabledTable == SetAsFun({
  <<  << "chain-1", "channel-1" >>,
      TRUE
  >>,
  <<  << "chain-9", "channel-9" >>,
      TRUE
  >>,
  <<  << "chain-2", "channel-2" >>,
      TRUE
  >>,
  <<  << "chain-8", "channel-8" >>,
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
