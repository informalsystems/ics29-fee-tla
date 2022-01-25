---- MODULE ChannelWithFee -----

EXTENDS Sequences

CONSTANT
  Null,
  AllChainIds,
  InitChannelIds,
  OpenTryChannelIds,
  ChanInitState,
  ChanOpenState,
  ChanTryOpenState,
  BaseVersions,
  VersionFees,
  MergeVersions(_, _)

VARIABLES
  all_channel_states,
  connected_channels,
  fees_supported_table,
  fees_enabled_table


LOCAL Utils == INSTANCE Utils
LOCAL BaseChannel == INSTANCE BaseChannel

Init ==
  /\  BaseChannel!Init
  /\  \E table \in [ AllChainIds -> BOOLEAN ]:
        fees_supported_table = table
  /\  fees_enabled_table = Utils!EmptyRecord

Unchanged ==
  /\  BaseChannel!Unchanged
  /\  UNCHANGED << fees_supported_table, fees_enabled_table >>

FeesSupported(chain_id) ==
  fees_supported_table[chain_id]

FeesEnabled(chain_id, channel_id) ==
  /\  FeesSupported(chain_id)
  /\  Utils!HasKey(fees_enabled_table, << chain_id, channel_id >>)
  /\  fees_enabled_table[chain_id, channel_id]

OnChanOpenInit(chain_id, counterparty_chain_id, channel_id, versions_acc) ==
  /\  ~Utils!HasKey(fees_enabled_table, << chain_id, channel_id >>)
  /\  IF FeesSupported(chain_id)
      THEN
        \E enabled \in BOOLEAN:
          LET
            new_versions_acc == IF enabled
              THEN MergeVersions(<<VersionFees>>, versions_acc)
              ELSE versions_acc
          IN
          /\  fees_enabled_table' = Utils!AddEntry(
                fees_enabled_table,
                << chain_id, channel_id >>,
                enabled
              )
          /\  BaseChannel!OnChanOpenInit(chain_id, counterparty_chain_id, channel_id, new_versions_acc)
      ELSE
        /\  UNCHANGED << fees_enabled_table >>
        /\  BaseChannel!OnChanOpenInit(chain_id, counterparty_chain_id, channel_id, versions_acc)

OnChanOpenTry(chain_id, counterparty_chain_id, channel_id, counterparty_channel_id, versions, versions_acc) ==
  IF FeesSupported(chain_id) /\ Head(versions) = VersionFees
  THEN
    /\  fees_enabled_table' = Utils!AddEntry(
          fees_enabled_table,
          << chain_id, channel_id >>,
          TRUE
        )
    /\  BaseChannel!OnChanOpenTry(
          chain_id,
          counterparty_chain_id,
          channel_id,
          counterparty_channel_id,
          Tail(versions),
          MergeVersions(versions_acc, <<VersionFees>>)
        )
  ELSE
    /\ UNCHANGED fees_enabled_table
    /\  BaseChannel!OnChanOpenTry(
          chain_id,
          counterparty_chain_id,
          channel_id,
          counterparty_channel_id,
          versions,
          versions_acc
        )

OnChanOpenAck(chain_id, channel_id, counterparty_channel_id, versions) ==
  IF FeesEnabled(chain_id, channel_id)
  THEN
    /\  Head(versions) = VersionFees
    /\  BaseChannel!OnChanOpenAck(
          chain_id,
          channel_id,
          counterparty_channel_id,
          Tail(versions)
        )
  ELSE
    BaseChannel!OnChanOpenAck(
      chain_id,
      channel_id,
      counterparty_channel_id,
      versions
    )

Next ==
  /\  UNCHANGED << fees_supported_table >>
  /\  \/  BaseChannel!AnyChanOpenInit(OnChanOpenInit)
      \/  BaseChannel!AnyChanOpenTry(OnChanOpenTry)
      \/  /\  UNCHANGED << fees_enabled_table >>
          /\  \/  BaseChannel!AnyChanOpenAck(OnChanOpenAck)
              \/  BaseChannel!AnyChanOpenConfirm(BaseChannel!OnChanOpenConfirm)

\* Next ==
\*   /\  UNCHANGED << fees_supported_table, fees_enabled_table >>
\*   /\  BaseChannel!Next

HasChannel(chain_id, channel_id) ==
  BaseChannel!HasChannel(chain_id, channel_id)

TotalChannels(chain_id) ==
  BaseChannel!TotalChannels(chain_id)

ChannelsConnected(chain_id, channel_id, counterparty_chain_id, counterparty_channel_id) ==
  BaseChannel!ChannelsConnected(chain_id, channel_id, counterparty_chain_id, counterparty_channel_id)

Invariant ==
  TRUE
\*   /\  \A chain_id_a, chain_id_b \in AllChainIds:
\*       \A channel_id_a, channel_id_b \in BaseChannel!AllChannelIds:
\*         FeesEnabled(chain_id_a, channel_id_a) => TRUE

=====
