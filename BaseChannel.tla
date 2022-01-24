----- MODULE BaseChannel -----

EXTENDS Naturals, Sequences, FiniteSets

CONSTANT
  Null,
  AllChainIds,
  AllChannelIds,
  ChanOpenInitState,
  ChanOpenTryState

LOCAL Utils == INSTANCE Utils

VARIABLES
  all_channel_states,
  init_channel_ids

HandshakeState(chain_id, channel_id) ==
  all_channel_states[chain_id][channel_id].handshake_state

CounterpartyChainId(chain_id, channel_id) ==
  all_channel_states[chain_id][channel_id].counterparty_chain_id

HasChannel(chain_id, channel_id) ==
  Utils!HasKey(all_channel_states[chain_id], channel_id)

TotalChannels(chain_id) ==
  Cardinality(DOMAIN all_channel_states[chain_id])

LOCAL InitChannelIds ==
  LET
    all_channels_count == Cardinality(AllChannelIds)
  IN
  \E subset_channels \in SUBSET AllChannelIds:
    LET
      subset_channels_count == Cardinality(subset_channels)
    IN
      /\ subset_channels_count < all_channels_count
      /\ subset_channels_count > 0
      /\ init_channel_ids = subset_channels

Init ==
  /\  all_channel_states =
      [ c \in AllChainIds |->
        Utils!EmptyRecord
      ]
  /\ InitChannelIds

LOCAL DoChanOpenInit(chain_id, counterparty_chain_id) ==
  LET
    channel_states == all_channel_states[chain_id]
  IN
  \E channel_id \in init_channel_ids:
    /\  ~Utils!HasKey(channel_states, channel_id)
    /\  LET
          channel_state == [
            handshake_state
              |-> ChanOpenInitState,
            counterparty_chain_id
              |-> counterparty_chain_id,
            counterparty_channel_id
              |-> Null
          ]

          new_channel_states == Utils!AddEntry(
            channel_states,
            channel_id,
            channel_state
          )
        IN
          all_channel_states' =
            Utils!UpdateEntry(
              all_channel_states,
              chain_id,
              new_channel_states
            )

LOCAL DoChanOpenTry(chain_id, counterparty_chain_id, channel_id, counterparty_channel_id) ==
  LET
    channel_states == all_channel_states[chain_id]
    counterparty_channel_states == all_channel_states[counterparty_chain_id]
  IN
    /\  ~Utils!HasKey(channel_states, channel_id)
    /\  Utils!HasKey(counterparty_channel_states, counterparty_channel_id)
    /\  counterparty_channel_states[counterparty_channel_id].handshake_state = ChanOpenInitState
    /\  LET
          channel_state == [
            handshake_state
              |-> ChanOpenTryState,
            counterparty_chain_id
              |-> counterparty_chain_id,
            counterparty_channel_id
              |-> counterparty_channel_id
          ]

          new_channel_states == Utils!AddEntry(
            channel_states,
            channel_id,
            channel_state
          )
        IN
          all_channel_states' = Utils!UpdateEntry(
            all_channel_states,
            chain_id,
            new_channel_states
          )


LOCAL DoAnyChanOpenInit ==
  \E chain_id \in AllChainIds:
  \E counterparty_chain_id \in AllChainIds:
    DoChanOpenInit(chain_id, counterparty_chain_id)

LOCAL DoAnyChanOpenTry ==
  \E chain_id \in AllChainIds:
  \E channel_id \in AllChannelIds:
    /\  HasChannel(chain_id, channel_id)
    /\  HandshakeState(chain_id, channel_id) = ChanOpenInitState
    /\  \E counterparty_channel_id \in AllChannelIds:
          DoChanOpenTry(
            CounterpartyChainId(chain_id, channel_id),
            chain_id,
            counterparty_channel_id,
            channel_id
          )

Next ==
  /\  UNCHANGED init_channel_ids
  /\  \/  DoAnyChanOpenInit
      \/  DoAnyChanOpenTry

Unchanged == UNCHANGED << all_channel_states, init_channel_ids >>

ChannelStateEquals(chain_id, channel_id, counterparty_chain_id, handshake_state) ==
  LET
    channel_state == all_channel_states[chain_id][channel_id]
  IN
    /\  channel_state.counterparty_chain_id = counterparty_chain_id
    /\  channel_state.handshake_state = handshake_state

=====
