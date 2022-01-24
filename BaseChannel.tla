----- MODULE BaseChannel -----

EXTENDS Naturals, Sequences, FiniteSets

CONSTANT
  Null,
  AllChainIds,
  InitChannelIds,
  OpenTryChannelIds,
  ChanInitState,
  ChanOpenState,
  ChanTryOpenState

LOCAL Utils == INSTANCE Utils

VARIABLES
  all_channel_states

LOCAL AllChannelIds == InitChannelIds \union OpenTryChannelIds

HandshakeState(chain_id, channel_id) ==
  all_channel_states[chain_id][channel_id].handshake_state

CounterpartyChainId(chain_id, channel_id) ==
  all_channel_states[chain_id][channel_id].counterparty_chain_id

HasChannel(chain_id, channel_id) ==
  Utils!HasKey(all_channel_states[chain_id], channel_id)

TotalChannels(chain_id) ==
  Cardinality(DOMAIN all_channel_states[chain_id])

Init ==
  /\  all_channel_states =
      [ c \in AllChainIds |->
        Utils!EmptyRecord
      ]

LOCAL DoChanOpenInit(chain_id, counterparty_chain_id, channel_id) ==
  LET
    channel_states == all_channel_states[chain_id]
  IN
    /\  ~Utils!HasKey(channel_states, channel_id)
    /\  LET
          channel_state == [
            handshake_state
              |-> ChanInitState,
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
    /\  counterparty_channel_states[counterparty_channel_id].handshake_state = ChanInitState
    /\  LET
          channel_state == [
            handshake_state
              |-> ChanTryOpenState,
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

LOCAL DoChannelOpenAck(chain_id, channel_id, counterparty_channel_id) ==
  LET
    channel_states == all_channel_states[chain_id]
    channel_state == channel_states[channel_id]
    counterparty_chain_id == channel_state.counterparty_chain_id
    counterparty_channel_states == all_channel_states[counterparty_chain_id]
    counterparty_channel_state == counterparty_channel_states[counterparty_channel_id]
  IN
    /\  channel_state.handshake_state = ChanInitState
    /\  counterparty_channel_state.handshake_state = ChanTryOpenState
    /\  counterparty_channel_state.counterparty_chain_id = chain_id
    /\  counterparty_channel_state.counterparty_channel_id = channel_id
    /\  LET
          new_channel_state == [
            handshake_state
              |-> ChanOpenState,
            counterparty_chain_id
              |-> counterparty_chain_id,
            counterparty_channel_id
              |-> counterparty_channel_id
          ]

          new_channel_states == Utils!UpdateEntry(
            channel_states,
            channel_id,
            new_channel_state
          )
        IN
          all_channel_states' = Utils!UpdateEntry(
            all_channel_states,
            chain_id,
            new_channel_states
          )

LOCAL DoChannelOpenConfirm(chain_id, channel_id) ==
  LET
    channel_states == all_channel_states[chain_id]
    channel_state == channel_states[channel_id]
    counterparty_chain_id == channel_state.counterparty_chain_id
    counterparty_channel_id == channel_state.counterparty_channel_id
    counterparty_channel_state == all_channel_states[counterparty_chain_id][counterparty_channel_id]
  IN
    /\  channel_state.handshake_state = ChanTryOpenState
    /\  counterparty_channel_state.handshake_state = ChanOpenState
    /\  counterparty_channel_state.counterparty_chain_id = chain_id
    /\  counterparty_channel_state.counterparty_channel_id = channel_id
    /\  LET
          new_channel_state == Utils!UpdateEntry(
            channel_state,
            "handshake_state",
            ChanOpenState
          )

          new_channel_states == Utils!UpdateEntry(
            channel_states,
            channel_id,
            new_channel_state
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
  \E channel_id \in InitChannelIds \ DOMAIN all_channel_states[chain_id]:
    DoChanOpenInit(chain_id, counterparty_chain_id, channel_id)

LOCAL DoAnyChanOpenTry ==
  \E chain_id \in AllChainIds:
  \E channel_id \in DOMAIN all_channel_states[chain_id]:
    /\  HandshakeState(chain_id, channel_id) = ChanInitState
    /\  \E counterparty_channel_id \in OpenTryChannelIds:
          DoChanOpenTry(
            CounterpartyChainId(chain_id, channel_id),
            chain_id,
            counterparty_channel_id,
            channel_id
          )

LOCAL DoAnyChanOpenAck ==
  \E chain_id \in AllChainIds:
  \E channel_id \in DOMAIN all_channel_states[chain_id]:
    /\  HasChannel(chain_id, channel_id)
    /\  HandshakeState(chain_id, channel_id) = ChanTryOpenState
    /\  LET
          channel_state == all_channel_states[chain_id][channel_id]
        IN
          DoChannelOpenAck(
            channel_state.counterparty_chain_id,
            channel_state.counterparty_channel_id,
            channel_id
          )

LOCAL DoAnyChanOpenConfirm ==
  \E chain_id \in AllChainIds:
  \E channel_id \in AllChannelIds:
    /\  HasChannel(chain_id, channel_id)
    /\  HandshakeState(chain_id, channel_id) = ChanOpenState
    /\  LET
          channel_state == all_channel_states[chain_id][channel_id]
        IN
          DoChannelOpenConfirm(
            channel_state.counterparty_chain_id,
            channel_state.counterparty_channel_id
          )

Next ==
  /\  \/  DoAnyChanOpenInit
      \/  DoAnyChanOpenTry
      \/  DoAnyChanOpenAck
      \/  DoAnyChanOpenConfirm


Unchanged == UNCHANGED << all_channel_states >>

ChainsConnected(chain_id, counterparty_chain_id, channel_id) ==
  LET
    channel_states == all_channel_states[chain_id]
    counterparty_channel_states == all_channel_states[counterparty_chain_id]
  IN
    /\  Utils!HasKey(channel_states, channel_id)
    /\  LET
          channel_state == channel_states[channel_id]
        IN
          /\  channel_state.handshake_state = ChanOpenState
          /\  channel_state.counterparty_chain_id = counterparty_chain_id
          /\  LET
                counterparty_channel_id == channel_state.counterparty_channel_id
                counterparty_channel_state == counterparty_channel_states[counterparty_channel_id]
              IN
                /\  counterparty_channel_state.handshake_state = ChanOpenState
                /\  counterparty_channel_state.counterparty_chain_id = chain_id
                /\  counterparty_channel_state.counterparty_channel_id = channel_id

=====
