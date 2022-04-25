----- MODULE FeeSupportedPacket -----

EXTENDS
  Types,
  Naturals,
  Sequences,
  FeeSupportedPacketVars,
  FeeSupportedPacketConst

BasePacket == INSTANCE BasePacket

Channel == INSTANCE FeeSupportedChannel

Utils == INSTANCE Utils

Bank == INSTANCE Bank

\* @type: PACKET_KEY -> ESCROW;
InitFeeEscrows ==
  LET
    \* @type: ESCROW;
    escrow == [
      receive_fee |-> 0,
      ack_fee |-> 0,
      timeout_fee |-> 0,
      refund_address |-> InvalidAddress
    ]
  IN
  Utils!EmptyRecord(escrow)

Init ==
  /\  BasePacket!Init
  /\  fee_escrows = InitFeeEscrows
  /\  completed_escrows = {}
  /\  relay_history = << >>

Unchanged ==
  /\  BasePacket!Unchanged
  /\  UNCHANGED << fee_escrows, completed_escrows, relay_history >>

\* @type: (CHAIN_ID, CHANNEL_ID, SEQUENCE, ADDRESS, Int, Int, Int) => Bool;
PayPacketFee(
  chain_id
, channel_id
, sequence
, user
, receive_fee
, ack_fee
, timeout_fee
) ==
  /\  receive_fee >= 0
  /\  ack_fee >= 0
  /\  timeout_fee >= 0
  /\  ~(receive_fee = 0 /\ ack_fee = 0)
  /\  Bank!SingleTransfer(
        Bank!CreateTransfer(
          chain_id
        , user
        , FeeModuleAccount
        , receive_fee + ack_fee + timeout_fee
        )
      )
  /\  LET
        escrow_key == BasePacket!PacketKey(chain_id, channel_id, sequence)
      IN
      fee_escrows' = Utils!AddEntry(
        fee_escrows,
        escrow_key,
        [ receive_fee
            |-> receive_fee
        , ack_fee
            |-> ack_fee
        , timeout_fee
            |-> timeout_fee
        , refund_address
            |-> user
        ]
      )

\* @type: (CHAIN_ID, CHANNEL_ID, SEQUENCE, Str) => Bool;
SendPacket(chain_id, channel_id, sequence, payload) ==
  /\  BasePacket!SendPacket(chain_id, channel_id, sequence, payload)
  /\  \/  /\  Channel!FeesEnabled(chain_id, channel_id)
          /\  \E user \in RegularUsers:
              \E receive_fee, ack_fee, timeout_fee \in AllFees:
                PayPacketFee(
                  chain_id
                , channel_id
                , sequence
                , user
                , receive_fee
                , ack_fee
                , timeout_fee
                )
          /\  UNCHANGED << completed_escrows, relay_history >>
      \/  /\  UNCHANGED << fee_escrows, completed_escrows, relay_history >>
          /\  Bank!Unchanged

\* @type: (PACKET, Seq(Str)) => Bool;
ReceivePacket(packet, ack_acc) ==
  /\  IF  Channel!FeesEnabled(
            packet.destination_chain_id
          , packet.destination_channel_id
          )
      THEN
        \E relayer \in Relayers:
        \E counterparty_relayer \in { relayer, InvalidAddress }:
          LET
            ack == Utils!Concat(
              ack_acc, <<
                relayer
              >>
            )
          IN
          /\  BasePacket!ReceivePacket(packet, ack)
          /\  relay_history' = Utils!Concat(
                relay_history
              , <<  [ event
                        |-> "receive"
                    , relayer
                        |-> relayer
                    , counterparty_relayer
                        |-> counterparty_relayer
                    , chain_id
                        |-> packet.destination_chain_id
                    , channel_id
                        |-> packet.destination_channel_id
                    , sequence
                        |-> packet.sequence
                  ]
                >>)
      ELSE
          /\  BasePacket!ReceivePacket(packet, ack_acc)
          /\  UNCHANGED << relay_history >>
  /\  Bank!Unchanged
  /\  UNCHANGED << fee_escrows, completed_escrows >>

\* @type: (CHAIN_ID, CHANNEL_ID, SEQUENCE, Seq(Str)) => Bool;
ConfirmPacket(chain_id, channel_id, sequence, acks) ==
  /\  IF  Channel!FeesEnabled(chain_id, channel_id)
      THEN
        /\  Len(acks) > 1
        /\  BasePacket!ConfirmPacket(chain_id, channel_id, sequence, Tail(acks))
        /\  LET
              forward_relayer == acks[1]
              escrow_key == BasePacket!PacketKey(chain_id, channel_id, sequence)
            IN
            IF escrow_key \in DOMAIN fee_escrows
            THEN
              LET
                escrow == fee_escrows[escrow_key]
                receive_fee_address ==
                  IF Bank!HasAccount(chain_id, forward_relayer)
                  THEN forward_relayer
                  ELSE escrow.refund_address
              IN
              /\  \E reverse_relayer \in Relayers:
                    /\  Bank!MultiTransfer( <<
                          Bank!CreateTransfer(
                            chain_id
                          , FeeModuleAccount
                          , reverse_relayer
                          , escrow.ack_fee
                          )
                        , Bank!CreateTransfer(
                            chain_id
                          , FeeModuleAccount
                          , receive_fee_address
                          , escrow.receive_fee
                          )
                        , Bank!CreateTransfer(
                            chain_id
                          , FeeModuleAccount
                          , escrow.refund_address
                          , escrow.timeout_fee
                          )
                        >> )
                    /\  relay_history' = Utils!Concat(
                          relay_history
                        , <<  [ event
                                  |-> "ack"
                              , relayer
                                  |-> reverse_relayer
                              , chain_id
                                  |-> chain_id
                              , channel_id
                                  |-> channel_id
                              , sequence
                                  |-> sequence
                            ]
                          >>)
              /\  completed_escrows' = completed_escrows \union { escrow_key }
              /\  UNCHANGED << fee_escrows >>
            ELSE
              /\  Bank!Unchanged
              /\  UNCHANGED << fee_escrows, completed_escrows, relay_history >>
      ELSE
        /\  BasePacket!ConfirmPacket(chain_id, channel_id, sequence, acks)
        /\  Bank!Unchanged
        /\  UNCHANGED << fee_escrows, completed_escrows, relay_history >>

\* @type: (PACKET) => Bool;
TimeoutPacket(packet) ==
  /\  BasePacket!TimeoutPacket(packet)
  /\  UNCHANGED << fee_escrows, completed_escrows, relay_history >>
  /\  Bank!Unchanged

\* @type: (CHAIN_ID, CHANNEL_ID, SEQUENCE) => Bool;
ConfirmTimeoutPacket(chain_id, channel_id, sequence) ==
  /\  BasePacket!ConfirmTimeoutPacket(chain_id, channel_id, sequence)
  /\
      \E timeout_relayer \in Relayers:
        LET
          escrow_key == BasePacket!PacketKey(chain_id, channel_id, sequence)
        IN
          /\  IF escrow_key \in DOMAIN fee_escrows
              THEN
                LET escrow == fee_escrows[escrow_key]
                IN
                  Bank!MultiTransfer( <<
                      Bank!CreateTransfer(
                        chain_id
                      , FeeModuleAccount
                      , escrow.refund_address
                      , escrow.ack_fee
                      )
                    , Bank!CreateTransfer(
                        chain_id
                      , FeeModuleAccount
                      , escrow.refund_address
                      , escrow.receive_fee
                      )
                    , Bank!CreateTransfer(
                        chain_id
                      , FeeModuleAccount
                      , timeout_relayer
                      , escrow.timeout_fee
                      )
                    >> )
              ELSE
                Bank!Unchanged
          /\  relay_history' = Utils!Concat(
                relay_history
              , <<  [ event
                        |-> "tiemout"
                    , relayer
                        |-> timeout_relayer
                    , chain_id
                        |-> chain_id
                    , channel_id
                        |-> channel_id
                    , sequence
                        |-> sequence
                  ]
                >>)
          /\  completed_escrows' = completed_escrows \union { escrow_key }
  /\  UNCHANGED << fee_escrows >>

Next ==
  \/  BasePacket!SendAnyPacket(SendPacket)
  \/  BasePacket!ReceiveAnyPacket(ReceivePacket)
  \/  BasePacket!ConfirmAnyPacket(ConfirmPacket)
  \/  BasePacket!TimeoutAnyPacket(TimeoutPacket)
  \/  BasePacket!ConfirmAnyTimeoutPacket(ConfirmTimeoutPacket)

\* Next ==
\*   /\  BasePacket!Next
\*   /\  Bank!Unchanged
\*   /\  UNCHANGED << fee_escrows, completed_escrows, relay_history >>

=====
