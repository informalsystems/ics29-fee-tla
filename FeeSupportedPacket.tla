----- MODULE FeeSupportedPacket -----

EXTENDS
    Naturals
  , Sequences
  , FeeSupportedPacketParams

LOCAL BasePacket == INSTANCE BasePacket

LOCAL Channel == INSTANCE FeeSupportedChannel

LOCAL Utils == INSTANCE Utils

LOCAL Bank == INSTANCE Bank

Init ==
  /\  BasePacket!Init
  /\  fee_escrows = Utils!EmptyRecord
  /\  completed_escrows = {}

Unchanged ==
  /\  BasePacket!Unchanged
  /\  Bank!Unchanged
  /\  UNCHANGED << fee_escrows, completed_escrows >>

PayPacketFee(
  chain_id
, channel_id
, sequence
, user
, receive_fee
, ack_fee
) ==
  /\  receive_fee >= 0
  /\  ack_fee >= 0
  /\  ~(receive_fee = 0 /\ ack_fee = 0)
  /\  Bank!Transfer(
        chain_id
      , user
      , FeeModuleAccount
      , receive_fee + ack_fee
      )
  /\  fee_escrows' = Utils!AddEntry(
        fee_escrows,
        << chain_id, channel_id, sequence >>,
        [ receive_fee |-> receive_fee
        , ack_fee |-> ack_fee
        , refund_address |-> user
        ]
      )

SendPacket(chain_id, channel_id, sequence, payload) ==
  /\  BasePacket!SendPacket(chain_id, channel_id, sequence, payload)
  /\  \/  /\  Channel!FeesEnabled(chain_id, channel_id)
          /\  \E user \in RegularUsers:
              \E receive_fee, ack_fee \in AllFees:
                PayPacketFee(
                  chain_id
                , channel_id
                , sequence
                , user
                , receive_fee
                , ack_fee
                )
          /\  UNCHANGED << completed_escrows >>
      \/  /\  UNCHANGED << fee_escrows, completed_escrows >>
          /\  Bank!Unchanged

ReceivePacket(packet, ack_acc) ==
  /\  IF  Channel!FeesEnabled(
            packet.destination_chain_id
          , packet.destination_channel_id
          )
      THEN
        \E relayer \in Relayers:
          LET
            ack == Utils!Concat(
              ack_acc, <<
                [ forward_relayer |-> relayer ]
              >>
            )
          IN
          BasePacket!ReceivePacket(packet, ack)
      ELSE
          BasePacket!ReceivePacket(packet, ack_acc)
  /\  Bank!Unchanged
  /\  UNCHANGED << fee_escrows, completed_escrows >>

ConfirmPacket(chain_id, channel_id, sequence, acks) ==
  /\  IF  Channel!FeesEnabled(chain_id, channel_id)
      THEN
        /\  Len(acks) > 1
        /\  BasePacket!ConfirmPacket(chain_id, channel_id, sequence, Tail(acks))
        /\  LET
              forward_relayer == acks[1].forward_relayer
              escrow_key == << chain_id, channel_id, sequence >>
            IN
            IF escrow_key \in DOMAIN fee_escrows
            THEN
              LET
                escrow == fee_escrows[escrow_key]
              IN
              /\  \E reverse_relayer \in Relayers:
                    Bank!MultiTransfer(<<
                      [ chain_id |-> chain_id
                      , sender |-> FeeModuleAccount
                      , receiver |-> reverse_relayer
                      , amount |-> escrow.ack_fee
                      ]
                    , [ chain_id |-> chain_id
                      , sender |-> FeeModuleAccount
                      , receiver |-> forward_relayer
                      , amount |-> escrow.receive_fee
                      ]
                    >> )
              /\  completed_escrows' = completed_escrows \union { escrow_key }
              /\  UNCHANGED << fee_escrows >>
            ELSE
              /\  Bank!Unchanged
              /\  UNCHANGED << fee_escrows, completed_escrows >>
      ELSE
        /\  BasePacket!ConfirmPacket(chain_id, channel_id, sequence, acks)
        /\  Bank!Unchanged
        /\  UNCHANGED << fee_escrows, completed_escrows >>

Next ==
  \/  BasePacket!SendAnyPacket(SendPacket)
  \/  BasePacket!ReceiveAnyPacket(ReceivePacket)
  \/  BasePacket!ConfirmAnyPacket(ConfirmPacket)

\* Next ==
\*   /\  BasePacket!Next
\*   /\  Bank!Unchanged
\*   /\  UNCHANGED << fee_escrows, completed_escrows >>

=====
