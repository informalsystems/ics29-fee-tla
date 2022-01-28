----- MODULE FeeSupportedPacket -----

EXTENDS
    Naturals
  , FeeSupportedPacketParams

LOCAL BasePacket == INSTANCE BasePacket

LOCAL Channel == INSTANCE FeeSupportedChannel

LOCAL Utils == INSTANCE Utils

LOCAL Bank == INSTANCE Bank

Init ==
  /\  BasePacket!Init
  /\  fee_escrows = Utils!EmptyRecord

Unchanged ==
  /\  BasePacket!Unchanged
  /\  Bank!Unchanged
  /\  UNCHANGED << fee_escrows >>

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
  /\  \/  /\  Channel!FeesEnabled(chain_id, channel_id)
          /\  \E user \in AllUsers:
              \E receive_fee, ack_fee \in AllFees:
                PayPacketFee(
                  chain_id
                , channel_id
                , sequence
                , user
                , receive_fee
                , ack_fee
                )
      \/  /\  UNCHANGED << fee_escrows >>
          /\  Bank!Unchanged
  /\  BasePacket!SendPacket(chain_id, channel_id, sequence, payload)

ReceivePacket(packet, ack_acc) ==
  /\  BasePacket!ReceivePacket(packet, ack_acc)
  /\  Bank!Unchanged
  /\  UNCHANGED << fee_escrows >>

ConfirmPacket(chain_id, channel_id, sequence, acks) ==
  /\  BasePacket!ConfirmPacket(chain_id, channel_id, sequence, acks)
  /\  Bank!Unchanged
  /\  UNCHANGED << fee_escrows >>

Next ==
  \/  BasePacket!SendAnyPacket(SendPacket)
  \/  BasePacket!ReceiveAnyPacket(ReceivePacket)
  \/  BasePacket!ConfirmAnyPacket(ConfirmPacket)

=====
