# Error handling when forward relayer address is invalid

[GitHub Discussion](https://github.com/cosmos/ibc-go/pull/276#discussion_r787916398)

Source file: `modules/apps/29-fee/keeper/escrow.go`

Code snippet:

```go
func (k Keeper) DistributePacketFees(ctx sdk.Context, refundAcc, forwardRelayer string, reverseRelayer sdk.AccAddress, feeInEscrow types.IdentifiedPacketFee) {
	// distribute fee for forward relaying
	forward, err := sdk.AccAddressFromBech32(forwardRelayer)
	if err == nil {
		k.distributeFee(ctx, forward, feeInEscrow.Fee.RecvFee)
	}
```

## Description

A relayer gets paid by the source chain by relaying a packet from the source chain to the destination chain. For the fee payment to work, the destination chain has to register the relayer's counterparty address on the source chain and include that information as the forward relayer address in the packet acknowledgement.

However since the the destination chain cannot know the address format of the source chain, a relayer may register a counterparty address of arbitrary string. It is also possible that the relayer do not register any counterparty address, in which case would be represented as an empty string which is also an invalid address.

When the forward relayer address is invalid, the call to `AccAddressFromBech32` would fail with error, and no fee will be distributed. As a result, the escrowed receive fee is lost forever.

## Suggestion

A proper fix for this is to refund the escrowed receive fee to the refund address.
