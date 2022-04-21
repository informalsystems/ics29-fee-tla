# Arbitary string in counterparty address

[GitHub Discussion](https://github.com/cosmos/ibc-go/pull/276#discussion_r787926055)

Source file: `modules/apps/29-fee/keeper/msg_server.go`

Code snippet:

```go
func (k Keeper) RegisterCounterpartyAddress(goCtx context.Context, msg *types.MsgRegisterCounterpartyAddress) (*types.MsgRegisterCounterpartyAddressResponse, error) {
	ctx := sdk.UnwrapSDKContext(goCtx)

	k.SetCounterpartyAddress(
		ctx, msg.Address, msg.CounterpartyAddress,
	)
```

## Description

A relayer gets paid by the source chain by relaying a packet from the source chain to the destination chain. For the fee payment to work, the destination chain has to register the relayer's counterparty address on the source chain and include that information as the forward relayer address in the packet acknowledgement.

Since the the destination chain cannot know the address format of the source chain, it cannot validate the string is a valid address for the source chain. However if this is left totally unvalidated, an attacker can use it to store arbitrary string content. This may lead to attacks such as XSS when a front end is displaying the address, or a DOS with an overly large string.

## Suggestion

The destination should do basic validation on the counterparty address that covers the majority of blockchain addresses in use today. e.g. `\w{1, 30}`.
