# Counterparty registration needs to be channel-specific

[Github Discussion](https://github.com/cosmos/ibc-go/pull/276#discussion_r787936701)

Source files:
  - `modules/apps/29-fee/keeper/msg_server.go`
  - `modules/apps/29-fee/types/tx.pb.go`

Code snippet:

```go
type MsgRegisterCounterpartyAddress struct {
	Address             string `protobuf:"bytes,1,opt,name=address,proto3" json:"address,omitempty"`
	CounterpartyAddress string `protobuf:"bytes,2,opt,name=counterparty_address,json=counterpartyAddress,proto3" json:"counterparty_address,omitempty" yaml:"counterparty_address"`
}

func (k Keeper) RegisterCounterpartyAddress(goCtx context.Context, msg *types.MsgRegisterCounterpartyAddress) (*types.MsgRegisterCounterpartyAddressResponse, error) {
```

## Description

A relayer gets paid by the source chain by relaying a packet from the source chain to the destination chain. For the fee payment to work, the destination chain has to register the relayer's counterparty address on the source chain and include that information as the forward relayer address in the packet acknowledgement.

The current API for registering the counterparty address do not takes in any parameter on which channel does the counterparty address is assigned to. This means that a relayer can only register one counterparty address for all source chains it is relaying to a destination chain. However since the relayer's address on each source chain is different, this means the relayer can only get paid successfully when relaying from a specific source chain.

## Suggestion

Add the channel ID and port parameters to `MsgRegisterCounterpartyAddress`, and store them as part of the key in the KV store.
