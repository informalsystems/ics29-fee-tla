# One-sided disabling of fee

[GitHub Discussion](https://github.com/cosmos/ibc-go/pull/276#discussion_r788577581)

Source file: `modules/apps/29-fee/ibc_module.go`


Code snippet:

```go
func (im IBCModule) OnChanCloseInit(
	ctx sdk.Context,
	portID,
	channelID string,
) error {
	// delete fee enabled on channel
	// and refund any remaining fees escrowed on channel
	im.keeper.DeleteFeeEnabled(ctx, portID, channelID)
	err := im.keeper.RefundFeesOnChannel(ctx, portID, channelID)
	// error should only be non-nil if there is a bug in the code
	// that causes module account to have insufficient funds to refund
	// all escrowed fees on the channel.
	// Disable all channels to allow for coordinated fix to the issue
	// and mitigate/reverse damage.
	// NOTE: Underlying application's packets will still go through, but
	// fee module will be disabled for all channels
	if err != nil {
		im.keeper.DisableAllChannels(ctx)
	}
```

## Description

In `OnChanCloseInit`, the fee middleware tries to refund the fees on all channels. If the call to `RefundFeesOnChannel` fails, it is assumed that some invariant is violated, and the fee middleware try to disable fee for all channels.

However the fee cannot be disabled only on one chain without notifying the counterparty chain. The fee middleware on the counterparty chain would only check if the fee is enabled locally, and if so will try to decode the message content as if it contains the wrapped fee information and fail. Similarly when the original chain process packets coming from the counterparty chain, it would only check that the fee is disabled locally, and pass on the request to the inner IBC module, which would attempt to decode a message that has been wrapped with fee information and fail. In other words, this will break all existing channels that have fee enabled.

## Suggestion

Do not disable the fee module even when there are invariant violation. The fee module can instead enable a crisis flag to disable

A better approach is design a protocol that allows existing channels to re-negotiate on enabling/disabling fees. This would also benefit existing chains to enable fee on existing channels without having to re-create the channels.
