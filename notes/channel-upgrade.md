# Channel Upgrade

A major limitation of the current fee middleware design is that it is not possible to enable fee on existing channels that are created prior to the upgrade. This can impose huge challenge for adoption, as it is likely infeasible for existing chains to close and recreate the channels.

For example, if Osmosis wanted to enable fee on all its existing channels, it would have to close and re-create the channels. This will also result in UX and migration nightmare, as the IBC denoms will all be changed, and all liquidity pools will have to be recreated.

If the main goal of the fee middleware is to incentivize existing relayers, this would likely fail because chains cannot enable fee even if they want to. Publicity-wise, it will also cause confusion to users, if they have to learn that relayer fees are only enabled on new channels.

## Recommendation

The fee middleware should be designed to allow soft upgrade
