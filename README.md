# ICS29 Fee Middleware Specification

This repository contains work in progress for the TLA+/Apalache code for specifying
the [ICS29 Fee Payment](https://github.com/cosmos/ibc/tree/master/spec/app/ics-029-fee-payment) specification.

An overview of the specification is available at https://app.excalidraw.com/l/4XqkU6POmGI/6ySHXye6DxI.

## Running

The specification can be run by installing [Apalache](https://apalache.informal.systems/). The simplest way is to first install [Cosmos.nix](https://github.com/informalsystems/cosmos.nix/#non-nixos) and then enter the Nix shell:

```bash
nix shell github:informalsystems/cosmos.nix#apalache
```

### Type Checking

To typecheck the spec, run:

```bash
apalache-mc typecheck spec/Main.tla
```

### Random Traces

To generate a random trace that involves fee transfer, run:

```bash
apalache-mc check --inv=WantedStateInvariant spec/Main.tla
```

You can modify the `WantedStateInvariant` in [`spec/Main.tla`](spec/Main.tla) to generate traces that reach a given state that you are interested in.

### Invariant Checks

To check for the correctness of the spec, with absence of invariant violation,
run:

```bash
apalache-mc check --inv=Invariant spec/Main.tla
```

Note that this may take 30~60 minutes or more for the checking to be completed
