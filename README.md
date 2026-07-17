# The Sundance SMT Solver

An SMT solver for program verification with support for uninterpreted functions, linear integer arithmetic, and
quantifier instantiation.

**Sundance is under active development, and there may be breaking
changes!**

## Dependencies

- yaspar
- yaspar-ir

## Building

```
git submodule init && git submodule update
cargo build
```

## Usage

```bash
cargo run -- path/to/your/smt/file.smt2
```

Goal-relative quantifier-instantiation ordering is enabled by default. Disable
it for comparison with:

```bash
cargo run -- path/to/your/smt/file.smt2 --no-goal-based-instantiation
```

This mode treats the final user assertion as distance zero and computes
SHAKE-style layers through shared user-defined symbols. Quantifier bodies remain
hidden until one of their trigger symbol sets is reachable. E-matches are then
ordered by the distances of their concrete trigger terms, instantiated bodies,
and bindings. The mode only reorders candidates; it does not discard them.

## Testing

```bash
cargo test -- --skip regression_test
```

To run the regression tests requires a release build:

```bash
cargo test --release -- --nocapture
```

## Benchmarking

To run the micro-benchmarks using [criterion](https://crates.io/crates/criterion), run

```bash
cargo bench
```


## Using z3 as an arithmetic solver

Sundance allows users to call z3 as an arithmetic solver instead of its own default solver.
Z3 will be compiled from source by default, but you can use a local build for z3 by
adding the `--no-default-features --features local-z3` flags with cargo. Make sure
the `Z3_SYS_Z3_HEADER` environment flag points to the path to `z3.h`.

To build without z3 entirely (using only the internal arithmetic solver):

```bash
cargo build --no-default-features
```

## Security

See [CONTRIBUTING](CONTRIBUTING.md#security-issue-notifications) for more information.

## License

This project is licensed under the Apache-2.0 License.
