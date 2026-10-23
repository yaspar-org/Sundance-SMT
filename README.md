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


## Arithmetic backends

The arithmetic backend is selected with `--arithmetic <backend>`:

| Backend | Description |
|---|---|
| `internalincremental` | Internal LIRA solver kept in sync with the SAT trail |
| `internal` | Internal LIRA solver, re-run from scratch on each check |
| `z3incremental` | Persistent Z3 solver kept in sync with the SAT trail (requires a Z3 build) |
| `z3` | Z3, re-run from scratch on each check (requires a Z3 build) |
| `none` | No arithmetic reasoning |

The default is `z3incremental` when Sundance is built with Z3, and `internalincremental` otherwise.

## Using z3 as an arithmetic solver

Z3 will be compiled from source by default, but you can use a local build for z3 by
adding the `--no-default-features --features local-z3` flags with cargo. Make sure
the `Z3_SYS_Z3_HEADER` environment flag points to the path to `z3.h`.

To build without z3 entirely (using only the internal arithmetic solvers):

```bash
cargo build --no-default-features
```

## Security

See [CONTRIBUTING](CONTRIBUTING.md#security-issue-notifications) for more information.

## License

This project is licensed under the Apache-2.0 License.
