# The Sundance SMT Solver

An SMT solver for program verification with support for uninterpreted functions, linear integer arithmetic, and quantifier instantiation.

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

## Security

See [CONTRIBUTING](CONTRIBUTING.md#security-issue-notifications) for more information.

## License

This project is licensed under the Apache-2.0 License.
