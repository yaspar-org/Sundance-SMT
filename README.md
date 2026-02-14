# The Sundance SMT Solver

An SMT solver for program verification with support for uninterpreted functions, linear integer arithmetic, and quantifier instantiation.

## Dependencies

- yaspar
- yaspar-ir

## Usage

```bash
cargo run -- path/to/your/smt/file.smt2
```

## Testing 

```bash
cargo test
```

## Using z3 as an arithmetic solver

Sundance allows to call z3 as an arithmetic solver instead of its own default solver.
Z3 will be compiled from source by default, but you can use a local build for z3 by 
adding the `--no-default-features --features local-z3` flags with cargo. Make sure 
the `Z3_SYS_Z3_HEADER` environment flag points to the path to `z3.h`

## Security

See [CONTRIBUTING](CONTRIBUTING.md#security-issue-notifications) for more information.

## License

This project is licensed under the Apache-2.0 License.