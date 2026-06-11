# Project Rules

- Never ask if the user wants to stop or pick up in a future session. Always continue working.
- Always build with `cargo build --release --no-default-features` before running regression tests.
- Run regression tests with `cargo test --release --no-default-features regression_test -- --no-capture`.
- Baseline: 352 correct, 0 incorrect, 17 timeout.
- Always run the full test suite before committing
- For complex tasks write a plan and STICK TO IT. If a subtask in the plan is more complicated than initially thought, create a subplan and add it as a component into the larger plan