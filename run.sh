#!/usr/bin/env bash

set -e
set -x

export RUSTFLAGS="-D warnings"

cargo clippy --all-features
cargo test --all-features
cargo run --example example
cargo run --example readme

exit 0
