#!/bin/bash
set -e

cargo +nightly fmt --all -- --check
cargo clippy --all-features --all-targets -- -D clippy::all
cargo doc --no-deps

cargo test --all-targets
