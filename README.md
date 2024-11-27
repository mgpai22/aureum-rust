# Aureum Rust

Aureum Rust is a rust library which compiles to wasi wasm. 

It's primary goal it to utilize `eval_phase_two_raw` from [uplc](https://crates.io/crates/uplc) to evaluate and get costs for Plutus scripts.

# Build Instructions

## Normal Build
Note that versions in `rust-toolchain.toml` must be used.

Nightly is required for `thiserror` crate.

`rustc 1.81.0-nightly` is needed to generate `wasm32-wasi` targets. Future versions seem to change to `wasm32-wasip1`. 

```
cargo build --target wasm32-wasi --release
```

## Docker Build

```bash
./build-docker.sh
```
