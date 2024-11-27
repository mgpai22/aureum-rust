FROM lukemathwalker/cargo-chef:latest as chef
WORKDIR /app

# Install clang and other build dependencies
RUN apt-get update && \
    apt-get install -y clang llvm && \
    apt-get clean && \
    rm -rf /var/lib/apt/lists/*

RUN rustup toolchain install nightly-2024-07-19 && \
    rustup default nightly-2024-07-19 && \
    rustup target add wasm32-wasi --toolchain nightly-2024-07-19

FROM chef AS planner
COPY ./Cargo.toml ./rust-toolchain.toml ./
COPY ./src ./src
RUN cargo chef prepare

FROM chef AS builder
COPY --from=planner /app/recipe.json .
RUN cargo chef cook --target wasm32-wasi --release
COPY . .
RUN cargo build --target wasm32-wasi --release

FROM scratch AS runtime
COPY --from=builder /app/target/wasm32-wasi/release/aureum.wasm /aureum.wasm