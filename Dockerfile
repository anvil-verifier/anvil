FROM ubuntu:latest

WORKDIR /anvil

SHELL ["/bin/bash", "-c"]

RUN apt-get update && apt-get install -y git wget unzip curl gcc
RUN curl --proto '=https' --tlsv1.2 --retry 10 --retry-connrefused -fsSL "https://sh.rustup.rs" | sh -s -- --default-toolchain none -y \
    && source "$HOME/.cargo/env" \
    && git clone https://github.com/verus-lang/verus.git \
    && cd verus/source \
    && ./tools/get-z3.sh \
    && source ../tools/activate \
    && vargo build --release

COPY build.sh build.sh
COPY src/ src/

RUN VERUS_DIR=/anvil/verus ./build.sh simple_controller.rs --time

ENTRYPOINT ["/anvil/src/simple-controller"]
