FROM rust:latest

WORKDIR /anvil

SHELL ["/bin/bash", "-c"]

COPY . .

RUN apt-get update && apt-get install -y git wget unzip curl gcc
RUN git clone https://github.com/verus-lang/verus.git \
    && cd verus/source \
    && ./tools/get-z3.sh \
    && source ../tools/activate \
    && vargo build --release

RUN VERUS_DIR=/anvil/verus ./build.sh simple_controller.rs --time

ENTRYPOINT ["/anvil/src/simple-controller"]
