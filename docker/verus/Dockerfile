FROM ubuntu:22.04

ARG VERUS_VER
WORKDIR /

SHELL ["/bin/bash", "-c"]

RUN apt-get update && apt-get install -y git wget unzip curl gcc
RUN git clone https://github.com/verus-lang/verus.git \
    && cd verus \
    && git checkout ${VERUS_VER}
RUN cd verus \
    && curl --proto '=https' --tlsv1.2 --retry 10 --retry-connrefused -fsSL "https://sh.rustup.rs" | sh -s -- --default-toolchain none -y \
    && . "$HOME/.cargo/env" \
    && rustup toolchain install
RUN cd verus/source \
    && ./tools/get-z3.sh \
    && source ../tools/activate \
    && vargo build --release
