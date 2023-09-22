FROM rust:1.72.0-slim-bullseye as builder

ARG VERUS_VER
WORKDIR /

SHELL ["/bin/bash", "-c"]

RUN apt-get update && apt-get install -y git wget unzip curl gcc
RUN git clone https://github.com/verus-lang/verus.git \
    && cd verus \
    && git checkout ${VERUS_VER} \
    && cd source \
    && ./tools/get-z3.sh \
    && source ../tools/activate \
    && vargo build --release
