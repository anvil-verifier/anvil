FROM rust:latest as builder

WORKDIR /

SHELL ["/bin/bash", "-c"]

RUN apt-get update && apt-get install -y git wget unzip curl gcc
RUN git clone https://github.com/verus-lang/verus.git \
    && cd verus/source \
    && ./tools/get-z3.sh \
    && source ../tools/activate \
    && vargo build --release
