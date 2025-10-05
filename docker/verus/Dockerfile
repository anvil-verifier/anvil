FROM rust:1.88-slim-bookworm

ARG VERUS_VER=0.2025.09.25.04e8687
WORKDIR /

SHELL ["/bin/bash", "-c"]

RUN apt-get update && apt-get install -y git wget unzip curl gcc
ENV PATH=$PATH:/usr/local/verus
RUN curl -LO https://github.com/verus-lang/verus/releases/download/release/${VERUS_VER}/verus-${VERUS_VER}-x86-linux.zip && \
    unzip verus-${VERUS_VER}-x86-linux.zip && \
    cp -r verus-x86-linux/ /usr/local/verus && \
    rm verus-${VERUS_VER}-x86-linux.zip && \
    rm -r verus-x86-linux && \
    cargo verus
