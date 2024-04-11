FROM ghcr.io/vmware-research/verifiable-controllers/verus:latest as builder

WORKDIR /anvil

SHELL ["/bin/bash", "-c"]

COPY . .

RUN apt install -y pkg-config libssl-dev
