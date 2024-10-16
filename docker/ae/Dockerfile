FROM ghcr.io/anvil-verifier/anvil/verus:latest as builder

WORKDIR /anvil

SHELL ["/bin/bash", "-c"]

COPY . .

RUN apt install -y pkg-config libssl-dev python3 python3-pip
RUN pip3 install tabulate
