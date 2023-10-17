FROM ghcr.io/vmware-research/verifiable-controllers/verus:latest as builder

ARG APP
WORKDIR /anvil

SHELL ["/bin/bash", "-c"]

COPY . .

RUN apt install -y pkg-config libssl-dev

RUN VERUS_DIR=/verus ./build.sh ${APP}_controller.rs --no-verify --time

# =============================================================================

FROM debian:bullseye-slim

COPY --from=builder /anvil/src/${APP}_controller /usr/local/bin/controller

ENTRYPOINT ["/usr/local/bin/controller", "run"]
