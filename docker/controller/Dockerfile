FROM ghcr.io/vmware-research/verifiable-controllers/verus:latest as builder

ARG APP
WORKDIR /anvil

SHELL ["/bin/bash", "-c"]

COPY . .

RUN VERUS_DIR=/verus ./build.sh ${APP}_controller.rs --no-verify --time -o controller

# =============================================================================

FROM debian:bullseye-slim

COPY --from=builder /anvil/src/controller /usr/local/bin/controller

ENTRYPOINT ["/usr/local/bin/controller", "run"]
