FROM ghcr.io/vmware-research/verifiable-controllers/verus:latest as builder

WORKDIR /anvil

SHELL ["/bin/bash", "-c"]

COPY . .

# Build the verified rabbitmq controller
RUN VERUS_DIR=/verus ./build.sh rabbitmq_controller.rs --time -o rabbitmq-controller

# Build the unverified rabbitmq controller
RUN cd reference-controllers/rabbitmq-controller && cargo build

# =============================================================================

FROM debian:bullseye-slim

COPY --from=builder /anvil/src/rabbitmq-controller /usr/local/bin/rabbitmq-controller
COPY --from=builder /anvil/reference-controllers/rabbitmq-controller/target/debug/rabbitmq-controller /usr/local/bin/rabbitmq-controller-unverified

ENTRYPOINT ["/usr/local/bin/rabbitmq-controller", "run"]
