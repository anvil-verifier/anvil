FROM ghcr.io/vmware-research/verifiable-controllers/verus:latest as builder

WORKDIR /anvil

SHELL ["/bin/bash", "-c"]

COPY . .

# Build the verified zookeeper controller
RUN VERUS_DIR=/verus ./build.sh zookeeper_controller.rs --time -o zookeeper-controller

# Build the unverified zookeeper controller
RUN cd reference-controllers/zookeeper-controller && cargo build

# =============================================================================

FROM debian:bullseye-slim

COPY --from=builder /anvil/src/zookeeper-controller /usr/local/bin/zookeeper-controller
COPY --from=builder /anvil/reference-controllers/zookeeper-controller/target/debug/zookeeper-controller /usr/local/bin/zookeeper-controller-unverified

ENTRYPOINT ["/usr/local/bin/zookeeper-controller", "run"]
