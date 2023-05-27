FROM ghcr.io/vmware-research/verifiable-controllers/verus:latest as builder

WORKDIR /anvil

SHELL ["/bin/bash", "-c"]

COPY . .

# Build the verified zookeeper controller
RUN VERUS_DIR=/verus ./build.sh zookeeper_controller.rs --time

# Build the unverified zookeeper controller
RUN cd reference_controllers/zookeeper_controller && cargo build

# =============================================================================

FROM debian:bullseye-slim

COPY --from=builder /anvil/src/zookeeper_controller /usr/local/bin/zookeeper_controller
COPY --from=builder /anvil/reference_controllers/zookeeper_controller/target/debug/zookeeper_controller_unverified /usr/local/bin/zookeeper_controller_unverified

ENTRYPOINT ["/usr/local/bin/zookeeper_controller", "run"]
