FROM ghcr.io/vmware-research/verifiable-controllers/verus:latest as builder

WORKDIR /anvil

SHELL ["/bin/bash", "-c"]

COPY . .

RUN cd reference_controllers/zookeeper_controller && cargo build

# =============================================================================

FROM debian:bullseye-slim

COPY --from=builder /anvil/reference_controllers/zookeeper_controller/target/debug/zookeeper_controller_unverified /usr/local/bin/zookeeper_controller_unverified

ENTRYPOINT ["/usr/local/bin/zookeeper_controller run"]
