FROM ghcr.io/vmware-research/verifiable-controllers/verus:latest as builder

WORKDIR /anvil

SHELL ["/bin/bash", "-c"]

COPY . .

RUN VERUS_DIR=/verus ./build.sh simple_controller.rs --time

RUN cd reference_controllers/simple_controller && cargo build

# =============================================================================

FROM debian:bullseye-slim

COPY --from=builder /anvil/src/simple_controller /usr/local/bin/simple_controller
COPY --from=builder /anvil/reference_controllers/simple_controller/target/debug/simple_controller_unverified /usr/local/bin/simple_controller_unverified

ENTRYPOINT ["/usr/local/bin/simple_controller run"]
