FROM ghcr.io/vmware-research/verifiable-controllers/verus:latest as builder

WORKDIR /anvil

SHELL ["/bin/bash", "-c"]

COPY . .

RUN VERUS_DIR=/verus ./build.sh simple_controller.rs --time -o simple-controller

RUN cd reference_controllers/simple-controller && cargo build

# =============================================================================

FROM debian:bullseye-slim

COPY --from=builder /anvil/src/simple-controller /usr/local/bin/simple-controller
COPY --from=builder /anvil/reference_controllers/simple-controller/target/debug/simple-controller /usr/local/bin/simple-controller-unverified

ENTRYPOINT ["/usr/local/bin/simple-controller run"]
