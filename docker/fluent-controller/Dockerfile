FROM ghcr.io/vmware-research/verifiable-controllers/verus:latest as builder

WORKDIR /anvil

SHELL ["/bin/bash", "-c"]

COPY . .

# Build the verified fluent controller
RUN VERUS_DIR=/verus ./build.sh fluent_controller.rs --time -o fluent-controller

# Build the unverified fluent controller
RUN cd reference-controllers/fluent-controller && cargo build

# =============================================================================

FROM debian:bullseye-slim

COPY --from=builder /anvil/src/fluent-controller /usr/local/bin/fluent-controller
COPY --from=builder /anvil/reference-controllers/fluent-controller/target/debug/fluent-controller /usr/local/bin/fluent-controller-unverified

ENTRYPOINT ["/usr/local/bin/fluent-controller", "run"]
