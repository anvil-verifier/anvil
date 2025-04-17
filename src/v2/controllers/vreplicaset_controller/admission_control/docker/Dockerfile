FROM clux/muslrust:stable AS builder

COPY Cargo.* ./
COPY src/ src/

RUN --mount=type=cache,target=/volume/target \
    --mount=type=cache,target=/root/.cargo/registry \
    cargo build --release --bin admission_control && \
    mv /volume/target/x86_64-unknown-linux-musl/release/admission_control .

FROM cgr.dev/chainguard/busybox:latest
COPY --from=builder --chown=nonroot:nonroot /volume/admission_control /app/admission_control
EXPOSE 8443
ENTRYPOINT ["/app/admission_control"]