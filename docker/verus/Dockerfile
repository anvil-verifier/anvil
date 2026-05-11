# Builder image with Rust + Verus + `cargo verus` preinstalled.
# Tagged as ghcr.io/anvil-verifier/anvil/verus:latest and consumed by
# docker/controller/Dockerfile.publish.
FROM rust:1.88-slim-bookworm

# Pin to the same Verus release that Cargo.toml's `vstd =` line targets.
ARG VERUS_VER=0.0.0-2026-05-10-0145
WORKDIR /

SHELL ["/bin/bash", "-c"]

RUN apt-get update && apt-get install -y --no-install-recommends \
        git wget unzip curl gcc ca-certificates \
    && rm -rf /var/lib/apt/lists/*

# Translate the crates.io-style version (0.0.0-YYYY-MM-DD-HHMM) into the
# Verus release tag format (YYYY.MM.DD.HHMM) and download the binary release.
RUN VERUS_TAG=$(echo "$VERUS_VER" | sed 's/^0\.0\.0-//; s/-/./g') \
 && curl -fsSL -o /tmp/verus.zip \
        "https://github.com/verus-lang/verus/releases/download/release%2F${VERUS_TAG}/verus-${VERUS_TAG}-x86-linux.zip" \
 && unzip -q /tmp/verus.zip -d /usr/local \
 && rm /tmp/verus.zip \
 && mv /usr/local/verus-x86-linux /usr/local/verus

ENV PATH="/usr/local/verus:${PATH}"

# Seed cargo-verus so the first project build doesn't have to.
RUN cargo verus --help >/dev/null
