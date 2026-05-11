# Builder image with Rust + Verus + `cargo verus` preinstalled.
# Tagged as ghcr.io/anvil-verifier/anvil/verus:latest and consumed by
# docker/controller/Dockerfile.publish.
#
# Always installs the latest Verus release at image-build time. To pin
# a specific version, pass --build-arg VERUS_TAG=0.YYYY.MM.DD.SHA.
FROM rust:1.88-slim-bookworm

ARG VERUS_TAG=
WORKDIR /

SHELL ["/bin/bash", "-c"]

RUN apt-get update && apt-get install -y --no-install-recommends \
        git wget unzip curl gcc ca-certificates jq \
    && rm -rf /var/lib/apt/lists/*

RUN if [ -z "${VERUS_TAG}" ]; then \
        VERUS_TAG=$(curl -fsSL https://api.github.com/repos/verus-lang/verus/releases/latest \
                    | jq -r .tag_name | sed 's|^release/||'); \
    fi \
 && echo "Installing Verus ${VERUS_TAG}" \
 && curl -fsSL -o /tmp/verus.zip \
        "https://github.com/verus-lang/verus/releases/download/release%2F${VERUS_TAG}/verus-${VERUS_TAG}-x86-linux.zip" \
 && unzip -q /tmp/verus.zip -d /usr/local \
 && rm /tmp/verus.zip \
 && mv /usr/local/verus-x86-linux /usr/local/verus

ENV PATH="/usr/local/verus:${PATH}"

# Seed cargo-verus so the first project build doesn't have to.
RUN cargo verus --help >/dev/null
