# Build outside the container with `cargo verus build`, then bake the binary.
FROM ubuntu:24.04

ARG APP

COPY target/release/${APP}_controller /usr/local/bin/controller

ENTRYPOINT ["/usr/local/bin/controller", "run"]
