FROM debian:bullseye-slim

ARG APP

COPY src/${APP}_controller /usr/local/bin/controller

ENTRYPOINT ["/usr/local/bin/controller", "run"]
