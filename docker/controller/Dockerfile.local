# keep consistent with CI env
FROM ubuntu:22.04

ARG APP

COPY src/${APP}_controller /usr/local/bin/controller

ENTRYPOINT ["/usr/local/bin/controller", "run"]
