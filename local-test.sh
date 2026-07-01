#!/usr/bin/env bash

## Build a controller image and run it locally in a kind cluster.
##
## Requires kind to be installed and the prerequisites of deploy.sh.
## Usage:
##   ./local-test.sh <controller_name> [--build] [extra cargo-verus args]

set -xeu

app=$(echo "$1" | tr '_' '-')
app_filename=$(echo "$app" | tr '-' '_')
dockerfile_path="docker/controller/Dockerfile"
build_controller="no"

if [ $# -gt 1 ]; then
    case "$2" in
        --build) build_controller="local" ;;
    esac
fi

build_controller_image() {
    local target_app="$1"
    local target_filename
    target_filename=$(echo "$target_app" | tr '-' '_')

    case "$build_controller" in
        local)
            echo "Building $target_app controller binary"
            cargo verus build --release --bin "${target_filename}_controller" -- --no-verify "${@:2}"
            echo "Building $target_app controller image"
            docker build -f docker/controller/Dockerfile \
                -t "local/${target_app}-controller:v0.1.0" \
                --build-arg APP="${target_filename}" .
            ;;
        no)
            echo "Use existing $target_app controller image"
            ;;
    esac
}

# Skip flags that the caller passed for the build step.
if [ $# -ge 2 ]; then
    shift 2
fi

build_controller_image "$app" "$@"

# For VDeployment, also build the VReplicaSet controller (its dependency).
if [ "$app" == "vdeployment" ]; then
    build_controller_image "vreplicaset" "$@"
fi

# For RabbitMQ, also build the VStatefulSet controller (its dependency).
if [ "$app" == "rabbitmq" ]; then
    build_controller_image "vstatefulset" "$@"
fi

# Set up cluster and deploy the controller as a pod.
./deploy.sh "$app" local
