#!/usr/bin/env bash

## Test the controller locally in a kind cluster.
##
## Requires kind to be installed and the prerequisites of deploy.sh.
## Usage: ./local-test.sh <controller_name> [--no-build]

set -eu

app=$(echo "$1" | tr '_' '-')
app_filename=$(echo "$app" | tr '-' '_')
dockerfile="docker/controller/Dockerfile.local"
build_controller=0

build() { # build app_name build_args
    echo "Building $1 controller binary"
    local app_filename=$(echo "$1" | tr '-' '_')
    ./build.sh "${app_filename}_controller.rs" "--no-verify" ${2:-}
    echo "Building $1 controller image"
    docker build -f $dockerfile -t local/$1-controller:v0.1.0 --build-arg APP=$app_filename .
}

if [ $# -gt 1 ]; then
    if  [ "$2" == "--build" ]; then # chain build.sh
        command -v verus; # if not set quit by set -e
        shift 2
        build $app $@;
        if [ "$app" == "vdeployment" ]; then
            build vreplicaset $@;
        elif [ "$app" == "rabbitmq" ]; then
            build vstatefulset $@;
        fi
    else
        echo "Use existing $app controller image"
    fi
fi

# Setup cluster, deploy the controller as a pod to the kind cluster, using the image just loaded
./deploy.sh $app local