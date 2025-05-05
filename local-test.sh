#!/usr/bin/env bash

## Test the controller locally in a kind cluster.
##
## Requires kind to be installed and the prerequisites of deploy.sh.

set -xeu

app=$(echo "$1" | tr '_' '-')
app_filename=$(echo "$app" | tr '-' '_')
build_controller="no"

if [ $# -gt 1 ]; then
    if  [ "$2" == "--build" ]; then # chain build.sh
        if [ ! -f "${VERUS_DIR}/source/target-verus/release/verus" ]; then
            echo "Verus not found. Please set VERUS_DIR correct"
            exit 1
        fi
        build_controller="local"
    elif [ "$2" == "--build-remote" ]; then
        build_controller="remote"
    fi
fi

case "$build_controller" in
    local)
        shift 2
        ./build.sh "${app_filename}_controller.rs" "--no-verify" $@
        docker build -f docker/controller/Dockerfile.local -t local/$app-controller:v0.1.0 --build-arg APP=$app_filename .
        ;;
    remote)
        docker build -f docker/controller/Dockerfile.remote -t local/$app-controller:v0.1.0 --build-arg APP=$app_filename .
        ;;
    no)
        shift 1
        docker build -f docker/controller/Dockerfile.local -t local/$app-controller:v0.1.0 --build-arg APP=$app_filename .
        ;;
esac


# Set up the kind cluster and load the image into the cluster
kind create cluster --config deploy/kind.yaml
kind load docker-image local/$app-controller:v0.1.0
# Deploy the controller as a pod to the kind cluster, using the image just loaded
./deploy.sh $app local
