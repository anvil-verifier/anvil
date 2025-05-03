#!/usr/bin/env bash

## Test the controller locally in a kind cluster.
##
## Requires kind to be installed and the prerequisites of deploy.sh.

set -xeu

app=$(echo "$1" | tr '_' '-')
app_filename=$(echo "$app" | tr '-' '_')

if [ $# -gt 1 ] && [ "$2" == "--build" ]; then
    if [ ! -f "${VERUS_DIR}/source/target-verus/release/verus" ]; then
        echo "Verus not found. Please set VERUS_DIR correct"
        exit 1
    fi
    shift 2
    ./build.sh "${app_filename}_controller.rs" "--no-verify" $@
fi

if [ ! -f "src/${app_filename}_controller" ]; then
    echo "Controller ${app_filename} not found. Please build the controller manually or use the --build flag"
    exit 1
fi

# Copy the Dockerfile and build the docker image of the controller
docker build -f docker/controller/Dockerfile -t local/$app-controller:v0.1.0 --build-arg APP=$app_filename .

# Set up the kind cluster and load the image into the cluster
kind create cluster --config deploy/kind.yaml
kind load docker-image local/$app-controller:v0.1.0
# Deploy the controller as a pod to the kind cluster, using the image just loaded
./deploy.sh $app local
