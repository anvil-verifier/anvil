#!/usr/bin/env bash

## Test the controller locally in a kind cluster.
##
## Requires kind to be installed and the prerequisites of deploy.sh.
## Usage: ./local-test.sh <controller_name> [--no-build]

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
        docker build -f docker/controller/Dockerfile.local -t local/$app-controller:v0.1.0 --build-arg APP=$app_filename .
        ;;
esac


# Set up the kind cluster and load the image into the cluster
kind create cluster --config deploy/kind.yaml
kind load docker-image local/$app-controller:v0.1.0

if [ "$app" == "v2-vdeployment" ]; then
    # deploy VReplicaSet controller as dependency
    echo "Building v2-vreplicaset controller image"
    if [ "$2" != "--no-build" ]; then
        docker build -t local/v2-vreplicaset-controller:v0.1.0 --build-arg APP=v2_vreplicaset .
    fi
    kind load docker-image local/v2-vreplicaset-controller:v0.1.0
fi
rm Dockerfile

# Deploy the controller as a pod to the kind cluster, using the image just loaded
./deploy.sh $app local
