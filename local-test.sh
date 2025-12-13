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

if [ $# -gt 1 ]; then
    if  [ "$2" == "--build" ]; then # chain build.sh
        command -v verus; # if not set quit by set -e
        build_controller=1
        echo "Building $app controller binary"
        shift 2
        ./build.sh "${app_filename}_controller.rs" "--no-verify" $@
        echo "Building $app controller image"
        docker build -f $dockerfile -t local/$app-controller:v0.1.0 --build-arg APP=$app_filename .
    else
        echo "Use existing $app controller image"
    fi
fi

# for VDeployment, need to deploy VReplicaSet as a dependency
if [ "$app" == "vdeployment" ]; then
    if [ $build_controller == 1 ]; then
        echo "Building vreplicaset controller binary"
        ./build.sh "vreplicaset_controller.rs" "--no-verify" $@
        echo "Building vreplicaset controller image"
        docker build -f $dockerfile -t local/vreplicaset-controller:v0.1.0 --build-arg APP=vreplicaset .
    else
        echo "Use existing vreplicaset controller image"
    fi
fi

# Setup cluster, deploy the controller as a pod to the kind cluster, using the image just loaded
./deploy.sh $app local