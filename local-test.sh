#!/usr/bin/env bash

## Test the controller locally in a kind cluster.
##
## Requires kind to be installed and the prerequisites of deploy.sh.
## Usage: ./local-test.sh <controller_name> [--no-build]

set -xeu

app=$(echo "$1" | tr '_' '-')
app_filename=$(echo "$app" | tr '-' '_')
build_controller="no"
dockerfile_path="docker/controller/Dockerfile.local"

if [ $# -gt 1 ]; then
    if  [ "$2" == "--build" ]; then # chain cargo verus build
        build_controller="local"
    elif [ "$2" == "--build-remote" ]; then
        build_controller="remote"
    fi
fi

case "$build_controller" in
    local)
        echo "Building $app controller binary"
        shift 2
        cargo verus build "${app_filename}_controller" -- "--no-verify" $@
        echo "Building $app controller image"
        docker build -f $dockerfile_path -t local/$app-controller:v0.1.0 --build-arg APP=$app_filename .
        ;;
    remote)
        echo "Building $app controller image using builder"
        dockerfile_path="docker/controller/Dockerfile.remote"
        docker build -f $dockerfile_path -t local/$app-controller:v0.1.0 --build-arg APP=$app_filename .
        ;;
    no)
        echo "Use existing $app controller image"
        ;;
esac

# for VDeployment, need to deploy VReplicaSet as a dependency
if [ "$app" == "vdeployment" ]; then
    case "$build_controller" in
        local)
            echo "Building vreplicaset controller binary"
            cargo verus build "vreplicaset_controller" -- "--no-verify" $@
            echo "Building vreplicaset controller image"
            docker build -f $dockerfile_path -t local/vreplicaset-controller:v0.1.0 --build-arg APP=vreplicaset .
            ;;
        remote)
            echo "Building vreplicaset controller image using builder"
            dockerfile_path="docker/controller/Dockerfile.remote"
            docker build -f $dockerfile_path -t local/vreplicaset-controller:v0.1.0 --build-arg APP=vreplicaset .
            ;;
        no)
            echo "Use existing vreplicaset controller image"
            ;;
    esac
fi

# Setup cluster, deploy the controller as a pod to the kind cluster, using the image just loaded
./deploy.sh $app local