#!/usr/bin/env bash

## Test the controller locally in a kind cluster.
##
## Requires kind to be installed and the prerequisites of deploy.sh.

set -xeu

app=$1

# Copy the Dockerfile and build the docker image of the controller
cp docker/controller/Dockerfile .
docker build -t local/$app-controller:v0.1.0 --build-arg APP=$app .
rm Dockerfile
# Set up the kind cluster and load the image into the cluster
kind create cluster --config deploy/kind.yaml
kind load docker-image local/$app-controller:v0.1.0
# Deploy the controller as a pod to the kind cluster, using the image just loaded
./deploy.sh $app local
