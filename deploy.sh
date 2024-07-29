#!/usr/bin/env bash

## Deploy the example controller to Kubernetes cluster.
##
## Requires a running Kubernetes cluster and kubectl to be installed.

set -xeu

YELLOW='\033[1;33m'
GREEN='\033[1;32m'
RED='\033[0;31m'
NC='\033[0m'

app=$1 # should be the controller's name
registry=$2 # should be either remote or local

## use imperative management for CRDs since metadata for PodTemplateSpec is too long.
if cd deploy/$1 && kubectl create -f crd.yaml && kubectl apply -f rbac.yaml && kubectl apply -f deploy_$registry.yaml; then
    echo ""
    echo -e "${GREEN}The $app controller is deployed in your Kubernetes cluster in namespace \"$app\".${NC}"
    echo -e "${GREEN}Run \"kubectl get pod -n $app\" to check the controller pod.${NC}"
    echo -e "${GREEN}Run \"kubectl apply -f deploy/$app/$app.yaml\" to deploy the cluster custom resource(s).${NC}"
else
    echo ""
    echo -e "${RED}Cannot deploy the controller.${NC}"
    echo -e "${YELLOW}Please ensure kubectl can connect to a Kubernetes cluster.${NC}"
    exit 3
fi
