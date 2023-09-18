#!/usr/bin/env bash

## Deploy the example controller to Kubernetes cluster.
##
## Requires a running Kubernetes cluster and kubectl to be installed.

set -xeu

YELLOW='\033[1;33m'
GREEN='\033[1;32m'
RED='\033[0;31m'
NC='\033[0m'

app=$1
registry=$2

if [ "$app" != "zookeeper" ] && [ "$app" != "rabbitmq" ] && [ "$app" != "fluent" ]; then
    echo -e "${RED}The first argument has to be one of: zookeeper, rabbitmq, fluent.${NC}"
    exit 1    
fi

if [ "$registry" != "remote" ] && [ "$registry" != "local" ]; then
    echo -e "${RED}The second argument has to be one of: remote, local.${NC}"
    exit 2
fi

if cd deploy/$1 && kubectl apply -f crd.yaml && kubectl apply -f rbac.yaml && kubectl apply -f deploy_$registry.yaml; then
    echo ""
    echo -e "${GREEN}The $app controller is deployed in your Kubernetes cluster in namespace \"$app\"."
    echo -e "Run \"kubectl get pod -n $app\" to check the controller pod."
    echo -e "Run \"kubectl apply -f deploy/$app/$app.yaml\" to deploy the cluster custom resource(s).${NC}"
else
    echo ""
    echo -e "${RED}Cannot deploy the controller."
    echo -e "${YELLOW}Please ensure kubectl can connect to a Kubernetes cluster.${NC}"
    exit 3
fi
