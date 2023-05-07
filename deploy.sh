#!/usr/bin/env bash

## Deploy the example controller to Kubernetes cluster.
##
## Requires a running Kubernetes cluster and kubectl to be installed.

set -eu

YELLOW='\033[1;33m'
GREEN='\033[1;32m'
RED='\033[0;31m'
NC='\033[0m'

if cd deploy && kubectl apply -f crd.yaml && kubectl apply -f deploy.yaml && kubectl apply -f simplecr.yaml; then
    echo ""
    echo -e "${GREEN}Simple controller is deployed in your Kubernetes cluster in namespace \"simple\"."
    echo -e "${GREEN}Run \"kubectl get pod -n simple\" to check the controller pod.${NC}"
else
    echo ""
    echo -e "${RED}Cannot deploy the controller."
    echo -e "${YELLOW}Please ensure kubectl can connect to a Kubernetes cluster.${NC}"
fi
