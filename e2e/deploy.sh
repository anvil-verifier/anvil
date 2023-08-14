#!/usr/bin/env bash

## Deploy the example controller to Kubernetes cluster.
##
## Requires a running Kubernetes cluster and kubectl to be installed.

set -eu

YELLOW='\033[1;33m'
GREEN='\033[1;32m'
RED='\033[0;31m'
NC='\033[0m'

if [ "$1" = "zookeeper" ]; then
    if kubectl apply -f ./deploy/zookeeper/crd.yaml && kubectl apply -f ./e2e/deploy/deploy_zookeeper.yaml; then
        echo ""
        echo -e "${GREEN}Zookeeper controller is deployed in your Kubernetes cluster in namespace \"zookeeper\"."
    else
        echo ""
        echo -e "${RED}Cannot deploy the controller."
        echo -e "${YELLOW}Please ensure kubectl can connect to a Kubernetes cluster.${NC}"
    fi
elif [ "$1" = "rabbitmq" ]; then
    if kubectl apply -f ./deploy/rabbitmq/crd.yaml && kubectl apply -f ./e2e/deploy/deploy_rabbitmq.yaml; then
        echo ""
        echo -e "${GREEN}Rabbitmq controller is deployed in your Kubernetes cluster in namespace \"rabbitmq\"."
    else
        echo ""
        echo -e "${RED}Cannot deploy the controller."
        echo -e "${YELLOW}Please ensure kubectl can connect to a Kubernetes cluster.${NC}"
    fi
else
    echo -e "${RED}Unsupported app name."
    echo -e "${YELLOW}Currently supported app: simple.${NC}"
fi
