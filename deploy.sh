#!/usr/bin/env bash

## Deploy the example controller to Kubernetes cluster.
##
## Requires a running Kubernetes cluster and kubectl to be installed.

set -eu

YELLOW='\033[1;33m'
GREEN='\033[1;32m'
RED='\033[0;31m'
NC='\033[0m'

if [ "$1" = "simple" ]; then
    if cd deploy/simple && kubectl apply -f crd.yaml && kubectl apply -f deploy.yaml; then
        echo ""
        echo -e "${GREEN}Simple controller is deployed in your Kubernetes cluster in namespace \"simple\"."
        echo -e "Run \"kubectl get pod -n simple\" to check the controller pod."
        echo -e "Run \"kubectl apply -f deploy/simple/simplecr.yaml\" to deploy a simple custom resource.${NC}"
    else
        echo ""
        echo -e "${RED}Cannot deploy the controller."
        echo -e "${YELLOW}Please ensure kubectl can connect to a Kubernetes cluster.${NC}"
    fi
elif [ "$1" = "zookeeper" ]; then
    if cd deploy/zookeeper && kubectl apply -f crd.yaml && kubectl apply -f deploy.yaml; then
        echo ""
        echo -e "${GREEN}Zookeeper controller is deployed in your Kubernetes cluster in namespace \"zookeeper\"."
        echo -e "Run \"kubectl get pod -n zookeeper\" to check the controller pod."
        echo -e "Run \"kubectl apply -f deploy/zookeeper/zookeeper.yaml\" to deploy a zookeeper cluster custom resource.${NC}"
    else
        echo ""
        echo -e "${RED}Cannot deploy the controller."
        echo -e "${YELLOW}Please ensure kubectl can connect to a Kubernetes cluster.${NC}"
    fi
elif [ "$1" = "rabbitmq" ]; then
    if cd deploy/rabbitmq && kubectl apply -f crd.yaml && kubectl apply -f deploy.yaml; then
        echo ""
        echo -e "${GREEN}Rabbitmq controller is deployed in your Kubernetes cluster in namespace \"rabbitmq\"."
        echo -e "Run \"kubectl get pod -n rabbitmq\" to check the controller pod."
        echo -e "Run \"kubectl apply -f deploy/rabbitmq/rabbitmq.yaml\" to deploy a rabbitmq cluster custom resource.${NC}"
    else
        echo ""
        echo -e "${RED}Cannot deploy the controller."
        echo -e "${YELLOW}Please ensure kubectl can connect to a Kubernetes cluster.${NC}"
    fi
else
    echo -e "${RED}Unsupported app name."
    echo -e "${YELLOW}Currently supported app: simple.${NC}"
fi
