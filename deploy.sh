#!/usr/bin/env bash

## Deploy the example controller to Kubernetes cluster.
##
## Requires a running Kubernetes cluster and kubectl to be installed.

set -xu

YELLOW='\033[1;33m'
GREEN='\033[1;32m'
RED='\033[0;31m'
NC='\033[0m'

app=$(echo "$1" | tr '_' '-') # should be the controller's name (with words separated by dashes)
app_filename=$(echo "$app" | tr '-' '_')
registry=$2 # should be either remote or local

kind get clusters | grep e2e > /dev/null 2>&1
if [ $? -eq 0 ]; then
    echo -e "${YELLOW}A kind cluster named \"e2e\" already exists. Deleting...${NC}"
    kind delete cluster --name e2e
fi

set -xeu
# Set up the kind cluster and load the image into the cluster
kind create cluster --config deploy/kind.yaml
kind load docker-image local/$app-controller:v0.1.0 --name e2e

# for VDeployment, need to deploy VReplicaSet as a dependency
if [ "$app" == "v2-vdeployment" ]; then
    kind load docker-image local/v2-vreplicaset-controller:v0.1.0 --name e2e
fi

if [ "$app" == "v2-vreplicaset-admission" ]; then
    cd src/v2/controllers/vreplicaset_controller/admission_control && ./setup.sh
    exit 0
fi

# use imperative management for CRDs since metadata for PodTemplateSpec is too long.
# why don't we directly create CRD using kube API?
if cd deploy/$app_filename && { for crd in $(ls crd*.yaml); do kubectl create -f "$crd"; done } && kubectl apply -f rbac.yaml && kubectl apply -f deploy_$registry.yaml; then
    echo ""
    echo -e "${GREEN}The $app controller is deployed in your Kubernetes cluster in namespace \"$app\".${NC}"
    echo -e "${GREEN}Run \"kubectl get pod -n $app\" to check the controller pod.${NC}"
    echo -e "${GREEN}Run \"kubectl apply -f deploy/$app_filename/$app_filename.yaml\" to deploy the cluster custom resource(s).${NC}"
else
    echo ""
    echo -e "${RED}Cannot deploy the controller.${NC}"
    echo -e "${YELLOW}Please ensure kubectl can connect to a Kubernetes cluster.${NC}"
    exit 3
fi
