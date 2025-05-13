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
cluster_name="${app}-e2e"
registry=$2 # should be either remote or local

kind get clusters | grep $cluster_name > /dev/null 2>&1
if [ $? -eq 0 ]; then
    echo -e "${YELLOW}A kind cluster named \"$cluster_name\" already exists. Deleting...${NC}"
    kind delete cluster --name $cluster_name
fi

set -xeu
# Set up the kind cluster and load the image into the cluster
kind create cluster --config deploy/kind.yaml --name $cluster_name
kind load docker-image local/$app-controller:v0.1.0 --name $cluster_name

# for VDeployment, need to deploy VReplicaSet as a dependency
if [ "$app" == "v2-vdeployment" ]; then
    kind load docker-image local/v2-vreplicaset-controller:v0.1.0 --name $cluster_name
fi

# admission controller has a different deployment process
if [ $(echo $app | awk -F'-' '{print $NF}') == "admission" ]; then
    app=${app%-admission}
    app_filename=${app_filename%_admission}
    set -o pipefail
    kubectl create -f deploy/${app_filename}/crd.yaml
    echo "Creating Webhook Server Certs"
    mkdir -p certs
    openssl genrsa -out certs/tls.key 2048
    openssl req -new -key certs/tls.key -out certs/tls.csr -subj "/CN=admission-server.default.svc"
    openssl x509 -req -extfile <(printf "subjectAltName=DNS:admission-server.default.svc") -in certs/tls.csr -signkey certs/tls.key -out certs/tls.crt

    echo "Creating Webhook Server TLS Secret"
    kubectl create secret tls admission-server-tls \
        --cert "certs/tls.crt" \
        --key "certs/tls.key"
    echo "Creating Webhook Server Deployment"
    kubectl create -f e2e/manifests/admission_server.yaml
    CA_PEM64="$(openssl base64 -A < certs/tls.crt)"
    echo "Creating K8s Webhooks"
    sed -e 's@${CA_PEM_B64}@'"$CA_PEM64"'@g' -e 's@${RESOURCE}@'"${app#v2-}"s'@g' <"manifests/admission_webhooks.yaml" | kubectl create -f -
    exit 0
fi

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
