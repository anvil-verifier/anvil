#! /usr/bin/env bash
set -euo pipefail

# first argument is resource crd folder name e.g. v2_vreplicaset
# second argument is the name of the resource e.g. vreplicasets
# this can be simplified into one argument if the naming of the crd
# consistently matches the resource name e.g. always v2_$resource_name

# Cleanup: Remove old if exists (immutable)
echo "Cleaning up"
kubectl delete -f manifests/admission_webhooks.yaml || true
kubectl delete -f manifests/admission_server.yaml || true
kubectl -n default delete secret admission-server-tls || true

kubectl create -f ../deploy/$1/crd.yaml || true

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
kubectl create -f manifests/admission_server.yaml

CA_PEM64="$(openssl base64 -A < certs/tls.crt)"

echo "Creating K8s Webhooks"
sed -e 's@${CA_PEM_B64}@'"$CA_PEM64"'@g' -e 's@${RESOURCE}@'"$2"'@g' <"manifests/admission_webhooks.yaml" | kubectl create -f -