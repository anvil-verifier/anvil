# CS523 Anvil Admission Controller

## Requirements
Before setting up, make sure the following tools are installed. The listed versions are what worked during testing but may vary based on your environment.

- `kubectl` (v1.32.2) – Kubernetes CLI
- `kind` (v0.27.0) – Running Kubernetes in Docker
- `Docker` (27.2.1) – Container runtime

## Setup

Follow these steps to set up and test the Deployment admission controller.



1. Start a Kubernetes Cluster

You can use any Kubernetes cluster, but this setup assumes you're using **kind**.
```bash
kind create cluster
```

2. Build the Docker Image

Build the container image for the admission controller, ensuring it is tagged as `admission_controller:v1`:
```bash
docker build -t local/vdeployment-admission-controller:v0.1.0 -f docker/Dockerfile .
```

3. Load the image into `kind`

Since kind runs Kubernetes inside Docker, the image must be explicitly loaded into the cluster:
```bash
kind load docker-image local/vdeployment-admission-controller:v0.1.0
```

4. Run the setup script

The setup script generates TLS certificates and applies the necessary Kubernetes configurations.
```bash
./setup.sh
```

5.  Verify the Admission Controller

You can test the admission controller using the provided manifests:
```bash
kubectl apply -f manifests/deployment/ok.yaml # should succeed
kubectl apply -f manifests/deployment/negative_replicas.yaml # should show "admission webhook "admission-server.default.svc" denied the request:..."
```
We also provide an automated testing suite for every manifest provided. Make sure to have a fresh local deployment. To execute, run:
```bash
cd tests
cargo run
```
