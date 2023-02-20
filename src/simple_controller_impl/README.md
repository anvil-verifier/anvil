## How to run the simple controller

You will need `kind` and `kubectl` installed
```bash
./setup # Set up a local Kubernetes cluster and install the CRD in it
cargo run
```
then you create the CR object
```bash
kubectl apply -f simple_cr.yaml
```
The simple controller will create a configmap for this cr.
To check it, you can query the configmaps in the Kubernetes API
```bash
kubectl get cm
```
and you will see the `foo-cm` created by the controller
```
NAME               DATA   AGE
foo-cm             0      7s
kube-root-ca.crt   1      3m16s
```
Remember to shut down the local Kubernetes cluster by `kind delete cluster`.
