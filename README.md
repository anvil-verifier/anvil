[![License](https://img.shields.io/badge/License-MIT-green.svg)](https://github.com/vmware-research/verifiable-controllers/blob/main/LICENSE)
[![ci](https://github.com/vmware-research/verifiable-controllers/actions/workflows/ci.yml/badge.svg)](https://github.com/vmware-research/verifiable-controllers/actions/workflows/ci.yml)
[![verus build](https://github.com/vmware-research/verifiable-controllers/actions/workflows/verus-build.yml/badge.svg)](https://github.com/vmware-research/verifiable-controllers/actions/workflows/verus-build.yml)
[![controller build](https://github.com/vmware-research/verifiable-controllers/actions/workflows/controller-build.yml/badge.svg)](https://github.com/vmware-research/verifiable-controllers/actions/workflows/controller-build.yml)
[![controller e2e test](https://github.com/vmware-research/verifiable-controllers/actions/workflows/controller-e2e-test.yml/badge.svg)](https://github.com/vmware-research/verifiable-controllers/actions/workflows/controller-e2e-test.yml)

# verifiable-controllers

## Overview

This is an experimental framework to build practical, formally verified, cluster management controllers. The goal is to be able to write a controller in Rust, and have it be formally verified for correctness using the [Verus](https://github.com/secure-foundations/verus/) toolkit.

## Try it out

You cannot compile the verifiable-controllers codebase with a standard rust compiler. You need to use the rust compiler supplied by the Verus project. Follow their [installation instructions](https://github.com/secure-foundations/verus/) to do so.

### Prerequisites

* A Verus installation, using the `main` branch

### Build the verified Zookeeper controller

Set `VERUS_DIR` to the path to Verus
```
export VERUS_DIR=<path-to-verus>
```

To build and verify the zookeeper controller:
```
$: ./build.sh zookeeper_controller.rs -o zookeeper-controller
```
For Mac users, you might need to manually add `ssl` to `LIBRARY_PATH` to build it.

### Deploy the verified Zookeeper controller

To deploy the verified zookeeper controller to a Kubernetes cluster:
```
$: ./deploy.sh zookeeper
```
This script will deploy the zookeeper controller image (hosted at [our repo](https://github.com/vmware-research/verifiable-controllers/packages)) inside your Kubernetes cluster.

## Documentation

Our verification approach is described [here](doc/framework_design.md).

## Contributing

The verifiable-controllers project team welcomes contributions from the community. Before you start working with verifiable-controllers, please
read our [Developer Certificate of Origin](https://cla.vmware.com/dco). All contributions to this repository must be
signed as described on that page. Your signature certifies that you wrote the patch or have the right to pass it on
as an open-source patch. For more detailed information, refer to [CONTRIBUTING.md](CONTRIBUTING.md).

## License

This project is available under an [MIT License](LICENSE).
