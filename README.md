# verifiable-controllers

## Overview

This is an experimental framework to build practical, formally verified, cluster management controllers. The goal is to be able to write a controller in Rust, and have it be formally verified for correctness using the [Verus](https://github.com/secure-foundations/verus/) toolkit.

## Try it out

You cannot compile the verifiable-controllers codebase with a standard rust compiler. You need to use the rust compiler supplied by the Verus project. Follow their [installation instructions](https://github.com/secure-foundations/verus/) to do so.

### Prerequisites

* A Verus installation, using the `main` branch

### Build and run

Set `VERUS_DIR` to the path to Verus
```
export VERUS_DIR=<path-to-verus>
```

To build and verify the simple controller:
```
$: ./build.sh simple_controller.rs
```
For Mac users, you might need to manually add `ssl` to `LIBRARY_PATH` to build it.

## Documentation

Our verification approach is described [here](doc/framework_design.md).

## Contributing

The verifiable-controllers project team welcomes contributions from the community. Before you start working with verifiable-controllers, please
read our [Developer Certificate of Origin](https://cla.vmware.com/dco). All contributions to this repository must be
signed as described on that page. Your signature certifies that you wrote the patch or have the right to pass it on
as an open-source patch. For more detailed information, refer to [CONTRIBUTING.md](CONTRIBUTING.md).

## License

This project is available under an [MIT License](LICENSE).
