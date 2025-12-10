# How to build, verify and run controller

## Code Structure

```shell
.
├── build.sh # build controller only
├── deploy
│   └── <controller_name>
│       └── <configuration files>
├── deploy.sh # subscript for e2e test
├── docker
│   └── controller
│       └── Dockerfile
├── e2e
│   └── src
├── local-test.sh # build and perform e2e test
├── src
│   └── <controller_name>_controller.rs
├──...
```

Controller source should be put in `src/`, with e2e test in `e2e/src` and test workload specified in `deploy/`

### Dependencies

```shell
# kubernetes version: v1.30
verus_release: release/rolling/0.2025.11.30.840fa61
kind_version: 0.23.0
go_version: "^1.20"
```

## Build and Verify

- add Verus to $PATH

- `./build.sh <controller_name.rs> [other verus arguments]` 

Make sure `<controller_name>` corresponds to entry file in `src`

> More argument usage by `verus --help`

## Build and Test

### Build controller only

`./build.sh <controller_name.rs> [--no-verify] [other verus arguments]`

`--no-verify` is optional for fast build. Controller built without this option from the section above can be directly used, but verifications could take long time.

### Test pipeline

1. Build controller binary by `build.sh`
2. Build controller docker image

   Base image and builder image is specified in `docker/controller/Dockerfile.[local|remote]` respectively
3. Setup cluster, apply controller image using [kind](https://kind.sigs.k8s.io/).
4. Apply test specified in `e2e/src` and workload in `deploy` by `deploy.sh`

This process can be automated with:

**1-3**

```
./local-test.sh <controller_name> [--build|--build-remote]
Usage:
	--build:		Call ./build.sh to build the controller before test, should have VERUS_DIR speccified
	<empty>:		Just use existing built controller image to set up kind cluster. Assume the image is named as `local/$app-controller:v0.1.0`
```

If deployment/test failed, you can manually run `./deploy.sh <controller_name> [local|remote]` to reset the e2e test environment.

**4**
```
cd e2e
cargo run -- <controller_name>
```

> More examples in `.github/workflows/ci.yml`
