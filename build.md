# How to build, verify and run controller

## Code Structure

```
.
├── build.md
├── build.sh
├── deploy
│   ├── ...
├── deploy.sh
├── docker
│   ├── controller
│   │   ├── Dockerfile.local
│   │   └── Dockerfile.remote
├── e2e
│   └── src
├── local-test.sh
├── src
│   └── <controller_name>_controller.rs
├──...
```

Controller source should be put in `src/`, with e2e test in `e2e/src` and test workload specified in `deploy/`

### Dependencies

```
verus_commit: 6b278074651d520825ea62fe2079ed1e3959cb69
kind_version: 0.23.0
go_version: "^1.20"
```

> Please refer to `.github/workflows/ci.yml` for the most recent versions used.

## Build and Verify

 `VERUS_DIR=../verus ./build.sh <controller_name.rs> [other verus arguments]` 

Make sure `VERUS_DIR` points to verus repo location and built binary exists, `<controller_name>` corresponds to entry file in `src`

> More argument usage by `verus --help`

## Build and Test

### Build controller only

`VERUS_DIR=../verus ./build.sh <controller_name.rs> [--no-verify] [other verus arguments]`

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
	--build-remote:		Call ./build.sh to build the controller image using Verus builder. This is useful when host has different runtime environment from image (Ubuntu 22.04), for example, different glibc version
	unspecified:		Just use existing built controller image to set up kind cluster. Assume the image is named as `local/$app-controller:v0.1.0`
```

If deployment/test failed, you can manually run `./deploy.sh <controller_name> [local|remote]` to reset the e2e test environment.

**4**
```
cd e2e
cargo run -- <controller_name>
```

> More examples in `.github/workflows/ci.yml`
