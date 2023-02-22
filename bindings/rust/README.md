aws-lc-sys
============

Low-level AWS-LC bindings crate for Rust.

### How it works
`aws-lc-sys` uses `bindgen` to generate Rust compatibility shims for the targeted platform. It is important to generate it for the correct platform because `bindgen` uses LLVM information for alignment which varies depending on architecture.

### Installation

In order to generate the `aws-lc-sys` crate, you need to have the following installed:

* Rust - installable with [rustup](https://rustup.rs/)
* libclang
* docker
* C compilation tools to build AWS-LC. We pull in [generated-src](https://github.com/aws/aws-lc/tree/main/generated-src) into `aws-lc-sys`, so Go and Perl aren't needed (for non-FIPS).
* CMake3 or above. [`cmake-rs`](https://docs.rs/cmake/latest/cmake/) appends build options after the path, which isn't supported in older versions of cmake.

### To Use
The `aws-lc-sys` create can be built by running the [generate.sh](./generate/generate.sh) script. 
The script requires the [docker images](../../tests/ci/docker_images/rust) to 
be [built](../../tests/ci/docker_images/rust/build_images.sh) and available locally. Bindings for `macos-x86_64` are generated on the native MacOS x86_64 platform. Bindings are generated for `linux-x86_64`, `linux-aarch64`, `linux-x86` using the corresponding docker images.

```
./bindings/rust/generate/generate.sh
```

See AWS-LC build documentation for more details: https://github.com/aws/aws-lc/blob/main/BUILDING.md

### Publishing
The `aws-lc-sys` crate should be fully generated and tested by running the [generate.sh](./generate/generate.sh) script, prior to publishing.
The following need to be done in order to publish:
* Log in via `cargo login`: requires API token generation from https://crates.io/settings/tokens
* `cargo install cargo-public-api`

```
./bindings/rust/publish/publish.sh
```
