aws-lc-sys
============

Low-level AWS-LC bindings crate for Rust.

### How it works
`aws-lc-sys` uses `bindgen` to generate Rust compatibility shims for the targeted platform. It is important to generate it for the correct platform because `bindgen` uses LLVM information for alignment which varies depending on architecture.

### To Use
The `aws-lc-sys` create can be built by running the [generate.sh](./generate/generate.sh) script. 
The script requires the [docker images](../../tests/ci/docker_images/rust) to 
be [built](../../tests/ci/docker_images/rust/build_images.sh) and available locally.

See AWS-LC build documentation for more details: https://github.com/awslabs/aws-lc/blob/main/BUILDING.md
