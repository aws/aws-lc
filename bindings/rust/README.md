aws-lc-sys
============

Low-level AWS-LC bindings crate for Rust.

### How it works
`aws-lc-sys` uses `bindgen` to generate Rust compatibility shims for the targeted platform. It is important to generate it for the correct platform because `bindgen` uses LLVM information for alignment which varies depending on architecture.

### To Use
The build requires `cmake` (>= 3.0) and other standard development tools to compile the native library. See AWS-LC documentation for more details: https://github.com/awslabs/aws-lc/blob/main/BUILDING.md
