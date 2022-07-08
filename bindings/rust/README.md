aws-lc-sys
============

Scripts that generate a low-level bindings crate for Rust.

### How it works
`aws-lc-sys` uses `bindgen` to generate Rust compatibility shims for the targeted platform. It is important to generate it for the correct platform because `bindgen` uses LLVM information for alignment which varies depending on architecture. These files are then packaged into a Rust crate.

### To Use
Build `boringssl` with `-DRUST_BINDINGS=<rust-triple>` and ensure that you have `bindgen` installed.

The `rust-triple` option should be one of the supported targets at https://doc.rust-lang.org/nightly/rustc/platform-support.html.

