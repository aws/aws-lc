// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

// Warn to use feature native_bindings if building on a platform where prebuilt-bindings
// aren't available
#[cfg(all(
    not(feature = "native_bindings"),
    not(any(
        all(target_os = "linux", target_arch = "x86"),
        all(target_os = "linux", target_arch = "x86_64"),
        all(target_os = "linux", target_arch = "aarch64"),
        all(target_os = "macos", target_arch = "x86_64")
    ))
))]
compile_error!("Prebuilt-bindings aren't available. Turn on feature native_bindings to build.");

#[cfg(all(feature = "native_bindings", feature = "generate"))]
compile_error!(
    "Generate is only for internal usage. Only turn on feature native_bindings to build."
);

macro_rules! use_bindings {
    ($bindings:ident) => {
        mod $bindings;
        pub use $bindings::*;
    };
}

#[cfg(all(
    not(feature = "native_bindings"),
    target_os = "linux",
    target_arch = "x86"
))]
use_bindings!(linux_x86_bindings);

#[cfg(all(
    not(feature = "native_bindings"),
    target_os = "linux",
    target_arch = "x86_64"
))]
use_bindings!(linux_x86_64_bindings);

#[cfg(all(
    not(feature = "native_bindings"),
    target_os = "linux",
    target_arch = "aarch64"
))]
use_bindings!(linux_aarch64_bindings);

#[cfg(all(
    not(feature = "native_bindings"),
    target_os = "macos",
    target_arch = "x86_64"
))]
use_bindings!(macos_x86_64_bindings);

#[cfg(feature = "native_bindings")]
use_bindings!(bindings);

#[allow(non_snake_case)]
/// # Safety
///
/// No special precaution required to call this method.
pub unsafe fn ERR_GET_LIB(packed_error: u32) -> i32 {
    ERR_GET_LIB_RUST(packed_error)
}

#[allow(non_snake_case)]
/// # Safety
///
/// No special precaution required to call this method.
pub unsafe fn ERR_GET_REASON(packed_error: u32) -> i32 {
    ERR_GET_REASON_RUST(packed_error)
}

#[allow(non_snake_case)]
/// # Safety
///
/// No special precaution required to call this method.
pub unsafe fn ERR_GET_FUNC(packed_error: u32) -> i32 {
    ERR_GET_FUNC_RUST(packed_error)
}
