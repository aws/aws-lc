// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#[cfg(all(not(feature = "bindgen"), target_os = "linux", target_arch = "x86"))]
pub use linux_x86_bindings::*;
#[cfg(all(not(feature = "bindgen"), target_os = "linux", target_arch = "x86"))]
mod linux_x86_bindings;

#[cfg(all(not(feature = "bindgen"), target_os = "linux", target_arch = "x86_64"))]
pub use linux_x86_64_bindings::*;
#[cfg(all(not(feature = "bindgen"), target_os = "linux", target_arch = "x86_64"))]
mod linux_x86_64_bindings;

#[cfg(all(not(feature = "bindgen"), target_os = "linux", target_arch = "aarch64"))]
pub use linux_aarch64_bindings::*;
#[cfg(all(not(feature = "bindgen"), target_os = "linux", target_arch = "aarch64"))]
mod linux_aarch64_bindings;

#[cfg(all(not(feature = "bindgen"), target_os = "macos", target_arch = "x86_64"))]
pub use macos_x86_64_bindings::*;
#[cfg(all(not(feature = "bindgen"), target_os = "macos", target_arch = "x86_64"))]
mod macos_x86_64_bindings;

#[cfg(feature = "bindgen")]
pub use bindings::*;
#[cfg(feature = "bindgen")]
mod bindings;

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
