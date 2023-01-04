// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

use paste::paste;
use std::os::raw::{c_long, c_char, c_void};

// Warn to use feature generate_bindings if building on a platform where prebuilt-bindings
// aren't available
#[cfg(all(not(feature = "bindgen"), not_pregenerated))]
compile_error!("Prebuilt-bindings aren't available. Turn on feature generate_bindings to build.");

#[cfg(all(feature = "generate_bindings", feature = "internal_generate"))]
compile_error!(
    "internal_generate is only for internal usage and does not work with the generate_bindings feature."
);

#[allow(unused_macros)]
macro_rules! use_bindings {
    ($bindings:ident) => {
        mod $bindings;
        pub use $bindings::*;
    };
}

macro_rules! platform_binding {
    ($platform:ident) => {
        paste! {
            #[cfg(all($platform, not(feature = "ssl")))]
            use_bindings!([< $platform _crypto >]);

            #[cfg(all($platform, feature = "ssl"))]
            use_bindings!([< $platform _crypto_ssl >]);
        }
    };
}

platform_binding!(linux_x86);

platform_binding!(linux_x86_64);

platform_binding!(linux_aarch64);

platform_binding!(macos_x86_64);

#[cfg(all(feature = "bindgen", not_pregenerated))]
mod generated {
    #![allow(
        unused_imports,
        non_camel_case_types,
        non_snake_case,
        non_upper_case_globals,
        improper_ctypes
    )]

    include!(concat!(env!("OUT_DIR"), "/bindings.rs"));
}
#[cfg(all(feature = "bindgen", not_pregenerated))]
pub use generated::*;

#[allow(non_snake_case)]
pub fn ERR_GET_LIB(packed_error: u32) -> i32 {
    unsafe { ERR_GET_LIB_RUST(packed_error) }
}

#[allow(non_snake_case)]
pub fn ERR_GET_REASON(packed_error: u32) -> i32 {
    unsafe { ERR_GET_REASON_RUST(packed_error) }
}

#[allow(non_snake_case)]
pub fn ERR_GET_FUNC(packed_error: u32) -> i32 {
    unsafe { ERR_GET_FUNC_RUST(packed_error) }
}

#[allow(non_snake_case)]
pub fn BIO_get_mem_data(b: *mut BIO, pp: *mut *mut c_char) -> c_long {
    unsafe { BIO_ctrl(b, BIO_CTRL_INFO, 0, pp as *mut c_void) }
}

pub fn init() {
    unsafe { CRYPTO_library_init() }
}
