// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

use std::ffi::{c_char, c_long, c_void};

// Warn to use feature generate_bindings if building on a platform where prebuilt-bindings
// aren't available
#[cfg(all(not(feature = "bindgen"), not_pregenerated))]
compile_error!("The FIPS static build is not supported on this platform.");

macro_rules! use_bindings {
    ($bindings:ident) => {
        mod $bindings;
        pub use $bindings::*;
    };
}

#[cfg(linux_x86_64_bindings)]
use_bindings!(linux_x86_64_bindings);

#[cfg(linux_aarch64_bindings)]
use_bindings!(linux_aarch64_bindings);

#[cfg(feature = "bindgen")]
use_bindings!(bindings);

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
