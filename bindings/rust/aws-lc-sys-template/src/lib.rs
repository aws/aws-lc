// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

mod bindings;
pub use bindings::*;

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

pub fn init() {
    unsafe { CRYPTO_library_init() }
}
