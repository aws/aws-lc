// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use std::mem::MaybeUninit;
use aws_lc_sys;

use openssl;

fn sha1_tester(input: &[u8]) -> [u8; 20] {
    let mut hash = MaybeUninit::<[u8; 20]>::uninit();

    unsafe {
        aws_lc_sys::SHA1(input.as_ptr(), input.len(), hash.as_mut_ptr().cast());
        hash.assume_init()
    }
}

fn compare(result: &[u8], expected_result: &[u8]) {
    println!("Comparing: {:?} to {:?}", result, expected_result);
    assert_eq!(result, expected_result);
}

#[test]
fn sha1() {
    let input1 = b"hello";
    let result1 = sha1_tester(input1);
    let openssl_result1 = openssl::sha::sha1(input1);
    compare(&result1, &openssl_result1);
}

#[test]
fn error_checking() {
    unsafe {
        let error = aws_lc_sys::ERR_get_error();
        let err_lib = aws_lc_sys::ERR_GET_LIB(error);
        let err_reason = aws_lc_sys::ERR_GET_REASON(error);
        let err_func = aws_lc_sys::ERR_GET_FUNC(error);
        assert_eq!(err_lib, 0);
        assert_eq!(err_reason, 0);
        assert_eq!(err_func, 0);
    }
}
