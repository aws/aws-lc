use std::mem::MaybeUninit;
use Vec;
use aws_lc_sys;

use sha1::{Sha1, Digest};

fn sha1_tester(input: &[u8]) -> [u8; 20] {
    let mut hash = MaybeUninit::<[u8; 20]>::uninit();

    unsafe {
        aws_lc_sys::SHA1(input.as_ptr(), input.len(), hash.as_mut_ptr().cast());
        hash.assume_init()
    }
}

fn compare(result: &[u8], expected_result: &[u8]) {
    //println!("Comparing: {:?} to {:?}", result, expected_result);
    assert_eq!(Vec::from(result), Vec::from(expected_result));
}

#[test]
fn sha1() {
    let input1 = b"hello";
    let result1 = sha1_tester(input1);
    let expected_result1 = Sha1::digest(input1);
    compare(&result1, &expected_result1);
}

#[test]
fn initialize() {
    aws_lc_sys::init();
}