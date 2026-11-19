// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

//! Rust code folded into libcrypto as `rust.o` (cmake/cargo.cmake). Its C-ABI
//! functions, declared in `internal.h`, are internal to libcrypto. They return
//! 1 on success and 0 on failure, and never panic across the boundary.

#![no_std]

use core::ffi::c_int;

/// Returns the sum of all bytes in `input`, wrapping on overflow.
fn byte_sum(input: &[u8]) -> u64 {
    input
        .iter()
        .fold(0u64, |acc, &b| acc.wrapping_add(u64::from(b)))
}

/// Builds a byte slice from a C pointer and length.
///
/// Returns `None` if `ptr` is NULL with a non-zero `len`, or if `len` exceeds
/// `isize::MAX`. A zero `len` yields an empty slice regardless of `ptr`, since
/// C callers commonly pass NULL for empty buffers but `from_raw_parts` forbids
/// it.
///
/// # Safety
///
/// If `len` is non-zero and `ptr` is non-NULL, `ptr` must be valid for reads
/// of `len` bytes for the lifetime `'a`, and the memory must not be mutated
/// during that lifetime.
unsafe fn slice_from_c<'a>(ptr: *const u8, len: usize) -> Option<&'a [u8]> {
    if len == 0 {
        return Some(&[]);
    }
    if ptr.is_null() || len > isize::MAX as usize {
        return None;
    }
    // SAFETY: `ptr` is non-NULL, `len` is in range, and the caller guarantees
    // `ptr` is valid for reads of `len` bytes for `'a`.
    Some(unsafe { core::slice::from_raw_parts(ptr, len) })
}

/// Writes the sum of the `input_len` bytes at `input` to `*out`.
///
/// Returns 1 on success, or 0 if `out` is NULL or `input` is NULL with a
/// non-zero `input_len`.
///
/// # Safety
///
/// `input` must be NULL or valid for reads of `input_len` bytes. `out` must be
/// NULL or valid for writing a `uint64_t`.
// rustc doesn't see the BORINGSSL_PREFIX headers, so in a prefix build CMake
// sets the `awslc_prefix` cfg and the BORINGSSL_PREFIX environment variable,
// and the function takes the prefixed name internal.h gives it.
#[cfg_attr(not(awslc_prefix), unsafe(no_mangle))]
#[cfg_attr(
    awslc_prefix,
    unsafe(export_name = concat!(env!("BORINGSSL_PREFIX"), "_caracal_byte_sum"))
)]
pub unsafe extern "C" fn caracal_byte_sum(
    input: *const u8,
    input_len: usize,
    out: *mut u64,
) -> c_int {
    if out.is_null() {
        return 0;
    }
    // SAFETY: forwarded from this function's contract.
    let Some(input) = (unsafe { slice_from_c(input, input_len) }) else {
        return 0;
    };
    // SAFETY: `out` is non-NULL and the caller guarantees it is writable.
    unsafe { out.write(byte_sum(input)) };
    1
}

/// Runtime support a `no_std` staticlib must provide.
mod rt {
    unsafe extern "C" {
        fn abort() -> !;
    }

    #[panic_handler]
    fn panic(_info: &core::panic::PanicInfo<'_>) -> ! {
        // SAFETY: `abort` takes no arguments and never returns.
        unsafe { abort() }
    }

    /// The prebuilt `core` is built for unwinding, so it refers to the
    /// personality routine even with `panic = "abort"`, and the real one needs
    /// nightly. Nothing unwinds through Rust frames here, so this one aborts.
    /// MSVC and wasm targets don't reference it, and their fold can't make it
    /// local, so it's left out there. On windows-gnullvm the fold renames it.
    #[cfg(not(any(all(windows, target_env = "msvc"), target_family = "wasm")))]
    #[unsafe(no_mangle)]
    extern "C" fn rust_eh_personality() -> ! {
        // SAFETY: `abort` takes no arguments and never returns.
        unsafe { abort() }
    }
}
