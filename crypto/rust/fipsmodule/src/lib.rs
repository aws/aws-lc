// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

//! Rust code in the FIPS module, `bcm.o` (cmake/cargo.cmake). Its C-ABI
//! functions, declared in `internal.h`, are called by the module's C code and
//! are internal to libcrypto. Those that can fail return 1 on success and 0 on
//! failure.
//!
//! Static FIPS builds compile the crate to assembly, which delocate takes into
//! `bcm.o` with `bcm.c`'s. Shared FIPS builds link its object into `bcm.o`,
//! and other builds fold it into libcrypto as `bcm-rust.o`, beside `bcm.c`'s
//! object. Module code follows C's module rules in every build, because
//! delocate enforces them in static FIPS builds:
//!
//! - mutable statics start zeroed and are reached only through
//!   `<name>_bss_get()`, which delocate writes, as with C's `DEFINE_BSS_GET`
//! - no statics holding pointers, such as function tables or the vtables of
//!   trait objects: delocate can't move them into the module, so it rejects
//!   them
//!
//! Calls the compiler inserts, such as `memcpy`, need no rule: delocate sends
//! them through its redirectors, as it does C's.

#![no_std]

/// The C name of `name`, for `export_name` and `link_name`. rustc doesn't see
/// the BORINGSSL_PREFIX headers, so in a prefix build CMake sets the
/// `awslc_prefix` cfg and the BORINGSSL_PREFIX environment variable, and the
/// name takes the prefix, as `internal.h` and the C code give it.
#[cfg(not(awslc_prefix))]
macro_rules! c_name {
    ($name:expr) => {
        $name
    };
}
#[cfg(awslc_prefix)]
macro_rules! c_name {
    ($name:expr) => {
        concat!(env!("BORINGSSL_PREFIX"), "_", $name)
    };
}

mod sha256;

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
