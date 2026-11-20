// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

//! Rust code folded into libcrypto as `bcm-rust.o` (cmake/cargo.cmake). Its
//! C-ABI functions, declared in `internal.h`, are internal to libcrypto. Those
//! that can fail return 1 on success and 0 on failure.
//!
//! CMake sets the `awslc_asm` cfg where AWS-LC builds its assembly, as
//! `OPENSSL_NO_ASM` and `ARCH` decide for C, and `awslc_no_avx` with
//! `MY_ASSEMBLER_IS_TOO_OLD_FOR_AVX`. Rust then calls the assembly C uses,
//! in bcm-rust.o's own copy (crypto/fipsmodule/CMakeLists.txt). If the cfgs
//! disagree with C, the link fails on a missing function.
//!
//! The crate is FIPS module code, built the same way in every build, so all
//! of it follows the module rules in `fips.rs`, which restrict how Rust code
//! can be written. They apply to every algorithm added later, not just
//! SHA-256. Only the integrity check and self-tests are FIPS-only: in static
//! FIPS builds on x86_64 and aarch64, CMake sets the `awslc_fips` cfg, and
//! `bcm-rust.o` becomes a FIPS module of its own.

#![no_std]
// Module code can't call memcpy or memset (fips.rs). Without no_builtins,
// LLVM turns the loops in `copy_bytes` and `zero_bytes` back into those calls.
#![no_builtins]

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

#[cfg(awslc_asm)]
mod cpu;
#[cfg(awslc_fips)]
mod fips;
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

/// Copies `src` into `dst`, which has the same length. Use it instead of
/// `copy_from_slice` wherever the length isn't a constant: that compiles to a
/// memcpy call, which FIPS module code can't make (fips.rs).
fn copy_bytes(dst: &mut [u8], src: &[u8]) {
    for (d, s) in dst.iter_mut().zip(src) {
        *d = *s;
    }
}

/// Zeroes `dst`. Use it instead of `fill(0)` wherever the length isn't a
/// constant: that compiles to a memset call (fips.rs).
fn zero_bytes(dst: &mut [u8]) {
    for d in dst {
        *d = 0;
    }
}

/// Runtime support a `no_std` staticlib must provide.
mod rt {
    #[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
    unsafe extern "C" {
        fn abort() -> !;
    }

    /// Stops the process. Module code can't call `abort` (fips.rs), so on the
    /// CPUs the module exists on, x86_64 and aarch64, this executes an
    /// undefined instruction instead. Stable Rust has no such instruction for
    /// every CPU, so other CPUs call `abort`.
    pub(crate) fn die() -> ! {
        #[cfg(target_arch = "x86_64")]
        // SAFETY: `ud2` raises an invalid-opcode exception and doesn't return.
        unsafe {
            core::arch::asm!("ud2", options(noreturn, nomem, nostack))
        }
        #[cfg(target_arch = "aarch64")]
        // SAFETY: `udf` raises an undefined-instruction exception and doesn't
        // return.
        unsafe {
            core::arch::asm!("udf #0", options(noreturn, nomem, nostack))
        }
        #[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
        // SAFETY: `abort` takes no arguments and never returns.
        unsafe {
            abort()
        }
    }

    #[panic_handler]
    fn panic(_info: &core::panic::PanicInfo<'_>) -> ! {
        die()
    }

    /// The prebuilt `core` is built for unwinding, so it refers to the
    /// personality routine even with `panic = "abort"`, and the real one needs
    /// nightly. Nothing unwinds through Rust frames here, so this one stops
    /// the process. MSVC and wasm targets don't reference it, and their fold
    /// can't make it local, so it's left out there. On windows-gnullvm the
    /// fold renames it.
    #[cfg(not(any(all(windows, target_env = "msvc"), target_family = "wasm")))]
    #[unsafe(no_mangle)]
    extern "C" fn rust_eh_personality() -> ! {
        die()
    }
}
