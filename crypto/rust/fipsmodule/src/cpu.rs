// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

//! AWS-LC's CPU capability flags, which C's `OPENSSL_cpuid_setup` fills in
//! (`crypto/fipsmodule/cpucap`). Rust reads the same flags as C, so the
//! `OPENSSL_ia32cap` and `OPENSSL_armcap` overrides reach it too, and repeats
//! the tests C's SHA-256 dispatch makes (`crypto/fipsmodule/sha/internal.h`
//! and `cpucap/internal.h`). The flags are atomics here because C writes them
//! while Rust may hold a reference; C writes them only once, at startup.

#[cfg(any(target_arch = "x86_64", target_arch = "x86"))]
mod flags {
    use core::sync::atomic::{AtomicU32, Ordering};

    unsafe extern "C" {
        #[link_name = c_name!("OPENSSL_ia32cap_P")]
        static OPENSSL_ia32cap_P: [AtomicU32; 4];
    }

    /// Word `i` of `OPENSSL_ia32cap_P`.
    fn word(i: usize) -> u32 {
        // SAFETY: C defines `OPENSSL_ia32cap_P` as four `uint32_t`, which
        // have AtomicU32's layout.
        unsafe { OPENSSL_ia32cap_P[i].load(Ordering::Relaxed) }
    }

    // CRYPTO_is_*_capable in cpucap/internal.h.
    #[cfg(target_arch = "x86")]
    fn fxsr() -> bool {
        word(0) & (1 << 24) != 0
    }
    #[cfg(not(awslc_no_avx))]
    fn intel() -> bool {
        word(0) & (1 << 30) != 0
    }
    fn ssse3() -> bool {
        word(1) & (1 << 9) != 0
    }
    #[cfg(not(awslc_no_avx))]
    fn avx() -> bool {
        word(1) & (1 << 28) != 0
    }
    #[cfg(target_arch = "x86_64")]
    fn shaext() -> bool {
        word(2) & (1 << 29) != 0
    }

    // sha256_*_capable in sha/internal.h.
    #[cfg(target_arch = "x86_64")]
    pub(crate) fn sha256_hw_capable() -> bool {
        shaext()
    }
    #[cfg(all(target_arch = "x86_64", not(awslc_no_avx)))]
    pub(crate) fn sha256_avx_capable() -> bool {
        avx() && ssse3() && intel()
    }
    #[cfg(target_arch = "x86_64")]
    pub(crate) fn sha256_ssse3_capable() -> bool {
        ssse3()
    }
    #[cfg(all(target_arch = "x86", not(awslc_no_avx)))]
    pub(crate) fn sha256_avx_capable() -> bool {
        avx() && intel() && fxsr()
    }
    #[cfg(target_arch = "x86")]
    pub(crate) fn sha256_ssse3_capable() -> bool {
        ssse3() && fxsr()
    }
}

#[cfg(any(target_arch = "aarch64", target_arch = "arm"))]
mod flags {
    use core::sync::atomic::{AtomicU32, Ordering};

    unsafe extern "C" {
        #[link_name = c_name!("OPENSSL_armcap_P")]
        static OPENSSL_armcap_P: AtomicU32;
    }

    // include/openssl/arm_arch.h.
    #[cfg(target_arch = "arm")]
    const ARMV7_NEON: u32 = 1 << 0;
    const ARMV8_SHA256: u32 = 1 << 4;

    fn armcap() -> u32 {
        // SAFETY: C defines `OPENSSL_armcap_P` as a `uint32_t`, which has
        // AtomicU32's layout.
        unsafe { OPENSSL_armcap_P.load(Ordering::Relaxed) }
    }

    // CRYPTO_is_NEON_capable and CRYPTO_is_ARMv8_SHA256_capable in
    // cpucap/internal.h.
    #[cfg(target_arch = "arm")]
    pub(crate) fn neon_capable() -> bool {
        armcap() & ARMV7_NEON != 0
    }
    pub(crate) fn sha256_hw_capable() -> bool {
        armcap() & ARMV8_SHA256 != 0
    }
}

// CMake sets awslc_asm for other CPUs too, which have no flags Rust reads.
#[cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm"
))]
pub(crate) use flags::*;
