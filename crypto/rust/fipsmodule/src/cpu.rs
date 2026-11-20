// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

//! AWS-LC's CPU capability flags, which C's `OPENSSL_cpuid_setup` fills in
//! (`crypto/fipsmodule/cpucap`). Rust reads the same flags as C, so the
//! `OPENSSL_ia32cap` and `OPENSSL_armcap` overrides reach it too, and repeats
//! the tests C's SHA-256 dispatch makes (`crypto/fipsmodule/sha/internal.h`
//! and `cpucap/internal.h`). Rust declares the flags atomic because C writes
//! them, once, at startup.
//!
//! Module code can't refer to the flags itself (fips.rs). They're outside the
//! module, so the reference would be a GOT load, which the final link
//! rewrites inside the hashed region. So on x86_64 and aarch64 ELF, where
//! bcm-rust.o can be a FIPS module, module code calls an accessor in
//! `.bcm_rust_outside`, which `bcm-rust.lds` places after the region, as
//! delocate places bcm.o's `OPENSSL_ia32cap_get`. Other targets refer to the
//! flags directly: Mach-O and COFF have no such section syntax, and no module.
//! Like bcm.o, the module reads flags that code outside it, in libcrypto,
//! holds.

#[cfg(any(target_arch = "x86_64", target_arch = "x86"))]
mod flags {
    use core::sync::atomic::{AtomicU32, Ordering};

    unsafe extern "C" {
        #[link_name = c_name!("OPENSSL_ia32cap_P")]
        static OPENSSL_ia32cap_P: [AtomicU32; 4];
    }

    // The accessor on x86_64 ELF (module doc): `lea` reaches the flags from
    // outside the hashed region, wherever the final link puts them. The CFI
    // directives give it unwind info, which crypto_test's unwind tests need.
    #[cfg(all(target_arch = "x86_64", not(any(target_vendor = "apple", windows))))]
    core::arch::global_asm!(
        ".pushsection .bcm_rust_outside, \"ax\", @progbits",
        ".hidden bcm_rust_ia32cap_addr",
        ".globl bcm_rust_ia32cap_addr",
        ".type bcm_rust_ia32cap_addr, @function",
        "bcm_rust_ia32cap_addr:",
        ".cfi_startproc",
        "leaq {cap}(%rip), %rax",
        "ret",
        ".cfi_endproc",
        ".size bcm_rust_ia32cap_addr, .-bcm_rust_ia32cap_addr",
        ".popsection",
        cap = sym OPENSSL_ia32cap_P,
        options(att_syntax),
    );
    #[cfg(all(target_arch = "x86_64", not(any(target_vendor = "apple", windows))))]
    unsafe extern "C" {
        safe fn bcm_rust_ia32cap_addr() -> *const [AtomicU32; 4];
    }

    /// The flags' address.
    fn flags() -> *const [AtomicU32; 4] {
        #[cfg(all(target_arch = "x86_64", not(any(target_vendor = "apple", windows))))]
        {
            bcm_rust_ia32cap_addr()
        }
        #[cfg(not(all(target_arch = "x86_64", not(any(target_vendor = "apple", windows)))))]
        {
            &raw const OPENSSL_ia32cap_P
        }
    }

    /// Word `i` of `OPENSSL_ia32cap_P`.
    fn word(i: usize) -> u32 {
        // SAFETY: C defines `OPENSSL_ia32cap_P` as four `uint32_t`, which
        // have AtomicU32's layout.
        unsafe { (*flags())[i].load(Ordering::Relaxed) }
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

    // The accessor on aarch64 ELF (module doc): `adrp` and `add` reach the
    // flags from outside the hashed region, wherever the final link puts them.
    // The CFI directives give it unwind info.
    #[cfg(all(target_arch = "aarch64", not(any(target_vendor = "apple", windows))))]
    core::arch::global_asm!(
        ".pushsection .bcm_rust_outside, \"ax\", %progbits",
        ".hidden bcm_rust_armcap_addr",
        ".globl bcm_rust_armcap_addr",
        ".type bcm_rust_armcap_addr, %function",
        "bcm_rust_armcap_addr:",
        ".cfi_startproc",
        "adrp x0, {cap}",
        "add x0, x0, :lo12:{cap}",
        "ret",
        ".cfi_endproc",
        ".size bcm_rust_armcap_addr, .-bcm_rust_armcap_addr",
        ".popsection",
        cap = sym OPENSSL_armcap_P,
    );
    #[cfg(all(target_arch = "aarch64", not(any(target_vendor = "apple", windows))))]
    unsafe extern "C" {
        safe fn bcm_rust_armcap_addr() -> *const AtomicU32;
    }

    /// The flags' address.
    fn flags() -> *const AtomicU32 {
        #[cfg(all(target_arch = "aarch64", not(any(target_vendor = "apple", windows))))]
        {
            bcm_rust_armcap_addr()
        }
        #[cfg(not(all(target_arch = "aarch64", not(any(target_vendor = "apple", windows)))))]
        {
            &raw const OPENSSL_armcap_P
        }
    }

    fn armcap() -> u32 {
        // SAFETY: C defines `OPENSSL_armcap_P` as a `uint32_t`, which has
        // AtomicU32's layout.
        unsafe { (*flags()).load(Ordering::Relaxed) }
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
