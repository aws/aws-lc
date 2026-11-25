// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

//! `bcm-rust.o` as a FIPS module of its own, where it serves libcrypto's
//! SHA-224 and SHA-256 functions: its integrity check and power-on
//! self-tests, in the FIPS builds crypto/CMakeLists.txt lists. This is a
//! prototype. The check works the way bcm.o's does, but the module isn't
//! validated and its hash isn't FIPS-valid.
//!
//! The module region holds the crate's code and constants, from `TEXT_START`
//! to `TEXT_END`. `inject_hash -rust` writes the region's HMAC-SHA256 into
//! `TEXT_HASH`, and at load time the module recomputes the HMAC and compares.
//! Shared FIPS builds hash the region in the final library, once the link has
//! fixed every reference, as they hash bcm.o's. There the fold's linker script
//! makes the region (cmake/cargo.cmake).
//!
//! Static FIPS builds hash the region in `bcm-rust.o`, before the consumer's
//! final link, so that link has to write the same bytes into it. There,
//! delocate writes the module from rustc's assembly for the crate and the
//! module's copy of the SHA-256 assembly, as it writes bcm.o
//! (crypto/fipsmodule/CMakeLists.txt). It puts the markers, the hash
//! placeholder, the code and the constants in one section, sends calls out of
//! the module through stubs after the region, rustc's own memcpy, memset and
//! abort calls included, and reaches data outside the module through
//! accessors. inject_hash then checks the region's relocations. These builds
//! exist only on x86_64 and aarch64, where delocate's handling of rustc's
//! assembly is tested.
//!
//! So module code follows C's module rules. The crate is built the same way in
//! every build, so they bind all of it:
//!
//! - **Mutable statics start zeroed and are reached only through an accessor,
//!   `<name>_bss_get()`**, as with C's `DEFINE_BSS_GET`. In static FIPS builds
//!   delocate writes the accessor and rejects a static that doesn't start
//!   zeroed, and inject_hash rejects a direct reference to one. Other builds
//!   have to define the accessor in Rust. The crate has no mutable statics yet.
//! - **No data the loader patches** in module code: no statics holding
//!   pointers, no trait objects, no panic messages or locations. delocate
//!   rejects them. Windows shared builds check this rule as well: COFF has no
//!   `.data.rel.ro`, so a constant that holds a pointer stays in the region,
//!   and inject_hash fails on the fix-up the loader would make to it.

use crate::sha256::{SHA256_IV, Sha256Ctx};

// The module region's bounds outside static FIPS builds. On ELF, bcm-rust.lds
// puts these sections first and last in the module's one section, and module
// code reads their addresses PC-relative, from inside it. On COFF the fold
// does the same by renaming sections (cmake/rust_crate_object_fold.cmake), and
// inject_hash finds the bounds by these names in the linker's map file.
#[cfg(not(any(target_vendor = "apple", awslc_delocate)))]
#[cfg_attr(windows, unsafe(export_name = "BORINGSSL_bcm_rust_text_start"))]
#[unsafe(link_section = ".bcm_rust_text_start")]
static TEXT_START: u8 = 0;

#[cfg(not(any(target_vendor = "apple", awslc_delocate)))]
#[cfg_attr(windows, unsafe(export_name = "BORINGSSL_bcm_rust_text_end"))]
#[unsafe(link_section = ".bcm_rust_text_end")]
static TEXT_END: u8 = 0;

// On Mach-O, the partial link puts the module's code and constants in one
// section, __TEXT,__bcm_rust (cmake/cargo.cmake), and the linker defines
// these symbols at its start and end.
#[cfg(target_vendor = "apple")]
unsafe extern "C" {
    #[link_name = "\u{1}section$start$__TEXT$__bcm_rust"]
    static TEXT_START: u8;
    #[link_name = "\u{1}section$end$__TEXT$__bcm_rust"]
    static TEXT_END: u8;
}

// In static FIPS builds, delocate writes the module's markers and hash
// placeholder, as it does bcm.o's, in the one section it writes the module's
// code and constants to (crypto/fipsmodule/CMakeLists.txt).
#[cfg(awslc_delocate)]
unsafe extern "C" {
    #[link_name = "BORINGSSL_bcm_rust_text_start"]
    static TEXT_START: u8;
    #[link_name = "BORINGSSL_bcm_rust_text_end"]
    static TEXT_END: u8;
    #[link_name = "BORINGSSL_bcm_rust_text_hash"]
    static TEXT_HASH: [u8; 32];
}

/// inject_hash replaces this placeholder (`RustUninitHashValue`) with the
/// region's HMAC-SHA256. Its section comes after the module region.
#[cfg(not(awslc_delocate))]
#[cfg_attr(
    not(target_vendor = "apple"),
    unsafe(link_section = ".bcm_rust_text_hash")
)]
#[cfg_attr(
    target_vendor = "apple",
    unsafe(link_section = "__TEXT,__bcm_rust_hash")
)]
static TEXT_HASH: [u8; 32] = [
    0xeb, 0xa0, 0xdc, 0x87, 0x3f, 0x90, 0x5a, 0x73, 0xae, 0x32, 0xd8, 0xb2, 0x74, 0xd9, 0x4c, 0x7c,
    0x50, 0x48, 0x00, 0xe1, 0xb2, 0xee, 0x1c, 0x96, 0x64, 0x35, 0x99, 0x82, 0xae, 0xfc, 0x2d, 0xd8,
];

/// The SHA-256 digest of the concatenation of `parts`.
fn sha256(parts: &[&[u8]]) -> [u8; 32] {
    let mut ctx = Sha256Ctx::new(SHA256_IV, 32);
    for part in parts {
        ctx.update(part);
    }
    let mut out = [0; 32];
    ctx.finish_into(&mut out);
    out
}

/// HMAC-SHA256 (FIPS 198-1) with a key of at most 64 bytes.
fn hmac_sha256(key: &[u8], data: &[u8]) -> [u8; 32] {
    let mut padded_key = [0u8; 64];
    padded_key[..key.len()].copy_from_slice(key);
    let mut pad = [0u8; 64];
    for (pad, key) in pad.iter_mut().zip(padded_key) {
        *pad = key ^ 0x36;
    }
    let inner = sha256(&[&pad, data]);
    for (pad, key) in pad.iter_mut().zip(padded_key) {
        *pad = key ^ 0x5c;
    }
    sha256(&[&pad, &inner])
}

/// The SHA-256 known-answer test. bcm-rust.o's vectors differ from bcm.o's,
/// so tools that find and break one of bcm.o's tests by its input bytes, such
/// as `break-kat.go`, find exactly one copy.
fn sha256_kat() -> bool {
    const INPUT: [u8; 16] = [
        0xa7, 0x27, 0x3a, 0x11, 0xaf, 0xd5, 0x87, 0xf7, 0xe7, 0x73, 0xf0, 0x17, 0x7f, 0x00, 0x0a,
        0x4b,
    ];
    const DIGEST: [u8; 32] = [
        0x47, 0xdc, 0x42, 0xdb, 0x99, 0x38, 0xd7, 0xd8, 0xfa, 0x03, 0xe0, 0xc4, 0x8f, 0xbe, 0xac,
        0x6a, 0x6d, 0x26, 0x32, 0x14, 0x95, 0xeb, 0x67, 0xeb, 0x24, 0x98, 0xd5, 0xa6, 0x29, 0x85,
        0xdb, 0x1c,
    ];
    sha256(&[&INPUT]) == DIGEST
}

/// The HMAC-SHA256 known-answer test, with the input as both key and
/// message, as bcm.o's is.
fn hmac_sha256_kat() -> bool {
    const INPUT: [u8; 16] = [
        0xa1, 0xf7, 0x78, 0xfc, 0xa0, 0xa4, 0x2f, 0xe6, 0xd8, 0x10, 0xfb, 0x2f, 0xc2, 0x68, 0x86,
        0x53,
    ];
    const MAC: [u8; 32] = [
        0x68, 0x3b, 0xa2, 0xee, 0x70, 0x8d, 0x42, 0xf4, 0x04, 0xf9, 0x63, 0xe0, 0xa2, 0x4c, 0x13,
        0xdc, 0x3c, 0xf0, 0x21, 0x85, 0x18, 0x7d, 0xac, 0xec, 0x48, 0x29, 0xcc, 0xfd, 0x9f, 0x16,
        0x88, 0x7f,
    ];
    hmac_sha256(&INPUT, &INPUT) == MAC
}

/// Checks the module's code and constants against the HMAC-SHA256 that
/// inject_hash embedded, with bcm.o's key of 64 zero bytes.
fn integrity_check() -> bool {
    let start = core::ptr::addr_of!(TEXT_START).expose_provenance();
    let end = core::ptr::addr_of!(TEXT_END).expose_provenance();
    let Some(len) = end.checked_sub(start) else {
        return false;
    };
    // SAFETY: TEXT_START and TEXT_END are the start and end of the region,
    // in one section, so the `len` bytes from TEXT_START are mapped and never
    // written: they are the module's own code and constants. Like bcm.o's
    // check, this reads machine code, which Rust's memory model doesn't
    // describe; the exposed address keeps the optimizer from assuming the
    // read stays inside TEXT_START.
    let text = unsafe {
        core::slice::from_raw_parts(core::ptr::with_exposed_provenance::<u8>(start), len)
    };
    let hash = (&raw const TEXT_HASH).cast::<u8>();
    let mut expected = [0u8; 32];
    for (i, expected) in expected.iter_mut().enumerate() {
        // A volatile read, so the compiler can't use the placeholder's value,
        // which inject_hash replaces after compilation.
        // SAFETY: TEXT_HASH is 32 bytes.
        *expected = unsafe { core::ptr::read_volatile(hash.add(i)) };
    }
    hmac_sha256(&[0; 64], text) == expected
}

/// The module's power-on self-tests, in bcm.o's order: the SHA-256 and
/// HMAC-SHA256 known-answer tests, then the integrity check, which uses them.
fn self_test() -> bool {
    sha256_kat() && hmac_sha256_kat() && integrity_check()
}

/// Runs the self-tests when bcm-rust.o is loaded, the way bcm.o's constructor
/// runs its own, independently of bcm.o, and stops the process if one fails.
/// A static link includes bcm-rust.o, and so this constructor, only if
/// something calls into the module.
extern "C" fn power_on_self_test() {
    if !self_test() {
        crate::rt::die();
    }
}

// bcm.o's constructor fills in the CPU flags, so this one runs after it. ELF
// and Mach-O builds get that order from libcrypto's link line. The Windows CRT
// runs .CRT$XC* initializers in the order of their names, and bcm.o's is in
// .CRT$XCU.
#[used]
#[cfg_attr(
    not(any(target_vendor = "apple", windows)),
    unsafe(link_section = ".init_array")
)]
#[cfg_attr(
    target_vendor = "apple",
    unsafe(link_section = "__DATA,__mod_init_func")
)]
#[cfg_attr(windows, unsafe(link_section = ".CRT$XCV"))]
static POWER_ON_SELF_TEST: extern "C" fn() = power_on_self_test;
