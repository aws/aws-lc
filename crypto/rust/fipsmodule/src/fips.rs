// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

//! `bcm-rust.o` as a FIPS module of its own, in static FIPS builds on x86_64
//! and aarch64, where it serves libcrypto's SHA-224 and SHA-256 functions:
//! its integrity check and power-on self-tests. This is a prototype. The
//! check works the way bcm.o's does, but the module isn't validated and its
//! hash isn't FIPS-valid.
//!
//! The fold (cmake/cargo.cmake, `bcm-rust.lds`) puts all of the crate's code
//! and constants in one section, from `TEXT_START` to `TEXT_END`, and
//! `inject_hash -rust` writes that region's HMAC-SHA256 into `TEXT_HASH`. At
//! load time the module recomputes the HMAC and compares. That works only if
//! the consumer's final link writes the same bytes into the region that
//! inject_hash hashed, so every reference made from the region has to be
//! PC-relative to a target in the same section. bcm.o gets that from
//! delocate, which rewrites the compiler's assembly, and so does the module's
//! own copy of the SHA-256 assembly (crypto/fipsmodule/CMakeLists.txt).
//! Nothing rewrites rustc's output, so Rust module code has to be written to
//! need no rewriting.
//!
//! The crate is module code in every build, built the same way, so these
//! rules apply to all of it, now and as it grows. Only static FIPS builds
//! add this file, `bcm-rust.lds`, delocate for the assembly copy, the tiny
//! code model on aarch64 and inject_hash, which fails the build when a rule
//! is broken:
//!
//! - **No calls out of the module, not even to libc.** Under fat LTO, rustc
//!   on x86_64 calls memcpy, memset, bcmp and abort through the GOT, which
//!   only the final link lays out. `-Zplt=yes` doesn't change that for those
//!   calls, because the prebuilt `core` sets it for the whole LTO module. So:
//!   - copies and fills whose length isn't a constant go through
//!     `copy_bytes` and `zero_bytes`, with `#![no_builtins]` so LLVM doesn't
//!     turn them back into calls
//!   - no `==` on byte slices or arrays (bcmp); compare with a loop, as
//!     `equal` does
//!   - no large struct copies or zeroing: above an inline size that depends
//!     on the target and the optimization level, LLVM calls memcpy or memset
//!     for those too. Code can pass in Release and fail in Debug
//!   - panics and self-test failures execute an undefined instruction
//!     (`rt::die`) instead of calling abort, so a failure prints nothing
//!
//!   Calls to functions with C names are direct with `-Crelro-level=partial`.
//!   Module code calls its copy of the SHA-256 assembly that way, and the
//!   CPU-flag accessors in `cpu.rs`, which sit after the region and reach the
//!   flags outside the module, as delocate's accessors do for bcm.o.
//! - **aarch64 module builds use `-Ccode-model=tiny`.** Every reference then
//!   reaches its target with `adr`, within 1 MiB. The default `adrp` can't
//!   be used: lld rewrites `adrp`+`add` pairs into `adr` when the target is
//!   near, so the bytes would depend on the consumer's linker. bcm.o has the
//!   same 1 MiB limit, because delocate turns `adrp` into `adr`. It's a
//!   ceiling for all static FIPS code on aarch64, C or Rust, and neither
//!   rustc nor delocate has a way past it today. Other builds can't use the
//!   tiny model: without `bcm-rust.lds`, the module's constants can end up
//!   farther than 1 MiB from its code.
//! - **No calls to the module's own C-ABI functions** from Rust. rustc
//!   treats exported functions as replaceable at link time and reaches them
//!   through the GOT on x86_64. Rust code calls an internal function instead,
//!   as `self_test` calls `Sha256Ctx::update`, not `bcm_rust_sha256_update`.
//! - **No data the loader patches** in module code: no statics holding
//!   pointers, no trait objects, no panic messages or locations (workstreams
//!   3.1). Such data lives in sections outside the region, so a reference to
//!   it fails the build too.
//!
//! These rules work only because rustc's x86_64 and aarch64 code can be made
//! to need no fix-ups inside one section. On other CPUs it can't: ppc64le
//! reaches data through the TOC and 32-bit x86 through the GOT's base, and
//! only the final link places either. So the module exists only on x86_64 and
//! aarch64. C builds static FIPS for ppc64le too, through delocate, so a
//! ppc64le static FIPS build that finds Rust fails configure. Supporting it
//! in Rust needs rustc to change, or a rewriting tool like delocate for
//! rustc's output.

use crate::copy_bytes;
use crate::sha256::{SHA256_IV, Sha256Ctx};

// bcm-rust.lds puts these sections first, last, and after the module. Module
// code reads their addresses PC-relative, from inside the same section.
#[unsafe(link_section = ".bcm_rust_text_start")]
static TEXT_START: u8 = 0;

#[unsafe(link_section = ".bcm_rust_text_end")]
static TEXT_END: u8 = 0;

/// inject_hash replaces this placeholder (`fipscommon.UninitHashValue`) with
/// the region's HMAC-SHA256.
#[unsafe(link_section = ".bcm_rust_text_hash")]
static TEXT_HASH: [u8; 32] = [
    0xae, 0x2c, 0xea, 0x2a, 0xbd, 0xa6, 0xf3, 0xec, 0x97, 0x7f, 0x9b, 0xf6, 0x94, 0x9a, 0xfc, 0x83,
    0x68, 0x27, 0xcb, 0xa0, 0xa0, 0x9f, 0x6b, 0x6f, 0xde, 0x52, 0xcd, 0xe2, 0xcd, 0xff, 0x31, 0x80,
];

/// Compares two byte strings without a memcmp call.
fn equal(a: &[u8], b: &[u8]) -> bool {
    a.len() == b.len() && a.iter().zip(b).fold(0, |acc, (x, y)| acc | (x ^ y)) == 0
}

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
    copy_bytes(&mut padded_key[..key.len()], key);
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

/// bcm.o's SHA-256 known-answer test (`boringssl_self_test_sha256`).
fn sha256_kat() -> bool {
    const INPUT: [u8; 16] = [
        0xff, 0x3b, 0x85, 0x7d, 0xa7, 0x23, 0x6a, 0x2b, 0xaa, 0x0f, 0x39, 0x6b, 0x51, 0x52, 0x22,
        0x17,
    ];
    const DIGEST: [u8; 32] = [
        0x7f, 0xe4, 0xd5, 0xf1, 0xa1, 0xe3, 0x82, 0x87, 0xd9, 0x58, 0xf5, 0x11, 0xc7, 0x1d, 0x5e,
        0x27, 0x5e, 0xcc, 0xd2, 0x66, 0xcf, 0xb9, 0xc8, 0xc6, 0x60, 0xd8, 0x92, 0x1e, 0x57, 0xfd,
        0x46, 0x75,
    ];
    equal(&sha256(&[&INPUT]), &DIGEST)
}

/// bcm.o's HMAC-SHA256 known-answer test (`boringssl_self_test_hmac_sha256`),
/// with the input as both key and message.
fn hmac_sha256_kat() -> bool {
    const INPUT: [u8; 16] = [
        0xda, 0xd9, 0x12, 0x93, 0xdf, 0xcf, 0x2a, 0x7c, 0x8e, 0xcd, 0x13, 0xfe, 0x35, 0x3f, 0xa7,
        0x5b,
    ];
    const MAC: [u8; 32] = [
        0x36, 0x5f, 0x5b, 0xd5, 0xf5, 0xeb, 0xfd, 0xc7, 0x6e, 0x53, 0xa5, 0x73, 0x6d, 0x73, 0x20,
        0x13, 0xaa, 0xd3, 0xbc, 0x86, 0x4b, 0xb8, 0x84, 0x94, 0x16, 0x46, 0x88, 0x9c, 0x48, 0xee,
        0xa9, 0x0e,
    ];
    equal(&hmac_sha256(&INPUT, &INPUT), &MAC)
}

/// Checks the module's code and constants against the HMAC-SHA256 that
/// inject_hash embedded, with bcm.o's key of 64 zero bytes.
fn integrity_check() -> bool {
    let start = core::ptr::addr_of!(TEXT_START).expose_provenance();
    let end = core::ptr::addr_of!(TEXT_END).expose_provenance();
    let Some(len) = end.checked_sub(start) else {
        return false;
    };
    // SAFETY: bcm-rust.lds puts TEXT_START and TEXT_END at the start and end
    // of one section, so the `len` bytes from TEXT_START are mapped and never
    // written: they are the module's own code and constants. Like bcm.o's
    // check, this reads machine code, which Rust's memory model doesn't
    // describe; the exposed address keeps the optimizer from assuming the
    // read stays inside TEXT_START.
    let text = unsafe {
        core::slice::from_raw_parts(core::ptr::with_exposed_provenance::<u8>(start), len)
    };
    let mut expected = [0u8; 32];
    for (expected, byte) in expected.iter_mut().zip(&TEXT_HASH) {
        // A volatile read, so the compiler can't use the placeholder's value,
        // which inject_hash replaces after compilation.
        // SAFETY: `byte` is a reference into TEXT_HASH.
        *expected = unsafe { core::ptr::read_volatile(byte) };
    }
    equal(&hmac_sha256(&[0; 64], text), &expected)
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

#[used]
#[unsafe(link_section = ".init_array")]
static POWER_ON_SELF_TEST: extern "C" fn() = power_on_self_test;
