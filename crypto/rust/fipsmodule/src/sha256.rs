// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

//! SHA-224 and SHA-256 (FIPS 180-4). In Rust builds these are libcrypto's
//! SHA-224 and SHA-256 functions: `crypto/rust/sha256.c` defines the C names
//! as calls to the functions here. bcm.c keeps C's sha256.c under private
//! names, for its own users.

use core::ffi::{c_int, c_uint};
use core::mem::offset_of;

use crate::{copy_bytes, slice_from_c, zero_bytes};
use block::block_data_order;

const BLOCK_LEN: usize = 64;

/// The length of a chaining value, `SHA256_CHAINING_LENGTH`.
const CHAINING_LEN: usize = 32;

/// C's `SHA256_CTX`. C code allocates it, and `tls_cbc.c` reads its fields,
/// so the layout is fixed.
#[repr(C)]
pub struct Sha256Ctx {
    h: [u32; 8],
    /// The message length in bits, low and high words.
    nl: u32,
    nh: u32,
    /// The partial block, zero past `num`.
    data: [u8; BLOCK_LEN],
    num: c_uint,
    md_len: c_uint,
}

// crypto/rust/sha256.c asserts the same literals.
const _: () = {
    assert!(size_of::<Sha256Ctx>() == 112);
    assert!(align_of::<Sha256Ctx>() == 4);
    assert!(offset_of!(Sha256Ctx, h) == 0);
    assert!(offset_of!(Sha256Ctx, nl) == 32);
    assert!(offset_of!(Sha256Ctx, nh) == 36);
    assert!(offset_of!(Sha256Ctx, data) == 40);
    assert!(offset_of!(Sha256Ctx, num) == 104);
    assert!(offset_of!(Sha256Ctx, md_len) == 108);
};

/// The block function where AWS-LC builds SHA-256 assembly: CMake sets
/// `awslc_asm` where it builds its assembly, and these are the CPUs that have
/// SHA-256 assembly (`crypto/fipsmodule/sha/internal.h`).
#[cfg(all(
    awslc_asm,
    any(
        target_arch = "x86_64",
        target_arch = "x86",
        target_arch = "aarch64",
        target_arch = "arm"
    )
))]
mod block {
    use super::BLOCK_LEN;
    use crate::cpu;

    // The assembly functions, with the C prototypes in sha/internal.h. Each
    // runs `num` blocks at `data` through `state`.
    macro_rules! asm_fns {
        ($($(#[$cfg:meta])* $name:ident),* $(,)?) => {
            unsafe extern "C" {
                $(
                    $(#[$cfg])*
                    #[link_name = c_name!(stringify!($name))]
                    fn $name(state: *mut u32, data: *const u8, num: usize);
                )*
            }
        };
    }

    asm_fns! {
        #[cfg(any(target_arch = "x86_64", target_arch = "aarch64", target_arch = "arm"))]
        sha256_block_data_order_hw,
        #[cfg(all(any(target_arch = "x86_64", target_arch = "x86"), not(awslc_no_avx)))]
        sha256_block_data_order_avx,
        #[cfg(any(target_arch = "x86_64", target_arch = "x86"))]
        sha256_block_data_order_ssse3,
        #[cfg(target_arch = "arm")]
        sha256_block_data_order_neon,
        sha256_block_data_order_nohw,
    }

    /// Runs `data`, a whole number of blocks, through the assembly that C's
    /// `sha256_block_data_order` would pick, tested in the same order.
    pub(super) fn block_data_order(state: &mut [u32; 8], data: &[u8]) {
        let num = data.len() / BLOCK_LEN;
        let (s, d) = (state.as_mut_ptr(), data.as_ptr());
        // SAFETY: `state` is 8 words and `data` holds `num` blocks, which is
        // what each assembly function reads and writes. Each one runs only if
        // the CPU has the instructions it uses, by the test C makes.
        unsafe {
            #[cfg(any(target_arch = "x86_64", target_arch = "aarch64", target_arch = "arm"))]
            if cpu::sha256_hw_capable() {
                return sha256_block_data_order_hw(s, d, num);
            }
            #[cfg(all(any(target_arch = "x86_64", target_arch = "x86"), not(awslc_no_avx)))]
            if cpu::sha256_avx_capable() {
                return sha256_block_data_order_avx(s, d, num);
            }
            #[cfg(any(target_arch = "x86_64", target_arch = "x86"))]
            if cpu::sha256_ssse3_capable() {
                return sha256_block_data_order_ssse3(s, d, num);
            }
            #[cfg(target_arch = "arm")]
            if cpu::neon_capable() {
                return sha256_block_data_order_neon(s, d, num);
            }
            sha256_block_data_order_nohw(s, d, num)
        }
    }
}

/// The block function where AWS-LC builds no SHA-256 assembly: Rust's own
/// portable code.
#[cfg(not(all(
    awslc_asm,
    any(
        target_arch = "x86_64",
        target_arch = "x86",
        target_arch = "aarch64",
        target_arch = "arm"
    )
)))]
mod block {
    use super::BLOCK_LEN;

    const K: [u32; 64] = [
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4,
        0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe,
        0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f,
        0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
        0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc,
        0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
        0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116,
        0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7,
        0xc67178f2,
    ];

    /// One round (FIPS 180-4, section 6.2.2, step 3) on the working variables
    /// `s` = a..h.
    #[inline(always)]
    fn round(s: &mut [u32; 8], k: u32, w: u32) {
        let [a, b, c, d, e, f, g, h] = *s;
        let sigma1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
        let ch = (e & f) ^ (!e & g);
        let t1 = h
            .wrapping_add(sigma1)
            .wrapping_add(ch)
            .wrapping_add(k)
            .wrapping_add(w);
        let sigma0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
        let maj = (a & b) ^ (a & c) ^ (b & c);
        let t2 = sigma0.wrapping_add(maj);
        *s = [t1.wrapping_add(t2), a, b, c, d.wrapping_add(t1), e, f, g];
    }

    /// Processes one block. The message schedule is kept as 16 rolling words.
    fn compress(state: &mut [u32; 8], block: &[u8]) {
        let mut w = [0u32; 16];
        for (w, bytes) in w.iter_mut().zip(block.chunks_exact(4)) {
            *w = u32::from_be_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]);
        }
        let mut s = *state;
        for i in 0..16 {
            round(&mut s, K[i], w[i]);
        }
        for i in 16..64 {
            let w15 = w[(i + 1) & 15];
            let w2 = w[(i + 14) & 15];
            let s0 = w15.rotate_right(7) ^ w15.rotate_right(18) ^ (w15 >> 3);
            let s1 = w2.rotate_right(17) ^ w2.rotate_right(19) ^ (w2 >> 10);
            w[i & 15] = w[i & 15]
                .wrapping_add(s0)
                .wrapping_add(w[(i + 9) & 15])
                .wrapping_add(s1);
            round(&mut s, K[i], w[i & 15]);
        }
        for (state, s) in state.iter_mut().zip(s) {
            *state = state.wrapping_add(s);
        }
    }

    /// Runs `data`, a whole number of blocks, through `compress`.
    pub(super) fn block_data_order(state: &mut [u32; 8], data: &[u8]) {
        for block in data.chunks_exact(BLOCK_LEN) {
            compress(state, block);
        }
    }
}

impl Sha256Ctx {
    pub(crate) fn new(h: [u32; 8], md_len: usize) -> Self {
        Sha256Ctx {
            h,
            nl: 0,
            nh: 0,
            data: [0; BLOCK_LEN],
            num: 0,
            md_len: md_len as c_uint,
        }
    }

    pub(crate) fn update(&mut self, mut input: &[u8]) {
        if input.is_empty() {
            return;
        }
        let len = input.len();
        let nl = self.nl.wrapping_add((len as u32) << 3);
        if nl < self.nl {
            self.nh = self.nh.wrapping_add(1);
        }
        self.nh = self.nh.wrapping_add((len >> 29) as u32);
        self.nl = nl;

        let num = self.num as usize;
        if num != 0 {
            let free = BLOCK_LEN - num;
            if input.len() < free {
                copy_bytes(&mut self.data[num..num + input.len()], input);
                self.num += input.len() as c_uint;
                return;
            }
            let (head, rest) = input.split_at(free);
            copy_bytes(&mut self.data[num..], head);
            block_data_order(&mut self.h, &self.data);
            self.data = [0; BLOCK_LEN];
            input = rest;
        }

        let (whole, tail) = input.split_at(input.len() - input.len() % BLOCK_LEN);
        if !whole.is_empty() {
            block_data_order(&mut self.h, whole);
        }
        copy_bytes(&mut self.data[..tail.len()], tail);
        self.num = tail.len() as c_uint;
    }

    /// Pads the message and processes the last blocks. Leaves `data` and
    /// `num` zero.
    fn finish(&mut self) {
        let mut n = self.num as usize;
        self.data[n] = 0x80;
        n += 1;
        // Fill the block with zeros if there isn't room for the length.
        if n > BLOCK_LEN - 8 {
            zero_bytes(&mut self.data[n..]);
            block_data_order(&mut self.h, &self.data);
            n = 0;
        }
        zero_bytes(&mut self.data[n..BLOCK_LEN - 8]);
        self.data[BLOCK_LEN - 8..BLOCK_LEN - 4].copy_from_slice(&self.nh.to_be_bytes());
        self.data[BLOCK_LEN - 4..].copy_from_slice(&self.nl.to_be_bytes());
        block_data_order(&mut self.h, &self.data);
        self.num = 0;
        self.data = [0; BLOCK_LEN];
    }

    /// Zeroes the context with volatile writes, which the optimizer can't
    /// remove, as C's `OPENSSL_cleanse` does.
    fn wipe(&mut self) {
        let p = (self as *mut Self).cast::<u32>();
        for i in 0..size_of::<Self>() / 4 {
            // SAFETY: `p` points to `*self`, `size_of::<Self>()` writable
            // bytes aligned to 4, and all-zero bytes are a valid `Sha256Ctx`.
            unsafe { p.add(i).write_volatile(0) };
        }
    }

    /// Finishes the hash and writes its digest to `out`. Returns false, with
    /// the hash still finished, if the context was set up for a digest of
    /// another length than `out`'s.
    pub(crate) fn finish_into(&mut self, out: &mut [u8]) -> bool {
        self.finish();
        if self.md_len as usize != out.len() {
            return false;
        }
        for (out, word) in out.chunks_exact_mut(4).zip(self.h) {
            out.copy_from_slice(&word.to_be_bytes());
        }
        true
    }
}

const SHA224_IV: [u32; 8] = [
    0xc1059ed8, 0x367cd507, 0x3070dd17, 0xf70e5939, 0xffc00b31, 0x68581511, 0x64f98fa7, 0xbefa4fa4,
];

pub(crate) const SHA256_IV: [u32; 8] = [
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
];

/// The initial hash value for a `md_len`-byte digest: SHA-224 for 28,
/// SHA-256 for 32.
fn iv(md_len: usize) -> Option<[u32; 8]> {
    match md_len {
        28 => Some(SHA224_IV),
        32 => Some(SHA256_IV),
        _ => None,
    }
}

/// Sets `*ctx` up for a `md_len`-byte digest: SHA-224 for 28, SHA-256 for 32.
///
/// Returns 1, or 0 if `ctx` is NULL or `md_len` is neither.
///
/// # Safety
///
/// `ctx` must be NULL or valid for writing a `SHA256_CTX`.
#[unsafe(export_name = c_name!("bcm_rust_sha256_init"))]
pub unsafe extern "C" fn bcm_rust_sha256_init(ctx: *mut Sha256Ctx, md_len: usize) -> c_int {
    let Some(h) = iv(md_len) else {
        return 0;
    };
    if ctx.is_null() {
        return 0;
    }
    // SAFETY: `ctx` is non-NULL, and the caller guarantees it is writable.
    unsafe { ctx.write(Sha256Ctx::new(h, md_len)) };
    1
}

/// Sets `*ctx` up for a `md_len`-byte digest that continues from the
/// big-endian chaining value at `h` after `n` bits, a whole number of blocks.
///
/// Returns 1, or 0 if a pointer is NULL, `md_len` is neither 28 nor 32, or
/// `n` isn't a multiple of the block size.
///
/// # Safety
///
/// `ctx` must be NULL or valid for writing a `SHA256_CTX`. `h` must be NULL or
/// valid for reading 32 bytes.
#[unsafe(export_name = c_name!("bcm_rust_sha256_init_from_state"))]
pub unsafe extern "C" fn bcm_rust_sha256_init_from_state(
    ctx: *mut Sha256Ctx,
    md_len: usize,
    h: *const u8,
    n: u64,
) -> c_int {
    if iv(md_len).is_none() || ctx.is_null() || h.is_null() || n % (BLOCK_LEN as u64 * 8) != 0 {
        return 0;
    }
    // SAFETY: `h` is non-NULL, and the caller guarantees 32 readable bytes.
    let h = unsafe { &*h.cast::<[u8; CHAINING_LEN]>() };
    let mut state = [0u32; 8];
    for (word, bytes) in state.iter_mut().zip(h.chunks_exact(4)) {
        *word = u32::from_be_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]);
    }
    let mut new = Sha256Ctx::new(state, md_len);
    new.nh = (n >> 32) as u32;
    new.nl = n as u32;
    // SAFETY: `ctx` is non-NULL, and the caller guarantees it is writable.
    unsafe { ctx.write(new) };
    1
}

/// Adds the `len` bytes at `data` to `*ctx`.
///
/// Returns 1, or 0 if `ctx` is NULL, or `data` is NULL with a non-zero `len`.
///
/// # Safety
///
/// `ctx` must be NULL or point to a `SHA256_CTX` set up by an init function.
/// `data` must be NULL or valid for reads of `len` bytes.
#[unsafe(export_name = c_name!("bcm_rust_sha256_update"))]
pub unsafe extern "C" fn bcm_rust_sha256_update(
    ctx: *mut Sha256Ctx,
    data: *const u8,
    len: usize,
) -> c_int {
    // SAFETY: forwarded from this function's contract.
    let (Some(ctx), Some(data)) = (unsafe { ctx.as_mut() }, unsafe { slice_from_c(data, len) })
    else {
        return 0;
    };
    ctx.update(data);
    1
}

/// Finishes the hash in `*ctx` and writes its `md_len`-byte digest to `out`.
///
/// Returns 1, or 0 if a pointer is NULL or `*ctx` was set up for another
/// digest length. `*ctx` is finished either way.
///
/// # Safety
///
/// `ctx` must be NULL or point to a `SHA256_CTX` set up by an init function.
/// `out` must be NULL or valid for writing `md_len` bytes.
#[unsafe(export_name = c_name!("bcm_rust_sha256_final"))]
pub unsafe extern "C" fn bcm_rust_sha256_final(
    out: *mut u8,
    md_len: usize,
    ctx: *mut Sha256Ctx,
) -> c_int {
    // SAFETY: forwarded from this function's contract.
    let Some(ctx) = (unsafe { ctx.as_mut() }) else {
        return 0;
    };
    if out.is_null() {
        ctx.finish();
        return 0;
    }
    // SAFETY: `out` is non-NULL, and the caller guarantees `md_len` writable
    // bytes.
    let out = unsafe { core::slice::from_raw_parts_mut(out, md_len) };
    ctx.finish_into(out) as c_int
}

/// Writes the `md_len`-byte digest of the `len` bytes at `data` to `out`:
/// SHA-224 for 28, SHA-256 for 32.
///
/// Returns 1, or 0 if `out` is NULL, `data` is NULL with a non-zero `len`, or
/// `md_len` is neither.
///
/// # Safety
///
/// `data` must be NULL or valid for reads of `len` bytes. `out` must be NULL
/// or valid for writing `md_len` bytes.
#[unsafe(export_name = c_name!("bcm_rust_sha256"))]
pub unsafe extern "C" fn bcm_rust_sha256(
    data: *const u8,
    len: usize,
    out: *mut u8,
    md_len: usize,
) -> c_int {
    // SAFETY: forwarded from this function's contract.
    let (Some(h), Some(data)) = (iv(md_len), unsafe { slice_from_c(data, len) }) else {
        return 0;
    };
    if out.is_null() {
        return 0;
    }
    // SAFETY: `out` is non-NULL, and the caller guarantees `md_len` writable
    // bytes.
    let out = unsafe { core::slice::from_raw_parts_mut(out, md_len) };
    let mut ctx = Sha256Ctx::new(h, md_len);
    ctx.update(data);
    let ok = ctx.finish_into(out);
    // C's SHA256 cleanses its context too.
    ctx.wipe();
    ok as c_int
}

/// Runs `num` blocks at `data` through `state`, with the block function the
/// other functions here use.
///
/// # Safety
///
/// `state` must be NULL or valid for reading and writing 8 words. `data` must
/// be valid for reads of `num` blocks.
#[unsafe(export_name = c_name!("bcm_rust_sha256_transform_blocks"))]
pub unsafe extern "C" fn bcm_rust_sha256_transform_blocks(
    state: *mut [u32; 8],
    data: *const u8,
    num: usize,
) {
    // SAFETY: forwarded from this function's contract.
    let (Some(state), Some(data)) = (unsafe { state.as_mut() }, unsafe {
        num.checked_mul(BLOCK_LEN)
            .and_then(|len| slice_from_c(data, len))
    }) else {
        return;
    };
    block_data_order(state, data);
}

/// Writes the chaining value of `*ctx`, big-endian, to the 32 bytes at
/// `out_h`, and the number of bits hashed so far to `*out_n`.
///
/// Returns 1, or 0 if a pointer is NULL or `*ctx` holds a partial block.
///
/// # Safety
///
/// `ctx` must be NULL or point to a `SHA256_CTX` set up by an init function.
/// `out_h` must be NULL or valid for writing 32 bytes, and `out_n` NULL or
/// valid for writing a `u64`.
#[unsafe(export_name = c_name!("bcm_rust_sha256_get_state"))]
pub unsafe extern "C" fn bcm_rust_sha256_get_state(
    ctx: *const Sha256Ctx,
    out_h: *mut u8,
    out_n: *mut u64,
) -> c_int {
    // SAFETY: forwarded from this function's contract.
    let Some(ctx) = (unsafe { ctx.as_ref() }) else {
        return 0;
    };
    // C checks only the low word: 512 divides 2^32.
    if out_h.is_null() || out_n.is_null() || ctx.nl % (BLOCK_LEN as u32 * 8) != 0 {
        return 0;
    }
    // SAFETY: `out_h` is non-NULL, and the caller guarantees 32 writable bytes.
    let out_h = unsafe { &mut *out_h.cast::<[u8; CHAINING_LEN]>() };
    for (out, word) in out_h.chunks_exact_mut(4).zip(ctx.h) {
        out.copy_from_slice(&word.to_be_bytes());
    }
    // SAFETY: `out_n` is non-NULL, and the caller guarantees it is writable.
    unsafe { out_n.write((u64::from(ctx.nh) << 32) + u64::from(ctx.nl)) };
    1
}
