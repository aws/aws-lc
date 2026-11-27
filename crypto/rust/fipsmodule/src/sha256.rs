// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

//! SHA-224 and SHA-256 (FIPS 180-4) behind C's `SHA256_*` functions, which
//! `crypto/fipsmodule/sha/sha256.c` keeps as thin wrappers, so every SHA-256
//! user in the FIPS module runs this code. C still picks the block function:
//! the CPU's assembly, or `bcm_rust_sha256_block_data_order`.

use core::ffi::{c_int, c_uint};
use core::mem::offset_of;

use crate::slice_from_c;

const BLOCK_LEN: usize = 64;

/// C's `SHA256_CTX`. C code allocates it and reads and writes its fields too
/// (`SHA256_Init_from_state`, `SHA256_get_state`), so the layout is fixed.
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

// sha256.c asserts the same literals.
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

unsafe extern "C" {
    /// C's block function dispatch.
    #[link_name = c_name!("SHA256_TransformBlocks")]
    fn SHA256_TransformBlocks(state: *mut u32, data: *const u8, num_blocks: usize);
}

/// Runs the block function over `data`, a whole number of blocks.
fn blocks(h: &mut [u32; 8], data: &[u8]) {
    // SAFETY: `h` is 8 words, and `data` holds `data.len() / BLOCK_LEN` blocks.
    unsafe { SHA256_TransformBlocks(h.as_mut_ptr(), data.as_ptr(), data.len() / BLOCK_LEN) }
}

impl Sha256Ctx {
    fn update(&mut self, mut input: &[u8]) {
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
                self.data[num..num + input.len()].copy_from_slice(input);
                self.num += input.len() as c_uint;
                return;
            }
            let (head, rest) = input.split_at(free);
            self.data[num..].copy_from_slice(head);
            blocks(&mut self.h, &self.data);
            self.data = [0; BLOCK_LEN];
            input = rest;
        }

        let (whole, tail) = input.split_at(input.len() - input.len() % BLOCK_LEN);
        if !whole.is_empty() {
            blocks(&mut self.h, whole);
        }
        self.data[..tail.len()].copy_from_slice(tail);
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
            self.data[n..].fill(0);
            blocks(&mut self.h, &self.data);
            n = 0;
        }
        self.data[n..BLOCK_LEN - 8].fill(0);
        self.data[BLOCK_LEN - 8..BLOCK_LEN - 4].copy_from_slice(&self.nh.to_be_bytes());
        self.data[BLOCK_LEN - 4..].copy_from_slice(&self.nl.to_be_bytes());
        blocks(&mut self.h, &self.data);
        self.num = 0;
        self.data = [0; BLOCK_LEN];
    }
}

const SHA224_IV: [u32; 8] = [
    0xc1059ed8, 0x367cd507, 0x3070dd17, 0xf70e5939, 0xffc00b31, 0x68581511, 0x64f98fa7, 0xbefa4fa4,
];

const SHA256_IV: [u32; 8] = [
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
];

/// Sets `*ctx` up for a `md_len`-byte digest: SHA-224 for 28, SHA-256 for 32.
///
/// Returns 1, or 0 if `ctx` is NULL or `md_len` is neither.
///
/// # Safety
///
/// `ctx` must be NULL or valid for writing a `SHA256_CTX`.
#[unsafe(export_name = c_name!("bcm_rust_sha256_init"))]
pub unsafe extern "C" fn bcm_rust_sha256_init(ctx: *mut Sha256Ctx, md_len: usize) -> c_int {
    let h = match md_len {
        28 => SHA224_IV,
        32 => SHA256_IV,
        _ => return 0,
    };
    if ctx.is_null() {
        return 0;
    }
    let init = Sha256Ctx {
        h,
        nl: 0,
        nh: 0,
        data: [0; BLOCK_LEN],
        num: 0,
        md_len: md_len as c_uint,
    };
    // SAFETY: `ctx` is non-NULL, and the caller guarantees it is writable.
    unsafe { ctx.write(init) };
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
    ctx.finish();
    if out.is_null() || ctx.md_len as usize != md_len {
        return 0;
    }
    // SAFETY: `out` is non-NULL, and the caller guarantees `md_len` writable
    // bytes.
    let out = unsafe { core::slice::from_raw_parts_mut(out, md_len) };
    for (out, word) in out.chunks_exact_mut(4).zip(ctx.h) {
        out.copy_from_slice(&word.to_be_bytes());
    }
    1
}

/// The portable block function: runs `num` blocks at `data` through `*state`.
///
/// # Safety
///
/// `state` must be NULL or valid for reading and writing 8 words. `data` must
/// be valid for reads of `num` blocks.
#[unsafe(export_name = c_name!("bcm_rust_sha256_block_data_order"))]
pub unsafe extern "C" fn bcm_rust_sha256_block_data_order(
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
    for block in data.chunks_exact(BLOCK_LEN) {
        compress(state, block);
    }
}

const K: [u32; 64] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
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
