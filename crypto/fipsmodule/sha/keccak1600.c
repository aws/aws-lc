/*
 * Copyright 2016 The OpenSSL Project Authors. All Rights Reserved.
 *
 * Licensed under the Apache License 2.0 (the "License").  You may not use
 * this file except in compliance with the License.  You can obtain a copy
 * in the file LICENSE in the source distribution or at
 * https://www.openssl.org/source/license.html
 */

#include <assert.h>

#if defined(__x86_64__) || defined(__aarch64__) || \
    defined(__mips64) || defined(__ia64) || defined(__loongarch_lp64) || \
    (defined(__VMS) && !defined(__vax))

 // These are available even in ILP32 flavours, but even then they are
 // capable of performing 64-bit operations as efficiently as in *P64.
 // Since it's not given that we can use sizeof(void *), just shunt it.
# define BIT_INTERLEAVE (0)
#else
# define BIT_INTERLEAVE (sizeof(void *) < 8)
#endif

#if !defined(KECCAK1600_ASM)

static const uint8_t rhotates[KECCAK1600_ROWS][KECCAK1600_ROWS] = {
    {  0,  1, 62, 28, 27 },
    { 36, 44,  6, 55, 20 },
    {  3, 10, 43, 25, 39 },
    { 41, 45, 15, 21,  8 },
    { 18,  2, 61, 56, 14 }
};

static const uint64_t iotas[] = {
    BIT_INTERLEAVE ? 0x0000000000000001ULL : 0x0000000000000001ULL,
    BIT_INTERLEAVE ? 0x0000008900000000ULL : 0x0000000000008082ULL,
    BIT_INTERLEAVE ? 0x8000008b00000000ULL : 0x800000000000808aULL,
    BIT_INTERLEAVE ? 0x8000808000000000ULL : 0x8000000080008000ULL,
    BIT_INTERLEAVE ? 0x0000008b00000001ULL : 0x000000000000808bULL,
    BIT_INTERLEAVE ? 0x0000800000000001ULL : 0x0000000080000001ULL,
    BIT_INTERLEAVE ? 0x8000808800000001ULL : 0x8000000080008081ULL,
    BIT_INTERLEAVE ? 0x8000008200000001ULL : 0x8000000000008009ULL,
    BIT_INTERLEAVE ? 0x0000000b00000000ULL : 0x000000000000008aULL,
    BIT_INTERLEAVE ? 0x0000000a00000000ULL : 0x0000000000000088ULL,
    BIT_INTERLEAVE ? 0x0000808200000001ULL : 0x0000000080008009ULL,
    BIT_INTERLEAVE ? 0x0000800300000000ULL : 0x000000008000000aULL,
    BIT_INTERLEAVE ? 0x0000808b00000001ULL : 0x000000008000808bULL,
    BIT_INTERLEAVE ? 0x8000000b00000001ULL : 0x800000000000008bULL,
    BIT_INTERLEAVE ? 0x8000008a00000001ULL : 0x8000000000008089ULL,
    BIT_INTERLEAVE ? 0x8000008100000001ULL : 0x8000000000008003ULL,
    BIT_INTERLEAVE ? 0x8000008100000000ULL : 0x8000000000008002ULL,
    BIT_INTERLEAVE ? 0x8000000800000000ULL : 0x8000000000000080ULL,
    BIT_INTERLEAVE ? 0x0000008300000000ULL : 0x000000000000800aULL,
    BIT_INTERLEAVE ? 0x8000800300000000ULL : 0x800000008000000aULL,
    BIT_INTERLEAVE ? 0x8000808800000001ULL : 0x8000000080008081ULL,
    BIT_INTERLEAVE ? 0x8000008800000000ULL : 0x8000000000008080ULL,
    BIT_INTERLEAVE ? 0x0000800000000001ULL : 0x0000000080000001ULL,
    BIT_INTERLEAVE ? 0x8000808200000000ULL : 0x8000000080008008ULL
};

#if defined(__i386) || defined(__i386__) || defined(_M_IX86) || \
    (defined(__x86_64) && !defined(__BMI__)) || defined(_M_X64) || \
    defined(__mips) || defined(__riscv) || defined(__s390__) || defined(__loongarch__) || \
    defined(__EMSCRIPTEN__)

 // These platforms don't support "logical and with complement" instruction.
# define KECCAK_COMPLEMENTING_TRANSFORM
#endif

#define ROL32(a, offset) (((a) << (offset)) | ((a) >> ((32 - (offset)) & 31)))

static uint64_t ROL64(uint64_t val, int offset)
{
    if (offset == 0) {
        return val;
    } else if (!BIT_INTERLEAVE) {
        return (val << offset) | (val >> (64-offset));
    } else {
        uint32_t hi = (uint32_t)(val >> 32), lo = (uint32_t)val;

        if ((offset & 1) != 0) {
            uint32_t tmp = hi;

            offset >>= 1;
            hi = ROL32(lo, offset);
            lo = ROL32(tmp, offset + 1);
        } else {
            offset >>= 1;
            lo = ROL32(lo, offset);
            hi = ROL32(hi, offset);
        }

        return ((uint64_t)hi << 32) | lo;
    }
}

 // KECCAK_2X:
 // This is the default implementation used in OpenSSL and the most efficient;
 // the other implementations were removed from this file.
 // This implementation is a variant of KECCAK_1X (see OpenSSL)
 // This implementation allows to take temporary storage
 // out of round procedure and simplify references to it by alternating
 // it with actual data (see round loop below). 
 // It ensures best compiler interpretation to assembly and provides best 
 // instruction per processed byte ratio at minimal round unroll factor.
static void Round(uint64_t R[KECCAK1600_ROWS][KECCAK1600_ROWS], uint64_t A[KECCAK1600_ROWS][KECCAK1600_ROWS], size_t i)
{
    uint64_t C[KECCAK1600_ROWS], D[KECCAK1600_ROWS];

    assert(i < (sizeof(iotas) / sizeof(iotas[0])));

    C[0] = A[0][0] ^ A[1][0] ^ A[2][0] ^ A[3][0] ^ A[4][0];
    C[1] = A[0][1] ^ A[1][1] ^ A[2][1] ^ A[3][1] ^ A[4][1];
    C[2] = A[0][2] ^ A[1][2] ^ A[2][2] ^ A[3][2] ^ A[4][2];
    C[3] = A[0][3] ^ A[1][3] ^ A[2][3] ^ A[3][3] ^ A[4][3];
    C[4] = A[0][4] ^ A[1][4] ^ A[2][4] ^ A[3][4] ^ A[4][4];

    D[0] = ROL64(C[1], 1) ^ C[4];
    D[1] = ROL64(C[2], 1) ^ C[0];
    D[2] = ROL64(C[3], 1) ^ C[1];
    D[3] = ROL64(C[4], 1) ^ C[2];
    D[4] = ROL64(C[0], 1) ^ C[3];

    C[0] =       A[0][0] ^ D[0];
    C[1] = ROL64(A[1][1] ^ D[1], rhotates[1][1]);
    C[2] = ROL64(A[2][2] ^ D[2], rhotates[2][2]);
    C[3] = ROL64(A[3][3] ^ D[3], rhotates[3][3]);
    C[4] = ROL64(A[4][4] ^ D[4], rhotates[4][4]);

#ifdef KECCAK_COMPLEMENTING_TRANSFORM
    R[0][0] = C[0] ^ ( C[1] | C[2]) ^ iotas[i];
    R[0][1] = C[1] ^ (~C[2] | C[3]);
    R[0][2] = C[2] ^ ( C[3] & C[4]);
    R[0][3] = C[3] ^ ( C[4] | C[0]);
    R[0][4] = C[4] ^ ( C[0] & C[1]);
#else
    R[0][0] = C[0] ^ (~C[1] & C[2]) ^ iotas[i];
    R[0][1] = C[1] ^ (~C[2] & C[3]);
    R[0][2] = C[2] ^ (~C[3] & C[4]);
    R[0][3] = C[3] ^ (~C[4] & C[0]);
    R[0][4] = C[4] ^ (~C[0] & C[1]);
#endif

    C[0] = ROL64(A[0][3] ^ D[3], rhotates[0][3]);
    C[1] = ROL64(A[1][4] ^ D[4], rhotates[1][4]);
    C[2] = ROL64(A[2][0] ^ D[0], rhotates[2][0]);
    C[3] = ROL64(A[3][1] ^ D[1], rhotates[3][1]);
    C[4] = ROL64(A[4][2] ^ D[2], rhotates[4][2]);

#ifdef KECCAK_COMPLEMENTING_TRANSFORM
    R[1][0] = C[0] ^ (C[1] |  C[2]);
    R[1][1] = C[1] ^ (C[2] &  C[3]);
    R[1][2] = C[2] ^ (C[3] | ~C[4]);
    R[1][3] = C[3] ^ (C[4] |  C[0]);
    R[1][4] = C[4] ^ (C[0] &  C[1]);
#else
    R[1][0] = C[0] ^ (~C[1] & C[2]);
    R[1][1] = C[1] ^ (~C[2] & C[3]);
    R[1][2] = C[2] ^ (~C[3] & C[4]);
    R[1][3] = C[3] ^ (~C[4] & C[0]);
    R[1][4] = C[4] ^ (~C[0] & C[1]);
#endif

    C[0] = ROL64(A[0][1] ^ D[1], rhotates[0][1]);
    C[1] = ROL64(A[1][2] ^ D[2], rhotates[1][2]);
    C[2] = ROL64(A[2][3] ^ D[3], rhotates[2][3]);
    C[3] = ROL64(A[3][4] ^ D[4], rhotates[3][4]);
    C[4] = ROL64(A[4][0] ^ D[0], rhotates[4][0]);

#ifdef KECCAK_COMPLEMENTING_TRANSFORM
    R[2][0] =  C[0] ^ ( C[1] | C[2]);
    R[2][1] =  C[1] ^ ( C[2] & C[3]);
    R[2][2] =  C[2] ^ (~C[3] & C[4]);
    R[2][3] = ~C[3] ^ ( C[4] | C[0]);
    R[2][4] =  C[4] ^ ( C[0] & C[1]);
#else
    R[2][0] = C[0] ^ (~C[1] & C[2]);
    R[2][1] = C[1] ^ (~C[2] & C[3]);
    R[2][2] = C[2] ^ (~C[3] & C[4]);
    R[2][3] = C[3] ^ (~C[4] & C[0]);
    R[2][4] = C[4] ^ (~C[0] & C[1]);
#endif

    C[0] = ROL64(A[0][4] ^ D[4], rhotates[0][4]);
    C[1] = ROL64(A[1][0] ^ D[0], rhotates[1][0]);
    C[2] = ROL64(A[2][1] ^ D[1], rhotates[2][1]);
    C[3] = ROL64(A[3][2] ^ D[2], rhotates[3][2]);
    C[4] = ROL64(A[4][3] ^ D[3], rhotates[4][3]);

#ifdef KECCAK_COMPLEMENTING_TRANSFORM
    R[3][0] =  C[0] ^ ( C[1] & C[2]);
    R[3][1] =  C[1] ^ ( C[2] | C[3]);
    R[3][2] =  C[2] ^ (~C[3] | C[4]);
    R[3][3] = ~C[3] ^ ( C[4] & C[0]);
    R[3][4] =  C[4] ^ ( C[0] | C[1]);
#else
    R[3][0] = C[0] ^ (~C[1] & C[2]);
    R[3][1] = C[1] ^ (~C[2] & C[3]);
    R[3][2] = C[2] ^ (~C[3] & C[4]);
    R[3][3] = C[3] ^ (~C[4] & C[0]);
    R[3][4] = C[4] ^ (~C[0] & C[1]);
#endif

    C[0] = ROL64(A[0][2] ^ D[2], rhotates[0][2]);
    C[1] = ROL64(A[1][3] ^ D[3], rhotates[1][3]);
    C[2] = ROL64(A[2][4] ^ D[4], rhotates[2][4]);
    C[3] = ROL64(A[3][0] ^ D[0], rhotates[3][0]);
    C[4] = ROL64(A[4][1] ^ D[1], rhotates[4][1]);

#ifdef KECCAK_COMPLEMENTING_TRANSFORM
    R[4][0] =  C[0] ^ (~C[1] & C[2]);
    R[4][1] = ~C[1] ^ ( C[2] | C[3]);
    R[4][2] =  C[2] ^ ( C[3] & C[4]);
    R[4][3] =  C[3] ^ ( C[4] | C[0]);
    R[4][4] =  C[4] ^ ( C[0] & C[1]);
#else
    R[4][0] = C[0] ^ (~C[1] & C[2]);
    R[4][1] = C[1] ^ (~C[2] & C[3]);
    R[4][2] = C[2] ^ (~C[3] & C[4]);
    R[4][3] = C[3] ^ (~C[4] & C[0]);
    R[4][4] = C[4] ^ (~C[0] & C[1]);
#endif
}

static void KeccakF1600(uint64_t A[KECCAK1600_ROWS][KECCAK1600_ROWS])
{
    uint64_t T[KECCAK1600_ROWS][KECCAK1600_ROWS];
    size_t i;

#ifdef KECCAK_COMPLEMENTING_TRANSFORM
    A[0][1] = ~A[0][1];
    A[0][2] = ~A[0][2];
    A[1][3] = ~A[1][3];
    A[2][2] = ~A[2][2];
    A[3][2] = ~A[3][2];
    A[4][0] = ~A[4][0];
#endif

    for (i = 0; i < 24; i += 2) {
        Round(T, A, i);
        Round(A, T, i + 1);
    }

#ifdef KECCAK_COMPLEMENTING_TRANSFORM
    A[0][1] = ~A[0][1];
    A[0][2] = ~A[0][2];
    A[1][3] = ~A[1][3];
    A[2][2] = ~A[2][2];
    A[3][2] = ~A[3][2];
    A[4][0] = ~A[4][0];
#endif
}

static uint64_t BitInterleave(uint64_t Ai)
{
    if (BIT_INTERLEAVE) {
        uint32_t hi = (uint32_t)(Ai >> 32), lo = (uint32_t)Ai;
        uint32_t t0, t1;

        t0 = lo & 0x55555555;
        t0 |= t0 >> 1;  t0 &= 0x33333333;
        t0 |= t0 >> 2;  t0 &= 0x0f0f0f0f;
        t0 |= t0 >> 4;  t0 &= 0x00ff00ff;
        t0 |= t0 >> 8;  t0 &= 0x0000ffff;

        t1 = hi & 0x55555555;
        t1 |= t1 >> 1;  t1 &= 0x33333333;
        t1 |= t1 >> 2;  t1 &= 0x0f0f0f0f;
        t1 |= t1 >> 4;  t1 &= 0x00ff00ff;
        t1 |= t1 >> 8;  t1 <<= 16;

        lo &= 0xaaaaaaaa;
        lo |= lo << 1;  lo &= 0xcccccccc;
        lo |= lo << 2;  lo &= 0xf0f0f0f0;
        lo |= lo << 4;  lo &= 0xff00ff00;
        lo |= lo << 8;  lo >>= 16;

        hi &= 0xaaaaaaaa;
        hi |= hi << 1;  hi &= 0xcccccccc;
        hi |= hi << 2;  hi &= 0xf0f0f0f0;
        hi |= hi << 4;  hi &= 0xff00ff00;
        hi |= hi << 8;  hi &= 0xffff0000;

        Ai = ((uint64_t)(hi | lo) << 32) | (t1 | t0);
    }

    return Ai;
}

static uint64_t BitDeinterleave(uint64_t Ai)
{
    if (BIT_INTERLEAVE) {
        uint32_t hi = (uint32_t)(Ai >> 32), lo = (uint32_t)Ai;
        uint32_t t0, t1;

        t0 = lo & 0x0000ffff;
        t0 |= t0 << 8;  t0 &= 0x00ff00ff;
        t0 |= t0 << 4;  t0 &= 0x0f0f0f0f;
        t0 |= t0 << 2;  t0 &= 0x33333333;
        t0 |= t0 << 1;  t0 &= 0x55555555;

        t1 = hi << 16;
        t1 |= t1 >> 8;  t1 &= 0xff00ff00;
        t1 |= t1 >> 4;  t1 &= 0xf0f0f0f0;
        t1 |= t1 >> 2;  t1 &= 0xcccccccc;
        t1 |= t1 >> 1;  t1 &= 0xaaaaaaaa;

        lo >>= 16;
        lo |= lo << 8;  lo &= 0x00ff00ff;
        lo |= lo << 4;  lo &= 0x0f0f0f0f;
        lo |= lo << 2;  lo &= 0x33333333;
        lo |= lo << 1;  lo &= 0x55555555;

        hi &= 0xffff0000;
        hi |= hi >> 8;  hi &= 0xff00ff00;
        hi |= hi >> 4;  hi &= 0xf0f0f0f0;
        hi |= hi >> 2;  hi &= 0xcccccccc;
        hi |= hi >> 1;  hi &= 0xaaaaaaaa;

        Ai = ((uint64_t)(hi | lo) << 32) | (t1 | t0);
    }

    return Ai;
}

 // Keccak1600_Absorb can be called multiple times; at each invocation the
 // largest multiple of |r| out of |len| bytes are processed. The
 // remaining amount of bytes is returned. This is done to spare caller
 // trouble of calculating the largest multiple of |r|. |r| can be viewed
 // as blocksize. It is commonly (1600 - 256*n)/8, e.g. 168, 136, 104,
 // 72, but can also be (1600 - 448)/8 = 144. All this means that message
 // padding and intermediate sub-block buffering, byte- or bitwise, is
 // caller's responsibility.
size_t Keccak1600_Absorb(uint64_t A[KECCAK1600_ROWS][KECCAK1600_ROWS], const uint8_t *inp, size_t len,
                   size_t r)
{
    uint64_t *A_flat = (uint64_t *)A;
    size_t i, w = r / 8;

    assert(r < (25 * sizeof(A[0][0])) && (r % 8) == 0);

    while (len >= r) {
        for (i = 0; i < w; i++) {
            uint64_t Ai = (uint64_t)inp[0]       | (uint64_t)inp[1] << 8  |
                          (uint64_t)inp[2] << 16 | (uint64_t)inp[3] << 24 |
                          (uint64_t)inp[4] << 32 | (uint64_t)inp[5] << 40 |
                          (uint64_t)inp[6] << 48 | (uint64_t)inp[7] << 56;
            inp += 8;

            A_flat[i] ^= BitInterleave(Ai);
        }
        KeccakF1600(A);
        len -= r;
    }

    return len;
}

void Keccak1600_Squeeze(uint64_t A[KECCAK1600_ROWS][KECCAK1600_ROWS], uint8_t *out, size_t len, size_t r, int padded)
// Keccak1600_Squeeze can be called multiple times to incrementally 
{
    uint64_t *A_flat = (uint64_t *)A;
    size_t i, w = r / 8;

    assert(r < (25 * sizeof(A[0][0])) && (r % 8) == 0);

    while (len != 0) {
        if (padded) {
            KeccakF1600(A); 
        }
        padded = 1;
        for (i = 0; i < w && len != 0; i++) {
            uint64_t Ai = BitDeinterleave(A_flat[i]);

            if (len < 8) {
                for (i = 0; i < len; i++) {
                    *out++ = (uint8_t)Ai;
                    Ai >>= 8;
                }
                return;
            }

            out[0] = (uint8_t)(Ai);
            out[1] = (uint8_t)(Ai >> 8);
            out[2] = (uint8_t)(Ai >> 16);
            out[3] = (uint8_t)(Ai >> 24);
            out[4] = (uint8_t)(Ai >> 32);
            out[5] = (uint8_t)(Ai >> 40);
            out[6] = (uint8_t)(Ai >> 48);
            out[7] = (uint8_t)(Ai >> 56);
            out += 8;
            len -= 8;
        }
    }
}

#else

size_t Keccak1600_Absorb_hw(uint64_t A[KECCAK1600_ROWS][KECCAK1600_ROWS], const uint8_t *inp, size_t len,
                       size_t r);

size_t Keccak1600_Absorb(uint64_t A[KECCAK1600_ROWS][KECCAK1600_ROWS], const uint8_t *inp, size_t len,
                   size_t r) {
    return Keccak1600_Absorb_hw(A, inp, len, r);
}

size_t Keccak1600_Squeeze_hw(uint64_t A[KECCAK1600_ROWS][KECCAK1600_ROWS], const uint8_t *out, size_t len,
                        size_t r, int padded);

void Keccak1600_Squeeze(uint64_t A[KECCAK1600_ROWS][KECCAK1600_ROWS], uint8_t *out, size_t len, size_t r, int padded) {
    Keccak1600_Squeeze_hw(A, out, len, r, padded);
}

#endif // !KECCAK1600_ASM
