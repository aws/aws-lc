/* Copyright (c) 2018, Google Inc.
 *
 * Permission to use, copy, modify, and/or distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
 * SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION
 * OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN
 * CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE. */

#ifndef OPENSSL_HEADER_SHA_INTERNAL_H
#define OPENSSL_HEADER_SHA_INTERNAL_H

#include <openssl/base.h>

#include "../../internal.h"
#include "../cpucap/internal.h"

#if defined(__cplusplus)
extern "C" {
#endif

// Internal SHA2 constants

// SHA*_CHAINING_LENGTH is the chaining length in bytes of SHA-*
// It corresponds to the length in bytes of the h part of the state
#define SHA1_CHAINING_LENGTH 20
#define SHA224_CHAINING_LENGTH 32
#define SHA256_CHAINING_LENGTH 32
#define SHA384_CHAINING_LENGTH 64
#define SHA512_CHAINING_LENGTH 64
#define SHA512_224_CHAINING_LENGTH 64
#define SHA512_256_CHAINING_LENGTH 64


// SHA3 constants, from NIST FIPS202.
// https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.202.pdf
#define KECCAK1600_ROWS 5
#define KECCAK1600_WIDTH 1600

#define SHA3_224_CAPACITY_BYTES 56
#define SHA3_224_DIGEST_BITLENGTH 224
#define SHA3_224_DIGEST_LENGTH 28

#define SHA3_256_CAPACITY_BYTES 64
#define SHA3_256_DIGEST_BITLENGTH 256
#define SHA3_256_DIGEST_LENGTH 32

#define SHA3_384_CAPACITY_BYTES 96
#define SHA3_384_DIGEST_BITLENGTH 384
#define SHA3_384_DIGEST_LENGTH 48

#define SHA3_512_CAPACITY_BYTES 128
#define SHA3_512_DIGEST_BITLENGTH 512
#define SHA3_512_DIGEST_LENGTH 64

#define SHA3_BLOCKSIZE(bitlen) (KECCAK1600_WIDTH - bitlen * 2) / 8
#define SHA3_PAD_CHAR 0x06

// SHAKE constants, from NIST FIPS202.
// https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.202.pdf
#define SHAKE_PAD_CHAR 0x1F
#define SHAKE128_BLOCKSIZE ((KECCAK1600_WIDTH - 128 * 2) / 8)
#define SHAKE256_BLOCKSIZE ((KECCAK1600_WIDTH - 256 * 2) / 8)
#define XOF_BLOCKBYTES SHAKE128_BLOCKSIZE

// SHAKE128 has the maximum block size among the SHA3/SHAKE algorithms.
#define SHA3_MAX_BLOCKSIZE SHAKE128_BLOCKSIZE

// Define state flag values for Keccak-based functions
#define KECCAK1600_STATE_ABSORB     0 
// KECCAK1600_STATE_SQUEEZE is set when |SHAKE_Squeeze| is called.
// It remains set while |SHAKE_Squeeze| is called repeatedly to output 
// chunks of the XOF output.
#define KECCAK1600_STATE_SQUEEZE    1  
// KECCAK1600_STATE_FINAL is set once |SHAKE_Final| is called 
// so that |SHAKE_Squeeze| cannot be called anymore.
#define KECCAK1600_STATE_FINAL      2 

typedef struct keccak_st KECCAK1600_CTX;

// The data buffer should have at least the maximum number of
// block size bytes to fit any SHA3/SHAKE block length.
struct keccak_st {
  uint64_t A[KECCAK1600_ROWS][KECCAK1600_ROWS];
  size_t block_size;                               // cached ctx->digest->block_size
  size_t md_size;                                  // output length, variable in XOF (SHAKE)
  size_t buf_load;                                 // used bytes in below buffer
  uint8_t buf[SHA3_MAX_BLOCKSIZE];                 // should have at least the max data block size bytes
  uint8_t pad;                                     // padding character
  uint8_t state;                                  // denotes the keccak phase (absorb, squeeze, final)
};

// Define SHA{n}[_{variant}]_ASM if sha{n}_block_data_order[_{variant}] is
// defined in assembly.

#if defined(OPENSSL_PPC64LE)
#define SHA1_ALTIVEC

void sha1_block_data_order(uint32_t *state, const uint8_t *data,
                             size_t num_blocks);

#elif !defined(OPENSSL_NO_ASM) && defined(OPENSSL_ARM)

#define SHA1_ASM_NOHW
#define SHA256_ASM_NOHW
#define SHA512_ASM_NOHW

#define SHA1_ASM_HW
OPENSSL_INLINE int sha1_hw_capable(void) {
  return CRYPTO_is_ARMv8_SHA1_capable();
}

#define SHA1_ASM_NEON
void sha1_block_data_order_neon(uint32_t state[5], const uint8_t *data,
                                size_t num);

#define SHA256_ASM_HW
OPENSSL_INLINE int sha256_hw_capable(void) {
  return CRYPTO_is_ARMv8_SHA256_capable();
}

#define SHA256_ASM_NEON
void sha256_block_data_order_neon(uint32_t state[8], const uint8_t *data,
                                  size_t num);

// Armv8.2 SHA-512 instructions are not available in 32-bit.
#define SHA512_ASM_NEON
void sha512_block_data_order_neon(uint64_t state[8], const uint8_t *data,
                                  size_t num);

#elif !defined(OPENSSL_NO_ASM) && defined(OPENSSL_AARCH64)

#define SHA1_ASM_NOHW
#define SHA256_ASM_NOHW
#define SHA512_ASM_NOHW

#define SHA1_ASM_HW
OPENSSL_INLINE int sha1_hw_capable(void) {
  return CRYPTO_is_ARMv8_SHA1_capable();
}

#define SHA256_ASM_HW
OPENSSL_INLINE int sha256_hw_capable(void) {
  return CRYPTO_is_ARMv8_SHA256_capable();
}

#define SHA512_ASM_HW
OPENSSL_INLINE int sha512_hw_capable(void) {
  return CRYPTO_is_ARMv8_SHA512_capable();
}

#elif !defined(OPENSSL_NO_ASM) && defined(OPENSSL_X86)

#define SHA1_ASM_NOHW
#define SHA256_ASM_NOHW

#define SHA1_ASM_SSSE3
OPENSSL_INLINE int sha1_ssse3_capable(void) {
  // TODO(davidben): Do we need to check the FXSR bit? The Intel manual does not
  // say to.
  return CRYPTO_is_SSSE3_capable() && CRYPTO_is_FXSR_capable();
}
void sha1_block_data_order_ssse3(uint32_t state[5], const uint8_t *data,
                                 size_t num);

#define SHA1_ASM_AVX
OPENSSL_INLINE int sha1_avx_capable(void) {
  // Pre-Zen AMD CPUs had slow SHLD/SHRD; Zen added the SHA extension; see the
  // discussion in sha1-586.pl.
  //
  // TODO(davidben): Should we enable SHAEXT on 32-bit x86?
  // TODO(davidben): Do we need to check the FXSR bit? The Intel manual does not
  // say to.
  return CRYPTO_is_AVX_capable() && CRYPTO_is_intel_cpu() &&
         CRYPTO_is_FXSR_capable();
}
void sha1_block_data_order_avx(uint32_t state[5], const uint8_t *data,
                               size_t num);

#define SHA256_ASM_SSSE3
OPENSSL_INLINE int sha256_ssse3_capable(void) {
  // TODO(davidben): Do we need to check the FXSR bit? The Intel manual does not
  // say to.
  return CRYPTO_is_SSSE3_capable() && CRYPTO_is_FXSR_capable();
}
void sha256_block_data_order_ssse3(uint32_t state[8], const uint8_t *data,
                                   size_t num);

#define SHA256_ASM_AVX
OPENSSL_INLINE int sha256_avx_capable(void) {
  // Pre-Zen AMD CPUs had slow SHLD/SHRD; Zen added the SHA extension; see the
  // discussion in sha1-586.pl.
  //
  // TODO(davidben): Should we enable SHAEXT on 32-bit x86?
  // TODO(davidben): Do we need to check the FXSR bit? The Intel manual does not
  // say to.
  return CRYPTO_is_AVX_capable() && CRYPTO_is_intel_cpu() &&
         CRYPTO_is_FXSR_capable();
}
void sha256_block_data_order_avx(uint32_t state[8], const uint8_t *data,
                                 size_t num);

// TODO(crbug.com/boringssl/673): Move the remaining CPU dispatch to C.
#define SHA512_ASM
void sha512_block_data_order(uint64_t state[8], const uint8_t *data,
                             size_t num_blocks);

#elif !defined(OPENSSL_NO_ASM) && defined(OPENSSL_X86_64)

#define SHA1_ASM_NOHW
#define SHA256_ASM_NOHW
#define SHA512_ASM_NOHW

#define SHA1_ASM_HW
OPENSSL_INLINE int sha1_hw_capable(void) {
  return CRYPTO_is_SHAEXT_capable() && CRYPTO_is_SSSE3_capable();
}

#define SHA1_ASM_AVX2
OPENSSL_INLINE int sha1_avx2_capable(void) {
  // TODO: Simplify this logic, which was extracted from the assembly:
  //  * Does AVX2 imply SSSE3?
  //  * sha1_block_data_order_avx2 does not seem to use SSSE3 instructions.
  return CRYPTO_is_AVX2_capable() && CRYPTO_is_BMI2_capable() &&
         CRYPTO_is_BMI1_capable() && CRYPTO_is_SSSE3_capable();
}
void sha1_block_data_order_avx2(uint32_t state[5], const uint8_t *data,
                                size_t num);

#define SHA1_ASM_AVX
OPENSSL_INLINE int sha1_avx_capable(void) {
  // TODO: Simplify this logic, which was extracted from the assembly:
  //  * Does AVX imply SSSE3?
  //  * sha1_block_data_order_avx does not seem to use SSSE3 instructions.
  // Pre-Zen AMD CPUs had slow SHLD/SHRD; Zen added the SHA extension; see the
  // discussion in sha1-586.pl.
  return CRYPTO_is_AVX_capable() && CRYPTO_is_SSSE3_capable() &&
         CRYPTO_is_intel_cpu();
}
void sha1_block_data_order_avx(uint32_t state[5], const uint8_t *data,
                               size_t num);

#define SHA1_ASM_SSSE3
OPENSSL_INLINE int sha1_ssse3_capable(void) {
  return CRYPTO_is_SSSE3_capable();
}
void sha1_block_data_order_ssse3(uint32_t state[5], const uint8_t *data,
                                 size_t num);

#define SHA256_ASM_HW
OPENSSL_INLINE int sha256_hw_capable(void) {
  return CRYPTO_is_SHAEXT_capable();
}

#define SHA256_ASM_AVX
OPENSSL_INLINE int sha256_avx_capable(void) {
  // TODO: Simplify this logic, which was extracted from the assembly:
  //  * Does AVX imply SSSE3?
  //  * sha256_block_data_order_avx does not seem to use SSSE3 instructions.
  // Pre-Zen AMD CPUs had slow SHLD/SHRD; Zen added the SHA extension; see the
  // discussion in sha1-586.pl.
  return CRYPTO_is_AVX_capable() && CRYPTO_is_SSSE3_capable() &&
         CRYPTO_is_intel_cpu();
}
void sha256_block_data_order_avx(uint32_t state[8], const uint8_t *data,
                                 size_t num);

#define SHA256_ASM_SSSE3
OPENSSL_INLINE int sha256_ssse3_capable(void) {
  return CRYPTO_is_SSSE3_capable();
}
void sha256_block_data_order_ssse3(uint32_t state[8], const uint8_t *data,
                                   size_t num);

#define SHA512_ASM_AVX
OPENSSL_INLINE int sha512_avx_capable(void) {
  // TODO: Simplify this logic, which was extracted from the assembly:
  //  * Does AVX imply SSSE3?
  //  * sha512_block_data_order_avx does not seem to use SSSE3 instructions.
  // Pre-Zen AMD CPUs had slow SHLD/SHRD; Zen added the SHA extension; see the
  // discussion in sha1-586.pl.
  return CRYPTO_is_AVX_capable() && CRYPTO_is_SSSE3_capable() &&
         CRYPTO_is_intel_cpu();
}
void sha512_block_data_order_avx(uint64_t state[8], const uint8_t *data,
                                 size_t num);

#endif

#if defined(SHA1_ASM_HW)
void sha1_block_data_order_hw(uint32_t state[5], const uint8_t *data,
                              size_t num);
#endif
#if defined(SHA1_ASM_NOHW)
void sha1_block_data_order_nohw(uint32_t state[5], const uint8_t *data,
                                size_t num);
#endif

#if defined(SHA256_ASM_HW)
void sha256_block_data_order_hw(uint32_t state[8], const uint8_t *data,
                                size_t num);
#endif
#if defined(SHA256_ASM_NOHW)
void sha256_block_data_order_nohw(uint32_t state[8], const uint8_t *data,
                                  size_t num);
#endif

#if defined(SHA512_ASM_HW)
void sha512_block_data_order_hw(uint64_t state[8], const uint8_t *data,
                                size_t num);
#endif

#if defined(SHA512_ASM_NOHW)
void sha512_block_data_order_nohw(uint64_t state[8], const uint8_t *data,
                                  size_t num);
#endif

#if !defined(OPENSSL_NO_ASM) && defined(OPENSSL_AARCH64)
#define KECCAK1600_ASM
#endif

// SHAx_Init_from_state is a low-level function that initializes |sha| with a
// custom state. |h| is the hash state in big endian. |n| is the number of bits
// processed at this point. It must be a multiple of |SHAy_CBLOCK*8|,
// where SHAy=SHA1 if SHAx=SHA1, SHAy=SHA256 if SHAx=SHA224 or SHA256, and
// SHAy=SHA512 otherwise.
// This function returns one on success and zero on error.
// This function is for internal use only and should never be directly called.
OPENSSL_EXPORT int SHA1_Init_from_state(
    SHA_CTX *sha, const uint8_t h[SHA1_CHAINING_LENGTH], uint64_t n);
OPENSSL_EXPORT int SHA224_Init_from_state(
    SHA256_CTX *sha, const uint8_t h[SHA224_CHAINING_LENGTH], uint64_t n);
OPENSSL_EXPORT int SHA256_Init_from_state(
    SHA256_CTX *sha, const uint8_t h[SHA256_CHAINING_LENGTH], uint64_t n);
OPENSSL_EXPORT int SHA384_Init_from_state(
    SHA512_CTX *sha, const uint8_t h[SHA384_CHAINING_LENGTH], uint64_t n);
OPENSSL_EXPORT int SHA512_Init_from_state(
    SHA512_CTX *sha, const uint8_t h[SHA512_CHAINING_LENGTH], uint64_t n);
OPENSSL_EXPORT int SHA512_224_Init_from_state(
    SHA512_CTX *sha, const uint8_t h[SHA512_224_CHAINING_LENGTH], uint64_t n);
OPENSSL_EXPORT int SHA512_256_Init_from_state(
    SHA512_CTX *sha, const uint8_t h[SHA512_256_CHAINING_LENGTH], uint64_t n);

// SHAx_get_state is a low-level function that exports the hash state in big
// endian into |out_h| and the number of bits processed at this point in
// |out_n|. |SHAx_Final| must not have been called before (otherwise results
// are not guaranteed). Furthermore, the number of bytes processed by
// |SHAx_Update| must be a multiple of the block length |SHAy_CBLOCK| and
// must be less than 2^61 (otherwise it fails). See comment above about
// |SHAx_Init_from_state| for the definition of SHAy.
// This function returns one on success and zero on error.
// This function is for internal use only and should never be directly called.
OPENSSL_EXPORT int SHA1_get_state(
    SHA_CTX *ctx, uint8_t out_h[SHA1_CHAINING_LENGTH], uint64_t *out_n);
OPENSSL_EXPORT int SHA224_get_state(
    SHA256_CTX *ctx, uint8_t out_h[SHA224_CHAINING_LENGTH], uint64_t *out_n);
OPENSSL_EXPORT int SHA256_get_state(
    SHA256_CTX *ctx, uint8_t out_h[SHA256_CHAINING_LENGTH], uint64_t *out_n);
OPENSSL_EXPORT int SHA384_get_state(
    SHA512_CTX *ctx, uint8_t out_h[SHA384_CHAINING_LENGTH], uint64_t *out_n);
OPENSSL_EXPORT int SHA512_get_state(
    SHA512_CTX *ctx, uint8_t out_h[SHA512_CHAINING_LENGTH], uint64_t *out_n);
OPENSSL_EXPORT int SHA512_224_get_state(
    SHA512_CTX *ctx, uint8_t out_h[SHA512_224_CHAINING_LENGTH],
    uint64_t *out_n);
OPENSSL_EXPORT int SHA512_256_get_state(
    SHA512_CTX *ctx, uint8_t out_h[SHA512_256_CHAINING_LENGTH],
    uint64_t *out_n);

// SHA3_224 writes the digest of |len| bytes from |data| to |out| and returns |out|.
// There must be at least |SHA3_224_DIGEST_LENGTH| bytes of space in |out|.
// On failure |SHA3_224| returns NULL.
OPENSSL_EXPORT uint8_t *SHA3_224(const uint8_t *data, size_t len,
                                 uint8_t out[SHA3_224_DIGEST_LENGTH]);

// SHA3_256 writes the digest of |len| bytes from |data| to |out| and returns |out|.
// There must be at least |SHA3_256_DIGEST_LENGTH| bytes of space in |out|.
// On failure |SHA3_256| returns NULL.
OPENSSL_EXPORT uint8_t *SHA3_256(const uint8_t *data, size_t len,
                                 uint8_t out[SHA3_256_DIGEST_LENGTH]);

// SHA3_384 writes the digest of |len| bytes from |data| to |out| and returns |out|.
// There must be at least |SHA3_384_DIGEST_LENGTH| bytes of space in |out|.
// On failure |SHA3_384| returns NULL.
OPENSSL_EXPORT uint8_t *SHA3_384(const uint8_t *data, size_t len,
                                 uint8_t out[SHA3_384_DIGEST_LENGTH]);

// SHA3_512 writes the digest of |len| bytes from |data| to |out| and returns |out|.
// There must be at least |SHA3_512_DIGEST_LENGTH| bytes of space in |out|.
// On failure |SHA3_512| returns NULL.
OPENSSL_EXPORT uint8_t *SHA3_512(const uint8_t *data, size_t len,
                  uint8_t out[SHA3_512_DIGEST_LENGTH]);

// SHAKE128 writes the |out_len| bytes output from |in_len| bytes |data|
// to |out| and returns |out| on success and NULL on failure.
OPENSSL_EXPORT uint8_t *SHAKE128(const uint8_t *data, const size_t in_len,
                                 uint8_t *out, size_t out_len);

// SHAKE256 writes |out_len| bytes output from |in_len| bytes |data|
// to |out| and returns |out| on success and NULL on failure.
OPENSSL_EXPORT uint8_t *SHAKE256(const uint8_t *data, const size_t in_len,
                                 uint8_t *out, size_t out_len);

// SHA3_Init initialises |ctx| fields through |FIPS202_Init| and 
// returns 1 on success and 0 on failure.
OPENSSL_EXPORT int SHA3_Init(KECCAK1600_CTX *ctx, size_t bitlen);

 // SHA3_Update check |ctx| pointer and |len| value, calls |FIPS202_Update| 
 // and returns 1 on success and 0 on failure.
int SHA3_Update(KECCAK1600_CTX *ctx, const void *data, size_t len);

// SHA3_Final pads the last data block and absorbs it through |FIPS202_Finalize|.
// It then calls |Keccak1600_Squeeze| and returns 1 on success 
// and 0 on failure.
int SHA3_Final(uint8_t *md, KECCAK1600_CTX *ctx);

// SHAKE_Init initialises |ctx| fields through |FIPS202_Init| and 
// returns 1 on success and 0 on failure.
int SHAKE_Init(KECCAK1600_CTX *ctx, size_t block_size);

// SHAKE_Absorb checks |ctx| pointer and |len| values. It updates and absorbs 
// input blocks via |FIPS202_Update|.
int SHAKE_Absorb(KECCAK1600_CTX *ctx, const void *data,
                               size_t len);

// SHAKE_Squeeze pads the last data block and absorbs it through 
// |FIPS202_Finalize| on first call. It writes |len| bytes of incremental 
// XOF output to |md| and returns 1 on success and 0 on failure. It can be 
// called multiple times.
int SHAKE_Squeeze(uint8_t *md, KECCAK1600_CTX *ctx, size_t len);

// SHAKE_Final writes |len| bytes of finalized extendible output to |md|, returns 1 on
// success and 0 on failure. It should be called once to finalize absorb and
// squeeze phases. Incremental XOF output should be generated via |SHAKE_Squeeze|.
int SHAKE_Final(uint8_t *md, KECCAK1600_CTX *ctx, size_t len);

// Keccak1600_Absorb processes the largest multiple of |r| (block size) out of
// |len| bytes and returns the remaining number of bytes.
size_t Keccak1600_Absorb(uint64_t A[KECCAK1600_ROWS][KECCAK1600_ROWS],
                                  const uint8_t *data, size_t len, size_t r);

// Keccak1600_Squeeze generates |out| value of |len| bytes (per call). It can be called
// multiple times when used as eXtendable Output Function. |padded| indicates
// whether it is the first call to Keccak1600_Squeeze; i.e., if the current block has
// been already processed and padded right after the last call to Keccak1600_Absorb.
// Squeezes full blocks of |r| bytes each. When performing multiple squeezes, any
// left over bytes from previous squeezes are not consumed, and |len| must be a
// multiple of the block size (except on the final squeeze).
OPENSSL_EXPORT void Keccak1600_Squeeze(uint64_t A[KECCAK1600_ROWS][KECCAK1600_ROWS],
                                 uint8_t *out, size_t len, size_t r, int padded);

#if defined(__cplusplus)
}  // extern "C"
#endif

#endif  // OPENSSL_HEADER_SHA_INTERNAL_H
