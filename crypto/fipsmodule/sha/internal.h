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

#if defined(__cplusplus)
extern "C" {
#endif

// Internal SHA2 constants

// SHA1_CHAINING_LENGTH is the chaining length in bytes of SHA-1
// It corresponds to the length in bytes of the h part of the state
#define SHA1_CHAINING_LENGTH 20

// SHA224_CHAINING_LENGTH is the chaining length in bytes of SHA-224
// It corresponds to the length in bytes of the h part of the state
#define SHA224_CHAINING_LENGTH 32

// SHA256_CHAINING_LENGTH is the chaining length in bytes of SHA-256
// It corresponds to the length in bytes of the h part of the state
#define SHA256_CHAINING_LENGTH 32

// SHA384_CHAINING_LENGTH is the chaining length in bytes of SHA-384
// It corresponds to the length in bytes of the h part of the state
#define SHA384_CHAINING_LENGTH 64

// SHA512_CHAINING_LENGTH is the chaining length in bytes of SHA-512
// It corresponds to the length in bytes of the h part of the state
#define SHA512_CHAINING_LENGTH 64

// SHA512_224_CHAINING_LENGTH is the chaining length in bytes of SHA-512-224
// It corresponds to the length in bytes of the h part of the state
#define SHA512_224_CHAINING_LENGTH 64

// SHA512_256_CHAINING_LENGTH is the chaining length in bytes of SHA-512-256
// It corresponds to the length in bytes of the h part of the state
#define SHA512_256_CHAINING_LENGTH 64


// SHA3 constants, from NIST FIPS202.
// https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.202.pdf
#define SHA3_ROWS 5
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
#define SHAKE128_BLOCKSIZE (KECCAK1600_WIDTH - 128 * 2) / 8
#define SHAKE256_BLOCKSIZE (KECCAK1600_WIDTH - 256 * 2) / 8

// SHAKE128 has the maximum block size among the SHA3/SHAKE algorithms.
#define SHA3_MAX_BLOCKSIZE SHAKE128_BLOCKSIZE

typedef struct keccak_st KECCAK1600_CTX;

// The data buffer should have at least the maximum number of
// block size bytes to fit any SHA3/SHAKE block length.
struct keccak_st {
  uint64_t A[SHA3_ROWS][SHA3_ROWS];
  size_t block_size;                               // cached ctx->digest->block_size
  size_t md_size;                                  // output length, variable in XOF (SHAKE)
  size_t buf_load;                                 // used bytes in below buffer
  uint8_t buf[SHA3_MAX_BLOCKSIZE];                 // should have at least the max data block size bytes
  uint8_t pad;
};

#if defined(OPENSSL_PPC64LE) ||                          \
    (!defined(OPENSSL_NO_ASM) &&                         \
     (defined(OPENSSL_X86) || defined(OPENSSL_X86_64) || \
      defined(OPENSSL_ARM) || defined(OPENSSL_AARCH64)))
// POWER has an intrinsics-based implementation of SHA-1 and thus the functions
// normally defined in assembly are available even with |OPENSSL_NO_ASM| in
// this case.
#define SHA1_ASM
void sha1_block_data_order(uint32_t *state, const uint8_t *in,
                           size_t num_blocks);
#endif

#if !defined(OPENSSL_NO_ASM) &&                         \
    (defined(OPENSSL_X86) || defined(OPENSSL_X86_64) || \
     defined(OPENSSL_ARM) || defined(OPENSSL_AARCH64))
#define SHA256_ASM
#define SHA512_ASM
void sha256_block_data_order(uint32_t *state, const uint8_t *in,
                             size_t num_blocks);
void sha512_block_data_order(uint64_t *state, const uint8_t *in,
                             size_t num_blocks);
#endif

#if !defined(OPENSSL_NO_ASM) && defined(OPENSSL_AARCH64)
#define KECCAK1600_ASM
#endif

// SHA1_Init_from_state is a low-level function that initializes |sha| with a
// custom state. |h| is the hash state in big endian. |n| is the number of bits
// processed at this point. It must be a multiple of |SHA256_CBLOCK*8|.
// It returns one on success and zero on programmer error.
// This function is for internal use only and should never be directly called.
OPENSSL_EXPORT int SHA1_Init_from_state(SHA_CTX *sha,
                                        const uint8_t h[SHA1_CHAINING_LENGTH],
                                        uint64_t n);

// SHA1_get_state is a low-level function that exports the hash state in big
// endian into |out_n| and the number of bits processed at this point in
// |out_n|. SHA1_Final must not have been called before (otherwise results
// are not guaranteed). Furthermore, the number of bytes processed by
// SHA1_Update must be a multiple of the block length |SHA1_CBLOCK|
// (otherwise it fails). It returns one on success and zero on programmer
// error.
// This function is for internal use only and should never be directly called.
OPENSSL_EXPORT int SHA1_get_state(SHA_CTX *ctx,
                                  uint8_t out_h[SHA1_CHAINING_LENGTH],
                                  uint64_t *out_n);

// SHA224_Init_from_state is a low-level function that initializes |sha| with a
// custom state. |h| is the hash state in big endian. |n| is the number of bits
// processed at this point. It must be a multiple of |SHA256_CBLOCK*8|.
// It returns one on success and zero on programmer error.
// This function is for internal use only and should never be directly called.
OPENSSL_EXPORT int SHA224_Init_from_state(
    SHA256_CTX *sha, const uint8_t h[SHA224_CHAINING_LENGTH], uint64_t n);

// SHA224_get_state is a low-level function that exports the hash state in big
// endian into |out_n| and the number of bits processed at this point in
// |out_n|. SHA224_Final must not have been called before (otherwise results
// are not guaranteed). Furthermore, the number of bytes processed by
// SHA224_Update must be a multiple of the block length |SHA224_CBLOCK|
// (otherwise it fails). It returns one on success and zero on programmer
// error.
// This function is for internal use only and should never be directly called.
OPENSSL_EXPORT int SHA224_get_state(SHA256_CTX *ctx,
                                    uint8_t out_h[SHA224_CHAINING_LENGTH],
                                    uint64_t *out_n);

// SHA256_Init_from_state is a low-level function that initializes |sha| with a
// custom state. |h| is the hash state in big endian. |n| is the number of bits
// processed at this point. It must be a multiple of |SHA256_CBLOCK*8|.
// It returns one on success and zero on programmer error.
// This function is for internal use only and should never be directly called.
OPENSSL_EXPORT int SHA256_Init_from_state(
    SHA256_CTX *sha, const uint8_t h[SHA256_CHAINING_LENGTH], uint64_t n);

// SHA256_get_state is a low-level function that exports the hash state in big
// endian into |out_n| and the number of bits processed at this point in
// |out_n|. SHA256_Final must not have been called before (otherwise results
// are not guaranteed). Furthermore, the number of bytes processed by
// SHA256_Update must be a multiple of the block length |SHA256_CBLOCK|
// (otherwise it fails). It returns one on success and zero on programmer
// error.
// This function is for internal use only and should never be directly called.
OPENSSL_EXPORT int SHA256_get_state(SHA256_CTX *ctx,
                                    uint8_t out_h[SHA256_CHAINING_LENGTH],
                                    uint64_t *out_n);

// SHA384_Init_from_state is a low-level function that initializes |sha| with a
// custom state. |h| is the hash state in big endian. |n| is the number of bits
// processed at this point. It must be a multiple of |SHA512_CBLOCK*8|.
// It returns one on success and zero on programmer error.
// This function is for internal use only and should never be directly called.
OPENSSL_EXPORT int SHA384_Init_from_state(
    SHA512_CTX *sha, const uint8_t h[SHA384_CHAINING_LENGTH], uint64_t n);

// SHA384_get_state is a low-level function that exports the hash state in big
// endian into |out_n| and the number of bits processed at this point in
// |out_n|. SHA384_Final must not have been called before (otherwise results
// are not guaranteed). Furthermore, the number of bytes processed by
// SHA384_Update must be a multiple of the block length |SHA384_CBLOCK|
// (otherwise it fails). It returns one on success and zero on programmer
// error.
// This function is for internal use only and should never be directly called.
OPENSSL_EXPORT int SHA384_get_state(SHA512_CTX *ctx,
                                    uint8_t out_h[SHA384_CHAINING_LENGTH],
                                    uint64_t *out_n);

// SHA512_Init_from_state is a low-level function that initializes |sha| with a
// custom state. |h| is the hash state in big endian. |n| is the number of bits
// processed at this point. It must be a multiple of |SHA512_CBLOCK*8|.
// It returns one on success and zero on programmer error.
// This function is for internal use only and should never be directly called.
OPENSSL_EXPORT int SHA512_Init_from_state(
    SHA512_CTX *sha, const uint8_t h[SHA512_CHAINING_LENGTH], uint64_t n);

// SHA512_get_state is a low-level function that exports the hash state in big
// endian into |out_n| and the number of bits processed at this point in
// |out_n|. SHA512_Final must not have been called before (otherwise results
// are not guaranteed). Furthermore, the number of bytes processed by
// SHA512_Update must be a multiple of the block length |SHA512_CBLOCK|
// (otherwise it fails). It returns one on success and zero on programmer
// error.
// This function is for internal use only and should never be directly called.
OPENSSL_EXPORT int SHA512_get_state(SHA512_CTX *ctx,
                                    uint8_t out_h[SHA512_CHAINING_LENGTH],
                                    uint64_t *out_n);

// SHA512_224_Init_from_state is a low-level function that initializes |sha|
// with a custom state. |h| is the hash state in big endian. |n| is the number
// of bits processed at this point. It must be a multiple of |SHA512_CBLOCK*8|.
// It returns one on success and zero on programmer error.
// This function is for internal use only and should never be directly called.
OPENSSL_EXPORT int SHA512_224_Init_from_state(
    SHA512_CTX *sha, const uint8_t h[SHA512_224_CHAINING_LENGTH], uint64_t n);

// SHA512_224_get_state is a low-level function that exports the hash state in
// big endian into |out_n| and the number of bits processed at this point in
// |out_n|. SHA512_224_Final must not have been called before (otherwise results
// are not guaranteed). Furthermore, the number of bytes processed by
// SHA512_224_Update must be a multiple of the block length |SHA512_CBLOCK|
// (otherwise it fails). It returns one on success and zero on programmer
// error.
// This function is for internal use only and should never be directly called.
OPENSSL_EXPORT int SHA512_224_get_state(
    SHA512_CTX *ctx, uint8_t out_h[SHA512_224_CHAINING_LENGTH],
    uint64_t *out_n);

// SHA512_256_Init_from_state is a low-level function that initializes |sha|
// with a custom state. |h| is the hash state in big endian. |n| is the number
// of bits processed at this point. It must be a multiple of |SHA512_CBLOCK*8|.
// It returns one on success and zero on programmer error.
// This function is for internal use only and should never be directly called.
OPENSSL_EXPORT int SHA512_256_Init_from_state(
    SHA512_CTX *sha, const uint8_t h[SHA512_256_CHAINING_LENGTH], uint64_t n);

// SHA512_256_get_state is a low-level function that exports the hash state in
// big endian into |out_n| and the number of bits processed at this point in
// |out_n|. SHA512_256_Final must not have been called before (otherwise results
// are not guaranteed). Furthermore, the number of bytes processed by
// SHA512_256_Update must be a multiple of the block length |SHA512_CBLOCK|
// (otherwise it fails). It returns one on success and zero on programmer
// error.
// This function is for internal use only and should never be directly called.
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

// SHAKE_Init initializes |ctx| with specified |block_size|, returns 1 on
// success and 0 on failure. Calls SHA3_Init under the hood.
OPENSSL_EXPORT int SHAKE_Init(KECCAK1600_CTX *ctx, size_t block_size);

// SHAKE_Final writes |len| bytes of finalized digest to |md|, returns 1 on
// success and 0 on failure. Calls SHA3_Final under the hood.
OPENSSL_EXPORT int SHAKE_Final(uint8_t *md, KECCAK1600_CTX *ctx, size_t len);

// SHA3_Reset zeros the bitstate and the amount of processed input.
OPENSSL_EXPORT void SHA3_Reset(KECCAK1600_CTX *ctx);

// SHA3_Init initialises |ctx| fields and returns 1 on success and 0 on failure.
OPENSSL_EXPORT int SHA3_Init(KECCAK1600_CTX *ctx, uint8_t pad,
                             size_t bitlen);

// SHA3_Update processes all data blocks that don't need pad through 
// |SHA3_Absorb| and returns 1 and 0 on failure.
OPENSSL_EXPORT int SHA3_Update(KECCAK1600_CTX *ctx, const void *data,
                               size_t len);

// SHA3_Final pads the last data block and processes it through |SHA3_Absorb|. 
// It processes the data through |SHA3_Squeeze| and returns 1 and 0 on failure.
OPENSSL_EXPORT int SHA3_Final(uint8_t *md, KECCAK1600_CTX *ctx);

// SHA3_Absorb processes the largest multiple of |r| out of |len| bytes and 
// returns the remaining number of bytes. 
OPENSSL_EXPORT size_t SHA3_Absorb(uint64_t A[SHA3_ROWS][SHA3_ROWS], 
                                  const uint8_t *data, size_t len, size_t r);

// SHA3_Squeeze generate |out| hash value of |len| bytes.
OPENSSL_EXPORT void SHA3_Squeeze(uint64_t A[SHA3_ROWS][SHA3_ROWS], 
                                 uint8_t *out, size_t len, size_t r);

#if defined(__cplusplus)
}  // extern "C"
#endif

#endif  // OPENSSL_HEADER_SHA_INTERNAL_H
