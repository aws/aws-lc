/* Copyright (C) 1995-1998 Eric Young (eay@cryptsoft.com)
 * All rights reserved.
 *
 * This package is an SSL implementation written
 * by Eric Young (eay@cryptsoft.com).
 * The implementation was written so as to conform with Netscapes SSL.
 *
 * This library is free for commercial and non-commercial use as long as
 * the following conditions are aheared to.  The following conditions
 * apply to all code found in this distribution, be it the RC4, RSA,
 * lhash, DES, etc., code; not just the SSL code.  The SSL documentation
 * included with this distribution is covered by the same copyright terms
 * except that the holder is Tim Hudson (tjh@cryptsoft.com).
 *
 * Copyright remains Eric Young's, and as such any Copyright notices in
 * the code are not to be removed.
 * If this package is used in a product, Eric Young should be given attribution
 * as the author of the parts of the library used.
 * This can be in the form of a textual message at program startup or
 * in documentation (online or textual) provided with the package.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. All advertising materials mentioning features or use of this software
 *    must display the following acknowledgement:
 *    "This product includes cryptographic software written by
 *     Eric Young (eay@cryptsoft.com)"
 *    The word 'cryptographic' can be left out if the rouines from the library
 *    being used are not cryptographic related :-).
 * 4. If you include any Windows specific code (or a derivative thereof) from
 *    the apps directory (application code) you must include an acknowledgement:
 *    "This product includes software written by Tim Hudson (tjh@cryptsoft.com)"
 *
 * THIS SOFTWARE IS PROVIDED BY ERIC YOUNG ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 * The licence and distribution terms for any publically available version or
 * derivative of this code cannot be changed.  i.e. this code cannot simply be
 * copied and put under another distribution licence
 * [including the GNU Public Licence.] */

#ifndef OPENSSL_HEADER_BASE64_H
#define OPENSSL_HEADER_BASE64_H

#include <openssl/base.h>

#if defined(__cplusplus)
extern "C" {
#endif

/**
 * @file
 * @brief base64 encoding and decoding functions.
 *
 * @details
 * For historical reasons, these functions have the `EVP_` prefix but just do
 * base64 encoding and decoding. Note that BoringSSL is a cryptography library,
 * so these functions are implemented with side channel protections, at a
 * performance cost. For other base64 uses, use a general-purpose base64
 * implementation.
 */


/**
 * @name Encoding Functions
 *
 * @{
 */

/**
 * @brief Base64 encodes bytes from `src` into `dst`.
 *
 * @details
 * Base64 encodes `src_len` bytes from `src` and writes the
 * result to `dst` with a trailing `NULL`.
 *
 * @param [out] dst    Base64 encoded value
 * @param [in] src     Bytes to encode
 * @param [in] src_len Number of bytes to encode
 *
 * @return The number of bytes written, not including the trailing `NULL`
 */
OPENSSL_EXPORT size_t EVP_EncodeBlock(uint8_t *dst, const uint8_t *src,
                                      size_t src_len);

/**
 * @brief Calculates the number of bytes needed to encode an input using Base64.
 *
 * @details
 * Sets `*out_len` to the number of bytes that will be needed to call
 * #EVP_EncodeBlock on an input of length `len`. `*out_len` includes the final
 * `NULL` that #EVP_EncodeBlock writes.
 *
 * @param [out] out_len Number of bytes needed to Base64 encode a source
 * @param [in] len      Source length
 *
 * @retval 1 Success
 * @retval 0 Error
 */
OPENSSL_EXPORT int EVP_EncodedLength(size_t *out_len, size_t len);

/** @} Encoding Functions */


/**
 * @name Decoding Functions
 *
 * @{
 */

/**
 * @brief Sets the maximum number of bytes need to store a decoded Base64 input.
 *
 * @param [out] out_len Maximum number of bytes to store decoded input
 * @param [in] len      Base64 formatted input length
 *
 * @retval 1 Success
 * @retval 0 `len` is not a valid length for a base64-encoded string
 */
OPENSSL_EXPORT int EVP_DecodedLength(size_t *out_len, size_t len);

/**
 * @brief Decodes specified number of Base64 formatted bytes to output buffer.
 *
 * @details
 * Decodes `in_len` bytes from base64 and writes `*out_len` bytes to `out`. If
 * `*out_len` doesn't have enough bytes for the maximum output size, the
 * operation fails.
 *
 * @param [out] out     Decoded output
 * @param [out] out_len Number of bytes written to `out`
 * @param [in] max_out  Length of `out`
 * @param [in] in       Base64 input buffer
 * @param [in] in_len   Number of bytes to decode from `in`
 *
 * @retval 1 Success
 * @retval 0 Error
 */
OPENSSL_EXPORT int EVP_DecodeBase64(uint8_t *out, size_t *out_len,
                                    size_t max_out, const uint8_t *in,
                                    size_t in_len);

/** @} Decoding Functions */

/**
 * @name Deprecated Functions
 *
 * OpenSSL provides a streaming base64 implementation, however its behavior is
 * very specific to PEM. It is also very lenient of invalid input. Use of any of
 * these functions is thus deprecated.
 *
 * @{
 */

/**
 * @brief Returns a newly-allocated EVP_ENCODE_CTX.
 *
 * @details
 * The caller must release the result with #EVP_ENCODE_CTX_free when
 * done.
 *
 * @returns Pointer to newly allocated EVP_ENCODE_CTX or `NULL` on error
 *
 * @deprecated OpenSSL provides a streaming base64 implementation, however its behavior is very specific to PEM. It is also very lenient of invalid input. Use of any of these functions is thus deprecated.
 */
OPENSSL_EXPORT EVP_ENCODE_CTX *EVP_ENCODE_CTX_new(void);

/**
 * @brief Releases memory associated with `ctx`.
 *
 * @param [in] ctx Pointer to deallocate
 *
 * @deprecated OpenSSL provides a streaming base64 implementation, however its behavior is very specific to PEM. It is also very lenient of invalid input. Use of any of these functions is thus deprecated.
 */
OPENSSL_EXPORT void EVP_ENCODE_CTX_free(EVP_ENCODE_CTX *ctx);

/**
 * @brief Initialises `*ctx`.
 *
 * @details
 * This is typically stack allocated, for an encoding operation.
 *
 * @param [in,out] ctx Context to initialize
 *
 * @warning The encoding operation breaks its output with newlines every 64 characters of output (48 characters of input). Use #EVP_EncodeBlock to encode raw base64.
 *
 * @deprecated OpenSSL provides a streaming base64 implementation, however its behavior is very specific to PEM. It is also very lenient of invalid input. Use of any of these functions is thus deprecated.
 */
OPENSSL_EXPORT void EVP_EncodeInit(EVP_ENCODE_CTX *ctx);

/**
 * @brief Encodes bytes from `in` to Base64 and writes the value to `out`.
 *
 * @details
 * Some state may be contained in `ctx` so #EVP_EncodeFinal must be used to
 * flush it before using the encoded data.
 *
 * @param [in,out] ctx     Encoding context
 * @param [out]    out     Base64 encoded value
 * @param [out]    out_len Number of bytes written
 * @param [in]     in      Input buffer
 * @param [in]     in_len  Number of bytes to encode
 *
 * @retval 1 Success
 * @retval 0 Failure or `in_len` was 0
 *
 * @deprecated OpenSSL provides a streaming base64 implementation, however its behavior is very specific to PEM. It is also very lenient of invalid input. Use of any of these functions is thus deprecated.
 */
OPENSSL_EXPORT int EVP_EncodeUpdate(EVP_ENCODE_CTX *ctx, uint8_t *out,
                                    int *out_len, const uint8_t *in,
                                    size_t in_len);

/**
 * @brief Flushes any remaining output bytes from `ctx` to `out`.
 *
 * @param [in,out] ctx     Encoding context
 * @param [out]    out     Output buffer
 * @param [out]    out_len Number of bytes written to buffer
 *
 * @deprecated OpenSSL provides a streaming base64 implementation, however its behavior is very specific to PEM. It is also very lenient of invalid input. Use of any of these functions is thus deprecated.
 */
OPENSSL_EXPORT void EVP_EncodeFinal(EVP_ENCODE_CTX *ctx, uint8_t *out,
                                    int *out_len);

/**
 * @brief Initialises `*ctx` for a decoding operation.
 *
 * @details
 * This is typically stack allocated.
 *
 * @param [in,out] ctx Context to initialize
 *
 * @todo davidben: This isn't a straight-up base64 decode either. Document and/or fix exactly what's going on here; maximum line length and such.
 *
 * @deprecated OpenSSL provides a streaming base64 implementation, however its behavior is very specific to PEM. It is also very lenient of invalid input. Use of any of these functions is thus deprecated.
 */
OPENSSL_EXPORT void EVP_DecodeInit(EVP_ENCODE_CTX *ctx);

/**
 * @brief Decodes bytes from `in` and writes the decoded data to `out`.
 *
 * @details
 * Some state may be contained in `ctx` so #EVP_DecodeFinal must be used to
 * flush it before using the decoded data.
 *
 * @param [in,out] ctx     Decoding context
 * @param [out]    out     Decoded bytes
 * @param [out]    out_len Number of bytes written
 * @param [in]     in      Input buffer
 * @param [in]     in_len  Number of bytes to decode
 *
 * @retval -1 Error
 * @retval 0 The line was short (i.e., it was the last line)
 * @retval 1 A full line of input was processed
 *
 * @deprecated OpenSSL provides a streaming base64 implementation, however its behavior is very specific to PEM. It is also very lenient of invalid input. Use of any of these functions is thus deprecated.
 */
OPENSSL_EXPORT int EVP_DecodeUpdate(EVP_ENCODE_CTX *ctx, uint8_t *out,
                                    int *out_len, const uint8_t *in,
                                    size_t in_len);

/**
 * @brief Flushes any remaining output bytes from `ctx` to `out`.
 *
 * @param [in,out] ctx Decoding context
 * @param [out]    out Output buffer
 * @param [out]    out_len Number of bytes written to buffer
 *
 * @retval 1 Success
 * @retval -1 Error
 *
 * @deprecated OpenSSL provides a streaming base64 implementation, however its behavior is very specific to PEM. It is also very lenient of invalid input. Use of any of these functions is thus deprecated.
 */
OPENSSL_EXPORT int EVP_DecodeFinal(EVP_ENCODE_CTX *ctx, uint8_t *out,
                                   int *out_len);

/**
 * @brief Decodes Base64 bytes from `src` and writes value to `dst`.
 *
 * @param [out] dst Decoded bytes
 * @param [in] src  Base64 encoded bytes
 * @param [in] src_len Number of bytes to decode
 *
 * @returns Number of bytes written or -1 on error
 *
 * @warning `EVP_DecodeBlock`'s return value does not take padding into account. It also strips leading whitespace and trailing whitespace and minuses.
 *
 * @deprecated OpenSSL provides a streaming base64 implementation, however its behavior is very specific to PEM. It is also very lenient of invalid input. Use of any of these functions is thus deprecated.
 */
OPENSSL_EXPORT int EVP_DecodeBlock(uint8_t *dst, const uint8_t *src,
                                   size_t src_len);

/** @} Deprecated Functions */

/**
 * @struct evp_encode_ctx_st
 * Encoding Context
 */
struct evp_encode_ctx_st {
  /**
   * @brief Number of valid bytes
   *
   * @details
   * When encoding, `data` will be filled and encoded as a lump. When decoding,
   * only the first four bytes of `data` will be used.
   */
  unsigned data_used;

  /**
   * @brief Encoded or decoded data.
   */
  uint8_t data[48];

  /**
   * @brief Indicates that the end of the base64 data has been seen.
   *
   * @details
   * Only used when decoding. Only whitespace can follow.
   */
  char eof_seen;

  /**
   * @brief indicates that invalid base64 data was found.
   *
   * @details
   * This will gitcause all future calls to fail.
   */
  char error_encountered;
};


#if defined(__cplusplus)
}  // extern C
#endif

#endif  // OPENSSL_HEADER_BASE64_H
