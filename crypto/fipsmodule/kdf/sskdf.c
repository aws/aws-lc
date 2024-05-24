// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <assert.h>
#include <openssl/base.h>
#include <openssl/digest.h>
#include <openssl/hmac.h>
#include <openssl/kdf.h>
#include "../delocate.h"
#include "internal.h"

static int sskdf_variant_digest_ctx_init(sskdf_variant_ctx *ctx,
                                         const EVP_MD *digest) {
  sskdf_variant_digest_ctx *variant_ctx = NULL;
  EVP_MD_CTX *md_ctx = NULL;

  int ret = 0;

  if (!ctx || ctx->data || !digest) {
    goto err;
  }

  variant_ctx = OPENSSL_malloc(sizeof(sskdf_variant_digest_ctx));
  if (!variant_ctx) {
    goto err;
  }

  md_ctx = EVP_MD_CTX_new();
  if (!md_ctx) {
    goto err;
  }

  ret = 1;
  variant_ctx->digest = digest;
  variant_ctx->md_ctx = md_ctx;
  ctx->data = variant_ctx;

  return ret;

err:
  EVP_MD_CTX_free(md_ctx);
  OPENSSL_free(variant_ctx);

  return ret;
}



static void sskdf_variant_digest_ctx_cleanup(sskdf_variant_ctx *ctx) {
  if (!ctx || !ctx->data) {
    return;
  }
  sskdf_variant_digest_ctx *variant_ctx = (sskdf_variant_digest_ctx *)ctx->data;
  EVP_MD_CTX_free(variant_ctx->md_ctx);
  OPENSSL_free(variant_ctx);
  ctx->data = NULL;
}

static int sskdf_variant_hmac_ctx_init(sskdf_variant_ctx *ctx,
                                       const EVP_MD *digest,
                                       const uint8_t *salt, size_t salt_len) {
  sskdf_variant_hmac_ctx *variant_ctx = NULL;
  HMAC_CTX *hmac_ctx = NULL;

  int ret = 0;

  if (!ctx || ctx->data || !digest) {
    goto err;
  }

  variant_ctx = OPENSSL_malloc(sizeof(sskdf_variant_hmac_ctx));
  if (!variant_ctx) {
    goto err;
  }

  hmac_ctx = HMAC_CTX_new();
  if (!hmac_ctx) {
    goto err;
  }

  if (!HMAC_Init_ex(hmac_ctx, salt, salt_len, digest, NULL)) {
    goto err;
  }

  ret = 1;
  variant_ctx->hmac_ctx = hmac_ctx;
  ctx->data = variant_ctx;

  return ret;

err:
  HMAC_CTX_free(hmac_ctx);
  OPENSSL_free(variant_ctx);

  return ret;
}



static void sskdf_variant_hmac_ctx_cleanup(sskdf_variant_ctx *ctx) {
  if (!ctx || !ctx->data) {
    return;
  }
  sskdf_variant_hmac_ctx *variant_ctx = (sskdf_variant_hmac_ctx *)ctx->data;
  HMAC_CTX_free(variant_ctx->hmac_ctx);
  OPENSSL_free(variant_ctx);
  ctx->data = NULL;
}

static size_t sskdf_variant_digest_output_size(sskdf_variant_ctx *ctx) {
  if (!ctx || !ctx->data) {
    return 0;
  }
  sskdf_variant_digest_ctx *variant_ctx = (sskdf_variant_digest_ctx *)ctx->data;
  return EVP_MD_size(variant_ctx->digest);
}

static int sskdf_variant_digest_compute(
    sskdf_variant_ctx *ctx, uint8_t *out, size_t out_len,
    const uint8_t counter[SSKDF_COUNTER_SIZE], const uint8_t *secret,
    size_t secret_len, const uint8_t *info, size_t info_len) {
  if (!ctx || !ctx->data || !out || !counter || !secret) {
    return 0;
  }

  sskdf_variant_digest_ctx *variant_ctx = (sskdf_variant_digest_ctx *)ctx->data;

  if (!variant_ctx->md_ctx || !variant_ctx->digest) {
    return 0;
  }

  uint32_t written;

  if (!EVP_MD_CTX_reset(variant_ctx->md_ctx) ||
      !EVP_DigestInit_ex(variant_ctx->md_ctx, variant_ctx->digest, NULL) ||
      !EVP_DigestUpdate(variant_ctx->md_ctx, &counter[0], SSKDF_COUNTER_SIZE) ||
      !EVP_DigestUpdate(variant_ctx->md_ctx, secret, secret_len) ||
      !EVP_DigestUpdate(variant_ctx->md_ctx, info, info_len) ||
      !EVP_DigestFinal(variant_ctx->md_ctx, out, &written) ||
      written != out_len) {
    return 0;
  }

  return 1;
}

static size_t sskdf_variant_hmac_output_size(sskdf_variant_ctx *ctx) {
  if (!ctx || !ctx->data) {
    return 0;
  }
  sskdf_variant_hmac_ctx *variant_ctx = (sskdf_variant_hmac_ctx *)ctx->data;
  if (!variant_ctx) {
    return 0;
  }
  return HMAC_size(variant_ctx->hmac_ctx);
}

static int sskdf_variant_hmac_compute(sskdf_variant_ctx *ctx, uint8_t *out,
                                      size_t out_len,
                                      const uint8_t counter[SSKDF_COUNTER_SIZE],
                                      const uint8_t *secret, size_t secret_len,
                                      const uint8_t *info, size_t info_len) {
  if (!ctx || !ctx->data || !out || !counter || !secret) {
    return 0;
  }

  sskdf_variant_hmac_ctx *variant_ctx = (sskdf_variant_hmac_ctx *)ctx->data;

  if (!variant_ctx->hmac_ctx) {
    return 0;
  }

  uint32_t written;

  if (!HMAC_Init_ex(variant_ctx->hmac_ctx, NULL, 0, NULL, NULL) ||
      !HMAC_Update(variant_ctx->hmac_ctx, &counter[0], SSKDF_COUNTER_SIZE) ||
      !HMAC_Update(variant_ctx->hmac_ctx, secret, secret_len) ||
      !HMAC_Update(variant_ctx->hmac_ctx, info, info_len) ||
      !HMAC_Final(variant_ctx->hmac_ctx, out, &written) || out_len != written) {
    return 0;
  }

  return 1;
}


DEFINE_METHOD_FUNCTION(sskdf_variant, sskdf_variant_digest) {
  memset(out, 0, sizeof(sskdf_variant));
  out->output_size = sskdf_variant_digest_output_size;
  out->compute = sskdf_variant_digest_compute;
}


DEFINE_METHOD_FUNCTION(sskdf_variant, sskdf_variant_hmac) {
  memset(out, 0, sizeof(sskdf_variant));
  out->output_size = sskdf_variant_hmac_output_size;
  out->compute = sskdf_variant_hmac_compute;
}

static int SSKDF(const sskdf_variant *variant, sskdf_variant_ctx *ctx,
                 uint8_t *out_key, size_t out_len, const uint8_t *secret,
                 size_t secret_len, const uint8_t *info, size_t info_len) {
  int ret = 0;

  if (!ctx || !variant) {
    return 0;
  }

  if (!out_key || out_len == 0 || !secret || secret_len == 0) {
    goto err;
  }

  // output_size is the length in bytes of output of the SSKDF variant auxilary
  // function (EVP_DigestFinal or HMAC_Final)
  size_t output_size = variant->output_size(ctx);
  if (output_size == 0) {
    goto err;
  }
  assert(output_size <= EVP_MAX_MD_SIZE);

  // NIST.SP.800-56Cr2:
  // 1. If L > 0, then set reps = ceil(L / H_outputBits); otherwise, output an
  // error indicator and exit this process without performing the remaining
  // actions
  uint64_t n = (out_len + output_size - 1) / output_size;

  // NIST.SP.800-56Cr2:
  // 2. If reps > (2^32 - 1), then output an error indicator and exit this
  // process without performing the remaining actions
  if (n > UINT32_MAX) {
    goto err;
  }

  // Validate that the sum of the fixed info lengths won't overflow a size_t
  // which will very based on 32-bit or 64-bit platforms. We will further clamp
  // this value below.
  if (info_len > SIZE_MAX - 4 - secret_len) {
    goto err;
  }

  // NIST.SP.800-56Cr2: "4. If counter || Z || FixedInfo is more than
  // max_H_inputBits bits long, then output an error indicator and exit this
  // process without performing any of the remaining actions"
  //
  // UINT32_MAX is a sufficient max value to satisfy this requirement. See
  // Section 4.2 Table 1 and 2
  // https://nvlpubs.nist.gov/nistpubs/SpecialPublications/NIST.SP.800-56Cr2.pdf
  if (4 + secret_len + info_len > UINT32_MAX) {
    goto err;
  }

  // TODO(awslc): Abstract buffer size, if we ever need to support KMAC this
  // could be variable. Currently sufficient for HMAC and digest variants
  uint8_t previous[EVP_MAX_MD_SIZE];

  size_t done = 0;

  // NIST.SP.800-56Cr2: "Initialize a big-endian 4-byte unsigned integer counter
  // as 0x00000000, corresponding to a 32-bit binary representation of the
  // number zero."
  //
  // Here `i` will act as our counter 32-bit counter.
  for (uint32_t i = 0; i < n; i++) {
    uint8_t counter[SSKDF_COUNTER_SIZE];
    size_t todo;

    // NIST.SP.800-56Cr2: "6.1 Increment counter by 1."
    CRYPTO_store_u32_be(&counter[0], i + 1);

    // NIST.SP.800-56Cr2: "6.2 Compute K(i) = H(counter || Z || FixedInfo)."
    if (!variant->compute(ctx, &previous[0], output_size, counter, secret,
                          secret_len, info, info_len)) {
      goto err;
    }

    // NIST.SP.800-56Cr2: "6.3 Set Result(i) = Result(i – 1) || K(i). ...
    // 7. Set DerivedKeyingMaterial equal to the leftmost L bits of
    // Result(reps).
    // 8. Output DerivedKeyingMaterial."
    todo = output_size;
    if (todo > out_len - done) {
      todo = out_len - done;
    }
    OPENSSL_memcpy(out_key + done, previous, todo);
    done += todo;
  }

  ret = 1;

err:
  return ret;
}

int SSKDF_digest(uint8_t *out_key, size_t out_len, const EVP_MD *digest,
                 const uint8_t *secret, size_t secret_len, const uint8_t *info,
                 size_t info_len) {
  sskdf_variant_ctx ctx = {0};
  int ret = 0;

  if (!sskdf_variant_digest_ctx_init(&ctx, digest)) {
    return 0;
  }

  if (!SSKDF(sskdf_variant_digest(), &ctx, out_key, out_len, secret, secret_len,
             info, info_len)) {
    goto end;
  }

  ret = 1;

end:
  sskdf_variant_digest_ctx_cleanup(&ctx);
  return ret;
}

int SSKDF_hmac(uint8_t *out_key, size_t out_len, const EVP_MD *digest,
               const uint8_t *secret, size_t secret_len, const uint8_t *info,
               size_t info_len, const uint8_t *salt, size_t salt_len) {
  sskdf_variant_ctx ctx = {0};
  int ret = 0;

  if (!sskdf_variant_hmac_ctx_init(&ctx, digest, salt, salt_len)) {
    return 0;
  }

  if (!SSKDF(sskdf_variant_hmac(), &ctx, out_key, out_len, secret, secret_len,
             info, info_len)) {
    goto end;
  }

  ret = 1;

end:
  sskdf_variant_hmac_ctx_cleanup(&ctx);
  return ret;
}
