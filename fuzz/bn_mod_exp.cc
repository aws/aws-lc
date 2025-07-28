/* Copyright (c) 2017, Google Inc.
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

#include <openssl/bn.h>
#include <openssl/bytestring.h>
#include <openssl/mem.h>

#define CHECK(expr)                 \
  do {                              \
    if (!(expr)) {                  \
      printf("%s failed\n", #expr); \
      abort();                      \
    }                               \
  } while (false)

// Basic implementation of mod_exp using square and multiple method.
int mod_exp(BIGNUM *r, const BIGNUM *a, const BIGNUM *p, const BIGNUM *m,
            BN_CTX *ctx) {
  if (BN_is_one(m)) {
    BN_zero(r);
    return 1;
  }

  bssl::UniquePtr<BIGNUM> exp(BN_dup(p));
  bssl::UniquePtr<BIGNUM> base(BN_new());
  if (!exp || !base) {
    return 0;
  }
  if (!BN_one(r) || !BN_nnmod(base.get(), a, m, ctx)) {
    return 0;
  }

  while (!BN_is_zero(exp.get())) {
    if (BN_is_odd(exp.get())) {
      if (!BN_mul(r, r, base.get(), ctx) || !BN_nnmod(r, r, m, ctx)) {
        return 0;
      }
    }
    if (!BN_rshift1(exp.get(), exp.get()) ||
        !BN_mul(base.get(), base.get(), base.get(), ctx) ||
        !BN_nnmod(base.get(), base.get(), m, ctx)) {
      return 0;
    }
  }

  return 1;
}

extern "C" int LLVMFuzzerTestOneInput(const uint8_t *buf, size_t len) {
  CBS cbs, child0, child1, child2, child3, child4, child5;
  uint8_t sign, sign1;
  CBS_init(&cbs, buf, len);
  if (!CBS_get_u16_length_prefixed(&cbs, &child0) ||
      !CBS_get_u8(&child0, &sign) ||
      CBS_len(&child0) == 0 ||
      !CBS_get_u16_length_prefixed(&cbs, &child1) ||
      CBS_len(&child1) == 0 ||
      !CBS_get_u16_length_prefixed(&cbs, &child2) ||
      CBS_len(&child2) == 0 ||
      !CBS_get_u16_length_prefixed(&cbs, &child3) ||
      !CBS_get_u8(&child3, &sign1) ||
      CBS_len(&child3) == 0 ||
      !CBS_get_u16_length_prefixed(&cbs, &child4) ||
      CBS_len(&child4) == 0 ||
      !CBS_get_u16_length_prefixed(&cbs, &child5) ||
      CBS_len(&child5) == 0) {
    return 0;
  }

  // Don't fuzz inputs larger than 512 bytes (4096 bits). This isn't ideal, but
  // the naive |mod_exp| above is somewhat slow, so this otherwise causes the
  // fuzzers to spend a lot of time exploring timeouts.
  if (CBS_len(&child0) > 512 ||
      CBS_len(&child1) > 512 ||
      CBS_len(&child2) > 512 ||
      CBS_len(&child3) > 512 ||
      CBS_len(&child4) > 512 ||
      CBS_len(&child5) > 512) {
    return 0;
  }

  bssl::UniquePtr<BIGNUM> base(
      BN_bin2bn(CBS_data(&child0), CBS_len(&child0), nullptr));
  BN_set_negative(base.get(), sign % 2);
  bssl::UniquePtr<BIGNUM> power(
      BN_bin2bn(CBS_data(&child1), CBS_len(&child1), nullptr));
  bssl::UniquePtr<BIGNUM> modulus(
      BN_bin2bn(CBS_data(&child2), CBS_len(&child2), nullptr));

  bssl::UniquePtr<BIGNUM> base1(
      BN_bin2bn(CBS_data(&child3), CBS_len(&child3), nullptr));
  BN_set_negative(base.get(), sign % 2);
  bssl::UniquePtr<BIGNUM> power1(
      BN_bin2bn(CBS_data(&child4), CBS_len(&child4), nullptr));
  bssl::UniquePtr<BIGNUM> modulus1(
      BN_bin2bn(CBS_data(&child5), CBS_len(&child5), nullptr));

  if (BN_is_zero(modulus.get()) || BN_is_zero(modulus1.get())) {
    return 0;
  }

  bssl::UniquePtr<BN_CTX> ctx(BN_CTX_new());
  bssl::UniquePtr<BIGNUM> result(BN_new());
  bssl::UniquePtr<BIGNUM> expected(BN_new());
  bssl::UniquePtr<BIGNUM> result1(BN_new());
  bssl::UniquePtr<BIGNUM> expected1(BN_new());
  CHECK(ctx);
  CHECK(result);
  CHECK(expected);
  CHECK(result1);
  CHECK(expected1);

  CHECK(mod_exp(expected.get(), base.get(), power.get(), modulus.get(),
                ctx.get()));
  CHECK(BN_mod_exp(result.get(), base.get(), power.get(), modulus.get(),
                   ctx.get()));
  CHECK(BN_cmp(result.get(), expected.get()) == 0);

  if (BN_is_odd(modulus.get())) {
    bssl::UniquePtr<BN_MONT_CTX> mont(
        BN_MONT_CTX_new_for_modulus(modulus.get(), ctx.get()));
    CHECK(mont);
    // |BN_mod_exp_mont| and |BN_mod_exp_mont_consttime| require reduced inputs.
    CHECK(BN_nnmod(base.get(), base.get(), modulus.get(), ctx.get()));
    CHECK(BN_mod_exp_mont(result.get(), base.get(), power.get(), modulus.get(),
                          ctx.get(), mont.get()));
    CHECK(BN_cmp(result.get(), expected.get()) == 0);
    CHECK(BN_mod_exp_mont_consttime(result.get(), base.get(), power.get(),
                                    modulus.get(), ctx.get(), mont.get()));
    CHECK(BN_cmp(result.get(), expected.get()) == 0);

    // If modulus1 is also odd, use the AVX-512 implementation.
    if (BN_is_odd(modulus1.get())) {
      bssl::UniquePtr<BN_MONT_CTX> mont1(
          BN_MONT_CTX_new_for_modulus(modulus1.get(), ctx.get()));
      CHECK(mont1);

      // Calculate the expected result for the second set of inputs.
      CHECK(mod_exp(expected1.get(), base1.get(), power1.get(), modulus1.get(),
                    ctx.get()));

      // Normalize them.
      CHECK(BN_nnmod(base1.get(), base1.get(), modulus1.get(), ctx.get()));

      // Run the x2 implementation and compare the results.
      CHECK(BN_mod_exp_mont_consttime_x2(result.get(), base.get(), power.get(),
                                         modulus.get(), mont.get(),
                                         result1.get(), base1.get(), power1.get(),
                                         modulus1.get(), mont1.get(),
					 ctx.get()));
      CHECK(BN_cmp(result.get(), expected.get()) == 0);
      CHECK(BN_cmp(result1.get(), expected1.get()) == 0);
    }
  }

  uint8_t *data = (uint8_t *)OPENSSL_malloc(BN_num_bytes(result.get()));
  BN_bn2bin(result.get(), data);
  OPENSSL_free(data);

  return 0;
}
