#include <openssl/base.h>
#include <openssl/evp.h>
#include <openssl/mem.h>

int EVP_PKEY_encapsulate(EVP_PKEY_CTX *ctx,
                         uint8_t *ciphertext, size_t *ciphertext_len,
                         uint8_t *shared_secret, size_t *shared_secret_len) {
  if (ctx != NULL &&
      ctx->pmeth != NULL &&
      ctx->pmeth->encapsulate != NULL) {
    return ctx->pmeth->encapsulate(ctx, ciphertext, ciphertext_len,
                                   shared_secret, shared_secret_len);
  }
  return 0;
}

int EVP_PKEY_decapsulate(EVP_PKEY_CTX *ctx,
                         uint8_t *shared_secret, size_t *shared_secret_len,
                         uint8_t *ciphertext, size_t ciphertext_len) {
  if (ctx != NULL &&
      ctx->pmeth != NULL &&
      ctx->pmeth->decapsulate != NULL) {
    return ctx->pmeth->decapsulate(ctx, shared_secret, shared_secret_len,
                                   ciphertext, ciphertext_len);
  }
  return 0;
}
