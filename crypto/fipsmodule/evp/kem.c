#include <openssl/base.h>
#include <openssl/evp.h>
#include <openssl/mem.h>

#define SUCCESS (1)
#define FAILURE (0)

static int kem_fetch(unsigned int algorithm_type, EVP_KEM *kem) {
  int ret = FAILURE;
  switch (algorithm_type) {
    case NID_KYBER512:
      *kem = EVP_KEM_kyber512;
      ret = SUCCESS;
      break;
    default:
      ret = FAILURE;
  }
  return ret;
}

int EVP_PKEY_encapsulate_init(EVP_PKEY_CTX *ctx, const OSSL_PARAM params[]) {
  EVP_KEM *kem = OPENSSL_malloc(sizeof(EVP_KEM));
  if (kem == NULL) {
    OPENSSL_PUT_ERROR(EVP, ERR_R_MALLOC_FAILURE);
    return FAILURE;
  }

  if (ctx != NULL &&
      ctx->pkey != NULL &&
      kem_fetch(ctx->pkey->type, kem) &&
      kem->encapsulate_init(ctx, ctx->pkey, params)) {
    ctx->op.encap.kem = kem;
    return SUCCESS;
  } else {
    OPENSSL_free(kem);
    return FAILURE;
  }
}

int EVP_PKEY_encapsulate(EVP_PKEY_CTX *ctx,
                         unsigned char *out, size_t *out_len,
                         unsigned char *secret, size_t *secret_len) {
  if (ctx != NULL &&
      ctx->op.encap.kem != NULL &&
      ctx->op.encap.kem->encapsulate != NULL) {
    return ctx->op.encap.kem->encapsulate(ctx, out, out_len, secret, secret_len);
  }
  return FAILURE;
}

int EVP_PKEY_decapsulate_init(EVP_PKEY_CTX *ctx, const OSSL_PARAM params[]) {
  EVP_KEM *kem = OPENSSL_malloc(sizeof(EVP_KEM));
  if (kem == NULL) {
    OPENSSL_PUT_ERROR(EVP, ERR_R_MALLOC_FAILURE);
    return FAILURE;
  }

  if (ctx != NULL &&
      ctx->pkey != NULL &&
      kem_fetch(ctx->pkey->type, kem) &&
      kem->decapsulate_init(ctx, ctx->pkey, params)) {
    ctx->op.encap.kem = kem;
    return SUCCESS;
  } else {
    OPENSSL_free(kem);
    return FAILURE;
  }
}

int EVP_PKEY_decapsulate(EVP_PKEY_CTX *ctx,
                         unsigned char *secret, size_t *secret_len,
                         const unsigned char *in, size_t in_len) {
  if (ctx != NULL &&
      ctx->op.encap.kem != NULL &&
      ctx->op.encap.kem->decapsulate != NULL) {
    return ctx->op.encap.kem->decapsulate(ctx, secret, secret_len, in, in_len);
  }
  return FAILURE;
}
