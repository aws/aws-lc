/*
 * Copyright 2001-2017 The OpenSSL Project Authors. All Rights Reserved.
 *
 * Licensed under the OpenSSL license (the "License").  You may not use
 * this file except in compliance with the License.  You can obtain a copy
 * in the file LICENSE in the source distribution or at
 * https://www.openssl.org/source/license.html
 */

// SPDX-License-Identifier: Apache-2.0 OR ISC
// Modifications Copyright Amazon.com, Inc. or its affiliates.

#include "internal.h"
#include "openssl/mem.h"

#define OCSP_MAX_RESP_LENGTH    (100 * 1024)
#define OCSP_MAX_LINE_LEN       4096;

// OCSP states

// If set no reading should be performed
#define OHS_NOREAD              0x1000
// Error condition
#define OHS_ERROR               (0 | OHS_NOREAD)

OCSP_REQ_CTX *OCSP_REQ_CTX_new(BIO *io, int maxline)
{
    OCSP_REQ_CTX *rctx = OPENSSL_malloc(sizeof(*rctx));

    if (rctx == NULL) {
      return NULL;
    }
    rctx->state = OHS_ERROR;
    rctx->max_resp_len = OCSP_MAX_RESP_LENGTH;
    rctx->mem = BIO_new(BIO_s_mem());
    rctx->io = io;
    if (maxline > 0) {
      rctx->iobuflen = maxline;
    }
    else {
      rctx->iobuflen = OCSP_MAX_LINE_LEN;
    }
    rctx->iobuf = OPENSSL_malloc(rctx->iobuflen);
    if (rctx->iobuf == NULL || rctx->mem == NULL) {
        OCSP_REQ_CTX_free(rctx);
        return NULL;
    }
    return rctx;
}

void OCSP_REQ_CTX_free(OCSP_REQ_CTX *rctx)
{
    if (rctx == NULL) {
      return;
    }
    BIO_free(rctx->mem);
    OPENSSL_free(rctx->iobuf);
    OPENSSL_free(rctx);
}
