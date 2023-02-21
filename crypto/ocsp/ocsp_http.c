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

// OCSP_REQ_CTX states

// If set no reading should be performed
#define OHS_NOREAD              0x1000
// Error condition
#define OHS_ERROR               (0 | OHS_NOREAD)
// First call: ready to start I/O
#define OHS_ASN1_WRITE_INIT     (5 | OHS_NOREAD)
// Headers set, no final \r\n included
#define OHS_HTTP_HEADER         (9 | OHS_NOREAD)

OCSP_REQ_CTX *OCSP_REQ_CTX_new(BIO *io, int maxline)
{
    OCSP_REQ_CTX *rctx = OPENSSL_malloc(sizeof(OCSP_REQ_CTX));

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

OCSP_REQ_CTX *OCSP_sendreq_new(BIO *io, const char *path, OCSP_REQUEST *req,
                               int maxline)
{

    OCSP_REQ_CTX *rctx = NULL;
    rctx = OCSP_REQ_CTX_new(io, maxline);
    if (rctx == NULL) {
      return NULL;
    }

    if (!OCSP_REQ_CTX_http(rctx, "POST", path)) {
      goto err;
    }
    if (req != NULL && !OCSP_REQ_CTX_set1_req(rctx, req)) {
      goto err;
    }
    return rctx;

 err:
    OCSP_REQ_CTX_free(rctx);
    return NULL;
}

int OCSP_REQ_CTX_http(OCSP_REQ_CTX *rctx, const char *op, const char *path)
{
    static const char http_hdr[] = "%s %s HTTP/1.0\r\n";

    // Set to a default path, if path is NULL.
    if (path == NULL) {
      path = "/";
    }

    if (BIO_printf(rctx->mem, http_hdr, op, path) <= 0) {
      return 0;
    }
    rctx->state = OHS_HTTP_HEADER;
    return 1;
}

int OCSP_REQ_CTX_set1_req(OCSP_REQ_CTX *rctx, OCSP_REQUEST *req)
{
    return OCSP_REQ_CTX_i2d(rctx, ASN1_ITEM_rptr(OCSP_REQUEST),
                            (ASN1_VALUE *)req);
}

int OCSP_REQ_CTX_add1_header(OCSP_REQ_CTX *rctx,
                             const char *name, const char *value)
{
    if (name == NULL) {
      return 0;
    }
    if (BIO_puts(rctx->mem, name) <= 0) {
      return 0;
    }
    if (value != NULL) {
        if (BIO_write(rctx->mem, ": ", 2) != 2) {
          return 0;
        }
        if (BIO_puts(rctx->mem, value) <= 0) {
          return 0;
        }
    }
    if (BIO_write(rctx->mem, "\r\n", 2) != 2) {
      return 0;
    }
    rctx->state = OHS_HTTP_HEADER;
    return 1;
}

int OCSP_REQ_CTX_i2d(OCSP_REQ_CTX *rctx, const ASN1_ITEM *it, ASN1_VALUE *val)
{
    static const char req_hdr[] =
        "Content-Type: application/ocsp-request\r\n"
        "Content-Length: %d\r\n\r\n";
    int reqlen = ASN1_item_i2d(val, NULL, it);
    if (BIO_printf(rctx->mem, req_hdr, reqlen) <= 0) {
      return 0;
    }
    if (ASN1_item_i2d_bio(it, rctx->mem, val) <= 0) {
      return 0;
    }
    rctx->state = OHS_ASN1_WRITE_INIT;
    return 1;
}

BIO *OCSP_REQ_CTX_get0_mem_bio(OCSP_REQ_CTX *rctx)
{
    return rctx->mem;
}
