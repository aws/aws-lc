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

#include <ctype.h>
#include <string.h>
#include "openssl/mem.h"

#include "internal.h"
#include "../internal.h"

#define OCSP_MAX_RESP_LENGTH    (100 * 1024)
#define OCSP_MAX_LINE_LEN       4096;

// OCSP_REQ_CTX states

// If set no reading should be performed
#define OHS_NOREAD              0x1000
// Error condition
#define OHS_ERROR               (0 | OHS_NOREAD)
// First line being read
#define OHS_FIRSTLINE           1
// MIME headers being read
#define OHS_HEADERS             2
// OCSP initial header (tag + length) being read
#define OHS_ASN1_HEADER         3
// OCSP content octets being read
#define OHS_ASN1_CONTENT        4
// First call: ready to start I/O
#define OHS_ASN1_WRITE_INIT     (5 | OHS_NOREAD)
// Request being sent
#define OHS_ASN1_WRITE          (6 | OHS_NOREAD)
// Request being flushed
#define OHS_ASN1_FLUSH          (7 | OHS_NOREAD)
// Completed
#define OHS_DONE                (8 | OHS_NOREAD)
// Headers set, no final \r\n included
#define OHS_HTTP_HEADER         (9 | OHS_NOREAD)

// Parse the HTTP response. This will look like this: "HTTP/1.0 200 OK". We
// need to obtain the numeric code and (optional) informational message.
static int parse_http_line(char *line)
{
    int http_code;
    char *code, *reason, *end;
    // Skip to first white space (passed protocol info)
    for (code = line; *code != '\0' && !isspace(*code); code++) {
      continue;
    }
    if (*code == '\0') {
        OPENSSL_PUT_ERROR(OCSP,  OCSP_R_SERVER_RESPONSE_PARSE_ERROR);
        return 0;
    }

    // Skip past white space to start of response code.
    while (*code != '\0' && isspace(*code)) {
      code++;
    }
    if (*code == '\0') {
        OPENSSL_PUT_ERROR(OCSP,  OCSP_R_SERVER_RESPONSE_PARSE_ERROR);
        return 0;
    }

    // Find end of response code: first whitespace after start of code.
    for (reason = code; *reason != '\0' && !isspace(*reason); reason++) {
      continue;
    }
    if (*reason == '\0') {
        OPENSSL_PUT_ERROR(OCSP,  OCSP_R_SERVER_RESPONSE_PARSE_ERROR);
        return 0;
    }

    // Set end of response code and start of message.
    *reason++ = '\0';
    // Attempt to parse numeric code
    http_code = (int)strtoul(code, &end, 10);
    if (*end != '\0') {
      return 0;
    }

    // Skip over any leading white space in message.
    while (*reason != '\0' && isspace(*reason)) {
      reason++;
    }
    if (*reason != '\0') {
        // Finally, zap any trailing white space in message (include CRLF).
        // We know reason has a non-white space character so this is OK.
        for (end = reason + strlen(reason) - 1; isspace(*end); end--) {
          *end = '\0';
        }
    }
    if (http_code != 200) {
        OPENSSL_PUT_ERROR(OCSP,  OCSP_R_SERVER_RESPONSE_PARSE_ERROR);
        if (*reason == '\0') {
          ERR_add_error_data(2, "Code=", code);
        }
        else {
          ERR_add_error_data(4, "Code=", code, ",Reason=", reason);
        }
        return 0;
    }
    return 1;
}

int OCSP_REQ_CTX_nbio(OCSP_REQ_CTX *rctx)
{
    int i, n;
    const unsigned char *p;
 next_io:
    if (!(rctx->state & OHS_NOREAD)) {
        n = BIO_read(rctx->io, rctx->iobuf, rctx->iobuflen);
        if (n <= 0) {
            if (BIO_should_retry(rctx->io)) {
              return -1;
            }
            return 0;
        }

        // Write data to memory BIO.
        if (BIO_write(rctx->mem, rctx->iobuf, n) != n) {
          return 0;
        }
    }

    switch (rctx->state) {
    case OHS_HTTP_HEADER:
        // Last operation was adding headers: need a final "\r\n".
        if (BIO_write(rctx->mem, "\r\n", 2) != 2) {
            rctx->state = OHS_ERROR;
            return 0;
        }
        rctx->state = OHS_ASN1_WRITE_INIT;

        OPENSSL_FALLTHROUGH;
    case OHS_ASN1_WRITE_INIT:
        rctx->asn1_len = BIO_get_mem_data(rctx->mem, NULL);
        rctx->state = OHS_ASN1_WRITE;

        OPENSSL_FALLTHROUGH;
    case OHS_ASN1_WRITE:
        n = BIO_get_mem_data(rctx->mem, &p);

        i = BIO_write(rctx->io, p + (n - rctx->asn1_len), (int)rctx->asn1_len);
        if (i <= 0) {
            if (BIO_should_retry(rctx->io)) {
              return -1;
            }
            rctx->state = OHS_ERROR;
            return 0;
        }

        rctx->asn1_len -= i;

        if (rctx->asn1_len > 0) {
          goto next_io;
        }

        rctx->state = OHS_ASN1_FLUSH;
        (void)BIO_reset(rctx->mem);

        OPENSSL_FALLTHROUGH;
    case OHS_ASN1_FLUSH:

        i = BIO_flush(rctx->io);
        if (i > 0) {
            rctx->state = OHS_FIRSTLINE;
            goto next_io;
        }

        if (BIO_should_retry(rctx->io)) {
          return -1;
        }
        rctx->state = OHS_ERROR;
        return 0;

    case OHS_ERROR:
        return 0;

    case OHS_FIRSTLINE:
    case OHS_HEADERS:

    // Attempt to read a line in.
 next_line:
        // Due to &%^*$" memory BIO behaviour with BIO_gets we have to check
        // there's a complete line in there before calling BIO_gets or we'll
        // just get a partial read.
        n = BIO_get_mem_data(rctx->mem, &p);
        if ((n <= 0) || !memchr(p, '\n', n)) {
            if (n >= rctx->iobuflen) {
                rctx->state = OHS_ERROR;
                return 0;
            }
            goto next_io;
        }
        n = BIO_gets(rctx->mem, (char *)rctx->iobuf, rctx->iobuflen);

        if (n <= 0) {
            if (BIO_should_retry(rctx->mem)) {
              goto next_io;
            }
            rctx->state = OHS_ERROR;
            return 0;
        }

        // Don't allow excessive lines.
        if (n == rctx->iobuflen) {
            rctx->state = OHS_ERROR;
            return 0;
        }

        // First line.
        if (rctx->state == OHS_FIRSTLINE) {
            if (parse_http_line((char *)rctx->iobuf)) {
                rctx->state = OHS_HEADERS;
                goto next_line;
            } else {
                rctx->state = OHS_ERROR;
                return 0;
            }
        } else {
            // Look for blank line: end of headers.
            for (p = rctx->iobuf; *p; p++) {
                if ((*p != '\r') && (*p != '\n')) {
                  break;
                }
            }
            if (*p != '\0') {
              goto next_line;
            }

            rctx->state = OHS_ASN1_HEADER;
        }

        OPENSSL_FALLTHROUGH;
    case OHS_ASN1_HEADER:
        // Now reading ASN1 header: can read at least 2 bytes which is enough
        // for ASN1 SEQUENCE header and either length field or at least the
        // length of the length field.
        n = BIO_get_mem_data(rctx->mem, &p);
        if (n < 2) {
          goto next_io;
        }

        // Check it is an ASN1 SEQUENCE.
        if (*p++ != (V_ASN1_SEQUENCE | V_ASN1_CONSTRUCTED)) {
            rctx->state = OHS_ERROR;
            return 0;
        }

        // Check out length field.
        if ((*p & 0x80) != 0) {
            // If MSB set on initial length octet we can now always read 6
            // octets: make sure we have them.
            if (n < 6) {
              goto next_io;
            }
            n = *p & 0x7F;
            // Not NDEF or excessive length.
            if (!n || (n > 4)) {
                rctx->state = OHS_ERROR;
                return 0;
            }
            p++;
            rctx->asn1_len = 0;
            for (i = 0; i < n; i++) {
                rctx->asn1_len <<= 8;
                rctx->asn1_len |= *p++;
            }
            if (rctx->asn1_len > rctx->max_resp_len) {
                rctx->state = OHS_ERROR;
                return 0;
            }
            rctx->asn1_len += n + 2;
        } else {
          rctx->asn1_len = *p + 2;
        }
        rctx->state = OHS_ASN1_CONTENT;

        OPENSSL_FALLTHROUGH;
    case OHS_ASN1_CONTENT:
        n = BIO_get_mem_data(rctx->mem, NULL);
        if (n < (int)rctx->asn1_len) {
          goto next_io;
        }
        rctx->state = OHS_DONE;
        return 1;

    case OHS_DONE:
        return 1;
    }

    return 0;
}

int OCSP_sendreq_nbio(OCSP_RESPONSE **presp, OCSP_REQ_CTX *rctx)
{
    return OCSP_REQ_CTX_nbio_d2i(rctx, (ASN1_VALUE **)presp,
                                 ASN1_ITEM_rptr(OCSP_RESPONSE));
}

OCSP_RESPONSE *OCSP_sendreq_bio(BIO *b, const char *path, OCSP_REQUEST *req)
{
    OCSP_RESPONSE *resp = NULL;
    OCSP_REQ_CTX *ctx;
    int rv;

    ctx = OCSP_sendreq_new(b, path, req, -1);
    if (ctx == NULL) {
      return NULL;
    }

    // This waits indefinitely on a response.
    do {
        rv = OCSP_sendreq_nbio(&resp, ctx);
    } while ((rv == -1) && BIO_should_retry(b));

    OCSP_REQ_CTX_free(ctx);
    if(rv) {
      return resp;
    }
    return NULL;
}

int OCSP_REQ_CTX_nbio_d2i(OCSP_REQ_CTX *rctx,
                          ASN1_VALUE **pval, const ASN1_ITEM *it)
{
    int rv;
    size_t len;
    const unsigned char *p;

    rv = OCSP_REQ_CTX_nbio(rctx);
    if (rv != 1) {
      return rv;
    }

    if(!BIO_mem_contents(rctx->mem, &p, &len)){
      goto err;
    }
    *pval = ASN1_item_d2i(NULL, &p, (long)len, it);
    if (*pval == NULL) {
      goto err;
    }
    return 1;

 err:
    rctx->state = OHS_ERROR;
    return 0;
}

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
    // The following being written conforms to the message-header field
    // specification in https://www.rfc-editor.org/rfc/rfc2616#section-4.2.
    // message-header = field-name ":" [ field-value ]
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
