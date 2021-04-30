/* Copyright (c) 2016, Google Inc.
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

#include <gtest/gtest.h>

#include "openssl/ocsp.h"


#include "../internal.h"

std::string GetTestData(const char *path);

TEST(OCSPTest, TestBasic) {
  OCSP_RESPONSE *ocsp_response = NULL;

  static const struct {
    const char *file;
  } kTests[] = {
      {"ocsp_response.der"},
      {"ocsp_response_no_next_update.der"},
  };

  for (const auto &test : kTests) {
    SCOPED_TRACE(test.file);

    std::string path = "crypto/ocsp/test/";
    path += test.file;

    ocsp_response = d2i_OCSP_RESPONSE(NULL, (const unsigned char **) \
      GetTestData(path.c_str()).c_str(),GetTestData(path.c_str()).length());
    ASSERT_TRUE(ocsp_response);

//    int ocsp_status = OCSP_response_status(ocsp_response);
//    ASSERT_EQ(OCSP_RESPONSE_STATUS_SUCCESSFUL, ocsp_status);
  }
}
