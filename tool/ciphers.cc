/* Copyright (c) 2015, Google Inc.
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

#include <string>
#include <vector>

#include <stdint.h>
#include <stdlib.h>

#include <openssl/ssl.h>

#include "internal.h"
#include "../ssl/internal.h"

static const argument_t kArguments[] = {
    {
        "-openssl-name", kBooleanArgument,
        "Print OpenSSL-style cipher names instead of IETF cipher names.",
    },
    {
        "-cipher-query", kOptionalArgument,
        "An OpenSSL-style cipher suite string that is matched against "
        "supported ciphers. Defaults to \"ALL\".",
    },
    {
        "-print-all", kBooleanArgument,
        "Prints all supported AWS-LC libssl ciphers for all TLS versions. "
        "If this option is used, all other options are ignored, except for "
        "-openssl-name.",
    },
    {
        "", kOptionalArgument, "",
    },
};

bool Ciphers(const std::vector<std::string> &args) {
  args_map_t args_map;
  args_list_t extra_args;

  if (!ParseKeyValueArguments(args_map, extra_args, args, kArguments) ||
      extra_args.size() > 0) {
    PrintUsage(kArguments);
    return false;
  }

  bool print_all;
  if (!GetBoolArgument(&print_all, "-print-all", args_map)) {
    fprintf(stderr, "Error parsing -print-all\n");
    return false;
  }

  bool openssl_name;
  if (!GetBoolArgument(&openssl_name, "-openssl-name", args_map)) {
    fprintf(stderr, "Error parsing -openssl-name\n");
    return false;
  }

  if (print_all) {
    return tls_print_all_supported_cipher_suites(openssl_name);
  }

  // Use a lambda to conditionally initialise const.
  const std::string ciphers_string = [&] {
    std::string non_const_ciphers_string;
    if (!GetString(&non_const_ciphers_string, "-cipher-query", "ALL", args_map)) {
      // Return an empty string from lambda as error. This also captures the
      // case where the argument of |-cipher-query| is empty, which we can
      // regard as an error.
      return std::string();
    }
    return non_const_ciphers_string;
  }();

  if (ciphers_string.empty()) {
    fprintf(stderr, "Error parsing -cipher-query: Query cipher string is empty\n");
    return false;
  }

  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
  if (!SSL_CTX_set_strict_cipher_list(ctx.get(), ciphers_string.c_str())) {
    fprintf(stderr, "Failed to parse cipher suite config.\n");
    ERR_print_errors_fp(stderr);
    return false;
  }

  STACK_OF(SSL_CIPHER) *ciphers = SSL_CTX_get_ciphers(ctx.get());

  bool last_in_group = false;
  for (size_t i = 0; i < sk_SSL_CIPHER_num(ciphers); i++) {
    bool in_group = SSL_CTX_cipher_in_group(ctx.get(), i);
    const SSL_CIPHER *cipher = sk_SSL_CIPHER_value(ciphers, i);

    if (in_group && !last_in_group) {
      printf("[\n  ");
    } else if (last_in_group) {
      printf("  ");
    }

    printf("%s\n", openssl_name ? SSL_CIPHER_get_name(cipher)
                                : SSL_CIPHER_standard_name(cipher));

    if (!in_group && last_in_group) {
      printf("]\n");
    }
    last_in_group = in_group;
  }

  return true;
}
