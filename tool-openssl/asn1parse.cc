// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/bio.h>
#include <openssl/pem.h>
#include "internal.h"

static const argument_t kArguments[] = {
    {"-help", kBooleanArgument, "Display option summary"},
    {"-in", kOptionalArgument, "Input file"},
    {"-inform", kOptionalArgument, "Input file format: PEM or DER"},
    {"", kOptionalArgument, ""}};

enum Format {
  FORMAT_PEM = 1,
  FORMAT_DER = 2
};

using ossl_free = decltype(&OPENSSL_free);

using ossl_uint8_ptr = std::unique_ptr<uint8_t, ossl_free>;
using ossl_char_ptr = std::unique_ptr<char, ossl_free>;

bool asn1parseTool(const args_list_t &args) {
  using namespace ordered_args;
  ordered_args_map_t parsed_args;
  args_list_t extra_args;
  if (!ParseOrderedKeyValueArguments(parsed_args, extra_args, args, kArguments)) {
    PrintUsage(kArguments);
    return false;
  }

  std::string in_path, inform_str;
  int input_format = FORMAT_PEM;
  bssl::UniquePtr<BIO> input_bio, stdout_bio;
  uint8_t *raw_input_bytes = nullptr;
  ossl_uint8_ptr input_bytes(nullptr, &OPENSSL_free);
  size_t input_bytes_len = 0;
  
  bool help = false;

  GetBoolArgument(&help, "-help", parsed_args);
  GetString(&in_path, "-in", "", parsed_args);
  GetString(&inform_str, "-inform", "PEM", parsed_args);

  // Display asn1parse tool option summary
  if (help) {
    PrintUsage(kArguments);
    return false;
  }

  if (isStringUpperCaseEqual(inform_str, "DER")) {
    input_format = FORMAT_DER;
  } else if (isStringUpperCaseEqual(inform_str, "PEM")) {
    input_format = FORMAT_PEM;
  } else {
    fprintf(stderr, "Error: Invalid input format '%s'. Must be PEM or DER\n", inform_str.c_str());
    goto err;
  }

  if (in_path.empty()) {
    fprintf(stderr, "Error: missing required argument '-in'\n");
    return false;
  }

  input_bio.reset(in_path.empty() ? BIO_new_fp(stdin, BIO_NOCLOSE)
                                  : BIO_new_file(in_path.c_str(), "rb"));
  if (!input_bio) {
    fprintf(stderr, "Error: Could not open input\n");
    goto err;
  }

  stdout_bio.reset(BIO_new_fp(stdout, BIO_NOCLOSE));
  if (!stdout_bio) {
    fprintf(stderr, "Error: Could not open standard output\n");
    goto err;
  }

  if (input_format == FORMAT_DER) {
    bssl::UniquePtr<BUF_MEM> buf(BUF_MEM_new());
    if (!buf || !BUF_MEM_grow(buf.get(), BUFSIZ * 8)) {
      fprintf(stderr, "Error: could not allocate memory buffer\n");
      goto err;
    }

    input_bytes_len = 0;
    int i = 0;
    // We could use BIO_read_asn1 here, but it does have some limitations. So match the OpenSSL behavior
    // here instead.
    for (;;) {
      if (!BUF_MEM_grow(buf.get(), input_bytes_len + BUFSIZ)) {
        goto err;
      }
      i = BIO_read(input_bio.get(), &(buf->data[input_bytes_len]), BUFSIZ);
      if (i <= 0)
        break;
      if (input_bytes_len + i > LONG_MAX) {
        goto err;
      }
      input_bytes_len += i;
    }
    // Take ownership of buf->data
    raw_input_bytes = reinterpret_cast<uint8_t *>(buf->data);
    buf->data = nullptr;
    input_bytes.reset(raw_input_bytes);
  } else {
    char *raw_name = nullptr;
    char *raw_header = nullptr;
    ossl_char_ptr name(nullptr, &OPENSSL_free);
    ossl_char_ptr header(nullptr, &OPENSSL_free);

    // Technically this is the `-strictpem` behavior from OpenSSL in combination with `-inform PEM`. Otherwise OpenSSL
    // would try to base64 decode outside of PEM blocks. This seems like a niche edge case so adopting the strict
    // behavior for now.
    long input_len = 0;
    if (!PEM_read_bio(input_bio.get(), &raw_name, &raw_header, &raw_input_bytes, &input_len)) {
      fprintf(stderr, "Error reading PEM file\n");
      goto err;
    }

    // We don't need the name or header, but the function doesn't allow nullptr
    // so configure it so we free them.
    name.reset(raw_name);
    header.reset(raw_header);
    input_bytes_len = input_len;
    input_bytes.reset(raw_input_bytes);
  }

  if (input_bytes_len > LONG_MAX) {
    fprintf(stderr, "Error: input file too large\n");
    goto err;
  }

  if (!ASN1_parse(stdout_bio.get(), input_bytes.get(), (long)input_bytes_len,
                  0)) {
    goto err;
  }

  return true;

err:
  ERR_print_errors_fp(stderr);
  return false;
}
