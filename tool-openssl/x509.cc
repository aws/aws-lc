/* Copyright (c) 2014, Google Inc.
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

#include <openssl/x509.h>
#include <openssl/pem.h>
#include <stdio.h>
#include <string>
#include <vector>
#include "../tool/internal.h"
#include "internal.h"

static const argument_t kArguments[] = {
  { "-in", kRequiredArgument, "Input file" },
  { "-out", kRequiredArgument, "Output file" },
  { "", kOptionalArgument, "" }
};

// Map arguments using tool/args.cc
bool X509Tool(const args_list_t &args) {
    args_map_t parsed_args;
    if (!ParseKeyValueArguments(&parsed_args, args, kArguments)) {
        PrintUsage(kArguments);
        return false;
    }

    // Check for required arguments
    std::string in_path, out_path;
    if (!GetString(&in_path, "-in", "", parsed_args)) {
        fprintf(stderr, "Missing required argument: -in\n");
        PrintUsage(kArguments);
        return false;
    }
    if (!GetString(&out_path, "-out", "", parsed_args)) {
        fprintf(stderr, "Missing required argument: -out\n");
        PrintUsage(kArguments);
        return false;
    }

    // Read input file using ReadAll function from tool/file.cc
    std::vector<uint8_t> input_data;
    {
        FILE *in_file = fopen(in_path.c_str(), "rb");
        if (!in_file) {
            fprintf(stderr, "Failed to open input file '%s'.\n", in_path.c_str());
            return false;
        }
        if (!ReadAll(&input_data, in_file)) {
            fprintf(stderr, "Failed to read input file '%s'.\n", in_path.c_str());
            fclose(in_file);
            return false;
        }
        fclose(in_file);
    }

    // Parse x509 certificate from input file
    const uint8_t *p = input_data.data();
    X509 *x509 = d2i_X509(nullptr, &p, input_data.size());
    if (!x509) {
        fprintf(stderr, "Failed to parse X509 certificate from '%s'.\n", in_path.c_str());
        ERR_print_errors_fp(stderr);
        return false;
    }

    // Serialize certificate to DER format
    uint8_t *out_data = nullptr;
    int len = i2d_X509(x509, &out_data);
    if (len < 0) {
        fprintf(stderr, "Failed to serialize X509 certificate.\n");
        ERR_print_errors_fp(stderr);
        X509_free(x509);
        return false;
    }

    // Write output file using WriteToFile function from tool/file.cc
    if (!WriteToFile(out_path, out_data, len)) {
        fprintf(stderr, "Failed to write X509 certificate to '%s'.\n", out_path.c_str());
        OPENSSL_free(out_data);
        X509_free(x509);
        return false;
    }

    OPENSSL_free(out_data);
    X509_free(x509);
    return true;
}
