// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/base.h>
#include <openssl/bio.h>
#include <openssl/bytestring.h>
#include <openssl/err.h>
#include <openssl/evp.h>
#include <openssl/pem.h>
#include <openssl/pkcs8.h>
#include <openssl/stack.h>
#include <openssl/x509.h>
#include <cerrno>
#include <cstdio>
#include <cstring>
#include <string>
#include <vector>
#include "internal.h"

// Import only: -export is not implemented, and unsupported flags fail
// argument parsing rather than silently no-op. -legacy is accepted as a
// no-op so OpenSSL 3 scripts keep working; this library already decrypts
// the legacy PBEs that flag enables. -clcerts/-cacerts are also
// unsupported: they are conventionally selected by the localKeyID bag
// attribute, which PKCS12_get_key_and_certs does not expose, and
// approximating that by key matching would misclassify real-world bundles.

static const argument_t kArguments[] = {
    {"-help", kBooleanArgument, "Display option summary"},
    {"-in", kOptionalArgument, "Input PKCS#12 file (default stdin)"},
    {"-out", kOptionalArgument, "Output file (default stdout)"},
    {"-nokeys", kBooleanArgument, "Do not output the private key"},
    {"-nocerts", kBooleanArgument, "Do not output certificates"},
    {"-nodes", kBooleanArgument,
     "Do not encrypt the output private key (overrides -passout)"},
    {"-noout", kBooleanArgument,
     "Do not output certificates or keys; only parse and authenticate"},
    {"-passin", kOptionalArgument, "PKCS#12 import password source"},
    {"-password", kOptionalArgument,
     "Import password source; overrides -passin if both are given"},
    {"-passout", kOptionalArgument,
     "Encrypts (AES-256-CBC) the output private key; required to output "
     "a key unless -nokeys or -nodes is given"},
    {"-legacy", kBooleanArgument,
     "Accepted for OpenSSL 3 script compatibility; has no effect"},
    {"", kOptionalArgument, ""}};

static void print_usage() {
  fprintf(stderr,
          "Usage: pkcs12 [options]\n"
          "Imports a PKCS#12 file: writes every certificate it contains, "
          "followed by\n"
          "the private key. \"Bag Attributes\" metadata is not printed and "
          "-export is not\n"
          "implemented. A private key present without -nokeys requires "
          "-passout or\n"
          "-nodes; there is no interactive prompt.\n\n"
          "Valid options are:\n");
  PrintUsage(kArguments);
}

int pkcs12Tool(const args_list_t &args) {
  using namespace ordered_args;
  ordered_args_map_t parsed_args;
  args_list_t extra_args;

  if (!ParseOrderedKeyValueArguments(parsed_args, extra_args, args,
                                     kArguments)) {
    print_usage();
    return kToolExitFailure;
  }

  bool help = false;
  GetBoolArgument(&help, "-help", parsed_args);
  if (help) {
    print_usage();
    return kToolExitSuccess;
  }

  if (!extra_args.empty()) {
    fprintf(stderr,
            "Error: pkcs12 does not accept positional arguments (got '%s')\n",
            extra_args[0].c_str());
    return kToolExitFailure;
  }

  std::string in_path, out_path;
  GetString(&in_path, "-in", "", parsed_args);
  GetString(&out_path, "-out", "", parsed_args);
  if ((HasArgument(parsed_args, "-in") && in_path.empty()) ||
      (HasArgument(parsed_args, "-out") && out_path.empty())) {
    fprintf(stderr, "Error: input and output filenames must not be empty\n");
    return kToolExitFailure;
  }

  bool nokeys = false, nocerts = false, nodes = false, noout = false;
  GetBoolArgument(&nokeys, "-nokeys", parsed_args);
  GetBoolArgument(&nocerts, "-nocerts", parsed_args);
  GetBoolArgument(&nodes, "-nodes", parsed_args);
  GetBoolArgument(&noout, "-noout", parsed_args);

  // Sensitive strings are cleared automatically when these go out of scope.
  Password passin_arg;
  Password password_arg;
  Password passout_arg;
  GetString(&passin_arg.get(), "-passin", "", parsed_args);
  GetString(&password_arg.get(), "-password", "", parsed_args);
  GetString(&passout_arg.get(), "-passout", "", parsed_args);

  const bool passin_given = HasArgument(parsed_args, "-passin");
  const bool password_given = HasArgument(parsed_args, "-password");
  const bool passout_given = HasArgument(parsed_args, "-passout");

  // -password is an alias for -passin that wins regardless of option order.
  if (password_given) {
    passin_arg = password_arg;
  }
  password_arg.clear();

  // Validate the effective source after alias resolution. An empty password
  // is spelled "pass:", not an empty source argument.
  if ((passin_given || password_given) && passin_arg.empty()) {
    fprintf(stderr,
            "Error: input password source is empty (use pass: for empty)\n");
    return kToolExitFailure;
  }
  if (passout_given && passout_arg.empty()) {
    fprintf(stderr, "Error: -passout requires a value (use pass: for empty)\n");
    return kToolExitFailure;
  }

  if (!pass_util::ExtractPasswords(passin_arg, passout_arg)) {
    fprintf(stderr, "Error extracting passwords\n");
    return kToolExitFailure;
  }

  // PKCS#12 files are always DER/BER; there is no PEM form and hence no
  // -inform/-outform.
  std::vector<uint8_t> input_bytes;
  if (in_path.empty()) {
    if (!ReadAll(&input_bytes, stdin)) {
      fprintf(stderr, "Error reading PKCS#12 data from stdin\n");
      return kToolExitFailure;
    }
  } else {
    ScopedFILE in_file(fopen(in_path.c_str(), "rb"));
    if (!in_file) {
      fprintf(stderr, "Error: unable to open input file '%s': %s\n",
              in_path.c_str(), strerror(errno));
      return kToolExitFailure;
    }
    if (!ReadAll(&input_bytes, in_file.get())) {
      fprintf(stderr, "Error reading input file '%s': %s\n", in_path.c_str(),
              strerror(errno));
      return kToolExitFailure;
    }
  }

  if (input_bytes.empty()) {
    fprintf(stderr, "Error: no PKCS#12 data read from input\n");
    return kToolExitFailure;
  }

  bssl::UniquePtr<STACK_OF(X509)> certs(sk_X509_new_null());
  if (!certs) {
    fprintf(stderr, "Error: memory allocation failure\n");
    return kToolExitFailure;
  }

  EVP_PKEY *raw_key = nullptr;
  CBS pkcs12_cbs;
  CBS_init(&pkcs12_cbs, input_bytes.data(), input_bytes.size());
  const char *password_cstr =
      passin_arg.empty() ? nullptr : passin_arg.get().c_str();
  // This verifies the MAC and decrypts every bag before returning success,
  // and rolls |certs| back on failure, so bad input never yields partial
  // output.
  if (!PKCS12_get_key_and_certs(&raw_key, certs.get(), &pkcs12_cbs,
                                password_cstr)) {
    // A bad password gets a one-line diagnostic; ERR_LIB_PKCS12 has no
    // registered strings, so dumping the queue would only add noise. Other
    // failures (malformed data, missing MAC, unsupported PBE) dump the queue
    // so they can be told apart.
    const uint32_t err = ERR_peek_last_error();
    if (ERR_GET_LIB(err) == ERR_LIB_PKCS12 &&
        ERR_GET_REASON(err) == PKCS12_R_MAC_VERIFY_FAILURE) {
      fprintf(stderr, "Mac verify error: invalid password?\n");
      ERR_clear_error();
    } else {
      fprintf(stderr, "Error: unable to parse PKCS#12 input\n");
      ERR_print_errors_fp(stderr);
    }
    return kToolExitFailure;
  }
  bssl::UniquePtr<EVP_PKEY> key(raw_key);

  // Decide whether a key would be written, and whether that's allowed,
  // before opening -out so a rejection never touches it. Tests
  // passout_given rather than passout_arg.empty() so an explicitly empty
  // -passout ("pass:") counts as given.
  const bool emit_key = !noout && !nokeys && key;
  const bool emit_certs = !noout && !nocerts;
  if (emit_key && !nodes && !passout_given) {
    fprintf(stderr,
            "Error: input contains a private key. Pass -nokeys to omit it, "
            "-passout to PEM-encrypt it (AES-256-CBC), or -nodes to write "
            "it unencrypted; this tool does not prompt interactively.\n");
    return kToolExitFailure;
  }

  bssl::UniquePtr<BIO> out;
  if (out_path.empty()) {
    out.reset(BIO_new_fp(stdout, BIO_NOCLOSE));
  } else {
    // Output is owner-only regardless of whether a key ends up in it.
    SetUmaskForPrivateKey();
    out.reset(BIO_new_file(out_path.c_str(), "wb"));
  }
  if (!out) {
    fprintf(stderr, "Error: unable to open output '%s'\n",
            out_path.empty() ? "stdout" : out_path.c_str());
    ERR_print_errors_fp(stderr);
    return kToolExitFailure;
  }

  // PKCS12_get_key_and_certs flattens the bag structure, so file order
  // cannot be preserved exactly. Certificates then key matches the layout
  // PKCS12_create produces and keeps `pkcs12 ... | x509` pipelines working.
  if (emit_certs) {
    size_t num_certs = sk_X509_num(certs.get());
    for (size_t i = 0; i < num_certs; i++) {
      if (!PEM_write_bio_X509(out.get(), sk_X509_value(certs.get(), i))) {
        fprintf(stderr, "Error writing certificate %zu: %s\n", i,
                strerror(errno));
        ERR_print_errors_fp(stderr);
        return kToolExitFailure;
      }
    }
  }

  if (emit_key) {
    int ok = 0;
    if (nodes) {
      ok = PEM_write_bio_PKCS8PrivateKey(out.get(), key.get(), nullptr, nullptr,
                                         0, nullptr, nullptr);
    } else {
      ok = PEM_write_bio_PKCS8PrivateKey(
          out.get(), key.get(), EVP_aes_256_cbc(), passout_arg.get().c_str(),
          static_cast<int>(passout_arg.get().length()), nullptr, nullptr);
    }
    if (!ok) {
      fprintf(stderr, "Error writing private key: %s\n", strerror(errno));
      ERR_print_errors_fp(stderr);
      return kToolExitFailure;
    }
  }

  if (!BIO_flush(out.get())) {
    fprintf(stderr, "Error flushing output: %s\n", strerror(errno));
    return kToolExitFailure;
  }
  return kToolExitSuccess;
}
