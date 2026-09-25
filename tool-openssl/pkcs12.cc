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
#include <climits>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>
#include "internal.h"

// Imports PKCS#12 or exports PEM keys/certificates with -export. There are no
// interactive password prompts: an omitted password means the empty password.
// -legacy is a no-op; the library already supports legacy PBEs. Export uses
// OpenSSL 1.1.1's 3DES-key/RC2-40-cert/SHA1-MAC defaults: PKCS12_create cannot
// produce OpenSSL 3's PBES2/AES bags. Explicit PBES2 requests fail, never
// downgrade. Unsupported options (including -chain, -caname, -macalg, -nomac,
// -twopass, -info and -nomacver) fail argument parsing. -clcerts/-cacerts are
// unsupported: PKCS12_get_key_and_certs does not expose the localKeyID used to
// select them. Export-only options require -export, preserving import's strict
// validation.

static const argument_t kArguments[] = {
    {"-help", kBooleanArgument, "Display option summary"},
    {"-in", kOptionalArgument,
     "Input PKCS#12 file, or PEM for -export (default stdin)"},
    {"-export", kBooleanArgument, "Create a DER PKCS#12 file from PEM input"},
    {"-inkey", kOptionalArgument, "Export: PEM private key (default from -in)"},
    {"-certfile", kOptionalArgument, "Export: additional PEM certificates"},
    {"-name", kOptionalArgument, "Export: friendlyName for the key and leaf"},
    {"-keypbe", kOptionalArgument,
     "Export: PBE-SHA1-3DES (default), PBE-SHA1-RC2-40, or NONE"},
    {"-certpbe", kOptionalArgument,
     "Export: PBE-SHA1-RC2-40 (default), PBE-SHA1-3DES, or NONE"},
    {"-descert", kBooleanArgument, "Export: encrypt certificates with 3DES"},
    {"-iter", kOptionalArgument,
     "Export: positive encryption and MAC iteration count (default 2048)"},
    {"-noiter", kBooleanArgument, "Export: set encryption iterations to 1"},
    {"-maciter", kBooleanArgument,
     "Export: accepted as a no-op, matching OpenSSL 3"},
    {"-nomaciter", kBooleanArgument, "Export: set MAC iterations to 1"},
    {"-out", kOptionalArgument, "Output file (default stdout)"},
    {"-nokeys", kBooleanArgument, "Do not output the private key"},
    {"-nocerts", kBooleanArgument, "Do not output certificates"},
    {"-nodes", kBooleanArgument,
     "Do not encrypt the output private key (overrides -passout)"},
    {"-noout", kBooleanArgument,
     "Do not output certificates or keys; only parse and authenticate"},
    {"-passin", kOptionalArgument,
     "Input password source (decrypts the PEM key with -export)"},
    {"-password", kOptionalArgument,
     "Overrides -passin for import or -passout for export"},
    {"-passout", kOptionalArgument,
     "Export password source; for import, encrypts the output PEM key with "
     "AES-256-CBC (required unless -nokeys or -nodes)"},
    {"-legacy", kBooleanArgument,
     "Accepted for OpenSSL 3 script compatibility; has no effect"},
    {"", kOptionalArgument, ""}};

static void print_usage() {
  fprintf(stderr,
          "Usage: pkcs12 [options]\n"
          "Imports a PKCS#12 file: writes every certificate it contains, "
          "followed by\n"
          "the private key. \"Bag Attributes\" metadata is not printed. A "
          "private key\n"
          "present without -nokeys requires -passout or -nodes.\n"
          "With -export, reads PEM and writes DER using OpenSSL 1.1.1's "
          "3DES/RC2-40\n"
          "encryption and SHA1 MAC defaults. PBES2/AES export is unsupported.\n"
          "There are no interactive prompts; omitted passwords are empty.\n"
          "Export ignores -nodes; -noout leaves nothing to export and fails.\n"
          "Unsupported: -chain, -caname, -macalg, -nomac, -twopass, -info,\n"
          "-nomacver, -clcerts, -cacerts.\n\n"
          "Valid options are:\n");
  PrintUsage(kArguments);
}

static bssl::UniquePtr<BIO> OpenOutput(const std::string &path) {
  bssl::UniquePtr<BIO> out;
  if (path.empty()) {
    out.reset(BIO_new_fp(stdout, BIO_NOCLOSE));
  } else {
    // Output is owner-only regardless of whether a key ends up in it.
    SetUmaskForPrivateKey();
    out.reset(BIO_new_file(path.c_str(), "wb"));
  }
  if (!out) {
    fprintf(stderr, "Error: unable to open output '%s'\n",
            path.empty() ? "stdout" : path.c_str());
    ERR_print_errors_fp(stderr);
  }
  return out;
}

static bssl::UniquePtr<BIO> ReadPEMInput(const std::string &path,
                                         std::vector<uint8_t> *bytes) {
  ScopedFILE file;
  FILE *in = stdin;
  if (!path.empty()) {
    file.reset(fopen(path.c_str(), "rb"));
    if (!file) {
      fprintf(stderr, "Error: unable to open input file '%s': %s\n",
              path.c_str(), strerror(errno));
      return nullptr;
    }
    in = file.get();
  }
  if (!ReadAll(bytes, in) || bytes->empty()) {
    fprintf(stderr, "Error reading PEM input '%s'\n",
            path.empty() ? "stdin" : path.c_str());
    return nullptr;
  }
  // ReadAll caps files at 1 MiB. The caller keeps |bytes| alive for this
  // read-only BIO, whose reset rewinds without clearing the PEM contents.
  return bssl::UniquePtr<BIO>(BIO_new_mem_buf(bytes->data(), bytes->size()));
}

static bool ReadCertificates(BIO *in, STACK_OF(X509) *certs,
                             const char *password) {
  const size_t before = sk_X509_num(certs);
  for (;;) {
    // PEM encryption headers are possible even on certificates. Always
    // supply a non-null password so they cannot trigger an interactive prompt.
    bssl::UniquePtr<X509> cert(PEM_read_bio_X509_AUX(
        in, nullptr, nullptr, const_cast<char *>(password)));
    if (!cert) {
      const uint32_t err = ERR_peek_last_error();
      if (ERR_GET_LIB(err) == ERR_LIB_PEM &&
          ERR_GET_REASON(err) == PEM_R_NO_START_LINE) {
        ERR_clear_error();
        break;
      }
      fprintf(stderr, "Error reading PEM certificate\n");
      ERR_print_errors_fp(stderr);
      return false;
    }
    if (!bssl::PushToStack(certs, std::move(cert))) {
      return false;
    }
  }
  if (sk_X509_num(certs) == before) {
    fprintf(stderr, "Error: no certificates in PEM input\n");
    return false;
  }
  return true;
}

static bool ParsePBE(int *nid, const std::string &name) {
  if (OPENSSL_strcasecmp(name.c_str(), "PBE-SHA1-3DES") == 0) {
    *nid = NID_pbe_WithSHA1And3_Key_TripleDES_CBC;
  } else if (OPENSSL_strcasecmp(name.c_str(), "PBE-SHA1-RC2-40") == 0) {
    *nid = NID_pbe_WithSHA1And40BitRC2_CBC;
  } else if (name == "NONE") {
    *nid = -1;
  } else {
    if (EVP_get_cipherbyname(name.c_str()) != nullptr) {
      fprintf(stderr,
              "Error: unsupported PBES2 export algorithm '%s': "
              "PKCS12_create only supports legacy PBE schemes\n",
              name.c_str());
    } else {
      fprintf(stderr, "Error: unknown PBE algorithm '%s'\n", name.c_str());
    }
    return false;
  }
  return true;
}

// Import keeps its existing first-value behavior. OpenSSL export options use
// the last value, while alias resolution (-password) happens after parsing.
static void GetExportString(std::string *out, const char *name,
                            const ordered_args::ordered_args_map_t &args) {
  out->clear();
  for (auto it = args.rbegin(); it != args.rend(); ++it) {
    if (it->first == name) {
      *out = it->second;
      return;
    }
  }
}

static int ExportPKCS12(const ordered_args::ordered_args_map_t &args,
                        const std::string &in_path,
                        const std::string &out_path) {
  using namespace ordered_args;
  bool nokeys = HasArgument(args, "-nokeys");
  bool nocerts = HasArgument(args, "-nocerts");
  if (HasArgument(args, "-noout") || (nokeys && nocerts)) {
    fprintf(stderr,
            "Nothing to export due to -noout or -nocerts and -nokeys\n");
    return kToolExitFailure;
  }
  if (HasArgument(args, "-nodes")) {
    fprintf(stderr,
            "Warning: output encryption option -nodes ignored with "
            "-export\n");
  }

  int key_nid = NID_pbe_WithSHA1And3_Key_TripleDES_CBC;
  int cert_nid = NID_pbe_WithSHA1And40BitRC2_CBC;
  // Unlike the library's MAC default of 1, both reference CLIs use 2048.
  int iterations = PKCS12_DEFAULT_ITER, mac_iterations = PKCS12_DEFAULT_ITER;
  for (const auto &arg : args) {
    if (arg.first == "-keypbe" || arg.first == "-certpbe") {
      if (!ParsePBE(arg.first == "-keypbe" ? &key_nid : &cert_nid,
                    arg.second)) {
        return kToolExitFailure;
      }
    } else if (arg.first == "-descert") {
      cert_nid = NID_pbe_WithSHA1And3_Key_TripleDES_CBC;
    } else if (arg.first == "-iter") {
      char *end = nullptr;
      errno = 0;
      long count = strtol(arg.second.c_str(), &end, 10);
      if (errno == ERANGE || end == arg.second.c_str() || *end != '\0' ||
          count <= 0 || count > INT_MAX) {
        fprintf(stderr, "Error: -iter requires a positive integer\n");
        return kToolExitFailure;
      }
      iterations = mac_iterations = static_cast<int>(count);
    } else if (arg.first == "-noiter") {
      iterations = 1;
    } else if (arg.first == "-nomaciter") {
      mac_iterations = 1;
    }
    // -maciter is a no-op in OpenSSL 3 (which introduced -iter). Process the
    // other iteration flags in order; -nomaciter does not disable the MAC.
  }

  std::string key_path, cert_path, name;
  GetExportString(&key_path, "-inkey", args);
  GetExportString(&cert_path, "-certfile", args);
  GetExportString(&name, "-name", args);
  if ((HasArgument(args, "-inkey") && key_path.empty()) ||
      (HasArgument(args, "-certfile") && cert_path.empty())) {
    fprintf(stderr, "Error: input filenames must not be empty\n");
    return kToolExitFailure;
  }

  Password passin, passout;
  GetExportString(&passin.get(), "-passin", args);
  // apps/pkcs12.c in OpenSSL_1_1_1w and openssl-3.0.16 resolves -password
  // after parsing: it overrides -passout on export, never -passin.
  if (HasArgument(args, "-password")) {
    GetExportString(&passout.get(), "-password", args);
  } else {
    GetExportString(&passout.get(), "-passout", args);
  }
  if ((HasArgument(args, "-passin") && passin.empty()) ||
      ((HasArgument(args, "-passout") || HasArgument(args, "-password")) &&
       passout.empty())) {
    fprintf(stderr, "Error: password source is empty (use pass: for empty)\n");
    return kToolExitFailure;
  }
  if (!pass_util::ExtractPasswords(passin, passout)) {
    fprintf(stderr, "Error extracting passwords\n");
    return kToolExitFailure;
  }

  // Buffer -in once so combined PEM input works on non-seekable stdin too.
  std::vector<uint8_t> input_bytes;
  bssl::UniquePtr<BIO> in;
  if (!nocerts || (!nokeys && key_path.empty())) {
    in = ReadPEMInput(in_path, &input_bytes);
    if (!in) {
      return kToolExitFailure;
    }
  }
  bssl::UniquePtr<EVP_PKEY> key;
  if (!nokeys) {
    std::vector<uint8_t> key_bytes;
    bssl::UniquePtr<BIO> key_in;
    if (!key_path.empty()) {
      key_in = ReadPEMInput(key_path, &key_bytes);
      if (!key_in) {
        return kToolExitFailure;
      }
    }
    // A non-null password (even "") prevents PEM's default callback from
    // prompting. Decrypt input keys only with -passin, not -passout.
    key.reset(PEM_read_bio_PrivateKey(
        key_in ? key_in.get() : in.get(), nullptr, nullptr,
        const_cast<char *>(passin.get().c_str())));
    if (!key) {
      fprintf(stderr, "Error reading PEM private key\n");
      ERR_print_errors_fp(stderr);
      return kToolExitFailure;
    }
    if (!key_in && BIO_reset(in.get()) != 1) {
      return kToolExitFailure;
    }
  }

  bssl::UniquePtr<STACK_OF(X509)> certs(sk_X509_new_null());
  bssl::UniquePtr<X509> leaf;
  if (!certs) {
    return kToolExitFailure;
  }
  if (!nocerts) {
    if (!ReadCertificates(in.get(), certs.get(), passin.get().c_str())) {
      return kToolExitFailure;
    }
    if (key) {
      for (size_t i = 0; i < sk_X509_num(certs.get()); i++) {
        if (X509_check_private_key(sk_X509_value(certs.get(), i), key.get())) {
          leaf.reset(sk_X509_delete(certs.get(), i));
          // OpenSSL discards input auxiliary attributes on the matching leaf.
          X509_keyid_set1(leaf.get(), nullptr, 0);
          X509_alias_set1(leaf.get(), nullptr, 0);
          break;
        }
        ERR_clear_error();
      }
      if (!leaf) {
        fprintf(stderr, "No certificate matches private key\n");
        return kToolExitFailure;
      }
    }
  }
  // Like OpenSSL, -nocerts suppresses certificates from -in, but not an
  // explicitly supplied -certfile. It does not perform chain building.
  if (!cert_path.empty()) {
    std::vector<uint8_t> chain_bytes;
    auto chain_in = ReadPEMInput(cert_path, &chain_bytes);
    if (!chain_in || !ReadCertificates(chain_in.get(), certs.get(), "")) {
      return kToolExitFailure;
    }
  }

  // PKCS12_create derives the same localKeyID from the leaf for both bags,
  // enabling Java keytool to recognize a PrivateKeyEntry and its chain.
  bssl::UniquePtr<PKCS12> p12(
      PKCS12_create(passout.get().c_str(),
                    HasArgument(args, "-name") ? name.c_str() : nullptr,
                    key.get(), leaf.get(), certs.get(), key_nid, cert_nid,
                    iterations, mac_iterations, 0));
  if (!p12) {
    fprintf(stderr, "Error creating PKCS#12 structure\n");
    ERR_print_errors_fp(stderr);
    return kToolExitFailure;
  }
  // Do not open/truncate output until every input and the complete bundle
  // have been validated. This also allows -in/-inkey/-certfile to equal -out.
  auto out = OpenOutput(out_path);
  if (!out) {
    return kToolExitFailure;
  }
  if (!i2d_PKCS12_bio(out.get(), p12.get()) || !BIO_flush(out.get())) {
    fprintf(stderr, "Error writing PKCS#12 output\n");
    ERR_print_errors_fp(stderr);
    return kToolExitFailure;
  }
  return kToolExitSuccess;
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
  const bool export_mode = HasArgument(parsed_args, "-export");
  if (export_mode) {
    GetExportString(&in_path, "-in", parsed_args);
    GetExportString(&out_path, "-out", parsed_args);
  } else {
    GetString(&in_path, "-in", "", parsed_args);
    GetString(&out_path, "-out", "", parsed_args);
  }
  if ((HasArgument(parsed_args, "-in") && in_path.empty()) ||
      (HasArgument(parsed_args, "-out") && out_path.empty())) {
    fprintf(stderr, "Error: input and output filenames must not be empty\n");
    return kToolExitFailure;
  }

  if (export_mode) {
    return ExportPKCS12(parsed_args, in_path, out_path);
  }
  for (const auto &arg : parsed_args) {
    if (arg.first == "-inkey" || arg.first == "-certfile" ||
        arg.first == "-name" || arg.first == "-keypbe" ||
        arg.first == "-certpbe" || arg.first == "-descert" ||
        arg.first == "-iter" || arg.first == "-noiter" ||
        arg.first == "-maciter" || arg.first == "-nomaciter") {
      fprintf(stderr, "Error: %s requires -export\n", arg.first.c_str());
      return kToolExitFailure;
    }
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
  // This verifies the MAC and decrypts every bag before returning success,
  // and rolls |certs| back on failure, so bad input never yields partial
  // output. The password buffer is borrowed from |passin_arg|, whose
  // destructor cleanses it.
  if (!PKCS12_get_key_and_certs(
          &raw_key, certs.get(), &pkcs12_cbs,
          passin_arg.empty() ? nullptr : passin_arg.get().c_str())) {
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

  auto out = OpenOutput(out_path);
  if (!out) {
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
