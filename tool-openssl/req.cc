// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <cstdio>
#include <cstring>

#include <algorithm>
#include <iostream>

#include <openssl/base.h>
#include <openssl/bio.h>
#include <openssl/err.h>
#include <openssl/evp.h>
#include <openssl/pem.h>
#include <openssl/rsa.h>
#include "../tool/internal.h"

#include "ca_req_common.h"
#include "internal.h"

#define DEFAULT_KEY_LENGTH 2048
#define MIN_KEY_LENGTH 512
#define MAX_KEY_LENGTH 16384
#define BUF_SIZE 1024

// NOTES:
// 1. We do not support -in as of now, so -new is implied with -x509.
//
// 2. AWS-LC does not support config files by design, but some of our
// dependencies still use this cli command with -config. Therefore, we decided
// to implement -config but will only parse a MINIMAL set of fields (e.g.,
// default_md, distiguished_name, etc.). This set will be updated and
// re-evaluated on an as-needed basis.
//
// 3. OpenSSL has a default config file when user input is not provided.
// https://github.com/openssl/openssl/blob/master/apps/openssl.cnf
// We don't support this default config file interface. For fields that are not
// overriden by user input, we hardcode default values (e.g. X509 extensions,
// -keyout defaults to privkey.pem, etc.)
static const argument_t kArguments[] = {
    {"-help", kBooleanArgument, "Display option summary"},
    {"-md5", kExclusiveBooleanArgument, "Supported digest function"},
    {"-ripemd160", kExclusiveBooleanArgument, "Supported digest function"},
    {"-sha1", kExclusiveBooleanArgument, "Supported digest function"},
    {"-sha256", kExclusiveBooleanArgument,
     "Supported digest function (default)"},
    {"-sha224", kExclusiveBooleanArgument, "Supported digest function"},
    {"-sha384", kExclusiveBooleanArgument, "Supported digest function"},
    {"-sha512", kExclusiveBooleanArgument, "Supported digest function"},
    {"-new", kBooleanArgument,
     "Generates a new certificate request."
     "It will prompt the user for the relevant field values."
     "If the -newkey option is not given it will generate a new "
     "private key with 2048 bits length"},
    {"-newkey", kOptionalArgument,
     "This option is used to generate a new private "
     "key. This option supports RSA keys in the format [rsa:]nbits. "
     "If nbits is not given, i.e. -newkey rsa is specified, 2048 "
     "bits length is used. This implies -new unless used with -x509."},
    {"-days", kOptionalArgument,
     "When -x509 is in use this specifies the number of "
     "days from today to certify the certificate for, otherwise it "
     "is ignored. n should be a positive integer. The default is"
     "30 days."},
    {"-nodes", kBooleanArgument,
     "If this option is specified then if a private "
     "key is created it will not be encrypted."},
    {"-x509", kBooleanArgument,
     "This option outputs a certificate instead of"
     "a certificate request. If the -newkey option is not given it "
     "will generate a new private key with 2048 bits length"},
    {"-subj", kOptionalArgument,
     "Sets subject name for new request. The arg must "
     "be formatted as /type0=value0/type1=value1/type2=.... "
     "Keyword characters may be escaped by \\ (backslash), and "
     "whitespace is retained."},
    {"-config", kOptionalArgument, "This specifies the request template file"},
    {"-extensions", kOptionalArgument,
     "Cert or request extension section (override value in config file)"},
    {"-key", kOptionalArgument,
     "This specifies the key file path to be used for signing."},
    {"-passin", kOptionalArgument,
     "This specifies the input private key password source."},
    {"-passout", kOptionalArgument,
     "This specifies the output private key password source."},
    {"-keyout", kOptionalArgument,
     "This specifies the output filename for the "
     " private key or writes to a file called privkey.pem in the current "
     "directory."},
    {"-out", kOptionalArgument,
     "This specifies the output filename to write to or "
     "standard output by default."},
    {"-outform", kOptionalArgument,
     "This specifies the output format. Valid options are -DER and -PEM"},
    {"", kOptionalArgument, ""}};


// Parse key specification string and generate key. Valid strings are in the
// format rsa:nbits. RSA key with 2048 bit length is used by default is
// |keyspec| is not valid.
static EVP_PKEY *GenerateKey(const char *keyspec, long default_keylen) {
  EVP_PKEY *pkey = NULL;
  long keylen = default_keylen;
  int pkey_type = EVP_PKEY_RSA;

  // Parse keyspec
  if (OPENSSL_strncasecmp(keyspec, "rsa:", 4) == 0) {
    char *endptr = NULL;
    errno = 0;
    long value = strtol(keyspec + 4, &endptr, 10);
    if (endptr != keyspec + 4 && *endptr == '\0' && errno != ERANGE) {
      keylen = value;
    } else {
      // Note: For OpenSSL, if the second part of keyspec (after the colon `:`)
      // is not a number, it will be treated as a parameter file path rather
      // than a key size. We do not support that at the moment and choose to
      // fall back to a default key size instead.
      fprintf(
          stderr,
          "Warning: Invalid RSA key length: %s, using default length of %ld "
          "bits\n",
          keyspec + 4, default_keylen);
    }
  } else if (OPENSSL_strcasecmp(keyspec, "rsa") == 0) {
    keylen = default_keylen;
  } else {
    fprintf(
        stderr,
        "Unknown key specification: %s. Only RSA key generation is supported\n",
        keyspec);
    return NULL;
  }

  // Validate key length
  if (keylen < MIN_KEY_LENGTH) {
    fprintf(stderr, "Key length too short (minimum %d bits)\n", MIN_KEY_LENGTH);
    return NULL;
  }

  if (keylen > MAX_KEY_LENGTH) {
    fprintf(stderr, "Key length too large (maximum %d bits)\n", MAX_KEY_LENGTH);
    return NULL;
  }

  // Create key generation context
  bssl::UniquePtr<EVP_PKEY_CTX> ctx(EVP_PKEY_CTX_new_id(pkey_type, NULL));
  if (ctx == NULL) {
    return NULL;
  }

  if (EVP_PKEY_keygen_init(ctx.get()) <= 0 ||
      EVP_PKEY_CTX_set_rsa_keygen_bits(ctx.get(), keylen) <= 0 ||
      EVP_PKEY_keygen(ctx.get(), &pkey) <= 0) {
    return NULL;
  }

  return pkey;
}

static bssl::UniquePtr<X509_NAME> BuildSubject(
    X509_REQ *req, CONF *req_conf, const std::string &req_section, bool is_csr,
    bool no_prompt, unsigned long chtype = MBSTRING_ASC) {
  // Get the subject name from the request
  bssl::UniquePtr<X509_NAME> subj(X509_NAME_new());
  if (!subj) {
    fprintf(stderr, "Error getting subject name from request\n");
    return NULL;
  }

  if (!no_prompt) {
    fprintf(stdout,
            "You are about to be asked to enter information that will be "
            "incorporated\n");
    fprintf(stdout, "into your certificate request.\n");
    fprintf(
        stdout,
        "What you are about to enter is what is called a Distinguished Name "
        "or a DN.\n");
    fprintf(stdout,
            "There are quite a few fields but you can leave some blank\n");
    fprintf(stdout, "For some fields there will be a default value,\n");
    fprintf(stdout, "If you enter '.', the field will be left blank.\n");
    fprintf(stdout, "\n");
  }

  char buffer[BUF_SIZE];
  const char *dn_section = NULL;
  if (req_conf) {
    dn_section = NCONF_get_string(req_conf, req_section.c_str(), REQ_DN_OPT);
  }

  // Process each subject field
  for (const auto &field : subject_fields) {
    const char *value = NULL;

    // Obtain value from config file if available
    if (req_conf && dn_section) {
      value = NCONF_get_string(req_conf, dn_section, field.field_ln);

      if (!value) {
        value = NCONF_get_string(req_conf, dn_section, field.field_sn);
      }
    }

    // Prompt user for input if no value available
    if (!value && !no_prompt) {
      value = PromptField(field, buffer, sizeof(buffer));
      if (value == NULL) {
        return NULL;
      }
    }

    // Only add non-empty values
    if (value && OPENSSL_strnlen(value, BUF_SIZE) > 0) {
      if (!X509_NAME_add_entry_by_NID(
              subj.get(), field.nid, chtype,
              reinterpret_cast<const unsigned char *>(value), -1, -1, 0)) {
        fprintf(stderr, "Error adding %s to subject\n", field.field_ln);
        return NULL;
      }
    }
  }

  if (X509_NAME_entry_count(subj.get()) == 0) {
    fprintf(stderr, "Error: At least one subject field must be provided.\n");
    return NULL;
  }

  const char *attr_section = NULL;
  if (req_conf) {
    attr_section =
        NCONF_get_string(req_conf, req_section.c_str(), REQ_ATTRIBUTES_OPT);
  }
  // If this is a CSR, handle extra attributes
  if (is_csr) {
    if (!no_prompt) {
      fprintf(stdout, "\nPlease enter the following 'extra' attributes\n");
      fprintf(stdout, "to be sent with your certificate request\n");
    }

    // Process each extra attribute
    for (const auto &attr : extra_attributes) {
      const char *value = NULL;

      // Obtain value from config file if available
      if (req_conf && attr_section) {
        value = NCONF_get_string(req_conf, attr_section, attr.field_ln);

        if (!value) {
          value = NCONF_get_string(req_conf, attr_section, attr.field_sn);
        }
      }

      // Prompt user for input if no value available
      if (!value && !no_prompt) {
        value = PromptField(attr, buffer, sizeof(buffer));
        if (value == NULL) {
          return NULL;
        }
      }

      // Only add non-empty attributes
      if (value && OPENSSL_strnlen(value, BUF_SIZE) > 0) {
        bssl::UniquePtr<X509_ATTRIBUTE> x509_attr(X509_ATTRIBUTE_create_by_NID(
            nullptr, attr.nid, MBSTRING_ASC,
            reinterpret_cast<const unsigned char *>(value), -1));
        if (!x509_attr) {
          fprintf(stderr, "Error creating attribute %s\n", attr.field_ln);
          return NULL;
        }

        if (!X509_REQ_add1_attr(req, x509_attr.get())) {
          fprintf(stderr, "Error adding attribute %s to request\n",
                  attr.field_ln);
          return NULL;
        }
      }
    }
  }

  return subj;
}

static bool MakeCertificateRequest(X509_REQ *req, EVP_PKEY *pkey,
                                   std::string &subject_name, CONF *req_conf,
                                   const std::string &req_section, bool is_csr,
                                   bool no_prompt) {
  bssl::UniquePtr<X509_NAME> name;

  // version 1
  if (!X509_REQ_set_version(req, 0L)) {
    return 0;
  }

  if (subject_name.empty()) {  // Prompt the user
    name = BuildSubject(req, req_conf, req_section, is_csr, no_prompt);
  } else {  // Parse user provided string
    name = ParseSubjectName(subject_name);
    if (!name) {
      return false;
    }
  }

  if (!X509_REQ_set_subject_name(req, name.get())) {
    return false;
  }

  if (!X509_REQ_set_pubkey(req, pkey)) {
    return false;
  }

  return true;
}

static int AdaptKeyIDExtension(X509 *cert, X509V3_CTX *ext_ctx,
                               const char *name, const char *value,
                               int add_if_missing) {
  bssl::UniquePtr<X509_EXTENSION> new_keyid_ext(
      X509V3_EXT_nconf(NULL, ext_ctx, name, value));

  if (new_keyid_ext == NULL) {
    return 0;
  }

  const ASN1_OBJECT *keyid_ext_obj =
      X509_EXTENSION_get_object(new_keyid_ext.get());
  if (keyid_ext_obj == NULL) {
    return 0;
  }

  // Check if the requested key identifier extension is already present
  int idx = X509_get_ext_by_OBJ(cert, keyid_ext_obj, -1);
  if (idx >= 0) {
    return 1;  // Extension found
  }

  return !add_if_missing || X509_add_ext(cert, new_keyid_ext.get(), -1);
}

static bool AddCertExtensions(X509 *cert, CONF *req_conf,
                              std::string &ext_section) {
  // Set up X509V3 context for certificate
  bool result = true;
  X509V3_CTX ext_ctx;
  X509V3_set_ctx(&ext_ctx, cert, cert, NULL, NULL,
                 X509V3_CTX_REPLACE);  // self-signed

  if (req_conf != NULL) {
    X509V3_set_nconf(&ext_ctx, req_conf);

    // Add extensions from config to the certificate
    if (!ext_section.empty()) {
      result = X509V3_EXT_add_nconf(req_conf, &ext_ctx, ext_section.c_str(),
                                    cert) != 0;
    }

    /* Prevent X509_V_ERR_MISSING_SUBJECT_KEY_IDENTIFIER */
    if (!AdaptKeyIDExtension(cert, &ext_ctx, "subjectKeyIdentifier", "hash",
                             1)) {
      fprintf(stderr, "Error: Failed to handle subject key identifier\n");
      return false;
    }
    /* Prevent X509_V_ERR_MISSING_AUTHORITY_KEY_IDENTIFIER */
    if (!AdaptKeyIDExtension(cert, &ext_ctx, "authorityKeyIdentifier",
                             "keyid, issuer", 0)) {
      fprintf(stderr, "Error: Failed to handle authority key identifier\n");
      return false;
    }
  } else {
    const char *default_config =
        "[v3_ca]\n"
        "subjectKeyIdentifier=hash\n"
        "authorityKeyIdentifier=keyid:always,issuer:always\n"
        "basicConstraints=critical,CA:true\n";

    // Create a BIO for the config
    bssl::UniquePtr<BIO> bio(
        BIO_new_mem_buf(default_config, strlen(default_config)));
    if (!bio) {
      fprintf(stderr, "Failed to create memory BIO\n");
      return false;
    }

    bssl::UniquePtr<CONF> conf(NCONF_new(NULL));
    if (!conf) {
      fprintf(stderr, "Error: Failed to create CONF structure\n");
      return false;
    }

    if (NCONF_load_bio(conf.get(), bio.get(), NULL) <= 0) {
      fprintf(stderr, "Error: Failed to load config from BIO\n");
      return false;
    }

    X509V3_set_nconf(&ext_ctx, conf.get());

    // Add extensions from config to the certificate
    result = X509V3_EXT_add_nconf(conf.get(), &ext_ctx, "v3_ca", cert) != 0;
  }

  return result;
}

static bool AddReqExtensions(X509_REQ *req, CONF *req_conf,
                             std::string &ext_section) {
  // Set up X509V3 context for certificate
  bool result = true;
  X509V3_CTX ext_ctx;
  X509V3_set_ctx(&ext_ctx, NULL, NULL, req, NULL,
                 X509V3_CTX_REPLACE);  // self-signed

  if (req_conf != NULL && !ext_section.empty()) {
    X509V3_set_nconf(&ext_ctx, req_conf);

    // Add extensions from config to the certificate
    result = X509V3_EXT_REQ_add_nconf(req_conf, &ext_ctx, ext_section.c_str(),
                                      req) != 0;
  } else {
    const char *default_config =
        "[v3_req]\n"
        "basicConstraints=CA:FALSE\n"
        "keyUsage=nonRepudiation,digitalSignature,keyEncipherment\n";

    // Create a BIO for the config
    bssl::UniquePtr<BIO> bio(BIO_new_mem_buf(default_config, -1));
    if (!bio) {
      fprintf(stderr, "Failed to create memory BIO\n");
      return false;
    }

    bssl::UniquePtr<CONF> conf(NCONF_new(NULL));
    if (!conf) {
      fprintf(stderr, "Error: Failed to create CONF structure\n");
      return false;
    }

    if (NCONF_load_bio(conf.get(), bio.get(), NULL) <= 0) {
      fprintf(stderr, "Error: Failed to load config from BIO\n");
      return false;
    }

    X509V3_set_nconf(&ext_ctx, conf.get());

    // Add extensions from config to the certificate
    result = X509V3_EXT_REQ_add_nconf(conf.get(), &ext_ctx, "v3_req", req) != 0;
  }

  return result;
}

// Generate a random serial number for a certificate
static bool GenerateSerial(X509 *cert) {
  bssl::UniquePtr<BIGNUM> bn(BN_new());
  if (!bn) {
    fprintf(stderr, "Error: Failed to create BIGNUM for serial\n");
    return false;
  }

  /*
   * Randomly generate a serial number
   *
   * IETF RFC 5280 says serial number must be <= 20 bytes. Use 159 bits
   * so that the first bit will never be one, so that the DER encoding
   * rules won't force a leading octet.
   */
  constexpr int SERIAL_RAND_BITS = 159;
  if (!BN_rand(bn.get(), SERIAL_RAND_BITS, BN_RAND_TOP_ANY,
               BN_RAND_BOTTOM_ANY)) {
    fprintf(stderr, "Error: Failed to generate random serial number\n");
    return false;
  }

  ASN1_INTEGER *serial = X509_get_serialNumber(cert);
  if (!serial) {
    fprintf(stderr, "Error: Failed to get certificate serial number field\n");
    return false;
  }

  if (!BN_to_ASN1_INTEGER(bn.get(), serial)) {
    fprintf(stderr, "Error: Failed to convert BIGNUM to ASN1_INTEGER\n");
    return false;
  }

  return true;
}

static bool WritePrivateKey(std::string &out_path,
                            Password &passout,
                            bssl::UniquePtr<EVP_PKEY> &pkey,
                            const EVP_CIPHER *cipher) {
  bssl::UniquePtr<BIO> out_bio;
  SetUmaskForPrivateKey();

  fprintf(stderr, "Writing private key to %s\n", out_path.c_str());

  out_bio.reset(BIO_new(BIO_s_file()));
  if (!out_bio) {
    fprintf(stderr, "Error: unable to create file %s\n", out_path.c_str());
    return false;
  }

  if (1 != BIO_write_filename(out_bio.get(), out_path.c_str())) {
    fprintf(stderr, "Error: unable to write to '%s'\n", out_path.c_str());
    return false;
  }

  if (!passout.empty() && !pass_util::ExtractPassword(passout)) {
    fprintf(stderr, "Error: Failed to extract password\n");
    return false;
  }

  if (!PEM_write_bio_PKCS8PrivateKey(
          out_bio.get(), pkey.get(), cipher,
          passout.empty() ? nullptr : passout.get().c_str(),
          passout.empty() ? 0 : passout.get().length(), nullptr, nullptr)) {
    fprintf(stderr, "Error: Failed to write private key.\n");
    return false;
  }


  return true;
}

bool reqTool(const args_list_t &args) {
  using namespace ordered_args;
  ordered_args_map_t parsed_args;
  args_list_t extra_args;
  if (!ParseOrderedKeyValueArguments(parsed_args, extra_args, args,
                                     kArguments) ||
      extra_args.size() > 0) {
    PrintUsage(kArguments);
    return false;
  }

  std::string newkey, subj, config_path, key_file_path, keyout, out_path,
      outform, ext_section, digest_name;
  Password passin, passout;
  unsigned int days;
  bool help = false, new_flag = false, x509_flag = false, nodes = false;

  GetBoolArgument(&help, "-help", parsed_args);
  GetBoolArgument(&new_flag, "-new", parsed_args);
  GetBoolArgument(&x509_flag, "-x509", parsed_args);
  GetBoolArgument(&nodes, "-nodes", parsed_args);
  GetString(&newkey, "-newkey", "", parsed_args);
  GetUnsigned(&days, "-days", 30u, parsed_args);
  GetString(&subj, "-subj", "", parsed_args);
  GetString(&config_path, "-config", "", parsed_args);
  GetString(&key_file_path, "-key", "", parsed_args);
  GetString(&passin.get(), "-passin", "", parsed_args);
  GetString(&passout.get(), "-passout", "", parsed_args);
  GetString(&keyout, "-keyout", "", parsed_args);
  GetString(&out_path, "-out", "", parsed_args);
  GetString(&outform, "-outform", "PEM", parsed_args);
  GetString(&ext_section, "-extensions", "", parsed_args);
  GetExclusiveBoolArgument(&digest_name, kArguments, "", parsed_args);

  if (help) {
    PrintUsage(kArguments);
    return true;
  }

  if (!new_flag && !x509_flag && newkey.empty()) {
    fprintf(stderr,
            "Error: Missing required options, -x509, -new, or -newkey must be "
            "specified. \n");
    return false;
  }

  if (!newkey.empty() && !key_file_path.empty()) {
    fprintf(stderr,
            "Warning: Not generating key via given -newkey option since -key "
            "is given\n");
  }

  // Check -outform has a valid value
  if (!outform.empty()) {
    if (!isStringUpperCaseEqual(outform, "DER") &&
        !isStringUpperCaseEqual(outform, "PEM")) {
      fprintf(
          stderr,
          "Error: '-outform' option must specify a valid encoding DER|PEM\n");
      return false;
    }
  }

  bssl::UniquePtr<CONF> req_conf(nullptr);
  if (!config_path.empty() && !LoadConfig(config_path, req_conf)) {
    return false;
  }

  std::string req_section = REQ_SECTION;
  if (req_conf.get() &&
      NCONF_get_section(req_conf.get(), REQ_SECTION) == NULL) {
    req_section = "default";
  }

  if (ext_section.empty() && req_conf.get()) {
    const char *ext_str =
        NCONF_get_string(req_conf.get(), req_section.c_str(),
                         x509_flag ? REQ_V3_EXT_OPT : REQ_REQ_EXT_OPT);
    if (ext_str) {
      ext_section = ext_str;
    }
  }

  // Check syntax of extension section in config file
  if (!ext_section.empty() && !config_path.empty()) {
    X509V3_CTX temp_ctx;
    X509V3_set_ctx_test(&temp_ctx);
    X509V3_set_nconf(&temp_ctx, req_conf.get());
    if (!X509V3_EXT_add_nconf(req_conf.get(), &temp_ctx, ext_section.c_str(),
                              NULL)) {
      fprintf(stderr, "Error: Invalid extension section %s\n",
              ext_section.c_str());
      return false;
    }
  }

  const EVP_MD *digest = nullptr;
  if (digest_name.empty()) {
    if (!config_path.empty()) {
      const char *digest_str = NCONF_get_string(
          req_conf.get(), req_section.c_str(), REQ_DEFAULT_MD_OPT);
      if (digest_str) {
        digest_name = digest_str;
      } else {
        digest_name = "sha256";
      }
    } else {
      digest_name = "sha256";
    }
  } else {
    digest_name = digest_name.substr(1);
  }

  digest = EVP_get_digestbyname(digest_name.c_str());

  bool encrypt_key = true;
  const char *encrypt_key_str = NULL;
  if (req_conf.get()) {
    encrypt_key_str = NCONF_get_string(req_conf.get(), req_section.c_str(),
                                       REQ_ENCRYPT_KEY_OPT);
  }

  if (encrypt_key_str != NULL &&
      isStringUpperCaseEqual(encrypt_key_str, "no")) {
    encrypt_key = false;
  }

  // Set private key
  // - If sign key is provided: use that key
  // - If no sign key is provided:
  //   - Set default key size to 2048 bits or as provided in config file.
  //   - If -newkey is given: generate key specified by -newkey
  //   - Else: generate default RSA key
  bssl::UniquePtr<EVP_PKEY> pkey;
  if (!key_file_path.empty()) {
    if (!LoadPrivateKey(key_file_path, passin, pkey)) {
      return false;
    }
  } else {
    // Before generating key, check if config has a default key length specified
    long default_keylen = DEFAULT_KEY_LENGTH;
    const char *bits_str = NULL;
    if (req_conf.get()) {
      bits_str =
          NCONF_get_string(req_conf.get(), req_section.c_str(), REQ_BITS_OPT);
    }

    if (bits_str) {
      char *endptr = nullptr;
      errno = 0;
      long val = strtol(bits_str, &endptr, 10);
      if (*endptr == '\0' && endptr != bits_str && errno != ERANGE) {
        default_keylen = val;
      } else {
        fprintf(stderr,
                "Warning: Invalid RSA key length from config file: %s. The "
                "default key length is set to %d\n",
                bits_str, DEFAULT_KEY_LENGTH);
      }
    }

    std::string keyspec = "rsa";
    if (!newkey.empty()) {
      keyspec = newkey;
    }

    // Generate key
    pkey.reset(GenerateKey(keyspec.c_str(), default_keylen));

    if (!pkey) {
      fprintf(stderr, "Error: Failed to generate private key.\n");
      return false;
    }
  }

  // If keyout is not provided:
  // 1. If -config, use it to set keyout
  // 2. If no -config, output key to privkey.pem (this imitates how OpenSSL
  // would default to the default openssl.conf file, which has default_keyfile
  // set to privkey.pem)
  if (keyout.empty() && key_file_path.empty()) {
    if (req_conf) {
      const char *default_keyfile = NCONF_get_string(
          req_conf.get(), req_section.c_str(), REQ_DEFAULT_KEYFILE_OPT);
      keyout = default_keyfile != NULL ? default_keyfile : "";
    } else {
      keyout = "privkey.pem";
    }
  }

  if (!keyout.empty()) {
    const EVP_CIPHER *cipher = NULL;
    if (!nodes && encrypt_key) {
      cipher = EVP_des_ede3_cbc();
    }

    if (!WritePrivateKey(keyout, passout, pkey, cipher)) {
      return false;
    }
  }

  bool no_prompt = false;
  const char *no_prompt_str = NULL;
  if (req_conf.get()) {
    no_prompt_str =
        NCONF_get_string(req_conf.get(), req_section.c_str(), REQ_PROMPT_OPT);
  }

  if (no_prompt_str != NULL && isStringUpperCaseEqual(no_prompt_str, "no")) {
    no_prompt = true;
  }

  // At this point, one of -new -newkey or -x509 must be defined
  // Like OpenSSL, generate CSR first - then convert to cert if needed
  bssl::UniquePtr<X509_REQ> req(X509_REQ_new());
  bssl::UniquePtr<X509> cert(X509_new());

  // Always create a CSR first
  if (req == NULL ||
      !MakeCertificateRequest(req.get(), pkey.get(), subj, req_conf.get(),
                              req_section, !x509_flag, no_prompt)) {
    fprintf(stderr, "Failed to create certificate request\n");
    return false;
  }

  // Convert CSR to certificate
  if (x509_flag) {
    if (cert == NULL) {
      fprintf(stderr, "Failed to create X509 structure\n");
      return false;
    }

    if (!X509_set_version(cert.get(), X509_VERSION_3)) {
      fprintf(stderr, "Failed to set certificate version\n");
      return false;
    }

    // Generate random serial number
    if (!GenerateSerial(cert.get())) {
      fprintf(stderr, "Failed to generate serial number\n");
      return false;
    }

    // Set subject and issuer from CSR
    if (!X509_set_subject_name(cert.get(),
                               X509_REQ_get_subject_name(req.get())) ||
        !X509_set_issuer_name(cert.get(),
                              X509_REQ_get_subject_name(req.get()))) {
      fprintf(stderr, "Failed to set subject/issuer\n");
      return false;
    }

    // Set expiration to be 'days' days from now
    if (!X509_gmtime_adj(X509_getm_notBefore(cert.get()), 0)) {
      fprintf(stderr, "Failed to set notBefore field\n");
      return false;
    }
    if (!X509_time_adj_ex(X509_getm_notAfter(cert.get()), days, 0, NULL)) {
      fprintf(stderr, "Failed to set notAfter field\n");
      return false;
    }

    // Copy public key from CSR
    EVP_PKEY *tmppkey = X509_REQ_get0_pubkey(req.get());
    if (!tmppkey || !X509_set_pubkey(cert.get(), tmppkey)) {
      fprintf(stderr, "Failed to set public key\n");
      return false;
    }

    // Add extensions to certificate
    if (!AddCertExtensions(cert.get(), req_conf.get(), ext_section)) {
      fprintf(stderr, "Failed to add extensions to certificate\n");
      return false;
    }

    // Sign the certificate
    if (!X509_sign(cert.get(), pkey.get(), digest)) {
      fprintf(stderr, "Failed to sign certificate\n");
      return false;
    }
  } else {
    // Add extensions to request
    if (!AddReqExtensions(req.get(), req_conf.get(), ext_section)) {
      fprintf(stderr, "Failed to add extensions to CSR\n");
      return false;
    }

    // Sign the request
    if (!X509_REQ_sign(req.get(), pkey.get(), digest)) {
      return false;
    }
  }

  bssl::UniquePtr<BIO> out_bio;
  if (!out_path.empty()) {
    out_bio.reset(BIO_new(BIO_s_file()));
    if (!out_bio) {
      fprintf(stderr, "Error: unable to create file %s\n", out_path.c_str());
      return false;
    }
    if (1 != BIO_write_filename(out_bio.get(), out_path.c_str())) {
      fprintf(stderr, "Error: unable to write to '%s'\n", out_path.c_str());
      return false;
    }
  } else {
    // Default to stdout
    out_bio.reset(BIO_new_fp(stdout, BIO_NOCLOSE));
  }

  // Handle writing out.
  if (x509_flag) {
    if (isStringUpperCaseEqual(outform, "DER")) {
      if (!i2d_X509_bio(out_bio.get(), cert.get())) {
        fprintf(stderr, "Error: Failed to write certificate\n");
        return false;
      }
    } else {
      if (!PEM_write_bio_X509(out_bio.get(), cert.get())) {
        fprintf(stderr, "Error: Failed to write certificate\n");
        return false;
      }
    }
  } else {
    if (isStringUpperCaseEqual(outform, "DER")) {
      if (!i2d_X509_REQ_bio(out_bio.get(), req.get())) {
        fprintf(stderr, "Error: Failed to write certificate request\n");
        return false;
      }
    } else {
      if (!PEM_write_bio_X509_REQ(out_bio.get(), req.get())) {
        fprintf(stderr, "Error: Failed to write certificate request\n");
        return false;
      }
    }
  }

  return true;
}
