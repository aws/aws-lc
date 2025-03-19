// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/base.h>
#include <openssl/pem.h>
#include "internal.h"
#include "../tool/internal.h"
#include <openssl/evp.h>
#include <openssl/err.h>
#include <openssl/bio.h>
#include <openssl/rsa.h>
#include <string.h>
#include <stdio.h>

#define DEFAULT_KEY_LENGTH 2048
#define MIN_KEY_LENGTH 512
#define DEFAULT_CHAR_TYPE MBSTRING_ASC

// Notes: -x509 option assumes -new when -in is not passed in with OpenSSL. We do not support -in as of now, so -new
// is implied with -x509.
//
// In general, OpenSSL supports a default config file which it defaults to when user input is
// not provided. We do not support this interface. Therefore, -keyout defaults to privkey.pem when
// user input is not provided.
static const argument_t kArguments[] = {
  { "-help", kBooleanArgument, "Display option summary" },
  { "-new", kBooleanArgument, "Generates a new certificate request." \
                    "It will prompt the user for the relevant field values." \
                    "If the -newkey option is not given it will generate a new " \
                    "private key with 2048 bits length" },
  { "-newkey", kOptionalArgument, "This option is used to generate a new private " \
    				        "key. This option supports RSA keys in the format [rsa:]nbits. " \
     				        "If nbits is not given, i.e. -newkey rsa is specified, 2048 " \
           			    "bits length is used. This implies -new unless used with -x509." },
  { "-days", kOptionalArgument, "When -x509 is in use this specifies the number of " \
					          "days from today to certify the certificate for, otherwise it " \
     				        "is ignored. n should be a positive integer. The default is" \
     				        "30 days." },
  { "-nodes", kBooleanArgument, "If this option is specified then if a private " \
                    "key is created it will not be encrypted." },
  { "-x509", kBooleanArgument, "This option outputs a certificate instead of" \
                    "a certificate request. If the -newkey option is not given it " \
        			"will generate a new private key with 2048 bits length" },
  { "-subj", kOptionalArgument, "Sets subject name for new request. The arg must " \
                    "be formatted as /type0=value0/type1=value1/type2=.... " \
     				        "Keyword characters may be escaped by \\ (backslash), and " \
     				        "whitespace is retained." },
  { "-keyout", kOptionalArgument, "This specifies the output filename for the " \
                    " private key or writes to a file called privkey.pem in the current directory." },
  { "-out", kOptionalArgument, "This specifies the output filename to write to or " \
                    "standard output by default." },
  { "", kOptionalArgument, "" }
};


// Parse key specification string and generate key. Valid strings are in the format rsa:nbits.
// RSA key with 2048 bit length is used by default is |keyspec| is not valid.
static EVP_PKEY *generate_key(const char *keyspec) {
    EVP_PKEY_CTX *ctx = NULL;
    EVP_PKEY *pkey = NULL;
    long keylen = DEFAULT_KEY_LENGTH;
    int pkey_type = EVP_PKEY_RSA;

    // Parse keyspec
    if (strncasecmp(keyspec, "rsa:", 4) == 0) {
      keylen = atol(keyspec + 4);
    } else if (strcasecmp(keyspec, "rsa") == 0) {
	    keylen = DEFAULT_KEY_LENGTH;
    } else {
      fprintf(stderr, "Unknown key specification: %s, using RSA key with 2048 bit length\n", keyspec);
    }


    // Validate key length
    if (keylen < MIN_KEY_LENGTH) {
        fprintf(stderr, "Key length too short (minimum %d bits)\n", MIN_KEY_LENGTH);
        return NULL;
    }

    // Create key generation context
    ctx = EVP_PKEY_CTX_new_id(pkey_type, NULL);
    if (ctx == NULL) {
      return NULL;
    }

	if (EVP_PKEY_keygen_init(ctx) <= 0 || EVP_PKEY_CTX_set_rsa_keygen_bits(ctx, keylen) <= 0
        || EVP_PKEY_keygen(ctx, &pkey) <= 0) {
    	EVP_PKEY_CTX_free(ctx);
        return NULL;
    }

    EVP_PKEY_CTX_free(ctx);
    return pkey;
}

// Parse the subject string provided by a user with the -subj option.
X509_NAME* parse_subject_name(std::string &subject_string) {
  const char *subject_name_ptr = subject_string.c_str();

  if (*subject_name_ptr++ != '/') {
    fprintf(stderr, "name is expected to be in the format "
                    "/type0=value0/type1=value1/type2=... where characters may "
                    "be escaped by \\. This name is not in that format: '%s'\n",
                   --subject_name_ptr);
    return nullptr;
  }

  // Create new X509_NAME
  X509_NAME* name = X509_NAME_new();
  if (!name) {
    return nullptr;
  }

  std::string type;
  std::string value;

  while (*subject_name_ptr) {
    // Reset strings for new iteration
    type.clear();
    value.clear();

    // Parse type
    while (*subject_name_ptr && *subject_name_ptr != '=') {
      type += *subject_name_ptr++;
    }

    if (!*subject_name_ptr) {
      fprintf(stderr, "Hit end of string before finding the equals.\n");
      X509_NAME_free(name);
      return nullptr;
    }

    // Skip '='
    subject_name_ptr++;

    // Parse value
    while (*subject_name_ptr && *subject_name_ptr != '/') {
      if (*subject_name_ptr == '\\' && *(subject_name_ptr + 1)) {
        // Handle escaped character
        subject_name_ptr++;
        value += *subject_name_ptr++;
      } else {
        value += *subject_name_ptr++;
      }
    }

    // Skip trailing '/' if present
    if (*subject_name_ptr == '/') {
      subject_name_ptr++;
    }

    // Convert type to NID, skip unknown attributes
    int nid = OBJ_txt2nid(type.c_str());
    if (nid == NID_undef) {
      fprintf(stderr, "Warning: Skipping unknown attribute \"%s\"\n", type.c_str());
      // Skip unknown attributes
      continue;
    }

    // Skip empty values
    if (value.empty()) {
      fprintf(stderr, "Warning: No value specified for attribute \"%s\", Skipped\n", type.c_str());
      continue;
    }

    // Add entry to the name
    if (!X509_NAME_add_entry_by_NID(name, nid, DEFAULT_CHAR_TYPE,
                                   (unsigned char*)value.c_str(),
                                   -1, -1, 0)) {
      OPENSSL_PUT_ERROR(X509, ERR_R_X509_LIB);
      X509_NAME_free(name);
      return nullptr;
    }
  }

  return name;
}

X509_NAME *prompt_for_subject(X509_REQ* req, bool isCSR, unsigned long chtype = MBSTRING_ASC) {
  // Default values for subject fields
  const struct {
    const char* field_name;
    const char* short_desc;
    const char* default_value;
    int nid;
  } subject_fields[] = {
    {"countryName", "Country Name (2 letter code)", "AU", NID_countryName},
    {"stateOrProvinceName", "State or Province Name (full name)", "Some-State", NID_stateOrProvinceName},
    {"localityName", "Locality Name (eg, city)", "", NID_localityName},
    {"organizationName", "Organization Name (eg, company)", "Internet Widgits Pty Ltd", NID_organizationName},
    {"organizationalUnitName", "Organizational Unit Name (eg, section)", "", NID_organizationalUnitName},
    {"commonName", "Common Name (e.g. server FQDN or YOUR name)", "", NID_commonName},
    {"emailAddress", "Email Address", "", NID_pkcs9_emailAddress}
  };

  // Extra attributes for CSR
  const struct {
    const char* field_name;
    const char* short_desc;
    const char* default_value;
    int nid;
  } extra_attributes[] = {
    {"challengePassword", "A challenge password", "", NID_pkcs9_challengePassword},
    {"unstructuredName", "An optional company name", "", NID_pkcs9_unstructuredName}
  };

  // Get the subject name from the request
  X509_NAME* subj = X509_NAME_new();
  if (!subj) {
    fprintf(stderr, "Error getting subject name from request\n");
    return NULL;
  }

  // Print the instructions
  fprintf(stdout, "You are about to be asked to enter information that will be incorporated\n");
  fprintf(stdout, "into your certificate request.\n");
  fprintf(stdout, "What you are about to enter is what is called a Distinguished Name or a DN.\n");
  fprintf(stdout, "There are quite a few fields but you can leave some blank\n");
  fprintf(stdout, "For some fields there will be a default value,\n");
  fprintf(stdout, "If you enter '.', the field will be left blank.\n");
  fprintf(stdout, "\n");

  char buffer[1024];

  // Process each subject field
  for (const auto& field : subject_fields) {
    // Prompt with default value if available
    if (field.default_value && field.default_value[0]) {
      fprintf(stdout, "%s [%s]: ", field.short_desc, field.default_value);
    } else {
      fprintf(stdout, "%s: ", field.short_desc);
    }
    fflush(stdout);

    // Get input with fgets
    if (fgets(buffer, sizeof(buffer), stdin) == NULL) {
      X509_NAME_free(subj);
      fprintf(stderr, "Error reading input\n");
      return NULL;
    }

    // Remove newline character if present
    size_t len = strlen(buffer);
    if (len > 0 && buffer[len - 1] == '\n') {
      buffer[len - 1] = '\0';
      len--;
    }

    // Process input
    const char* value = nullptr;
    if (strcmp(buffer, ".") == 0) {
      // Empty entry requested
      value = "";
    } else if (len == 0 && field.default_value) {
      // Use default value
      value = field.default_value;
    } else if (len > 0) {
      // Use provided input
      value = buffer;
    } else {
      // Empty input and no default - use empty string
      value = "";
    }

    // Only add non-empty values
    if (value && value[0]) {
      if (!X509_NAME_add_entry_by_NID(subj, field.nid, chtype,
                                     reinterpret_cast<const unsigned char*>(value),
                                     -1, -1, 0)) {
        X509_NAME_free(subj);
        fprintf(stderr, "Error adding %s to subject\n", field.field_name);
        return NULL;
      }
    }
  }

  // If this is a CSR, handle extra attributes
  if (isCSR) {
    fprintf(stdout, "\nPlease enter the following 'extra' attributes\n");
    fprintf(stdout, "to be sent with your certificate request\n");

    // Process each extra attribute
    for (const auto& attr : extra_attributes) {
      // Prompt with default value if available
      if (attr.default_value && attr.default_value[0]) {
        fprintf(stdout, "%s [%s]: ", attr.short_desc, attr.default_value);
      } else {
        fprintf(stdout, "%s: ", attr.short_desc);
      }
      fflush(stdout);

      // Get input with fgets
      if (fgets(buffer, sizeof(buffer), stdin) == NULL) {
        fprintf(stderr, "Error reading input\n");
        return NULL;
      }

      // Remove newline character if present
      size_t len = strlen(buffer);
      if (len > 0 && buffer[len - 1] == '\n') {
        buffer[len - 1] = '\0';
        len--;
      }

      // Process input
      const char* value = nullptr;
      if (strcmp(buffer, ".") == 0) {
        // Empty entry requested
        value = "";
      } else if (len == 0 && attr.default_value) {
        // Use default value
        value = attr.default_value;
      } else if (len > 0) {
        // Use provided input
        value = buffer;
      } else {
        // Empty input and no default - use empty string
        value = "";
      }

      // Only add non-empty attributes
      if (value && value[0]) {
        X509_ATTRIBUTE* x509_attr = X509_ATTRIBUTE_create_by_NID(nullptr,
                                                               attr.nid,
                                                               MBSTRING_ASC,
                                                               reinterpret_cast<const unsigned char*>(value),
                                                               -1);
        if (!x509_attr) {
          fprintf(stderr, "Error creating attribute %s\n", attr.field_name);
          return NULL;
        }

        if (!X509_REQ_add1_attr(req, x509_attr)) {
          fprintf(stderr, "Error adding attribute %s to request\n", attr.field_name);
          X509_ATTRIBUTE_free(x509_attr);
          return NULL;
        }

        X509_ATTRIBUTE_free(x509_attr);
      }
    }
  }

  return subj;
}

static int make_certificate_request(X509_REQ *req, EVP_PKEY *pkey, std::string &subject_name, bool isCSR) {
  X509_NAME *name;

  // Set version
  if (!X509_REQ_set_version(req, 0L))  // version 1
    return 0;

  if (subject_name.empty()) {// Prompt the user
    name = prompt_for_subject(req, isCSR);
  } else { // Parse user provided string
    name = parse_subject_name(subject_name);
    if (!name) {
      return 0;
    }
  }

  if (!X509_REQ_set_subject_name(req, name)) {
    X509_NAME_free(name);
    return 0;
  }
  X509_NAME_free(name);

  if (!X509_REQ_set_pubkey(req, pkey)) {
    return 0;
  }

  return 1;
}

static int req_password_callback(char *buf, int size, int rwflag, void *userdata) {
  const char *prompt = "Enter PEM pass phrase:";
  char verify_buf[1024];
  int len;

  // Display prompt
  fprintf(stderr, "%s", prompt);
  fflush(stderr);

  // Get password
  if (fgets(buf, size, stdin) == NULL) {
    fprintf(stderr, "Error reading password\n");
    return 0;
  }

  // Remove trailing newline
  len = strlen(buf);
  if (len > 0 && buf[len-1] == '\n')
    buf[--len] = '\0';

  // For encryption only (which is the case for req tool)
  if (rwflag) {
    // Verify password
    fprintf(stderr, "Verifying - %s", prompt);
    fflush(stderr);

    if (fgets(verify_buf, sizeof(verify_buf), stdin) == NULL) {
      fprintf(stderr, "Error reading verification password\n");
      return 0;
    }

    // Remove trailing newline
    int verify_len = strlen(verify_buf);
    if (verify_len > 0 && verify_buf[verify_len-1] == '\n')
      verify_buf[--verify_len] = '\0';

    // Check if passwords match
    if (strcmp(buf, verify_buf) != 0) {
      fprintf(stderr, "Passwords don't match\n");
      return 0;
    }

    // Enforce minimum length
    if (len < 4) {
      fprintf(stderr, "Password too short (minimum 4 characters)\n");
      return 0;
    }
  }

  return len;
}

// Default extensions used in OpenSSL
bool create_config(CONF **conf_out, BIO **bio_out) {
    // Create in-memory configuration string
    const char *config =
        "[v3_ca]\n"
        "subjectKeyIdentifier=hash\n"
        "authorityKeyIdentifier=keyid:always,issuer:always\n"
        "basicConstraints=critical,CA:true\n";

    // Create a BIO for the config
    BIO *bio = BIO_new_mem_buf(config, -1);
    if (!bio) {
        fprintf(stderr, "Failed to create memory BIO\n");
        return false;
    }

    CONF *conf = NCONF_new(NULL);
    if (!conf) {
        BIO_free(bio);
        fprintf(stderr, "Failed to create CONF structure\n");
        return false;
    }

    if (NCONF_load_bio(conf, bio, NULL) <= 0) {
        BIO_free(bio);
        NCONF_free(conf);
        fprintf(stderr, "Failed to load config from BIO\n");
        return false;
    }

    *conf_out = conf;
    *bio_out = bio;
    return true;
}

// Function to add extensions to a certificate
bool add_cert_extensions(X509 *cert) {
    CONF *conf = NULL;
    BIO *bio = NULL;

    if (!create_config(&conf, &bio)) {
        return false;
    }

    // Set up X509V3 context for certificate
    X509V3_CTX ctx;
    X509V3_set_ctx_nodb(&ctx);
    X509V3_set_ctx(&ctx, cert, cert, NULL, NULL, 0);  // Self-signed: cert is both issuer and subject
    X509V3_set_nconf(&ctx, conf);

    // Add extensions from config to the certificate
    bool result = X509V3_EXT_add_nconf(conf, &ctx, "v3_ca", cert) != 0;

    // Clean up
    NCONF_free(conf);
    BIO_free(bio);

    if (!result) {
        fprintf(stderr, "Failed to add extensions to certificate\n");
    }

    return result;
}

// Function to add extensions to a CSR
bool add_csr_extensions(X509_REQ *req) {
    CONF *conf = NULL;
    BIO *bio = NULL;

    if (!create_config(&conf, &bio)) {
        return false;
    }

    // Set up X509V3 context for CSR
    X509V3_CTX ctx;
    X509V3_set_ctx_nodb(&ctx);
    X509V3_set_ctx(&ctx, NULL, NULL, req, NULL, 0);  // CSR doesn't have issuer/subject certs
    X509V3_set_nconf(&ctx, conf);

    // Add extensions from config to the CSR
    bool result = X509V3_EXT_REQ_add_nconf(conf, &ctx, "v3_ca", req) != 0;

    // Clean up
    NCONF_free(conf);
    BIO_free(bio);

    if (!result) {
        fprintf(stderr, "Failed to add extensions to CSR\n");
    }

    return result;
}

// Generate a random serial number for a certificate
bool generate_serial(X509 *cert) {
  // Create a new BIGNUM to hold the random value
  bssl::UniquePtr<BIGNUM> bn(BN_new());
  if (!bn) {
    fprintf(stderr, "Failed to create BIGNUM for serial\n");
    return false;
  }

  // Generate random number with 159 bits (same as OpenSSL's SERIAL_RAND_BITS)
  constexpr int SERIAL_RAND_BITS = 159;
  if (!BN_rand(bn.get(), SERIAL_RAND_BITS, BN_RAND_TOP_ANY, BN_RAND_BOTTOM_ANY)) {
    fprintf(stderr, "Failed to generate random serial number\n");
    return false;
  }

  // Get a pointer to the certificate's ASN1_INTEGER serial number field
  ASN1_INTEGER *serial = X509_get_serialNumber(cert);
  if (!serial) {
    fprintf(stderr, "Failed to get certificate serial number field\n");
    return false;
  }

  // Convert BIGNUM to ASN1_INTEGER and set it as the certificate's serial number
  if (!BN_to_ASN1_INTEGER(bn.get(), serial)) {
    fprintf(stderr, "Failed to convert BIGNUM to ASN1_INTEGER\n");
    return false;
  }

  return true;
}

bool reqTool(const args_list_t &args) {
  args_map_t parsed_args;
  args_list_t extra_args;
  if (!ParseKeyValueArguments(parsed_args, extra_args, args, kArguments) ||
      extra_args.size() > 0) {
    PrintUsage(kArguments);
    return false;
  }

  std::string newkey, subj, keyout, out;
  unsigned int days;
  bool help = false, new_flag = false, x509_flag = false, nodes = false;

  GetBoolArgument(&help, "-help", parsed_args);
  GetBoolArgument(&new_flag, "-new", parsed_args);
  GetBoolArgument(&x509_flag, "-x509", parsed_args);
  GetBoolArgument(&nodes, "-nodes", parsed_args);

  GetString(&newkey, "-newkey", "", parsed_args);
  GetUnsigned(&days, "-days", 30u, parsed_args);
  GetString(&subj, "-subj", "", parsed_args);
  GetString(&keyout, "-keyout", "" , parsed_args);
  GetString(&out, "-out", "" , parsed_args);

  if (help) {
    PrintUsage(kArguments);
    return false;
  }

  if (!new_flag && !x509_flag && newkey.empty()) {
    fprintf(stderr, "Error: Missing required options, -x509, -new, or -newkey must be specified. \n");
    return false;
  }

  std::string keyspec = "rsa:2048";
  if (!newkey.empty()) {
	keyspec = newkey;
  }

  bssl::UniquePtr<EVP_PKEY> pkey(generate_key(keyspec.c_str()));
  if (!pkey) {
    fprintf(stderr, "Error: Failed to generate private key.\n");
    return false;
  }

  // Generate and write private key
  EVP_CIPHER *cipher = NULL;
  if (!nodes) {
	cipher = (EVP_CIPHER*)EVP_des_ede3_cbc();
  }

  bssl::UniquePtr<BIO> out_bio;
  if (!keyout.empty()) {
    fprintf(stderr, "Writing private key to %s\n", keyout.c_str());
    out_bio.reset(BIO_new_file(keyout.c_str(), "w"));
  } else {
    // Default to privkey.pem in the current directory
    const char* default_keyfile = "privkey.pem";
    fprintf(stderr, "Writing private key to %s (default)\n", default_keyfile);
    out_bio.reset(BIO_new_file(default_keyfile, "w"));
  }

  // If encryption disabled, don't use password prompting callback
  if (!out_bio || !PEM_write_bio_PrivateKey(out_bio.get(), pkey.get(), cipher, NULL, 0,
                                            cipher ? req_password_callback : NULL, NULL)) {
	  fprintf(stderr, "Failed to write private key.\n");
    return false;
  }

  // At this point, one of -new -newkey or -x509 must be defined
  // Like OpenSSL, generate CSR first - then convert to cert if needed
  bssl::UniquePtr<X509_REQ> req(X509_REQ_new());
  bssl::UniquePtr<X509> cert(X509_new());
  int ret = 0;

  // Always create a CSR first
  if (req == NULL || !make_certificate_request(req.get(), pkey.get(), subj, !x509_flag)) {
    fprintf(stderr, "Failed to create certificate request\n");
    return false;
  }


  // Convert CSR to certificate
  if (x509_flag) {
    if (cert == NULL) {
      fprintf(stderr, "Failed to create X509 structure\n");
      return false;
    }
    // Set version
    if (!X509_set_version(cert.get(), 2)) {
      fprintf(stderr, "Failed to set certificate version\n");
      return false;
    }

    // Generate random serial number
    if (!generate_serial(cert.get())) {
      fprintf(stderr, "Failed to generate serial number\n");
      return false;
    }

    // Set subject and issuer from CSR
    if (!X509_set_subject_name(cert.get(), X509_REQ_get_subject_name(req.get())) ||
        !X509_set_issuer_name(cert.get(), X509_REQ_get_subject_name(req.get()))) {
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
    if (!add_cert_extensions(cert.get())) {
      fprintf(stderr, "Failed to add extensions to certificate\n");
      return false;
    }

    // Sign the certificate
    if (!X509_sign(cert.get(), pkey.get(), EVP_sha256())) {
      fprintf(stderr, "Failed to sign certificate\n");
      return false;
    }
  } else {
    // Add extensions to certificate
    if (!add_csr_extensions(req.get())) {
      fprintf(stderr, "Failed to add extensions to certificate\n");
      return false;
    }

    // Sign the request
	  if (!X509_REQ_sign(req.get(), pkey.get(), EVP_sha256())) {
  	  return 0;
 	  }
  }

  // Handle writing out.


  return true;
}
