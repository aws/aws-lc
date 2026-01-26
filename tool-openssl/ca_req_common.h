// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#ifndef TOOL_OPENSSL_CA_REQ_COMMON_H
#define TOOL_OPENSSL_CA_REQ_COMMON_H

#include <openssl/nid.h>

#include "internal.h"

#define REQ_SECTION "req"

#define REQ_PROMPT_OPT "prompt"
#define REQ_DN_OPT "distinguished_name"
#define REQ_BITS_OPT "default_bits"
#define REQ_DEFAULT_MD_OPT "default_md"
#define REQ_DEFAULT_KEYFILE_OPT "default_keyfile"
#define REQ_ENCRYPT_KEY_OPT "encrypt_key"
#define REQ_ATTRIBUTES_OPT "attributes"
#define REQ_V3_EXT_OPT "x509_extensions"
#define REQ_REQ_EXT_OPT "req_extensions"

typedef struct {
  const char *field_ln;
  const char *field_sn;
  const char *short_desc;
  const char *default_value;
  int nid;
} ReqField;

// Default values for subject fields
const ReqField subject_fields[] = {
    {"countryName", "C", "Country Name (2 letter code)", "AU", NID_countryName},
    {"stateOrProvinceName", "ST", "State or Province Name (full name)",
     "Some-State", NID_stateOrProvinceName},
    {"localityName", "L", "Locality Name (eg, city)", "", NID_localityName},
    {"organizationName", "O", "Organization Name (eg, company)",
     "Internet Widgits Pty Ltd", NID_organizationName},
    {"organizationalUnitName", "OU", "Organizational Unit Name (eg, section)",
     "", NID_organizationalUnitName},
    {"commonName", "CN", "Common Name (e.g. server FQDN or YOUR name)", "",
     NID_commonName},
    {"emailAddress", "emailAddress", "Email Address", "",
     NID_pkcs9_emailAddress}};

// Extra attributes for CSR
const ReqField extra_attributes[] = {
    {"challengePassword", "challengePassword", "A challenge password",
     "A challenge password", NID_pkcs9_challengePassword},
    {"unstructuredName", "unstructuredName", "An optional company name",
     "An optional company name", NID_pkcs9_unstructuredName}};

const char *PromptField(const ReqField &field, char *buffer,
                        size_t buffer_size);

bool LoadConfig(const std::string &config_path, bssl::UniquePtr<CONF> &conf);

bool parse_bool(const char *str, bool default_value);

bool LoadPrivateKey(const std::string &key_file_path,
                    Password &passin,
                    bssl::UniquePtr<EVP_PKEY> &pkey);

bssl::UniquePtr<X509_NAME> ParseSubjectName(std::string &subject_string);

#endif
