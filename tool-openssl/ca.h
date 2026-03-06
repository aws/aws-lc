// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#ifndef TOOL_OPENSSL_CA_H
#define TOOL_OPENSSL_CA_H

#include <openssl/base.h>
#include <openssl/mem.h>

#define CA_SECTION "ca"
#define CA_DEFAULT_CA_OPT "default_ca"

#define RANDFILE_OPT "RANDFILE"
#define DEFAULT_CA_OPT "default_ca"

#define CA_DATABASE_OPT "database"
#define CA_SERIAL_OPT "serial"
#define CA_RAND_SERIAL_OPT "rand_serial"
#define CA_PRIVATE_KEY_OPT "private_key"
#define CA_CERT_OPT "cert"
#define CA_NEW_CERTS_DIR_OPT "new_certs_dir"
#define CA_DFLT_MD_OPT "default_md"
#define CA_UNIQ_SUBJ_OPT "unique_subject"
#define CA_PRESERVE_OPT "preserve"
#define CA_POLICY_OPT "policy"
#define CA_X509_EXT_OPT "x509_extensions"
#define CA_COPY_EXT_OPT "copy_extensions"
#define CA_DFLT_STRTDT_OPT "default_startdate"
#define CA_DFLT_ENDDT_OPT "default_enddate"
#define CA_DAYS_OPT "days"
#define CA_NEW_CERTS_DIR_OPT "new_certs_dir"

typedef struct db_attr_st DB_ATTR;

typedef struct ca_db_st CA_DB;

enum EXT_COPY_TYPE { EXT_COPY_UNKNOWN, EXT_COPY_NONE, EXT_COPY_ADD, EXT_COPY_ALL };
enum DEF_DGST_USAGE { DEF_DGST_UNKNOWN, DEF_DGST_ADVISORY, DEF_DGST_REQUIRED };

void FreeIndex(CA_DB *db);

BSSL_NAMESPACE_BEGIN

BORINGSSL_MAKE_DELETER(CA_DB, FreeIndex);

BSSL_NAMESPACE_END

#endif
