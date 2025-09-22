// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/ec.h>
#include <openssl/pem.h>
#include <openssl/err.h>
#include <openssl/obj.h>
#include "../tool/internal.h"
#include "internal.h"

#define FORMAT_PEM 1
#define FORMAT_DER 2

static const argument_t kArguments[] = {
  { "-help", kBooleanArgument, "Display option summary" },
  { "-name", kOptionalArgument, "Use the ec parameters with specified 'short name'" },
  { "-out", kOptionalArgument, "Output file, default stdout" },
  { "-outform", kOptionalArgument, "Output format (PEM or DER), default PEM" },
  { "-conv_form", kOptionalArgument, "Point conversion form (compressed or uncompressed)" },
  { "-noout", kBooleanArgument, "Do not print the ec parameter" },
  { "-genkey", kBooleanArgument, "Generate ec key" },
  { "", kOptionalArgument, "" }
};

bool ecparamTool(const args_list_t &args) {
  using namespace ordered_args;
  ordered_args_map_t parsed_args;
  args_list_t extra_args;

  if (!ParseOrderedKeyValueArguments(parsed_args, extra_args, args, kArguments) ||
      extra_args.size() > 0) {
    PrintUsage(kArguments);
    return false;
  }

  if (HasArgument(parsed_args, "-help")) {
    PrintUsage(kArguments);
    return true;
  }

  bool ret = false;
  std::string curve_name, out_path, outform, conv_form;
  bool noout = false, genkey = false;
  point_conversion_form_t form = POINT_CONVERSION_UNCOMPRESSED;
  int outformat = FORMAT_PEM;
  int nid = NID_undef;
  bssl::UniquePtr<EC_GROUP> group;
  bssl::UniquePtr<EC_KEY> eckey;
  bssl::UniquePtr<BIO> out_bio;

  GetString(&curve_name, "-name", "", parsed_args);
  GetString(&out_path, "-out", "", parsed_args);
  GetString(&outform, "-outform", "", parsed_args);
  GetString(&conv_form, "-conv_form", "", parsed_args);
  GetBoolArgument(&noout, "-noout", parsed_args);
  GetBoolArgument(&genkey, "-genkey", parsed_args);

  if (curve_name.empty()) {
    fprintf(stderr, "No curve specified\n");
    goto err;
  }

  // Parse output format
  if (!outform.empty()) {
    if (isStringUpperCaseEqual(outform, "DER")) {
      outformat = FORMAT_DER;
    } else if (isStringUpperCaseEqual(outform, "PEM")) {
      outformat = FORMAT_PEM;
    } else {
      fprintf(stderr, "Invalid output format: %s\n", outform.c_str());
      goto err;
    }
  }

  // Parse point conversion form
  if (!conv_form.empty()) {
    if (conv_form == "compressed") {
      form = POINT_CONVERSION_COMPRESSED;
    } else if (conv_form == "uncompressed") {
      form = POINT_CONVERSION_UNCOMPRESSED;
    } else {
      fprintf(stderr, "Invalid point conversion form: %s\n", conv_form.c_str());
      goto err;
    }
  }

  // Get curve NID
  nid = OBJ_sn2nid(curve_name.c_str());
  if (nid == NID_undef) {
    nid = EC_curve_nist2nid(curve_name.c_str());
  }
  if (nid == NID_undef) {
    fprintf(stderr, "Unknown curve: %s\n", curve_name.c_str());
    goto err;
  }

  // Create EC group
  group.reset(EC_GROUP_new_by_curve_name(nid));
  if (!group) {
    fprintf(stderr, "Failed to create EC group\n");
    goto err;
  }

  // Set up output BIO
  if (out_path.empty()) {
    out_bio.reset(BIO_new_fp(stdout, BIO_NOCLOSE));
  } else {
    out_bio.reset(BIO_new_file(out_path.c_str(), outformat == FORMAT_DER ? "wb" : "w"));
  }
  if (!out_bio) {
    fprintf(stderr, "Error opening output\n");
    goto err;
  }

  if (genkey) {
    // Generate EC key using high-level EVP APIs
    bssl::UniquePtr<EVP_PKEY_CTX> ctx(EVP_PKEY_CTX_new_id(EVP_PKEY_EC, nullptr));
    if (!ctx) {
      goto err;
    }
    
    if (EVP_PKEY_keygen_init(ctx.get()) <= 0) {
      goto err;
    }
    
    if (EVP_PKEY_CTX_set_ec_paramgen_curve_nid(ctx.get(), nid) <= 0) {
      goto err;
    }
    
    bssl::UniquePtr<EVP_PKEY> pkey;
    EVP_PKEY* pkey_raw = nullptr;
    if (EVP_PKEY_keygen(ctx.get(), &pkey_raw) <= 0) {
      goto err;
    }
    pkey.reset(pkey_raw);
    
    // Get the EC_KEY for setting conversion form
    eckey.reset(EVP_PKEY_get1_EC_KEY(pkey.get()));
    if (!eckey) {
      goto err;
    }
    
    // Set point conversion form on the key
    EC_KEY_set_conv_form(eckey.get(), form);
    
    if (!noout) {
      if (outformat == FORMAT_PEM) {
        if (!PEM_write_bio_ECPrivateKey(out_bio.get(), eckey.get(), nullptr, nullptr, 0, nullptr, nullptr)) {
          goto err;
        }
      } else {
        if (!i2d_ECPrivateKey_bio(out_bio.get(), eckey.get())) {
          goto err;
        }
      }
    }
  } else {
    // Output parameters
    if (!noout) {
      if (outformat == FORMAT_PEM) {
        if (!PEM_write_bio_ECPKParameters(out_bio.get(), group.get())) {
          goto err;
        }
      } else {
        if (!i2d_ECPKParameters_bio(out_bio.get(), group.get())) {
          goto err;
        }
      }
    }
  }

  ret = true;

err:
  return ret;
}
