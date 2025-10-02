// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/ec.h>
#include <openssl/pem.h>
#include <openssl/err.h>
#include <openssl/obj.h>
#include "../tool/internal.h"
#include "internal.h"

enum OutputFormat {
  FORMAT_PEM = 1,
  FORMAT_DER = 2
};

static bool ValidateECCurve(const std::string& curve_name, int* out_nid) {
    int nid = OBJ_sn2nid(curve_name.c_str());
    if (nid == NID_undef) {
        nid = EC_curve_nist2nid(curve_name.c_str());
    }

    if (nid == NID_undef) {
        fprintf(stderr, "unknown curve name (%s)\n", curve_name.c_str());

        size_t num_curves = EC_get_builtin_curves(nullptr, 0);
        std::vector<EC_builtin_curve> curves(num_curves);
        EC_get_builtin_curves(curves.data(), num_curves);

        fprintf(stderr, "Supported curves:\n");
        for (const auto& curve : curves) {
            const char* nist_name = EC_curve_nid2nist(curve.nid);
            const char* sn = OBJ_nid2sn(curve.nid);

            if (nist_name) {
                fprintf(stderr, "  %s (%s) - %s\n", sn, nist_name, curve.comment);
            } else {
                fprintf(stderr, "  %s - %s\n", sn, curve.comment);
            }
        }
        return false;
    }

    if (out_nid) {
        *out_nid = nid;
    }
    return true;
}

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
  point_conversion_form_t point_form = POINT_CONVERSION_UNCOMPRESSED;
  OutputFormat output_format = FORMAT_PEM;
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
      output_format = FORMAT_DER;
    } else if (isStringUpperCaseEqual(outform, "PEM")) {
      output_format = FORMAT_PEM;
    } else {
      fprintf(stderr, "Invalid output format: %s\n", outform.c_str());
      goto err;
    }
  }

  // Parse point conversion form
  if (!conv_form.empty()) {
    if (conv_form == "compressed") {
      point_form = POINT_CONVERSION_COMPRESSED;
    } else if (conv_form == "uncompressed") {
      point_form = POINT_CONVERSION_UNCOMPRESSED;
    } else {
      fprintf(stderr, "Invalid point conversion form: %s\n", conv_form.c_str());
      goto err;
    }
  }

  // Validate curve name and get NID
  if (!ValidateECCurve(curve_name, &nid)) {
    goto err;
  }

  group.reset(EC_GROUP_new_by_curve_name(nid));
  if (!group) {
    fprintf(stderr, "Failed to create EC group\n");
    goto err;
  }

  // Set up output BIO
  if (out_path.empty()) {
    out_bio.reset(BIO_new_fp(stdout, BIO_NOCLOSE));
  } else {
    out_bio.reset(BIO_new_file(out_path.c_str(), output_format == FORMAT_DER ? "wb" : "w"));
  }
  if (!out_bio) {
    fprintf(stderr, "Error opening output\n");
    goto err;
  }

  if (genkey) {
    // Generate EC key using direct EC_KEY API
    eckey.reset(EC_KEY_new_by_curve_name(nid));
    if (!eckey) {
      fprintf(stderr, "Failed to create EC key for curve\n");
      goto err;
    }
    
    if (!EC_KEY_generate_key(eckey.get())) {
      fprintf(stderr, "Failed to generate EC key\n");
      goto err;
    }
    
    // Set point conversion form on the key
    EC_KEY_set_conv_form(eckey.get(), point_form);
    
    if (!noout) {
      if (output_format == FORMAT_PEM) {
        if (!PEM_write_bio_ECPrivateKey(out_bio.get(), eckey.get(), nullptr, nullptr, 0, nullptr, nullptr)) {
          fprintf(stderr, "Failed to write private key in PEM format\n");
          goto err;
        }
      } else {
        if (!i2d_ECPrivateKey_bio(out_bio.get(), eckey.get())) {
          fprintf(stderr, "Failed to write private key in DER format\n");
          goto err;
        }
      }
    }
  } else if (!noout) {
    // Output parameters
    if (output_format == FORMAT_PEM) {
      if (!PEM_write_bio_ECPKParameters(out_bio.get(), group.get())) {
        fprintf(stderr, "Failed to write EC parameters in PEM format\n");
        goto err;
      }
    } else {
      if (!i2d_ECPKParameters_bio(out_bio.get(), group.get())) {
        fprintf(stderr, "Failed to write EC parameters in DER format\n");
        goto err;
      }
    }
  }

  ret = true;

err:
  ERR_print_errors_fp(stderr);
  return ret;
}
