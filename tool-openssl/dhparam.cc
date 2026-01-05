// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/bio.h>
#include <openssl/bn.h>
#include <openssl/dh.h>
#include <openssl/pem.h>
#include <openssl/err.h>
#include "../tool/internal.h"
#include "internal.h"

static const argument_t kArguments[] = {
  { "-help", kBooleanArgument, "Display option summary" },
  { "-in", kOptionalArgument, "Input file, default stdin" },
  { "-out", kOptionalArgument, "Output file, default stdout" },
  { "-inform", kOptionalArgument, "Input format (PEM or DER), default PEM" },
  { "-outform", kOptionalArgument, "Output format (PEM or DER), default PEM" },
  { "-text", kBooleanArgument, "Print parameters in text form" },
  { "-noout", kBooleanArgument, "Do not output encoded parameters" },
  { "", kOptionalArgument, "" }
};

// Print DH parameters in text format
static bool PrintDHParamsText(BIO *out, const DH *dh) {
  const BIGNUM *p = DH_get0_p(dh);
  const BIGNUM *g = DH_get0_g(dh);

  if (!p || !g) {
    fprintf(stderr, "Error: Invalid DH parameters\n");
    return false;
  }

  int bits = BN_num_bits(p);
  BIO_printf(out, "DH Parameters: (%d bit)\n", bits);

  BIO_printf(out, "    P:   ");
  BN_print(out, p);
  BIO_printf(out, "\n");

  BIO_printf(out, "    G:   ");
  BN_print(out, g);
  BIO_printf(out, "\n");

  return true;
}

// Callback function for DH parameter generation progress.
// Displays progress indicators to stderr during parameter generation.
static int dh_progress_callback(int event, int n, BN_GENCB *cb) {
  switch (event) {
    case BN_GENCB_GENERATED:
      // Print a dot for each potential prime number generated
      fprintf(stderr, ".");
      fflush(stderr);
      break;
    case BN_GENCB_PRIME_TEST:
      if (n == -1) {
        // Trial division complete
        fprintf(stderr, "+");
      } else {
        // Each primality test
        fprintf(stderr, "*");
      }
      fflush(stderr);
      break;
    case 3:
      // Generation complete (special event for DH)
      fprintf(stderr, "\n");
      break;
  }
  return 1; // Continue generation
}

bool dhparamTool(const args_list_t &args) {
  using namespace ordered_args;
  ordered_args_map_t parsed_args;
  args_list_t extra_args;

  if (!ParseOrderedKeyValueArguments(parsed_args, extra_args, args, kArguments)) {
    PrintUsage(kArguments);
    return false;
  }

  if (HasArgument(parsed_args, "-help")) {
    PrintUsage(kArguments);
    return true;
  }

  bool ret = false;
  std::string in_path, out_path, inform_str, outform_str;
  bool text = false, noout = false;
  Format inform = FORMAT_PEM;
  Format outform = FORMAT_PEM;
  unsigned numbits = 0;
  bssl::UniquePtr<DH> dh;
  bssl::UniquePtr<BIO> in_bio;
  bssl::UniquePtr<BIO> out_bio;

  // Extract arguments
  GetString(&in_path, "-in", "", parsed_args);
  GetString(&out_path, "-out", "", parsed_args);
  GetString(&inform_str, "-inform", "", parsed_args);
  GetString(&outform_str, "-outform", "", parsed_args);
  GetBoolArgument(&text, "-text", parsed_args);
  GetBoolArgument(&noout, "-noout", parsed_args);

  // Check for numbits argument (positional argument for generation)
  if (!extra_args.empty()) {
    if (extra_args.size() > 1) {
      fprintf(stderr, "Error: Too many arguments\n");
      PrintUsage(kArguments);
      goto err;
    }

    const std::string &numbits_str = extra_args[0];
    if (!IsNumeric(numbits_str)) {
      fprintf(stderr, "Error: Invalid numbits argument: %s\n", numbits_str.c_str());
      goto err;
    }

    numbits = std::stoul(numbits_str);

    if (numbits < 512) {
      fprintf(stderr, "Error: Number of bits must be at least 512\n");
      goto err;
    }
  }

  // Parse input format
  if (!inform_str.empty()) {
    if (isStringUpperCaseEqual(inform_str, "DER")) {
      inform = FORMAT_DER;
    } else if (isStringUpperCaseEqual(inform_str, "PEM")) {
      inform = FORMAT_PEM;
    } else {
      fprintf(stderr, "Error: Invalid input format: %s\n", inform_str.c_str());
      goto err;
    }
  }

  // Parse output format
  if (!outform_str.empty()) {
    if (isStringUpperCaseEqual(outform_str, "DER")) {
      outform = FORMAT_DER;
    } else if (isStringUpperCaseEqual(outform_str, "PEM")) {
      outform = FORMAT_PEM;
    } else {
      fprintf(stderr, "Error: Invalid output format: %s\n", outform_str.c_str());
      goto err;
    }
  }

  // Generate or read parameters
  if (numbits > 0) {
    // Generate new DH parameters
    if (!in_path.empty()) {
      fprintf(stderr, "Error: Cannot specify both numbits and -in\n");
      goto err;
    }

    dh.reset(DH_new());
    if (!dh) {
      fprintf(stderr, "Error: Failed to create DH object\n");
      goto err;
    }

    // Generate parameters with generator 2 (most common)
    BN_GENCB cb;
    BN_GENCB_set(&cb, dh_progress_callback, nullptr);
    if (!DH_generate_parameters_ex(dh.get(), numbits, DH_GENERATOR_2, &cb)) {
      fprintf(stderr, "Error: Failed to generate DH parameters\n");
      goto err;
    }
  } else {
    // Read parameters from input
    if (in_path.empty()) {
      in_bio.reset(BIO_new_fp(stdin, BIO_NOCLOSE));
    } else {
      in_bio.reset(BIO_new_file(in_path.c_str(), inform == FORMAT_DER ? "rb" : "r"));
    }

    if (!in_bio) {
      fprintf(stderr, "Error: Failed to open input\n");
      goto err;
    }

    if (inform == FORMAT_PEM) {
      dh.reset(PEM_read_bio_DHparams(in_bio.get(), nullptr, nullptr, nullptr));
    } else {
      dh.reset(d2i_DHparams_bio(in_bio.get(), nullptr));
    }

    if (!dh) {
      fprintf(stderr, "Error: Failed to read DH parameters\n");
      goto err;
    }
  }

  // Set up output BIO
  if (text || !noout) {
    if (out_path.empty()) {
      out_bio.reset(BIO_new_fp(stdout, BIO_NOCLOSE));
    } else {
      out_bio.reset(BIO_new_file(out_path.c_str(), outform == FORMAT_DER ? "wb" : "w"));
    }

    if (!out_bio) {
      fprintf(stderr, "Error: Failed to open output\n");
      goto err;
    }
  }

  // Output text format if requested
  if (text) {
    if (!PrintDHParamsText(out_bio.get(), dh.get())) {
      goto err;
    }
  }

  // Output encoded format unless -noout is specified
  if (!noout) {
    if (outform == FORMAT_PEM) {
      if (!PEM_write_bio_DHparams(out_bio.get(), dh.get())) {
        fprintf(stderr, "Error: Failed to write DH parameters in PEM format\n");
        goto err;
      }
    } else {
      if (!i2d_DHparams_bio(out_bio.get(), dh.get())) {
        fprintf(stderr, "Error: Failed to write DH parameters in DER format\n");
        goto err;
      }
    }
  }

  ret = true;

err:
  if (!ret) {
    ERR_print_errors_fp(stderr);
  }
  return ret;
}
