# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0
#!/bin/bash

set -exuo pipefail

# -e: Exit on any failure
# -x: Print the command before running
# -u: Any variable that is not set will cause an error if used
# -o pipefail: Makes sure to exit a pipeline with a non-zero error code if any command in the pipeline exists with a
#              non-zero error code.

cp -r aws-lc-cryptofuzz/ linux-aarch/cryptofuzz_ubuntu-19.10_clang-9x_sanitizer/
cp -r aws-lc-cryptofuzz/ linux-x86/cryptofuzz_ubuntu-19.10_clang-9x_sanitizer/
cp -r aws-lc-cryptofuzz/ linux-x86/cryptofuzz_fedora-31_clang-9x/
cp -r aws-lc-cryptofuzz/ linux-x86/cryptofuzz_generate_corpus/
cp build_configs_install_deps.sh linux-aarch/cryptofuzz_ubuntu-19.10_clang-9x_sanitizer/
cp build_configs_install_deps.sh linux-x86/cryptofuzz_ubuntu-19.10_clang-9x_sanitizer/
cp build_configs_install_deps.sh linux-x86/cryptofuzz_fedora-31_clang-9x/
cp run_aws_lc_cryptofuzz.sh linux-aarch/cryptofuzz_ubuntu-19.10_clang-9x_sanitizer/
cp run_aws_lc_cryptofuzz.sh linux-x86/cryptofuzz_ubuntu-19.10_clang-9x_sanitizer/
cp run_aws_lc_cryptofuzz.sh linux-x86/cryptofuzz_fedora-31_clang-9x/
