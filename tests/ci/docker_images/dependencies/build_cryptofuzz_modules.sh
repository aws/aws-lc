#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC
set -exo pipefail

function env {
  export "$1"="$2"
  echo "export ${1}=\"${2}\"" >> "${FUZZ_ROOT}/fuzz_env.sh"
}
# Recommended flags from https://github.com/guidovranken/cryptofuzz/blob/master/docs/building.md
# Remove-fsanitize=undefined which doesn't fail the build but creates additional noise in build output
export CFLAGS="-fsanitize=address,fuzzer-no-link -O2 -g -Wno-gnu-designator"
export CXXFLAGS="-fsanitize=address,fuzzer-no-link -D_GLIBCXX_DEBUG -O2 -g"

# Setup base of Cryptofuzz
cd "$FUZZ_ROOT"
MODULES_ROOT="${FUZZ_ROOT}/modules"
# TODO this is not the latest (which is cryptofuzz-9461c91.tar.gz, but newer boton is not compiling so pinning)
curl -OL https://d2yr98kym3baw0.cloudfront.net/cryptofuzz-508c384.tar.gz
tar xvzf cryptofuzz-*.tar.gz
rm cryptofuzz-*.tar.gz
cd cryptofuzz
CRYPTOFUZZ_SRC=$(pwd)
python3 gen_repository.py

mkdir "$MODULES_ROOT"
cd "$MODULES_ROOT"

# Setup the other crypto libraries for differential fuzzing
# Botan https://github.com/guidovranken/cryptofuzz/blob/master/docs/botan.md
git clone https://github.com/randombit/botan.git
cd botan
# TODO: Current tip of botan is not compiling for us (maybe C++20 related?)
# reverting to the version of botan we built with cryptofuzz@508c384
git checkout 51b06ca93d1998d19927699f78b8d67539148dde
git rev-parse HEAD
python3 configure.py --cc-bin=$CXX --cc-abi-flags="${CXXFLAGS}" --disable-shared --disable-modules=locking_allocator,x509,tls --build-targets=static --without-documentation
make -j$(nproc)
env LIBBOTAN_A_PATH "$(realpath libbotan-3.a)"
env BOTAN_INCLUDE_PATH "$(realpath build/include)"
export CXXFLAGS="${CXXFLAGS} -DCRYPTOFUZZ_BOTAN"
cd "${CRYPTOFUZZ_SRC}/modules/botan/"
make -j$(nproc)

# Crypto++ https://github.com/guidovranken/cryptofuzz/blob/master/docs/cryptopp.md
cd "$MODULES_ROOT"
git clone --depth 1 https://github.com/weidai11/cryptopp.git
cd cryptopp/
git rev-parse HEAD
make libcryptopp.a -j$(nproc)
export CXXFLAGS="${CXXFLAGS} -DCRYPTOFUZZ_CRYPTOPP"
env LIBCRYPTOPP_A_PATH "$(realpath libcryptopp.a)"
env CRYPTOPP_INCLUDE_PATH "$(realpath .)"
cd "${CRYPTOFUZZ_SRC}/modules/cryptopp/"
make -j$(nproc)

# Extract the seed corpus, docker layers are already compressed so this won't use any more space and save time when running
cd "$FUZZ_ROOT"
unzip cryptofuzz_data.zip
rm cryptofuzz_data.zip
env CRYPTOFUZZ_SEED_CORPUS "$(realpath cryptofuzz_seed_corpus)"
env CRYPTOFUZZ_DICT "$(realpath cryptofuzz-dict.txt)"

# Save final common flags
env CFLAGS "$CFLAGS"
env CXXFLAGS "$CXXFLAGS"
env CRYPTOFUZZ_SRC "$CRYPTOFUZZ_SRC"

# Cryptofuzz builds its modules into $CRYPTOFUZZ_SRC/modules that includes everything it needs, deleting the module source
# code saves a substantial amount of space in the docker image
rm -rf "${MODULES_ROOT:?}"

# Prebuild the required libcpu_features to save time
cd "$CRYPTOFUZZ_SRC"
make third_party/cpu_features/build/libcpu_features.a
