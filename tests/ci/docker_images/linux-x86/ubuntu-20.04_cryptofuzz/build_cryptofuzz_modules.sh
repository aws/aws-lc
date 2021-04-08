#!/bin/bash
set -exo pipefail

function env {
  export "$1"="$2"
  echo "export ${1}=\"${2}\"" >> "${FUZZ_ROOT}/fuzz_env.sh"
}
# Recommended flags from https://github.com/guidovranken/cryptofuzz/blob/master/docs/building.md
export CFLAGS="-fsanitize=address,undefined,fuzzer-no-link -O2 -g"
export CXXFLAGS="-fsanitize=address,undefined,fuzzer-no-link -D_GLIBCXX_DEBUG -O2 -g"

# Setup base of Cryptofuzz
MODULES_ROOT="${FUZZ_ROOT}/modules"
git clone --depth 1 https://github.com/guidovranken/cryptofuzz.git
cd cryptofuzz
CRYPTOFUZZ_SRC=$(pwd)
python3 gen_repository.py

mkdir "$MODULES_ROOT"
cd "$MODULES_ROOT"

# Botan https://github.com/guidovranken/cryptofuzz/blob/master/docs/botan.md
git clone --depth 1 https://github.com/randombit/botan.git
cd botan
python3 configure.py --cc-bin=$CXX --cc-abi-flags="$CXXFLAGS" --disable-shared --disable-modules=locking_allocator,x509,tls --build-targets=static --without-documentation
make -j$(nproc)
export CXXFLAGS="$CXXFLAGS -DCRYPTOFUZZ_BOTAN"
env LIBBOTAN_A_PATH `realpath libbotan-3.a`
env BOTAN_INCLUDE_PATH `realpath build/include`
cd "${CRYPTOFUZZ_SRC}/modules/botan/"
make -j$(nproc)

# Crypto++ https://github.com/guidovranken/cryptofuzz/blob/master/docs/cryptopp.md
cd "$MODULES_ROOT"
git clone --depth 1 https://github.com/weidai11/cryptopp.git
cd cryptopp/
make libcryptopp.a -j$(nproc)
export CXXFLAGS="$CXXFLAGS -DCRYPTOFUZZ_CRYPTOPP"
env LIBCRYPTOPP_A_PATH `realpath libcryptopp.a`
env CRYPTOPP_INCLUDE_PATH `realpath .`
cd "${CRYPTOFUZZ_SRC}/modules/cryptopp/"
make


# Save final common flags
env CFLAGS "$CFLAGS"
env CXXFLAGS "$CXXFLAGS"
env CRYPTOFUZZ_SRC "$CRYPTOFUZZ_SRC"
