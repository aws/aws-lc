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
cd "$FUZZ_ROOT"
MODULES_ROOT="${FUZZ_ROOT}/modules"
git clone --depth 1 https://github.com/guidovranken/cryptofuzz.git
cd cryptofuzz
git rev-parse HEAD
CRYPTOFUZZ_SRC=$(pwd)
python3 gen_repository.py

mkdir "$MODULES_ROOT"
cd "$MODULES_ROOT"

# Setup the other crypto libraries for differential fuzzing
# Botan https://github.com/guidovranken/cryptofuzz/blob/master/docs/botan.md
git clone --depth 1 https://github.com/randombit/botan.git
cd botan
git rev-parse HEAD
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
git rev-parse HEAD
make libcryptopp.a -j$(nproc)
export CXXFLAGS="$CXXFLAGS -DCRYPTOFUZZ_CRYPTOPP"
env LIBCRYPTOPP_A_PATH `realpath libcryptopp.a`
env CRYPTOPP_INCLUDE_PATH `realpath .`
cd "${CRYPTOFUZZ_SRC}/modules/cryptopp/"
make

# Extract the seed corpus, docker layers are already compressed so this won't use any more space and save time when running
cd "$FUZZ_ROOT"
unzip cryptofuzz_data.zip
rm cryptofuzz_data.zip
env CRYPTOFUZZ_SEED_CORPUS `realpath cryptofuzz_seed_corpus`
env CRYPTOFUZZ_DICT `realpath cryptofuzz-dict.txt`

# Save final common flags
env CFLAGS "$CFLAGS"
env CXXFLAGS "$CXXFLAGS"
env CRYPTOFUZZ_SRC "$CRYPTOFUZZ_SRC"

# Cryptofuzz builds it's modules into $CRYPTOFUZZ_SRC/modules that includes everything it needs, this saves a substantial amount of space
rm -rf "$MODULES_ROOT"