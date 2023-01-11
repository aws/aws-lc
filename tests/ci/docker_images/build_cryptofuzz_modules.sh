#!/bin/bash
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
git clone --depth 1 https://github.com/guidovranken/cryptofuzz.git
cd cryptofuzz
git rev-parse HEAD
CRYPTOFUZZ_SRC=$(pwd)
python3 gen_repository.py

mkdir "$MODULES_ROOT"
cd "$MODULES_ROOT"

# Setup the other crypto libraries for differential fuzzing
# wolfCrypt https://github.com/guidovranken/cryptofuzz/blob/master/docs/wolfcrypt.md
export CFLAGS="$CFLAGS -DHAVE_AES_ECB -DWOLFSSL_DES_ECB -DHAVE_ECC_SECPR2 -DHAVE_ECC_SECPR3 -DHAVE_ECC_BRAINPOOL -DHAVE_ECC_KOBLITZ -DWOLFSSL_ECDSA_SET_K -DWOLFSSL_ECDSA_SET_K_ONE_LOOP"
git clone --depth 1 https://github.com/wolfSSL/wolfssl.git
cd wolfssl/
autoreconf -ivf
./configure --enable-static --enable-md2 --enable-md4 --enable-ripemd --enable-blake2 --enable-blake2s --enable-pwdbased --enable-scrypt --enable-hkdf --enable-cmac --enable-arc4 --enable-camellia --enable-aesccm --enable-aesctr --enable-xts --enable-des3 --enable-x963kdf --enable-harden --enable-aescfb --enable-aesofb --enable-aeskeywrap --enable-aessiv --enable-aesgcm-stream --enable-keygen --enable-curve25519 --enable-curve448 --enable-shake256 --enable-shake128 --disable-crypttests --disable-examples --enable-compkey --enable-ed448 --enable-ed25519 --enable-ecccustcurves --enable-xchacha --enable-siphash --enable-cryptocb --enable-eccencrypt --enable-smallstack --enable-ed25519-stream --enable-ed448-stream --enable-eccsi
make -j$(nproc)
export CXXFLAGS="$CXXFLAGS -DCRYPTOFUZZ_WOLFCRYPT"
env WOLFCRYPT_LIBWOLFSSL_A_PATH `realpath src/.libs/libwolfssl.a`
env WOLFCRYPT_INCLUDE_PATH `realpath .`
cd "${CRYPTOFUZZ_SRC}/modules/wolfcrypt/"
make -j$(nproc)

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

# Cryptofuzz builds its modules into $CRYPTOFUZZ_SRC/modules that includes everything it needs, deleting the module source
# code saves a substantial amount of space in the docker image
rm -rf "$MODULES_ROOT"

# Prebuild the required libcpu_features to save time
cd "$CRYPTOFUZZ_SRC"
make third_party/cpu_features/build/libcpu_features.a
