#!/bin/bash

set -exuo pipefail

# -e: Exit on any failure
# -x: Print the command before running
# -u: Any variable that is not set will cause an error if used
# -o pipefail: Makes sure to exit a pipeline with a non-zero error code if any command in the pipeline exists with a
#              non-zero error code.

# Install aws cli
cd / 
curl "https://awscli.amazonaws.com/awscli-exe-linux-x86_64.zip" -o "awscliv2.zip" 
unzip -q awscliv2.zip 
./aws/install

# Generate some necessary headers for aws-lc-cryptofuzz
cd aws-lc-cryptofuzz/ 
python2 gen_repository.py

# Set environment variables so that cryptofuzz can find AWS-LC
export CXXFLAGS="$CXXFLAGS -DCRYPTOFUZZ_AWS_LC"
export OPENSSL_INCLUDE_PATH=/aws-lc/third_party/boringssl/include/
export OPENSSL_LIBCRYPTO_A_PATH=/aws-lc/build/third_party/boringssl/crypto/libcrypto.a
export CPATH=$CPATH:$OPENSSL_INCLUDE_PATH

# Build Botan
cd / 
git clone --depth 1 https://github.com/randombit/botan.git 
cd botan/ 
./configure.py --cc-bin=$CXX --cc-abi-flags="$CXXFLAGS" --disable-shared --disable-modules=locking_allocator 
make -j$(nproc)

# Set environment variables so that cryptofuzz can find Botan
export CXXFLAGS="$CXXFLAGS -DCRYPTOFUZZ_BOTAN"
export LIBBOTAN_A_PATH=/botan/libbotan-2.a
export BOTAN_INCLUDE_PATH=/botan/build/include
export CPATH=$CPATH:BOTAN_INCLUDE_PATH

# Build botan module within aws-lc-cryptofuzz
cd / 
cd aws-lc-cryptofuzz/modules/botan/ 
make

# Build Crypto++
cd / 
git clone --depth 1 https://github.com/weidai11/cryptopp/ 
cd cryptopp/ 
make -j$(nproc)

# Set environment variables so that aws-lc-cryptofuzz can find Crypto++
export CXXFLAGS="$CXXFLAGS -DCRYPTOFUZZ_CRYPTOPP"
export LIBCRYPTOPP_A_PATH=/cryptopp/libcryptopp.a
export CRYPTOPP_INCLUDE_PATH=/cryptopp/
export CPATH=$CPATH:$CRYPTOPP_INCLUDE_PATH

# Build Crypto++ module within aws-lc-cryptofuzz
cd / 
cd aws-lc-cryptofuzz/modules/cryptopp/ 
make

# Build WolfCrypt
cd / 
git clone --depth 1 https://github.com/wolfSSL/wolfssl.git 
cd wolfssl/ 
autoreconf -ivf 
./configure --enable-static --enable-md2 --enable-md4 --enable-ripemd --enable-blake2 --enable-blake2s --enable-pwdbased --enable-scrypt --enable-hkdf --enable-cmac --enable-arc4 --enable-camellia --enable-rabbit --enable-aesccm --enable-aesctr --enable-hc128 --enable-xts --enable-des3 --enable-idea --enable-x963kdf --enable-harden --enable-aescfb --enable-aesofb --enable-aeskeywrap 
make -j$(nproc)

# Set environment variables so that aws-lc-cryptofuzz can find WolfCrypt
export CXXFLAGS="$CXXFLAGS -DCRYPTOFUZZ_WOLFCRYPT"
export WOLFCRYPT_LIBWOLFSSL_A_PATH=/wolfssl/src/.libs/libwolfssl.a
export WOLFCRYPT_INCLUDE_PATH=/wolfssl/
export CPATH=$CPATH:WOLFCRYPT_INCLUDE_PATH

# Build WolfCrypt module within aws-lc-cryptofuzz
cd / 
cd aws-lc-cryptofuzz/modules/wolfcrypt/ 
make

# Build mbedTLS
cd / 
git clone --depth 1 https://github.com/ARMmbed/mbedtls.git 
cd mbedtls/ 
scripts/config.pl set MBEDTLS_PLATFORM_MEMORY 
scripts/config.pl set MBEDTLS_CMAC_C 
scripts/config.pl set MBEDTLS_NIST_KW_C 
scripts/config.pl set MBEDTLS_ARIA_C 
scripts/config.pl set MBEDTLS_MD2_C 
scripts/config.pl set MBEDTLS_MD4_C 
mkdir build/ 
cd build/ 
cmake .. -DENABLE_PROGRAMS=0 -DENABLE_TESTING=0 
make -j$(nproc)

# Set environment variables so that aws-lc-cryptofuzz can find mbedTLS
export MBEDTLS_LIBMBEDCRYPTO_A_PATH=/mbedtls/build/library/libmbedcrypto.a
export MBEDTLS_INCLUDE_PATH=/mbedtls/include
export CXXFLAGS="$CXXFLAGS -DCRYPTOFUZZ_MBEDTLS"
export CPATH=$CPATH:$MBEDTLS_INCLUDE_PATH

# Build mbedTLS module within aws-lc-cryptofuzz
cd / 
cd aws-lc-cryptofuzz/modules/mbedtls/ 
make

# Build libtomcrypt
cd / 
git clone --depth 1 https://github.com/libtom/libtomcrypt 
cd libtomcrypt 
make -j$(nproc)

# Set environment variables so that aws-lc-cryptofuzz can find libtomcrypt
export CXXFLAGS="$CXXFLAGS -DCRYPTOFUZZ_LIBTOMCRYPT"
export LIBTOMCRYPT_INCLUDE_PATH=/libtomcrypt/src/headers/
export LIBTOMCRYPT_A_PATH=/libtomcrypt/libtomcrypt.a
export CPATH=$CPATH:$LIBTOMCRYPT_INCLUDE_PATH

# Build libtomcrypt module within aws-lc-cryptofuzz
cd / 
cd aws-lc-cryptofuzz/modules/libtomcrypt/ 
make

# Build libgmp
cd / 
hg clone https://gmplib.org/repo/gmp/ libgmp/ 
cd libgmp 
autoreconf -ivf 
./configure --enable-maintainer-mode 
make -j$(nproc)

# Set environment variables so that aws-lc-cryptofuzz can find libgmp
export CXXFLAGS="$CXXFLAGS -DCRYPTOFUZZ_LIBGMP"
export LIBGMP_INCLUDE_PATH=/libgmp/
export LIBGMP_A_PATH=/libgmp/.libs/libgmp.a
export CPATH=$CPATH:$LIBGMP_INCLUDE_PATH

# Build libgmp module within aws-lc-cryptofuzz
cd / 
cd aws-lc-cryptofuzz/modules/libgmp/ 
make

# Build mpdecimal
cd /  
wget https://www.bytereef.org/software/mpdecimal/releases/mpdecimal-2.4.2.tar.gz 
tar zxvf mpdecimal-2.4.2.tar.gz 
cd mpdecimal-2.4.2/ 
./configure && make -j$(nproc)

# Set environment variables so that aws-lc-cryptofuzz can find mpdecimal
export CXXFLAGS="$CXXFLAGS -DCRYPTOFUZZ_MPDECIMAL"
export LIBMPDEC_A_PATH=/mpdecimal-2.4.2/libmpdec/libmpdec.a
export LIBMPDEC_INCLUDE_PATH=/mpdecimal-2.4.2/libmpdec/
export CPATH=$CPATH:$LIBMPDEC_INCLUDE_PATH

# Build mpdecimal module within aws-lc-cryptofuzz
cd / 
cd aws-lc-cryptofuzz/modules/mpdecimal/ 
make

# Build libsodium
cd / 
git clone --depth 1 https://github.com/jedisct1/libsodium.git 
cd libsodium/ 
autoreconf -ivf 
./configure 
make -j$(nproc)

# Set environment variables so that aws-lc-cryptofuzz can find libsodium
export CXXFLAGS="$CXXFLAGS -DCRYPTOFUZZ_LIBSODIUM"
export LIBSODIUM_A_PATH=/libsodium/src/libsodium/.libs/libsodium.a
export LIBSODIUM_INCLUDE_PATH=/libsodium/src/libsodium/include
export CPATH=$CPATH:$LIBSODIUM_INCLUDE_PATH

# Build libsodium module within aws-lc-cryptofuzz
cd / 
cd aws-lc-cryptofuzz/modules/libsodium/ 
make

# Build linux crypto api
cd / 
git clone --depth 1 https://github.com/smuellerDD/libkcapi.git 
cd libkcapi/ 
autoreconf -ivf 
./configure 
make -j$(nproc)

# Set environment variables so that aws-lc-cryptofuzz can find linux crypto api
export CXXFLAGS="$CXXFLAGS -DCRYPTOFUZZ_LINUX"
export LIBKCAPI_A_PATH=/libkcapi/.libs/libkcapi.a
export LIBKCAPI_INCLUDE_PATH=/libkcapi/lib
export CPATH=$CPATH:$LIBKCAPI_INCLUDE_PATH

# Build linux crypto api module within aws-lc-cryptofuzz
cd / 
cd aws-lc-cryptofuzz/modules/linux/ 
make

# Build SymCrypt
cd / 
git clone --depth 1 https://github.com/microsoft/SymCrypt.git 
cd SymCrypt/ 
sed -i "s/^add_subdirectory(unittest)$//g" CMakeLists.txt 
mkdir b/ 
cd b/ 
cmake ../ 
make -j$(nproc)

# Set environment variables so that aws-lc-cryptofuzz can find SymCrypt
export CXXFLAGS="$CXXFLAGS -DCRYPTOFUZZ_SYMCRYPT"
export SYMCRYPT_INCLUDE_PATH=/SymCrypt/inc/
export LIBSYMCRYPT_COMMON_A_PATH=/SymCrypt/b/lib/x86_64/Generic/libsymcrypt_common.a
export SYMCRYPT_GENERIC_A_PATH=/SymCrypt/b/lib/x86_64/Generic/symcrypt_generic.a
export CPATH=$CPATH:$LIBSYMCRYPT_INCLUDE_PATH

# Build SymCrypt module within aws-lc-cryptofuzz
cd / 
cd aws-lc-cryptofuzz/modules/symcrypt/ 
make

# Set fuzzer in environment variable
export LIBFUZZER_LINK="-fsanitize=fuzzer"

# Store all necessary environment variables for build aws-lc and running aws-lc-cryptofuzz
echo "export CXXFLAGS=${CXXFLAGS}" >> env.sh
echo "export CFLAGS=${CFLAGS}" >> env.sh
echo "export CPATH=${CPATH}" >> env.sh
echo "export OPENSSL_INCLUDE_PATH=${OPENSSL_INCLUDE_PATH}" >> env.sh
echo "export OPENSSL_LIBCRYPTO_A_PATH=${OPENSSL_LIBCRYPTO_A_PATH}" >> env.sh
echo "export LIBFUZZER_LINK=${LIBFUZZER_LINK}" >> env.sh
