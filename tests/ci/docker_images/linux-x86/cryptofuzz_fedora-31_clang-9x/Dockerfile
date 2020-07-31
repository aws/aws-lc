# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

FROM fedora:31

SHELL ["/bin/bash", "-c"]

COPY . .

# Install dependencies
RUN dnf -y install \
    llvm \
    clang \
    compiler-rt \
    libunwind-devel \
    cmake \
    ninja-build \
    perl \
    golang \
    python2 \
    python \
    curl \
    zip \
    unzip \
    boost-devel \
    git \
    ca-certificates \
    --setopt=install_weak_deps=False --best && \
    dnf -y autoremove && \
    dnf clean all && \
    rm -rf /tmp/*

# Install aws cli
RUN curl "https://awscli.amazonaws.com/awscli-exe-linux-x86_64.zip" -o "awscliv2.zip" && \
    unzip -q awscliv2.zip && \
    ./aws/install

# Set environment variables for building
ENV CC=clang-9
ENV CXX=clang++-9
ENV CFLAGS="-fsanitize=address,undefined,fuzzer-no-link -O2 -g"
ENV CXXFLAGS="-fsanitize=address,undefined,fuzzer-no-link -D_GLIBCXX_DEBUG -O2 -g"

# Generate some necessary headers for aws-lc-cryptofuzz
RUN cd aws-lc-cryptofuzz/ && \
    python2 gen_repository.py

# Set environment variables so that cryptofuzz can find AWS-LC
ENV CXXFLAGS="$CXXFLAGS -DCRYPTOFUZZ_AWS_LC"
ENV OPENSSL_INCLUDE_PATH=/aws-lc/third_party/boringssl/include/
ENV OPENSSL_LIBCRYPTO_A_PATH=/aws-lc/third_party/boringssl/build/crypto/libcrypto.a
ENV CPATH=$CPATH:$OPENSSL_INCLUDE_PATH

# Build Botan
RUN git clone --depth 1 https://github.com/randombit/botan.git && \
    cd botan/ && \
    ./configure.py --cc-bin=$CXX --cc-abi-flags="$CXXFLAGS" --disable-shared --disable-modules=locking_allocator && \
    make -j$(nproc)

# Set environment variables so that cryptofuzz can find Botan
ENV CXXFLAGS="$CXXFLAGS -DCRYPTOFUZZ_BOTAN"
ENV LIBBOTAN_A_PATH=/botan/libbotan-2.a
ENV BOTAN_INCLUDE_PATH=/botan/build/include
ENV CPATH=$CPATH:BOTAN_INCLUDE_PATH

# Build botan module within aws-lc-cryptofuzz
RUN cd aws-lc-cryptofuzz/modules/botan/ && \
    make

# Build Crypto++
RUN git clone --depth 1 https://github.com/weidai11/cryptopp/ && \
    cd cryptopp/ && \
    make -j$(nproc)

# Set environment variables so that aws-lc-cryptofuzz can find Crypto++
ENV CXXFLAGS="$CXXFLAGS -DCRYPTOFUZZ_CRYPTOPP"
ENV LIBCRYPTOPP_A_PATH=/cryptopp/libcryptopp.a
ENV CRYPTOPP_INCLUDE_PATH=/cryptopp/
ENV CPATH=$CPATH:$CRYPTOPP_INCLUDE_PATH

# Build Crypto++ module within aws-lc-cryptofuzz
RUN cd aws-lc-cryptofuzz/modules/cryptopp/ && \
    make

RUN dnf -y install \
    libtool

# Build WolfCrypt
RUN git clone --depth 1 https://github.com/wolfSSL/wolfssl.git && \
    cd wolfssl/ && \
    autoreconf -ivf && \
    ./configure --enable-static --enable-md2 --enable-md4 --enable-ripemd --enable-blake2 --enable-blake2s --enable-pwdbased --enable-scrypt --enable-hkdf --enable-cmac --enable-arc4 --enable-camellia --enable-rabbit --enable-aesccm --enable-aesctr --enable-hc128 --enable-xts --enable-des3 --enable-idea --enable-x963kdf --enable-harden --enable-aescfb --enable-aesofb --enable-aeskeywrap && \
    make -j$(nproc)

# Set environment variables so that aws-lc-cryptofuzz can find WolfCrypt
ENV CXXFLAGS="$CXXFLAGS -DCRYPTOFUZZ_WOLFCRYPT"
ENV WOLFCRYPT_LIBWOLFSSL_A_PATH=/wolfssl/src/.libs/libwolfssl.a
ENV WOLFCRYPT_INCLUDE_PATH=/wolfssl/
ENV CPATH=$CPATH:WOLFCRYPT_INCLUDE_PATH

# Build WolfCrypt module within aws-lc-cryptofuzz
RUN cd aws-lc-cryptofuzz/modules/wolfcrypt/ && \
    make

# Build mbedTLS
RUN git clone --depth 1 https://github.com/ARMmbed/mbedtls.git && \
    cd mbedtls/ && \
    scripts/config.pl set MBEDTLS_PLATFORM_MEMORY && \
    scripts/config.pl set MBEDTLS_CMAC_C && \
    scripts/config.pl set MBEDTLS_NIST_KW_C && \
    scripts/config.pl set MBEDTLS_ARIA_C && \
    scripts/config.pl set MBEDTLS_MD2_C && \
    scripts/config.pl set MBEDTLS_MD4_C && \
    mkdir build/ && \
    cd build/ && \
    cmake .. -DENABLE_PROGRAMS=0 -DENABLE_TESTING=0 && \
    make -j$(nproc)

# Set environment variables so that aws-lc-cryptofuzz can find mbedTLS
ENV MBEDTLS_LIBMBEDCRYPTO_A_PATH=/mbedtls/build/library/libmbedcrypto.a
ENV MBEDTLS_INCLUDE_PATH=/mbedtls/include
ENV CXXFLAGS="$CXXFLAGS -DCRYPTOFUZZ_MBEDTLS"
ENV CPATH=$CPATH:$MBEDTLS_INCLUDE_PATH

# Build mbedTLS module within aws-lc-cryptofuzz
RUN cd aws-lc-cryptofuzz/modules/mbedtls/ && \
    make

# Build libtomcrypt
RUN git clone --depth 1 https://github.com/libtom/libtomcrypt && \
    cd libtomcrypt && \
    make -j$(nproc)

# Set environment variables so that aws-lc-cryptofuzz can find libtomcrypt
ENV CXXFLAGS="$CXXFLAGS -DCRYPTOFUZZ_LIBTOMCRYPT"
ENV LIBTOMCRYPT_INCLUDE_PATH=/libtomcrypt/src/headers/
ENV LIBTOMCRYPT_A_PATH=/libtomcrypt/libtomcrypt.a
ENV CPATH=$CPATH:$LIBTOMCRYPT_INCLUDE_PATH

# Build libtomcrypt module within aws-lc-cryptofuzz
RUN cd aws-lc-cryptofuzz/modules/libtomcrypt/ && \
    make

# Install a few more dependencies
RUN dnf -y install \
    mercurial \
    bison \
    flex \
    texinfo \
    wget

# Build libgmp
RUN hg clone https://gmplib.org/repo/gmp/ libgmp/ && \
    cd libgmp && \
    autoreconf -ivf && \
    ./configure --enable-maintainer-mode && \
    make -j$(nproc)

# Set environment variables so that aws-lc-cryptofuzz can find libgmp
ENV CXXFLAGS="$CXXFLAGS -DCRYPTOFUZZ_LIBGMP"
ENV LIBGMP_INCLUDE_PATH=/libgmp/
ENV LIBGMP_A_PATH=/libgmp/.libs/libgmp.a
ENV CPATH=$CPATH:$LIBGMP_INCLUDE_PATH

# Build libgmp module within aws-lc-cryptofuzz
RUN cd aws-lc-cryptofuzz/modules/libgmp/ && \
    make

# Build mpdecimal
RUN wget https://www.bytereef.org/software/mpdecimal/releases/mpdecimal-2.4.2.tar.gz && \
    tar zxvf mpdecimal-2.4.2.tar.gz && \
    cd mpdecimal-2.4.2/ && \
    ./configure && make -j$(nproc)

# Set environment variables so that aws-lc-cryptofuzz can find mpdecimal
ENV CXXFLAGS="$CXXFLAGS -DCRYPTOFUZZ_MPDECIMAL"
ENV LIBMPDEC_A_PATH=/mpdecimal-2.4.2/libmpdec/libmpdec.a
ENV LIBMPDEC_INCLUDE_PATH=/mpdecimal-2.4.2/libmpdec/
ENV CPATH=$CPATH:$LIBMPDEC_INCLUDE_PATH

# Build mpdecimal module within aws-lc-cryptofuzz
RUN cd aws-lc-cryptofuzz/modules/mpdecimal/ && \
    make

# Build libsodium
RUN git clone --depth 1 https://github.com/jedisct1/libsodium.git && \
    cd libsodium/ && \
    autoreconf -ivf && \
    ./configure && \
    make -j$(nproc)

# Set environment variables so that aws-lc-cryptofuzz can find libsodium
ENV CXXFLAGS="$CXXFLAGS -DCRYPTOFUZZ_LIBSODIUM"
ENV LIBSODIUM_A_PATH=/libsodium/src/libsodium/.libs/libsodium.a
ENV LIBSODIUM_INCLUDE_PATH=/libsodium/src/libsodium/include
ENV CPATH=$CPATH:$LIBSODIUM_INCLUDE_PATH

# Build libsodium module within aws-lc-cryptofuzz
RUN cd aws-lc-cryptofuzz/modules/libsodium/ && \
    make

# Build linux crypto api
RUN git clone --depth 1 https://github.com/smuellerDD/libkcapi.git && \
    cd libkcapi/ && \
    autoreconf -ivf && \
    ./configure && \
    make -j$(nproc)

# Set environment variables so that aws-lc-cryptofuzz can find linux crypto api
ENV CXXFLAGS="$CXXFLAGS -DCRYPTOFUZZ_LINUX"
ENV LIBKCAPI_A_PATH=/libkcapi/.libs/libkcapi.a
ENV LIBKCAPI_INCLUDE_PATH=/libkcapi/lib
ENV CPATH=$CPATH:$LIBKCAPI_INCLUDE_PATH

# Build linux crypto api module within aws-lc-cryptofuzz
RUN cd aws-lc-cryptofuzz/modules/linux/ && \
    make

# Build SymCrypt
RUN git clone --depth 1 https://github.com/microsoft/SymCrypt.git && \
    cd SymCrypt/ && \
    sed -i "s/^add_subdirectory(unittest)$//g" CMakeLists.txt && \
    mkdir b/ && \
    cd b/ && \
    cmake ../ && \
    make -j$(nproc)

# Set environment variables so that aws-lc-cryptofuzz can find SymCrypt
ENV CXXFLAGS="$CXXFLAGS -DCRYPTOFUZZ_SYMCRYPT"
ENV SYMCRYPT_INCLUDE_PATH=/SymCrypt/inc/
ENV LIBSYMCRYPT_COMMON_A_PATH=/SymCrypt/b/lib/x86_64/Generic/libsymcrypt_common.a
ENV SYMCRYPT_GENERIC_A_PATH=/SymCrypt/b/lib/x86_64/Generic/symcrypt_generic.a
ENV CPATH=$CPATH:$LIBSYMCRYPT_INCLUDE_PATH

# Build SymCrypt module within aws-lc-cryptofuzz
RUN cd aws-lc-cryptofuzz/modules/symcrypt/ && \
    make

# Set fuzzer in environment variable
ENV LIBFUZZER_LINK="-fsanitize=fuzzer"

CMD aws s3 cp s3://${GITHUB_CODE_BUCKET}/${REPO_OWNER}/${REPO_NAME}/${REPO_OWNER}_${REPO_NAME}.zip ./ && \
    unzip ${REPO_OWNER}_${REPO_NAME}.zip -d aws-lc && \
    cd / && \
    ls && \
    cd aws-lc/third_party/boringssl/ && \
    mkdir build/ && \
    cd build/ && \
    cmake -DCMAKE_CXX_FLAGS="$CXXFLAGS" -DCMAKE_C_FLAGS="$CFLAGS" -DBORINGSSL_ALLOW_CXX_RUNTIME=1 .. && \
    make crypto -j$(nproc) && \
    cd / && \
    cd aws-lc-cryptofuzz/modules/openssl/ && \
    make && \
    cd / && \
    chmod +x cryptofuzz.sh && \
    ./cryptofuzz.sh 
