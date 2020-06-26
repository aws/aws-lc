include_directories(${INCLUDE_DIR})
include_directories(test_framework)

# Add minimal googletest targets. The provided one has many side-effects, and
# googletest has a very straightforward build.
add_library(awslc_gtest third_party/googletest/src/gtest-all.cc)
target_include_directories(awslc_gtest PRIVATE third_party/googletest)

include_directories(third_party/googletest/include)

add_subdirectory(test_framework)

include(test_sources.cmake)

# urandom_test is a separate binary because it needs to be able to observe the
# PRNG initialisation, which means that it can't have other tests running before
# it does.
add_executable(
  urandom_test

  rand/urandom_test.cc
)

add_executable(
  crypto_test

  aead/aead_test.cc
  aead/gcm_test.cc

  auth/cmac_test.cc
  auth/hmac_test.cc
  auth/poly1305_test.cc

  certs/x509_test.cc
  certs/x509_time_test.cc
  certs/v3name_test.cc
  certs/tab_test.cc

  cipher/aes_test.cc
  cipher/chacha_test.cc
  cipher/cipher_test.cc

  crypto-services/bio_test.cc
  crypto-services/buf_test.cc
  crypto-services/err_test.cc
  crypto-services/evp_extra_test.cc
  crypto-services/evp_test.cc
  crypto-services/obj_test.cc

  formats/asn1_test.cc
  formats/bytestring_test.cc
  formats/base64_test.cc
  formats/pem_test.cc
  formats/pkcs7_test.cc
  formats/pkcs8_test.cc
  formats/pkcs12_test.cc

  hash/digest_test.cc
  hash/md5_test.cc
  hash/sha_test.cc
  hash/siphash_test.cc

  kdf/hkdf_test.cc
  kex/dh_test.cc
  kex/ecdh_test.cc
  kex/x25519_test.cc

  math/bn_test.cc
  math/ec_test.cc
  math/p256-x86_64_test.cc

  pake/scrypt_test.cc
  pke/spake25519_test.cc
  pbkdf/pbkdf_test.cc

  rand/ctrdrbg_test.cc
  rand/rand_test.cc

  signature/dsa_test.cc
  signature/ecdsa_test.cc
  signature/ed25519_test.cc
  signature/rsa_test.cc

  test_framework/file_test_gtest.cc

  utils/abi_self_test.cc
  utils/compiler_test.cc
  utils/constant_time_test.cc
  utils/cpu-arm-linux_test.cc
  utils/impl_dispatch_test.cc
  utils/lhash_test.cc
  utils/pool_test.cc
  utils/refcount_test.cc
  utils/self_test.cc
  utils/stack_test.cc
  utils/thread_test.cc

  $<TARGET_OBJECTS:crypto_test_data>
  $<TARGET_OBJECTS:awslc_gtest_main>
)

add_executable(
  decrepit_test

  cipher/cfb_test.cc

  $<TARGET_OBJECTS:awslc_gtest_main>
)

add_dependencies(decrepit_test global_target)
add_dependencies(crypto_test global_target)
add_dependencies(urandom_test global_target)

target_link_libraries(crypto_test test_support_lib awslc_gtest crypto)
target_link_libraries(decrepit_test test_support_lib awslc_gtest decrepit
                      crypto)
target_link_libraries(urandom_test test_support_lib awslc_gtest crypto)

if(WIN32)
  target_link_libraries(crypto_test ws2_32)
  target_link_libraries(decrepit_test ws2_32)
endif()

add_dependencies(all_tests crypto_test)
add_dependencies(all_tests decrepit_test)
add_dependencies(all_tests urandom_test)
