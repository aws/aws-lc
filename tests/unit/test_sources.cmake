#########################################################################
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0
# The license is detailed in the file LICENSE.md, and applies to this file.
###########################################################################

set(WYCHEPROOF_DIR third_party/wycheproof_testvectors)

set(
  CRYPTO_TEST_DATA

  aead/aes_128_cbc_sha1_tls_implicit_iv_tests.txt
  aead/aes_128_cbc_sha1_tls_tests.txt
  aead/aes_128_cbc_sha256_tls_tests.txt
  aead/aes_128_ccm_bluetooth_tests.txt
  aead/aes_128_ccm_bluetooth_8_tests.txt
  aead/aes_128_ctr_hmac_sha256.txt
  aead/aes_128_gcm_siv_tests.txt
  aead/aes_128_gcm_tests.txt
  aead/aes_192_gcm_tests.txt
  aead/aes_256_cbc_sha1_tls_implicit_iv_tests.txt
  aead/aes_256_cbc_sha1_tls_tests.txt
  aead/aes_256_cbc_sha256_tls_tests.txt
  aead/aes_256_cbc_sha384_tls_tests.txt
  aead/aes_256_ctr_hmac_sha256.txt
  aead/aes_256_gcm_siv_tests.txt
  aead/aes_256_gcm_tests.txt
  aead/chacha20_poly1305_tests.txt
  aead/des_ede3_cbc_sha1_tls_implicit_iv_tests.txt
  aead/des_ede3_cbc_sha1_tls_tests.txt
  aead/gcm_tests.txt
  aead/xchacha20_poly1305_tests.txt

  auth/cavp_3des_cmac_tests.txt
  auth/cavp_aes128_cmac_tests.txt
  auth/cavp_aes192_cmac_tests.txt
  auth/cavp_aes256_cmac_tests.txt
  auth/hmac_tests.txt
  auth/poly1305_tests.txt

  certs/many_constraints.pem
  certs/many_names1.pem
  certs/many_names2.pem
  certs/many_names3.pem
  certs/some_names1.pem
  certs/some_names2.pem
  certs/some_names3.pem

  cipher/aes_tests.txt
  cipher/cipher_tests.txt
  cipher/nist_cavp/aes_128_cbc.txt
  cipher/nist_cavp/aes_128_ctr.txt
  cipher/nist_cavp/aes_128_gcm.txt
  cipher/nist_cavp/aes_192_cbc.txt
  cipher/nist_cavp/aes_192_ctr.txt
  cipher/nist_cavp/aes_256_cbc.txt
  cipher/nist_cavp/aes_256_ctr.txt
  cipher/nist_cavp/aes_256_gcm.txt
  cipher/nist_cavp/tdes_cbc.txt
  cipher/nist_cavp/tdes_ecb.txt

  crypto-services/evp_tests.txt
  kex/ecdh_tests.txt

  hash/siphash_tests.txt
  math/bn_tests.txt
  math/ec_scalar_base_mult_tests.txt
  math/miller_rabin_tests.txt
  math/p256-x86_64_tests.txt

  pake/scrypt_tests.txt
  rand/ctrdrbg_vectors.txt

  signature/ecdsa_sign_tests.txt
  signature/ecdsa_verify_tests.txt
  signature/ed25519_tests.txt

  ${WYCHEPROOF_DIR}/aes_cbc_pkcs5_test.txt
  ${WYCHEPROOF_DIR}/aes_cmac_test.txt
  ${WYCHEPROOF_DIR}/aes_gcm_siv_test.txt
  ${WYCHEPROOF_DIR}/aes_gcm_test.txt
  ${WYCHEPROOF_DIR}/chacha20_poly1305_test.txt
  ${WYCHEPROOF_DIR}/dsa_test.txt
  ${WYCHEPROOF_DIR}/ecdh_secp224r1_test.txt
  ${WYCHEPROOF_DIR}/ecdh_secp256r1_test.txt
  ${WYCHEPROOF_DIR}/ecdh_secp384r1_test.txt
  ${WYCHEPROOF_DIR}/ecdh_secp521r1_test.txt
  ${WYCHEPROOF_DIR}/ecdsa_secp224r1_sha224_test.txt
  ${WYCHEPROOF_DIR}/ecdsa_secp224r1_sha256_test.txt
  ${WYCHEPROOF_DIR}/ecdsa_secp224r1_sha512_test.txt
  ${WYCHEPROOF_DIR}/ecdsa_secp256r1_sha256_test.txt
  ${WYCHEPROOF_DIR}/ecdsa_secp256r1_sha512_test.txt
  ${WYCHEPROOF_DIR}/ecdsa_secp384r1_sha384_test.txt
  ${WYCHEPROOF_DIR}/ecdsa_secp384r1_sha512_test.txt
  ${WYCHEPROOF_DIR}/ecdsa_secp521r1_sha512_test.txt
  ${WYCHEPROOF_DIR}/eddsa_test.txt
  ${WYCHEPROOF_DIR}/hkdf_sha1_test.txt
  ${WYCHEPROOF_DIR}/hkdf_sha256_test.txt
  ${WYCHEPROOF_DIR}/hkdf_sha384_test.txt
  ${WYCHEPROOF_DIR}/hkdf_sha512_test.txt
  ${WYCHEPROOF_DIR}/hmac_sha1_test.txt
  ${WYCHEPROOF_DIR}/hmac_sha224_test.txt
  ${WYCHEPROOF_DIR}/hmac_sha256_test.txt
  ${WYCHEPROOF_DIR}/hmac_sha384_test.txt
  ${WYCHEPROOF_DIR}/hmac_sha512_test.txt
  ${WYCHEPROOF_DIR}/kwp_test.txt
  ${WYCHEPROOF_DIR}/kw_test.txt
  ${WYCHEPROOF_DIR}/primality_test.txt
  ${WYCHEPROOF_DIR}/rsa_oaep_2048_sha1_mgf1sha1_test.txt
  ${WYCHEPROOF_DIR}/rsa_oaep_2048_sha224_mgf1sha1_test.txt
  ${WYCHEPROOF_DIR}/rsa_oaep_2048_sha224_mgf1sha224_test.txt
  ${WYCHEPROOF_DIR}/rsa_oaep_2048_sha256_mgf1sha1_test.txt
  ${WYCHEPROOF_DIR}/rsa_oaep_2048_sha256_mgf1sha256_test.txt
  ${WYCHEPROOF_DIR}/rsa_oaep_2048_sha384_mgf1sha1_test.txt
  ${WYCHEPROOF_DIR}/rsa_oaep_2048_sha384_mgf1sha384_test.txt
  ${WYCHEPROOF_DIR}/rsa_oaep_2048_sha512_mgf1sha1_test.txt
  ${WYCHEPROOF_DIR}/rsa_oaep_2048_sha512_mgf1sha512_test.txt
  ${WYCHEPROOF_DIR}/rsa_oaep_3072_sha256_mgf1sha1_test.txt
  ${WYCHEPROOF_DIR}/rsa_oaep_3072_sha256_mgf1sha256_test.txt
  ${WYCHEPROOF_DIR}/rsa_oaep_3072_sha512_mgf1sha1_test.txt
  ${WYCHEPROOF_DIR}/rsa_oaep_3072_sha512_mgf1sha512_test.txt
  ${WYCHEPROOF_DIR}/rsa_oaep_4096_sha256_mgf1sha1_test.txt
  ${WYCHEPROOF_DIR}/rsa_oaep_4096_sha256_mgf1sha256_test.txt
  ${WYCHEPROOF_DIR}/rsa_oaep_4096_sha512_mgf1sha1_test.txt
  ${WYCHEPROOF_DIR}/rsa_oaep_4096_sha512_mgf1sha512_test.txt
  ${WYCHEPROOF_DIR}/rsa_oaep_misc_test.txt
  ${WYCHEPROOF_DIR}/rsa_pkcs1_2048_test.txt
  ${WYCHEPROOF_DIR}/rsa_pkcs1_3072_test.txt
  ${WYCHEPROOF_DIR}/rsa_pkcs1_4096_test.txt
  ${WYCHEPROOF_DIR}/rsa_pss_2048_sha1_mgf1_20_test.txt
  ${WYCHEPROOF_DIR}/rsa_pss_2048_sha256_mgf1_0_test.txt
  ${WYCHEPROOF_DIR}/rsa_pss_2048_sha256_mgf1_32_test.txt
  ${WYCHEPROOF_DIR}/rsa_pss_3072_sha256_mgf1_32_test.txt
  ${WYCHEPROOF_DIR}/rsa_pss_4096_sha256_mgf1_32_test.txt
  ${WYCHEPROOF_DIR}/rsa_pss_4096_sha512_mgf1_32_test.txt
  ${WYCHEPROOF_DIR}/rsa_pss_misc_test.txt
  ${WYCHEPROOF_DIR}/rsa_sig_gen_misc_test.txt
  ${WYCHEPROOF_DIR}/rsa_signature_2048_sha224_test.txt
  ${WYCHEPROOF_DIR}/rsa_signature_2048_sha256_test.txt
  ${WYCHEPROOF_DIR}/rsa_signature_2048_sha384_test.txt
  ${WYCHEPROOF_DIR}/rsa_signature_2048_sha512_test.txt
  ${WYCHEPROOF_DIR}/rsa_signature_3072_sha256_test.txt
  ${WYCHEPROOF_DIR}/rsa_signature_3072_sha384_test.txt
  ${WYCHEPROOF_DIR}/rsa_signature_3072_sha512_test.txt
  ${WYCHEPROOF_DIR}/rsa_signature_4096_sha384_test.txt
  ${WYCHEPROOF_DIR}/rsa_signature_4096_sha512_test.txt
  ${WYCHEPROOF_DIR}/rsa_signature_test.txt
  ${WYCHEPROOF_DIR}/x25519_test.txt
  ${WYCHEPROOF_DIR}/xchacha20_poly1305_test.txt
)

add_custom_command(
  OUTPUT crypto_test_data.cc
  COMMAND ${GO_EXECUTABLE} run embed_test_data.go ${CRYPTO_TEST_DATA} > 
  ${CMAKE_CURRENT_BINARY_DIR}/crypto_test_data.cc
  DEPENDS embed_test_data.go ${CRYPTO_TEST_DATA}
  WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR})

add_library(crypto_test_data OBJECT crypto_test_data.cc)
