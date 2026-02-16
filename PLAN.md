# Wycheproof Vectors Migration Plan

Migration from `third_party/wycheproof_testvectors/` to `third_party/vectors/` system.

## Overview

Breaking the migration into logical groups. We'll work through categories in order and decide when to open PRs based on progress.

Each category follows the same pattern:
1. Add vectors using `./sync.py --new wycheproof/testvectors_v1/[vector_name].json`
2. Update test file paths from old to new location
3. Add duvet annotations to tests
4. Run `duvet report` to update snapshot
5. Test locally and verify all tests pass

---

## Category 1: HMAC Vectors

**Test file:** `crypto/hmac_extra/hmac_test.cc`

### Vectors to Add
- [x] hmac_sha1_test.json
- [x] hmac_sha224_test.json
- [x] hmac_sha256_test.json
- [x] hmac_sha384_test.json
- [x] hmac_sha512_test.json
- [x] hmac_sha512_224_test.json
- [x] hmac_sha512_256_test.json
- [x] hmac_sha3_224_test.json
- [x] hmac_sha3_256_test.json
- [x] hmac_sha3_384_test.json
- [x] hmac_sha3_512_test.json

### Tasks
- [x] Add all vectors via sync.py
- [x] Update paths in hmac_test.cc (11 references)
- [x] Add duvet annotations to each test
- [x] Run duvet report
- [x] Run tests locally
- [x] **Decision point: Open PR or continue?**

---

## Category 2: HKDF Vectors

**Test file:** `crypto/fipsmodule/hkdf/hkdf_test.cc`

### Vectors to Add
- [x] hkdf_sha1_test.json
- [x] hkdf_sha256_test.json
- [x] hkdf_sha384_test.json
- [x] hkdf_sha512_test.json

### Tasks
- [x] Add all vectors via sync.py
- [x] Update paths in hkdf_test.cc (4 references)
- [x] Add duvet annotations to each test
- [x] Run duvet report
- [x] Run tests locally
- [x] **Decision point: Open PR or continue?**

---

## Category 3: AEAD Vectors (ChaCha20-Poly1305, XChaCha20-Poly1305, AES-GCM-SIV)

**Test files:** 
- `crypto/cipher_extra/aead_test.cc`
- `crypto/cipher_extra/cipher_test.cc` (ChaCha20 part only)

### Vectors to Add
- [x] chacha20_poly1305_test.json
- [x] xchacha20_poly1305_test.json
- [x] aes_gcm_siv_test.json

### Tasks
- [x] Add all vectors via sync.py
- [x] Update paths in aead_test.cc (3 references)
- [x] Update paths in cipher_test.cc (1 reference for ChaCha20)
- [x] Add duvet annotations to each test
- [x] Run duvet report
- [x] Run tests locally
- [x] **Decision point: Open PR or continue?**

---

## Category 4: AES Cipher Vectors (CBC, CCM, Key Wrap, CMAC)

**Test files:**
- `crypto/cipher_extra/cipher_test.cc` (remaining tests)
- `crypto/fipsmodule/aes/aes_test.cc`
- `crypto/fipsmodule/cmac/cmac_test.cc`

### Vectors to Add
- [x] aes_cbc_pkcs5_test.json
- [x] aes_ccm_test.json
- [x] aes_wrap_test.json (was kw_test.json)
- [x] aes_kwp_test.json (was kwp_test.json)
- [x] aes_cmac_test.json

### Tasks
- [x] Add all vectors via sync.py
- [x] Update paths in cipher_test.cc (2 references)
- [x] Update paths in aes_test.cc (3 references for KW/KWP)
- [x] Update paths in cmac_test.cc (1 reference)
- [x] Add duvet annotations to each test
- [x] Run duvet report
- [x] Run tests locally
- [x] **Decision point: Open PR or continue?**

---

## Category 5: ECDH and X25519 Vectors

**Test files:**
- `crypto/ecdh_extra/ecdh_test.cc`
- `crypto/fipsmodule/curve25519/x25519_test.cc`

### Vectors to Add
- [ ] ecdh_secp224r1_test.json
- [ ] ecdh_secp256r1_test.json
- [ ] ecdh_secp384r1_test.json
- [ ] ecdh_secp521r1_test.json
- [ ] x25519_test.json

### Tasks
- [ ] Add all vectors via sync.py
- [ ] Update paths in ecdh_test.cc (4 references)
- [ ] Update paths in x25519_test.cc (1 reference)
- [ ] Add duvet annotations to each test
- [ ] Run duvet report
- [ ] Run tests locally
- [ ] **Decision point: Open PR or continue?**

---

## Category 6: RSA OAEP Vectors

**Test file:** `crypto/evp_extra/evp_test.cc` (OAEP tests only)

### Vectors to Add
- [ ] rsa_oaep_2048_sha1_mgf1sha1_test.json
- [ ] rsa_oaep_2048_sha224_mgf1sha1_test.json
- [ ] rsa_oaep_2048_sha224_mgf1sha224_test.json
- [ ] rsa_oaep_2048_sha256_mgf1sha1_test.json
- [ ] rsa_oaep_2048_sha256_mgf1sha256_test.json
- [ ] rsa_oaep_2048_sha384_mgf1sha1_test.json
- [ ] rsa_oaep_2048_sha384_mgf1sha384_test.json
- [ ] rsa_oaep_2048_sha512_mgf1sha1_test.json
- [ ] rsa_oaep_2048_sha512_mgf1sha512_test.json
- [ ] rsa_oaep_3072_sha256_mgf1sha1_test.json
- [ ] rsa_oaep_3072_sha256_mgf1sha256_test.json
- [ ] rsa_oaep_3072_sha512_mgf1sha1_test.json
- [ ] rsa_oaep_3072_sha512_mgf1sha512_test.json
- [ ] rsa_oaep_4096_sha256_mgf1sha1_test.json
- [ ] rsa_oaep_4096_sha256_mgf1sha256_test.json
- [ ] rsa_oaep_4096_sha512_mgf1sha1_test.json
- [ ] rsa_oaep_4096_sha512_mgf1sha512_test.json
- [ ] rsa_oaep_misc_test.json

### Tasks
- [ ] Add all vectors via sync.py
- [ ] Update paths in evp_test.cc (18 references in OAEP tests)
- [ ] Add duvet annotations to each test
- [ ] Run duvet report
- [ ] Run tests locally
- [ ] **Decision point: Open PR or continue?**

---

## Category 7: RSA PSS Vectors

**Test file:** `crypto/evp_extra/evp_test.cc` (PSS tests only)

### Vectors to Add
- [ ] rsa_pss_2048_sha1_mgf1_20_test.json
- [ ] rsa_pss_2048_sha256_mgf1_0_test.json
- [ ] rsa_pss_2048_sha256_mgf1_32_test.json
- [ ] rsa_pss_3072_sha256_mgf1_32_test.json
- [ ] rsa_pss_4096_sha256_mgf1_32_test.json
- [ ] rsa_pss_4096_sha512_mgf1_32_test.json
- [ ] rsa_pss_misc_test.json

### Tasks
- [ ] Add all vectors via sync.py
- [ ] Update paths in evp_test.cc (7 references in PSS tests)
- [ ] Add duvet annotations to each test
- [ ] Run duvet report
- [ ] Run tests locally
- [ ] **Decision point: Open PR or continue?**

---

## Category 8: Primality Test Vectors

**Test file:** `crypto/fipsmodule/bn/bn_test.cc`

### Vectors to Add
- [ ] primality_test.json

### Tasks
- [ ] Add vector via sync.py
- [ ] Update path in bn_test.cc (1 reference)
- [ ] Add duvet annotation to test
- [ ] Run duvet report
- [ ] Run tests locally
- [ ] **Decision point: Open PR or continue?**

---

## Category 9: Cleanup - Remove Old Directory

**Final cleanup after all migrations complete (separate PR)**

### Tasks
- [ ] Verify all previous work merged
- [ ] Verify no remaining references to `wycheproof_testvectors` in code
- [ ] Delete `third_party/wycheproof_testvectors/` directory
- [ ] Run full test suite
- [ ] Open cleanup PR

---

## Notes

### Path Transformation Pattern
Old: `third_party/wycheproof_testvectors/[name]_test.txt`
New: `third_party/vectors/converted/wycheproof/testvectors_v1/[name]_test.txt`

### Duvet Annotation Template
```cpp
//= third_party/vectors/vectors_spec.md#wycheproof
//# AWS-LC MUST test against `testvectors_v1/hmac_sha1_test.txt`.
//# AWS-LC MUST test against `testvectors_v1/hmac_sha224_test.txt`.
//# AWS-LC MUST test against `testvectors_v1/hmac_sha256_test.txt`.
TEST(...) { ... }
```

**Important:** When citing multiple spec lines in one duvet block, they MUST:
- Be in the same order as they appear in vectors_spec.md
- Be adjacent lines in the spec (no gaps between them)
- Otherwise duvet will not recognize them

Single-line annotations work the same way (just one `//# AWS-LC MUST...` line).

### Sync Command Template
```bash
cd third_party/vectors
./sync.py --new wycheproof/testvectors_v1/[name]_test.json
```

### Testing Commands
```bash
# Build and run crypto_test (contains all crypto tests)
ninja -C build crypto/crypto_test

# Run specific test filter
./build/crypto/crypto_test --gtest_filter="*TestName*"

# Or run all tests
ninja -C build run_tests
```
