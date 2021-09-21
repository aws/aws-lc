# AWS LibCrypto Formal Verification

This repository contains specifications, proof scripts, and other artifacts required to formally verify portions of [AWS libcrypto](https://github.com/awslabs/aws-lc). Formal verification is used to locate bugs and increase assurance of the correctness and security of the library.

## Verified Code

AWS libcrypto includes many cryptographic algorithm implementations for several different platforms. Only a subset of algorithms are formally verified, and only for certain platforms. The formal verification ensures that the API operations listed in the following table have the correct behavior as defined by a formal specification. This specification describes cryptographic behavior as well as behavior related to state and memory management. In some cases, the verification is limited to certain input lengths, or there are other caveats as described below. The verified implementations are:

| Algorithm | Variants |  API Operations | Platform   | Caveats | Tech |
| ----------| -------------| --------------- | -----------| ------------ | --------- |
| SHA-2     | 384, 512     | EVP_DigestInit, EVP_DigestUpdate, EVP_DigestFinal | SandyBridge+ | NoEngine, MemCorrect | [SAW](SAW/README.md) |
| HMAC      | with <nobr>SHA-384</nobr> | HMAC_CTX_init, HMAC_Init_ex, HMAC_Update, HMAC_Final, HMAC | SandyBridge+ | InputLength, NoEngine, MemCorrect, InitZero | [SAW](SAW/README.md) |
| AES-GCM   | 256 | EVP_CipherInit_ex, EVP_EncryptUpdate, EVP_DecryptUpdate, EVP_EncryptFinal_ex, EVP_DecryptFinal_ex | SandyBridge+ | InputLength, NoEngine, MemCorrect, InitZero, AESNI_GCM_Patch, AES_GCM_FROM_CIPHER_CTX_Correct, NoInline | [SAW](SAW/README.md) |
| <nobr>AES-KW(P)</nobr>  | 256     | AES_wrap_key, AES_unwrap_key, AES_wrap_key_padded, AES_unwrap_key_padded | SandyBridge+ | InputLength, MemCorrect, NoInline |[SAW](SAW/README.md) |
| Elliptic Curve Keys and Parameters | with <nobr>P-384</nobr> | EVP_PKEY_CTX_new_id, EVP_PKEY_CTX_new, EVP_PKEY_paramgen_init, EVP_PKEY_CTX_set_ec_paramgen_curve_nid, EVP_PKEY_paramgen, EVP_PKEY_keygen_init, EVP_PKEY_keygen | SandyBridge+ | NoEngine, MemCorrect, CRYPTO_refcount_Correct |[SAW](SAW/README.md) |
| ECDSA     | with <nobr>P-384</nobr>, <nobr>SHA-384</nobr> | EVP_DigestSignInit, EVP_DigestVerifyInit, EVP_DigestSignUpdate, EVP_DigestVerifyUpdate, EVP_DigestSignFinal, EVP_DigestVerifyFinal | SandyBridge+ | InputLength, NoEngine, MemCorrect, ECDSA_k_Valid, ECDSA_SignatureLength, CRYPTO_refcount_Correct, ERR_put_error_Correct, NoInline |[SAW](SAW/README.md) |
| ECDH      | with <nobr>P-384</nobr> | EVP_PKEY_derive_init, EVP_PKEY_derive | SandyBridge+ | NoEngine, CRYPTO_refcount_Correct |[SAW](SAW/README.md) |

The platforms for which code is verified are defined in the following table. In all cases, the actual verification is performed on code that is produced by Clang 10, but the verification results also apply to any compiler that produces semantically equivalent code.

| Platform        | Description |
| --------------- | ------------|
| SandyBridge+ | x86-64 with AES-NI, CLMUL, and AVX. Compile switches: -DCMAKE_BUILD_TYPE=Release

The caveats associated with some of the verification results are defined in the table below.

| Caveat        | Description |
| --------------| ------------|
| InputLength    | The implementation is verified correct only on a limited number of input lengths. These lengths were chosen to exercise all paths through the code, and the code is verified correct for all possible input values of each length. |
| NoEngine      | For any API operation that accepts an ENGINE*, the implementation is only verified when the supplied pointer is null. |
| MemCorrect    | Basic memory management functions such as OPENSSL_malloc and OPENSSL_free are not verified, and are assumed to behave correctly. |
| InitZero      | The specification for the "init" function requires a context to be in a "zeroized" state. According to this specification, contexts cannot be reused without first being returned to this zeroized state by some other mechanism. |
| AESNI_GCM_Patch | Functions aesni_gcm_encrypt and aesni_gcm_decrypt are patched in order to remove the key aliasing check. This check is a no-op when these functions are called in compliance with the ABI. |
| AES_GCM_FROM_CIPHER_CTX_Correct | Getter function aes_gcm_from_cipher_ctx is not verified, and is assumed to behave correctly. |
| ECDSA_k_Valid | The implementation is verified correct assuming function bn_rand_range_words returns (at first call) a random integer `k` that results in a valid signature. |
| ECDSA_SignatureLength | The implementation is verified correct only for a given length, in bytes, of the signature in ASN1 format. The length is determined by the bitwidth of `r` and `s`, which are determined by `k`. |
| CRYPTO_refcount_Correct | Functions CRYPTO_refcount_inc, and CRYPTO_refcount_dec_and_test_zero_ov are not verified, and are assumed to behave correctly. |
| ERR_put_error_Correct | Function ERR_put_error is not verified, and is assumed to behave correctly. |
| NoInline | The implementation is verified correct assuming that certain functions are not inlined when compiled with optimizations enabled. |

### Functions marked as `noinline`

Most of the code is verified with optimizations enabled, which causes Clang to aggressively inline certain functions during compilation. There are some functions which currently pose issues for SAW when inlined, so we patch these functions to mark them as `noinline` to prevent Clang from inlining them. The table below describes all such functions and the reasons why they are marked as `noinline`:

| Function | Algorithms Used In | Reason |
| -------- | ------------------ | ------ |
| `aes_gcm_from_cipher_ctx` | AES-GCM | This is an unverified function which performs tricky pointer arithmetic. See also the AES_GCM_FROM_CIPHER_CTX_Correct caveat above. |
| `bn_mod_add_words` | ECDSA | This function invokes several functions which use inline assembly, such as `bn_add_words`. Without `noinline`, this inline assembly would be inlined into several larger functions which cannot currently use `llvm_verify_x86`. |
| `bn_reduce_once_in_place` | ECDSA | This function invokes several functions which use inline assembly, such as `bn_sub_words`. Without `noinline`, this inline assembly would be inlined into several larger functions which cannot currently use `llvm_verify_x86`. |
| `bn_sub_words` | ECDSA | This function directly uses inline assembly. Without `noinline`, this inline assembly would be inlined into several larger functions which cannot currently use `llvm_verify_x86`. |
| `ec_scalar_is_zero` | ECDSA | There isn't anything immediately problematic about this function, and indeed, SAW is able to verify its specification. The problem is that this function is used in the main loop of `ECDSA_do_sign`, which will not break out of the loop unless `ec_scalar_is_zero` returns 0. The input to `ec_scalar_is_zero` is ultimately computed from randomly generated data, so given enough iterations of the loop, it is highly probable that `ec_scalar_is_zero` will eventually receive non-zero input and return 1. However, SAW does not realize this, so it will enter an infinite loop when reasoning about the `ECDSA_do_sign` without assistance. Therefore, we override `ec_scalar_is_zero` with a specification that always returns 0 to trigger the end of the loop, but this will only work if `ec_scalar_is_zero` is not inlined away, hence the `noinline`. |
| `value_barrier_w` | <nobr>AES-KW(P)</nobr>, ECDSA | This function directly uses inline assembly. Without `noinline`, this inline assembly would be inlined into several larger functions which cannot currently use `llvm_verify_x86`. Note that `value_barrier_w(x)` is semantically equivalent to `x` for all `x`; `value_barrier_w` primarily exists to prevent Clang from applying certain optimizations to `x` which would adversely affect constant-time code. |

## License

This project is licensed under the [Apache-2.0 License](LICENSE). See [Contributing](CONTRIBUTING.md) for information about contributions to this repository.
