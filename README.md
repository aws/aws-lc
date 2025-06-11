# AWS LibCrypto Formal Verification

[![.github/workflows/main.yml](https://github.com/awslabs/aws-lc-verification/actions/workflows/main.yml/badge.svg)](https://github.com/awslabs/aws-lc-verification/actions/workflows/main.yml)


This repository contains specifications, proof scripts, and other artifacts required to formally verify portions of [AWS libcrypto](https://github.com/awslabs/aws-lc). Formal verification is used to locate bugs and increase assurance of the correctness and security of the library.

C and X86_64 proofs are carried out in [SAW](https://saw.galois.com/) using [Cryptol](https://cryptol.net/) specifications stored in the [Galois Cryptol spec repository](https://github.com/GaloisInc/cryptol-specs). AArch64 proofs are carried out in NSym (a tool for symbolically-simulating and verifying Arm machine code that is currently under development by AWS) using translated specifications from Cryptol. [Coq](https://coq.inria.fr) proofs are developed for proving properties of some of the Cryptol specifications.

## Building and Running
The easiest way to build the library and run the proofs is to use [Docker](https://docs.docker.com/get-docker/). To check the proofs, execute the following steps in the top-level directory of the repository.

1. Clone the submodules
   1. `git submodule update --init`
   2. `pushd Coq/fiat-crypto; git submodule update --init --recursive; popd`

2. Build a Docker image:
   `docker build --pull --no-cache -f Dockerfile.[...] -t awslc-saw .`
   1. For running SAW proofs on X86_64, use: `Dockerfile.saw_x86`
   1. For running SAW proofs for AES-GCM on X86_64, use: `Dockerfile.saw_x86_aes_gcm`
   3. For running SAW proofs on AARCH64, use: `Dockerfile.saw_aarch64`
   4. For running Coq proofs, use: `Dockerfile.coq`
   5. For running NSym proofs, use: `Dockerfile.nsym`

3. Run the SAW proofs inside the Docker container: ``docker run -v `pwd`:`pwd` -w `pwd` awslc-saw``
   1. Run SAW proofs on X86_64: ``docker run -it -v `pwd`:`pwd` -w `pwd` --entrypoint SAW/scripts/x86_64/docker_entrypoint.sh awslc-saw``
      1. This step will also run formally-verified tests on certain hard-coded constant values.
   2. RUN SAW proofs for AES-GCM on x86_64: ``docker run -it -v `pwd`:`pwd` -w `pwd` --entrypoint SAW/scripts/x86_64/docker_entrypoint_aes_gcm.sh awslc-saw``
   3. Run SAW proofs on AARCH64: ``docker run -it -v `pwd`:`pwd` -w `pwd` --entrypoint SAW/scripts/aarch64/docker_entrypoint.sh awslc-saw``
   4. Use Coq to validate the Cryptol specs used in the SAW proofs: ``docker run -it -v `pwd`:`pwd` -w `pwd` --entrypoint Coq/docker_entrypoint.sh awslc-saw``
   5. Run NSym for AARCH64 assembly: ``docker run -it -v `pwd`:`pwd` -w `pwd` --entrypoint NSym/scripts/docker_entrypoint.sh awslc-saw``

Running ``docker run -it -v `pwd`:`pwd` -w `pwd` --entrypoint bash awslc-saw`` will enter an interactive shell within the container, which is often useful for debugging.

## Verified Code

AWS libcrypto includes many cryptographic algorithm implementations for several different platforms. Only a subset of algorithms are formally verified, and only for certain platforms. The formal verification ensures that the API operations listed in the following table have the correct behavior as defined by a formal specification. This specification describes cryptographic behavior as well as behavior related to state and memory management. In some cases, the verification is limited to certain input lengths, or there are other caveats as described below. The verified implementations are:

| Algorithm | Variants |  API Operations | Platform   | Caveats | Tech |
| ----------| -------------| --------------- | -----------| ------------ | --------- |
| [SHA-2](SPEC.md#SHA-2) | 384, 512 | EVP_DigestInit, EVP_DigestUpdate, EVP_DigestFinal | SandyBridge+ | NoEngine, MemCorrect | SAW |
| [SHA-2](SPEC.md#SHA-2) | 384, 512 | EVP_DigestInit, EVP_DigestUpdate, EVP_DigestFinal | neoverse-n1, neoverse-v1 | NoEngine, NoInline, MemCorrect, ArmSpecGap, ToolGap, LaxPointer | SAW, NSym |
| [HMAC](SPEC.md#HMAC-with-SHA-384) | with <nobr>SHA-384</nobr> | HMAC_CTX_init, HMAC_Init_ex, HMAC_Update, HMAC_Final, HMAC | SandyBridge+ | NoEngine, MemCorrect, InitZero, NoInline, CRYPTO_once_Correct | SAW |
| [<nobr>AES-KW(P)</nobr>](SPEC.md#AES-KWP) | 256 | AES_wrap_key, AES_unwrap_key, AES_wrap_key_padded, AES_unwrap_key_padded | SandyBridge+ | InputLength, MemCorrect, NoInline | SAW |
| [<nobr>AES-GCM</nobr>](SPEC.md#AES-GCM) | 256 | EVP_CipherInit_ex, EVP_CIPHER_CTX_ctrl, EVP_EncryptUpdate, EVP_DecryptUpdate, EVP_EncryptFinal_ex, EVP_DecryptFinal_ex | SandyBridge-Skylake | MemCorrect, NoInline, GcmSpecGap, GcmMultipleOf16, GcmADNotVerified, GcmIV12Tag16, GcmWellFoundedInduction | SAW |
<!--- | [HKDF](SPEC.md#HKDF-with-HMAC-SHA384) | with <nobr>HMAC-SHA384</nobr> | HKDF_extract, HKDF_expand, HKDF | SandyBridge+ | MemCorrect, NoEngine, NoInline, OutputLength, CRYPTO_once_Correct | SAW | --->
<!--- | [Elliptic Curve Keys and Parameters](SPEC.md#Elliptic-Curve-Keys-and-Parameters) | with <nobr>P-384</nobr> | EVP_PKEY_CTX_new_id, EVP_PKEY_CTX_new, EVP_PKEY_paramgen_init, EVP_PKEY_CTX_set_ec_paramgen_curve_nid, EVP_PKEY_paramgen, EVP_PKEY_keygen_init, EVP_PKEY_keygen | SandyBridge+ | SAWCore_Coq, EC_Fiat_Crypto, ToolGap, NoEngine, MemCorrect, CRYPTO_refcount_Correct, CRYPTO_once_Correct, OptNone, SAWBreakpoint, LaxPointer | SAW, Coq | --->
<!--- | [ECDSA](SPEC.md#ECDSA) | with <nobr>P-384</nobr>, <nobr>SHA-384</nobr> | EVP_DigestSignInit, EVP_DigestVerifyInit, EVP_DigestSignUpdate, EVP_DigestVerifyUpdate, EVP_DigestSignFinal, EVP_DigestVerifyFinal, EVP_DigestSign, EVP_DigestVerify | SandyBridge+ | EC_Pub_Mul_Correct, EC_Constants_Correct, EC_Conversion_Correct, SAWCore_Coq, EC_Fiat_Crypto, NoEngine, MemCorrect, ECDSA_k_Valid, ECDSA_SignatureLength, CRYPTO_refcount_Correct, CRYPTO_once_Correct, ERR_put_error_Correct, NoInline | SAW, Coq | --->
<!--- | [ECDH](SPEC.md#ECDH) | with <nobr>P-384</nobr> | EVP_PKEY_derive_init, EVP_PKEY_derive | SandyBridge+ | SAWCore_Coq, EC_Fiat_Crypto, ECDH_InfinityTestCorrect, ToolGap, MemCorrect, NoEngine, CRYPTO_refcount_Correct, PubKeyValid | SAW, Coq | --->

The platforms for which code is verified are defined in the following table. In all cases, the actual verification is performed on code that is produced by Clang, but the verification results also apply to any compiler that produces semantically equivalent code.

| Platform        | Description | Compiler |
| --------------- | ------------| -------- |
| SandyBridge+ | x86-64 with AES-NI, CLMUL, and AVX. | Clang 10. Compile switches: see [build_llvm.sh](SAW/scripts/x86_64/build_llvm.sh) and [build_x86.sh](SAW/scripts/x86_64/build_x86.sh)
| SandyBridge-Skylake | x86-64 with AES-NI, CLMUL, and AVX, but not AVX-512. | Clang 10. Compile switches: see [build_llvm.sh](SAW/scripts/x86_64/build_llvm.sh) and [build_x86.sh](SAW/scripts/x86_64/build_x86.sh)
| neoverse-n1 | aarch64 without SHA512. | Clang 10 for C and Clang 10/14 for assembly. Compile switches: see [build_llvm.sh](SAW/scripts/aarch64/build_llvm.sh) and [build_aarch64.sh](NSym/scripts/build_aarch64.sh)
| neoverse-v1 | aarch64 with SHA512. | Clang 10 for C and Clang 14 for assembly. Compile switches: see [build_llvm.sh](SAW/scripts/aarch64/build_llvm.sh) and [build_aarch64.sh](NSym/scripts/build_aarch64.sh)

The caveats associated with some of the verification results are defined in the table below.

| Caveat        | Description |
| --------------| ------------|
| SAWCore_Coq | Certain facts are admitted in Coq code provided by the saw-core-coq library. |
| EC_Fiat_Crypto | The proof uses formal specifications of finite field arithmetic provided by Fiat-Crypto. When building in the specified configurations, the finite field implementation is provided by s2n-bignum, which is verified against a different formal specification. The overall formal verification result only holds for this configuration if s2n-bignum code is also correct w.r.t. the formal specification taken from Fiat-Crypto. To obtain a formally verified implementation without this mechanization gap, the code can be built in a configuration that causes the finite field arithmetic code from Fiat-Crypto to be used instead of s2n-bignum.|
| ECDH_InfinityTestCorrect | The ECDH output conversion tests that the resulting point is not the point at infinity. This test is not formally verified, and it is assumed this test always returns "false" in the ECDH operation. This latter assumption is justified by the Coq proofs that show that ECDH correctly implements group multiplication, and the point at infinity is not in the group. |
| EC_Pub_Mul_Correct    | The proof assumes the correctness of the "public" point multilpication operation used by ECDSA signature verification that computes `aG + bP` where `G` is the base point, `P` is an arbitrary point, and `a` and `b` are scalars. |
| InputLength    | The implementation is verified correct only on a limited number of input lengths. These lengths were chosen to exercise all paths through the code, and the code is verified correct for all possible input values of each length. |
| OutputLength    | The implementation is verified correct only on a limited number of output lengths. These lengths were chosen to satisfy the verification needs of other cryptographic functions, and the code is verified correct for all possible input values of each length. |
| NoEngine      | For any API operation that accepts an ENGINE*, the implementation is only verified when the supplied pointer is null. |
| MemCorrect    | Basic memory management functions such as OPENSSL_malloc and OPENSSL_free are not verified, and are assumed to behave correctly. |
| InitZero      | The specification for the "init" function requires a context to be in a "zeroized" state. According to this specification, contexts cannot be reused without first being returned to this zeroized state by some other mechanism. |
| ECDSA_k_Valid | The implementation is verified correct assuming function bn_rand_range_words returns (at first call) a random integer `k` that results in a valid signature. |
| ECDSA_SignatureLength | The implementation is verified correct only for a given length, in bytes, of the signature in ASN1 format. The length is determined by the bitwidth of `r` and `s`, which are determined by `k`. |
| CRYPTO_refcount_Correct | Functions CRYPTO_refcount_inc, and CRYPTO_refcount_dec_and_test_zero_ov are not verified, and are assumed to behave correctly. |
| CRYPTO_once_Correct | Function CRYPTO_once is not verified, and is assumed to behave correctly and initialize the *_storage global by calling the `*_init` function passed as the second argument. All `*_init` functions passed as arguments to CRYPTO_once are verified separately. |
| ERR_put_error_Correct | Function ERR_put_error is not verified, and is assumed to behave correctly. |
| NoInline | The implementation is verified correct assuming that certain functions are not inlined when compiled with optimizations enabled. |
| OptNone | The implementation is verified correct assuming that certain functions are not optimized by the compiler. |
| PubKeyValid | Public key validity checks are not verified, and the code is only proved correct for the public keys that pass these checks. |
| SAWBreakpoint | The proof uses SAW's breakpoint feature. This feature assumes the specification on the breakpoint function for the inductive hypothesis. The feature lacks well-foundedness check for the inductive invariant. |
| ArmSpecGap | The Cryptol specification used in NSym proofs for Arm is different from the one used in the corresponding SAW proofs. Specifically, recursive comprehensions are written as recursions. We verify the body of the recursions are equivalent but the top-level loop structure is not verified. |
| ToolGap | Adjacent components in the implementation are formally verified using different tools.  These tools may use different language semantics, memory models, etc. It is assumed that a proof of correctness in one tool implies correct behavior as determined by another tool. Additionally, it is assumed that parameter values correctly flow from one component to another. |
| GcmSpecGap | AES-GCM is verified using an implementation-specific Cryptol spec describing an optimized form of AES-GCM. |
| GcmMultipleOf16 | EVP_{Encrypt,Decrypt}Update are only verified for cases where whole blocks are encrypted/decrypted, i.e., the length is a multiple of 16. |
| GcmADNotVerified | Supplying additional data (AD) to AES-GCM is not verified. |
| GcmIV12Tag16 | The AES-GCM functions are only verified for 12-byte IVs and 16-byte tags. |
| GcmWellFoundedInduction | The AES-GCM proofs make use of inductive proofs to prove theorems about unbounded loops, but the inductive hypotheses are assumed, as SAW lacks a well-foundedness check for the inductive invariants. |
| LaxPointer | The Clang optimization will sometimes introduce comparisons between pointers from different allocation blocks. This is considered an undefined behaviour in SAW. In these benign cases, we use `enable_lax_pointer_ordering` to disable such pointer checks.


### Functions with compiler optimization disabled

Most of the code is verified with compiler optimizations enabled, which causes Clang to aggressively inline certain functions during compilation. There are some functions which currently pose issues for SAW when inlined, so we patch these functions to mark them as `noinline` to prevent Clang from inlining them. The table below describes all such functions and the reasons why they are marked as `noinline`:

| Function | Algorithms Used In | Reason |
| -------- | ------------------ | ------ |
| `bn_mod_add_words` | ECDSA | This function invokes several functions which use inline assembly, such as `bn_add_words`. Without `noinline`, this inline assembly would be inlined into several larger functions which cannot currently use `llvm_verify_x86`. |
| `bn_reduce_once_in_place` | ECDSA | This function invokes several functions which use inline assembly, such as `bn_sub_words`. Without `noinline`, this inline assembly would be inlined into several larger functions which cannot currently use `llvm_verify_x86`. |
| `bn_sub_words` | ECDSA | This function directly uses inline assembly. Without `noinline`, this inline assembly would be inlined into several larger functions which cannot currently use `llvm_verify_x86`. |
| `ec_scalar_is_zero` | ECDSA | There isn't anything immediately problematic about this function, and indeed, SAW is able to verify its specification. The problem is that this function is used in the main loop of `ECDSA_do_sign`, which will not break out of the loop unless `ec_scalar_is_zero` returns 0. The input to `ec_scalar_is_zero` is ultimately computed from randomly generated data, so given enough iterations of the loop, it is highly probable that `ec_scalar_is_zero` will eventually receive non-zero input and return 1. However, SAW does not realize this, so it will enter an infinite loop when reasoning about the `ECDSA_do_sign` without assistance. Therefore, we override `ec_scalar_is_zero` with a specification that always returns 0 to trigger the end of the loop, but this will only work if `ec_scalar_is_zero` is not inlined away, hence the `noinline`. |
| `value_barrier_w` | <nobr>AES-KW(P)</nobr>, ECDSA | This function directly uses inline assembly. Without `noinline`, this inline assembly would be inlined into several larger functions which cannot currently use `llvm_verify_x86`. Note that `value_barrier_w(x)` is semantically equivalent to `x` for all `x`; `value_barrier_w` primarily exists to prevent Clang from applying certain optimizations to `x` which would adversely affect constant-time code. |
| `GetInPlaceMethods` | HMAC | The specification for `GetInPlaceMethods` is used in the compositional proof of `HMAC_Init_ex`. Without `noinline`, `GetInPlaceMethods` will be inlined and the override for `GetInPlaceMethods` will fail. |
| `HMAC_Final` | HMAC | The specification for `HMAC_Final` is used in the compositional proof of `HMAC`. Without `noinline`, `HMAC_Final` will be inlined and the override for `HMAC_Final` will fail. |
| `HMAC_Update` | HMAC | The specification for `HMAC_Update` is used in the compositional proof of `HMAC`. Without `noinline`, `HMAC_Update` will be inlined and the override for `HMAC_Update` will fail. |
| `HKDF_extract` | HKDF | The specification for `HKDF_extract` is used in the compositional proof of `HKDF`. Without `noinline`, `HKDF_extract` will be inlined and the override for `HKDF_extract` will fail. |
| `HKDF_expand` | HKDF | The specification for `HKDF_expand` is used in the compositional proof of `HKDF`. Without `noinline`, `HKDF_expand` will be inlined and the override for `HKDF_expand` will fail. |
| `SHA384_Update` | ECDSA | The specification for `SHA384_Update` is used in the compositional proof of `EVP_DigestSignUpdate`. Without `noinline`, `SHA384_Update` will be inlined and the override for `SHA384_Update` will fail. |
| `SHA384_Final` | ECDSA | The specification for `SHA384_Final` is used in the compositional proof of `EVP_DigestSignFinal`. Without `noinline`, `SHA384_Final` will be inlined and the override for `SHA384_Final` will fail. |
| `EVP_DigestSignUpdate` | ECDSA | The specification for `EVP_DigestSignUpdate` is used in the compositional proof of `EVP_DigestSign`. Without `noinline`, `EVP_DigestSignUpdate` will be inlined and the override for `EVP_DigestSignUpdate` will fail. |
| `EVP_DigestVerifyUpdate` | ECDSA | The specification for `EVP_DigestVerifyUpdate` is used in the compositional proof of `EVP_DigestVerify`. Without `noinline`, `EVP_DigestVerifyUpdate` will be inlined and the override for `EVP_DigestVerifyUpdate` will fail. |
| `p384_select_point_affine` | EC | The specification for `p384_select_point_affine` is used in the compositional proof of `ec_GFp_nistp384_point_mul_base`. Without `noinline`, `p384_select_point_affine` will be inlined and the override for `p384_select_point_affine` will fail. |
| `bn_is_bit_set_words` | EC | The specification for `bn_is_bit_set_words` is used in the compositional proof of `ec_compute_wNAF`. Without `noinline`, `bn_is_bit_set_words` will be inlined and the override for `bn_is_bit_set_words` will fail. |
| `ec_compute_wNAF` | EC | The specification `ec_compute_wNAF` is used in the compositional proof of `ec_GFp_nistp384_point_mul_public`. Without `noinline`, `ec_compute_wNAF` will be inlined and the override for `ec_compute_wNAF` will fail. |

SAW's breakpoint feature for invariant proof capability requires all local variables used in a loop to be fully captured at the point of loop condition check. Compiler optimization might invent new local variables or move variables around that makes it hard to use the breakpoint feature. Therefore verification of functions that use the breakpoint feature are marked as `optnone` to disable compiler optimization on this specific function.

| Function | Algorithms Used In | Reason |
| -------- | ------------------ | ------ |
| `ec_GFp_nistp384_point_mul_public` | EC | This function has a loop that is computationally hard for SAW. We use SAW's breakpoint feature to conduct invariant proof instead of doing loop-unrolling. |

## Specification

The [SPEC.md](SPEC.md) file contains specifications for each verified implementation.

## License

This project is licensed under the [Apache-2.0 License](LICENSE). See [Contributing](CONTRIBUTING.md) for information about contributions to this repository.
