# AWS LibCrypto Formal Verification

This repository contains specifications, proof scripts, and other artifacts required to formally verify portions of [AWS libcrypto](https://github.com/awslabs/aws-lc). Formal verification is used to locate bugs and increase assurance of the correctness and security of the library. 

## Verified Code

AWS libcrypto includes many cryptographic algorithm implementations for several different platforms. Only a subset of algorithms are formally verified, and only for certain platforms. The formal verification ensures that the API operations listed in the following table have the correct behavior as defined by a formal specification. This specification describes cryptographic behavior as well as behavior related to state and memory management. In some cases, the verification is limited to certain input lengths, or there are other caveats as described below. The verified implementations are:

| Algorithm | Variants |  API Operations | Platform   | Caveats | Tech |
| ----------| -------------| --------------- | -----------| ------------ | --------- |
| SHA-2     | 384, 512     | EVP_DigestInit, EVP_DigestUpdate, EVP_DigestFinal, EVP_Digest     | SandyBridge+ | InputLength, NoEngine, MemCorrect | [SAW](SAW/README.md) |
| HMAC      | with <nobr>SHA-384</nobr> | HMAC_CTX_init, HMAC_Init_ex, HMAC_Update, HMAC_Final, HMAC | SandyBridge+ | InputLength, NoEngine, MemCorrect, InitZero | [SAW](SAW/README.md) |
| AES-GCM   | 256 | EVP_CipherInit_ex, EVP_EncryptUpdate, EVP_DecryptUpdate, EVP_EncryptFinal_ex, EVP_DecryptFinal_ex | SandyBridge+ | InputLength, NoEngine, MemCorrect, InitZero, AESNI_GCM_Patch, AES_GCM_FROM_CIPHER_CTX_Correct | [SAW](SAW/README.md) |

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


## License

This project is licensed under the [Apache-2.0 License](LICENSE). See [Contributing](CONTRIBUTING.md) for information about contributions to this repository.
