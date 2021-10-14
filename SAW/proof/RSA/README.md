# RSA-PSS Verification using SAW

The following table describes the RSA-PSS implementation that is verified using SAW. See the [top-level README](../../../README.md) for general information and definitions related to this table.

| Algorithm | Variants |  API Operations | Platform   | Caveats
| ----------| -------------| --------------- | -----------| ------------
| RSA       | 1024, with <nobr>SHA-384</nobr> | EVP_DigestSignInit, EVP_DigestVerifyInit, EVP_DigestSignUpdate, EVP_DigestVerifyUpdate, EVP_DigestSignFinal, EVP_DigestVerifyFinal | SandyBridge+ | InputLength, NoEngine, MemCorrect, RSA_Blinding, CRYPTO_refcount_Correct, CRYPTO_MUTEX_Correct, CRYPTO_once_Correct, ERR_put_error_Correct, DebugSettings

The caveats associated with the RSA-PSS verification results are defined in the table below.

| Caveat        | Description |
| --------------| ------------|
| RSA_Blinding | Functions rsa_blinding_get, and rsa_blinding_release are are not verified, and are assumed to get and release a valid blinding factor.
| CRYPTO_MUTEX_Correct | Functions CRYPTO_MUTEX_lock_read, CRYPTO_MUTEX_unlock_read, CRYPTO_MUTEX_lock_write, and CRYPTO_MUTEX_unlock_write are not verified, and are assumed to behave correctly. |
| DebugSettings | The implementation is verified correct using code that is compiled using CMake's `-DCMAKE_BUILD_TYPE=Debug` settings, which does not apply certain optimizations that are used in `-DCMAKE_BUILD_TYPE=Release` settings. |

The EVP_DigestSign*/EVP_DigestVerify* functions are verified to have the following properties related to RSA-PSS with SHA-384. For more detailed specifications, see [evp-function-specs.saw](evp-function-specs.saw). BLOCK_LENGTH is the block length of the hash function, in bytes. KEY_SIZE is the RSA key size, in bytes. For RSA-PSS-1024 with SHA-384, BLOCK_LENGTH is 64 and KEY_SIZE is 128.

The RSA key generation is not verified.

| Function  | Preconditions |  Postconditions |
| ----------| --------------| --------------- |
| EVP_DigestSignInit | <ul><li>The parameters are an allocated EVP_MD_CTX, a valid EVP_MD such as the value returned by EVP_sha384(), and an initialized EVP_PKEY containing a private RSA key </li></ul> | <ul><li>The context is valid and initialized for the sign operation with the given key and the given digest algorithm.</li></ul> |
| EVP_DigestVerifyInit | <ul><li>The parameters are an allocated EVP_MD_CTX, a valid EVP_MD such as the value returned by EVP_sha384(), and an initialized EVP_PKEY containing a public RSA key </li></ul> | <ul><li>The context is valid and initialized for the verify operation with the given key and the given digest algorithm.</li></ul> |
| EVP_DigestSignUpdate | <ul><li>The context is valid (for the sign operation) and the internal buffer offset is n.</li><li>The input length is k, and the input buffer has at least k allocated bytes.</li></ul> | <ul><li>The hash state in the context has been correctly updated for each complete block as defined by the SHA-2 specification.</li><li>The first (n+k)%BLOCK_LENGTH bytes of the internal buffer are equal to the remaining input bytes, and the internal buffer offset has been updated to (n+k)%BLOCK_LENGTH.</li></ul> |
| EVP_DigestVerifyUpdate | <ul><li>The context is valid (for the verify operation) and the internal buffer offset is n.</li><li>The input length is k, and the input buffer has at least k allocated bytes.</li></ul> | <ul><li>The hash state in the context has been correctly updated for each complete block as defined by the SHA-2 specification.</li><li>The first (n+k)%BLOCK_LENGTH bytes of the internal buffer are equal to the remaining input bytes, and the internal buffer offset has been updated to (n+k)%BLOCK_LENGTH.</li></ul> |
| EVP_DigestSignFinal | <ul><li>The context is valid and the internal buffer offset is n.</li><li> The output buffer has at least KEY_SIZE allocated bytes.</li><li> The length output pointer points to the integer KEY_SIZE.</li></ul> | <ul><li>The output buffer holds the correct signature as defined by the RSA-PSS specification. This signature is produced from the hash value (as defined by the SHA-2 specification) and the private key.</li><li>The output length pointer points to the integer KEY_SIZE.</li></ul> |
| EVP_DigestVerifyFinal | <ul><li>The context is valid and the internal buffer offset is n.</li><li>The input buffer contains an RSA-PSS signature candidate.</li></ul> | <ul><li>The function returns 1 if the signature is valid as defined by the RSA-PSS specification, 0 otherwise. This signature is validated for the hash value (as defined by the SHA-2 specification) and the public key.</li></ul> |

