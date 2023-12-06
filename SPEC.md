# High-level Specification

This section describes high-level specification for verified implementations.

## SHA-2

The EVP_Digest* functions are verified to have the following properties related to SHA-2. For more detailed specifications, see [evp-function-specs.saw](SAW/proof/SHA512/evp-function-specs.saw). BLOCK_LENGTH is the block length of the hash function, in bytes. DIGEST_LENGTH is the digest length of the hash function, in bytes. For example, for SHA-384, BLOCK_LENGTH is 64 and DIGEST_LENGTH is 48.

| Function  | Preconditions |  Postconditions |
| ---------------| -------------| --------------- |
| EVP_DigestInit | <ul><li>The parameters are an allocated EVP_MD_CTX and a valid EVP_MD such as the value returned by EVP_sha384()</li></ul> | <ul><li>The context is valid and initialized for the desired algorithm.</li></ul> |
| EVP_DigestUpdate | <ul><li>The context is valid and the internal buffer offset is a symbolic integer n.</li><li>The input length is a symbolic integer k, and the input buffer has at least k allocated bytes.</li></ul> | <ul><li>The hash state in the context has been correctly updated for each complete block as defined by the SHA-2 specification.</li><li>The first (n+k)%BLOCK_LENGTH bytes of the internal buffer are equal to the remaining input bytes, and the internal buffer offset has been updated to (n+k)%BLOCK_LENGTH.</li></ul> |
| EVP_DigestFinal | <ul><li>The context is valid and the internal buffer offset is a symbolic integer n.</li><li> The output buffer has at least DIGEST_LENGTH allocated bytes.</li><li> The length output pointer is either null or it points to an integer.</li></ul> | <ul><li>The output buffer holds the correct hash value as defined by the SHA-2 specification. This hash value is produced from the hash state and the remaining n bytes in the internal buffer.</li><li> If the output length pointer is non-null, it points to the value DIGEST_LENGTH.</li></ul> |

## HMAC with SHA-384

The HMAC_* functions are verified to have the following properties related to HMAC with SHA-384. For more detailed specifications, see [HMAC-array.saw](SAW/proof/HMAC/HMAC-array.saw). BLOCK_LENGTH is the block length of the hash function, in bytes. DIGEST_LENGTH is the digest length of the hash function, in bytes. For SHA-384, BLOCK_LENGTH is 64 and DIGEST_LENGTH is 48.

| Function  | Preconditions |  Postconditions |
| ---------------| -------------| --------------- |
| HMAC_CTX_init | <ul><li>The parameter is an allocated context.</li></ul> | <ul><li>The context is returned to its zeroized state.</li></ul> |
| HMAC_Init_ex | <ul><li>The context is in its zeroized state. </li><li>The digest type points to the correct global EVP_MD, such as the value returned by EVP_sha384().</li><li>The key array contains at least `key_len` bytes.</li></ul> | <ul><li>The context is valid and initialized for HMAC with the desired hash function.</li><li>The internal buffer offsets are less than BLOCK_LENGTH and the internal buffer offset for `o_ctx` equals 0.</li></ul>  |
| HMAC_Update |  <ul><li>The context is valid. The internal buffer offsets are less than BLOCK_LENGTH. </li><li> The input buffer has at least `data_len` allocated bytes.</li></ul> | <ul><li>The HMAC context is valid and the state in the context has been correctly updated for each complete block as defined by the HMAC specification.</li><li> The internal buffer offsets are less than BLOCK_LENGTH and the internal buffer offset for `o_ctx` equals 0. </li></ul> |
| HMAC_Final | <ul><li>The context is valid. The internal buffer offsets are less than BLOCK_LENGTH. </li><li> The output buffer has at least DIGEST_LENGTH allocated bytes.</li><li> The length output pointer is either null or it points to an integer.</li></ul> | <ul><li>The output buffer holds the correct value as defined by the HMAC specification. This value is produced from the HMAC state and the remaining n bytes in the internal buffer.</li><li> If the output length pointer is non-null, it points to the value DIGEST_LENGTH.</li></ul> |
| HMAC | <ul><li>The digest type points to the correct global EVP_MD, such as the value returned by EVP_sha384().</li><li> The key array contains at least `key_len` bytes.</li><li>  The input buffer has at least `data_len` allocated bytes.</li><li> The output buffer has at least DIGEST_LENGTH allocated bytes. </li><li>The length output pointer is either null or it points to an integer.</li></ul> | <ul><li>The output buffer holds the correct  value as defined by the HMAC specification.</li><li> If the output length pointer is non-null, it points to the value DIGEST_LENGTH.</li></ul> |

## AES-KW(P)

The AES_(un)wrap_key_* functions are verified to have the following properties related to AES Key Wrap (and AES Key Wrap with Padding) using AES-256. These operations are defined in [NIST SP 800-38F](https://nvlpubs.nist.gov/nistpubs/SpecialPublications/NIST.SP.800-38F.pdf). For more detailed specifications, see [AES_KW.saw](SAW/proof/AES_KW/AES_KW.saw).

| Function  | Preconditions |  Postconditions |
| ---------------| -------------| --------------- |
| AES_wrap_key | <ul><li>The plaintext length is k, which is a multiple of 8 and at least 16.</li><li>The parameters are a 32-byte AES-256 key, an 8-byte initialization vector or null pointer, a k+8-byte output array, a k-byte input array, and the integer k.</li></ul> | <ul><li>The output buffer holds the value produced by the AES KW encrypt operation using the key, initialization vector(or default value 0xA6A6A6A6A6A6A6A6 if IV pointer is null), and input buffer.</li><li>The value returned is k+8.</li></ul> |
| AES_unwrap_key | <ul><li>The plaintext length is k, which is a multiple of 8 and at least 16.</li><li>The parameters are a 32-byte AES-256 key, an 8-byte initialization vector or null pointer, a k-byte output array, a k+8-byte input array, and the integer k+8.</li></ul> | <ul><li>The output buffer holds the value produced by the AES KW decrypt operation using the key, initialization vector(or default value 0xA6A6A6A6A6A6A6A6 if IV pointer is null), and input buffer.</li><li>If the AES KW decrypt operation should succeed, then the function returns k, otherwise it returns -1.</li></ul> |
| AES_wrap_key_padded | <ul><li>The plaintext length is k, which is an arbitrary positive integer. The integer p is the smallest non-negative value such that k+p is a multiple of 8.</li><li>The parameters are a 32-byte AES-256 key, a k+p+8-byte output array, a pointer to an integer which accepts the output length, the integer k+p+8, a k-byte input array, and the integer k.</li></ul> | <ul><li>The output buffer holds the value produced by the AES KWP encrypt operation using the key, the constant IV 0xA65959A6, and the input buffer.</li><li>The ouptut length integer holds the value k+p+8.</li><li>The value returned is 1.</li></ul> |
| AES_unwrap_key_padded | <ul><li>The plaintext length is k, which is an arbitrary positive integer. The integer p is the smallest non-negative value such that k+p is a multiple of 8.</li><li>The parameters are a 32-byte AES-256 key, a k+p-byte output array, a pointer to an integer which accepts the output length, the integer k+p, a k+p+8-byte input array, and the integer k+p+8.</li></ul> | <ul><li>The output buffer holds the value produced by the AES KWP decrypt operation using the key, the constant IV 0xA65959A6, and the input buffer.</li><li>The ouptut length integer holds the correct plaintext length k.</li><li>If the AES KWP decrypt operation should succeed, the function returns 1, otherwise it returns 0.</li></ul> |

## Elliptic Curve Keys and Parameters

The EVP_PKEY_* functions are verified to have the following properties related to EC using P-384. For more detailed specifications, see [evp-function-specs.saw](SAW/proof/ECDH/evp-function-specs.saw).

| Function  | Preconditions |  Postconditions |
| ----------| --------------| --------------- |
| EVP_PKEY_CTX_new_id | <ul><li> The parameter is EVP_PKEY_EC, the key type NID. </li></ul> | <ul><li> The returned EVP_PKEY_CTX is allocated for the EC key type, is in its zeroized state, and its key is set to the null EVP_PKEY. </li></ul> |
| EVP_PKEY_CTX_new | <ul><li> The parameter is a non-null EVP_PKEY of type EVP_PKEY_EC. </li></ul> | <ul><li> The returned EVP_PKEY_CTX is allocated for the EC key type, is in its zeroized state, and its key is set to the EVP_PKEY parameter. </li></ul> |
| EVP_PKEY_paramgen_init | <ul><li> The EVP_PKEY_CTX parameter is valid. </li><li> The operation parameter is EVP_PKEY_OP_PARAMGEN. </li></ul>| <ul><li> The EVP_PKEY_CTX operation is set to EVP_PKEY_OP_PARAMGEN. </li></ul> |
| EVP_PKEY_CTX_set_ec_paramgen_curve_nid | <ul><li> The EVP_PKEY_CTX parameter is valid (for the EC key type and the paramgen operation), and its curve is not set. </li><li> The curve NID parameter is NID_secp384r1. </li></ul> | <ul><li> The curve of EVP_PKEY_CTX is set to P384. </li></ul> |
| EVP_PKEY_paramgen | <ul><li> The EVP_PKEY_CTX parameter is valid (for the EC key type and the paramgen operation), and its curve is set to P384. </li><li>The output pointer points to null.</li></ul> | <ul><li> The output pointer holds a pointer to an EVP_PKEY that is allocated for the EC key type, its curve is set to P384, and its private and public keys are set to null. </li></ul> |
| EVP_PKEY_keygen_init | <ul><li> The EVP_PKEY_CTX parameter is valid. </li><li> The operation parameter is EVP_PKEY_OP_KEYGEN. </li></ul>| <ul><li> The EVP_PKEY_CTX operation is set to EVP_PKEY_OP_KEYGEN. </li></ul> |
| EVP_PKEY_keygen | <ul><li> The EVP_PKEY_CTX parameter is valid (for the EC key type and the keygen operation), and its curve is set to P384. </li><li>The output pointer points to null.</li></ul> | <ul><li> The output pointer holds a pointer to an EVP_PKEY that is allocated for the EC key type, its curve is set to P384, and its private and public keys are set to a correct P384 key pair. </li></ul> |

## ECDSA

The EVP_DigestSign*/EVP_DigestVerify* functions are verified to have the following properties related to ECDSA using P-384 and SHA-384. For more detailed specifications, see [evp-function-specs.saw](SAW/proof/ECDSA/evp-function-specs.saw). BLOCK_LENGTH is the block length of the hash function, in bytes. MAX_SIGNATURE_LENGTH is the maximum length of the signature in ASN1 format, in bytes. For ECDSA with P-384 and SHA-384, BLOCK_LENGTH is 64 and MAX_SIGNATURE_LENGTH is 104.

| Function  | Preconditions |  Postconditions |
| ----------| --------------| --------------- |
| EVP_DigestSignInit | <ul><li>The parameters are an allocated EVP_MD_CTX, a valid EVP_MD such as the value returned by EVP_sha384(), and an initialized EVP_PKEY containing a private EC_KEY </li></ul> | <ul><li>The context is valid and initialized for the sign operation with the given key and the given digest algorithm.</li></ul> |
| EVP_DigestVerifyInit | <ul><li>The parameters are an allocated EVP_MD_CTX, a valid EVP_MD such as the value returned by EVP_sha384(), and an initialized EVP_PKEY containing a public EC_KEY </li></ul> | <ul><li>The context is valid and initialized for the verify operation with the given key and the given digest algorithm.</li></ul> |
| EVP_DigestSignUpdate | <ul><li>The context is valid (for the sign operation).</li><li>The input buffer has at least `len` allocated bytes.</li></ul> | <ul><li>The hash state in the context has been correctly updated for each complete block as defined by the SHA-2 specification.</li></ul> |
| EVP_DigestVerifyUpdate | <ul><li>The context is valid (for the verify operation).</li><li>The input buffer has at least `len` allocated bytes.</li></ul> | <ul><li>The hash state in the context has been correctly updated for each complete block as defined by the SHA-2 specification.</li></ul> |
| EVP_DigestSignFinal | <ul><li>The context is valid (for the sign operation).</li><li> The output buffer has at least MAX_SIGNATURE_LENGTH allocated bytes.</li><li> The length output pointer points to the integer MAX_SIGNATURE_LENGTH.</li></ul> | <ul><li>The output buffer holds the correct signature in ASN1 format as defined by the ECDSA specification. This signature is produced from the hash value (as defined by the SHA-2 specification) and the private key.</li><li>The output length pointer points to the length of the signature in ASN1 format.</li></ul> |
| EVP_DigestVerifyFinal | <ul><li>The context is valid (for the verify operation).</li><li>The input buffer contains an ECDSA signature in ASN1 format.</li></ul> | <ul><li>The function returns 1 if the signature is valid as defined by the ECDSA specification, 0 otherwise. This signature is validated for the hash value (as defined by the SHA-2 specification) and the public key.</li></ul> |
| EVP_DigestSign | <ul><li>The context is valid (for the sign operation).</li><li> The output buffer has at least MAX_SIGNATURE_LENGTH allocated bytes.</li><li> The length output pointer points to the integer MAX_SIGNATURE_LENGTH.</li><li>The input buffer has at least `len` allocated bytes.</li></ul> | <ul><li>The output buffer holds the correct signature in ASN1 format as defined by the ECDSA specification. This signature is produced from the hash value (as defined by the SHA-2 specification) and the private key.</li><li>The output length pointer points to the length of the signature in ASN1 format.</li></ul> |
| EVP_DigestVerify | <ul><li>The context is valid (for the verify operation).</li><li>The input `sig` buffer contains an ECDSA signature in ASN1 format.</li><li>The input `data` buffer has at least `len` allocated bytes.</li></ul> | <ul><li>The function returns 1 if the signature is valid as defined by the ECDSA specification, 0 otherwise. This signature is validated for the hash value (as defined by the SHA-2 specification) and the public key.</li></ul> |

## ECDH

The EVP_PKEY_derive* functions are verified to have the following properties related to ECDH using P-384. For more detailed specifications, see [evp-function-specs.saw](SAW/proof/ECDH/evp-function-specs.saw).

| Function  | Preconditions |  Postconditions |
| ----------| --------------| --------------- |
| EVP_PKEY_derive_init | <ul><li> The EVP_PKEY_CTX parameter is valid. </li><li> The operation parameter is EVP_PKEY_OP_DERIVE. </li></ul>| <ul><li> The EVP_PKEY_CTX operation is set to EVP_PKEY_OP_DERIVE. </li></ul> |
| EVP_PKEY_derive_set_peer_spec | <ul><li> The EVP_PKEY_CTX parameter is valid (for the EC key type and the derive operation), and its key is set to a valid P384 EVP_PKEY. </li><li>The EVP_PKEY parameter is a valid P384 key. </li></ul> | <ul><li>The EVP_PKEY_CTX peer key is set to the EVP_PKEY parameter. </li></ul> |
| EVP_PKEY_derive | <ul><li>The EVP_PKEY_CTX parameter is valid (for the EC key type and the derive operation), its key is set to a valid P384 EVP_PKEY, and its peer key is set to valid P384 EVP_PKEY that passes the public key checks in `EC_KEY_check_fips`.</li><li> The key output buffer has at least 48 allocated bytes.</li><li>The length output pointer holds the integer 48.</li></ul> | <ul><li>The key output buffer holds the correct key as defined by the ECDH specification. This key is derived from the EVP_PKEY_CTX key and the EVP_PKEY_CTX peer key.</li><li>The length output pointer holds the integer 48.</li></ul> |

## HKDF with HMAC-SHA384

The HKDF_* functions are verified to have the following properties related to HKDF with HMAC-SHA384. For more detailed specifications, see [HKDF.saw](SAW/proof/KDF/HKDF.saw). DIGEST_LENGTH is the digest length of the hash function, in bytes. For HMAC-SHA384, DIGEST_LENGTH is 48.

| Function  | Preconditions |  Postconditions |
| ---------------| -------------| --------------- |
| HKDF_extract |  <ul><li>The secret buffer has at least `secret_len` allocated bytes. </li><li> The salt buffer has at least `salt_len` allocated bytes.</li><li>The output buffer has at least DIGEST_LENGTH allocated bytes.</li><li> The output length pointer is not null.</li></ul> | <ul><li>The output buffer holds the correct value as defined by the HKDF_extract specification.</li><li> The output length pointer points to the value DIGEST_LENGTH. </li></ul> |
| HKDF_expand |  <ul><li>The output buffer is allocated successfully. </li><li> The prk buffer has at least DIGEST_LENGTH allocated bytes.</li><li>The info buffer has at least `info_len` allocated bytes.</li></ul> | <ul><li>The output buffer holds the correct value as defined by the HKDF_expand specification.</li></ul> |
| HKDF | <ul><li>The output buffer is allocated successfully. </li><li>The secret buffer has at least `secret_len` allocated bytes. </li><li> The salt buffer has at least `salt_len` allocated bytes.</li><li>The info buffer has at least `info_len` allocated bytes.</li></ul> | <ul><li>The output buffer holds the correct value as defined by the HKDF specification.</li></ul> |
