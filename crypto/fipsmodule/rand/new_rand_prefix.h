// Prefix some symbols.
// Delete when promoting "new rand" to default choice.

#ifndef OPENSSL_HEADER_CRYPTO_RAND_LOCAL_PREFIX_INTERNAL_H
#define OPENSSL_HEADER_CRYPTO_RAND_LOCAL_PREFIX_INTERNAL_H

#define NR_CONCAT(x,y) x##_##y
#define NR_PREFIX(x) NR_CONCAT(new_rand,x)

#define RAND_bytes_with_additional_data NR_PREFIX(RAND_bytes_with_additional_data)
#define RAND_bytes NR_PREFIX(RAND_bytes)
#define RAND_priv_bytes NR_PREFIX(RAND_priv_bytes)
#define RAND_pseudo_bytes NR_PREFIX(RAND_pseudo_bytes)

#endif // OPENSSL_HEADER_CRYPTO_RAND_LOCAL_PREFIX_INTERNAL_H

#if defined(NEW_RAND_UNPREFIX)

#if 0
#define poc_RAND_bytes_with_additional_data RAND_bytes_with_additional_data 
#define poc_RAND_bytes RAND_bytes 
#define poc_RAND_priv_bytes RAND_priv_bytes 
#define poc_RAND_pseudo_bytes RAND_pseudo_bytes 
#endif

#undef RAND_bytes_with_additional_data
#undef RAND_bytes
#undef RAND_priv_bytes
#undef RAND_pseudo_bytes

#endif