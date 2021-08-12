# Porting from OpenSSL/BoringSSL to AWS-LC

When porting from OpenSSL to AWS-LC, most notes of BoringSSL [PORTING.md](/PORTING.md) are applicable except below:

* AWS-LC has replaced `OPENSSL_IS_BORINGSSL` with `OPENSSL_IS_AWSLC` to distinguish BoringSSL from AWS-LC.
