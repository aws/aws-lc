# Porting from OpenSSL/BoringSSL to AWS-LC

AWS-LC is a OpenSSL/BoringSSL derivative and is mostly source-compatible. 

The `OPENSSL_IS_AWSLC` macro can be used to distinguish OpenSSL/BoringSSL from
AWSLC in configure scripts. Do not use the presence or absence of particular
symbols to detect AWS-LC.
