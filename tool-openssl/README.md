# OpenSSL Tools for AWS-LC
*Files expected to change*

Current status:
* Contains initial implementation for OpenSSL x509, rsa, and md5 tools
  * x509 options: -in -out, -req, -signkey, -modulus, -days, -dates,
    -checkend, -noout (x509.cc)
  * rsa options: -in, -out, -noout, -modulus (rsa.cc)
  * md5 options: N/A (md5.cc)
* Unit, integration, and OpenSSL comparison tests (x509_test.cc, rsa_test.cc, md5_test.cc)
  * OpenSSL comparison tests require environment variables for both AWS-LC ("AWSLC_TOOL_PATH") and OpenSSL ("OPENSSL_TOOL_PATH") tools

