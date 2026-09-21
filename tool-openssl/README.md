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
  * Tests that connect to a live, remote host (s_client_integration_test.cc) are built into the `integration_test` executable, not `tool_openssl_test`

## Notable differences from OpenSSL

### verify

`-CAfile` and `-CApath` may be used independently or together; an explicit path replaces the default for that source, and `-no-CAfile`/`-no-CApath` disable the corresponding default (but not an explicit path). Defaults honor `SSL_CERT_FILE` and `SSL_CERT_DIR`. CA directories must be indexed by subject hash, as produced by `openssl rehash`.

`-purpose` checks certificate key usage/EKU and, for purposes with a corresponding trust type (such as `sslserver` and `sslclient`), the auxiliary trust/reject attributes in `TRUSTED CERTIFICATE` PEM trust anchors. `-purpose any` retains the default trust check rather than selecting a purpose-specific trust type.

Exit status follows OpenSSL: 1 for option or trust store setup errors (including a `-CApath` that is not a directory), 2 when any input certificate fails to load or verify. `-verbose` is accepted and has no effect.

### x509

`-subject` prints names in modern OpenSSL's `CN=value` form (no spaces around `=`). `-nameopt oneline` restores the previous `CN = value` form.

`-nameopt` accepts only the case-insensitive presets `compat`, `oneline`, `RFC2253`, and `multiline`, not OpenSSL's comma-separated individual flags. When given, it also governs the Issuer/Subject lines of `-text`; otherwise `-text` output is unchanged. `compat` uses `X509_NAME_oneline`, which does not mark multi-valued RDNs with `+`; use `RFC2253` when that distinction matters.
