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

## pkcs12 (import only)

`pkcs12` supports importing a bundle and extracting its certificates and private key:

```sh
openssl pkcs12 -nokeys -legacy -in bundle.p12 -password file:password.txt -out chain.pem
openssl pkcs12 -nodes -in bundle.p12 -passin pass:secret -out key_and_chain.pem
```

Supported options are `-in`, `-out`, `-nokeys`, `-nocerts`, `-nodes`, `-noout`, `-passin`, `-password`, `-passout`, `-legacy`, and `-help`. Input and output default to stdin and stdout. Password sources use the same `pass:`, `file:`, `env:`, `stdin`, and (on POSIX) `fd:` forms as the other commands. For import, `-password` overrides `-passin` regardless of their order, as in OpenSSL. `-legacy` is accepted as a no-op so OpenSSL 3 scripts keep working; this tool can already decrypt the RC2/3DES bags that flag loads the legacy provider for.

The entire bundle is parsed and authenticated before output is opened, so a failed import does not truncate `-out`. That is stricter than OpenSSL 1.1.x, which creates or truncates `-out` before parsing. A successful run still opens (and truncates) `-out` even when `-noout` or `-nocerts -nokeys` writes nothing, matching OpenSSL. Certificates are written first, then the private key, matching the output order of OpenSSL for bundles produced by `PKCS12_create`/`pkcs12 -export`. If a private key is to be output, either `-nodes` (unencrypted PKCS#8) or `-passout` (PKCS#8 encrypted with AES-256-CBC) is required; there is no interactive prompt. `-nodes` overrides `-passout`. An explicitly empty password uses `pass:`. Omitting both input password options attempts an empty password.

Import passwords must be valid UTF-8 and cannot contain characters outside the Basic Multilingual Plane; the underlying PKCS#12 parser does not support supplementary characters such as most emoji. The shared password helper rejects empty environment-variable values, so use `pass:` rather than `env:NAME` with an empty variable for an empty password.

Differences from OpenSSL: `-export`, `-info`, `-clcerts`, `-cacerts`, `-twopass`, `-nomacver`, `-chain`, `-descert`, and interactive prompts are not implemented, and those unsupported options fail rather than being silently ignored. The `Bag Attributes`, `subject=`, and `issuer=` comment lines OpenSSL prints before each PEM block are omitted. The AWS-LC PKCS#12 parser is stricter than OpenSSL's in a few ways that surface here: bundles without a MAC (such as those produced by `openssl pkcs12 -export -nomac`) are rejected rather than imported with a warning, and bundles containing more than one private key are rejected. Like the other subcommands, this CLI's file reader caps input at 1 MiB.
