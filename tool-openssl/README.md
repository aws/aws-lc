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

## req

`-batch` suppresses DN and request-attribute prompts. With `prompt = no`, config values are used directly; with `-subj`, the supplied subject is used unchanged. Otherwise, fields listed in the configured DN/attribute sections use their `_value` or `_default` and fields without a value/default are omitted, in config order. `_value = .` omits a field, and an empty `_value` falls back to `_default`. Password sources such as `-passin stdin` remain explicit input reads, independent of `-batch`.

## pkcs12

`pkcs12` supports importing a bundle and extracting its certificates and private key:

```sh
openssl pkcs12 -nokeys -legacy -in bundle.p12 -password file:password.txt -out chain.pem
openssl pkcs12 -nodes -in bundle.p12 -passin pass:secret -out key_and_chain.pem
```

Supported options are `-in`, `-out`, `-nokeys`, `-nocerts`, `-nodes`, `-noout`, `-passin`, `-password`, `-passout`, `-legacy`, and `-help`. Input and output default to stdin and stdout. Password sources use the same `pass:`, `file:`, `env:`, `stdin`, and (on POSIX) `fd:` forms as the other commands. For import, `-password` overrides `-passin` regardless of their order, as in OpenSSL. `-legacy` is accepted as a no-op so OpenSSL 3 scripts keep working; this tool can already decrypt the RC2/3DES bags that flag loads the legacy provider for.

The entire bundle is parsed and authenticated before output is opened, so a failed import does not truncate `-out`. That is stricter than OpenSSL 1.1.x, which creates or truncates `-out` before parsing. A successful run still opens (and truncates) `-out` even when `-noout` or `-nocerts -nokeys` writes nothing, matching OpenSSL. Certificates are written first, then the private key, matching the output order of OpenSSL for bundles produced by `PKCS12_create`/`pkcs12 -export`. If a private key is to be output, either `-nodes` (unencrypted PKCS#8) or `-passout` (PKCS#8 encrypted with AES-256-CBC) is required; there is no interactive prompt. `-nodes` overrides `-passout`. An explicitly empty password uses `pass:`. Omitting both input password options attempts an empty password.

Import passwords must be valid UTF-8 and cannot contain characters outside the Basic Multilingual Plane; the underlying PKCS#12 parser does not support supplementary characters such as most emoji. The shared password helper rejects empty environment-variable values, so use `pass:` rather than `env:NAME` with an empty variable for an empty password.

Differences from OpenSSL: `-info`, `-clcerts`, `-cacerts`, `-twopass`, `-nomacver`, `-chain`, and interactive prompts are not implemented, and those unsupported options fail rather than being silently ignored. The `Bag Attributes`, `subject=`, and `issuer=` comment lines OpenSSL prints before each PEM block are omitted. The AWS-LC PKCS#12 parser is stricter than OpenSSL's in a few ways that surface here: bundles without a MAC (such as those produced by `openssl pkcs12 -export -nomac`) are rejected rather than imported with a warning, and bundles containing more than one private key are rejected. Like the other subcommands, this CLI's file reader caps input at 1 MiB.

### Export

```sh
openssl pkcs12 -export -inkey key.pem -in cert.pem -certfile chain.pem -name server -keypbe PBE-SHA1-3DES -certpbe PBE-SHA1-3DES -passout pass:secret -out bundle.p12
openssl pkcs12 -export -in combined.pem -passin pass:key-secret -password pass:bundle-secret -out bundle.p12
```

`-export` reads PEM and writes DER PKCS#12. Without `-inkey`, the private key is read from `-in`, including combined key/certificate input on stdin. The first certificate from `-in` matching the key becomes the leaf; the remaining certificates retain their order, followed by all certificates from `-certfile`. No chain building or validation is performed. `-name` sets the key and leaf's friendlyName, and the library links them with the same localKeyID for consumers such as Java `keytool`.

`-passin` decrypts the input key. On export, `-password` overrides `-passout` regardless of order and does not supply `-passin`. These alias rules match `apps/pkcs12.c` in `OpenSSL_1_1_1w` and `openssl-3.0.16`. All password-source forms listed above work. Omitted passwords are empty, with no interactive prompt; unlike this CLI, OpenSSL normally prompts when the export password is omitted. Use an explicit password for password-protected deployment artifacts.

Export defaults follow OpenSSL 1.1.1: `PBE-SHA1-3DES` for keys, `PBE-SHA1-RC2-40` for certificates, and a SHA1 MAC. Both encryption and MAC iteration counts default to 2048. AWS-LC's `PKCS12_create` cannot generate the PBES2/AES bags used by OpenSSL 3 defaults, so this CLI does not claim those defaults or silently substitute legacy encryption for an explicit AES request. `-keypbe` and `-certpbe` support `PBE-SHA1-3DES`, `PBE-SHA1-RC2-40`, and `NONE` (unencrypted); PBES2 cipher names and other algorithms fail explicitly. `-descert` sets the certificate PBE to 3DES; the last `-descert`/`-certpbe` wins. RC2-40 and `NONE` are compatibility options, not recommended protection for new deployments.

Iteration options follow OpenSSL 3, which introduced `-iter`: a positive `-iter N` sets both counts, `-noiter` sets encryption iterations to 1, `-nomaciter` sets MAC iterations to 1 (it does not remove the MAC), and `-maciter` is a no-op. Options are processed in order. OpenSSL 1.1.1 differs only in that `-maciter` resets MAC iterations to 2048 and `-iter` is unavailable.

`-nokeys` omits the key; `-nocerts` omits certificates from `-in` but, like OpenSSL, still includes explicitly supplied `-certfile` certificates. `-nodes` is ignored with a warning during export; use `-keypbe NONE` to omit key encryption. `-noout` or `-nokeys -nocerts` fails with nothing to export. `-legacy` remains a no-op. Export-only flags require `-export` rather than being ignored on import. Unsupported export flags, including `-chain`, `-caname`, `-macalg`, `-nomac`, `-CSP`, `-LMK`, `-keyex`, and `-keysig`, fail argument parsing.

All inputs and passwords are validated and the complete PKCS#12 object is built before output is opened, so validation failures preserve an existing `-out`. Input and output may name the same file.
