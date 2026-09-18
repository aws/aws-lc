# System Crypto Policies

Built with `-DENABLE_CRYPTO_POLICIES=ON`, AWS-LC seeds every new `SSL_CTX` from the
system-wide `crypto-policies` policy. This document compares that behavior with
what the framework expects of a back-end and with what OpenSSL does with the same
file. See [BUILDING.md](../BUILDING.md) for the build flag, the path overrides, and
AWS-LC's own `AWSLC.PostQuantum` directive.

## The framework

`crypto-policies` is a Fedora project ([documentation][fedora-docs],
[source][upstream]) shipped by Fedora, RHEL, and Amazon Linux 2023. An
administrator selects one policy, optionally with subpolicies
(`update-crypto-policies --set DEFAULT:PQ`), and the framework renders it into one
configuration file per consumer under `/etc/crypto-policies/back-ends/`. Amazon
Linux 2023 ships fourteen, covering BIND, GnuTLS, Java, Kerberos, Libreswan,
libssh, NSS, OpenSSH, OpenSSL, and RPM.

AWS-LC reads exactly one of them: `opensslcnf.config`, the OpenSSL
configuration-file back-end, which is a symlink into
`/usr/share/crypto-policies/<POLICY>/`. The `openssl.config` and
`openssl_fips.config` back-ends drive the `openssl` command-line tool; AWS-LC
ignores those along with every back-end belonging to another library.

## Directives

| Directive | AWS-LC |
| --- | --- |
| `CipherString` | applied as the TLS 1.2 and below cipher list; an `@SECLEVEL=N` prefix is parsed and dropped |
| `Ciphersuites` | applied as the TLS 1.3 cipher suites |
| `TLS.MinProtocol`, `TLS.MaxProtocol` | applied as the version bounds of a TLS context; a `MinProtocol` AWS-LC cannot resolve raises the floor to `MaxProtocol` |
| `DTLS.MinProtocol`, `DTLS.MaxProtocol` | applied as the version bounds of a DTLS context, under the same rule |
| `Groups` | filtered to the groups AWS-LC implements, in the policy's order |
| `SignatureAlgorithms` | filtered to the algorithms AWS-LC implements, in the policy's order |
| anything else | ignored |

Seeding cannot fail an application's startup. A missing or unreadable file, an
unparsable line, a value longer than AWS-LC's buffers, and a directive AWS-LC
cannot satisfy all leave the built-in default in force. A context created from a
version-locked method such as `TLSv1_2_method` keeps its pinned version and takes
no bounds from the policy.

A `MinProtocol` is the one directive that does not simply fall back. AWS-LC's
built-in floor of TLS 1.0 sits below any floor a policy can ask for, so leaving it
would offer the versions the policy forbids. A `MinProtocol` AWS-LC cannot resolve
therefore raises the floor to `MaxProtocol`, and one naming a protocol older than
TLS 1.0 keeps the built-in floor, which is already stricter.

## List syntax

`Groups` and `SignatureAlgorithms` carry OpenSSL 3.5 list syntax, and a stock
policy uses all of it. Amazon Linux 2023 renders `DEFAULT:PQ` with two modifiers on
its first group and a tuple boundary in the middle of the list:

```
Groups = *?X25519MLKEM768:?x25519_mlkem768:?SecP256r1MLKEM768:?p256_mlkem768:?SecP384r1MLKEM1024:?p384_mlkem1024/*X25519:secp256r1:X448:secp521r1:secp384r1:ffdhe2048:ffdhe3072:ffdhe4096:ffdhe6144:ffdhe8192
```

| Syntax | OpenSSL | AWS-LC |
| --- | --- | --- |
| `*` | send a key share for this group | stripped; AWS-LC selects its own key shares |
| `?` | tolerate a name the library does not implement | stripped; AWS-LC tolerates every name |
| `-` | remove the entry | removes it from AWS-LC's default list |
| `/` | separate preference tuples | another entry boundary; AWS-LC keeps one flat preference list |
| a name the library does not implement | rejects the whole list unless the name carries `?` | dropped, keeping the rest of the list |

The last row is why the lists are filtered rather than applied verbatim: every
stock policy names something AWS-LC does not implement -- X448 and the FFDHE
groups, Ed448, the RSA-PSS-PSS algorithms, the SHA-224 pairs -- and AWS-LC's
setters, like OpenSSL's, reject a list on the first name they do not recognize.
Applying such a value as written would silently discard the operator's whole
preference order.

## Against OpenSSL on the same host

| | OpenSSL 3.5 on Amazon Linux 2023 | AWS-LC with `-DENABLE_CRYPTO_POLICIES=ON` |
| --- | --- | --- |
| Reaches the policy through | an `.include` of the back-end file from `/etc/pki/tls/openssl.cnf` | opening the back-end file directly |
| Applies it | once, when the library reads its configuration | in each `SSL_CTX_new` |
| The rest of `openssl.cnf` | honored | ignored; AWS-LC reads no other system configuration |
| `@SECLEVEL=N` | enforced | parsed and dropped; AWS-LC has no security levels |
| Post-quantum under a policy silent about it | none offered | AWS-LC's own defaults stay |

## Post-quantum

Upstream Fedora ships a `NO-PQ` subpolicy, which removes every ML-KEM group and
ML-DSA algorithm, and no `PQ` one: post-quantum key exchange is in its `DEFAULT`
and an operator opts out of it. Amazon Linux 2023 and RHEL 9 invert that. Their
`DEFAULT` says nothing about post-quantum algorithms and an opt-in `PQ` subpolicy
adds them.

AWS-LC's group and signature-algorithm setters replace its defaults rather than
intersect with them, so a policy silent about post-quantum algorithms would strip
ML-KEM and ML-DSA from every context. AWS-LC keeps its own when the policy names
none, and stands aside when the policy names any: under `DEFAULT:PQ` the operator's
order wins, ML-KEM hybrids first among the groups and ML-DSA ahead of the classical
signature algorithms.

The `PQ` module also names `MLKEM1024-X448` and the composite ML-DSA signatures,
which AWS-LC does not implement. Neither reaches the OpenSSL back-end file, since
OpenSSL 3.5 does not implement them either, so on Amazon Linux 2023 the rendered
policy names only post-quantum algorithms AWS-LC has.

## Amazon Linux 2023

Amazon Linux 2023 ships four policies -- `DEFAULT`, `FIPS`, `FUTURE`, `LEGACY` --
and eight subpolicy modules, `PQ` among them. All four policies set
`TLS.MinProtocol = TLSv1.2` and `TLS.MaxProtocol = TLSv1.3`, so seeding raises a
context's floor from AWS-LC's TLS 1.0 and leaves its ceiling where it was. They
differ in cipher string, in security level, and in groups: `FIPS` names neither
X25519 nor Ed25519, and `FUTURE` drops `ffdhe2048` and requires `@SECLEVEL=3`,
which AWS-LC ignores.

The `FIPS` policy narrows what a context negotiates and nothing more. A
FIPS-validated build of AWS-LC is a separate matter, selected with `-DFIPS=1`.

[fedora-docs]: https://docs.fedoraproject.org/en-US/security/cryptography/policies/
[upstream]: https://gitlab.com/redhat-crypto/fedora-crypto-policies
