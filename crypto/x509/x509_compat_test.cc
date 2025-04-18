// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <gtest/gtest.h>

#include <openssl/x509.h>

#include "../internal.h"
#include "../test/test_util.h"
#include "../test/x509_util.h"

/*

The default root certificate key, "ROOT_KEY_1", used for self-signed
roots, unless otherwise specified. This is EC prime256v1 key.
-----BEGIN PRIVATE KEY-----
MIGHAgEAMBMGByqGSM49AgEGCCqGSM49AwEHBG0wawIBAQQgfVMH4tqIaJ6OzyxY
mqWXNwmK7gpXYDFhX80mXKgzrGGhRANCAATCqXrfbdTjFimzdBHxj71Ejcc/stea
5xAU/xxK+s77yXzB5lfy/zEbcYxuOrnwHrWsX9sugWgCy74ZRNWJPTDW
-----END PRIVATE KEY-----

The default intermediate certificate key, "INT_KEY_1", used for intermediate certs,
unless otherwise specified. This is EC prime256v1 key.

-----BEGIN PRIVATE KEY-----
MIGHAgEAMBMGByqGSM49AgEGCCqGSM49AwEHBG0wawIBAQQgi8u0pAYRFQMfuPFA
lZbxzOm4ZKQ0WovdzFj+CzdvnzOhRANCAASeZNGM4efwO6Ui3wQtVProzLEi54vG
YNlyza0aFtw0n5noIoCV3hlbCk7W1kdat0QyFz9rMoDlDjXLaGLE3THR
-----END PRIVATE KEY-----

The default end-entity certificate key, "EE_KEY_1", used for ee certs,
unless otherwise specified. This is EC prime256v1 key.
-----BEGIN PRIVATE KEY-----
MIGHAgEAMBMGByqGSM49AgEGCCqGSM49AwEHBG0wawIBAQQgfVMH4tqIaJ6OzyxY
mqWXNwmK7gpXYDFhX80mXKgzrGGhRANCAATCqXrfbdTjFimzdBHxj71Ejcc/stea
5xAU/xxK+s77yXzB5lfy/zEbcYxuOrnwHrWsX9sugWgCy74ZRNWJPTDW
-----END PRIVATE KEY-----
*/

/*
This self-signed root certificate's basicConstraints extension
cA:false. The root certificate though has the keyCertSign bit set for the
keyUsage extension. This is in violation of RFC 5280 4.2.1.9:
"If the cA boolean is not asserted, then the keyCertSign bit in the key
usage extension MUST NOT be asserted"

Certificate:
    Data:
        Version: 3 (0x2)
        Serial Number:
            0b:1e:77:95:de:6d:eb:b6:ab:2b:c4:51:3c:a6:70:02:99:f7:e5:f3
        Signature Algorithm: ecdsa-with-SHA256
        Issuer: C = US, ST = Washington, O = AWS Libcrypto, OU = Bad CA, CN = RFC 5280 4.2.1.9 cA:false
        Validity
            Not Before: Jan  1 00:00:00 2015 GMT
            Not After : Jan  1 00:00:00 2100 GMT
        Subject: C = US, ST = Washington, O = AWS Libcrypto, OU = Bad CA, CN = RFC 5280 4.2.1.9 cA:false
        Subject Public Key Info:
            Public Key Algorithm: id-ecPublicKey
                Public-Key: (256 bit)
                pub:
                    04:c2:a9:7a:df:6d:d4:e3:16:29:b3:74:11:f1:8f:
                    bd:44:8d:c7:3f:b2:d7:9a:e7:10:14:ff:1c:4a:fa:
                    ce:fb:c9:7c:c1:e6:57:f2:ff:31:1b:71:8c:6e:3a:
                    b9:f0:1e:b5:ac:5f:db:2e:81:68:02:cb:be:19:44:
                    d5:89:3d:30:d6
                ASN1 OID: prime256v1
                NIST CURVE: P-256
        X509v3 extensions:
            X509v3 Key Usage: critical
                Certificate Sign
            X509v3 Basic Constraints: critical
                CA:FALSE
            X509v3 Subject Key Identifier:
                19:19:E1:8C:09:E2:5D:5C:16:04:E1:9C:74:66:19:FD:B8:52:5B:DF
    Signature Algorithm: ecdsa-with-SHA256
    Signature Value:
        30:45:02:20:55:72:9f:65:36:59:eb:0f:c4:50:d0:d7:fb:58:
        3e:54:5e:dc:bf:7e:37:a8:a4:9c:41:a8:91:91:ae:ce:39:ff:
        02:21:00:8b:d0:01:0d:89:6f:61:4b:7a:ec:85:d4:ef:80:13:
        bd:52:44:ae:cd:56:32:08:5d:37:44:32:ac:50:f2:cb:c1
*/
static const char kRootBadBasicConstraints[] = R"(
-----BEGIN CERTIFICATE-----
MIICITCCAcegAwIBAgIUCx53ld5t67arK8RRPKZwApn35fMwCgYIKoZIzj0EAwIw
bzELMAkGA1UEBhMCVVMxEzARBgNVBAgMCldhc2hpbmd0b24xFjAUBgNVBAoMDUFX
UyBMaWJjcnlwdG8xDzANBgNVBAsMBkJhZCBDQTEiMCAGA1UEAwwZUkZDIDUyODAg
NC4yLjEuOSBjQTpmYWxzZTAgFw0xNTAxMDEwMDAwMDBaGA8yMTAwMDEwMTAwMDAw
MFowbzELMAkGA1UEBhMCVVMxEzARBgNVBAgMCldhc2hpbmd0b24xFjAUBgNVBAoM
DUFXUyBMaWJjcnlwdG8xDzANBgNVBAsMBkJhZCBDQTEiMCAGA1UEAwwZUkZDIDUy
ODAgNC4yLjEuOSBjQTpmYWxzZTBZMBMGByqGSM49AgEGCCqGSM49AwEHA0IABMKp
et9t1OMWKbN0EfGPvUSNxz+y15rnEBT/HEr6zvvJfMHmV/L/MRtxjG46ufAetaxf
2y6BaALLvhlE1Yk9MNajPzA9MA4GA1UdDwEB/wQEAwICBDAMBgNVHRMBAf8EAjAA
MB0GA1UdDgQWBBQZGeGMCeJdXBYE4Zx0Zhn9uFJb3zAKBggqhkjOPQQDAgNIADBF
AiBVcp9lNlnrD8RQ0Nf7WD5UXty/fjeopJxBqJGRrs45/wIhAIvQAQ2Jb2FLeuyF
1O+AE71SRK7NVjIIXTdEMqxQ8svB
-----END CERTIFICATE-----
)";

/*
This is an EE certificate signed by |kRootBadBasicConstraints|.
This should not be considered valid as the kRootBadBasicConstraints is a v3
certificate which has a basicConstraints extension indicating that it is not
a CA, and it violates the RFC 5280 condition.

Certificate:
    Data:
        Version: 3 (0x2)
        Serial Number:
            7b:8e:6c:6e:5a:d0:53:59:e7:fc:e2:93:b3:f4:19:16:1e:c3:81:82
        Signature Algorithm: ecdsa-with-SHA256
        Issuer: C = US, ST = Washington, O = AWS Libcrypto, OU = Bad CA, CN = RFC 5280 4.2.1.9 cA:false
        Validity
            Not Before: Jan  1 00:00:00 2015 GMT
            Not After : Jan  1 00:00:00 2100 GMT
        Subject: C = US, ST = Washington, O = AWS Libcrypto, OU = Bad Endpoint, CN = RFC 5280 4.2.1.9 cA:false
        Subject Public Key Info:
            Public Key Algorithm: id-ecPublicKey
                Public-Key: (256 bit)
                pub:
                    04:b2:b7:bd:35:f2:eb:da:86:d5:dc:40:44:c7:23:
                    14:f9:d0:a5:40:17:30:85:b6:c6:11:38:c2:db:2c:
                    c5:bc:0c:19:11:d8:68:61:d6:a3:92:6b:8a:18:52:
                    2c:dc:86:a7:ad:29:ad:91:ac:7e:df:87:24:3b:f3:
                    b4:71:2b:4e:58
                ASN1 OID: prime256v1
                NIST CURVE: P-256
        X509v3 extensions:
            X509v3 Key Usage: critical
                Digital Signature, Key Encipherment
            X509v3 Basic Constraints: critical
                CA:FALSE
            X509v3 Extended Key Usage:
                TLS Web Server Authentication, TLS Web Client Authentication
            X509v3 Subject Key Identifier:
                C8:78:64:E9:F7:9C:0F:56:E2:1D:CE:EE:ED:24:E0:9F:1D:4B:A3:BF
            X509v3 Authority Key Identifier:
                19:19:E1:8C:09:E2:5D:5C:16:04:E1:9C:74:66:19:FD:B8:52:5B:DF
    Signature Algorithm: ecdsa-with-SHA256
    Signature Value:
        30:45:02:20:38:ca:c4:54:ed:fc:bb:76:60:e9:4e:b5:85:91:
        f8:dc:a5:6a:54:9b:d2:22:a4:2c:6e:a6:df:fd:00:85:c0:06:
        02:21:00:ee:15:23:50:40:1b:67:b0:eb:13:75:6e:29:66:b0:
        e6:58:cf:1f:c2:5e:a1:85:01:45:9c:4d:ab:e7:61:ac:70
*/
static const char kEndEntitySignedByBadRoot[] = R"(
-----BEGIN CERTIFICATE-----
MIICZzCCAg2gAwIBAgIUe45sblrQU1nn/OKTs/QZFh7DgYIwCgYIKoZIzj0EAwIw
bzELMAkGA1UEBhMCVVMxEzARBgNVBAgMCldhc2hpbmd0b24xFjAUBgNVBAoMDUFX
UyBMaWJjcnlwdG8xDzANBgNVBAsMBkJhZCBDQTEiMCAGA1UEAwwZUkZDIDUyODAg
NC4yLjEuOSBjQTpmYWxzZTAgFw0xNTAxMDEwMDAwMDBaGA8yMTAwMDEwMTAwMDAw
MFowdTELMAkGA1UEBhMCVVMxEzARBgNVBAgMCldhc2hpbmd0b24xFjAUBgNVBAoM
DUFXUyBMaWJjcnlwdG8xFTATBgNVBAsMDEJhZCBFbmRwb2ludDEiMCAGA1UEAwwZ
UkZDIDUyODAgNC4yLjEuOSBjQTpmYWxzZTBZMBMGByqGSM49AgEGCCqGSM49AwEH
A0IABLK3vTXy69qG1dxARMcjFPnQpUAXMIW2xhE4wtssxbwMGRHYaGHWo5JrihhS
LNyGp60prZGsft+HJDvztHErTlijfzB9MA4GA1UdDwEB/wQEAwIFoDAMBgNVHRMB
Af8EAjAAMB0GA1UdJQQWMBQGCCsGAQUFBwMBBggrBgEFBQcDAjAdBgNVHQ4EFgQU
yHhk6fecD1biHc7u7STgnx1Lo78wHwYDVR0jBBgwFoAUGRnhjAniXVwWBOGcdGYZ
/bhSW98wCgYIKoZIzj0EAwIDSAAwRQIgOMrEVO38u3Zg6U61hZH43KVqVJvSIqQs
bqbf/QCFwAYCIQDuFSNQQBtnsOsTdW4pZrDmWM8fwl6hhQFFnE2r52GscA==
-----END CERTIFICATE-----
)";

/*
The is a valid root certificate that is expected to pass validation.
It may be used as a trust-anchor for both good or bad intermediate or
client certificates in testing.

Certificate:
    Data:
        Version: 3 (0x2)
        Serial Number:
            2e:0f:2e:da:e3:11:b2:fa:42:b3:29:09:b0:cc:93:87:ac:15:25:3d
        Signature Algorithm: ecdsa-with-SHA256
        Issuer: C = US, ST = Washington, O = AWS Libcrypto, OU = Good CA, CN = Root CA 1
        Validity
            Not Before: Jan  1 00:00:00 2015 GMT
            Not After : Jan  1 00:00:00 2100 GMT
        Subject: C = US, ST = Washington, O = AWS Libcrypto, OU = Good CA, CN = Root CA 1
        Subject Public Key Info:
            Public Key Algorithm: id-ecPublicKey
                Public-Key: (256 bit)
                    04:c2:a9:7a:df:6d:d4:e3:16:29:b3:74:11:f1:8f:
                    bd:44:8d:c7:3f:b2:d7:9a:e7:10:14:ff:1c:4a:fa:
                    ce:fb:c9:7c:c1:e6:57:f2:ff:31:1b:71:8c:6e:3a:
                    b9:f0:1e:b5:ac:5f:db:2e:81:68:02:cb:be:19:44:
                    d5:89:3d:30:d6
                ASN1 OID: prime256v1
                NIST CURVE: P-256
        X509v3 extensions:
            X509v3 Key Usage: critical
                Digital Signature, Certificate Sign, CRL Sign
            X509v3 Basic Constraints: critical
                CA:TRUE
            X509v3 Subject Key Identifier:
                19:19:E1:8C:09:E2:5D:5C:16:04:E1:9C:74:66:19:FD:B8:52:5B:DF
    Signature Algorithm: ecdsa-with-SHA256
    Signature Value:
        30:45:02:21:00:a4:39:29:1b:07:a2:3e:cc:21:eb:f6:5c:fd:
        b8:88:ee:79:46:37:25:e5:9a:79:2e:3d:2f:21:15:56:43:c8:
        b8:02:20:36:bd:03:bc:df:f6:7d:d2:a3:d2:a5:48:a8:64:75:
        00:4e:01:cd:67:b9:19:87:49:2b:bd:15:94:3e:f5:75:ca
*/
static const char kValidRootCA1[] = R"(
-----BEGIN CERTIFICATE-----
MIICBjCCAaygAwIBAgIULg8u2uMRsvpCsykJsMyTh6wVJT0wCgYIKoZIzj0EAwIw
YDELMAkGA1UEBhMCVVMxEzARBgNVBAgMCldhc2hpbmd0b24xFjAUBgNVBAoMDUFX
UyBMaWJjcnlwdG8xEDAOBgNVBAsMB0dvb2QgQ0ExEjAQBgNVBAMMCVJvb3QgQ0Eg
MTAgFw0xNTAxMDEwMDAwMDBaGA8yMTAwMDEwMTAwMDAwMFowYDELMAkGA1UEBhMC
VVMxEzARBgNVBAgMCldhc2hpbmd0b24xFjAUBgNVBAoMDUFXUyBMaWJjcnlwdG8x
EDAOBgNVBAsMB0dvb2QgQ0ExEjAQBgNVBAMMCVJvb3QgQ0EgMTBZMBMGByqGSM49
AgEGCCqGSM49AwEHA0IABMKpet9t1OMWKbN0EfGPvUSNxz+y15rnEBT/HEr6zvvJ
fMHmV/L/MRtxjG46ufAetaxf2y6BaALLvhlE1Yk9MNajQjBAMA4GA1UdDwEB/wQE
AwIBhjAPBgNVHRMBAf8EBTADAQH/MB0GA1UdDgQWBBQZGeGMCeJdXBYE4Zx0Zhn9
uFJb3zAKBggqhkjOPQQDAgNIADBFAiEApDkpGweiPswh6/Zc/biI7nlGNyXlmnku
PS8hFVZDyLgCIDa9A7zf9n3So9KlSKhkdQBOAc1nuRmHSSu9FZQ+9XXK
-----END CERTIFICATE-----
)";

/*
This is an EE certificate signed by |kValidRootCA1|, and is invalid as it
has an Authority Key Identifier (AKID) extension marked critical which
is not valid per RFC 5280 4.2.1.1:
"Conforming CAs MUST mark this extension as non-critical."

Certificate:
    Data:
        Version: 3 (0x2)
        Serial Number:
            27:8c:f7:17:16:47:56:c0:58:32:6c:dd:65:09:10:6b:44:bb:0e:a7
        Signature Algorithm: ecdsa-with-SHA256
        Issuer: C = US, ST = Washington, O = AWS Libcrypto, OU = Good CA, CN = Root CA 1
        Validity
            Not Before: Jan  1 00:00:00 2015 GMT
            Not After : Jan  1 00:00:00 2100 GMT
        Subject: C = US, ST = Washington, O = AWS Libcrypto, OU = Bad Endpoint, CN = RFC 5280 4.2.1.1 AKID MUST be non-critical
        Subject Public Key Info:
            Public Key Algorithm: id-ecPublicKey
                Public-Key: (256 bit)
                pub:
                    04:b2:b7:bd:35:f2:eb:da:86:d5:dc:40:44:c7:23:
                    14:f9:d0:a5:40:17:30:85:b6:c6:11:38:c2:db:2c:
                    c5:bc:0c:19:11:d8:68:61:d6:a3:92:6b:8a:18:52:
                    2c:dc:86:a7:ad:29:ad:91:ac:7e:df:87:24:3b:f3:
                    b4:71:2b:4e:58
                ASN1 OID: prime256v1
                NIST CURVE: P-256
        X509v3 extensions:
            X509v3 Key Usage: critical
                Digital Signature, Key Encipherment
            X509v3 Basic Constraints: critical
                CA:FALSE
            X509v3 Extended Key Usage:
                TLS Web Server Authentication, TLS Web Client Authentication
            X509v3 Authority Key Identifier: critical
                19:19:E1:8C:09:E2:5D:5C:16:04:E1:9C:74:66:19:FD:B8:52:5B:DF
            X509v3 Subject Key Identifier:
                C8:78:64:E9:F7:9C:0F:56:E2:1D:CE:EE:ED:24:E0:9F:1D:4B:A3:BF
    Signature Algorithm: ecdsa-with-SHA256
    Signature Value:
        30:46:02:21:00:9f:57:ba:de:8e:1a:82:1f:02:11:87:8d:00:
        fa:a2:eb:85:43:0d:c2:57:c6:12:c6:65:3b:e6:e9:aa:66:13:
        9e:02:21:00:fc:7f:a9:58:79:ba:bf:51:50:21:8f:f8:6e:89:
        c9:2c:14:fd:9f:9b:dd:f7:15:a9:6e:8d:9e:fe:0d:df:4e:35
*/
static const char kInvalidEECertificateWithCriticalAKID[] = R"(
-----BEGIN CERTIFICATE-----
MIICcDCCAhWgAwIBAgIUJ4z3FxZHVsBYMmzdZQkQa0S7DqcwCgYIKoZIzj0EAwIw
YDELMAkGA1UEBhMCVVMxEzARBgNVBAgMCldhc2hpbmd0b24xFjAUBgNVBAoMDUFX
UyBMaWJjcnlwdG8xEDAOBgNVBAsMB0dvb2QgQ0ExEjAQBgNVBAMMCVJvb3QgQ0Eg
MTAgFw0xNTAxMDEwMDAwMDBaGA8yMTAwMDEwMTAwMDAwMFowgYYxCzAJBgNVBAYT
AlVTMRMwEQYDVQQIDApXYXNoaW5ndG9uMRYwFAYDVQQKDA1BV1MgTGliY3J5cHRv
MRUwEwYDVQQLDAxCYWQgRW5kcG9pbnQxMzAxBgNVBAMMKlJGQyA1MjgwIDQuMi4x
LjEgQUtJRCBNVVNUIGJlIG5vbi1jcml0aWNhbDBZMBMGByqGSM49AgEGCCqGSM49
AwEHA0IABLK3vTXy69qG1dxARMcjFPnQpUAXMIW2xhE4wtssxbwMGRHYaGHWo5Jr
ihhSLNyGp60prZGsft+HJDvztHErTlijgYMwgYAwDgYDVR0PAQH/BAQDAgWgMAwG
A1UdEwEB/wQCMAAwHQYDVR0lBBYwFAYIKwYBBQUHAwEGCCsGAQUFBwMCMCIGA1Ud
IwEB/wQYMBaAFBkZ4YwJ4l1cFgThnHRmGf24UlvfMB0GA1UdDgQWBBTIeGTp95wP
VuIdzu7tJOCfHUujvzAKBggqhkjOPQQDAgNJADBGAiEAn1e63o4agh8CEYeNAPqi
64VDDcJXxhLGZTvm6apmE54CIQD8f6lYebq/UVAhj/huicksFP2fm933FalujZ7+
Dd9ONQ==
-----END CERTIFICATE-----
)";

/*
This certificate has a CRL Distribution Points extension, that per RFC 5280:
"The [CRL distribution points] extension SHOULD be non-critical, but this
profile RECOMMENDS support for this extension by CAs and applications."

OpenSSL 1.1.1 supports this extension being marked as critical, and will not
fail certificate verification because so.

Certificate:
    Data:
        Version: 3 (0x2)
        Serial Number:
            78:ea:d8:8b:b6:51:24:24:05:ed:24:af:8f:d5:1f:e2:43:bb:f6:1c
        Signature Algorithm: ecdsa-with-SHA256
        Issuer: C = US, ST = Washington, O = AWS Libcrypto, OU = Good CA, CN = Root CA 1
        Validity
            Not Before: Jan  1 00:00:00 2015 GMT
            Not After : Jan  1 00:00:00 2100 GMT
        Subject: C = US, ST = Washington, O = AWS Libcrypto, OU = Good Endpoint, CN = RFC 5280 4.2.1.13, SN = CRL distribution points ... extension SHOULD be non-critical
        Subject Public Key Info:
            Public Key Algorithm: id-ecPublicKey
                Public-Key: (256 bit)
                pub:
                    04:b2:b7:bd:35:f2:eb:da:86:d5:dc:40:44:c7:23:
                    14:f9:d0:a5:40:17:30:85:b6:c6:11:38:c2:db:2c:
                    c5:bc:0c:19:11:d8:68:61:d6:a3:92:6b:8a:18:52:
                    2c:dc:86:a7:ad:29:ad:91:ac:7e:df:87:24:3b:f3:
                    b4:71:2b:4e:58
                ASN1 OID: prime256v1
                NIST CURVE: P-256
        X509v3 extensions:
            X509v3 Key Usage: critical
                Digital Signature, Key Encipherment
            X509v3 Basic Constraints: critical
                CA:FALSE
            X509v3 Extended Key Usage:
                TLS Web Server Authentication, TLS Web Client Authentication
            X509v3 CRL Distribution Points: critical
                Full Name:
                  URI:http://example.com/crl
            X509v3 Subject Key Identifier:
                C8:78:64:E9:F7:9C:0F:56:E2:1D:CE:EE:ED:24:E0:9F:1D:4B:A3:BF
            X509v3 Authority Key Identifier:
                19:19:E1:8C:09:E2:5D:5C:16:04:E1:9C:74:66:19:FD:B8:52:5B:DF
    Signature Algorithm: ecdsa-with-SHA256
    Signature Value:
        30:46:02:21:00:cc:41:52:6e:40:01:46:d1:5e:4c:5b:23:27:
        55:ea:02:55:60:62:10:0c:9b:45:65:9a:a4:5b:9b:74:72:fa:
        c4:02:21:00:ba:2f:dc:ba:96:6d:ae:f3:19:3e:66:aa:18:9b:
        c5:ec:61:53:5a:d6:25:e5:66:bf:f3:9b:d6:d9:d2:e3:88:63
*/
static char kValidEECertWithCriticalCRLDistributionExt[] = R"(
-----BEGIN CERTIFICATE-----
MIICyDCCAm2gAwIBAgIUeOrYi7ZRJCQF7SSvj9Uf4kO79hwwCgYIKoZIzj0EAwIw
YDELMAkGA1UEBhMCVVMxEzARBgNVBAgMCldhc2hpbmd0b24xFjAUBgNVBAoMDUFX
UyBMaWJjcnlwdG8xEDAOBgNVBAsMB0dvb2QgQ0ExEjAQBgNVBAMMCVJvb3QgQ0Eg
MTAgFw0xNTAxMDEwMDAwMDBaGA8yMTAwMDEwMTAwMDAwMFowgbUxCzAJBgNVBAYT
AlVTMRMwEQYDVQQIDApXYXNoaW5ndG9uMRYwFAYDVQQKDA1BV1MgTGliY3J5cHRv
MRYwFAYDVQQLDA1Hb29kIEVuZHBvaW50MRowGAYDVQQDDBFSRkMgNTI4MCA0LjIu
MS4xMzFFMEMGA1UEBAw8Q1JMIGRpc3RyaWJ1dGlvbiBwb2ludHMgLi4uIGV4dGVu
c2lvbiBTSE9VTEQgYmUgbm9uLWNyaXRpY2FsMFkwEwYHKoZIzj0CAQYIKoZIzj0D
AQcDQgAEsre9NfLr2obV3EBExyMU+dClQBcwhbbGETjC2yzFvAwZEdhoYdajkmuK
GFIs3IanrSmtkax+34ckO/O0cStOWKOBrDCBqTAOBgNVHQ8BAf8EBAMCBaAwDAYD
VR0TAQH/BAIwADAdBgNVHSUEFjAUBggrBgEFBQcDAQYIKwYBBQUHAwIwKgYDVR0f
AQH/BCAwHjAcoBqgGIYWaHR0cDovL2V4YW1wbGUuY29tL2NybDAdBgNVHQ4EFgQU
yHhk6fecD1biHc7u7STgnx1Lo78wHwYDVR0jBBgwFoAUGRnhjAniXVwWBOGcdGYZ
/bhSW98wCgYIKoZIzj0EAwIDSQAwRgIhAMxBUm5AAUbRXkxbIydV6gJVYGIQDJtF
ZZqkW5t0cvrEAiEAui/cupZtrvMZPmaqGJvF7GFTWtYl5Wa/85vW2dLjiGM=
-----END CERTIFICATE-----
)";

/*
This is a v3 certificate that has the keyCertSign keyUsage bit set but is
missing the Basic Constraints extension. Per RFC 5280 4.2.1.9: "If the basic
constraints extension is not present in a version 3 certificate, or the
extension is present but the cA boolean is not asserted, then the certified
public key MUST NOT be used to verify certificate signatures."

Certificate:
    Data:
        Version: 3 (0x2)
        Serial Number:
            3e:d2:f9:bf:f8:43:a5:8a:69:cb:8f:6e:e6:29:43:a3:b8:be:2c:e1
        Signature Algorithm: ecdsa-with-SHA256
        Issuer: C = US, ST = Washington, O = AWS Libcrypto, OU = Bad CA, CN = RFC 528 4.2.1.9 not present, SN = MUST NOT be used to verify certificate signatures
        Validity
            Not Before: Jan  1 00:00:00 2015 GMT
            Not After : Jan  1 00:00:00 2100 GMT
        Subject: C = US, ST = Washington, O = AWS Libcrypto, OU = Bad CA, CN = RFC 528 4.2.1.9 not present, SN = MUST NOT be used to verify certificate signatures
        Subject Public Key Info:
            Public Key Algorithm: id-ecPublicKey
                Public-Key: (256 bit)
                pub:
                    04:c2:a9:7a:df:6d:d4:e3:16:29:b3:74:11:f1:8f:
                    bd:44:8d:c7:3f:b2:d7:9a:e7:10:14:ff:1c:4a:fa:
                    ce:fb:c9:7c:c1:e6:57:f2:ff:31:1b:71:8c:6e:3a:
                    b9:f0:1e:b5:ac:5f:db:2e:81:68:02:cb:be:19:44:
                    d5:89:3d:30:d6
                ASN1 OID: prime256v1
                NIST CURVE: P-256
        X509v3 extensions:
            X509v3 Key Usage: critical
                Digital Signature, Certificate Sign, CRL Sign
            X509v3 Subject Key Identifier:
                19:19:E1:8C:09:E2:5D:5C:16:04:E1:9C:74:66:19:FD:B8:52:5B:DF
    Signature Algorithm: ecdsa-with-SHA256
    Signature Value:
        30:44:02:20:35:fb:3a:0f:95:a5:bf:2d:bc:74:91:f9:f5:0f:
        bb:79:34:dc:e7:b5:cb:c4:21:5a:be:4d:10:e1:3e:97:e0:b8:
        02:20:54:2e:9c:98:89:3a:11:ec:7a:34:40:64:84:3f:b1:72:
        b1:bb:33:a2:d2:29:aa:ab:c1:1d:38:44:fa:62:fb:20
*/
static char kInvalidRootCertificateWithMissingBasicConstraintsExt[] = R"(
-----BEGIN CERTIFICATE-----
MIICkDCCAjegAwIBAgIUPtL5v/hDpYppy49u5ilDo7i+LOEwCgYIKoZIzj0EAwIw
ga0xCzAJBgNVBAYTAlVTMRMwEQYDVQQIDApXYXNoaW5ndG9uMRYwFAYDVQQKDA1B
V1MgTGliY3J5cHRvMQ8wDQYDVQQLDAZCYWQgQ0ExJDAiBgNVBAMMG1JGQyA1Mjgg
NC4yLjEuOSBub3QgcHJlc2VudDE6MDgGA1UEBAwxTVVTVCBOT1QgYmUgdXNlZCB0
byB2ZXJpZnkgY2VydGlmaWNhdGUgc2lnbmF0dXJlczAgFw0xNTAxMDEwMDAwMDBa
GA8yMTAwMDEwMTAwMDAwMFowga0xCzAJBgNVBAYTAlVTMRMwEQYDVQQIDApXYXNo
aW5ndG9uMRYwFAYDVQQKDA1BV1MgTGliY3J5cHRvMQ8wDQYDVQQLDAZCYWQgQ0Ex
JDAiBgNVBAMMG1JGQyA1MjggNC4yLjEuOSBub3QgcHJlc2VudDE6MDgGA1UEBAwx
TVVTVCBOT1QgYmUgdXNlZCB0byB2ZXJpZnkgY2VydGlmaWNhdGUgc2lnbmF0dXJl
czBZMBMGByqGSM49AgEGCCqGSM49AwEHA0IABMKpet9t1OMWKbN0EfGPvUSNxz+y
15rnEBT/HEr6zvvJfMHmV/L/MRtxjG46ufAetaxf2y6BaALLvhlE1Yk9MNajMTAv
MA4GA1UdDwEB/wQEAwIBhjAdBgNVHQ4EFgQUGRnhjAniXVwWBOGcdGYZ/bhSW98w
CgYIKoZIzj0EAwIDRwAwRAIgNfs6D5Wlvy28dJH59Q+7eTTc57XLxCFavk0Q4T6X
4LgCIFQunJiJOhHsejRAZIQ/sXKxuzOi0imqq8EdOET6Yvsg
-----END CERTIFICATE-----
)";

/*
This is a bad endpoint certificate that has been signed by
|kInvalidRootCertificateWithMissingBasicConstraintsExt| which is an invalid CA
due to it missing the Basic Constraints extension per RFC 528 4.2.1.9.

Certificate:
    Data:
        Version: 3 (0x2)
        Serial Number:
            64:73:40:dd:b0:f3:e9:45:6f:12:bf:f8:76:46:ef:77:f0:8d:02:2a
        Signature Algorithm: ecdsa-with-SHA256
        Issuer: C = US, ST = Washington, O = AWS Libcrypto, OU = Bad CA, CN = RFC 528 4.2.1.9 not present, SN = MUST NOT be used to verify certificate signatures
        Validity
            Not Before: Jan  1 00:00:00 2015 GMT
            Not After : Jan  1 00:00:00 2100 GMT
        Subject: C = US, ST = Washington, O = AWS Libcrypto, OU = Bad Endpoint, CN = RFC 528 4.2.1.9 not present, SN = MUST NOT be used to verify certificate signatures
        Subject Public Key Info:
            Public Key Algorithm: id-ecPublicKey
                Public-Key: (256 bit)
                pub:
                    04:b2:b7:bd:35:f2:eb:da:86:d5:dc:40:44:c7:23:
                    14:f9:d0:a5:40:17:30:85:b6:c6:11:38:c2:db:2c:
                    c5:bc:0c:19:11:d8:68:61:d6:a3:92:6b:8a:18:52:
                    2c:dc:86:a7:ad:29:ad:91:ac:7e:df:87:24:3b:f3:
                    b4:71:2b:4e:58
                ASN1 OID: prime256v1
                NIST CURVE: P-256
        X509v3 extensions:
            X509v3 Key Usage: critical
                Digital Signature, Key Encipherment
            X509v3 Basic Constraints: critical
                CA:FALSE
            X509v3 Extended Key Usage:
                TLS Web Server Authentication, TLS Web Client Authentication
            X509v3 Subject Key Identifier:
                C8:78:64:E9:F7:9C:0F:56:E2:1D:CE:EE:ED:24:E0:9F:1D:4B:A3:BF
            X509v3 Authority Key Identifier:
                19:19:E1:8C:09:E2:5D:5C:16:04:E1:9C:74:66:19:FD:B8:52:5B:DF
    Signature Algorithm: ecdsa-with-SHA256
    Signature Value:
        30:44:02:20:47:a2:ae:cc:22:a1:00:17:00:db:d6:f9:1d:73:
        09:c3:d4:cf:4f:f2:e0:2c:e9:3d:14:2f:46:c9:c7:73:c1:dd:
        02:20:3f:6a:d3:15:10:f6:38:fe:84:90:06:08:17:f7:cf:37:
        b7:9a:a2:6e:b1:ba:38:ba:ca:0f:c0:52:06:10:a5:4c
*/
static char kInvalidEECertificateSignedByRootMissingBasicConstraintsExt[] = R"(
-----BEGIN CERTIFICATE-----
MIIC5DCCAougAwIBAgIUZHNA3bDz6UVvEr/4dkbvd/CNAiowCgYIKoZIzj0EAwIw
ga0xCzAJBgNVBAYTAlVTMRMwEQYDVQQIDApXYXNoaW5ndG9uMRYwFAYDVQQKDA1B
V1MgTGliY3J5cHRvMQ8wDQYDVQQLDAZCYWQgQ0ExJDAiBgNVBAMMG1JGQyA1Mjgg
NC4yLjEuOSBub3QgcHJlc2VudDE6MDgGA1UEBAwxTVVTVCBOT1QgYmUgdXNlZCB0
byB2ZXJpZnkgY2VydGlmaWNhdGUgc2lnbmF0dXJlczAgFw0xNTAxMDEwMDAwMDBa
GA8yMTAwMDEwMTAwMDAwMFowgbMxCzAJBgNVBAYTAlVTMRMwEQYDVQQIDApXYXNo
aW5ndG9uMRYwFAYDVQQKDA1BV1MgTGliY3J5cHRvMRUwEwYDVQQLDAxCYWQgRW5k
cG9pbnQxJDAiBgNVBAMMG1JGQyA1MjggNC4yLjEuOSBub3QgcHJlc2VudDE6MDgG
A1UEBAwxTVVTVCBOT1QgYmUgdXNlZCB0byB2ZXJpZnkgY2VydGlmaWNhdGUgc2ln
bmF0dXJlczBZMBMGByqGSM49AgEGCCqGSM49AwEHA0IABLK3vTXy69qG1dxARMcj
FPnQpUAXMIW2xhE4wtssxbwMGRHYaGHWo5JrihhSLNyGp60prZGsft+HJDvztHEr
TlijfzB9MA4GA1UdDwEB/wQEAwIFoDAMBgNVHRMBAf8EAjAAMB0GA1UdJQQWMBQG
CCsGAQUFBwMBBggrBgEFBQcDAjAdBgNVHQ4EFgQUyHhk6fecD1biHc7u7STgnx1L
o78wHwYDVR0jBBgwFoAUGRnhjAniXVwWBOGcdGYZ/bhSW98wCgYIKoZIzj0EAwID
RwAwRAIgR6KuzCKhABcA29b5HXMJw9TPT/LgLOk9FC9Gycdzwd0CID9q0xUQ9jj+
hJAGCBf3zze3mqJusbo4usoPwFIGEKVM
-----END CERTIFICATE-----
)";

/*
This is technically an invalid certificate due to it having a negative serial
number which is not valid per RFC 5280 4.1.2.2: "The serial number MUST be a
positive integer assigned by the CA to each certificate".

Historically OpenSSL 1.1.1 supports negative serial numbers as had other
implementations.

Certificate is signed by |kValidRootCA1|.

Certificate:
    Data:
        Version: 3 (0x2)
        Serial Number: -1337 (-0x539)
        Signature Algorithm: ecdsa-with-SHA256
        Issuer: C = US, ST = Washington, O = AWS Libcrypto, OU = Good CA, CN = Root CA 1
        Validity
            Not Before: Jan  1 00:00:00 2015 GMT
            Not After : Jan  1 00:00:00 2100 GMT
        Subject: C = US, ST = Washington, O = AWS Libcrypto, OU = Bad Endpoint, CN = RFC 5280 serial number MUST be a positive integer
        Subject Public Key Info:
            Public Key Algorithm: id-ecPublicKey
                Public-Key: (256 bit)
                pub:
                    04:b2:b7:bd:35:f2:eb:da:86:d5:dc:40:44:c7:23:
                    14:f9:d0:a5:40:17:30:85:b6:c6:11:38:c2:db:2c:
                    c5:bc:0c:19:11:d8:68:61:d6:a3:92:6b:8a:18:52:
                    2c:dc:86:a7:ad:29:ad:91:ac:7e:df:87:24:3b:f3:
                    b4:71:2b:4e:58
                ASN1 OID: prime256v1
                NIST CURVE: P-256
        X509v3 extensions:
            X509v3 Key Usage: critical
                Digital Signature, Key Encipherment
            X509v3 Basic Constraints: critical
                CA:FALSE
            X509v3 Extended Key Usage:
                TLS Web Server Authentication, TLS Web Client Authentication
            X509v3 Subject Key Identifier:
                C8:78:64:E9:F7:9C:0F:56:E2:1D:CE:EE:ED:24:E0:9F:1D:4B:A3:BF
            X509v3 Authority Key Identifier:
                19:19:E1:8C:09:E2:5D:5C:16:04:E1:9C:74:66:19:FD:B8:52:5B:DF
    Signature Algorithm: ecdsa-with-SHA256
    Signature Value:
        30:45:02:21:00:a1:0d:15:19:11:bc:84:2f:9c:64:ae:c1:89:
        c6:37:90:df:c9:36:f0:bf:e5:4f:5b:53:54:48:55:dd:e0:f3:
        8c:02:20:21:22:ff:f5:9b:79:55:03:04:86:92:e1:c5:b2:11:
        6d:7f:f8:77:23:e4:c0:09:53:c0:01:07:3d:f5:00:77:ec
*/
static char kValidEECertificateWithNegativeSerialNumber[] = R"(
-----BEGIN CERTIFICATE-----
MIICXzCCAgWgAwIBAgIC+scwCgYIKoZIzj0EAwIwYDELMAkGA1UEBhMCVVMxEzAR
BgNVBAgMCldhc2hpbmd0b24xFjAUBgNVBAoMDUFXUyBMaWJjcnlwdG8xEDAOBgNV
BAsMB0dvb2QgQ0ExEjAQBgNVBAMMCVJvb3QgQ0EgMTAgFw0xNTAxMDEwMDAwMDBa
GA8yMTAwMDEwMTAwMDAwMFowgY0xCzAJBgNVBAYTAlVTMRMwEQYDVQQIDApXYXNo
aW5ndG9uMRYwFAYDVQQKDA1BV1MgTGliY3J5cHRvMRUwEwYDVQQLDAxCYWQgRW5k
cG9pbnQxOjA4BgNVBAMMMVJGQyA1MjgwIHNlcmlhbCBudW1iZXIgTVVTVCBiZSBh
IHBvc2l0aXZlIGludGVnZXIwWTATBgcqhkjOPQIBBggqhkjOPQMBBwNCAASyt701
8uvahtXcQETHIxT50KVAFzCFtsYROMLbLMW8DBkR2Ghh1qOSa4oYUizchqetKa2R
rH7fhyQ787RxK05Yo38wfTAOBgNVHQ8BAf8EBAMCBaAwDAYDVR0TAQH/BAIwADAd
BgNVHSUEFjAUBggrBgEFBQcDAQYIKwYBBQUHAwIwHQYDVR0OBBYEFMh4ZOn3nA9W
4h3O7u0k4J8dS6O/MB8GA1UdIwQYMBaAFBkZ4YwJ4l1cFgThnHRmGf24UlvfMAoG
CCqGSM49BAMCA0gAMEUCIQChDRUZEbyEL5xkrsGJxjeQ38k28L/lT1tTVEhV3eDz
jAIgISL/9Zt5VQMEhpLhxbIRbX/4dyPkwAlTwAEHPfUAd+w=
-----END CERTIFICATE-----
)";

/*
Intermediate CA signed by |kValidRootCA1|.

Certificate:
    Data:
        Version: 3 (0x2)
        Serial Number:
            1e:d3:b4:51:2e:cc:35:dd:ac:45:03:34:94:ff:5e:ae:a2:0c:c7:98
        Signature Algorithm: ecdsa-with-SHA256
        Issuer: C=US, ST=Washington, O=AWS Libcrypto, OU=Good CA, CN=Root CA 1
        Validity
            Not Before: Jan  1 00:00:00 2015 GMT
            Not After : Jan  1 00:00:00 2100 GMT
        Subject: C=US, ST=Washington, O=AWS Libcrypto, OU=Good CA, CN=Int NC CA 1
        Subject Public Key Info:
            Public Key Algorithm: id-ecPublicKey
                Public-Key: (256 bit)
                pub:
                    04:9e:64:d1:8c:e1:e7:f0:3b:a5:22:df:04:2d:54:
                    fa:e8:cc:b1:22:e7:8b:c6:60:d9:72:cd:ad:1a:16:
                    dc:34:9f:99:e8:22:80:95:de:19:5b:0a:4e:d6:d6:
                    47:5a:b7:44:32:17:3f:6b:32:80:e5:0e:35:cb:68:
                    62:c4:dd:31:d1
                ASN1 OID: prime256v1
                NIST CURVE: P-256
        X509v3 extensions:
            X509v3 Key Usage: critical
                Digital Signature, Certificate Sign, CRL Sign
            X509v3 Basic Constraints: critical
                CA:TRUE
            X509v3 Name Constraints:
                Permitted:
                  IP:10.1.0.0/255.255.0.0
                Excluded:
                  IP:10.1.1.0/255.255.255.0
            X509v3 Subject Key Identifier:
                B9:D1:CF:08:A5:F2:99:2B:5A:80:C9:78:23:78:D1:BC:79:70:9F:FB
            X509v3 Authority Key Identifier:
                19:19:E1:8C:09:E2:5D:5C:16:04:E1:9C:74:66:19:FD:B8:52:5B:DF
    Signature Algorithm: ecdsa-with-SHA256
    Signature Value:
        30:45:02:20:0d:0f:59:61:82:af:ad:7e:45:38:95:c7:76:17:
        34:5b:57:a7:00:1c:bc:b6:24:79:00:61:f5:a6:02:5f:a1:48:
        02:21:00:93:a0:2d:0e:6d:60:23:4d:0a:12:4d:a7:db:f4:f4:
        f0:4b:b7:d0:7c:6b:6c:95:9f:99:e3:15:b7:d3:76:d3:c0
*/
static char kValidIntCAWithIPv4NameConstraints[] = R"(
-----BEGIN CERTIFICATE-----
MIICUjCCAfigAwIBAgIUHtO0US7MNd2sRQM0lP9erqIMx5gwCgYIKoZIzj0EAwIw
YDELMAkGA1UEBhMCVVMxEzARBgNVBAgMCldhc2hpbmd0b24xFjAUBgNVBAoMDUFX
UyBMaWJjcnlwdG8xEDAOBgNVBAsMB0dvb2QgQ0ExEjAQBgNVBAMMCVJvb3QgQ0Eg
MTAgFw0xNTAxMDEwMDAwMDBaGA8yMTAwMDEwMTAwMDAwMFowYjELMAkGA1UEBhMC
VVMxEzARBgNVBAgMCldhc2hpbmd0b24xFjAUBgNVBAoMDUFXUyBMaWJjcnlwdG8x
EDAOBgNVBAsMB0dvb2QgQ0ExFDASBgNVBAMMC0ludCBOQyBDQSAxMFkwEwYHKoZI
zj0CAQYIKoZIzj0DAQcDQgAEnmTRjOHn8DulIt8ELVT66MyxIueLxmDZcs2tGhbc
NJ+Z6CKAld4ZWwpO1tZHWrdEMhc/azKA5Q41y2hixN0x0aOBizCBiDAOBgNVHQ8B
Af8EBAMCAYYwDwYDVR0TAQH/BAUwAwEB/zAlBgNVHR4EHjAcoAwwCocICgEAAP//
AAChDDAKhwgKAQEA////ADAdBgNVHQ4EFgQUudHPCKXymStagMl4I3jRvHlwn/sw
HwYDVR0jBBgwFoAUGRnhjAniXVwWBOGcdGYZ/bhSW98wCgYIKoZIzj0EAwIDSAAw
RQIgDQ9ZYYKvrX5FOJXHdhc0W1enABy8tiR5AGH1pgJfoUgCIQCToC0ObWAjTQoS
Tafb9PTwS7fQfGtslZ+Z4xW303bTwA==
-----END CERTIFICATE-----
)";

/*
End-entity certificate signed by |kValidIntCAWithIPv4NameConstraints|.

Certificate:
    Data:
        Version: 3 (0x2)
        Serial Number:
            3c:e0:97:cf:b4:c1:15:28:aa:a8:21:76:23:3b:ad:08:31:18:a5:4f
        Signature Algorithm: ecdsa-with-SHA256
        Issuer: C=US, ST=Washington, O=AWS Libcrypto, OU=Good CA, CN=Int NC CA 1
        Validity
            Not Before: Jan  1 00:00:00 2015 GMT
            Not After : Jan  1 00:00:00 2100 GMT
        Subject: C=US, ST=Washington, O=AWS Libcrypto, OU=Good Endpoint, CN=Permitted IP
        Subject Public Key Info:
            Public Key Algorithm: id-ecPublicKey
                Public-Key: (256 bit)
                pub:
                    04:b2:b7:bd:35:f2:eb:da:86:d5:dc:40:44:c7:23:
                    14:f9:d0:a5:40:17:30:85:b6:c6:11:38:c2:db:2c:
                    c5:bc:0c:19:11:d8:68:61:d6:a3:92:6b:8a:18:52:
                    2c:dc:86:a7:ad:29:ad:91:ac:7e:df:87:24:3b:f3:
                    b4:71:2b:4e:58
                ASN1 OID: prime256v1
                NIST CURVE: P-256
        X509v3 extensions:
            X509v3 Key Usage: critical
                Digital Signature, Key Encipherment
            X509v3 Basic Constraints: critical
                CA:FALSE
            X509v3 Extended Key Usage:
                TLS Web Server Authentication, TLS Web Client Authentication
            X509v3 Subject Alternative Name:
                DNS:example.com, IP Address:10.1.2.1
            X509v3 Subject Key Identifier:
                C8:78:64:E9:F7:9C:0F:56:E2:1D:CE:EE:ED:24:E0:9F:1D:4B:A3:BF
            X509v3 Authority Key Identifier:
                B9:D1:CF:08:A5:F2:99:2B:5A:80:C9:78:23:78:D1:BC:79:70:9F:FB
    Signature Algorithm: ecdsa-with-SHA256
    Signature Value:
        30:45:02:21:00:da:b5:af:58:58:38:69:be:d1:c0:38:b3:7c:
        2e:18:fe:5a:a8:7e:2b:85:44:b2:d8:66:78:bf:fa:b7:44:9d:
        a7:02:20:7a:80:35:24:95:08:5e:98:af:3e:4a:4a:a5:8d:11:
        06:90:cf:b8:34:25:04:94:86:a4:b4:9b:84:b9:61:00:65
*/
static char kValidEECertWithValidIPv4SubjectAltName[] = R"(
-----BEGIN CERTIFICATE-----
MIICbjCCAhSgAwIBAgIUPOCXz7TBFSiqqCF2IzutCDEYpU8wCgYIKoZIzj0EAwIw
YjELMAkGA1UEBhMCVVMxEzARBgNVBAgMCldhc2hpbmd0b24xFjAUBgNVBAoMDUFX
UyBMaWJjcnlwdG8xEDAOBgNVBAsMB0dvb2QgQ0ExFDASBgNVBAMMC0ludCBOQyBD
QSAxMCAXDTE1MDEwMTAwMDAwMFoYDzIxMDAwMTAxMDAwMDAwWjBpMQswCQYDVQQG
EwJVUzETMBEGA1UECAwKV2FzaGluZ3RvbjEWMBQGA1UECgwNQVdTIExpYmNyeXB0
bzEWMBQGA1UECwwNR29vZCBFbmRwb2ludDEVMBMGA1UEAwwMUGVybWl0dGVkIElQ
MFkwEwYHKoZIzj0CAQYIKoZIzj0DAQcDQgAEsre9NfLr2obV3EBExyMU+dClQBcw
hbbGETjC2yzFvAwZEdhoYdajkmuKGFIs3IanrSmtkax+34ckO/O0cStOWKOBnjCB
mzAOBgNVHQ8BAf8EBAMCBaAwDAYDVR0TAQH/BAIwADAdBgNVHSUEFjAUBggrBgEF
BQcDAQYIKwYBBQUHAwIwHAYDVR0RBBUwE4ILZXhhbXBsZS5jb22HBAoBAgEwHQYD
VR0OBBYEFMh4ZOn3nA9W4h3O7u0k4J8dS6O/MB8GA1UdIwQYMBaAFLnRzwil8pkr
WoDJeCN40bx5cJ/7MAoGCCqGSM49BAMCA0gAMEUCIQData9YWDhpvtHAOLN8Lhj+
Wqh+K4VEsthmeL/6t0SdpwIgeoA1JJUIXpivPkpKpY0RBpDPuDQlBJSGpLSbhLlh
AGU=
-----END CERTIFICATE-----
)";

/*
An invalid end-entity certificate signed by |kValidIntCAWithIPv4NameConstraints|
with an excluded IP address in the subject alternative name.

Certificate:
    Data:
        Version: 3 (0x2)
        Serial Number:
            33:19:62:14:a9:8a:02:74:a0:ba:55:ad:73:c9:a4:7e:83:ce:18:7e
        Signature Algorithm: ecdsa-with-SHA256
        Issuer: C=US, ST=Washington, O=AWS Libcrypto, OU=Good CA, CN=Int NC CA 1
        Validity
            Not Before: Jan  1 00:00:00 2015 GMT
            Not After : Jan  1 00:00:00 2100 GMT
        Subject: C=US, ST=Washington, O=AWS Libcrypto, OU=Bad Endpoint, CN=Excluded IP
        Subject Public Key Info:
            Public Key Algorithm: id-ecPublicKey
                Public-Key: (256 bit)
                pub:
                    04:b2:b7:bd:35:f2:eb:da:86:d5:dc:40:44:c7:23:
                    14:f9:d0:a5:40:17:30:85:b6:c6:11:38:c2:db:2c:
                    c5:bc:0c:19:11:d8:68:61:d6:a3:92:6b:8a:18:52:
                    2c:dc:86:a7:ad:29:ad:91:ac:7e:df:87:24:3b:f3:
                    b4:71:2b:4e:58
                ASN1 OID: prime256v1
                NIST CURVE: P-256
        X509v3 extensions:
            X509v3 Key Usage: critical
                Digital Signature, Key Encipherment
            X509v3 Basic Constraints: critical
                CA:FALSE
            X509v3 Extended Key Usage:
                TLS Web Server Authentication, TLS Web Client Authentication
            X509v3 Subject Alternative Name:
                DNS:example.com, IP Address:10.1.1.2
            X509v3 Subject Key Identifier:
                C8:78:64:E9:F7:9C:0F:56:E2:1D:CE:EE:ED:24:E0:9F:1D:4B:A3:BF
            X509v3 Authority Key Identifier:
                B9:D1:CF:08:A5:F2:99:2B:5A:80:C9:78:23:78:D1:BC:79:70:9F:FB
    Signature Algorithm: ecdsa-with-SHA256
    Signature Value:
        30:44:02:20:72:ec:70:f1:58:de:9c:66:8f:98:22:9d:ad:5a:
        b2:e2:4a:24:2f:82:43:0f:6d:17:e7:a6:3f:81:8a:e6:76:40:
        02:20:10:e0:6e:15:9b:9e:db:15:c8:39:5a:76:5f:17:f9:62:
        f3:8d:c7:87:0b:eb:bc:42:42:22:73:65:b5:82:01:91
*/
static char kInvalidEECertWithInvalidExcludedIPv4SubjAlt[] = R"(
-----BEGIN CERTIFICATE-----
MIICazCCAhKgAwIBAgIUMxliFKmKAnSgulWtc8mkfoPOGH4wCgYIKoZIzj0EAwIw
YjELMAkGA1UEBhMCVVMxEzARBgNVBAgMCldhc2hpbmd0b24xFjAUBgNVBAoMDUFX
UyBMaWJjcnlwdG8xEDAOBgNVBAsMB0dvb2QgQ0ExFDASBgNVBAMMC0ludCBOQyBD
QSAxMCAXDTE1MDEwMTAwMDAwMFoYDzIxMDAwMTAxMDAwMDAwWjBnMQswCQYDVQQG
EwJVUzETMBEGA1UECAwKV2FzaGluZ3RvbjEWMBQGA1UECgwNQVdTIExpYmNyeXB0
bzEVMBMGA1UECwwMQmFkIEVuZHBvaW50MRQwEgYDVQQDDAtFeGNsdWRlZCBJUDBZ
MBMGByqGSM49AgEGCCqGSM49AwEHA0IABLK3vTXy69qG1dxARMcjFPnQpUAXMIW2
xhE4wtssxbwMGRHYaGHWo5JrihhSLNyGp60prZGsft+HJDvztHErTlijgZ4wgZsw
DgYDVR0PAQH/BAQDAgWgMAwGA1UdEwEB/wQCMAAwHQYDVR0lBBYwFAYIKwYBBQUH
AwEGCCsGAQUFBwMCMBwGA1UdEQQVMBOCC2V4YW1wbGUuY29thwQKAQECMB0GA1Ud
DgQWBBTIeGTp95wPVuIdzu7tJOCfHUujvzAfBgNVHSMEGDAWgBS50c8IpfKZK1qA
yXgjeNG8eXCf+zAKBggqhkjOPQQDAgNHADBEAiBy7HDxWN6cZo+YIp2tWrLiSiQv
gkMPbRfnpj+BiuZ2QAIgEOBuFZue2xXIOVp2Xxf5YvONx4cL67xCQiJzZbWCAZE=
-----END CERTIFICATE-----
)";

/*
Signed by |kValidIntCAWithIPv4NameConstraints|, but with an invalid permitted ip address.

Certificate:
    Data:
        Version: 3 (0x2)
        Serial Number:
            7a:15:18:c0:d9:39:b6:d9:8e:9a:29:87:d8:6a:ad:ce:5b:90:cc:49
        Signature Algorithm: ecdsa-with-SHA256
        Issuer: C=US, ST=Washington, O=AWS Libcrypto, OU=Good CA, CN=Int NC CA 1
        Validity
            Not Before: Jan  1 00:00:00 2015 GMT
            Not After : Jan  1 00:00:00 2100 GMT
        Subject: C=US, ST=Washington, O=AWS Libcrypto, OU=Bad Endpoint, CN=Not Permitted IP
        Subject Public Key Info:
            Public Key Algorithm: id-ecPublicKey
                Public-Key: (256 bit)
                pub:
                    04:b2:b7:bd:35:f2:eb:da:86:d5:dc:40:44:c7:23:
                    14:f9:d0:a5:40:17:30:85:b6:c6:11:38:c2:db:2c:
                    c5:bc:0c:19:11:d8:68:61:d6:a3:92:6b:8a:18:52:
                    2c:dc:86:a7:ad:29:ad:91:ac:7e:df:87:24:3b:f3:
                    b4:71:2b:4e:58
                ASN1 OID: prime256v1
                NIST CURVE: P-256
        X509v3 extensions:
            X509v3 Key Usage: critical
                Digital Signature, Key Encipherment
            X509v3 Basic Constraints: critical
                CA:FALSE
            X509v3 Extended Key Usage:
                TLS Web Server Authentication, TLS Web Client Authentication
            X509v3 Subject Alternative Name:
                DNS:example.com, IP Address:10.2.0.1
            X509v3 Subject Key Identifier:
                C8:78:64:E9:F7:9C:0F:56:E2:1D:CE:EE:ED:24:E0:9F:1D:4B:A3:BF
            X509v3 Authority Key Identifier:
                B9:D1:CF:08:A5:F2:99:2B:5A:80:C9:78:23:78:D1:BC:79:70:9F:FB
    Signature Algorithm: ecdsa-with-SHA256
    Signature Value:
        30:45:02:21:00:de:8a:39:0b:90:fe:1b:37:f3:9f:ab:60:77:
        58:8b:79:1b:3a:06:ed:dc:91:85:98:b5:21:44:d5:a6:da:04:
        e9:02:20:22:60:af:9d:79:56:4c:bf:50:ae:eb:93:ac:fd:6e:
        d1:f9:60:d5:24:0e:09:00:33:8c:f1:46:6a:69:f8:24:03
*/
static char kInvalidEECertWithInvalidPermittedIPv4SubjAlt[] = R"(
-----BEGIN CERTIFICATE-----
MIICcTCCAhegAwIBAgIUehUYwNk5ttmOmimH2GqtzluQzEkwCgYIKoZIzj0EAwIw
YjELMAkGA1UEBhMCVVMxEzARBgNVBAgMCldhc2hpbmd0b24xFjAUBgNVBAoMDUFX
UyBMaWJjcnlwdG8xEDAOBgNVBAsMB0dvb2QgQ0ExFDASBgNVBAMMC0ludCBOQyBD
QSAxMCAXDTE1MDEwMTAwMDAwMFoYDzIxMDAwMTAxMDAwMDAwWjBsMQswCQYDVQQG
EwJVUzETMBEGA1UECAwKV2FzaGluZ3RvbjEWMBQGA1UECgwNQVdTIExpYmNyeXB0
bzEVMBMGA1UECwwMQmFkIEVuZHBvaW50MRkwFwYDVQQDDBBOb3QgUGVybWl0dGVk
IElQMFkwEwYHKoZIzj0CAQYIKoZIzj0DAQcDQgAEsre9NfLr2obV3EBExyMU+dCl
QBcwhbbGETjC2yzFvAwZEdhoYdajkmuKGFIs3IanrSmtkax+34ckO/O0cStOWKOB
njCBmzAOBgNVHQ8BAf8EBAMCBaAwDAYDVR0TAQH/BAIwADAdBgNVHSUEFjAUBggr
BgEFBQcDAQYIKwYBBQUHAwIwHAYDVR0RBBUwE4ILZXhhbXBsZS5jb22HBAoCAAEw
HQYDVR0OBBYEFMh4ZOn3nA9W4h3O7u0k4J8dS6O/MB8GA1UdIwQYMBaAFLnRzwil
8pkrWoDJeCN40bx5cJ/7MAoGCCqGSM49BAMCA0gAMEUCIQDeijkLkP4bN/Ofq2B3
WIt5GzoG7dyRhZi1IUTVptoE6QIgImCvnXlWTL9QruuTrP1u0flg1SQOCQAzjPFG
amn4JAM=
-----END CERTIFICATE-----
)";

/*
Signed by |kValidRootCA1|.

Certificate:
    Data:
        Version: 3 (0x2)
        Serial Number:
            5b:f2:ea:34:90:86:19:ae:89:9d:e7:81:9b:37:4d:93:8e:32:10:48
        Signature Algorithm: ecdsa-with-SHA256
        Issuer: C=US, ST=Washington, O=AWS Libcrypto, OU=Good CA, CN=Root CA 1
        Validity
            Not Before: Jan  1 00:00:00 2015 GMT
            Not After : Jan  1 00:00:00 2100 GMT
        Subject: C=US, ST=Washington, O=AWS Libcrypto, OU=Good CA, CN=Int NC CA 2
        Subject Public Key Info:
            Public Key Algorithm: id-ecPublicKey
                Public-Key: (256 bit)
                pub:
                    04:9e:64:d1:8c:e1:e7:f0:3b:a5:22:df:04:2d:54:
                    fa:e8:cc:b1:22:e7:8b:c6:60:d9:72:cd:ad:1a:16:
                    dc:34:9f:99:e8:22:80:95:de:19:5b:0a:4e:d6:d6:
                    47:5a:b7:44:32:17:3f:6b:32:80:e5:0e:35:cb:68:
                    62:c4:dd:31:d1
                ASN1 OID: prime256v1
                NIST CURVE: P-256
        X509v3 extensions:
            X509v3 Key Usage: critical
                Digital Signature, Certificate Sign, CRL Sign
            X509v3 Basic Constraints: critical
                CA:TRUE
            X509v3 Name Constraints:
                Permitted:
                  IP:0:0:0:0:0:FFFF:A01:0/FFFF:FFFF:FFFF:FFFF:FFFF:FFFF:FFFF:0
                Excluded:
                  IP:0:0:0:0:0:FFFF:A01:100/FFFF:FFFF:FFFF:FFFF:FFFF:FFFF:FFFF:FF00
            X509v3 Subject Key Identifier:
                B9:D1:CF:08:A5:F2:99:2B:5A:80:C9:78:23:78:D1:BC:79:70:9F:FB
            X509v3 Authority Key Identifier:
                19:19:E1:8C:09:E2:5D:5C:16:04:E1:9C:74:66:19:FD:B8:52:5B:DF
    Signature Algorithm: ecdsa-with-SHA256
    Signature Value:
        30:45:02:20:22:a0:76:63:1e:2b:a6:f7:f3:e7:ba:ca:23:65:
        f6:ed:7e:c5:e2:84:5a:81:70:58:d3:33:2c:0a:5c:c6:0a:a0:
        02:21:00:f3:87:b7:3f:e6:3b:fe:a2:00:c9:b7:e2:a0:5e:52:
        36:ce:25:39:83:55:bb:45:55:95:09:47:a5:2e:20:85:42
*/
static char kValidIntCAWithIPv6NameConstraints[] = R"(
-----BEGIN CERTIFICATE-----
MIICgjCCAiigAwIBAgIUW/LqNJCGGa6JneeBmzdNk44yEEgwCgYIKoZIzj0EAwIw
YDELMAkGA1UEBhMCVVMxEzARBgNVBAgMCldhc2hpbmd0b24xFjAUBgNVBAoMDUFX
UyBMaWJjcnlwdG8xEDAOBgNVBAsMB0dvb2QgQ0ExEjAQBgNVBAMMCVJvb3QgQ0Eg
MTAgFw0xNTAxMDEwMDAwMDBaGA8yMTAwMDEwMTAwMDAwMFowYjELMAkGA1UEBhMC
VVMxEzARBgNVBAgMCldhc2hpbmd0b24xFjAUBgNVBAoMDUFXUyBMaWJjcnlwdG8x
EDAOBgNVBAsMB0dvb2QgQ0ExFDASBgNVBAMMC0ludCBOQyBDQSAyMFkwEwYHKoZI
zj0CAQYIKoZIzj0DAQcDQgAEnmTRjOHn8DulIt8ELVT66MyxIueLxmDZcs2tGhbc
NJ+Z6CKAld4ZWwpO1tZHWrdEMhc/azKA5Q41y2hixN0x0aOBuzCBuDAOBgNVHQ8B
Af8EBAMCAYYwDwYDVR0TAQH/BAUwAwEB/zBVBgNVHR4ETjBMoCQwIocgAAAAAAAA
AAAAAP//CgEAAP//////////////////AAChJDAihyAAAAAAAAAAAAAA//8KAQEA
////////////////////ADAdBgNVHQ4EFgQUudHPCKXymStagMl4I3jRvHlwn/sw
HwYDVR0jBBgwFoAUGRnhjAniXVwWBOGcdGYZ/bhSW98wCgYIKoZIzj0EAwIDSAAw
RQIgIqB2Yx4rpvfz57rKI2X27X7F4oRagXBY0zMsClzGCqACIQDzh7c/5jv+ogDJ
t+KgXlI2ziU5g1W7RVWVCUelLiCFQg==
-----END CERTIFICATE-----
)";

/*
Certificate:
    Data:
        Version: 3 (0x2)
        Serial Number:
            50:69:9a:a0:95:99:2f:a6:e6:b1:72:93:88:56:64:bd:33:98:83:92
        Signature Algorithm: ecdsa-with-SHA256
        Issuer: C=US, ST=Washington, O=AWS Libcrypto, OU=Good CA, CN=Int NC CA 2
        Validity
            Not Before: Jan  1 00:00:00 2015 GMT
            Not After : Jan  1 00:00:00 2100 GMT
        Subject: C=US, ST=Washington, O=AWS Libcrypto, OU=Good Endpoint, CN=Permitted IPv6
        Subject Public Key Info:
            Public Key Algorithm: id-ecPublicKey
                Public-Key: (256 bit)
                pub:
                    04:b2:b7:bd:35:f2:eb:da:86:d5:dc:40:44:c7:23:
                    14:f9:d0:a5:40:17:30:85:b6:c6:11:38:c2:db:2c:
                    c5:bc:0c:19:11:d8:68:61:d6:a3:92:6b:8a:18:52:
                    2c:dc:86:a7:ad:29:ad:91:ac:7e:df:87:24:3b:f3:
                    b4:71:2b:4e:58
                ASN1 OID: prime256v1
                NIST CURVE: P-256
        X509v3 extensions:
            X509v3 Key Usage: critical
                Digital Signature, Key Encipherment
            X509v3 Basic Constraints: critical
                CA:FALSE
            X509v3 Extended Key Usage:
                TLS Web Server Authentication, TLS Web Client Authentication
            X509v3 Subject Alternative Name:
                DNS:example.com, IP Address:0:0:0:0:0:FFFF:A01:201
            X509v3 Subject Key Identifier:
                C8:78:64:E9:F7:9C:0F:56:E2:1D:CE:EE:ED:24:E0:9F:1D:4B:A3:BF
            X509v3 Authority Key Identifier:
                B9:D1:CF:08:A5:F2:99:2B:5A:80:C9:78:23:78:D1:BC:79:70:9F:FB
    Signature Algorithm: ecdsa-with-SHA256
    Signature Value:
        30:44:02:20:06:7e:89:4d:f3:c0:9f:bc:8d:1c:b7:10:43:a4:
        06:dc:63:b3:29:d3:96:bb:b8:15:a6:f3:8f:28:75:6b:a6:f0:
        02:20:49:7f:ce:91:3d:44:0e:f4:c8:22:c0:c1:fe:f0:e1:a4:
        55:31:29:24:30:40:06:27:29:51:89:1a:aa:a9:7e:4e
*/
static char kValidEECertWithValidIPv6SubjectAltName[] = R"(
-----BEGIN CERTIFICATE-----
MIICezCCAiKgAwIBAgIUUGmaoJWZL6bmsXKTiFZkvTOYg5IwCgYIKoZIzj0EAwIw
YjELMAkGA1UEBhMCVVMxEzARBgNVBAgMCldhc2hpbmd0b24xFjAUBgNVBAoMDUFX
UyBMaWJjcnlwdG8xEDAOBgNVBAsMB0dvb2QgQ0ExFDASBgNVBAMMC0ludCBOQyBD
QSAyMCAXDTE1MDEwMTAwMDAwMFoYDzIxMDAwMTAxMDAwMDAwWjBrMQswCQYDVQQG
EwJVUzETMBEGA1UECAwKV2FzaGluZ3RvbjEWMBQGA1UECgwNQVdTIExpYmNyeXB0
bzEWMBQGA1UECwwNR29vZCBFbmRwb2ludDEXMBUGA1UEAwwOUGVybWl0dGVkIElQ
djYwWTATBgcqhkjOPQIBBggqhkjOPQMBBwNCAASyt7018uvahtXcQETHIxT50KVA
FzCFtsYROMLbLMW8DBkR2Ghh1qOSa4oYUizchqetKa2RrH7fhyQ787RxK05Yo4Gq
MIGnMA4GA1UdDwEB/wQEAwIFoDAMBgNVHRMBAf8EAjAAMB0GA1UdJQQWMBQGCCsG
AQUFBwMBBggrBgEFBQcDAjAoBgNVHREEITAfggtleGFtcGxlLmNvbYcQAAAAAAAA
AAAAAP//CgECATAdBgNVHQ4EFgQUyHhk6fecD1biHc7u7STgnx1Lo78wHwYDVR0j
BBgwFoAUudHPCKXymStagMl4I3jRvHlwn/swCgYIKoZIzj0EAwIDRwAwRAIgBn6J
TfPAn7yNHLcQQ6QG3GOzKdOWu7gVpvOPKHVrpvACIEl/zpE9RA70yCLAwf7w4aRV
MSkkMEAGJylRiRqqqX5O
-----END CERTIFICATE-----
)";

/*
Certificate:
    Data:
        Version: 3 (0x2)
        Serial Number:
            15:a5:1d:5a:37:04:67:db:0c:ff:14:fe:5e:48:6b:fe:bb:d3:13:6c
        Signature Algorithm: ecdsa-with-SHA256
        Issuer: C=US, ST=Washington, O=AWS Libcrypto, OU=Good CA, CN=Int NC CA 2
        Validity
            Not Before: Jan  1 00:00:00 2015 GMT
            Not After : Jan  1 00:00:00 2100 GMT
        Subject: C=US, ST=Washington, O=AWS Libcrypto, OU=Good Endpoint, CN=Excluded IPv6
        Subject Public Key Info:
            Public Key Algorithm: id-ecPublicKey
                Public-Key: (256 bit)
                pub:
                    04:b2:b7:bd:35:f2:eb:da:86:d5:dc:40:44:c7:23:
                    14:f9:d0:a5:40:17:30:85:b6:c6:11:38:c2:db:2c:
                    c5:bc:0c:19:11:d8:68:61:d6:a3:92:6b:8a:18:52:
                    2c:dc:86:a7:ad:29:ad:91:ac:7e:df:87:24:3b:f3:
                    b4:71:2b:4e:58
                ASN1 OID: prime256v1
                NIST CURVE: P-256
        X509v3 extensions:
            X509v3 Key Usage: critical
                Digital Signature, Key Encipherment
            X509v3 Basic Constraints: critical
                CA:FALSE
            X509v3 Extended Key Usage:
                TLS Web Server Authentication, TLS Web Client Authentication
            X509v3 Subject Alternative Name:
                DNS:example.com, IP Address:0:0:0:0:0:FFFF:A01:102
            X509v3 Subject Key Identifier:
                C8:78:64:E9:F7:9C:0F:56:E2:1D:CE:EE:ED:24:E0:9F:1D:4B:A3:BF
            X509v3 Authority Key Identifier:
                B9:D1:CF:08:A5:F2:99:2B:5A:80:C9:78:23:78:D1:BC:79:70:9F:FB
    Signature Algorithm: ecdsa-with-SHA256
    Signature Value:
        30:44:02:20:4c:76:bd:2e:df:89:c9:be:78:53:f7:71:d6:85:
        49:a0:f7:5e:c6:ed:f5:f2:88:be:3f:dc:ad:19:ab:bd:ec:ee:
        02:20:0d:ad:b4:45:a4:3d:c3:e5:f4:16:56:40:0b:5e:33:10:
        e6:4e:49:a6:9d:c3:eb:27:bf:3e:98:cd:d5:87:ce:db
*/
static char kInvalidEECertWithInvalidExcludedIPv6SubjAlt[] = R"(
-----BEGIN CERTIFICATE-----
MIICejCCAiGgAwIBAgIUFaUdWjcEZ9sM/xT+Xkhr/rvTE2wwCgYIKoZIzj0EAwIw
YjELMAkGA1UEBhMCVVMxEzARBgNVBAgMCldhc2hpbmd0b24xFjAUBgNVBAoMDUFX
UyBMaWJjcnlwdG8xEDAOBgNVBAsMB0dvb2QgQ0ExFDASBgNVBAMMC0ludCBOQyBD
QSAyMCAXDTE1MDEwMTAwMDAwMFoYDzIxMDAwMTAxMDAwMDAwWjBqMQswCQYDVQQG
EwJVUzETMBEGA1UECAwKV2FzaGluZ3RvbjEWMBQGA1UECgwNQVdTIExpYmNyeXB0
bzEWMBQGA1UECwwNR29vZCBFbmRwb2ludDEWMBQGA1UEAwwNRXhjbHVkZWQgSVB2
NjBZMBMGByqGSM49AgEGCCqGSM49AwEHA0IABLK3vTXy69qG1dxARMcjFPnQpUAX
MIW2xhE4wtssxbwMGRHYaGHWo5JrihhSLNyGp60prZGsft+HJDvztHErTlijgaow
gacwDgYDVR0PAQH/BAQDAgWgMAwGA1UdEwEB/wQCMAAwHQYDVR0lBBYwFAYIKwYB
BQUHAwEGCCsGAQUFBwMCMCgGA1UdEQQhMB+CC2V4YW1wbGUuY29thxAAAAAAAAAA
AAAA//8KAQECMB0GA1UdDgQWBBTIeGTp95wPVuIdzu7tJOCfHUujvzAfBgNVHSME
GDAWgBS50c8IpfKZK1qAyXgjeNG8eXCf+zAKBggqhkjOPQQDAgNHADBEAiBMdr0u
34nJvnhT93HWhUmg917G7fXyiL4/3K0Zq73s7gIgDa20RaQ9w+X0FlZAC14zEOZO
Saadw+snvz6YzdWHzts=
-----END CERTIFICATE-----
)";

/*
Certificate:
    Data:
        Version: 3 (0x2)
        Serial Number:
            75:62:5c:30:b0:0e:c2:19:c0:ae:5d:f1:32:70:09:9c:7f:0e:db:d1
        Signature Algorithm: ecdsa-with-SHA256
        Issuer: C=US, ST=Washington, O=AWS Libcrypto, OU=Good CA, CN=Int NC CA 2
        Validity
            Not Before: Jan  1 00:00:00 2015 GMT
            Not After : Jan  1 00:00:00 2100 GMT
        Subject: C=US, ST=Washington, O=AWS Libcrypto, OU=Bad Endpoint, CN=Not Permitted IPv6
        Subject Public Key Info:
            Public Key Algorithm: id-ecPublicKey
                Public-Key: (256 bit)
                pub:
                    04:b2:b7:bd:35:f2:eb:da:86:d5:dc:40:44:c7:23:
                    14:f9:d0:a5:40:17:30:85:b6:c6:11:38:c2:db:2c:
                    c5:bc:0c:19:11:d8:68:61:d6:a3:92:6b:8a:18:52:
                    2c:dc:86:a7:ad:29:ad:91:ac:7e:df:87:24:3b:f3:
                    b4:71:2b:4e:58
                ASN1 OID: prime256v1
                NIST CURVE: P-256
        X509v3 extensions:
            X509v3 Key Usage: critical
                Digital Signature, Key Encipherment
            X509v3 Basic Constraints: critical
                CA:FALSE
            X509v3 Extended Key Usage:
                TLS Web Server Authentication, TLS Web Client Authentication
            X509v3 Subject Alternative Name:
                DNS:example.com, IP Address:0:0:0:0:0:FFFF:A02:1
            X509v3 Subject Key Identifier:
                C8:78:64:E9:F7:9C:0F:56:E2:1D:CE:EE:ED:24:E0:9F:1D:4B:A3:BF
            X509v3 Authority Key Identifier:
                B9:D1:CF:08:A5:F2:99:2B:5A:80:C9:78:23:78:D1:BC:79:70:9F:FB
    Signature Algorithm: ecdsa-with-SHA256
    Signature Value:
        30:44:02:20:4f:a4:0e:29:a3:3c:43:53:78:87:5b:9e:f7:a4:
        92:ae:fa:d0:51:db:da:1e:ec:69:cc:25:6b:be:cf:b7:e1:8a:
        02:20:1d:f5:10:0a:3d:92:84:f3:7d:b0:86:0e:95:6b:97:b5:
        0f:ca:4c:6b:99:0b:a0:b1:10:17:17:94:a0:bd:62:f9
*/
static char kInvalidEECertWithInvalidPermittedIPv6SubjAlt[] = R"(
-----BEGIN CERTIFICATE-----
MIICfjCCAiWgAwIBAgIUdWJcMLAOwhnArl3xMnAJnH8O29EwCgYIKoZIzj0EAwIw
YjELMAkGA1UEBhMCVVMxEzARBgNVBAgMCldhc2hpbmd0b24xFjAUBgNVBAoMDUFX
UyBMaWJjcnlwdG8xEDAOBgNVBAsMB0dvb2QgQ0ExFDASBgNVBAMMC0ludCBOQyBD
QSAyMCAXDTE1MDEwMTAwMDAwMFoYDzIxMDAwMTAxMDAwMDAwWjBuMQswCQYDVQQG
EwJVUzETMBEGA1UECAwKV2FzaGluZ3RvbjEWMBQGA1UECgwNQVdTIExpYmNyeXB0
bzEVMBMGA1UECwwMQmFkIEVuZHBvaW50MRswGQYDVQQDDBJOb3QgUGVybWl0dGVk
IElQdjYwWTATBgcqhkjOPQIBBggqhkjOPQMBBwNCAASyt7018uvahtXcQETHIxT5
0KVAFzCFtsYROMLbLMW8DBkR2Ghh1qOSa4oYUizchqetKa2RrH7fhyQ787RxK05Y
o4GqMIGnMA4GA1UdDwEB/wQEAwIFoDAMBgNVHRMBAf8EAjAAMB0GA1UdJQQWMBQG
CCsGAQUFBwMBBggrBgEFBQcDAjAoBgNVHREEITAfggtleGFtcGxlLmNvbYcQAAAA
AAAAAAAAAP//CgIAATAdBgNVHQ4EFgQUyHhk6fecD1biHc7u7STgnx1Lo78wHwYD
VR0jBBgwFoAUudHPCKXymStagMl4I3jRvHlwn/swCgYIKoZIzj0EAwIDRwAwRAIg
T6QOKaM8Q1N4h1ue96SSrvrQUdvaHuxpzCVrvs+34YoCIB31EAo9koTzfbCGDpVr
l7UPykxrmQugsRAXF5SgvWL5
-----END CERTIFICATE-----
)";


// EE certificate should not verify if signed by invalid root CA
TEST(X509CompatTest, CertificatesFromTrustStoreValidated) {
  bssl::UniquePtr<X509> root = CertFromPEM(kRootBadBasicConstraints);
  ASSERT_TRUE(root);
  bssl::UniquePtr<X509> leaf = CertFromPEM(kEndEntitySignedByBadRoot);
  ASSERT_TRUE(leaf);

  EXPECT_EQ(X509_V_ERR_INVALID_CA,
            Verify(leaf.get(), /*roots=*/{root.get()}, /*intermediates=*/{},
                   /*crls=*/{}, /*flags=*/0));
}

// Certificate should be rejected if it contains a critical AKID extension.
// This reports a X509_V_ERR_UNHANDLED_CRITICAL_EXTENSION due to it being an
// unhandled critical exception.
TEST(X509CompatTest, EECertificateWithCriticalAKID) {
  bssl::UniquePtr<X509> root = CertFromPEM(kValidRootCA1);
  ASSERT_TRUE(root);
  bssl::UniquePtr<X509> leaf =
      CertFromPEM(kInvalidEECertificateWithCriticalAKID);
  ASSERT_TRUE(leaf);

  EXPECT_EQ(X509_V_ERR_UNHANDLED_CRITICAL_EXTENSION,
            Verify(leaf.get(), /*roots=*/{root.get()}, /*intermediates=*/{},
                   /*crls=*/{}, /*flags=*/0));
}

// Certificate should not be rejected if it contains a critical CRL Distribution
// Points extension.
TEST(X509CompatTest, EECertificateWithCriticalCRLDistributionPointsExt) {
  bssl::UniquePtr<X509> root = CertFromPEM(kValidRootCA1);
  ASSERT_TRUE(root);
  bssl::UniquePtr<X509> leaf =
      CertFromPEM(kValidEECertWithCriticalCRLDistributionExt);
  ASSERT_TRUE(leaf);

  EXPECT_EQ(X509_V_OK,
            Verify(leaf.get(), /*roots=*/{root.get()}, /*intermediates=*/{},
                   /*crls=*/{}, /*flags=*/0));
}

// EE certificate's trust root is missing the basic constraints extension.
TEST(X509CompatTest, EECertificateSignedByInvalidRootMissingBasicConstraints) {
  bssl::UniquePtr<X509> root =
      CertFromPEM(kInvalidRootCertificateWithMissingBasicConstraintsExt);
  ASSERT_TRUE(root);
  bssl::UniquePtr<X509> leaf =
      CertFromPEM(kInvalidEECertificateSignedByRootMissingBasicConstraintsExt);
  ASSERT_TRUE(leaf);

  EXPECT_EQ(X509_V_ERR_INVALID_CA,
            Verify(leaf.get(), /*roots=*/{root.get()}, /*intermediates=*/{},
                   /*crls=*/{}, /*flags=*/0));
}

// EE certificate with negative serial number, while technically invalid per RFC
// 5280, should pass.
TEST(X509CompatTest, EECertificateWithNegativeSerialNumber) {
  bssl::UniquePtr<X509> root = CertFromPEM(kValidRootCA1);
  ASSERT_TRUE(root);
  bssl::UniquePtr<X509> leaf =
      CertFromPEM(kValidEECertificateWithNegativeSerialNumber);
  ASSERT_TRUE(leaf);

  EXPECT_EQ(X509_V_OK,
            Verify(leaf.get(), /*roots=*/{root.get()}, /*intermediates=*/{},
                   /*crls=*/{}, /*flags=*/0));
}

TEST(X509CompatTest, EECertificateWithValidNameConstrainedSubjAltIPv4) {
  bssl::UniquePtr<X509> root = CertFromPEM(kValidRootCA1);
  ASSERT_TRUE(root);
  bssl::UniquePtr<X509> inter = CertFromPEM(kValidIntCAWithIPv4NameConstraints);
  ASSERT_TRUE(inter);
  bssl::UniquePtr<X509> leaf =
      CertFromPEM(kValidEECertWithValidIPv4SubjectAltName);
  ASSERT_TRUE(leaf);

  EXPECT_EQ(X509_V_OK, Verify(leaf.get(), /*roots=*/{root.get()},
                              /*intermediates=*/{inter.get()},
                              /*crls=*/{}, /*flags=*/0));
}

TEST(X509CompatTest, EECertificateWithInvalidExcludedNameConstrainedSubjAltIPv4) {
  bssl::UniquePtr<X509> root = CertFromPEM(kValidRootCA1);
  ASSERT_TRUE(root);
  bssl::UniquePtr<X509> inter = CertFromPEM(kValidIntCAWithIPv4NameConstraints);
  ASSERT_TRUE(inter);
  bssl::UniquePtr<X509> leaf =
      CertFromPEM(kInvalidEECertWithInvalidExcludedIPv4SubjAlt);
  ASSERT_TRUE(leaf);

  EXPECT_EQ(X509_V_ERR_EXCLUDED_VIOLATION,
            Verify(leaf.get(), /*roots=*/{root.get()},
                   /*intermediates=*/{inter.get()},
                   /*crls=*/{}, /*flags=*/0));
}

TEST(X509CompatTest, EECertificateWithInvalidPermittedNameConstrainedSubjAltIPv4) {
  bssl::UniquePtr<X509> root = CertFromPEM(kValidRootCA1);
  ASSERT_TRUE(root);
  bssl::UniquePtr<X509> inter = CertFromPEM(kValidIntCAWithIPv4NameConstraints);
  ASSERT_TRUE(inter);
  bssl::UniquePtr<X509> leaf =
      CertFromPEM(kInvalidEECertWithInvalidPermittedIPv4SubjAlt);
  ASSERT_TRUE(leaf);

  EXPECT_EQ(X509_V_ERR_PERMITTED_VIOLATION,
            Verify(leaf.get(), /*roots=*/{root.get()},
                   /*intermediates=*/{inter.get()},
                   /*crls=*/{}, /*flags=*/0));
}

TEST(X509CompatTest, EECertificateWithValidNameConstrainedSubjAltIPv6) {
  bssl::UniquePtr<X509> root = CertFromPEM(kValidRootCA1);
  ASSERT_TRUE(root);
  bssl::UniquePtr<X509> inter = CertFromPEM(kValidIntCAWithIPv6NameConstraints);
  ASSERT_TRUE(inter);
  bssl::UniquePtr<X509> leaf =
      CertFromPEM(kValidEECertWithValidIPv6SubjectAltName);
  ASSERT_TRUE(leaf);

  EXPECT_EQ(X509_V_OK, Verify(leaf.get(), /*roots=*/{root.get()},
                              /*intermediates=*/{inter.get()},
                              /*crls=*/{}, /*flags=*/0));
}

TEST(X509CompatTest,
     EECertificateWithInvalidExcludedNameConstrainedSubjAltIPv6) {
  bssl::UniquePtr<X509> root = CertFromPEM(kValidRootCA1);
  ASSERT_TRUE(root);
  bssl::UniquePtr<X509> inter = CertFromPEM(kValidIntCAWithIPv6NameConstraints);
  ASSERT_TRUE(inter);
  bssl::UniquePtr<X509> leaf =
      CertFromPEM(kInvalidEECertWithInvalidExcludedIPv6SubjAlt);
  ASSERT_TRUE(leaf);

  EXPECT_EQ(X509_V_ERR_EXCLUDED_VIOLATION,
            Verify(leaf.get(), /*roots=*/{root.get()},
                   /*intermediates=*/{inter.get()},
                   /*crls=*/{}, /*flags=*/0));
}

TEST(X509CompatTest,
     EECertificateWithInvalidPermittedNameConstrainedSubjAltIPv6) {
  bssl::UniquePtr<X509> root = CertFromPEM(kValidRootCA1);
  ASSERT_TRUE(root);
  bssl::UniquePtr<X509> inter = CertFromPEM(kValidIntCAWithIPv6NameConstraints);
  ASSERT_TRUE(inter);
  bssl::UniquePtr<X509> leaf =
      CertFromPEM(kInvalidEECertWithInvalidPermittedIPv6SubjAlt);
  ASSERT_TRUE(leaf);

  EXPECT_EQ(X509_V_ERR_PERMITTED_VIOLATION,
            Verify(leaf.get(), /*roots=*/{root.get()},
                   /*intermediates=*/{inter.get()},
                   /*crls=*/{}, /*flags=*/0));
}
