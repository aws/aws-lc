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
// This reports a X509_V_ERR_UNHANDLED_CRITICAL_EXTENSION due to it being an unhandled
// critical exception.
TEST(X509CompatTest, EndpointCertificateWithCriticalAKID) {
  bssl::UniquePtr<X509> root = CertFromPEM(kValidRootCA1);
  ASSERT_TRUE(root);
  bssl::UniquePtr<X509> leaf = CertFromPEM(kInvalidEECertificateWithCriticalAKID);
  ASSERT_TRUE(leaf);

  EXPECT_EQ(X509_V_ERR_UNHANDLED_CRITICAL_EXTENSION,
            Verify(leaf.get(), /*roots=*/{root.get()}, /*intermediates=*/{},
                   /*crls=*/{}, /*flags=*/0));
}
