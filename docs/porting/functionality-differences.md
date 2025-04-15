# No-op Symbols and Configurations

Although the `OPENSSL_IS_AWSLC` preprocessor macro is available for downstream projects to distinguish AWS-LC from OpenSSL, we wish to limit the number of `#ifdef`s needed for projects to support us. No-ops symbols are used in place for functions that are less involved in key code paths to allow for easier integration. A no-op (no operation) symbol refers to a symbol that does nothing and has no effect on the state of the program. AWS-LC uses these across various utility functions and configuration flags to provide easier compatibility with OpenSSL.

No-op symbols can be differentiated into two types:

1. Symbols related to certain functionalities and configurations in OpenSSL that we don’t support (i.e. Security Levels, DH ciphersuites, etc).
2. Symbols that were historically needed to configure OpenSSL correctly, but aren’t needed to configure AWS-LC (i.e. threading, entropy configuration, etc.)

## libssl No-ops & Absent Functionality

libssl is the portion of OpenSSL which supports TLS. AWS-LC does not have support for every OpenSSL libssl feature. Notable absent functionalities from libssl include SSL Security Levels, SSL Compression, and DANE TLSA. Certain SSL ciphersuites are also not supported such as ciphers using FFDH and RC4. Partially absent features include minimal[TLS renegotiation support](https://github.com/aws/aws-lc/blob/main/PORTING.md#dsa-evp_pkeys) and Stateful Session Resumption (only supported for TLS 1.2 and earlier). More details can be found in the [ssl.h header documentation](https://github.com/aws/aws-lc/blob/main/include/openssl/ssl.h).

**When migrating to AWS-LC, it is important to understand the SSL features your application is reliant on from** **OpenSSL****. Many nuances with libssl can only be discovered at runtime****, so consumers should have specific test cases available****. For example, absent ciphersuite support cannot be detected unless there are specific tests expecting the ciphersuite to be available.** <ins>**Migrators to AWS-LC are expected to understand their intended use cases and have tests surrounding functionality they are dependent on.**</ins> AWS-LC provides test coverage for functional correctness and compliance with TLS standards and implemented extensions. Different cryptographic libraries may implement some behavior by convention that is not standardized and thus is not guaranteed to work the same way in AWS-LC. Customers are responsible for writing their own tests to determine whether they are affected by these kinds of differences, and AWS-LC will publish a list of known differences in the future.

**If you have a valid use case for any missing functionality or if anything is not clarified in our documentation, feel free to [cut an issue](https://github.com/aws/aws-lc/issues/new?assignees=&labels=&projects=&template=general-issue.md&title=) or create a PR to let us know.**

### libssl No-ops

<table border=0 cellspacing=0 cellpadding=0
 style='border-collapse:collapse'>
 <tr>
  <td>
  <p><b><span>Related Functionality</span></b></p>
  </td>
  <td>
  <p><b><span>Details</span></b></p>
  </td>
  <td>
  <p><b><span>No-op function</span></b></p>
  </td>
  <td>
  <p><b><span>Return value</span></b></p>
  </td>
 </tr>
 <tr>
  <td rowspan=2>
  <p><span>Security Levels</span></p>
  </td>
  <td rowspan=2>
  <p>
    <span>
        <a href="https://github.com/aws/aws-lc/blob/e91524c10ad698fd56f77289ba3430baf3c7af64/include/openssl/ssl.h#L5709-L5751">
            Security Levels No-ops
        </a>
    </span></p>
  </td>
  <td>
  <p><span>SSL_CTX_get_security_level</span></p>
  </td>
  <td>
  <p><span>Returns zero.</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>SSL_CTX_set_security_level</span></p>
  </td>
  <td>
  <p><span>Does nothing.</span></p>
  </td>
 </tr>
 <tr>
  <td rowspan=4>
  <p><span>DH ciphersuites</span></p>
  </td>
  <td rowspan=4>
  <p>
    <span>
        <a href="https://github.com/aws/aws-lc/blob/e91524c10ad698fd56f77289ba3430baf3c7af64/include/openssl/ssl.h#L5677-L5706">
            FFDH Ciphersuite No-ops
        </a>
    </span></p>
  </td>
  <td>
  <p><span>SSL_CTX_set_tmp_dh</span></p>
  </td>
  <td>
  <p><span>Returns one.</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>SSL_set_tmp_dh</span></p>
  </td>
  <td>
  <p><span>Returns one.</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>SSL_CTX_set_tmp_dh_callback</span></p>
  </td>
  <td>
  <p><span>Does nothing.</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>SSL_set_tmp_dh_callback</span></p>
  </td>
  <td>
  <p><span>Does nothing.</span></p>
  </td>
 </tr>
 <tr>
  <td rowspan=6>
  <p><span>SSL_COMP</span>
    <span> and </span>
  <span>COMP_METHOD</span></p>
  </td>
  <td rowspan=6>
  <p>
    <span>
        <a href="https://github.com/aws/aws-lc/blob/e91524c10ad698fd56f77289ba3430baf3c7af64/include/openssl/ssl.h#L5630-L5674">
            SSL_COMP and COMP_METHOD No-ops
        </a>
    </span></p>
  </td>
  <td>
  <p><span>SSL_COMP_get_compression_methods</span></p>
  </td>
  <td>
  <p><span>Returns NULL.</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>SSL_COMP_add_compression_method</span></p>
  </td>
  <td>
  <p><span>Returns one.</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>SSL_COMP_get_name</span></p>
  </td>
  <td>
  <p><span>Returns NULL.</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>SSL_COMP_free_compression_methods</span></p>
  </td>
  <td>
  <p><span>Does nothing.</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>SSL_get_current_compression</span></p>
  </td>
  <td>
  <p><span>Returns NULL.</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>SSL_get_current_expansion</span></p>
  </td>
  <td>
  <p><span>Returns NULL.</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>TLS Renegotiation</span></p>
  </td>
  <td>
  <p>
    <span>
        <a href="https://github.com/aws/aws-lc/blob/e91524c10ad698fd56f77289ba3430baf3c7af64/include/openssl/ssl.h#L4573-L4648">
            TLS Renegotiation
        </a>
    </span></p>
  </td>
  <td>
  <p><span>SSL_renegotiate</span></p>
  </td>
  <td>
  <p>
    Returns 1 on success, 0 on failure. <br><br>
    There is no support for renegotiation for TLS as a server or DTLS. <br><br>
    There is only minimal support for initiating renegotiation as a client.
    SSL_set_renegotiate_mode must be set to ssl_renegotiate_once, ssl_renegotiate_freely, 
    or ssl_renegotiate_explicit for SSL_renegotiate to work.
  </p>
  </td>
 </tr>
 <tr>
  <td rowspan=3>
  <p><span>General</span></p>
  </td>
  <td>
  <p>
    <span>
        <a href="https://github.com/aws/aws-lc/blob/e91524c10ad698fd56f77289ba3430baf3c7af64/include/openssl/ssl.h#L5759-L5764">
            SSL_get_shared_ciphers
        </a>
    </span></p>
  </td>
  <td>
  <p><span>SSL_get_shared_ciphers</span></p>
  </td>
  <td>
  <p><span>Writes an empty string and returns a pointer containing it or returns NULL.</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p>
    <span>
        <a href="https://github.com/aws/aws-lc/blob/e91524c10ad698fd56f77289ba3430baf3c7af64/include/openssl/ssl.h#L5766-L5769">
            SSL_get_shared_sigalgs
        </a>
    </span></p>
  </td>
  <td>
  <p><span>SSL_get_shared_sigalgs</span></p>
  </td>
  <td>
  <p><span>Returns zero.</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p>
    <span>
        <a href="https://github.com/aws/aws-lc/blob/e91524c10ad698fd56f77289ba3430baf3c7af64/include/openssl/ssl.h#L5682-L5685">
            SSL_get_server_tmp_key
        </a>
    </span></p>
  </td>
  <td>
  <p><span>SSL_get_server_tmp_key</span></p>
  </td>
  <td>
  <p><span>Returns zero.</span></p>
  </td>
 </tr>
</table>

### libssl TLS supported ciphersuites

TLS 1.2 supported cipher suites between AWS-LC and OpenSSL 1.1.1u:

|Ciphersuite	|OpenSSL 1.1.1	|AWS-LC	|
|---	|---	|---	|
|AES128-GCM-SHA256	|X	|X	|
|AES128-SHA	|X	|X	|
|AES128-SHA256	|X	|X	|
|AES256-GCM-SHA384	|X	|X	|
|AES256-SHA	|X	|X	|
|AES256-SHA256	|X	|	|
|DES-CBC3-SHA	|	|X	|
|DHE-RSA-AES128-GCM-SHA256	|X	|	|
|DHE-RSA-AES128-SHA	|X	|	|
|DHE-RSA-AES128-SHA256	|X	|	|
|DHE-RSA-AES256-GCM-SHA384	|X	|	|
|DHE-RSA-AES256-SHA	|X	|	|
|DHE-RSA-AES256-SHA256	|X	|	|
|DHE-RSA-CHACHA20-POLY1305	|X	|	|
|ECDHE-ECDSA-AES128-GCM-SHA256	|X	|X	|
|ECDHE-ECDSA-AES128-SHA	|X	|X	|
|ECDHE-ECDSA-AES128-SHA256	|X	|	|
|ECDHE-ECDSA-AES256-GCM-SHA384	|X	|X	|
|ECDHE-ECDSA-AES256-SHA	|X	|X	|
|ECDHE-ECDSA-AES256-SHA384	|X	|	|
|ECDHE-ECDSA-CHACHA20-POLY1305	|X	|X	|
|ECDHE-PSK-AES128-CBC-SHA	|	|X	|
|ECDHE-PSK-AES256-CBC-SHA	|	|X	|
|ECDHE-PSK-CHACHA20-POLY1305	|	|X	|
|ECDHE-RSA-AES128-GCM-SHA256	|X	|X	|
|ECDHE-RSA-AES128-SHA	|X	|X	|
|ECDHE-RSA-AES128-SHA256	|X	|X	|
|ECDHE-RSA-AES256-GCM-SHA384	|X	|X	|
|ECDHE-RSA-AES256-SHA	|X	|X	|
|ECDHE-RSA-AES256-SHA384	|X	|X |
|ECDHE-RSA-CHACHA20-POLY1305	|X	|X	|
|PSK-AES128-CBC-SHA	|	|X	|
|PSK-AES256-CBC-SHA	|	|X	|

TLS 1.3 supported cipher suites between AWS-LC and OpenSSL 1.1.1u:

|Ciphersuite	|OpenSSL 1.1.1	|AWS-LC	|
|---	|---	|---	|
|TLS_AES_128_GCM_SHA256	|X	|X	|
|TLS_AES_256_GCM_SHA384	|X	|X	|
|TLS_CHACHA20_POLY1305_SHA256	|X	|X	|

## libcrypto No-ops & Absent Functionality

libcrypto is the portion of OpenSSL for performing general-purpose cryptography, which can be used without libssl. Commonly used standardized formats such as `X509` and `ASN1` are also implemented in libcrypto. AWS-LC does not have support for every feature in OpenSSL’s libcrypto. Notable absent functionalities include OpenSSL’s [`CONF` modules](https://www.openssl.org/docs/manmaster/man3/CONF_modules_load_file.html). Utility functions surrounding `RAND` are no-ops, consumers should call `RAND_bytes` directly instead. Setting flags to configure `EVP_MD_CTX` and `EVP_CIPHER_CTX` is also not supported.

Older and less common usages of `EVP_PKEY` have been removed. For example, signing and verifying with `EVP_PKEY_DSA`  is not supported. More details on specific features can be found in the corresponding [header documentation](https://github.com/aws/aws-lc/tree/main/include/openssl).

Memory debugging functionality between AWS-LC and OpenSSL 1.1.1u:

|Function |OpenSSL 1.1.1 |AWS-LC |
|--- |--- |--- |
|CRYPTO_mem_ctrl() |X | |
|CRYPTO_mem_leaks() |X | |
|CRYPTO_mem_leaks_fp() |X | |
|CRYPTO_mem_leaks_cb() |X | |

Note: AWS-LC defines OPENSSL_NO_CRYPTO_MDEBUG by default.

**When migrating to AWS-LC, it is important to understand the specific libcrypto components your application is reliant on from OpenSSL. For example, there may be underlying differences when consuming** **X509 certificate verification** **from AWS-LC.** <ins>**Migrators to AWS-LC are expected to understand their intended use cases and have tests surrounding functionality they are dependent on.**</ins> AWS-LC provides test coverage for functional and cryptographic correctness, along with compliance with standards like PKCS and X509. Different cryptographic libraries may implement some behavior by convention that is not standardized and thus is not guaranteed to work the same way in AWS-LC. Customers are responsible for writing their own tests to determine whether they are affected by these kinds of differences, and AWS-LC will publish a list of known differences in the future.

**If you have a valid use case for any missing functionality or if anything is not clarified in our documentation, feel free to [cut an issue](https://github.com/aws/aws-lc/issues/new?assignees=&labels=&projects=&template=general-issue.md&title=) or create a PR to let us know.**

### libcrypto No-ops

<table border=0 cellspacing=0 cellpadding=0
 style='border-collapse:collapse'>
 <tr>
  <td>
  <p><b><span>Related Functionality</span></b></p>
  </td>
  <td>
  <p><b><span>Details</span></b></p>
  </td>
  <td>
  <p><b><span>No-op function</span></b></p>
  </td>
  <td>
  <p><b><span>Return value</span></b></p>
  </td>
 </tr>
 <tr>
  <td rowspan=5>
  <p><span>EVP_PKEY</span></p>
  </td>
  <td rowspan=2>
  <p>
    <span>
        <a href="https://github.com/aws/aws-lc/blob/746d06505b3a3827cf61959ca0c3d87c3f21accc/include/openssl/evp.h#L1180-L1194">
            EVP_PKEY_DSA No-ops
        </a>
        <br><br>
        <a href="https://github.com/aws/aws-lc/blob/main/PORTING.md#dsa-evp_pkeys">
            Porting Guide
        </a>
    </span>
  </p>
  </td>
  <td>
  <p><span>EVP_PKEY_CTX_set_dsa_paramgen_bits</span></p>
  </td>
  <td>
  <p><span>Returns zero.</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>EVP_PKEY_CTX_set_dsa_paramgen_q_bits</span></p>
  </td>
  <td>
  <p><span>Returns zero.</span></p>
  </td>
 </tr>
 <tr>
  <td rowspan=2>
  <p>
    <span>
        <a href="https://github.com/aws/aws-lc/blob/746d06505b3a3827cf61959ca0c3d87c3f21accc/include/openssl/evp.h#L1197-L1213">
            EVP_PKEY_DH No-ops
        </a>
    </span>
  </p>
  </td>
  <td>
  <p><span>EVP_PKEY_get0_DH</span></p>
  </td>
  <td>
  <p><span>Returns NULL.</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>EVP_PKEY_get1_DH</span></p>
  </td>
  <td>
  <p><span>Returns NULL.</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p>
    <span>
        <a href="https://github.com/aws/aws-lc/blob/746d06505b3a3827cf61959ca0c3d87c3f21accc/include/openssl/evp.h#L1145-L1152">
            evp.h
        </a>
    </span>
  </p>
  </td>
  <td>
  <p>EVP_PKEY_get0</p>
  </td>
  <td>
  <p>
    Void function that does not return anything (NULL).
  </p>
  </td>
 </tr>
 <tr>
  <td rowspan=6>
  <p><span>EC</span></p>
  </td>
  <td rowspan=3>
  <p>
    <span>
        <a href="https://github.com/aws/aws-lc/blob/746d06505b3a3827cf61959ca0c3d87c3f21accc/include/openssl/ec_key.h#L360-L363">
            EC_KEY
        </a>
        <br><br>
        <a href="https://github.com/aws/aws-lc/blob/746d06505b3a3827cf61959ca0c3d87c3f21accc/include/openssl/ec.h#L433-L441">
            EC_GROUP
        </a>
    </span>
  </p>
  </td>
  <td>
  <p><span>EC_KEY_set_asn1_flag</span></p>
  </td>
  <td>
  <p><span>Does nothing.</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>EC_GROUP_set_asn1_flag</span></p>
  </td>
  <td>
  <p><span>Does nothing.</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>EC_GROUP_get_asn1_flag</span></p>
  </td>
  <td>
  <p><span>Returns OPENSSL_EC_NAMED_CURVE.</span></p>
  </td>
 </tr>
 <tr>
  <td rowspan=2>
  <p>
    <span>
        <a href="https://github.com/aws/aws-lc/blob/746d06505b3a3827cf61959ca0c3d87c3f21accc/include/openssl/ec.h#L451-L468">
            EC_METHOD
        </a>
    </span>
  </p>
  </td>
  <td>
  <p><span>EC_GROUP_method_of</span></p>
  </td>
  <td>
  <p><span>Returns a dummy non-NULL EC_METHOD pointer.</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>EC_METHOD_get_field_type</span></p>
  </td>
  <td>
  <p><span>Returns NID_X9_62_prime_field.</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p>
    <span>
        <a href="https://github.com/aws/aws-lc/blob/746d06505b3a3827cf61959ca0c3d87c3f21accc/include/openssl/ec.h#L443-L448">
            Compressed Forms
        </a>
    </span>
  </p>
  </td>
  <td>
  <p><span>EC_GROUP_set_point_conversion_form</span></p>
  </td>
  <td>
  <p>
    Returns nothing as a void function. Aborts if a form other than
    POINT_CONVERSION_UNCOMPRESSED or POINT_CONVERSION_COMPRESSED is requested.
  </p>
  </td>
 </tr>
 <tr>
  <td rowspan=5>
  <p><span>CONF modules</span></p>
  </td>
  <td rowspan=5>
  <p>
    <span>
        <a href="https://github.com/aws/aws-lc/blob/746d06505b3a3827cf61959ca0c3d87c3f21accc/include/openssl/conf.h#L127-L149">
            conf.h
        </a>
    </span>
  </p>
  </td>
  <td>
  <p><span>CONF_modules_load_file</span></p>
  </td>
  <td>
  <p><span>Returns one.</span></p>
  </td>
 </tr>
  <tr>
  <td>
  <p><span>CONF_get1_default_config_file</span></p>
  </td>
  <td>
  <p><span>Returns a fixed dummy string(&quot;</span>No support for Config files in AWS-LC.&quot;)</p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>CONF_modules_unload</span></p>
  </td>
  <td>
  <p><span>Does nothing.</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>CONF_modules_finish</span></p>
  </td>
  <td>
  <p><span>Does nothing.</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>CONF_modules_free</span></p>
  </td>
  <td>
  <p><span>Does nothing.</span></p>
  </td>
 </tr>
 <tr>
  <td rowspan=13>
  <p><span>RAND Functions</span></p>
  </td>
  <td rowspan=13>
  <p>
    <span>
        <a href="https://github.com/aws/aws-lc/blob/746d06505b3a3827cf61959ca0c3d87c3f21accc/include/openssl/rand.h#L79-L141">
            rand.h
        </a>
        <br><br>
        <a href="https://github.com/aws/aws-lc/blob/5c358103c5df836b9343bf995717b5bc13d5e82f/crypto/fipsmodule/FIPS.md#entropy-sources">
            Entropy Sources
        </a>
    </span>
  </p>
  </td>
  <td>
  <p><span>RAND_load_file</span></p>
  </td>
  <td>
  <p><span>Returns a non-negative number.</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>RAND_write_file</span></p>
  </td>
  <td>
  <p><span>Does nothing and returns negative one.</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>RAND_file_name</span></p>
  </td>
  <td>
  <p><span>Returns NULL.</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>RAND_add</span></p>
  </td>
  <td>
  <p><span>Does nothing.</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>RAND_egd</span></p>
  </td>
  <td>
  <p><span>Returns 255.</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>RAND_poll</span></p>
  </td>
  <td>
  <p><span>Returns one.</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>RAND_status</span></p>
  </td>
  <td>
  <p><span>Returns one.</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>RAND_cleanup</span></p>
  </td>
  <td>
  <p><span>Does nothing.</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>RAND_SSLeay</span></p>
  </td>
  <td>
  <p><span>Returns a dummy RAND_METHOD pointer.</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>RAND_OpenSSL</span></p>
  </td>
  <td>
  <p><span>Returns a dummy RAND_METHOD pointer.</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>RAND_get_rand_method</span></p>
  </td>
  <td>
  <p><span>Returns a dummy </span>
  <span>RAND_METHOD</span>
  <span> pointer.</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>RAND_set_rand_method</span></p>
  </td>
  <td>
  <p><span>Returns one.</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>RAND_keep_random_devices_open</span></p>
  </td>
  <td>
  <p><span>Does nothing.</span></p>
  </td>
 </tr>
 <tr>
  <td rowspan=4>
  <p><span>ASN1</span></p>
  </td>
  <td rowspan=4>
  <p>
    <span>
        <a href="https://github.com/aws/aws-lc/blob/746d06505b3a3827cf61959ca0c3d87c3f21accc/include/openssl/asn1.h#L2045-L2061">
            asn1.h
        </a>
    </span>
  </p>
  </td>
  <td>
  <p><span>ASN1_STRING_set_default_mask</span></p>
  </td>
  <td>
  <p><span>Does nothing.</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>ASN1_STRING_set_default_mask_asc</span></p>
  </td>
  <td>
  <p><span>Returns one.</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>ASN1_STRING_get_default_mask</span></p>
  </td>
  <td>
  <p><span>Returns B_ASN1_UTF8STRING (The default value AWS-LC uses).</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>ASN1_STRING_TABLE_cleanup</span></p>
  </td>
  <td>
  <p><span>Does nothing.</span></p>
  </td>
 </tr>
 <tr>
  <td rowspan=16>
  <p><span>Thread Safety</span></p>
  </td>
  <td rowspan=16>
  <p>
    <span>
        <a href="https://github.com/aws/aws-lc/blob/746d06505b3a3827cf61959ca0c3d87c3f21accc/include/openssl/thread.h#L119-L204">
            thread.h
        </a>
    </span>
  </p>
  </td>
  <td>
  <p><span>CRYPTO_num_locks</span></p>
  </td>
  <td>
  <p><span>Returns one.</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>CRYPTO_set_locking_callback</span></p>
  </td>
  <td>
  <p><span>Does nothing.</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>CRYPTO_set_add_lock_callback</span></p>
  </td>
  <td>
  <p><span>Does nothing.</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>CRYPTO_get_locking_callback</span></p>
  </td>
  <td>
  <p><span>Returns NULL.</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>CRYPTO_get_lock_name</span></p>
  </td>
  <td>
  <p><span>Returns a fixed dummy string
  (&quot;</span>No old-style OpenSSL locks anymore&quot;)</p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>CRYPTO_THREADID_set_callback</span></p>
  </td>
  <td>
  <p><span>Returns one.</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>CRYPTO_THREADID_set_numeric</span></p>
  </td>
  <td>
  <p><span>Does nothing.</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>CRYPTO_THREADID_set_pointer</span></p>
  </td>
  <td>
  <p><span>Does nothing.</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>CRYPTO_THREADID_current</span></p>
  </td>
  <td>
  <p><span>Does nothing.</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>CRYPTO_set_id_callback</span></p>
  </td>
  <td>
  <p><span>Does nothing.</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>CRYPTO_set_dynlock_create_callback</span></p>
  </td>
  <td>
  <p><span>Does nothing.</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>CRYPTO_set_dynlock_lock_callback</span></p>
  </td>
  <td>
  <p><span>Does nothing.</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>CRYPTO_set_dynlock_destroy_callback</span></p>
  </td>
  <td>
  <p><span>Does nothing.</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>CRYPTO_get_dynlock_create_callback</span></p>
  </td>
  <td>
  <p><span>Returns NULL.</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>CRYPTO_get_dynlock_lock_callback</span></p>
  </td>
  <td>
  <p><span>Returns NULL.</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>CRYPTO_get_dynlock_destroy_callback</span></p>
  </td>
  <td>
  <p><span>Returns NULL.</span></p>
  </td>
 </tr>
<tr>
 <td>
  <p><span>Memory Debugging</span></p>
 </td>
 <td>
  <p><span>crypto.h</span></p>
 </td>
 <td>
  <p><span>CRYPTO_mem_ctrl</span></p>
 </td>
<td>
<p><span>Returns 0.</span></p>
</td>
</tr>
 <tr>
  <td rowspan=14>
  <p><span>Miscellaneous</span></p>
  </td>
  <td rowspan=5>
  <p>
    <span>
        <a href="https://github.com/aws/aws-lc/blob/746d06505b3a3827cf61959ca0c3d87c3f21accc/include/openssl/evp.h#L1154-L1178">
            evp.h
        </a>
    </span>
  </p>
  </td>
  <td>
  <p><span>OpenSSL_add_all_algorithms</span></p>
  </td>
  <td>
  <p><span>Does nothing.</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>OPENSSL_add_all_algorithms_conf</span></p>
  </td>
  <td>
  <p><span>Does nothing.</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>OpenSSL_add_all_ciphers</span></p>
  </td>
  <td>
  <p><span>Does nothing.</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>OpenSSL_add_all_digests</span></p>
  </td>
  <td>
  <p><span>Does nothing.</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>EVP_cleanup</span></p>
  </td>
  <td>
  <p><span>Does nothing.</span></p>
  </td>
 </tr>
 <tr>
  <td rowspan=2>
  <p>
    <span>
        <a href="https://github.com/aws/aws-lc/blob/746d06505b3a3827cf61959ca0c3d87c3f21accc/include/openssl/cipher.h#L559-L573">
            cipher.h
        </a>
    </span>
  </p>
  </td>
  <td>
  <p><span>EVP_CIPHER_CTX_set_flags</span></p>
  </td>
  <td>
  <p><span>Does nothing.</span><br>
  <br>
  This functions sets flags for EVP_CIPHER_CTX, so any related flags are also no-ops. Related no-op flags can be found in 
    <a href="https://github.com/aws/aws-lc/blob/746d06505b3a3827cf61959ca0c3d87c3f21accc/include/openssl/cipher.h#L559-L569">
      the surrounding documentation
    </a>
    .
  </p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>EVP_add_cipher_alias</span></p>
  </td>
  <td>
  <p><span>Does nothing and returns one</span></p>
  </td>
 </tr>
 <tr>
  <td rowspan=2>
  <p>
    <span>
        <a href="https://github.com/aws/aws-lc/blob/746d06505b3a3827cf61959ca0c3d87c3f21accc/include/openssl/digest.h#L356-L370">
            digest.h
        </a>
    </span>
  </p>
  </td>
  <td>
  <p><span>EVP_MD_CTX_set_flags</span></p>
  </td>
  <td>
  <p>
    Does nothing.<br><br>
    This functions sets flags for EVP_MD_CTX, so any related flags are also no-ops. Related no-op flags can be found in 
    <a href="https://github.com/aws/aws-lc/blob/746d06505b3a3827cf61959ca0c3d87c3f21accc/include/openssl/digest.h#L361-L365">
      the surrounding documentation
    </a>
    .
  </p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>EVP_add_digest</span></p>
  </td>
  <td>
  <p><span>Does nothing and returns one</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p>
    <span>
        <a href="https://github.com/aws/aws-lc/blob/746d06505b3a3827cf61959ca0c3d87c3f21accc/include/openssl/dh.h#L352-L365">
            dh.h
        </a>
    </span>
  </p>
  </td>
  <td>
  <p><span>DH_clear_flags</span></p>
  </td>
  <td>
  <p>
    Does nothing.<br><br>
    This functions clears flags for DH, so any related flags are also no-ops. Related no-op flags can be found in 
    <a href="https://github.com/aws/aws-lc/blob/746d06505b3a3827cf61959ca0c3d87c3f21accc/include/openssl/dh.h#L354-L365">
      the surrounding documentation
    </a>
    .
  </p>
  </td>
 </tr>
 <tr>
  <td rowspan=2>
  <p>
    <span>
        <a href="https://github.com/aws/aws-lc/blob/746d06505b3a3827cf61959ca0c3d87c3f21accc/include/openssl/ex_data.h#L178-L185">
            ex_data.h
        </a>
    </span>
  </p>
  </td>
  <td>
  <p><span>CRYPTO_cleanup_all_ex_data</span></p>
  </td>
  <td>
  <p><span>Does nothing.</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>CRYPTO_EX_dup</span></p>
  </td>
  <td>
  <p><span>Legacy Callback function that's ignored.</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p>
    <span>
        <a href="https://github.com/aws/aws-lc/blob/746d06505b3a3827cf61959ca0c3d87c3f21accc/include/openssl/bio.h#L880-L886">
            bio.h
        </a>
    </span>
  </p>
  </td>
  <td>
  <p><span>BIO_set_write_buffer_size</span></p>
  </td>
  <td>
  <p><span>Returns zero.</span></p>
  </td>
 </tr>
<tr>
<td>
<p>
<span>
        <a href="https://github.com/aws/aws-lc/blob/412be9d1bb4f9d2f962dba1beac41249dbacdb55/include/openssl/x509.h#L5097">
            x509.h
        </a>
    </span>
</p>
</td>
<td>
  <p><span>X509_TRUST_cleanup</span></p>
  </td>
  <td>
  <p><span>Does nothing.</span></p>
  </td>
</tr>
</table>