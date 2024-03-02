# Differences in Configuration Defaults

Cryptography and SSL should have less configurations and be hard to misuse. As mentioned earlier, AWS-LC has cut down on the available knobs in crypto/ssl and made certain optimizations the default. Most configuration flags OpenSSL historically had available have been changed to no-ops in AWS-LC. 
No-op flags can also be differentiated into two types here:

1. The configuration is already provided by default in AWS-LC.  
2. There are certain configurations and historic workarounds in OpenSSL that we don’t support (see [`SSL_OP_ALL`](https://www.openssl.org/docs/manmaster/man3/SSL_CTX_set_options.html)).

There are also a few configurations which OpenSSL has “OFF” by default, that AWS-LC has turned “ON” by default. This section outlines all known no-op configuration flags and default configuration differences.

## Default Behavioral Differences and No-op Configuration Flags

The following tables only contains the differences in configuration options AWS-LC and OpenSSL provides.

1. **The following two tables under `libssl` and `libcrypto` only focus on the flags that exist within AWS-LC. There are other flags supported by only OpenSSL that aren’t listed here. Missing flags we are aware of are documented in [Intentionally Omitted Configuration Flags](#intentionally-omitted-configuration-flags).
    If there is a valid use case for an undocumented flag non-existent within AWS-LC, feel free to** [**cut an issue**](https://github.com/aws/aws-lc/issues/new?assignees=&labels=&projects=&template=general-issue.md&title=) **to us.**
2. Flags that are no-ops within both AWS-LC and OpenSSL have been omitted from the table.
3. Flags that are listed as no-ops in the **Configurability** section, means that there is no support to configure the listed behavior within AWS-LC. The flags are merely provided for easier compatibility.

### Things to be Aware

**When integrating with AWS-LC, it is important to keep note if your application is dependent on any of the flags outlined in the following tables.  Your application should have tests regarding expected behavior and understand the customer impact behavioral changes will cause before migrating to AWS-LC.**

* <ins>**Anything that is labeled “ON” in “AWS-LC Default” is a behavioral difference between AWS-LC and OpenSSL</ins> (with the exception of** [**`SSL_MODE_AUTO_RETRY`**](https://www.openssl.org/docs/man1.1.1/man3/SSL_CTX_set_mode.html)**). Developers should make sure that migrating to AWS-LC, is the equivalent of turning these flags “ON” by default in OpenSSL.**
    * **Aside from** [**`SSL_MODE_NO_AUTO_CHAIN`**](https://github.com/aws/aws-lc/blob/c8d82c7599449609d3540eefb7972f137fc1b872/include/openssl/ssl.h#L839-L849), <ins>**there is no way to clear any flags that are “ON” by default in AWS-LC.**</ins>
* <ins>**Anything that is labeled “OFF” in “AWS-LC Default” is also a "NO-OP". These flags merely exist for compatibility and the state of AWS-LC does not change when attempting to configure them.</ins> If any of these flags are used, differences will be exposed at run-time with your application.** 

To determine whether your consuming application is impacted, do a search for the relevant “**Context Flags Setting Function**"s in your codebase. If the function is used, be aware of any relevant flags that have been listed in “**Context Flags**”. More context on what each flag configures can be found in our documentation by clicking the corresponding link.

## libssl Differences

The following table contains the differences in libssl configuration options AWS-LC and OpenSSL provides. **These flags are relevant to all TLS connections, unless specified otherwise.**

* **Aside from and `SSL_MODE_AUTO_RETRY` being "ON" by default in OpenSSL, everything is "OFF" by default in OpenSSL.**
* Each “**Context Flag”** has a link that provides more details on the flag’s functionality and our decision behind it (WIP)


<table border=0 cellspacing=0 cellpadding=0
 style='border-collapse:collapse'>
 <tr>
  <td>
  <p><b><span>Context Flags Setting Function</span></b></p>
  </td>
  <td>
  <p><b><span>Context Flags</span></b></p>
  </td>
  <td>
  <p><b><span>AWS-LC Default</span></b></p>
  </td>
  <td>
  <p><b><span>Configurability</span></b></p>
  </td>
 </tr>
 <tr>
  <td rowspan=5>
  <p><span><a
  href="https://www.openssl.org/docs/manmaster/man3/SSL_CTX_set_mode.html">SSL_CTX_set_mode<br>
  <span style='color:windowtext;text-decoration:none'>SSL_set_mode</span></a><br>
  <a href="https://www.openssl.org/docs/manmaster/man3/SSL_CTX_set_mode.html"><br>
  SSL_CTX_clear_mode<br>
  SSL_clear_mode</a></span></p>
  </td>
  <td>
  <p><span><a
  href="https://github.com/aws/aws-lc/blob/c8d82c7599449609d3540eefb7972f137fc1b872/include/openssl/ssl.h#L839-L849">SSL_MODE_NO_AUTO_CHAIN</a></span></p>
  </td>
  <td>
  <p><span>ON</span></p>
  </td>
  <td>
  <p><span>Configurable</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>SSL_MODE_AUTO_RETRY</span></p>
  </td>
  <td>
  <p><span>ON</span></p>
  </td>
  <td>
  <p><span>NO-OP</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>SSL_MODE_RELEASE_BUFFERS</span></p>
  </td>
  <td>
  <p><span>ON</span></p>
  </td>
  <td>
  <p><span>NO-OP</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>SSL_MODE_SEND_CLIENTHELLO_TIME</span></p>
  </td>
  <td>
  <p><span>OFF</span></p>
  </td>
  <td>
  <p><span>NO-OP</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>SSL_MODE_SEND_SERVERHELLO_TIME</span></p>
  </td>
  <td>
  <p><span>ON</span></p>
  </td>
  <td>
  <p><span>NO-OP</span></p>
  </td>
 </tr>
 <tr>
  <td rowspan=10>
  <p><span><a
  href="https://www.openssl.org/docs/manmaster/man3/SSL_CTX_set_options.html">SSL_CTX_set_options<br>
  <span style='color:windowtext;text-decoration:none'>SSL_set_options</span></a><br>
  <br>
  <a href="https://www.openssl.org/docs/manmaster/man3/SSL_CTX_set_options.html">SSL_CTX_clear_options<br>
  SSL_clear_options</a></span></p>
  </td>
  <td>
  <p><span>SSL_OP_ALL</span></p>
  </td>
  <td>
  <p><span>OFF</span></p>
  </td>
  <td>
  <p><span>NO-OP</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>SSL_OP_ALLOW_UNSAFE_LEGACY_RENEGOTIATION</span></p>
  </td>
  <td>
  <p><span>OFF</span></p>
  </td>
  <td>
  <p><span>NO-OP</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>SSL_OP_DONT_INSERT_EMPTY_FRAGMENTS</span></p>
  </td>
  <td>
  <p><span>ON</span></p>
  </td>
  <td>
  <p><span>NO-OP</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>SSL_OP_LEGACY_SERVER_CONNECT</span></p>
  </td>
  <td>
  <p><span>OFF</span></p>
  </td>
  <td>
  <p><span>NO-OP</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>SSL_OP_NO_COMPRESSION</span></p>
  </td>
  <td>
  <p><span>ON</span></p>
  </td>
  <td>
  <p><span>NO-OP</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>SSL_OP_NO_RENEGOTIATION</span></p>
  </td>
  <td>
  <p><span>ON</span></p>
  </td>
  <td>
  <p><span>NO-OP<br>
  <br>
  Renegotiation is enabled with </span><span style='font-size:10.0pt;
  font-family:"Courier New"'>SSL_set_renegotiate_mode</span>
  <span>, an AWS-LC/BoringSSL specific
  API.</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>SSL_OP_NO_SESSION_RESUMPTION_ON_RENEGOTIATION</span></p>
  </td>
  <td>
  <p><span>ON</span></p>
  </td>
  <td>
  <p><span>NO-OP</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>SSL_OP_NO_SSLv3</span></p>
  </td>
  <td>
  <p><span>ON</span></p>
  </td>
  <td>
  <p><span>NO-OP</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>SSL_OP_TLS_ROLLBACK_BUG</span></p>
  </td>
  <td>
  <p><span>OFF</span></p>
  </td>
  <td>
  <p><span>NO-OP</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>SSL_VERIFY_CLIENT_ONCE</span></p>
  </td>
  <td>
  <p><span>OFF</span></p>
  </td>
  <td>
  <p><span>NO-OP</span></p>
  </td>
 </tr>
 <tr>
  <td rowspan=2>
  <p><span><a
  href="https://www.openssl.org/docs/manmaster/man3/X509_VERIFY_PARAM_get0_peername.html">SSL_set_hostflags<br>
  X509_STORE_CTX_set_flags<br>
  X509_STORE_set_flags<br>
  X509_VERIFY_PARAM_set_flags<br>
  X509_VERIFY_PARAM_set_hostflags</a></span></p>
  </td>
  <td>
  <p><span>X509_V_FLAG_X509_STRICT</span></p>
  </td>
  <td>
  <p><span>ON</span></p>
  </td>
  <td>
  <p><span>NO-OP</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>X509_V_FLAG_ALLOW_PROXY_CERTS</span></p>
  </td>
  <td>
  <p><span>OFF</span></p>
  </td>
  <td>
  <p><span>NO-OP</span></p>
  </td>
 </tr>
</table>

## libcrypto Differences

The following table contains the differences in libcrypto configuration options AWS-LC and OpenSSL provides. 

* **Everything is "OFF" and "Configurable" by default in OpenSSL.**
* Each “**Context Flag”** has a link that provides more details on the flag’s functionality (WIP)

<table border=0 cellspacing=0 cellpadding=0
 style='border-collapse:collapse'>
 <tr>
  <td>
  <p><b><span>Context Flags Setting Function</span></b></p>
  </td>
  <td>
  <p><b><span>Context Flags</span></b></p>
  </td>
  <td>
  <p><b><span>AWS-LC Default</span></b></p>
  </td>
  <td>
  <p><b><span>Configurability</span></b></p>
  </td>
 </tr>
 <tr>
  <td rowspan=6>
  <p><span><a
  href="https://www.openssl.org/docs/manmaster/man3/X509_check_host.html">X509_check_host
  <br>
  X509_check_email<br>
  X509_check_ip<br>
  X509_check_ip_asc</a></span></p>
  </td>
  <td>
  <p><span>X509_CHECK_FLAG_NO_WILDCARDS</span></p>
  </td>
  <td>
  <p><span>OFF</span></p>
  </td>
  <td>
  <p><span>Configurable</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>X509_CHECK_FLAG_NEVER_CHECK_SUBJECT</span></p>
  </td>
  <td>
  <p><span>OFF</span></p>
  </td>
  <td>
  <p><span>Configurable</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>X509_CHECK_FLAG_ALWAYS_CHECK_SUBJECT</span></p>
  </td>
  <td>
  <p><span>OFF</span></p>
  </td>
  <td>
  <p><span>NO-OP</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>X509_CHECK_FLAG_NO_PARTIAL_WILDCARDS</span></p>
  </td>
  <td>
  <p><span>ON</span></p>
  </td>
  <td>
  <p><span>NO-OP</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>X509_CHECK_FLAG_MULTI_LABEL_WILDCARDS</span></p>
  </td>
  <td>
  <p><span>OFF</span></p>
  </td>
  <td>
  <p><span>NO-OP</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>X509_CHECK_FLAG_SINGLE_LABEL_SUBDOMAINS</span></p>
  </td>
  <td>
  <p><span>OFF</span></p>
  </td>
  <td>
  <p><span>NO-OP</span></p>
  </td>
 </tr>
 <tr>
  <td rowspan=8>
  <p><span><a
  href="https://www.openssl.org/docs/manmaster/man3/PKCS7_sign.html">PKCS7_sign</a></span></p>
  </td>
  <td>
  <p><span>PKCS7_DETACHED</span></p>
  </td>
  <td>
  <p><span>OFF</span></p>
  </td>
  <td>
  <p><span>Configurable</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>PKCS7_BINARY</span></p>
  </td>
  <td rowspan=3>
  <p><i><span>Partially Supported<br>
  </span></
  i><sp><br>
  These flags must be used simultaneously together with </span>
  <span style='font-family:"Courier New"'>PKCS7_DETACHED</span>
  <span> to generate a detached RSA
  SHA-256 signature of the data and produces a PKCS#7 SignedData structure
  containing it.</span></p>
  </td>
  <td rowspan=3>
  <p><b><span>Must be used along with </span></b><b>
        <span>PKCS7_DETACHED</span></b>
  <span>. Other combinations are not
  supported<b>.</b></span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>PKCS7_NOATTR</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>PKCS7_PARTIAL</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>PKCS7_TEXT</span></p>
  </td>
  <td>
  <p><span>OFF</span></p>
  </td>
  <td>
  <p><span>NO-OP</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>PKCS7_NOCERTS</span></p>
  </td>
  <td>
  <p><span>OFF</span></p>
  </td>
  <td>
  <p><span>NO-OP</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>PKCS7_STREAM</span></p>
  </td>
  <td>
  <p><span>OFF</span></p>
  </td>
  <td>
  <p><span>NO-OP</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>PKCS7_NOSMIMECAP</span></p>
  </td>
  <td>
  <p><span>OFF</span></p>
  </td>
  <td>
  <p><span>NO-OP</span></p>
  </td>
 </tr>
 <tr>
  <td rowspan=4>
  <p><span>EVP_PKEY_assign</span></p>
  </td>
  <td>
  <p><span>EVP_PKEY_DH</span></p>
  </td>
  <td>
  <p><span>Not Supported</span></p>
  </td>
  <td>
  <p><span>NO-OP</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>EVP_PKEY_X448</span></p>
  </td>
  <td>
  <p><span>Not Supported</span></p>
  </td>
  <td>
  <p><span>NO-OP</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>EVP_PKEY_ED448</span></p>
  </td>
  <td>
  <p><span>Not Supported</span></p>
  </td>
  <td>
  <p><span>NO-OP</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>EVP_PKEY_RSA2</span></p>
  </td>
  <td>
  <p><span>Not Supported</span></p>
  </td>
  <td>
  <p><span>NO-OP</span></p>
  </td>
 </tr>
</table>

### Intentionally Omitted Configuration Flags

The following table contains configuration options AWS-LC has intentionally omitted. If your application uses a non-existent flag outlined here, it will fail to compile with AWS-LC.  

* Each “**Context Flag”** has a link that provides more details on the flag’s functionality (WIP)
* If you feel that there is a valid use case for any of these flags, feel free to [cut an issue](https://github.com/aws/aws-lc/issues/new?assignees=&labels=&projects=&template=general-issue.md&title=) to us.

<table border=0 cellspacing=0 cellpadding=0
 style='border-collapse:collapse'>
 <tr>
  <td>
  <p><b><span>Context Flags Setting Function</span></b></p>
  </td>
  <td>
  <p><b><span>Context Flags</span></b></p>
  </td>
  <td>
  <p><b><span>AWS-LC Default</span></b></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>BN_set_flags</span></p>
  </td>
  <td>
  <p><span><a
  href="https://github.com/aws/aws-lc/blob/f61870199f1bdfe3182e493231e60ea7243edbcb/include/openssl/bn.h#L1053-L1062">BN_FLG_CONSTTIME</a></span></p>
  </td>
  <td>
  <p><span>Not Implemented</span></p>
  </td>
 </tr>
 <tr>
  <td rowspan=2>
  <p><span>ASN1_aux_cb</span></p>
  </td>
  <td>
  <p><span>ASN1_OP_I2D_PRE</span></p>
  </td>
  <td>
  <p><span>Not Implemented</span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>ASN1_OP_I2D_POST</span></p>
  </td>
  <td>
  <p><span>Not Implemented</span></p>
  </td>
 </tr>
</table>
