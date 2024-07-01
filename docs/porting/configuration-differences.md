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
  <p>
    <span>
      <a href="https://github.com/aws/aws-lc/blob/e91524c10ad698fd56f77289ba3430baf3c7af64/include/openssl/ssl.h#L889-L892">
        SSL_CTX_set_mode<br>
        SSL_set_mode
      </a>
      <br><br>
      <a href="https://github.com/aws/aws-lc/blob/e91524c10ad698fd56f77289ba3430baf3c7af64/include/openssl/ssl.h#L894-L897">
        SSL_CTX_clear_mode<br>
        SSL_clear_mode
      </a>
    </span>
  </p>
  </td>
  <td>
  <p>
    <span>
      <a href="https://github.com/aws/aws-lc/blob/c8d82c7599449609d3540eefb7972f137fc1b872/include/openssl/ssl.h#L839-L849">
        SSL_MODE_NO_AUTO_CHAIN
      </a>
    </span>
    </p>
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
  <p><span>
    <a href="https://github.com/aws/aws-lc/blob/e91524c10ad698fd56f77289ba3430baf3c7af64/include/openssl/ssl.h#L5534-L5538">
      SSL_MODE_AUTO_RETRY
    </a>  
  </span></p>
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
  <p><span>
    <a href="https://github.com/aws/aws-lc/blob/e91524c10ad698fd56f77289ba3430baf3c7af64/include/openssl/ssl.h#L5540-L5543">
      SSL_MODE_RELEASE_BUFFERS
    </a>
  </span></p>
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
  <p><span>
    <a href="https://github.com/aws/aws-lc/blob/e91524c10ad698fd56f77289ba3430baf3c7af64/include/openssl/ssl.h#L5545-L5548">
      SSL_MODE_SEND_CLIENTHELLO_TIME
    </a>
  </span></p>
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
  <p><span>
    <a href="https://github.com/aws/aws-lc/blob/e91524c10ad698fd56f77289ba3430baf3c7af64/include/openssl/ssl.h#L5550-L5552">
      SSL_MODE_SEND_SERVERHELLO_TIME
    </a>
  </span></p>
  </td>
  <td>
  <p><span>ON</span></p>
  </td>
  <td>
  <p><span>NO-OP</span></p>
  </td>
 </tr>
 <tr>
  <td rowspan=13>
  <p>
    <span>
      <a href="https://github.com/aws/aws-lc/blob/e91524c10ad698fd56f77289ba3430baf3c7af64/include/openssl/ssl.h#L794-L797">
        SSL_CTX_set_options<br>
        SSL_set_options
      </a>
      <br><br>
      <a href="https://github.com/aws/aws-lc/blob/e91524c10ad698fd56f77289ba3430baf3c7af64/include/openssl/ssl.h#L799-L802">
        SSL_CTX_clear_options<br>
        SSL_clear_options
      </a>
    </span>
    </p>
  </td>
  <td>
  <p><span>
    <a href="https://github.com/aws/aws-lc/blob/e91524c10ad698fd56f77289ba3430baf3c7af64/include/openssl/ssl.h#L5554-L5559">
      SSL_OP_ALL
    </a>
  </span></p>
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
  <p><span>
    <a href="https://github.com/aws/aws-lc/blob/e91524c10ad698fd56f77289ba3430baf3c7af64/include/openssl/ssl.h#L5561-L5564">
      SSL_OP_ALLOW_UNSAFE_LEGACY_RENEGOTIATION
    </a>
  </span></p>
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
  <p><span>
    <a href="">
      SSL_OP_CRYPTOPRO_TLSEXT_BUG
    </a>
  </span></p>
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
  <p><span>
    <a href="https://github.com/aws/aws-lc/blob/e91524c10ad698fd56f77289ba3430baf3c7af64/include/openssl/ssl.h#L5566-L5570">
      SSL_OP_DONT_INSERT_EMPTY_FRAGMENTS
    </a>
  </span></p>
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
  <p><span>
    <a href="https://github.com/aws/aws-lc/blob/e91524c10ad698fd56f77289ba3430baf3c7af64/include/openssl/ssl.h#L5572-L5575">
      SSL_OP_LEGACY_SERVER_CONNECT
    </a>
  </span></p>
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
  <p><span>
    <a href="https://github.com/aws/aws-lc/blob/e91524c10ad698fd56f77289ba3430baf3c7af64/include/openssl/ssl.h#L5577-L5579">
      SSL_OP_NO_COMPRESSION
    </a>
  </span></p>
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
  <p><span>
    <a href="https://github.com/aws/aws-lc/blob/e91524c10ad698fd56f77289ba3430baf3c7af64/include/openssl/ssl.h#L5581-L5584">
      SSL_OP_NO_RENEGOTIATION
    </a>
  </span></p>
  </td>
  <td>
  <p><span>ON</span></p>
  </td>
  <td>
  <p>
    NO-OP<br><br>
    Renegotiation is enabled with SSL_set_renegotiate_mode, an AWS-LC/BoringSSL specific API.
  </p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>
    <a href="https://github.com/aws/aws-lc/blob/e91524c10ad698fd56f77289ba3430baf3c7af64/include/openssl/ssl.h#L5586-L5591">
      SSL_OP_NO_SESSION_RESUMPTION_ON_RENEGOTIATION
    </a>
  </span></p>
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
  <p><span>
    <a href="https://github.com/aws/aws-lc/blob/e91524c10ad698fd56f77289ba3430baf3c7af64/include/openssl/ssl.h#L5597-L5599">
      SSL_OP_NO_SSLv3
    </a>
  </span></p>
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
  <p><span>
    <a href="">
      SSL_OP_SAFARI_ECDHE_ECDSA_BUG
    </a>
  </span></p>
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
  <p><span>
    <a href="">
      SSL_OP_TLSEXT_PADDING
    </a>
  </span></p>
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
  <p><span>
    <a href="https://github.com/aws/aws-lc/blob/e91524c10ad698fd56f77289ba3430baf3c7af64/include/openssl/ssl.h#L5601-L5604">
      SSL_OP_TLS_ROLLBACK_BUG
    </a>
  </span></p>
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
  <p><span>
    <a href="https://github.com/aws/aws-lc/blob/e91524c10ad698fd56f77289ba3430baf3c7af64/include/openssl/ssl.h#L5606-L5609">
      SSL_VERIFY_CLIENT_ONCE
    </a>
  </span></p>
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
  <p>
    <span>
      <a href="https://github.com/aws/aws-lc/blob/e91524c10ad698fd56f77289ba3430baf3c7af64/include/openssl/ssl.h#L3089-L3096l">
        SSL_set_hostflags<br>
      </a>
      <!-- TODO: Update the links below once we pull in google/boringssl@5bed5b9 and other documentation commits. -->
      <a href="https://github.com/aws/aws-lc/blob/311ca381c01957c654575cd378926ffd26a19093/include/openssl/x509.h#L3463-L3464">
        X509_STORE_CTX_set_flags<br>
      </a>
      <a href="https://github.com/aws/aws-lc/blob/311ca381c01957c654575cd378926ffd26a19093/include/openssl/x509.h#L3340">
        X509_STORE_set_flags<br>
      </a>
      <a href="https://github.com/aws/aws-lc/blob/311ca381c01957c654575cd378926ffd26a19093/include/openssl/x509.h#L3541-L3542">
        X509_VERIFY_PARAM_set_flags<br>
      </a>
      <a href="https://github.com/aws/aws-lc/blob/311ca381c01957c654575cd378926ffd26a19093/include/openssl/x509.h#L3603-L3606">
        X509_VERIFY_PARAM_set_hostflags<br>
      </a>
    </span>
  </p>
  </td>
  <td>
  <p><span>
    <a href="https://github.com/aws/aws-lc/blob/10a389e1adda37889b4ef9186901df15c48846b5/include/openssl/x509.h#L3015-L3018">
      X509_V_FLAG_X509_STRICT
    </a>
  </span></p>
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
  <p><span>
    <a href="https://github.com/aws/aws-lc/blob/10a389e1adda37889b4ef9186901df15c48846b5/include/openssl/x509.h#L3019-L3021">
      X509_V_FLAG_ALLOW_PROXY_CERTS
    </a>
  </span></p>
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
  <p>
    <span>
      <a href="https://github.com/aws/aws-lc/blob/10a389e1adda37889b4ef9186901df15c48846b5/include/openssl/x509.h#L4343-L4351">
        X509_check_host<br>
      </a>
      <a href="https://github.com/aws/aws-lc/blob/10a389e1adda37889b4ef9186901df15c48846b5/include/openssl/x509.h#L4353-L4360">
        X509_check_email<br>
      </a>
      <a href="https://github.com/aws/aws-lc/blob/10a389e1adda37889b4ef9186901df15c48846b5/include/openssl/x509.h#L4362-L4369">
        X509_check_ip<br>
        X509_check_ip_asc
      </a>
    </span>
  </p>
  </td>
  <td>
  <p><span>
    <a href="https://github.com/aws/aws-lc/blob/10a389e1adda37889b4ef9186901df15c48846b5/include/openssl/x509.h#L4310-L4312">
      X509_CHECK_FLAG_NO_WILDCARDS
    </a>
  </span></p>
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
  <p><span>
    <a href="https://github.com/aws/aws-lc/blob/10a389e1adda37889b4ef9186901df15c48846b5/include/openssl/x509.h#L4314-L4316">
      X509_CHECK_FLAG_NEVER_CHECK_SUBJECT
    </a>
  </span></p>
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
  <p><span>
    <a href="https://github.com/aws/aws-lc/blob/10a389e1adda37889b4ef9186901df15c48846b5/include/openssl/x509.h#L4323-L4328">
      X509_CHECK_FLAG_ALWAYS_CHECK_SUBJECT
    </a>
  </span></p>
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
  <p><span>
    <a href="https://github.com/aws/aws-lc/blob/10a389e1adda37889b4ef9186901df15c48846b5/include/openssl/x509.h#L4318-L4321">
      X509_CHECK_FLAG_NO_PARTIAL_WILDCARDS
    </a>
  </span></p>
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
  <p><span>
    <a href="https://github.com/aws/aws-lc/blob/10a389e1adda37889b4ef9186901df15c48846b5/include/openssl/x509.h#L4330-L4334">
      X509_CHECK_FLAG_MULTI_LABEL_WILDCARDS
    </a>
  </span></p>
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
  <p><span>
    <a href="https://github.com/aws/aws-lc/blob/10a389e1adda37889b4ef9186901df15c48846b5/include/openssl/x509.h#L4336-L4341">
      X509_CHECK_FLAG_SINGLE_LABEL_SUBDOMAINS
    </a>
  </span></p>
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
  <p>
    <span>
      <a href="https://github.com/aws/aws-lc/blob/10a389e1adda37889b4ef9186901df15c48846b5/include/openssl/pkcs7.h#L231-L250">
        PKCS7_sign
      </a>
    </span>
  </p>
  </td>
  <td>
  <p><span>
    <a href="https://github.com/aws/aws-lc/blob/10a389e1adda37889b4ef9186901df15c48846b5/include/openssl/pkcs7.h#L192-L193">
      PKCS7_DETACHED
    </a>
  </span></p>
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
  <p><span>
    <a href="https://github.com/aws/aws-lc/blob/10a389e1adda37889b4ef9186901df15c48846b5/include/openssl/pkcs7.h#L195-L198">
      PKCS7_BINARY
    </a>
  </span></p>
  </td>
  <td rowspan=3>
  <p>
    <i>Partially Supported</i><br><br>
    These flags must be used simultaneously together with
    PKCS7_DETACHED to generate a detached RSA
    SHA-256 signature of the data and produces a PKCS#7 SignedData structure
    containing it.
  </p>
  </td>
  <td rowspan=3>
  <p>
    <b>Must be used along with PKCS7_DETACHED.</b>
    Other combinations are not supported.
  </p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>
    <a href="https://github.com/aws/aws-lc/blob/10a389e1adda37889b4ef9186901df15c48846b5/include/openssl/pkcs7.h#L200-L202">
      PKCS7_NOATTR
    </a>
  </span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>
    <a href="https://github.com/aws/aws-lc/blob/10a389e1adda37889b4ef9186901df15c48846b5/include/openssl/pkcs7.h#L204-L207">
      PKCS7_PARTIAL
    </a>
  </span></p>
  </td>
 </tr>
 <tr>
  <td>
  <p><span>
    <a href="https://github.com/aws/aws-lc/blob/10a389e1adda37889b4ef9186901df15c48846b5/include/openssl/pkcs7.h#L209-L211">
      PKCS7_TEXT
    </a>
  </span></p>
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
  <p><span>
    <a href="https://github.com/aws/aws-lc/blob/10a389e1adda37889b4ef9186901df15c48846b5/include/openssl/pkcs7.h#L213-L215">
      PKCS7_NOCERTS
    </a>
  </span></p>
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
  <p><span>
    <a href="https://github.com/aws/aws-lc/blob/10a389e1adda37889b4ef9186901df15c48846b5/include/openssl/pkcs7.h#L220-L223">
      PKCS7_STREAM
    </a>
  </span></p>
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
  <p><span>
    <a href="https://github.com/aws/aws-lc/blob/10a389e1adda37889b4ef9186901df15c48846b5/include/openssl/pkcs7.h#L217-L218">
      PKCS7_NOSMIMECAP
    </a>
  </span></p>
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
  <p><span>
    <a href="https://github.com/aws/aws-lc/blob/10a389e1adda37889b4ef9186901df15c48846b5/include/openssl/evp.h#L1123-L1129">
      EVP_PKEY_assign
    </a>
  </span></p>
  </td>
  <td>
  <p><span>
    <a href="https://github.com/aws/aws-lc/blob/10a389e1adda37889b4ef9186901df15c48846b5/include/openssl/evp.h#L1197-L1200">
      EVP_PKEY_DH
    </a>
  </span></p>
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
  <p><span>
    <a href="https://github.com/aws/aws-lc/blob/10a389e1adda37889b4ef9186901df15c48846b5/include/openssl/evp.h#L935-L937">
      EVP_PKEY_X448
    </a>
  </span></p>
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
  <p><span>
    <a href="https://github.com/aws/aws-lc/blob/10a389e1adda37889b4ef9186901df15c48846b5/include/openssl/evp.h#L939-L941">
      EVP_PKEY_ED448
    </a>
  </span></p>
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
  <p><span>
    <a href="https://github.com/aws/aws-lc/blob/10a389e1adda37889b4ef9186901df15c48846b5/include/openssl/evp.h#L931-L933">
      EVP_PKEY_RSA2
    </a>
  </span></p>
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
  <p>
    <span>
      <a href="https://github.com/aws/aws-lc/blob/10a389e1adda37889b4ef9186901df15c48846b5/include/openssl/bn.h#L1053-L1062">
        BN_FLG_CONSTTIME
      </a>
    </span>
  </p>
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
