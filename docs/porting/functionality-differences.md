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

<table class=MsoNormalTable border=0 cellspacing=0 cellpadding=0
 style='border-collapse:collapse'>
 <tr>
  <td style='border:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><b><span
  style='font-family:"Times New Roman",serif'>Related Functionality</span></b></p>
  </td>
  <td style='border:solid #E6E6E6 1.0pt;border-left:none;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><b><span
  style='font-family:"Times New Roman",serif'>Details</span></b></p>
  </td>
  <td style='border:solid #E6E6E6 1.0pt;border-left:none;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><b><span
  style='font-family:"Times New Roman",serif'>No-op function</span></b></p>
  </td>
  <td style='border:solid #E6E6E6 1.0pt;border-left:none;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><b><span
  style='font-family:"Times New Roman",serif'>Return value</span></b></p>
  </td>
 </tr>
 <tr>
  <td rowspan=2 style='border:solid #E6E6E6 1.0pt;border-top:none;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Security Levels</span></p>
  </td>
  <td rowspan=2 style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'><a
  href="https://github.com/aws/aws-lc/blob/0aaec70548c91e755918452713e0419eadb032bb/include/openssl/ssl.h#L5211-L5240">ssl.h<br>
  Security Levels</a></span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>SSL_CTX_get_security_level</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Returns zero.</span></p>
  </td>
 </tr>
 <tr>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>SSL_CTX_set_security_level</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Does nothing.</span></p>
  </td>
 </tr>
 <tr>
  <td rowspan=4 style='border:solid #E6E6E6 1.0pt;border-top:none;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>DH ciphersuites</span></p>
  </td>
  <td rowspan=4 style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'><a
  href="https://github.com/aws/aws-lc/blob/0aaec70548c91e755918452713e0419eadb032bb/include/openssl/ssl.h#L5148-L5161">ssl.h
  <br>
  Deprecated DH functions</a></span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>SSL_CTX_set_tmp_dh</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Returns one.</span></p>
  </td>
 </tr>
 <tr>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>SSL_set_tmp_dh</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Returns one.</span></p>
  </td>
 </tr>
 <tr>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>SSL_CTX_set_tmp_dh_callback</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Does nothing.</span></p>
  </td>
 </tr>
 <tr>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>SSL_set_tmp_dh_callback</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Does nothing.</span></p>
  </td>
 </tr>
 <tr>
  <td rowspan=6 style='border:solid #E6E6E6 1.0pt;border-top:none;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>SSL_COMP</span><span
  style='font-family:"Times New Roman",serif'> and </span><span
  style='font-size:10.0pt;font-family:"Courier New"'>COMP_METHOD</span></p>
  </td>
  <td rowspan=6 style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'><a
  href="https://github.com/aws/aws-lc/blob/0aaec70548c91e755918452713e0419eadb032bb/include/openssl/ssl.h#L4938-L4957">ssl.h
  <br>
  Deprecated COMP functions</a></span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>SSL_COMP_get_compression_methods</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Returns NULL.</span></p>
  </td>
 </tr>
 <tr>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>SSL_COMP_add_compression_method</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Returns one.</span></p>
  </td>
 </tr>
 <tr>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>SSL_COMP_get_name</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Returns NULL.</span></p>
  </td>
 </tr>
 <tr>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>SSL_COMP_free_compression_methods</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Does nothing.</span></p>
  </td>
 </tr>
 <tr>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>SSL_get_current_compression</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Returns NULL.</span></p>
  </td>
 </tr>
 <tr>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>SSL_get_current_expansion</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Returns NULL.</span></p>
  </td>
 </tr>
 <tr>
  <td style='border:solid #E6E6E6 1.0pt;border-top:none;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>TLS Renegotiation</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'><a
  href="https://github.com/aws/aws-lc/blob/0aaec70548c91e755918452713e0419eadb032bb/include/openssl/ssl.h#L4542-L4609">ssl.h<br>
  TLS Renegotiation</a></span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>SSL_renegotiate</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Returns 1 on success, 0 on
  failure. <br>
  <br>
  There is no support for renegotiation for TLS as a server or DTLS. <br>
  <br>
  There is only minimal support for initiating renegotiation as a client. </span><span
  style='font-size:10.0pt;font-family:"Courier New"'>SSL_set_renegotiate_mode</span><span
  style='font-family:"Times New Roman",serif'> must be set to </span><span
  style='font-size:10.0pt;font-family:"Courier New"'>ssl_renegotiate_once</span><span
  style='font-family:"Times New Roman",serif'>, </span><span style='font-size:
  10.0pt;font-family:"Courier New"'>ssl_renegotiate_freely</span><span
  style='font-family:"Times New Roman",serif'>, or </span><span
  style='font-size:10.0pt;font-family:"Courier New"'>ssl_renegotiate_explicit</span><span
  style='font-family:"Times New Roman",serif'> for </span><span
  style='font-size:10.0pt;font-family:"Courier New"'>SSL_renegotiate</span><span
  style='font-family:"Times New Roman",serif'> to work.</span></p>
  </td>
 </tr>
 <tr>
  <td rowspan=3 style='border:solid #E6E6E6 1.0pt;border-top:none;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>General</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'><a
  href="https://github.com/aws/aws-lc/blob/0aaec70548c91e755918452713e0419eadb032bb/include/openssl/ssl.h#L5085-L5087">ssl.h<br>
  SSL_get_shared_ciphers</a></span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>SSL_get_shared_ciphers</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Writes an empty string and
  returns a pointer containing it or returns NULL.</span></p>
  </td>
 </tr>
 <tr>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'><a
  href="https://github.com/aws/aws-lc/blob/0aaec70548c91e755918452713e0419eadb032bb/include/openssl/ssl.h#L5089-L5092">ssl.h<br>
  SSL_get_shared_sigalgs</a></span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>SSL_get_shared_sigalgs</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Returns zero.</span></p>
  </td>
 </tr>
 <tr>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'><a
  href="https://github.com/aws/aws-lc/blob/0aaec70548c91e755918452713e0419eadb032bb/include/openssl/ssl.h#L5145-L5146C20">ssl.h<br>
  SSL_get_server_tmp_key</a></span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>SSL_get_server_tmp_key</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Returns zero.</span></p>
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
|ECDHE-RSA-AES256-SHA384	|X	|	|
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

**When migrating to AWS-LC, it is important to understand the specific libcrypto components your application is reliant on from OpenSSL. For example, there may be underlying differences when consuming** **X509 certificate verification** **from AWS-LC.** <ins>**Migrators to AWS-LC are expected to understand their intended use cases and have tests surrounding functionality they are dependent on.**</ins> AWS-LC provides test coverage for functional and cryptographic correctness, along with compliance with standards like PKCS and X509. Different cryptographic libraries may implement some behavior by convention that is not standardized and thus is not guaranteed to work the same way in AWS-LC. Customers are responsible for writing their own tests to determine whether they are affected by these kinds of differences, and AWS-LC will publish a list of known differences in the future.

**If you have a valid use case for any missing functionality or if anything is not clarified in our documentation, feel free to [cut an issue](https://github.com/aws/aws-lc/issues/new?assignees=&labels=&projects=&template=general-issue.md&title=) or create a PR to let us know.**

### libcrypto No-ops

<table class=MsoNormalTable border=0 cellspacing=0 cellpadding=0
 style='border-collapse:collapse'>
 <tr>
  <td style='border:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><b><span
  style='font-family:"Times New Roman",serif'>Related Functionality</span></b></p>
  </td>
  <td style='border:solid #E6E6E6 1.0pt;border-left:none;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><b><span
  style='font-family:"Times New Roman",serif'>Details</span></b></p>
  </td>
  <td style='border:solid #E6E6E6 1.0pt;border-left:none;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><b><span
  style='font-family:"Times New Roman",serif'>No-op function</span></b></p>
  </td>
  <td style='border:solid #E6E6E6 1.0pt;border-left:none;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><b><span
  style='font-family:"Times New Roman",serif'>Return value</span></b></p>
  </td>
 </tr>
 <tr>
  <td rowspan=5 style='border:solid #E6E6E6 1.0pt;border-top:none;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>EVP_PKEY</span></p>
  </td>
  <td rowspan=2 style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'><a
  href="https://github.com/aws/aws-lc/blob/0aaec70548c91e755918452713e0419eadb032bb/include/openssl/evp.h#L182">evp.h</a><br>
  <a href="https://github.com/aws/aws-lc/blob/main/PORTING.md#dsa-evp_pkeys">EVP_PKEY_DSA</a></span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>EVP_PKEY_CTX_set_dsa_paramgen_bits</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Returns zero.</span></p>
  </td>
 </tr>
 <tr>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>EVP_PKEY_CTX_set_dsa_paramgen_q_bits</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Returns zero.</span></p>
  </td>
 </tr>
 <tr>
  <td rowspan=2 style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'><a
  href="https://github.com/aws/aws-lc/blob/0aaec70548c91e755918452713e0419eadb032bb/include/openssl/evp.h#L932-L934">evp.h</a></span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>EVP_PKEY_get0_DH</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Returns NULL.</span></p>
  </td>
 </tr>
 <tr>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>EVP_PKEY_get1_DH</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Returns NULL.</span></p>
  </td>
 </tr>
 <tr>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'><a
  href="https://github.com/aws/aws-lc/blob/0aaec70548c91e755918452713e0419eadb032bb/include/openssl/evp.h#L948-L951">evp.h</a></span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>EVP_PKEY_get0</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Void function that does not
  return anything (NULL).</span></p>
  </td>
 </tr>
 <tr>
  <td rowspan=6 style='border:solid #E6E6E6 1.0pt;border-top:none;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>EC</span></p>
  </td>
  <td rowspan=3 style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'><a
  href="https://github.com/aws/aws-lc/blob/5c358103c5df836b9343bf995717b5bc13d5e82f/include/openssl/ec_key.h#L314-L315">ec_key.h<br>
  </a><br>
  <a
  href="https://github.com/aws/aws-lc/blob/5c358103c5df836b9343bf995717b5bc13d5e82f/include/openssl/ec.h#L413-L417">ec.h</a></span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>EC_KEY_set_asn1_flag</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Does nothing.</span></p>
  </td>
 </tr>
 <tr>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>EC_GROUP_set_asn1_flag</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Does nothing.</span></p>
  </td>
 </tr>
 <tr>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>EC_GROUP_get_asn1_flag</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Returns </span><span
  style='font-size:10.0pt;font-family:"Courier New"'>OPENSSL_EC_NAMED_CURVE</span><span
  style='font-family:"Times New Roman",serif'>.</span></p>
  </td>
 </tr>
 <tr>
  <td rowspan=2 style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'><a
  href="https://github.com/aws/aws-lc/blob/5c358103c5df836b9343bf995717b5bc13d5e82f/include/openssl/ec.h#L419-L425">ec.h</a></span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>EC_GROUP_method_of</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Returns a dummy non-NULL
  EC_METHOD pointer.</span></p>
  </td>
 </tr>
 <tr>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>EC_METHOD_get_field_type</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Returns </span><span
  style='font-size:10.0pt;font-family:"Courier New"'>NID_X9_62_prime_field</span><span
  style='font-family:"Times New Roman",serif'>.</span></p>
  </td>
 </tr>
 <tr>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'><a
  href="https://github.com/aws/aws-lc/blob/5c358103c5df836b9343bf995717b5bc13d5e82f/include/openssl/ec.h#L427-L431">ec.h</a></span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>EC_GROUP_set_point_conversion_form</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Returns nothing as a void
  function. Aborts if a form other than</span><span style='font-size:10.0pt;
  font-family:"Courier New"'> POINT_CONVERSION_UNCOMPRESSED</span><span
  style='font-family:"Times New Roman",serif'> is requested.</span></p>
  </td>
 </tr>
 <tr>
  <td rowspan=4 style='border:solid #E6E6E6 1.0pt;border-top:none;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>CONF modules</span></p>
  </td>
  <td rowspan=4 style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'><a
  href="https://github.com/aws/aws-lc/blob/5c358103c5df836b9343bf995717b5bc13d5e82f/include/openssl/conf.h#L134-L147">conf.h</a></span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>CONF_modules_load_file</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Returns one.</span></p>
  </td>
 </tr>
 <tr>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>CONF_modules_unload</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Does nothing.</span></p>
  </td>
 </tr>
 <tr>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>CONF_modules_finish</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Does nothing.</span></p>
  </td>
 </tr>
 <tr>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>CONF_modules_free</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Does nothing.</span></p>
  </td>
 </tr>
 <tr>
  <td rowspan=13 style='border:solid #E6E6E6 1.0pt;border-top:none;padding:
  .75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>RAND Functions</span></p>
  </td>
  <td rowspan=13 style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'><a
  href="https://github.com/aws/aws-lc/blob/5c358103c5df836b9343bf995717b5bc13d5e82f/crypto/fipsmodule/FIPS.md#entropy-sources">Entropy
  Sources</a></span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>RAND_load_file</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Returns a non-negative number.</span></p>
  </td>
 </tr>
 <tr>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>RAND_write_file</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Does nothing and returns negative
  one.</span></p>
  </td>
 </tr>
 <tr>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>RAND_file_name</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Returns NULL.</span></p>
  </td>
 </tr>
 <tr>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>RAND_add</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Does nothing.</span></p>
  </td>
 </tr>
 <tr>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>RAND_egd</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Returns 255.</span></p>
  </td>
 </tr>
 <tr>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>RAND_poll</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Returns one.</span></p>
  </td>
 </tr>
 <tr>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>RAND_status</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Returns one.</span></p>
  </td>
 </tr>
 <tr>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>RAND_cleanup</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Does nothing.</span></p>
  </td>
 </tr>
 <tr>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>RAND_SSLeay</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Returns a dummy </span><span
  style='font-size:10.0pt;font-family:"Courier New"'>RAND_METHOD</span><span
  style='font-family:"Times New Roman",serif'> pointer.</span></p>
  </td>
 </tr>
 <tr>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>RAND_OpenSSL</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Returns a dummy </span><span
  style='font-size:10.0pt;font-family:"Courier New"'>RAND_METHOD</span><span
  style='font-family:"Times New Roman",serif'> pointer.</span></p>
  </td>
 </tr>
 <tr>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>RAND_get_rand_method</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Returns a dummy </span><span
  style='font-size:10.0pt;font-family:"Courier New"'>RAND_METHOD</span><span
  style='font-family:"Times New Roman",serif'> pointer.</span></p>
  </td>
 </tr>
 <tr>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>RAND_set_rand_method</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Returns one.</span></p>
  </td>
 </tr>
 <tr>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>RAND_keep_random_devices_open</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Does nothing.</span></p>
  </td>
 </tr>
 <tr>
  <td rowspan=4 style='border:solid #E6E6E6 1.0pt;border-top:none;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>ASN1</span></p>
  </td>
  <td rowspan=4 style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'><a
  href="https://github.com/aws/aws-lc/blob/5c358103c5df836b9343bf995717b5bc13d5e82f/include/openssl/asn1.h#L1894-L1904">asn1.h</a></span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>ASN1_STRING_set_default_mask</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Does nothing.</span></p>
  </td>
 </tr>
 <tr>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>ASN1_STRING_set_default_mask_asc</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Returns one.</span></p>
  </td>
 </tr>
 <tr>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>ASN1_STRING_get_default_mask</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Returns </span><span
  style='font-size:10.0pt;font-family:"Courier New"'>B_ASN1_UTF8STRING</span><span
  style='font-family:"Times New Roman",serif'> (The default value AWS-LC uses).</span></p>
  </td>
 </tr>
 <tr>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>ASN1_STRING_TABLE_cleanup</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Does nothing.</span></p>
  </td>
 </tr>
 <tr>
  <td rowspan=16 style='border:solid #E6E6E6 1.0pt;border-top:none;padding:
  .75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Thread Safety</span></p>
  </td>
  <td rowspan=16 style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'><a
  href="https://github.com/aws/aws-lc/blob/5c358103c5df836b9343bf995717b5bc13d5e82f/API-CONVENTIONS.md#thread-safety">Thread
  safety</a></span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>CRYPTO_num_locks</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Returns one.</span></p>
  </td>
 </tr>
 <tr>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>CRYPTO_set_locking_callback</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Does nothing.</span></p>
  </td>
 </tr>
 <tr>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>CRYPTO_set_add_lock_callback</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Does nothing.</span></p>
  </td>
 </tr>
 <tr>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>CRYPTO_get_locking_callback</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Returns NULL.</span></p>
  </td>
 </tr>
 <tr>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>CRYPTO_get_lock_name</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Returns a fixed dummy string
  (&quot;</span><span style='font-size:10.0pt;font-family:"Courier New"'>No
  old-style OpenSSL locks anymore&quot;)</span></p>
  </td>
 </tr>
 <tr>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>CRYPTO_THREADID_set_callback</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Returns one.</span></p>
  </td>
 </tr>
 <tr>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>CRYPTO_THREADID_set_numeric</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Does nothing.</span></p>
  </td>
 </tr>
 <tr>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>CRYPTO_THREADID_set_pointer</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Does nothing.</span></p>
  </td>
 </tr>
 <tr>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>CRYPTO_THREADID_current</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Does nothing.</span></p>
  </td>
 </tr>
 <tr>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>CRYPTO_set_id_callback</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Does nothing.</span></p>
  </td>
 </tr>
 <tr>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>CRYPTO_set_dynlock_create_callback</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Does nothing.</span></p>
  </td>
 </tr>
 <tr>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>CRYPTO_set_dynlock_lock_callback</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Does nothing.</span></p>
  </td>
 </tr>
 <tr>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>CRYPTO_set_dynlock_destroy_callback</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Does nothing.</span></p>
  </td>
 </tr>
 <tr>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>CRYPTO_get_dynlock_create_callback</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Returns NULL.</span></p>
  </td>
 </tr>
 <tr>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>CRYPTO_get_dynlock_lock_callback</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Returns NULL.</span></p>
  </td>
 </tr>
 <tr>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>CRYPTO_get_dynlock_destroy_callback</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Returns NULL.</span></p>
  </td>
 </tr>
 <tr>
  <td rowspan=13 style='border:solid #E6E6E6 1.0pt;border-top:none;padding:
  .75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Miscellaneous</span></p>
  </td>
  <td rowspan=5 style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'><a
  href="https://github.com/aws/aws-lc/blob/5c358103c5df836b9343bf995717b5bc13d5e82f/include/openssl/evp.h#L961-L975">evp.h</a></span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>OpenSSL_add_all_algorithms</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Does nothing.</span></p>
  </td>
 </tr>
 <tr>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>OPENSSL_add_all_algorithms_conf</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Does nothing.</span></p>
  </td>
 </tr>
 <tr>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>OpenSSL_add_all_ciphers</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Does nothing.</span></p>
  </td>
 </tr>
 <tr>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>OpenSSL_add_all_digests</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Does nothing.</span></p>
  </td>
 </tr>
 <tr>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>EVP_cleanup</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Does nothing.</span></p>
  </td>
 </tr>
 <tr>
  <td rowspan=2 style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'><a
  href="https://github.com/aws/aws-lc/blob/5c358103c5df836b9343bf995717b5bc13d5e82f/include/openssl/cipher.h#L561-L566">cipher.h</a></span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>EVP_CIPHER_CTX_set_flags</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Does nothing.<br>
  <br>
  This functions sets flags for </span><span style='font-size:10.0pt;
  font-family:"Courier New"'>EVP_CIPHER_CTX</span><span style='font-family:
  "Times New Roman",serif'>, so any related flags are also no-ops. Related
  no-op flags can be found in <a
  href="https://github.com/aws/aws-lc/blob/5c358103c5df836b9343bf995717b5bc13d5e82f/include/openssl/cipher.h#L560-L566">the
  surrounding documentation</a>.</span></p>
  </td>
 </tr>
 <tr>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>EVP_add_cipher_alias</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Does nothing and returns one</span></p>
  </td>
 </tr>
 <tr>
  <td rowspan=2 style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'><a
  href="https://github.com/aws/aws-lc/blob/5c358103c5df836b9343bf995717b5bc13d5e82f/include/openssl/digest.h#L303-L310">digest.h</a></span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>EVP_MD_CTX_set_flags</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Does nothing.<br>
  <br>
  This functions sets flags for </span><span style='font-size:10.0pt;
  font-family:"Courier New"'>EVP_MD_CTX</span><span style='font-family:"Times New Roman",serif'>,
  so any related flags are also no-ops. Related no-op flags can be found in <a
  href="https://github.com/aws/aws-lc/blob/c8d82c7599449609d3540eefb7972f137fc1b872/include/openssl/digest.h#L303-L310">the
  surrounding documentation</a>.</span></p>
  </td>
 </tr>
 <tr>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>EVP_add_digest</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Does nothing and returns one</span></p>
  </td>
 </tr>
 <tr>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'><a
  href="https://github.com/aws/aws-lc/blob/5c358103c5df836b9343bf995717b5bc13d5e82f/include/openssl/dh.h#L351-L360">dh.h</a></span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>DH_clear_flags</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Does nothing.<br>
  <br>
  <br>
  This functions clears flags for </span><span style='font-size:10.0pt;
  font-family:"Courier New"'>DH</span><span style='font-family:"Times New Roman",serif'>,
  so any related flags are also no-ops. Related no-op flags can be found in <a
  href="https://github.com/aws/aws-lc/blob/c8d82c7599449609d3540eefb7972f137fc1b872/include/openssl/dh.h#L351-L360">the
  surrounding documentation</a>.</span></p>
  </td>
 </tr>
 <tr>
  <td rowspan=2 style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'><a
  href="https://github.com/aws/aws-lc/blob/5c358103c5df836b9343bf995717b5bc13d5e82f/include/openssl/ex_data.h#L180-L185">ex_data.h</a></span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>CRYPTO_cleanup_all_ex_data</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Does nothing.</span></p>
  </td>
 </tr>
 <tr>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>CRYPTO_EX_dup</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Legacy Callback function that's
  ignored.</span></p>
  </td>
 </tr>
 <tr>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'><a
  href="https://github.com/aws/aws-lc/blob/5c358103c5df836b9343bf995717b5bc13d5e82f/include/openssl/bio.h#L865-L866">bio.h</a></span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-size:10.0pt;font-family:"Courier New"'>BIO_set_write_buffer_size</span></p>
  </td>
  <td style='border-top:none;border-left:none;border-bottom:solid #E6E6E6 1.0pt;
  border-right:solid #E6E6E6 1.0pt;padding:.75pt .75pt .75pt .75pt'>
  <p class=MsoNormal align=center style='text-align:center'><span
  style='font-family:"Times New Roman",serif'>Returns zero.</span></p>
  </td>
 </tr>
</table>
