/* Copyright (c) 2014, Google Inc.
 *
 * Permission to use, copy, modify, and/or distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
 * SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION
 * OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN
 * CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE. */

#include <openssl/base.h>

#include <stdio.h>

#if !defined(OPENSSL_WINDOWS)
#include <sys/select.h>
#include <unistd.h>
static int closesocket(int sock) {
  return close(sock);
}
#else
OPENSSL_MSVC_PRAGMA(warning(push, 3))
#include <winsock2.h>
OPENSSL_MSVC_PRAGMA(warning(pop))
#endif

#include <openssl/err.h>
#include <openssl/pem.h>
#include <openssl/ssl.h>

#include "../crypto/internal.h"
#include "internal.h"
#include "transport_common.h"


static const argument_t kArguments[] = {
    {
        "-connect", kRequiredArgument,
        "The hostname and port of the server to connect to, e.g. foo.com:443",
    },
    {
        "-cipher", kOptionalArgument,
        "An OpenSSL-style cipher suite string that configures the offered "
        "ciphers",
    },
    {
        "-curves", kOptionalArgument,
        "An OpenSSL-style ECDH curves list that configures the offered curves",
    },
    {
        "-sigalgs", kOptionalArgument,
        "An OpenSSL-style signature algorithms list that configures the "
        "signature algorithm preferences",
    },
    {
        "-max-version", kOptionalArgument,
        "The maximum acceptable protocol version",
    },
    {
        "-min-version", kOptionalArgument,
        "The minimum acceptable protocol version",
    },
    {
        "-server-name", kOptionalArgument, "The server name to advertise",
    },
    {
        "-ech-grease", kBooleanArgument, "Enable ECH GREASE",
    },
    {
        "-ech-config-list", kOptionalArgument,
        "Path to file containing serialized ECHConfigs",
    },
    {
        "-select-next-proto", kOptionalArgument,
        "An NPN protocol to select if the server supports NPN",
    },
    {
        "-alpn-protos", kOptionalArgument,
        "A comma-separated list of ALPN protocols to advertise",
    },
    {
        "-fallback-scsv", kBooleanArgument, "Enable FALLBACK_SCSV",
    },
    {
        "-ocsp-stapling", kBooleanArgument,
        "Advertise support for OCSP stabling",
    },
    {
        "-signed-certificate-timestamps", kBooleanArgument,
        "Advertise support for signed certificate timestamps",
    },
    {
        "-channel-id-key", kOptionalArgument,
        "The key to use for signing a channel ID",
    },
    {
        "-false-start", kBooleanArgument, "Enable False Start",
    },
    {
        "-session-in", kOptionalArgument,
        "A file containing a session to resume.",
    },
    {
        "-session-out", kOptionalArgument,
        "A file to write the negotiated session to.",
    },
    {
        "-key", kOptionalArgument,
        "PEM-encoded file containing the private key.",
    },
    {
        "-cert", kOptionalArgument,
        "PEM-encoded file containing the leaf certificate and optional "
        "certificate chain. This is taken from the -key argument if this "
        "argument is not provided.",
    },
    {
        "-starttls", kOptionalArgument,
        "A STARTTLS mini-protocol to run before the TLS handshake. Supported"
        " values: 'smtp'",
    },
    {
        "-grease", kBooleanArgument, "Enable GREASE",
    },
    {
        "-permute-extensions",
        kBooleanArgument,
        "Permute extensions in handshake messages",
    },
    {
        "-test-resumption", kBooleanArgument,
        "Connect to the server twice. The first connection is closed once a "
        "session is established. The second connection offers it.",
    },
    {
        "-root-certs", kOptionalArgument,
        "A filename containing one or more PEM root certificates. Implies that "
        "verification is required.",
    },
    {
        "-root-cert-dir", kOptionalArgument,
        "A directory containing one or more root certificate PEM files in "
        "OpenSSL's hashed-directory format. Implies that verification is "
        "required.",
    },
    {
        "-early-data", kOptionalArgument, "Enable early data. The argument to "
        "this flag is the early data to send or if it starts with '@', the "
        "file to read from for early data.",
    },
    {
        "-http-tunnel", kOptionalArgument,
        "An HTTP proxy server to tunnel the TCP connection through",
    },
    {
        "-renegotiate-freely", kBooleanArgument,
        "Allow renegotiations from the peer.",
    },
    {
        "-debug", kBooleanArgument,
        "Print debug information about the handshake",
    },
    {
        "", kOptionalArgument, "",
    },
};

static bssl::UniquePtr<EVP_PKEY> LoadPrivateKey(const std::string &file) {
  bssl::UniquePtr<BIO> bio(BIO_new(BIO_s_file()));
  if (!bio || !BIO_read_filename(bio.get(), file.c_str())) {
    return nullptr;
  }
  bssl::UniquePtr<EVP_PKEY> pkey(PEM_read_bio_PrivateKey(bio.get(), nullptr,
                                 nullptr, nullptr));
  return pkey;
}

static int NextProtoSelectCallback(SSL* ssl, uint8_t** out, uint8_t* outlen,
                                   const uint8_t* in, unsigned inlen, void* arg) {
  *out = reinterpret_cast<uint8_t *>(arg);
  *outlen = strlen(reinterpret_cast<const char *>(arg));
  return SSL_TLSEXT_ERR_OK;
}

static FILE *g_keylog_file = nullptr;

static void KeyLogCallback(const SSL *ssl, const char *line) {
  fprintf(g_keylog_file, "%s\n", line);
  fflush(g_keylog_file);
}

static bssl::UniquePtr<BIO> session_out;
static bssl::UniquePtr<SSL_SESSION> resume_session;

static int NewSessionCallback(SSL *ssl, SSL_SESSION *session) {
  if (session_out) {
    if (!PEM_write_bio_SSL_SESSION(session_out.get(), session) ||
        BIO_flush(session_out.get()) <= 0) {
      fprintf(stderr, "Error while saving session:\n");
      ERR_print_errors_fp(stderr);
      return 0;
    }
  }
  resume_session = bssl::UniquePtr<SSL_SESSION>(session);
  return 1;
}

static bool WaitForSession(SSL *ssl, int sock) {
  fd_set read_fds;
  FD_ZERO(&read_fds);

  if (!SocketSetNonBlocking(sock, true)) {
    return false;
  }

  while (!resume_session) {
#if defined(OPENSSL_WINDOWS)
    // Windows sockets are really of type SOCKET, not int, but everything here
    // casts them to ints. Clang gets unhappy about signed values as a result.
    //
    // TODO(davidben): Keep everything as the appropriate platform type.
    FD_SET(static_cast<SOCKET>(sock), &read_fds);
#else
    FD_SET(sock, &read_fds);
#endif
    int ret = select(sock + 1, &read_fds, NULL, NULL, NULL);
    if (ret <= 0) {
      perror("select");
      return false;
    }

    uint8_t buffer[512];
    int ssl_ret = SSL_read(ssl, buffer, sizeof(buffer));

    if (ssl_ret <= 0) {
      int ssl_err = SSL_get_error(ssl, ssl_ret);
      if (ssl_err == SSL_ERROR_WANT_READ) {
        continue;
      }
      PrintSSLError(stderr, "Error while reading", ssl_err, ssl_ret);
      return false;
    }
  }

  return true;
}

static void print_verify_details(SSL *s) {
  long verify_err = SSL_get_verify_result(s);

  if (verify_err == X509_V_OK) {
    fprintf(stdout, "Verification: OK\n");
  } else {
    const char *reason = X509_verify_cert_error_string(verify_err);
    fprintf(stdout, "Verification error: %s\n", reason);
  }
}

static void PrintOpenSSLConnectionInfo(SSL *ssl, bool show_certs) {
  STACK_OF(X509) *sk;

  sk = SSL_get_peer_cert_chain(ssl);
  if (sk != NULL) {
    fprintf(stdout, "---\nCertificate chain\n");
    for (size_t i = 0; i < sk_X509_num(sk); i++) {
      fprintf(stdout, "%2zu s:", i);
      if (X509_NAME_print_ex_fp(stdout, X509_get_subject_name(sk_X509_value(sk, i)),
                            0, XN_FLAG_ONELINE) < 0) {
        fprintf(stderr, "Error: Printing subject name failed");
      }
      fprintf(stdout, "\n   i:");
      if (X509_NAME_print_ex_fp(stdout, X509_get_issuer_name(sk_X509_value(sk, i)),
                            0, XN_FLAG_ONELINE) < 0) {
        fprintf(stderr, "Error: Printing issuer name failed");
      }
      fprintf(stdout, "\n");
      if (show_certs) {
        PEM_write_X509(stdout, sk_X509_value(sk, i));
      }
    }
  }

  fprintf(stdout, "---\n");
  bssl::UniquePtr<X509> peer(SSL_get_peer_certificate(ssl));
  if (peer) {
    fprintf(stdout, "Server certificate\n");
    PEM_write_X509(stdout, peer.get());
    fprintf(stdout, "subject=");
    if (X509_NAME_print_ex_fp(stdout, X509_get_subject_name(peer.get()),
                       0, XN_FLAG_ONELINE) < 0) {
      fprintf(stderr, "Error: Printing subject name failed");
    }
    fprintf(stdout, "\n\nissuer=");
    if (X509_NAME_print_ex_fp(stdout, X509_get_issuer_name(peer.get()),
                          0, XN_FLAG_ONELINE) < 0) {
      fprintf(stderr, "Error: Printing issuer name failed");
    }
    fprintf(stdout, "\n\n---\n");
  } else {
    fprintf(stdout, "no peer certificate available\n");
  }

  // TODO (aws-lc): we are missing some functions needed to print the following data
  //  print_ca_names(bio, s);
  //  ssl_print_sigalgs(bio, s);
  //  ssl_print_tmp_key(bio, s);

  fprintf(stdout,
             "---\nSSL handshake has read %d bytes "
             "and written %d bytes\n",
        (int)BIO_number_read(SSL_get_rbio(ssl)),
        (int)BIO_number_written(SSL_get_wbio(ssl)));
  print_verify_details(ssl);
}

static bool DoConnection(SSL_CTX *ctx,
                         std::map<std::string, std::string> args_map,
                         bool (*cb)(SSL *ssl, int sock), bool is_openssl_s_client) {
  int sock = -1;
  if (args_map.count("-http-tunnel") != 0) {
    if (!Connect(&sock, args_map["-http-tunnel"], is_openssl_s_client)) {
      return false;
    }
    if (!DoHTTPTunnel(sock, args_map["-connect"])) {
      closesocket(sock);
      return false;
    }
  } else if (!Connect(&sock, args_map["-connect"], is_openssl_s_client)) {
    return false;
  }

  // print for openssl tool
  if (is_openssl_s_client) {
    fprintf(stdout, "CONNECTED(%08d)\n", sock);
  }

  if (args_map.count("-starttls") != 0) {
    const std::string& starttls = args_map["-starttls"];
    if (starttls == "smtp") {
      if (!DoSMTPStartTLS(sock)) {
        closesocket(sock);
        return false;
      }
    } else {
      closesocket(sock);
      fprintf(stderr, "Unknown value for -starttls: %s\n", starttls.c_str());
      return false;
    }
  }

  // BIO takes ownership of |sock| from this point forward.
  bssl::UniquePtr<BIO> bio(BIO_new_socket(sock, BIO_CLOSE));
  bssl::UniquePtr<SSL> ssl(SSL_new(ctx));

  if (args_map.count("-server-name") != 0) {
    if (!SSL_set_tlsext_host_name(ssl.get(),
                                  args_map["-server-name"].c_str())) {
      return false;
    }
  }

  if (args_map.count("-ech-grease") != 0) {
    SSL_set_enable_ech_grease(ssl.get(), 1);
  }

  if (args_map.count("-ech-config-list") != 0) {
    const char *filename = args_map["-ech-config-list"].c_str();
    ScopedFILE f(fopen(filename, "rb"));
    std::vector<uint8_t> data;
    if (f == nullptr || !ReadAll(&data, f.get())) {
      fprintf(stderr, "Error reading %s.\n", filename);
      return false;
    }
    if (!SSL_set1_ech_config_list(ssl.get(), data.data(), data.size())) {
      fprintf(stderr, "Error setting ECHConfigList\n");
      return false;
    }
  }

  if (args_map.count("-session-in") != 0) {
    bssl::UniquePtr<BIO> in(BIO_new_file(args_map["-session-in"].c_str(),
                                         "rb"));
    if (!in) {
      fprintf(stderr, "Error reading session\n");
      ERR_print_errors_fp(stderr);
      return false;
    }
    bssl::UniquePtr<SSL_SESSION> session(PEM_read_bio_SSL_SESSION(in.get(),
                                         nullptr, nullptr, nullptr));
    if (!session) {
      fprintf(stderr, "Error reading session\n");
      ERR_print_errors_fp(stderr);
      return false;
    }
    SSL_set_session(ssl.get(), session.get());
  }

  if (args_map.count("-renegotiate-freely") != 0) {
    SSL_set_renegotiate_mode(ssl.get(), ssl_renegotiate_freely);
  }

  if (resume_session) {
    SSL_set_session(ssl.get(), resume_session.get());
  }

  SSL_set_bio(ssl.get(), bio.get(), bio.get());
  bio.release();

  int ret = SSL_connect(ssl.get());
  if (ret != 1) {
    int ssl_err = SSL_get_error(ssl.get(), ret);
    PrintSSLError(stderr, "Error while connecting", ssl_err, ret);
    return false;
  }

  if (args_map.count("-early-data") != 0 && SSL_in_early_data(ssl.get())) {
    std::string early_data = args_map["-early-data"];
    if (early_data.size() > 0 && early_data[0] == '@') {
      const char *filename = early_data.c_str() + 1;
      std::vector<uint8_t> data;
      ScopedFILE f(fopen(filename, "rb"));
      if (f == nullptr || !ReadAll(&data, f.get())) {
        fprintf(stderr, "Error reading %s.\n", filename);
        return false;
      }
      early_data = std::string(data.begin(), data.end());
    }
    if (!early_data.empty()) {
      int ed_size = early_data.size();
      int ssl_ret = SSL_write(ssl.get(), early_data.data(), ed_size);
      if (ssl_ret <= 0) {
        int ssl_err = SSL_get_error(ssl.get(), ssl_ret);
        PrintSSLError(stderr, "Error while writing", ssl_err, ssl_ret);
        return false;
      } else if (ssl_ret != ed_size) {
        fprintf(stderr, "Short write from SSL_write.\n");
        return false;
      }
    }
  }

  // print for bssl
  if (!is_openssl_s_client) {
    fprintf(stderr, "Connected.\n");
    bssl::UniquePtr<BIO> bio_stderr(BIO_new_fp(stderr, BIO_NOCLOSE));
    PrintConnectionInfo(bio_stderr.get(), ssl.get());
  } else { // print for openssl
    PrintOpenSSLConnectionInfo(ssl.get(), args_map.count("-showcerts"));
  }

  return cb(ssl.get(), sock);
}

static void InfoCallback(const SSL *ssl, int type, int value) {
  switch (type) {
    case SSL_CB_HANDSHAKE_START:
      fprintf(stderr, "Handshake started.\n");
      break;
    case SSL_CB_HANDSHAKE_DONE:
      fprintf(stderr, "Handshake done.\n");
      break;
    case SSL_CB_CONNECT_LOOP:
      fprintf(stderr, "Handshake progress: %s\n", SSL_state_string_long(ssl));
      break;
  }
}

static int verify_cb(int ok, X509_STORE_CTX *ctx)
{
  X509 *err_cert = X509_STORE_CTX_get_current_cert(ctx);
  int err = X509_STORE_CTX_get_error(ctx);
  int depth = X509_STORE_CTX_get_error_depth(ctx);
  bssl::UniquePtr<BIO> bio_err(BIO_new_fp(stderr, BIO_CLOSE));

  BIO_printf(bio_err.get(), "depth=%d ", depth);
  if (err_cert != NULL) {
    X509_NAME_print_ex(bio_err.get(),
                       X509_get_subject_name(err_cert),
                       0, XN_FLAG_ONELINE);
    BIO_puts(bio_err.get(), "\n");
  } else {
    BIO_puts(bio_err.get(), "<no cert>\n");
  }

  if (!ok) {
    BIO_printf(bio_err.get(), "verify error:num=%d:%s\n", err,
               X509_verify_cert_error_string(err));
    ok = 1;
  }

  switch (err) {
    case X509_V_ERR_UNABLE_TO_GET_ISSUER_CERT:
      if (err_cert != NULL) {
        BIO_puts(bio_err.get(), "issuer= ");
        X509_NAME_print_ex(bio_err.get(), X509_get_issuer_name(err_cert),
                           0, XN_FLAG_ONELINE);
        BIO_puts(bio_err.get(), "\n");
      }
      ok = 1;
      break;
    case X509_V_ERR_CERT_NOT_YET_VALID:
    case X509_V_ERR_ERROR_IN_CERT_NOT_BEFORE_FIELD:
      if (err_cert != NULL) {
        BIO_printf(bio_err.get(), "notBefore=");
        ASN1_TIME_print(bio_err.get(), X509_get0_notBefore(err_cert));
        BIO_printf(bio_err.get(), "\n");
      }
      ok = 1;
      break;
    case X509_V_ERR_CERT_HAS_EXPIRED:
    case X509_V_ERR_ERROR_IN_CERT_NOT_AFTER_FIELD:
      if (err_cert != NULL) {
        BIO_printf(bio_err.get(), "notAfter=");
        ASN1_TIME_print(bio_err.get(), X509_get0_notAfter(err_cert));
        BIO_printf(bio_err.get(), "\n");
      }
      ok = 1;
      break;
    case X509_V_ERR_NO_EXPLICIT_POLICY:
      ok = 1;
      break;
  }

  BIO_printf(bio_err.get(), "verify return:%d\n", ok);
  return ok;
}

bool Client(const std::vector<std::string> &args) {
  std::map<std::string, std::string> args_map;
  args_list_t extra_args;

  if (!ParseKeyValueArguments(args_map, extra_args, args, kArguments) ||
      extra_args.size() > 0) {
    PrintUsage(kArguments);
    return false;
  }

  return DoClient(args_map, false);
}

bool DoClient(std::map<std::string, std::string> args_map, bool is_openssl_s_client) {
  if (!InitSocketLibrary()) {
    return false;
  }

  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));

  const char *keylog_file = getenv("SSLKEYLOGFILE");
  if (keylog_file) {
    g_keylog_file = fopen(keylog_file, "a");
    if (g_keylog_file == nullptr) {
      perror("fopen");
      return false;
    }
    SSL_CTX_set_keylog_callback(ctx.get(), KeyLogCallback);
  }

  if (args_map.count("-cipher") != 0 &&
      !SSL_CTX_set_strict_cipher_list(ctx.get(), args_map["-cipher"].c_str())) {
    fprintf(stderr, "Failed setting cipher list\n");
    return false;
  }

  if (args_map.count("-curves") != 0 &&
      !SSL_CTX_set1_curves_list(ctx.get(), args_map["-curves"].c_str())) {
    fprintf(stderr, "Failed setting curves list\n");
    return false;
  }

  if (args_map.count("-sigalgs") != 0 &&
      !SSL_CTX_set1_sigalgs_list(ctx.get(), args_map["-sigalgs"].c_str())) {
    fprintf(stderr, "Failed setting signature algorithms list\n");
    return false;
  }

  uint16_t max_version = TLS1_3_VERSION;
  if (args_map.count("-max-version") != 0 &&
      !VersionFromString(&max_version, args_map["-max-version"])) {
    fprintf(stderr, "Unknown protocol version: '%s'\n",
            args_map["-max-version"].c_str());
    return false;
  }

  if (!SSL_CTX_set_max_proto_version(ctx.get(), max_version)) {
    return false;
  }

  if (args_map.count("-min-version") != 0) {
    uint16_t version;
    if (!VersionFromString(&version, args_map["-min-version"])) {
      fprintf(stderr, "Unknown protocol version: '%s'\n",
              args_map["-min-version"].c_str());
      return false;
    }
    if (!SSL_CTX_set_min_proto_version(ctx.get(), version)) {
      return false;
    }
  }

  if (args_map.count("-select-next-proto") != 0) {
    const std::string &proto = args_map["-select-next-proto"];
    if (proto.size() > 255) {
      fprintf(stderr, "Bad NPN protocol: '%s'\n", proto.c_str());
      return false;
    }
    // |SSL_CTX_set_next_proto_select_cb| is not const-correct.
    SSL_CTX_set_next_proto_select_cb(ctx.get(), NextProtoSelectCallback,
                                     const_cast<char *>(proto.c_str()));
  }

  if (args_map.count("-alpn-protos") != 0) {
    const std::string &alpn_protos = args_map["-alpn-protos"];
    std::vector<uint8_t> wire;
    size_t i = 0;
    while (i <= alpn_protos.size()) {
      size_t j = alpn_protos.find(',', i);
      if (j == std::string::npos) {
        j = alpn_protos.size();
      }
      size_t len = j - i;
      if (len > 255) {
        fprintf(stderr, "Invalid ALPN protocols: '%s'\n", alpn_protos.c_str());
        return false;
      }
      wire.push_back(static_cast<uint8_t>(len));
      wire.resize(wire.size() + len);
      OPENSSL_memcpy(wire.data() + wire.size() - len, alpn_protos.data() + i,
                     len);
      i = j + 1;
    }
    if (SSL_CTX_set_alpn_protos(ctx.get(), wire.data(), wire.size()) != 0) {
      return false;
    }
  }

  if (args_map.count("-fallback-scsv") != 0) {
    SSL_CTX_set_mode(ctx.get(), SSL_MODE_SEND_FALLBACK_SCSV);
  }

  if (args_map.count("-ocsp-stapling") != 0) {
    SSL_CTX_enable_ocsp_stapling(ctx.get());
  }

  if (args_map.count("-signed-certificate-timestamps") != 0) {
    SSL_CTX_enable_signed_cert_timestamps(ctx.get());
  }

  if (args_map.count("-channel-id-key") != 0) {
    bssl::UniquePtr<EVP_PKEY> pkey =
        LoadPrivateKey(args_map["-channel-id-key"]);
    if (!pkey || !SSL_CTX_set1_tls_channel_id(ctx.get(), pkey.get())) {
      return false;
    }
  }

  if (args_map.count("-false-start") != 0) {
    SSL_CTX_set_mode(ctx.get(), SSL_MODE_ENABLE_FALSE_START);
  }

  if (args_map.count("-key") != 0) {
    const std::string &key = args_map["-key"];
    if (!SSL_CTX_use_PrivateKey_file(ctx.get(), key.c_str(),
                                     SSL_FILETYPE_PEM)) {
      fprintf(stderr, "Failed to load private key: %s\n", key.c_str());
      return false;
    }
    const std::string &cert =
        args_map.count("-cert") != 0 ? args_map["-cert"] : key;
    if (!SSL_CTX_use_certificate_chain_file(ctx.get(), cert.c_str())) {
      fprintf(stderr, "Failed to load cert chain: %s\n", cert.c_str());
      return false;
    }
  }

  SSL_CTX_set_session_cache_mode(ctx.get(), SSL_SESS_CACHE_CLIENT);
  SSL_CTX_sess_set_new_cb(ctx.get(), NewSessionCallback);

  if (args_map.count("-session-out") != 0) {
    session_out.reset(BIO_new_file(args_map["-session-out"].c_str(), "wb"));
    if (!session_out) {
      fprintf(stderr, "Error while opening %s:\n",
              args_map["-session-out"].c_str());
      ERR_print_errors_fp(stderr);
      return false;
    }
  }

  if (args_map.count("-grease") != 0) {
    SSL_CTX_set_grease_enabled(ctx.get(), 1);
  }

  if (args_map.count("-permute-extensions") != 0) {
    SSL_CTX_set_permute_extensions(ctx.get(), 1);
  }

  std::string certPathFlag;
  int verify = SSL_VERIFY_NONE;
  if (args_map.count("-root-certs") != 0) {
    certPathFlag = "-root-certs";
    verify = SSL_VERIFY_PEER;
  }
  // For the OpenSSL tool, simply specifying -CAfile does not imply verification
  if (args_map.count("-CAfile") != 0) {
    certPathFlag = "-CAfile";
  }
  if (!certPathFlag.empty()) {
    if (!SSL_CTX_load_verify_locations(
            ctx.get(), args_map[certPathFlag].c_str(), nullptr)) {
      fprintf(stderr, "Failed to load root certificates.\n");
      ERR_print_errors_fp(stderr);
      return false;
    }
  }

  certPathFlag = "";
  if (args_map.count("-root-cert-dir") != 0) {
    certPathFlag = "-root-cert-dir";
    verify = SSL_VERIFY_PEER;
  }
  // For the OpenSSL tool, simply specifying -CApath does not imply verification
  if (args_map.count("-CApath") != 0) {
    certPathFlag = "-CApath";
  }

  if (!certPathFlag.empty()) {
    if (!SSL_CTX_load_verify_locations(
            ctx.get(), nullptr, args_map[certPathFlag].c_str())) {
      fprintf(stderr, "Failed to load root certificates.\n");
      ERR_print_errors_fp(stderr);
      return false;
    }
  }

  if (args_map.count("-verify") != 0) {
    unsigned int depth;
    if (!GetUnsigned(&depth, "-verify", 0, args_map)) {
      fprintf(stderr, "s_client: Can't parse \"%s\" as a number\n", args_map.find("-verify")->second.c_str());
      return false;
    }
    fprintf(stdout, "verify depth is %d\n", (int)depth);
    verify = SSL_VERIFY_PEER;
  }

  if (is_openssl_s_client) { // openssl tool
    SSL_CTX_set_verify(ctx.get(), verify, verify_cb);
  } else {
    SSL_CTX_set_verify(ctx.get(), verify, nullptr);
  }

  if (args_map.count("-early-data") != 0) {
    SSL_CTX_set_early_data_enabled(ctx.get(), 1);
  }

  if (args_map.count("-debug") != 0) {
    SSL_CTX_set_info_callback(ctx.get(), InfoCallback);
  }

  if (args_map.count("-test-resumption") != 0) {
    if (args_map.count("-session-in") != 0) {
      fprintf(stderr,
              "Flags -session-in and -test-resumption are incompatible.\n");
      return false;
    }

    if (!DoConnection(ctx.get(), args_map, &WaitForSession, is_openssl_s_client)) {
      return false;
    }
  }

  return DoConnection(ctx.get(), args_map, &TransferData, is_openssl_s_client);
}
