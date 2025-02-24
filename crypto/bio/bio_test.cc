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

#include <algorithm>
#include <string>
#include <utility>

#include <gtest/gtest.h>

#include <openssl/bio.h>
#include <openssl/crypto.h>
#include <openssl/err.h>
#include <openssl/mem.h>

#include "../internal.h"
#include "../test/file_util.h"
#include "../test/test_util.h"

#if !defined(OPENSSL_WINDOWS)
#include <arpa/inet.h>
#include <errno.h>
#include <fcntl.h>
#include <netinet/in.h>
#include <poll.h>
#include <string.h>
#include <sys/socket.h>
#include <unistd.h>
#else
#include <io.h>
#include <fcntl.h>
OPENSSL_MSVC_PRAGMA(warning(push, 3))
#include <winsock2.h>
#include <ws2tcpip.h>
OPENSSL_MSVC_PRAGMA(warning(pop))
#endif

#if !defined(OPENSSL_WINDOWS)
using Socket = int;
#define INVALID_SOCKET (-1)
static int closesocket(int sock) { return close(sock); }
static std::string LastSocketError() { return strerror(errno); }
static const int kOpenReadOnlyBinary = O_RDONLY;
static const int kOpenReadOnlyText = O_RDONLY;
#else
using Socket = SOCKET;
static std::string LastSocketError() {
  char buf[DECIMAL_SIZE(int) + 1];
  snprintf(buf, sizeof(buf), "%d", WSAGetLastError());
  return buf;
}
static const int kOpenReadOnlyBinary = _O_RDONLY | _O_BINARY;
static const int kOpenReadOnlyText = O_RDONLY | _O_TEXT;
#endif

class OwnedSocket {
 public:
  OwnedSocket() = default;
  explicit OwnedSocket(Socket sock) : sock_(sock) {}
  OwnedSocket(OwnedSocket &&other) { *this = std::move(other); }
  ~OwnedSocket() { reset(); }
  OwnedSocket &operator=(OwnedSocket &&other) {
    reset(other.release());
    return *this;
  }

  bool is_valid() const { return sock_ != INVALID_SOCKET; }
  Socket get() const { return sock_; }
  Socket release() {
    Socket temp = std::move(sock_);
    sock_ = INVALID_SOCKET;
    return temp;
  }

  void reset(Socket sock = INVALID_SOCKET) {
    if (is_valid()) {
      closesocket(sock_);
    }

    sock_ = sock;
  }

 private:
  Socket sock_ = INVALID_SOCKET;
};

struct SockaddrStorage {
  SockaddrStorage() : storage(), len(sizeof(storage)) {}

  int family() const { return storage.ss_family; }

  sockaddr *addr_mut() { return reinterpret_cast<sockaddr *>(&storage); }
  const sockaddr *addr() const {
    return reinterpret_cast<const sockaddr *>(&storage);
  }

  sockaddr_in ToIPv4() const {
    if (family() != AF_INET || len != sizeof(sockaddr_in)) {
      abort();
    }
    // These APIs were seemingly designed before C's strict aliasing rule, and
    // C++'s strict union handling. Make a copy so the compiler does not read
    // this as an aliasing violation.
    sockaddr_in ret;
    OPENSSL_memcpy(&ret, &storage, sizeof(ret));
    return ret;
  }

  sockaddr_in6 ToIPv6() const {
    if (family() != AF_INET6 || len != sizeof(sockaddr_in6)) {
      abort();
    }
    // These APIs were seemingly designed before C's strict aliasing rule, and
    // C++'s strict union handling. Make a copy so the compiler does not read
    // this as an aliasing violation.
    sockaddr_in6 ret;
    OPENSSL_memcpy(&ret, &storage, sizeof(ret));
    return ret;
  }

  sockaddr_storage storage;
  socklen_t len;
};

static OwnedSocket Bind(int family, const sockaddr *addr, socklen_t addr_len) {
  OwnedSocket sock(socket(family, SOCK_STREAM, 0));
  if (!sock.is_valid()) {
    return OwnedSocket();
  }

  if (bind(sock.get(), addr, addr_len) != 0) {
    return OwnedSocket();
  }

  return sock;
}

static OwnedSocket ListenLoopback(int backlog) {
  // Try binding to IPv6.
  sockaddr_in6 sin6;
  OPENSSL_memset(&sin6, 0, sizeof(sin6));
  sin6.sin6_family = AF_INET6;
  if (inet_pton(AF_INET6, "::1", &sin6.sin6_addr) != 1) {
    return OwnedSocket();
  }
  OwnedSocket sock =
      Bind(AF_INET6, reinterpret_cast<const sockaddr *>(&sin6), sizeof(sin6));
  if (!sock.is_valid()) {
    // Try binding to IPv4.
    sockaddr_in sin;
    OPENSSL_memset(&sin, 0, sizeof(sin));
    sin.sin_family = AF_INET;
    if (inet_pton(AF_INET, "127.0.0.1", &sin.sin_addr) != 1) {
      return OwnedSocket();
    }
    sock = Bind(AF_INET, reinterpret_cast<const sockaddr *>(&sin), sizeof(sin));
  }
  if (!sock.is_valid()) {
    return OwnedSocket();
  }

  if (listen(sock.get(), backlog) != 0) {
    return OwnedSocket();
  }

  return sock;
}

static bool SocketSetNonBlocking(Socket sock) {
#if defined(OPENSSL_WINDOWS)
  u_long arg = 1;
  return ioctlsocket(sock, FIONBIO, &arg) == 0;
#else
  int flags = fcntl(sock, F_GETFL, 0);
  if (flags < 0) {
    return false;
  }
  flags |= O_NONBLOCK;
  return fcntl(sock, F_SETFL, flags) == 0;
#endif
}

enum class WaitType { kRead, kWrite };

static bool WaitForSocket(Socket sock, WaitType wait_type) {
  // Use an arbitrary 5 second timeout, so the test doesn't hang indefinitely if
  // there's an issue.
  static const int kTimeoutSeconds = 5;
#if defined(OPENSSL_WINDOWS)
  fd_set read_set, write_set;
  FD_ZERO(&read_set);
  FD_ZERO(&write_set);
  fd_set *wait_set = wait_type == WaitType::kRead ? &read_set : &write_set;
  FD_SET(sock, wait_set);
  timeval timeout;
  timeout.tv_sec = kTimeoutSeconds;
  timeout.tv_usec = 0;
  if (select(0 /* unused on Windows */, &read_set, &write_set, nullptr,
             &timeout) <= 0) {
    return false;
  }
  return FD_ISSET(sock, wait_set);
#else
  short events = wait_type == WaitType::kRead ? POLLIN : POLLOUT;
  pollfd fd = {/*fd=*/sock, events, /*revents=*/0};
  return poll(&fd, 1, kTimeoutSeconds * 1000) == 1 && (fd.revents & events);
#endif
}

TEST(BIOTest, SocketConnect) {
  static const char kTestMessage[] = "test";
  OwnedSocket listening_sock = ListenLoopback(/*backlog=*/1);
  ASSERT_TRUE(listening_sock.is_valid()) << LastSocketError();

  SockaddrStorage addr;
  ASSERT_EQ(getsockname(listening_sock.get(), addr.addr_mut(), &addr.len), 0)
      << LastSocketError();

  char hostname[80];
  if (addr.family() == AF_INET6) {
    snprintf(hostname, sizeof(hostname), "[::1]:%d",
             ntohs(addr.ToIPv6().sin6_port));
  } else {
    snprintf(hostname, sizeof(hostname), "127.0.0.1:%d",
             ntohs(addr.ToIPv4().sin_port));
  }

  // Connect to it with a connect BIO.
  bssl::UniquePtr<BIO> bio(BIO_new_connect(hostname));
  ASSERT_TRUE(bio);

  // Write a test message to the BIO. This is assumed to be smaller than the
  // transport buffer.
  ASSERT_EQ(static_cast<int>(sizeof(kTestMessage)),
            BIO_write(bio.get(), kTestMessage, sizeof(kTestMessage)))
      << LastSocketError();

  // Accept the socket.
  OwnedSocket sock(accept(listening_sock.get(), addr.addr_mut(), &addr.len));
  ASSERT_TRUE(sock.is_valid()) << LastSocketError();

  // Check the same message is read back out.
  char buf[sizeof(kTestMessage)];
  ASSERT_EQ(static_cast<int>(sizeof(kTestMessage)),
            recv(sock.get(), buf, sizeof(buf), 0))
      << LastSocketError();
  EXPECT_EQ(Bytes(kTestMessage, sizeof(kTestMessage)), Bytes(buf, sizeof(buf)));
}

TEST(BIOTest, SocketNonBlocking) {
  OwnedSocket listening_sock = ListenLoopback(/*backlog=*/1);
  ASSERT_TRUE(listening_sock.is_valid()) << LastSocketError();

  // Connect to |listening_sock|.
  SockaddrStorage addr;
  ASSERT_EQ(getsockname(listening_sock.get(), addr.addr_mut(), &addr.len), 0)
      << LastSocketError();
  OwnedSocket connect_sock(socket(addr.family(), SOCK_STREAM, 0));
  ASSERT_TRUE(connect_sock.is_valid()) << LastSocketError();
  ASSERT_EQ(connect(connect_sock.get(), addr.addr(), addr.len), 0)
      << LastSocketError();
  ASSERT_TRUE(SocketSetNonBlocking(connect_sock.get())) << LastSocketError();
  bssl::UniquePtr<BIO> connect_bio(
      BIO_new_socket(connect_sock.get(), BIO_NOCLOSE));
  ASSERT_TRUE(connect_bio);

  // Make a corresponding accepting socket.
  OwnedSocket accept_sock(
      accept(listening_sock.get(), addr.addr_mut(), &addr.len));
  ASSERT_TRUE(accept_sock.is_valid()) << LastSocketError();
  ASSERT_TRUE(SocketSetNonBlocking(accept_sock.get())) << LastSocketError();
  bssl::UniquePtr<BIO> accept_bio(
      BIO_new_socket(accept_sock.get(), BIO_NOCLOSE));
  ASSERT_TRUE(accept_bio);

  // Exchange data through the socket.
  static const char kTestMessage[] = "hello, world";

  // Reading from |accept_bio| should not block.
  char buf[sizeof(kTestMessage)];
  int ret = BIO_read(accept_bio.get(), buf, sizeof(buf));
  EXPECT_EQ(ret, -1);
  EXPECT_TRUE(BIO_should_read(accept_bio.get())) << LastSocketError();

  // Writing to |connect_bio| should eventually overflow the transport buffers
  // and also give a retryable error.
  int bytes_written = 0;
  for (;;) {
    ret = BIO_write(connect_bio.get(), kTestMessage, sizeof(kTestMessage));
    if (ret <= 0) {
      EXPECT_EQ(ret, -1);
      EXPECT_TRUE(BIO_should_write(connect_bio.get())) << LastSocketError();
      break;
    }
    bytes_written += ret;
  }
  EXPECT_GT(bytes_written, 0);

  // |accept_bio| should readable. Drain it. Note data is not always available
  // from loopback immediately, notably on macOS, so wait for the socket first.
  int bytes_read = 0;
  while (bytes_read < bytes_written) {
    ASSERT_TRUE(WaitForSocket(accept_sock.get(), WaitType::kRead))
        << LastSocketError();
    ret = BIO_read(accept_bio.get(), buf, sizeof(buf));
    ASSERT_GT(ret, 0);
    bytes_read += ret;
  }

  // |connect_bio| should become writeable again.
  ASSERT_TRUE(WaitForSocket(accept_sock.get(), WaitType::kWrite))
      << LastSocketError();
  ret = BIO_write(connect_bio.get(), kTestMessage, sizeof(kTestMessage));
  EXPECT_EQ(static_cast<int>(sizeof(kTestMessage)), ret);

  ASSERT_TRUE(WaitForSocket(accept_sock.get(), WaitType::kRead))
      << LastSocketError();
  ret = BIO_read(accept_bio.get(), buf, sizeof(buf));
  EXPECT_EQ(static_cast<int>(sizeof(kTestMessage)), ret);
  EXPECT_EQ(Bytes(buf), Bytes(kTestMessage));

  // Close one socket. We should get an EOF out the other.
  connect_bio.reset();
  connect_sock.reset();

  ASSERT_TRUE(WaitForSocket(accept_sock.get(), WaitType::kRead))
      << LastSocketError();
  ret = BIO_read(accept_bio.get(), buf, sizeof(buf));
  EXPECT_EQ(ret, 0) << LastSocketError();
  EXPECT_FALSE(BIO_should_read(accept_bio.get()));
}

TEST(BIOTest, Printf) {
  // Test a short output, a very long one, and various sizes around
  // 256 (the size of the buffer) to ensure edge cases are correct.
  static const size_t kLengths[] = {5, 250, 251, 252, 253, 254, 1023};

  bssl::UniquePtr<BIO> bio(BIO_new(BIO_s_mem()));
  ASSERT_TRUE(bio);
  ASSERT_EQ(strcmp(BIO_method_name(bio.get()), "memory buffer"), 0);

  for (size_t length : kLengths) {
    SCOPED_TRACE(length);

    std::string in(length, 'a');

    int ret = BIO_printf(bio.get(), "test %s", in.c_str());
    ASSERT_GE(ret, 0);
    EXPECT_EQ(5 + length, static_cast<size_t>(ret));

    const uint8_t *contents;
    size_t len;
    ASSERT_TRUE(BIO_mem_contents(bio.get(), &contents, &len));
    EXPECT_EQ("test " + in,
              std::string(reinterpret_cast<const char *>(contents), len));

    ASSERT_TRUE(BIO_reset(bio.get()));
  }
}

TEST(BIOTest, CloseFlags) {
#if defined(OPENSSL_ANDROID)
  // On Android, when running from an APK, |tmpfile| does not work. See
  // b/36991167#comment8.
  GTEST_SKIP();
#endif

  const char *test_str = "test\ntest\ntest\n";

  // Assert that CRLF line endings get inserted on write and translated back out
  // on read for text mode.
  TempFILE text_bio_file = createTempFILE();
  ASSERT_TRUE(text_bio_file);
  bssl::UniquePtr<BIO> text_bio(
      BIO_new_fp(text_bio_file.get(), BIO_NOCLOSE | BIO_FP_TEXT));
  int bytes_written = BIO_write(text_bio.get(), test_str, strlen(test_str));
  EXPECT_GE(bytes_written, 0);
  ASSERT_TRUE(BIO_flush(text_bio.get()));
  ASSERT_EQ(0, BIO_seek(text_bio.get(), 0));  // 0 indicates success here
  char contents[256];
  OPENSSL_memset(contents, 0, sizeof(contents));
  int bytes_read = BIO_read(text_bio.get(), contents, sizeof(contents));
  EXPECT_GE(bytes_read, bytes_written);
  EXPECT_EQ(test_str, std::string(contents));

  // Windows should have translated '\n' to '\r\n' on write, so validate that
  // by opening the file in raw binary mode (i.e. no BIO_FP_TEXT).
  bssl::UniquePtr<BIO> text_bio_raw(
      BIO_new_fp(text_bio_file.get(), BIO_NOCLOSE));
  ASSERT_EQ(0, BIO_seek(text_bio.get(), 0));  // 0 indicates success here
  OPENSSL_memset(contents, 0, sizeof(contents));
  bytes_read = BIO_read(text_bio_raw.get(), contents, sizeof(contents));
  EXPECT_GT(bytes_read, 0);
#if defined(OPENSSL_WINDOWS)
  EXPECT_EQ("test\r\ntest\r\ntest\r\n", std::string(contents));
#else
  EXPECT_EQ(test_str, std::string(contents));
#endif

  // Assert that CRLF line endings don't get inserted on write for
  // (default) binary mode.
  TempFILE binary_bio_file = createTempFILE();
  ASSERT_TRUE(binary_bio_file);
  bssl::UniquePtr<BIO> binary_bio(
      BIO_new_fp(binary_bio_file.get(), BIO_NOCLOSE));
  bytes_written = BIO_write(binary_bio.get(), test_str, strlen(test_str));
  EXPECT_EQ((int)strlen(test_str), bytes_written);
  ASSERT_TRUE(BIO_flush(binary_bio.get()));
  ASSERT_EQ(0, BIO_seek(binary_bio.get(), 0));  // 0 indicates success here
  OPENSSL_memset(contents, 0, sizeof(contents));
  bytes_read = BIO_read(binary_bio.get(), contents, sizeof(contents));
  EXPECT_GE(bytes_read, bytes_written);
  EXPECT_EQ(test_str, std::string(contents));

  // This test is meant to ensure that we're correctly handling a ftell/fseek
  // bug on Windows documented and reproduced here:
  // https://developercommunity.visualstudio.com/t/fseek-ftell-fail-in-text-mode-for-unix-style-text/425878
  long pos;
  char b1[256], b2[256];
  binary_bio.reset(BIO_new_fp(binary_bio_file.get(), BIO_NOCLOSE));
  ASSERT_EQ(0, BIO_seek(binary_bio.get(), 0));  // 0 indicates success here
  BIO_gets(binary_bio.get(), b1, sizeof(b1));
  pos = BIO_tell(binary_bio.get());
  ASSERT_GT(BIO_gets(binary_bio.get(), b1, sizeof(b1)), 0);
  BIO_seek(binary_bio.get(), pos);
  BIO_gets(binary_bio.get(), b2, sizeof(b2));
  EXPECT_EQ(std::string(b1), std::string(b2));

  // Assert that BIO_CLOSE causes the underlying file to be closed on BIO free
  // (ftell will return < 0)
  FILE *tmp = createRawTempFILE();
  ASSERT_TRUE(tmp);
  BIO *bio = BIO_new_fp(tmp, BIO_CLOSE);
  EXPECT_EQ(0, BIO_tell(bio));
  // save off fd to avoid referencing |tmp| after free and angering valgrind
  int tmp_fd = fileno(tmp);
  EXPECT_LT(0, tmp_fd);
  EXPECT_TRUE(BIO_free(bio));
  // Windows CRT hits an assertion error and stack overflow (exception code
  // 0xc0000409) when calling _tell or lseek on an already-closed file
  // descriptor, so only consider the non-Windows case here.
#if !defined(OPENSSL_WINDOWS)
  EXPECT_EQ(-1, lseek(tmp_fd, 0, SEEK_CUR));
  EXPECT_EQ(EBADF, errno);  // EBADF indicates that |BIO_free| closed the file
#endif

  // Assert that BIO_NOCLOSE does not close the underlying file on BIO free
  tmp = createRawTempFILE();
  ASSERT_TRUE(tmp);
  bio = BIO_new_fp(tmp, BIO_NOCLOSE);
  EXPECT_EQ(0, BIO_tell(bio));
  EXPECT_TRUE(BIO_free(bio));
  EXPECT_TRUE(tmp);
  EXPECT_EQ(0, ftell(tmp));   // 0 indicates file is still open
  EXPECT_EQ(0, fclose(tmp));  // 0 indicates success for fclose
}

TEST(BIOTest, ReadASN1) {
  static const size_t kLargeASN1PayloadLen = 8000;

  struct ASN1Test {
    bool should_succeed;
    std::vector<uint8_t> input;
    // suffix_len is the number of zeros to append to |input|.
    size_t suffix_len;
    // expected_len, if |should_succeed| is true, is the expected length of the
    // ASN.1 element.
    size_t expected_len;
    size_t max_len;
  } kASN1Tests[] = {
      {true, {0x30, 2, 1, 2, 0, 0}, 0, 4, 100},
      {false /* truncated */, {0x30, 3, 1, 2}, 0, 0, 100},
      {false /* should be short len */, {0x30, 0x81, 1, 1}, 0, 0, 100},
      {false /* zero padded */, {0x30, 0x82, 0, 1, 1}, 0, 0, 100},

      // Test a large payload.
      {true,
       {0x30, 0x82, kLargeASN1PayloadLen >> 8, kLargeASN1PayloadLen & 0xff},
       kLargeASN1PayloadLen,
       4 + kLargeASN1PayloadLen,
       kLargeASN1PayloadLen * 2},
      {false /* max_len too short */,
       {0x30, 0x82, kLargeASN1PayloadLen >> 8, kLargeASN1PayloadLen & 0xff},
       kLargeASN1PayloadLen,
       4 + kLargeASN1PayloadLen,
       3 + kLargeASN1PayloadLen},

      // Test an indefinite-length input.
      {true,
       {0x30, 0x80},
       kLargeASN1PayloadLen + 2,
       2 + kLargeASN1PayloadLen + 2,
       kLargeASN1PayloadLen * 2},
      {false /* max_len too short */,
       {0x30, 0x80},
       kLargeASN1PayloadLen + 2,
       2 + kLargeASN1PayloadLen + 2,
       2 + kLargeASN1PayloadLen + 1},
  };

  for (const auto &t : kASN1Tests) {
    std::vector<uint8_t> input = t.input;
    input.resize(input.size() + t.suffix_len, 0);

    bssl::UniquePtr<BIO> bio(BIO_new_mem_buf(input.data(), input.size()));
    ASSERT_TRUE(bio);

    uint8_t *out;
    size_t out_len;
    int ok = BIO_read_asn1(bio.get(), &out, &out_len, t.max_len);
    if (!ok) {
      out = nullptr;
    }
    bssl::UniquePtr<uint8_t> out_storage(out);

    ASSERT_EQ(t.should_succeed, (ok == 1));
    if (t.should_succeed) {
      EXPECT_EQ(Bytes(input.data(), t.expected_len), Bytes(out, out_len));
    }
  }
}

TEST(BIOTest, MemReadOnly) {
  // A memory BIO created from |BIO_new_mem_buf| is a read-only buffer.
  static const char kData[] = "abcdefghijklmno";
  bssl::UniquePtr<BIO> bio(BIO_new_mem_buf(kData, strlen(kData)));
  ASSERT_TRUE(bio);

  // Writing to read-only buffers should fail.
  EXPECT_EQ(BIO_write(bio.get(), kData, strlen(kData)), -1);

  const uint8_t *contents;
  size_t len;
  ASSERT_TRUE(BIO_mem_contents(bio.get(), &contents, &len));
  EXPECT_EQ(Bytes(contents, len), Bytes(kData));
  EXPECT_EQ(BIO_eof(bio.get()), 0);

  // Read less than the whole buffer.
  char buf[6];
  int ret = BIO_read(bio.get(), buf, sizeof(buf));
  ASSERT_GT(ret, 0);
  EXPECT_EQ(Bytes(buf, ret), Bytes("abcdef"));

  ASSERT_TRUE(BIO_mem_contents(bio.get(), &contents, &len));
  EXPECT_EQ(Bytes(contents, len), Bytes("ghijklmno"));
  EXPECT_EQ(BIO_eof(bio.get()), 0);

  ret = BIO_read(bio.get(), buf, sizeof(buf));
  ASSERT_GT(ret, 0);
  EXPECT_EQ(Bytes(buf, ret), Bytes("ghijkl"));

  ASSERT_TRUE(BIO_mem_contents(bio.get(), &contents, &len));
  EXPECT_EQ(Bytes(contents, len), Bytes("mno"));
  EXPECT_EQ(BIO_eof(bio.get()), 0);

  // Read the remainder of the buffer.
  ret = BIO_read(bio.get(), buf, sizeof(buf));
  ASSERT_GT(ret, 0);
  EXPECT_EQ(Bytes(buf, ret), Bytes("mno"));

  ASSERT_TRUE(BIO_mem_contents(bio.get(), &contents, &len));
  EXPECT_EQ(Bytes(contents, len), Bytes(""));
  EXPECT_EQ(BIO_eof(bio.get()), 1);

  // By default, reading from a consumed read-only buffer returns EOF.
  EXPECT_EQ(BIO_read(bio.get(), buf, sizeof(buf)), 0);
  EXPECT_FALSE(BIO_should_read(bio.get()));

  // A memory BIO can be configured to return an error instead of EOF. This is
  // error is returned as retryable. (This is not especially useful here. It
  // makes more sense for a writable BIO.)
  EXPECT_EQ(BIO_set_mem_eof_return(bio.get(), -1), 1);
  EXPECT_EQ(BIO_read(bio.get(), buf, sizeof(buf)), -1);
  EXPECT_TRUE(BIO_should_read(bio.get()));

  // Read exactly the right number of bytes, to test the boundary condition is
  // correct.
  bio.reset(BIO_new_mem_buf("abc", 3));
  ASSERT_TRUE(bio);
  ret = BIO_read(bio.get(), buf, 3);
  ASSERT_GT(ret, 0);
  EXPECT_EQ(Bytes(buf, ret), Bytes("abc"));
  EXPECT_EQ(BIO_eof(bio.get()), 1);
}

TEST(BIOTest, MemWritable) {
  // A memory BIO created from |BIO_new| is writable.
  bssl::UniquePtr<BIO> bio(BIO_new(BIO_s_mem()));
  ASSERT_TRUE(bio);

  auto check_bio_contents = [&](Bytes b) {
    const uint8_t *contents;
    size_t len;
    ASSERT_TRUE(BIO_mem_contents(bio.get(), &contents, &len));
    EXPECT_EQ(Bytes(contents, len), b);

    char *contents_c;
    long len_l = BIO_get_mem_data(bio.get(), &contents_c);
    ASSERT_GE(len_l, 0);
    EXPECT_EQ(Bytes(contents_c, len_l), b);

    BUF_MEM *buf;
    ASSERT_EQ(BIO_get_mem_ptr(bio.get(), &buf), 1);
    EXPECT_EQ(Bytes(buf->data, buf->length), b);
  };

  // It is initially empty.
  check_bio_contents(Bytes(""));
  EXPECT_EQ(BIO_eof(bio.get()), 1);

  // Reading from it should default to returning a retryable error.
  char buf[32];
  EXPECT_EQ(BIO_read(bio.get(), buf, sizeof(buf)), -1);
  EXPECT_TRUE(BIO_should_read(bio.get()));

  // This can be configured to return an EOF.
  EXPECT_EQ(BIO_set_mem_eof_return(bio.get(), 0), 1);
  EXPECT_EQ(BIO_read(bio.get(), buf, sizeof(buf)), 0);
  EXPECT_FALSE(BIO_should_read(bio.get()));

  // Restore the default. A writable memory |BIO| is typically used in this mode
  // so additional data can be written when exhausted.
  EXPECT_EQ(BIO_set_mem_eof_return(bio.get(), -1), 1);

  // Writes append to the buffer.
  ASSERT_EQ(BIO_write(bio.get(), "abcdef", 6), 6);
  check_bio_contents(Bytes("abcdef"));
  EXPECT_EQ(BIO_eof(bio.get()), 0);

  // Writes can include embedded NULs.
  ASSERT_EQ(BIO_write(bio.get(), "\0ghijk", 6), 6);
  check_bio_contents(Bytes("abcdef\0ghijk", 12));
  EXPECT_EQ(BIO_eof(bio.get()), 0);

  // Do a partial read.
  int ret = BIO_read(bio.get(), buf, 4);
  ASSERT_GT(ret, 0);
  EXPECT_EQ(Bytes(buf, ret), Bytes("abcd"));
  check_bio_contents(Bytes("ef\0ghijk", 8));
  EXPECT_EQ(BIO_eof(bio.get()), 0);

  // Reads and writes may alternate.
  ASSERT_EQ(BIO_write(bio.get(), "lmnopq", 6), 6);
  check_bio_contents(Bytes("ef\0ghijklmnopq", 14));
  EXPECT_EQ(BIO_eof(bio.get()), 0);

  // Reads may consume embedded NULs.
  ret = BIO_read(bio.get(), buf, 4);
  ASSERT_GT(ret, 0);
  EXPECT_EQ(Bytes(buf, ret), Bytes("ef\0g", 4));
  check_bio_contents(Bytes("hijklmnopq"));
  EXPECT_EQ(BIO_eof(bio.get()), 0);

  // The read buffer exceeds the |BIO|, so we consume everything.
  ret = BIO_read(bio.get(), buf, sizeof(buf));
  ASSERT_GT(ret, 0);
  EXPECT_EQ(Bytes(buf, ret), Bytes("hijklmnopq"));
  check_bio_contents(Bytes(""));
  EXPECT_EQ(BIO_eof(bio.get()), 1);

  // The |BIO| is now empty.
  EXPECT_EQ(BIO_read(bio.get(), buf, sizeof(buf)), -1);
  EXPECT_TRUE(BIO_should_read(bio.get()));

  // Repeat the above, reading exactly the right number of bytes, to test the
  // boundary condition is correct.
  ASSERT_EQ(BIO_write(bio.get(), "abc", 3), 3);
  ret = BIO_read(bio.get(), buf, 3);
  EXPECT_EQ(Bytes(buf, ret), Bytes("abc"));
  EXPECT_EQ(BIO_read(bio.get(), buf, sizeof(buf)), -1);
  EXPECT_TRUE(BIO_should_read(bio.get()));
  EXPECT_EQ(BIO_eof(bio.get()), 1);
}

TEST(BIOTest, Gets) {
  const struct {
    std::string bio;
    int gets_len;
    std::string gets_result;
  } kGetsTests[] = {
      // BIO_gets should stop at the first newline. If the buffer is too small,
      // stop there instead. Note the buffer size
      // includes a trailing NUL.
      {"123456789\n123456789", 5, "1234"},
      {"123456789\n123456789", 9, "12345678"},
      {"123456789\n123456789", 10, "123456789"},
      {"123456789\n123456789", 11, "123456789\n"},
      {"123456789\n123456789", 12, "123456789\n"},
      {"123456789\n123456789", 256, "123456789\n"},

      // If we run out of buffer, read the whole buffer.
      {"12345", 5, "1234"},
      {"12345", 6, "12345"},
      {"12345", 10, "12345"},

      // NUL bytes do not terminate gets.
      {std::string("abc\0def\nghi", 11), 256, std::string("abc\0def\n", 8)},

      // An output size of one means we cannot read any bytes. Only the trailing
      // NUL is included.
      {"12345", 1, ""},

      // Empty line.
      {"\nabcdef", 256, "\n"},
      // Empty BIO.
      {"", 256, ""},
  };
  for (const auto &t : kGetsTests) {
    SCOPED_TRACE(t.bio);
    SCOPED_TRACE(t.gets_len);

    auto check_bio_gets = [&](BIO *bio) {
      std::vector<char> buf(t.gets_len, 'a');
      int ret = BIO_gets(bio, buf.data(), t.gets_len);
      ASSERT_GE(ret, 0);
      // |BIO_gets| should write a NUL terminator, not counted in the return
      // value.
      EXPECT_EQ(Bytes(buf.data(), ret + 1),
                Bytes(t.gets_result.data(), t.gets_result.size() + 1));

      // The remaining data should still be in the BIO.
      buf.resize(t.bio.size() + 1);
      ret = BIO_read(bio, buf.data(), static_cast<int>(buf.size()));
      ASSERT_GE(ret, 0);
      EXPECT_EQ(Bytes(buf.data(), ret),
                Bytes(t.bio.substr(t.gets_result.size())));
    };

    {
      SCOPED_TRACE("memory");
      bssl::UniquePtr<BIO> bio(BIO_new_mem_buf(t.bio.data(), t.bio.size()));
      ASSERT_TRUE(bio);
      check_bio_gets(bio.get());
    }

    if (!SkipTempFileTests()) {
      TemporaryFile file;
      ASSERT_TRUE(file.Init(t.bio));

      // TODO(crbug.com/boringssl/585): If the line has an embedded NUL, file
      // BIOs do not currently report the answer correctly.
      if (t.bio.find('\0') == std::string::npos) {
        SCOPED_TRACE("file");

        // Test |BIO_new_file|.
        bssl::UniquePtr<BIO> bio(BIO_new_file(file.path().c_str(), "rb"));
        ASSERT_TRUE(bio);
        check_bio_gets(bio.get());

        // Test |BIO_read_filename|.
        bio.reset(BIO_new(BIO_s_file()));
        ASSERT_TRUE(bio);
        ASSERT_TRUE(BIO_read_filename(bio.get(), file.path().c_str()));
        check_bio_gets(bio.get());

        // Test |BIO_NOCLOSE|.
        ScopedFILE file_obj = file.Open("rb");
        ASSERT_TRUE(file_obj);
        bio.reset(BIO_new_fp(file_obj.get(), BIO_NOCLOSE));
        ASSERT_TRUE(bio);
        check_bio_gets(bio.get());

        // Test |BIO_CLOSE|.
        file_obj = file.Open("rb");
        ASSERT_TRUE(file_obj);
        bio.reset(BIO_new_fp(file_obj.get(), BIO_CLOSE));
        ASSERT_TRUE(bio);
        file_obj.release();  // |BIO_new_fp| took ownership on success.
        check_bio_gets(bio.get());
      }

      {
        SCOPED_TRACE("fd");
#if defined(OPENSSL_WINDOWS)
        int open_flags = _O_RDONLY | _O_BINARY;
#else
        int open_flags = O_RDONLY;
#endif

        // Test |BIO_NOCLOSE|.
        ScopedFD fd = file.OpenFD(open_flags);
        ASSERT_TRUE(fd.is_valid());
        bssl::UniquePtr<BIO> bio(BIO_new_fd(fd.get(), BIO_NOCLOSE));
        ASSERT_TRUE(bio);
        check_bio_gets(bio.get());

        // Test |BIO_CLOSE|.
        fd = file.OpenFD(open_flags);
        ASSERT_TRUE(fd.is_valid());
        bio.reset(BIO_new_fd(fd.get(), BIO_CLOSE));
        ASSERT_TRUE(bio);
        fd.release();  // |BIO_new_fd| took ownership on success.
        check_bio_gets(bio.get());
      }
    }
  }

  // Negative and zero lengths should not output anything, even a trailing NUL.
  bssl::UniquePtr<BIO> bio(BIO_new_mem_buf("12345", -1));
  ASSERT_TRUE(bio);
  char c = 'a';
  EXPECT_EQ(0, BIO_gets(bio.get(), &c, -1));
  EXPECT_EQ(0, BIO_gets(bio.get(), &c, 0));
  EXPECT_EQ(c, 'a');
}

TEST(BIOTest, ExternalData) {
  // Create a |BIO| object
  bssl::UniquePtr<BIO> bio(BIO_new(BIO_s_mem()));
  int bio_index =
      BIO_get_ex_new_index(0, nullptr, nullptr, nullptr, CustomDataFree);
  ASSERT_GT(bio_index, 0);

  // Associate custom data with the |BIO| using |BIO_set_ex_data| and set an
  // arbitrary number.
  auto *custom_data = static_cast<CustomData *>(malloc(sizeof(CustomData)));
  ASSERT_TRUE(custom_data);
  custom_data->custom_data = 123;
  ASSERT_TRUE(BIO_set_ex_data(bio.get(), bio_index, custom_data));

  // Retrieve the custom data using |BIO_get_ex_data|.
  auto *retrieved_data =
      static_cast<CustomData *>(BIO_get_ex_data(bio.get(), bio_index));
  ASSERT_TRUE(retrieved_data);
  EXPECT_EQ(retrieved_data->custom_data, 123);
}

// Test that, on Windows, |BIO_read_filename| opens files in binary mode.
TEST(BIOTest, FileMode) {
  if (SkipTempFileTests()) {
    GTEST_SKIP();
  }

  TemporaryFile temp;
  ASSERT_TRUE(temp.Init("hello\r\nworld"));

  auto expect_file_contents = [](BIO *bio, const std::string &str) {
    // Read more than expected, to make sure we've reached the end of the file.
    std::vector<char> buf(str.size() + 100);
    int len = BIO_read(bio, buf.data(), static_cast<int>(buf.size()));
    ASSERT_GT(len, 0);
    EXPECT_EQ(Bytes(buf.data(), len), Bytes(str));
  };
  auto expect_binary_mode = [&](BIO *bio) {
    expect_file_contents(bio, "hello\r\nworld");
  };
  auto expect_text_mode = [&](BIO *bio) {
#if defined(OPENSSL_WINDOWS)
    expect_file_contents(bio, "hello\nworld");
#else
    expect_file_contents(bio, "hello\r\nworld");
#endif
  };

  // |BIO_read_filename| should open in binary mode.
  bssl::UniquePtr<BIO> bio(BIO_new(BIO_s_file()));
  ASSERT_TRUE(bio);
  ASSERT_TRUE(BIO_read_filename(bio.get(), temp.path().c_str()));
  expect_binary_mode(bio.get());
  // |BIO_new_file| does not set |BIO_FP_TEXT|, so expect it to set the file's
  // mode to binary in all cases. This odd behavior, but it's what OpenSSL does.
  bio.reset(BIO_new_file(temp.path().c_str(), "rb"));
  ASSERT_TRUE(bio);
  expect_binary_mode(bio.get());
  bio.reset(BIO_new_file(temp.path().c_str(), "r"));
  ASSERT_TRUE(bio);
  // NOTE: Our behavior here aligns with OpenSSL which is to |_setmode| the file
  // to binary. BoringSSL would |expect_text_mode| below because it respects 
  // default mode on Windows which is text and doesn't call |_setmode| (unless
  // |BIO_FP_TEXT| is set, which is not the case here).
  expect_binary_mode(bio.get());
  // |BIO_new_fp| will always set |_O_BINARY| if |BIO_FP_TEXT| is not set in the
  // call to |BIO_new_fp|.
  ScopedFILE file = temp.Open("rb");
  ASSERT_TRUE(file);
  bio.reset(BIO_new_fp(file.get(), BIO_NOCLOSE));
  ASSERT_TRUE(bio);
  expect_binary_mode(bio.get());
  file = temp.Open("r");
  ASSERT_TRUE(file);
  bio.reset(BIO_new_fp(file.get(), BIO_NOCLOSE));
  ASSERT_TRUE(bio);
  // NOTE: Our behavior here aligns with OpenSSL. BoringSSL would
  // |expect_text_mode| below because they don't call |_setmode| unless
  // |BIO_FP_TEXT| is set.
  expect_binary_mode(bio.get());
  // However, |BIO_FP_TEXT| changes the file to be text mode, no matter how it
  // was opened.
  file = temp.Open("rb");
  ASSERT_TRUE(file);
  bio.reset(BIO_new_fp(file.get(), BIO_NOCLOSE | BIO_FP_TEXT));
  ASSERT_TRUE(bio);
  expect_text_mode(bio.get());
  file = temp.Open("r");
  ASSERT_TRUE(file);
  bio.reset(BIO_new_fp(file.get(), BIO_NOCLOSE | BIO_FP_TEXT));
  ASSERT_TRUE(bio);
  expect_text_mode(bio.get());
  // |BIO_new_fd| inherits the FD's existing mode.
  ScopedFD fd = temp.OpenFD(kOpenReadOnlyBinary);
  ASSERT_TRUE(fd.is_valid());
  bio.reset(BIO_new_fd(fd.get(), BIO_NOCLOSE));
  ASSERT_TRUE(bio);
  expect_binary_mode(bio.get());
  fd = temp.OpenFD(kOpenReadOnlyText);
  ASSERT_TRUE(fd.is_valid());
  bio.reset(BIO_new_fd(fd.get(), BIO_NOCLOSE));
  ASSERT_TRUE(bio);
  expect_text_mode(bio.get());
}

// Run through the tests twice, swapping |bio1| and |bio2|, for symmetry.
class BIOPairTest : public testing::TestWithParam<bool> {};

TEST_P(BIOPairTest, TestPair) {
  BIO *bio1, *bio2;
  ASSERT_TRUE(BIO_new_bio_pair(&bio1, 10, &bio2, 10));
  bssl::UniquePtr<BIO> free_bio1(bio1), free_bio2(bio2);

  if (GetParam()) {
    std::swap(bio1, bio2);
  }

  // Check initial states.
  EXPECT_EQ(10u, BIO_ctrl_get_write_guarantee(bio1));
  EXPECT_EQ(0u, BIO_ctrl_get_read_request(bio1));

  // Data written in one end may be read out the other.
  uint8_t buf[20];
  EXPECT_EQ(5, BIO_write(bio1, "12345", 5));
  EXPECT_EQ(5u, BIO_ctrl_get_write_guarantee(bio1));
  ASSERT_EQ(5, BIO_read(bio2, buf, sizeof(buf)));
  EXPECT_EQ(Bytes("12345"), Bytes(buf, 5));
  EXPECT_EQ(10u, BIO_ctrl_get_write_guarantee(bio1));

  // Attempting to write more than 10 bytes will write partially.
  EXPECT_EQ(10, BIO_write(bio1, "1234567890___", 13));
  EXPECT_EQ(0u, BIO_ctrl_get_write_guarantee(bio1));
  EXPECT_EQ(-1, BIO_write(bio1, "z", 1));
  EXPECT_TRUE(BIO_should_write(bio1));
  ASSERT_EQ(10, BIO_read(bio2, buf, sizeof(buf)));
  EXPECT_EQ(Bytes("1234567890"), Bytes(buf, 10));
  EXPECT_EQ(10u, BIO_ctrl_get_write_guarantee(bio1));

  // Unsuccessful reads update the read request.
  EXPECT_EQ(-1, BIO_read(bio2, buf, 5));
  EXPECT_TRUE(BIO_should_read(bio2));
  EXPECT_EQ(5u, BIO_ctrl_get_read_request(bio1));

  // The read request is clamped to the size of the buffer.
  EXPECT_EQ(-1, BIO_read(bio2, buf, 20));
  EXPECT_TRUE(BIO_should_read(bio2));
  EXPECT_EQ(10u, BIO_ctrl_get_read_request(bio1));

  // Data may be written and read in chunks.
  EXPECT_EQ(5, BIO_write(bio1, "12345", 5));
  EXPECT_EQ(5u, BIO_ctrl_get_write_guarantee(bio1));
  EXPECT_EQ(5, BIO_write(bio1, "67890___", 8));
  EXPECT_EQ(0u, BIO_ctrl_get_write_guarantee(bio1));
  ASSERT_EQ(3, BIO_read(bio2, buf, 3));
  EXPECT_EQ(Bytes("123"), Bytes(buf, 3));
  EXPECT_EQ(3u, BIO_ctrl_get_write_guarantee(bio1));
  ASSERT_EQ(7, BIO_read(bio2, buf, sizeof(buf)));
  EXPECT_EQ(Bytes("4567890"), Bytes(buf, 7));
  EXPECT_EQ(10u, BIO_ctrl_get_write_guarantee(bio1));

  // Successful reads reset the read request.
  EXPECT_EQ(0u, BIO_ctrl_get_read_request(bio1));

  // Test writes and reads starting in the middle of the ring buffer and
  // wrapping to front.
  EXPECT_EQ(8, BIO_write(bio1, "abcdefgh", 8));
  EXPECT_EQ(2u, BIO_ctrl_get_write_guarantee(bio1));
  ASSERT_EQ(3, BIO_read(bio2, buf, 3));
  EXPECT_EQ(Bytes("abc"), Bytes(buf, 3));
  EXPECT_EQ(5u, BIO_ctrl_get_write_guarantee(bio1));
  EXPECT_EQ(5, BIO_write(bio1, "ijklm___", 8));
  EXPECT_EQ(0u, BIO_ctrl_get_write_guarantee(bio1));
  ASSERT_EQ(10, BIO_read(bio2, buf, sizeof(buf)));
  EXPECT_EQ(Bytes("defghijklm"), Bytes(buf, 10));
  EXPECT_EQ(10u, BIO_ctrl_get_write_guarantee(bio1));

  // Data may flow from both ends in parallel.
  EXPECT_EQ(5, BIO_write(bio1, "12345", 5));
  EXPECT_EQ(5, BIO_write(bio2, "67890", 5));
  ASSERT_EQ(5, BIO_read(bio2, buf, sizeof(buf)));
  EXPECT_EQ(Bytes("12345"), Bytes(buf, 5));
  ASSERT_EQ(5, BIO_read(bio1, buf, sizeof(buf)));
  EXPECT_EQ(Bytes("67890"), Bytes(buf, 5));

  // Closing the write end causes an EOF on the read half, after draining.
  EXPECT_EQ(5, BIO_write(bio1, "12345", 5));
  EXPECT_TRUE(BIO_shutdown_wr(bio1));
  ASSERT_EQ(5, BIO_read(bio2, buf, sizeof(buf)));
  EXPECT_EQ(Bytes("12345"), Bytes(buf, 5));
  EXPECT_EQ(0, BIO_read(bio2, buf, sizeof(buf)));

  // A closed write end may not be written to.
  EXPECT_EQ(0u, BIO_ctrl_get_write_guarantee(bio1));
  EXPECT_EQ(-1, BIO_write(bio1, "_____", 5));
  EXPECT_TRUE(ErrorEquals(ERR_get_error(), ERR_LIB_BIO, BIO_R_BROKEN_PIPE));

  // The other end is still functional.
  EXPECT_EQ(5, BIO_write(bio2, "12345", 5));
  ASSERT_EQ(5, BIO_read(bio1, buf, sizeof(buf)));
  EXPECT_EQ(Bytes("12345"), Bytes(buf, 5));
}

#define CALL_BACK_FAILURE -1234567
#define CB_TEST_COUNT 2
static int test_count_ex;
static BIO *param_b_ex[CB_TEST_COUNT];
static int param_oper_ex[CB_TEST_COUNT];
static const char *param_argp_ex[CB_TEST_COUNT];
static int param_argi_ex[CB_TEST_COUNT];
static long param_argl_ex[CB_TEST_COUNT];
static long param_ret_ex[CB_TEST_COUNT];
static size_t param_len_ex[CB_TEST_COUNT];
static size_t param_processed_ex[CB_TEST_COUNT];

static long bio_cb_ex(BIO *b, int oper, const char *argp, size_t len, int argi,
                      long argl, int ret, size_t *processed) {
  if (test_count_ex >= CB_TEST_COUNT) {
    return CALL_BACK_FAILURE;
  }
  param_b_ex[test_count_ex] = b;
  param_oper_ex[test_count_ex] = oper;
  param_argp_ex[test_count_ex] = argp;
  param_argi_ex[test_count_ex] = argi;
  param_argl_ex[test_count_ex] = argl;
  param_ret_ex[test_count_ex] = ret;
  param_len_ex[test_count_ex] = len;
  param_processed_ex[test_count_ex] = processed != NULL ? *processed : 0;
  test_count_ex++;
  return ret;
}

static void bio_callback_cleanup() {
  // These mocks are used in multiple tests and need to be reset
  test_count_ex = 0;
  OPENSSL_cleanse(param_b_ex, sizeof(param_b_ex));
  OPENSSL_cleanse(param_oper_ex, sizeof(param_oper_ex));
  OPENSSL_cleanse(param_argp_ex, sizeof(param_argp_ex));
  OPENSSL_cleanse(param_argi_ex, sizeof(param_argi_ex));
  OPENSSL_cleanse(param_argl_ex, sizeof(param_argl_ex));
  OPENSSL_cleanse(param_ret_ex, sizeof(param_ret_ex));
  OPENSSL_cleanse(param_len_ex, sizeof(param_len_ex));
  OPENSSL_cleanse(param_processed_ex, sizeof(param_processed_ex));
}

#define TEST_BUF_LEN 20
#define TEST_DATA_WRITTEN 5
TEST_P(BIOPairTest, TestCallbacks) {
  bio_callback_cleanup();

  BIO *bio1, *bio2;
  ASSERT_TRUE(BIO_new_bio_pair(&bio1, 10, &bio2, 10));

  if (GetParam()) {
    std::swap(bio1, bio2);
  }

  BIO_set_callback_ex(bio2, bio_cb_ex);

  // Data written in one end may be read out the other.
  uint8_t buf[TEST_BUF_LEN];
  EXPECT_EQ(TEST_DATA_WRITTEN, BIO_write(bio1, "12345", TEST_DATA_WRITTEN));
  ASSERT_EQ(TEST_DATA_WRITTEN, BIO_read(bio2, buf, sizeof(buf)));
  EXPECT_EQ(Bytes("12345"), Bytes(buf, TEST_DATA_WRITTEN));

  // Check that read or write was called first, then the combo with
  // BIO_CB_RETURN
  ASSERT_EQ(param_oper_ex[0], BIO_CB_READ);
  ASSERT_EQ(param_oper_ex[1], BIO_CB_READ | BIO_CB_RETURN);

  // argp is a pointer to a buffer for read/write operations. We don't care
  // where the buf is, but it should be the same before and after the BIO calls
  ASSERT_EQ(param_argp_ex[0], param_argp_ex[1]);

  // The calls before the BIO operation use 1 for the BIO's return value
  ASSERT_EQ(param_ret_ex[0], 1);

  // The calls after the BIO call use the return value from the BIO, which is
  // the length of data read/written
  ASSERT_EQ(param_ret_ex[1], TEST_DATA_WRITTEN);

  // For callback_ex the |len| param is the requested number of bytes to
  // read/write
  ASSERT_EQ(param_len_ex[0], (size_t)TEST_BUF_LEN);
  ASSERT_EQ(param_len_ex[0], (size_t)TEST_BUF_LEN);

  // For callback_ex argi and arl are unused
  ASSERT_EQ(param_argi_ex[0], 0);
  ASSERT_EQ(param_argi_ex[1], 0);
  ASSERT_EQ(param_argl_ex[0], 0);
  ASSERT_EQ(param_argl_ex[1], 0);

  // processed is null (0 in the array) the first call and the actual data the
  // second time
  ASSERT_EQ(param_processed_ex[0], 0u);
  ASSERT_EQ(param_processed_ex[1], 5u);

  // The mock should be "full" at this point
  ASSERT_EQ(test_count_ex, CB_TEST_COUNT);

  // If we attempt to read or write more from either BIO the callback fails
  // and the callback return value is returned to the caller
  ASSERT_EQ(CALL_BACK_FAILURE, BIO_read(bio2, buf, sizeof(buf)));

  // Run bio_callback_cleanup to reset the mock, without this when BIO_free
  // calls the callback it would fail before freeing the memory and be detected
  // as a memory leak.
  bio_callback_cleanup();
  ASSERT_EQ(BIO_free(bio1), 1);
  ASSERT_EQ(BIO_free(bio2), 1);

  ASSERT_EQ(param_oper_ex[0], BIO_CB_FREE);

  ASSERT_EQ(param_argp_ex[0], nullptr);
  ASSERT_EQ(param_argi_ex[0], 0);
  ASSERT_EQ(param_argl_ex[0], 0);
  ASSERT_EQ(param_ret_ex[0], 1);
  ASSERT_EQ(param_len_ex[0], 0u);
}

namespace {
static int callback_invoked = 0;

static long callback(BIO *b, int state, int res) {
  callback_invoked = 1;
  EXPECT_EQ(state, 0);
  EXPECT_EQ(res, -1);
  return 0;
}

TEST(BIOTest, InvokeConnectCallback) {
  ASSERT_EQ(callback_invoked, 0);
  BIO *bio = BIO_new(BIO_s_connect());
  ASSERT_NE(bio, nullptr);

  ASSERT_TRUE(BIO_set_conn_hostname(bio, "localhost"));
  ASSERT_TRUE(BIO_set_conn_port(bio, "5325"));
  ASSERT_TRUE(BIO_callback_ctrl(bio, BIO_CTRL_SET_CALLBACK, callback));

  ASSERT_EQ(BIO_do_connect(bio), 0);
  ASSERT_EQ(callback_invoked, 1);

  ASSERT_TRUE(BIO_free(bio));
}
}  // namespace

INSTANTIATE_TEST_SUITE_P(All, BIOPairTest, testing::Values(false, true));

TEST(BIOTest, ReadWriteEx) {
  bssl::UniquePtr<BIO> bio(BIO_new(BIO_s_mem()));
  ASSERT_TRUE(bio);

  // Reading from an initially empty bio should default to returning a error.
  // Check that both |BIO_read| and |BIO_read_ex| fail.
  char buf[32];
  size_t read = 1;
  EXPECT_EQ(BIO_read(bio.get(), buf, sizeof(buf)), -1);
  EXPECT_FALSE(BIO_read_ex(bio.get(), buf, sizeof(buf), &read));
  EXPECT_EQ(read, (size_t)0);

  // Write and read normally from buffer.
  size_t written = 1;
  ASSERT_TRUE(BIO_write_ex(bio.get(), "abcdef", 6, &written));
  EXPECT_EQ(written, (size_t)6);
  ASSERT_TRUE(BIO_read_ex(bio.get(), buf, sizeof(buf), &read));
  EXPECT_EQ(read, (size_t)6);
  EXPECT_EQ(Bytes(buf, read), Bytes("abcdef"));

  // Test NULL |written_bytes| behavior works.
  ASSERT_TRUE(BIO_write_ex(bio.get(), "ghilmnop", 8, nullptr));
  ASSERT_TRUE(BIO_read_ex(bio.get(), buf, sizeof(buf), &read));
  EXPECT_EQ(read, (size_t)8);
  EXPECT_EQ(Bytes(buf, read), Bytes("ghilmnop"));

  // Test NULL |read_bytes| behavior fails.
  ASSERT_TRUE(BIO_write_ex(bio.get(), "ghilmnop", 8, nullptr));
  ASSERT_FALSE(BIO_read_ex(bio.get(), buf, sizeof(buf), nullptr));

  // Test that |BIO_write/read_ex| align with their non-ex counterparts, when
  // encountering NULL data. EOF in |BIO_read| is indicated by returning 0.
  // In |BIO_read_ex| however, EOF returns a failure and sets |read| to 0.
  EXPECT_FALSE(BIO_write(bio.get(), nullptr, 0));
  EXPECT_FALSE(BIO_write_ex(bio.get(), nullptr, 0, &written));
  EXPECT_EQ(written, (size_t)0);
  EXPECT_EQ(BIO_read(bio.get(), nullptr, 0), 0);
  EXPECT_FALSE(BIO_read_ex(bio.get(), nullptr, 0, &read));
  EXPECT_EQ(read, (size_t)0);
}

TEST(BIOTest, TestPutsAsWrite) {
  // By default, |BIO_puts| acts as |BIO_write|.
  bssl::UniquePtr<BIO> bio(BIO_new(BIO_s_mem()));
  ASSERT_TRUE(bio);

  // Test basic puts and read
  uint8_t buf[32];
  EXPECT_EQ(12, BIO_puts(bio.get(), "hello world\n"));
  EXPECT_EQ(12, BIO_read(bio.get(), buf, sizeof(buf)));
}

namespace {
// Define custom BIO and BIO_METHODS to test BIO_puts without write
static int customPuts(BIO *b, const char *in) {
  return 0;
}
static int customNew(BIO *b) {
  b->init=1;
  return 1;
}
static const BIO_METHOD custom_method = {
  BIO_TYPE_NONE, "CustomBioMethod", NULL /* write */,
  NULL,          customPuts,        NULL,
  NULL,          customNew,         NULL,
  NULL
};

static const BIO_METHOD *BIO_cust(void) { return &custom_method; }

TEST(BIOTest, TestCustomPuts) {
  bssl::UniquePtr<BIO> bio(BIO_new(BIO_cust()));
  ASSERT_TRUE(bio);

  ASSERT_EQ(0, BIO_puts(bio.get(), "hello world"));

  // Test setting new puts method by creating a new BIO
  bssl::UniquePtr<BIO_METHOD> method(BIO_meth_new(0, nullptr));
  ASSERT_TRUE(method);
  ASSERT_TRUE(BIO_meth_set_create(
    method.get(), [](BIO *b) -> int {
      BIO_set_init(b, 1);
      return 1;
  }));
  ASSERT_TRUE(BIO_meth_set_puts(
    method.get(), [](BIO *b, const char *in) -> int {
      return 100;
    }
  ));
  bssl::UniquePtr<BIO> bio1(BIO_new(method.get()));
  ASSERT_TRUE(bio1);
  ASSERT_TRUE(bio1.get()->method->bputs);
  ASSERT_FALSE(bio1.get()->method->bwrite);
  // The new BIO_puts should only return 100
  ASSERT_EQ(100, BIO_puts(bio1.get(), "hello world"));
}

TEST(BIOTest, TestPutsNullMethod) {
  // Create new BIO to test when neither puts nor write is set
  bssl::UniquePtr<BIO_METHOD> method(BIO_meth_new(0, nullptr));
  ASSERT_TRUE(method);
  ASSERT_TRUE(BIO_meth_set_create(
    method.get(), [](BIO *b) -> int {
      BIO_set_init(b, 1);
      return 1;
  }));
  bssl::UniquePtr<BIO> bio(BIO_new(method.get()));
  ASSERT_TRUE(bio);

  ASSERT_FALSE(bio.get()->method->bputs);
  ASSERT_FALSE(bio.get()->method->bwrite);
  ASSERT_EQ(-2, BIO_puts(bio.get(), "hello world"));
}
} //namespace

TEST(BIOTest, TestPutsCallbacks) {
  bio_callback_cleanup();
  BIO* bio = BIO_new(BIO_s_mem());
  ASSERT_TRUE(bio);

  BIO_set_callback_ex(bio, bio_cb_ex);

  EXPECT_EQ(TEST_DATA_WRITTEN, BIO_puts(bio, "12345"));

  ASSERT_EQ(param_oper_ex[0], BIO_CB_PUTS);
  ASSERT_EQ(param_oper_ex[1], BIO_CB_PUTS | BIO_CB_RETURN);

  ASSERT_EQ(param_argp_ex[0], param_argp_ex[1]);
  ASSERT_EQ(param_ret_ex[0], 1);
  ASSERT_EQ(param_ret_ex[1], TEST_DATA_WRITTEN);

  // len unused in puts callback
  ASSERT_FALSE(param_len_ex[0]);
  ASSERT_FALSE(param_len_ex[1]);

  ASSERT_EQ(param_argi_ex[0], 0);
  ASSERT_EQ(param_argi_ex[1], 0);
  ASSERT_EQ(param_argl_ex[0], 0);
  ASSERT_EQ(param_argl_ex[1], 0);

  ASSERT_EQ(param_processed_ex[0], 0u);
  ASSERT_EQ(param_processed_ex[1], 5u);

  // The mock should be "full" at this point
  ASSERT_EQ(test_count_ex, CB_TEST_COUNT);

  bio_callback_cleanup();
  ASSERT_EQ(BIO_free(bio), 1);
}

TEST(BIOTest, TestGetsCallback) {
  bio_callback_cleanup();

  BIO* bio = BIO_new(BIO_s_mem());
  ASSERT_TRUE(bio);
  // write data to BIO, then set callback
  EXPECT_EQ(TEST_DATA_WRITTEN, BIO_write(bio, "12345", TEST_DATA_WRITTEN));
  char buf[TEST_BUF_LEN];
  BIO_set_callback_ex(bio, bio_cb_ex);

  ASSERT_EQ(TEST_DATA_WRITTEN, BIO_gets(bio, buf, sizeof(buf)));

  ASSERT_EQ(param_oper_ex[0], BIO_CB_GETS);
  ASSERT_EQ(param_oper_ex[1], BIO_CB_GETS | BIO_CB_RETURN);

  ASSERT_EQ(param_argp_ex[0], param_argp_ex[1]);
  ASSERT_EQ(param_ret_ex[0], 1);
  ASSERT_EQ(param_ret_ex[1], TEST_DATA_WRITTEN);

  ASSERT_EQ(param_len_ex[0], (size_t)TEST_BUF_LEN);
  ASSERT_EQ(param_len_ex[1], (size_t)TEST_BUF_LEN);

  ASSERT_EQ(param_argi_ex[0], 0);
  ASSERT_EQ(param_argi_ex[1], 0);
  ASSERT_EQ(param_argl_ex[0], 0);
  ASSERT_EQ(param_argl_ex[1], 0);

  ASSERT_EQ(param_processed_ex[0], 0u);
  ASSERT_EQ(param_processed_ex[1], 5u);

  ASSERT_EQ(test_count_ex, CB_TEST_COUNT);

  bio_callback_cleanup();
  ASSERT_EQ(BIO_free(bio), 1);
}

TEST(BIOTest, TestCtrlCallback) {
  bio_callback_cleanup();

  BIO* bio = BIO_new(BIO_s_mem());
  ASSERT_TRUE(bio);
  BIO_set_callback_ex(bio, bio_cb_ex);

  char buf[TEST_BUF_LEN];
  // Test BIO_ctrl. This is not normally called directly so we can use one of
  // the macros such as BIO_reset to test it
  ASSERT_EQ(BIO_reset(bio), 1);

  ASSERT_EQ(param_oper_ex[0], BIO_CB_CTRL);
  ASSERT_EQ(param_oper_ex[1], BIO_CB_CTRL | BIO_CB_RETURN);

  // argi in this case in the cmd sent to the ctrl method
  ASSERT_EQ(param_argi_ex[0], BIO_CTRL_RESET);
  ASSERT_EQ(param_argi_ex[1], BIO_CTRL_RESET);

  // BIO_ctrl of a memory bio sets ret to 1 when it calls the reset method
  ASSERT_EQ(param_ret_ex[0], 1);
  ASSERT_EQ(param_ret_ex[1], 1);

  // processed is unused in ctrl
  ASSERT_EQ(param_processed_ex[0], 0u);
  ASSERT_EQ(param_processed_ex[1], 0u);

  bio_callback_cleanup();
  // check that BIO_reset was called correctly
  ASSERT_EQ(BIO_gets(bio, buf, sizeof(buf)), 0);

  bio_callback_cleanup();
  ASSERT_EQ(BIO_free(bio), 1);
}
