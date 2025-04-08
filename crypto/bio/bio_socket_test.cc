// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC


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
#else
using Socket = SOCKET;
static std::string LastSocketError() {
  char buf[DECIMAL_SIZE(int) + 1];
  snprintf(buf, sizeof(buf), "%d", WSAGetLastError());
  return buf;
}
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
