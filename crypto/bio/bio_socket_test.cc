// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC


#include <algorithm>
#include <string>

#include <gtest/gtest.h>

#include <openssl/bio.h>
#include <openssl/err.h>
#include <openssl/mem.h>

#include "../internal.h"
#include "../test/test_util.h"

#if !defined(OPENSSL_WINDOWS)
#include <arpa/inet.h>
#include <fcntl.h>
#include <netinet/in.h>
#include <poll.h>
#include <sys/socket.h>
#include <unistd.h>
#else
#include <fcntl.h>
#include <io.h>
OPENSSL_MSVC_PRAGMA(warning(push, 3))
#include <winsock2.h>
#include <ws2tcpip.h>
OPENSSL_MSVC_PRAGMA(warning(pop))
#endif

#if defined(AF_UNIX) && !defined(OPENSSL_WINDOWS) && !defined(OPENSSL_ANDROID)
#define AWS_LC_HAS_AF_UNIX 1
#endif

#if !defined(OPENSSL_WINDOWS)
using Socket = int;
#define INVALID_SOCKET (-1)
static int closesocket(const int sock) { return close(sock); }
static std::string LastSocketError() { return strerror(errno); }
#else
using Socket = SOCKET;
static std::string LastSocketError() {
  char buf[DECIMAL_SIZE(int) + 1];
  snprintf(buf, sizeof(buf), "%d", WSAGetLastError());
  return buf;
}
#endif

struct SockaddrStorage {
  SockaddrStorage() : storage(), len(sizeof(storage)) {}

  int family() const { return storage.ss_family; }

  sockaddr *addr_mut() { return reinterpret_cast<sockaddr *>(&storage); }
  const sockaddr *addr() const {
    return reinterpret_cast<const sockaddr *>(&storage);
  }

  sockaddr_in ToIPv4() const {
    if (family() != AF_INET || len != sizeof(sockaddr_in)) {
      ADD_FAILURE() << LastSocketError();
      return sockaddr_in(); // Initialize to zero
    }
    // Make a copy so the compiler does not read this as an aliasing violation.
    sockaddr_in ret; // Initialize to zero
    OPENSSL_memcpy(&ret, &storage, sizeof(ret));
    return ret;
  }

  sockaddr_in6 ToIPv6() const {
    if (family() != AF_INET6 || len != sizeof(sockaddr_in6)) {
      ADD_FAILURE() << LastSocketError();
      return sockaddr_in6();
    }
    // Make a copy so the compiler does not read this as an aliasing violation.
    sockaddr_in6 ret;
    OPENSSL_memcpy(&ret, &storage, sizeof(ret));
    return ret;
  }
#ifdef AWS_LC_HAS_AF_UNIX
  sockaddr_un ToUnix() const {
    if (family() != AF_UNIX || len != sizeof(sockaddr_un)) {
      ADD_FAILURE() << LastSocketError();
      return sockaddr_un();
    }
    // Make a copy so the compiler does not read this as an aliasing violation.
    sockaddr_un ret;
    OPENSSL_memcpy(&ret, &storage, sizeof(ret));
    return ret;
  }
#endif
  BIO_ADDR ToBIO_ADDR() const {
    BIO_ADDR bap;
    switch (family()) {
      case AF_INET:
        OPENSSL_memcpy(&bap.s_in, &storage, sizeof(sockaddr_in));
        break;
#ifdef AWS_LC_HAS_AF_UNIX
      case AF_UNIX:
        OPENSSL_memcpy(&bap.s_un, &storage, sizeof(sockaddr_un));
        break;
#endif
      default:
        OPENSSL_memcpy(&bap.s_in6, &storage, sizeof(sockaddr_in6));
        break;
    }
    return bap;
  }

  sockaddr_storage storage;
  socklen_t len;
};

static bool operator==(const BIO_ADDR &lhs, const BIO_ADDR &rhs) {
  const sockaddr *lhs_sa = reinterpret_cast<const sockaddr *>(&lhs);
  const sockaddr *rhs_sa = reinterpret_cast<const sockaddr *>(&rhs);
  if (lhs_sa->sa_family != rhs_sa->sa_family) {
    return false;
  }

  if (lhs_sa->sa_family == AF_INET) {
    return !OPENSSL_memcmp(&lhs, &rhs, sizeof(sockaddr_in));
  }
#ifdef AF_INET6
  if (lhs_sa->sa_family == AF_INET6) {
    return !OPENSSL_memcmp(&lhs, &rhs, sizeof(sockaddr_in6));
  }
#endif
#ifdef AWS_LC_HAS_AF_UNIX
  if (lhs_sa->sa_family == AF_UNIX) {
    return !OPENSSL_memcmp(&lhs, &rhs, sizeof(sockaddr_un));
  }
#endif

  return 0;
}

class OwnedSocket {
 public:
  OwnedSocket() = default;
  explicit OwnedSocket(const Socket sock) : sock_(sock) {}
  OwnedSocket(OwnedSocket &&other) { *this = std::move(other); }
  ~OwnedSocket() { reset(); }
  OwnedSocket &operator=(OwnedSocket &&other) {
    reset(other.release());
    return *this;
  }

  bool is_valid() const { return sock_ > 0; }
  Socket get() const { return sock_; }
  Socket release() {
    const Socket temp = sock_;
    sock_ = INVALID_SOCKET;
    return temp;
  }

  SockaddrStorage storage() const {
    SockaddrStorage server_addr;
    if (0 != getsockname(get(), server_addr.addr_mut(), &server_addr.len)) {
      ADD_FAILURE() << LastSocketError();
    }
    return server_addr;
  }

  void reset(const Socket sock = INVALID_SOCKET) {
    if (is_valid()) {
      closesocket(sock_);
    }

    sock_ = sock;
  }

 private:
  Socket sock_ = INVALID_SOCKET;
};

static OwnedSocket Bind(const int family, const int type, const sockaddr *addr,
                        const socklen_t addr_len) {
  OwnedSocket sock(socket(family, type, 0));
  if (!sock.is_valid()) {
    return {};
  }

  // If no port given (e.g., addr.sin_port == 0), one is selected arbitrarily.
  if (bind(sock.get(), addr, addr_len) != 0) {
    return {};
  }

  return sock;
}

#ifdef AWS_LC_HAS_AF_UNIX
static int prepare_unix_domain_socket(sockaddr_un *sun) {
  assert(sun != NULL);

  OPENSSL_cleanse(sun, sizeof(struct sockaddr_un));
  sun->sun_family = AF_UNIX;

  char dir_buffer[PATH_MAX] = {0};
  char file_buffer[PATH_MAX] = {0};

  const size_t tmp_dir_len = createTempDirPath(dir_buffer);
  const size_t tmp_file_len = createTempFILEpath(file_buffer);

  const size_t tmp_combined_len = tmp_dir_len + tmp_file_len + 1;
  if (tmp_dir_len == 0 || tmp_file_len == 0 ||
      tmp_combined_len >= sizeof(sun->sun_path) ||
      tmp_combined_len >= PATH_MAX) {
    return 0;
  }
  OPENSSL_memcpy((void *)sun->sun_path, (void *)dir_buffer, tmp_dir_len);
  sun->sun_path[tmp_dir_len] = '/';
  OPENSSL_memcpy((void *)(sun->sun_path + tmp_dir_len + 1), (void *)file_buffer,
                 tmp_file_len);
  sun->sun_path[tmp_combined_len] = '\0';
  return 1;
}
#endif

static OwnedSocket ListenLoopback(int type, int addr_family = 0,
                                  int backlog = 1) {
  OwnedSocket sock;
  if (addr_family == 0 || addr_family == AF_INET6) {
    // Try binding to IPv6
    sockaddr_in6 sin6;
    OPENSSL_cleanse(&sin6, sizeof(sin6));
    sin6.sin6_family = AF_INET6;
    if (inet_pton(AF_INET6, "::1", &sin6.sin6_addr) != 1) {
      ADD_FAILURE() << LastSocketError();
      return OwnedSocket();
    }
    sock = Bind(AF_INET6, type, reinterpret_cast<const sockaddr *>(&sin6),
                sizeof(sin6));
  }
  if (addr_family == AF_INET || (addr_family == 0 && !sock.is_valid())) {
    // Try binding to IPv4.
    sockaddr_in sin;
    OPENSSL_cleanse(&sin, sizeof(sin));
    sin.sin_family = AF_INET;
    if (inet_pton(AF_INET, "127.0.0.1", &sin.sin_addr) != 1) {
      ADD_FAILURE() << LastSocketError();
      return OwnedSocket();
    }
    sock = Bind(AF_INET, type, reinterpret_cast<const sockaddr *>(&sin),
                sizeof(sin));

    if (!sock.is_valid()) {
      ADD_FAILURE() << LastSocketError();
      return OwnedSocket();
    }
  }
#ifdef AWS_LC_HAS_AF_UNIX
  if (addr_family == AF_UNIX) {
    sockaddr_un sun;
    if (1 != prepare_unix_domain_socket(&sun)) {
      ADD_FAILURE() << LastSocketError();
      return OwnedSocket();
    }

    // Try binding to Unix domain socket
    sock = Bind(AF_UNIX, type, reinterpret_cast<const sockaddr *>(&sun),
                sizeof(sun));
    if (!sock.is_valid()) {
      ADD_FAILURE() << LastSocketError();
      unlink((char *)sun.sun_path);
      return OwnedSocket();
    }

    // Set socket permissions (optional)
    if (chmod(sun.sun_path, 0660) == -1) {
      ADD_FAILURE() << LastSocketError();
      unlink((char *)sun.sun_path);
      return OwnedSocket();
    }
  }
#endif
  // Mark the socket as being used to accept incoming connection requests using
  // accept(2). Socket must be of type SOCK_STREAM or SOCK_SEQPACKET.
  if (type == SOCK_STREAM || type == SOCK_SEQPACKET) {
    if (listen(sock.get(), backlog) != 0) {
      ADD_FAILURE() << LastSocketError();
      return OwnedSocket();
    }
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
  // Use an arbitrary 5-second timeout, so the test doesn't hang indefinitely if
  // there's an issue.
  static constexpr int kTimeoutSeconds = 5;
#if defined(OPENSSL_WINDOWS)
  fd_set read_set, write_set;
  FD_ZERO(&read_set);
  FD_ZERO(&write_set);
  fd_set *wait_set = wait_type == WaitType::kRead ? &read_set : &write_set;
  FD_SET(sock, wait_set);
  timeval timeout = {kTimeoutSeconds, 0};
  if (select(0 /* unused on Windows */, &read_set, &write_set, nullptr,
             &timeout) <= 0) {
    return false;
  }
  return FD_ISSET(sock, wait_set);
#else
  const short events = wait_type == WaitType::kRead ? POLLIN : POLLOUT;
  pollfd fd = {.fd = sock, .events = events, .revents = 0};
  return poll(&fd, 1, kTimeoutSeconds * 1000) == 1 && (fd.revents & events);
#endif
}

TEST(BIOTest, SocketConnect) {
  static constexpr char kTestMessage[] = "test";
  const OwnedSocket listening_sock = ListenLoopback(SOCK_STREAM);
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
  const bssl::UniquePtr<BIO> bio(BIO_new_connect(hostname));
  ASSERT_TRUE(bio);

  // Write a test message to the BIO. This is assumed to be smaller than the
  // transport buffer.
  ASSERT_EQ(static_cast<int>(sizeof(kTestMessage)),
            BIO_write(bio.get(), kTestMessage, sizeof(kTestMessage)))
      << LastSocketError();

  // Accept the socket.
  const OwnedSocket sock(
      accept(listening_sock.get(), addr.addr_mut(), &addr.len));
  ASSERT_TRUE(sock.is_valid()) << LastSocketError();

  // Check the same message is read back out.
  char buf[sizeof(kTestMessage)];
  ASSERT_EQ(static_cast<int>(sizeof(kTestMessage)),
            recv(sock.get(), buf, sizeof(buf), 0))
      << LastSocketError();
  ASSERT_EQ(Bytes(kTestMessage, sizeof(kTestMessage)), Bytes(buf, sizeof(buf)));
}

TEST(BIOTest, SocketNonBlocking) {
  OwnedSocket listening_sock = ListenLoopback(SOCK_STREAM);
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
  static constexpr char kTestMessage[] = "hello, world";

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

static bssl::UniquePtr<BIO> create_server_bio(int addr_family, int type) {
  // Create a server socket.
  OwnedSocket server_sock(ListenLoopback(type, addr_family));
  if (!server_sock.is_valid()) {
    if (addr_family != AF_INET6) {
      // Some CodeBuild environments don't support IPv6
      ADD_FAILURE() << LastSocketError();
    }
    return nullptr;
  }

  // Wrap the server socket in a BIO.
  return bssl::UniquePtr<BIO>(BIO_new_dgram(server_sock.release(), BIO_CLOSE));
}

static bssl::UniquePtr<BIO> create_client_bio(int addr_family, int type) {
  OwnedSocket client_sock;

#ifdef AWS_LC_HAS_AF_UNIX
  // Create a client socket.
  if (addr_family == AF_UNIX) {
    // Unix domain sockets must be configured with a file in order to
    // receive a message.
    sockaddr_un sun;
    if (1 != prepare_unix_domain_socket(&sun)) {
      ADD_FAILURE() << LastSocketError();
      return nullptr;
    }

    // Try binding to Unix domain socket
    client_sock = Bind(AF_UNIX, type, reinterpret_cast<const sockaddr *>(&sun),
                       sizeof(sun));
  } else
#endif
  {
    client_sock.reset(socket(addr_family, type, 0));
  }
  if (!client_sock.is_valid()) {
    ADD_FAILURE() << LastSocketError();
    return nullptr;
  }

  // Wrap the client socket in a BIO.
  return bssl::UniquePtr<BIO>(BIO_new_dgram(client_sock.release(), BIO_CLOSE));
}

static void test_send_receive(bssl::UniquePtr<BIO> &sender_bio,
                              bssl::UniquePtr<BIO> &receiver_bio) {
  static constexpr char kTestMessage[] = "test";

  // Send a message
  ASSERT_EQ((int)strlen(kTestMessage) + 1,
            BIO_write(sender_bio.get(), kTestMessage, sizeof(kTestMessage)))
      << LastSocketError();
  // BIO_flush is a no-op, but test it anyway.
  ASSERT_EQ(1, BIO_flush(sender_bio.get())) << LastSocketError();

  // Receive a message
  char buff[1024];
  OPENSSL_cleanse(buff, sizeof(buff));
  ASSERT_EQ((int)strlen(kTestMessage) + 1,
            BIO_read(receiver_bio.get(), buff, sizeof(buff)))
      << LastSocketError();

  // Verify the message received matches the message sent.
  ASSERT_EQ(Bytes(buff), Bytes(kTestMessage));
}

static void test_puts_receive(bssl::UniquePtr<BIO> &sender_bio,
                              bssl::UniquePtr<BIO> &receiver_bio) {
  static constexpr char kTestMessage[] = "test";

  // Send a message
  ASSERT_EQ((int)strlen(kTestMessage),
            BIO_puts(sender_bio.get(), kTestMessage))
      << LastSocketError();
  // BIO_flush is a no-op, but test it anyway.
  ASSERT_EQ(1, BIO_flush(sender_bio.get())) << LastSocketError();

  // Receive a message.
  char buff[1024];
  OPENSSL_cleanse(buff, sizeof(buff));
  // `BIO_puts` does not send the \0 byte at the end of the string.
  ASSERT_EQ((int)strlen(kTestMessage),
            BIO_read(receiver_bio.get(), buff, sizeof(buff)))
      << LastSocketError();
  buff[strlen(kTestMessage)] = '\0';

  // Verify the message received matches the message sent.
  ASSERT_EQ(Bytes(buff), Bytes(kTestMessage));
}

class BIODgramTest : public testing::TestWithParam<int> {
  // You can implement all the usual fixture class members here.
  // To access the test parameter, call GetParam() from class
  // TestWithParam<T>.
};


#if defined(AF_INET6)
#if defined(AWS_LC_HAS_AF_UNIX)
INSTANTIATE_TEST_SUITE_P(AddrFamily, BIODgramTest,
                         testing::Values(AF_INET, AF_INET6, AF_UNIX));
#else
INSTANTIATE_TEST_SUITE_P(AddrFamily, BIODgramTest,
                         testing::Values(AF_INET, AF_INET6));
#endif
#elif defined(AWS_LC_HAS_AF_UNIX)
INSTANTIATE_TEST_SUITE_P(AddrFamily, BIODgramTest,
                         testing::Values(AF_INET, AF_UNIX));
#else
INSTANTIATE_TEST_SUITE_P(AddrFamily, BIODgramTest, testing::Values(AF_INET));
#endif

TEST_P(BIODgramTest, SocketDatagramSetPeer) {
  int addr_family = GetParam();
  // Wrap the server socket in a BIO.
  bssl::UniquePtr<BIO> server_bio = create_server_bio(addr_family, SOCK_DGRAM);
  if (!server_bio && addr_family == AF_INET6) {
    // Some CodeBuild environments don't support IPv6
    GTEST_SKIP() << "IPv6 not supported";
    return;
  }
#if defined(__MINGW32__)
  if (addr_family == AF_UNIX) {
    // Wine (is not an emulator) doesn't properly support Unix domain sockets
    GTEST_SKIP() << "Unix domain sockets not supported";
    return;
  }
#endif
  ASSERT_TRUE(server_bio) << LastSocketError();
  ASSERT_EQ(1, BIO_get_close(server_bio.get())) << LastSocketError();

  OwnedSocket server_sock(BIO_get_fd(server_bio.get(), NULL));
  ASSERT_EQ(1, BIO_set_close(server_bio.get(), BIO_NOCLOSE))
      << LastSocketError();
  SockaddrStorage server_addr = server_sock.storage();

  // Get the server socket's address
  bssl::UniquePtr<BIO> client_bio =
      create_client_bio(server_addr.family(), SOCK_DGRAM);
  ASSERT_TRUE(client_bio) << LastSocketError();

  // "Connect" the client to server
  BIO_ADDR bio_server_addr = server_addr.ToBIO_ADDR();
  ASSERT_EQ(1, BIO_dgram_set_peer(client_bio.get(), &bio_server_addr))
      << LastSocketError();

  // Get peer
  BIO_ADDR bio_server_addr_copy;
  ASSERT_GT(BIO_dgram_get_peer(client_bio.get(), &bio_server_addr_copy), 0)
      << LastSocketError();

  ASSERT_EQ(bio_server_addr, bio_server_addr_copy) << LastSocketError();

  test_send_receive(client_bio, server_bio);
  ASSERT_EQ(0, BIO_dgram_send_timedout(client_bio.get()));
  ASSERT_EQ(0, BIO_dgram_recv_timedout(server_bio.get()));
  test_send_receive(server_bio, client_bio);
  test_puts_receive(client_bio, server_bio);
}

TEST_P(BIODgramTest, SocketDatagramSetConnected) {
  int addr_family = GetParam();
  // Wrap the server socket in a BIO.
  bssl::UniquePtr<BIO> server_bio = create_server_bio(addr_family, SOCK_DGRAM);
  if (!server_bio && addr_family == AF_INET6) {
    // Some CodeBuild environments don't support IPv6
    GTEST_SKIP() << "IPv6 not supported";
    return;
  }
  ASSERT_TRUE(server_bio) << LastSocketError();

  OwnedSocket server_sock(BIO_get_fd(server_bio.get(), NULL));
  ASSERT_EQ(1, BIO_set_close(server_bio.get(), BIO_NOCLOSE))
      << LastSocketError();
  SockaddrStorage server_addr = server_sock.storage();

  // Get the server socket's address
  bssl::UniquePtr<BIO> client_bio =
      create_client_bio(server_addr.family(), SOCK_DGRAM);
  ASSERT_TRUE(client_bio) << LastSocketError();

  int client_fd = 0;
  int result = BIO_get_fd(client_bio.get(), &client_fd);
  ASSERT_EQ(result, client_fd);
  ASSERT_EQ(1, BIO_set_close(server_bio.get(), BIO_NOCLOSE))
      << LastSocketError();

  // "Connect" the client to server
  ASSERT_EQ(connect(client_fd, server_addr.addr(), server_addr.len), 0)
      << LastSocketError();
  BIO_ADDR server_bio_addr = server_addr.ToBIO_ADDR();
  ASSERT_EQ(1, BIO_ctrl_set_connected(client_bio.get(), &server_bio_addr))
      << LastSocketError();

  test_send_receive(client_bio, server_bio);
  test_send_receive(server_bio, client_bio);

  ASSERT_EQ(1, BIO_ctrl_set_connected(client_bio.get(), NULL))
      << LastSocketError();

  static constexpr char kTestMessage[] = "test";

  // Behavior is different on Linux
  int expected_result =
#if defined(OPENSSL_LINUX)
      addr_family == AF_INET6
          ? (int)OPENSSL_strnlen((const char *)kTestMessage, 32) + 1
          : -1;
#else
      -1;
#endif

#if defined(__MINGW32__)
// Mingw environments are inconsistent as to this behavior.
  if (addr_family == AF_INET6) {
    return;
  }
#endif
  ASSERT_EQ(expected_result,
            BIO_write(client_bio.get(), kTestMessage, sizeof(kTestMessage)))
      << LastSocketError();
}

TEST_P(BIODgramTest, SocketDatagramConnect) {
  int addr_family = GetParam();
  // Wrap the server socket in a BIO.
  bssl::UniquePtr<BIO> server_bio = create_server_bio(addr_family, SOCK_DGRAM);
  if (!server_bio && addr_family == AF_INET6) {
    // Some CodeBuild environments don't support IPv6
    GTEST_SKIP() << "IPv6 not supported";
    return;
  }
  ASSERT_TRUE(server_bio) << LastSocketError();

  OwnedSocket server_sock(BIO_get_fd(server_bio.get(), NULL));
  ASSERT_EQ(1, BIO_set_close(server_bio.get(), BIO_NOCLOSE))
      << LastSocketError();
  SockaddrStorage server_addr = server_sock.storage();

  // Get the server socket's address
  bssl::UniquePtr<BIO> client_bio =
      create_client_bio(server_addr.family(), SOCK_DGRAM);
  ASSERT_TRUE(client_bio) << LastSocketError();

  // "Connect" the client to server
  BIO_ADDR server_bio_addr = server_addr.ToBIO_ADDR();
  ASSERT_EQ(1, BIO_ctrl_dgram_connect(client_bio.get(), &server_bio_addr))
      << LastSocketError();
  ;

  test_send_receive(client_bio, server_bio);
  test_send_receive(server_bio, client_bio);
}
