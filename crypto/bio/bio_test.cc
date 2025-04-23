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

#include <gtest/gtest.h>

#include <openssl/bio.h>
#include <openssl/crypto.h>
#include <openssl/err.h>
#include <openssl/mem.h>

#include "../internal.h"
#include "../test/test_util.h"

#if !defined(OPENSSL_WINDOWS)
#include <arpa/inet.h>
#include <errno.h>
#include <fcntl.h>
#include <netinet/in.h>
#include <string.h>
#include <sys/socket.h>
#include <unistd.h>
#else
#include <io.h>
OPENSSL_MSVC_PRAGMA(warning(push, 3))
#include <winsock2.h>
#include <ws2tcpip.h>
OPENSSL_MSVC_PRAGMA(warning(pop))
#endif


#if !defined(OPENSSL_WINDOWS)
static int closesocket(int sock) { return close(sock); }
static std::string LastSocketError() { return strerror(errno); }
#else
static std::string LastSocketError() {
  char buf[DECIMAL_SIZE(int) + 1];
  BIO_snprintf(buf, sizeof(buf), "%d", WSAGetLastError());
  return buf;
}
#endif

class ScopedSocket {
 public:
  explicit ScopedSocket(int sock) : sock_(sock) {}
  ~ScopedSocket() { closesocket(sock_); }

 private:
  const int sock_;
};

TEST(BIOTest, SocketConnect) {
  static const char kTestMessage[] = "test";
  int listening_sock = -1;
  socklen_t len = 0;
  sockaddr_storage ss;
  struct sockaddr_in6 *sin6 = (struct sockaddr_in6 *)&ss;
  struct sockaddr_in *sin = (struct sockaddr_in *)&ss;
  OPENSSL_memset(&ss, 0, sizeof(ss));

  ss.ss_family = AF_INET6;
  listening_sock = socket(AF_INET6, SOCK_STREAM, 0);
  ASSERT_NE(-1, listening_sock) << LastSocketError();
  len = sizeof(*sin6);
  ASSERT_EQ(1, inet_pton(AF_INET6, "::1", &sin6->sin6_addr))
      << LastSocketError();
  if (bind(listening_sock, (struct sockaddr *)sin6, sizeof(*sin6)) == -1) {
    closesocket(listening_sock);

    ss.ss_family = AF_INET;
    listening_sock = socket(AF_INET, SOCK_STREAM, 0);
    ASSERT_NE(-1, listening_sock) << LastSocketError();
    len = sizeof(*sin);
    ASSERT_EQ(1, inet_pton(AF_INET, "127.0.0.1", &sin->sin_addr))
        << LastSocketError();
    ASSERT_EQ(0, bind(listening_sock, (struct sockaddr *)sin, sizeof(*sin)))
        << LastSocketError();
  }

  ScopedSocket listening_sock_closer(listening_sock);
  ASSERT_EQ(0, listen(listening_sock, 1)) << LastSocketError();
  ASSERT_EQ(0, getsockname(listening_sock, (struct sockaddr *)&ss, &len))
      << LastSocketError();

  char hostname[80];
  if (ss.ss_family == AF_INET6) {
    BIO_snprintf(hostname, sizeof(hostname), "[::1]:%d",
                 ntohs(sin6->sin6_port));
  } else if (ss.ss_family == AF_INET) {
    BIO_snprintf(hostname, sizeof(hostname), "127.0.0.1:%d",
                 ntohs(sin->sin_port));
  }

  // Connect to it with a connect BIO.
  bssl::UniquePtr<BIO> bio(BIO_new_connect(hostname));
  ASSERT_TRUE(bio);

  // Write a test message to the BIO.
  ASSERT_EQ(static_cast<int>(sizeof(kTestMessage)),
            BIO_write(bio.get(), kTestMessage, sizeof(kTestMessage)));

  // Accept the socket.
  int sock = accept(listening_sock, (struct sockaddr *)&ss, &len);
  ASSERT_NE(-1, sock) << LastSocketError();
  ScopedSocket sock_closer(sock);

  // Check the same message is read back out.
  char buf[sizeof(kTestMessage)];
  ASSERT_EQ(static_cast<int>(sizeof(kTestMessage)),
            recv(sock, buf, sizeof(buf), 0))
      << LastSocketError();
  EXPECT_EQ(Bytes(kTestMessage, sizeof(kTestMessage)), Bytes(buf, sizeof(buf)));
}

TEST(BIOTest, Printf) {
  // Test a short output, a very long one, and various sizes around
  // 256 (the size of the buffer) to ensure edge cases are correct.
  static const size_t kLengths[] = {5, 250, 251, 252, 253, 254, 1023};

  bssl::UniquePtr<BIO> bio(BIO_new(BIO_s_mem()));
  ASSERT_TRUE(bio);

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

typedef struct {
  int custom_data;
} CustomData;

static void CustomDataFree(void *parent, void *ptr, CRYPTO_EX_DATA *ad,
                           int index, long argl, void *argp) {
  free(ptr);
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

  uint32_t err = ERR_get_error();
  EXPECT_EQ(ERR_LIB_BIO, ERR_GET_LIB(err));
  EXPECT_EQ(BIO_R_BROKEN_PIPE, ERR_GET_REASON(err));

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
    ASSERT_TRUE(BIO_set_conn_port(bio, "8080"));
    ASSERT_TRUE(BIO_callback_ctrl(bio, BIO_CTRL_SET_CALLBACK, callback));

    ASSERT_EQ(BIO_do_connect(bio), 0);
    ASSERT_EQ(callback_invoked, 1);

    ASSERT_TRUE(BIO_free(bio));
  }
}

INSTANTIATE_TEST_SUITE_P(All, BIOPairTest, testing::Values(false, true));
