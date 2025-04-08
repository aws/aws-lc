// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/bio.h>
#include <openssl/mem.h>

#if defined(OPENSSL_WINDOWS)
#include <windows.h>
#include <winsock2.h>
#include <afunix.h>
#include <ws2ipdef.h>
#else
#include <netinet/in.h>
#include <sys/socket.h>
#include <sys/un.h>
#include <unistd.h>
#endif
#include <sys/time.h>

#include "../internal.h"
#include "./internal.h"

#if !defined(OPENSSL_WINDOWS)
static int closesocket(const int sock) { return close(sock); }
#endif

/*
 * BIO_ADDR_make - non-public routine to fill a BIO_ADDR with the contents
 * of a struct sockaddr.
 */

static int BIO_ADDR_make(BIO_ADDR *bap, const struct sockaddr *sap) {
  GUARD_PTR(bap);
  GUARD_PTR(sap);
  if (sap->sa_family == AF_INET) {
    OPENSSL_memcpy(&bap->s_in, sap, sizeof(struct sockaddr_in));
    return 1;
  }
#ifdef AF_INET6
  if (sap->sa_family == AF_INET6) {
    OPENSSL_memcpy(&bap->s_in6, sap, sizeof(struct sockaddr_in6));
    return 1;
  }
#endif
#ifdef AF_UNIX
  if (sap->sa_family == AF_UNIX) {
    OPENSSL_memcpy(&bap->s_un, sap, sizeof(struct sockaddr_un));
    return 1;
  }
#endif

  return 0;
}

typedef struct bio_dgram_data_st {
  BIO_ADDR peer;
  unsigned int connected;
  unsigned int _errno;
  unsigned int mtu;
} bio_dgram_data;

static socklen_t BIO_ADDR_sockaddr_size(const BIO_ADDR *bap) {
  GUARD_PTR(bap);
  if (bap->sa.sa_family == AF_INET) {
    return sizeof(bap->s_in);
  }
#ifdef AF_INET6
  if (bap->sa.sa_family == AF_INET6) {
    return sizeof(bap->s_in6);
  }
#endif
#ifdef AF_UNIX
  if (bap->sa.sa_family == AF_UNIX) {
    return sizeof(bap->s_un);
  }
#endif
  return sizeof(*bap);
}



static struct sockaddr *BIO_ADDR_sockaddr_noconst(BIO_ADDR *bap) {
  GUARD_PTR(bap);
  return &bap->sa;
}

static const struct sockaddr *BIO_ADDR_sockaddr(const BIO_ADDR *bap) {
  GUARD_PTR(bap);
  return &bap->sa;
}

static int dgram_write(BIO *bp, const char *in, const int in_len) {
  GUARD_PTR(bp);
  GUARD_PTR(in);

  bio_dgram_data *data = bp->ptr;
  ssize_t result;

  if (in_len <= 0) {
    OPENSSL_PUT_ERROR(BIO, BIO_R_INVALID_ARGUMENT);
    return 0;
  }

  bio_clear_socket_error(bp->num);
  if (data->connected) {
    // With a zero flags argument, send() is equivalent to write(2).
    result = send(bp->num, in, in_len, 0);
  } else {
    // If sendto() is used on a connection-mode (SOCK_STREAM, SOCK_SEQPACKET)
    // socket, the arguments dest_addr and addrlen are ignored
    const socklen_t peerlen = BIO_ADDR_sockaddr_size(&data->peer);
    result = sendto(bp->num, in, in_len, 0, BIO_ADDR_sockaddr(&data->peer), peerlen);
  }

  if (result < INT_MIN || result > INT_MAX) {
    abort();
  }
  const int ret = result;

  BIO_clear_retry_flags(bp);
  if (ret <= 0 && bio_socket_should_retry(ret)) {
    BIO_set_retry_write(bp);
    data->_errno = bio_sock_error_get_and_clear(bp->num);
  }
  return ret;
}

static int dgram_read(BIO *bp, char *out, const int out_len) {
  GUARD_PTR(bp);
  GUARD_PTR(out);

  bio_dgram_data *data = bp->ptr;
  BIO_ADDR peer = {0};
  socklen_t len = sizeof(peer);

  bio_clear_socket_error(bp->num);

  // recvfrom may be used to receive data on a socket regardless of whether
  // it's connection-oriented.
  const ssize_t result = recvfrom(bp->num, out, out_len, 0,
                     BIO_ADDR_sockaddr_noconst(&peer), &len);

  if (result < INT_MIN || result > INT_MAX) {
    abort();
  }
  const int ret = result;

  if (!data->connected && ret >= 0) {
    assert(len == BIO_ADDR_sockaddr_size(&peer));
    BIO_ctrl(bp, BIO_CTRL_DGRAM_SET_PEER, 0, &peer);
  }

  BIO_clear_retry_flags(bp);
  if (ret < 0 && bio_socket_should_retry(ret)) {
    BIO_set_retry_read(bp);
    data->_errno = bio_sock_error_get_and_clear(bp->num);
  }

  return ret;
}

static int dgram_puts(BIO *bp, const char *str) {
  GUARD_PTR(bp);
  GUARD_PTR(str);

  const int len = OPENSSL_strnlen(str, INT_MAX);
  return dgram_write(bp, str, len);
}

static int dgram_free(BIO *bp) {
  GUARD_PTR(bp);
  if (bp->shutdown && bp->init) {
    if (0 != closesocket(bp->num)) {
      // the show must go on
    }
  }
  bp->init = 0;
  bp->flags = 0;
  OPENSSL_free(bp->ptr);
  bp->ptr = NULL;
  return 1;
}

static long dgram_ctrl(BIO *bp, const int cmd, const long num, void *ptr) {
  GUARD_PTR(bp);
  bio_dgram_data *data = bp->ptr;

  long ret = 1;

  switch (cmd) {
    case BIO_C_SET_FD:
      GUARD_PTR(ptr);
      if (0 == dgram_free(bp)) {
        assert(0);
      }
      bp->num = *(int*)ptr;
      bp->shutdown = (int)num;
      bp->init = 1;
      break;
    case BIO_C_GET_FD:
      GUARD_PTR(ptr);
      if (bp->init) {
        int *ip = ptr;
        if (ip) {
          *ip = bp->num;
        }
        ret = bp->num;
      } else {
        ret = -1;
      }
      break;
    case BIO_CTRL_GET_CLOSE:
      ret = bp->shutdown;
      break;
    case BIO_CTRL_SET_CLOSE:
      bp->shutdown = (num != 0);
      break;
    case BIO_CTRL_FLUSH:
      ret = 1;
      break;
    case BIO_CTRL_DGRAM_GET_MTU:
      GUARD_PTR(data);
      ret = data->mtu;
      break;
    case BIO_CTRL_DGRAM_SET_MTU:
      GUARD_PTR(data);
      data->mtu = num;
      ret = num;
      break;
    case BIO_CTRL_DGRAM_SET_CONNECTED:
      GUARD_PTR(data);
      if (ptr != NULL) {
        data->connected = 1;
        ret = BIO_ADDR_make(&data->peer, BIO_ADDR_sockaddr(ptr));
      } else {
        data->connected = 0;
        OPENSSL_cleanse(&data->peer, sizeof(data->peer));
        ret = 1;
      }
      break;
    case BIO_CTRL_DGRAM_CONNECT:
      GUARD_PTR(data);
      GUARD_PTR(ptr);
      ret = BIO_ADDR_make(&data->peer, BIO_ADDR_sockaddr(ptr));
      break;
    case BIO_CTRL_DGRAM_GET_PEER: {
      GUARD_PTR(data);
      GUARD_PTR(ptr);
      const socklen_t size = BIO_ADDR_sockaddr_size(&data->peer);
      if (num == 0 || num > size) {
        OPENSSL_memcpy(ptr, &data->peer, size);
        ret = size;
      } else {
        ret = 0;
      }
      break;
    }
    case BIO_CTRL_DGRAM_SET_PEER:
      GUARD_PTR(data);
      GUARD_PTR(ptr);
      ret = BIO_ADDR_make(&data->peer, BIO_ADDR_sockaddr(ptr));
      break;
    case BIO_CTRL_DGRAM_GET_SEND_TIMER_EXP:
    case BIO_CTRL_DGRAM_GET_RECV_TIMER_EXP: {

      GUARD_PTR(data);
      int d_errno = 0;
# ifdef OPENSSL_WINDOWS
      d_errno = (data->_errno == WSAETIMEDOUT);
# else
      /*
      * if no data has been transferred and the timeout has been reached,
      * then -1 is returned with errno set to EAGAIN or EWOULDBLOCK,
      * or EINPROGRESS (for connect(2)) just as if the socket was specified
      * to be nonblocking.
     */
      d_errno = (data->_errno == EAGAIN) || (data->_errno == EWOULDBLOCK) ||
          (data->_errno == EINPROGRESS);
# endif
      if (d_errno) {
        ret = 1;
        data->_errno = 0;
      } else
        ret = 0;
      break;
    }
    default:
      ret = 0;
      break;
  }
  return ret;
}

static int dgram_new(BIO *bio) {
  bio_dgram_data *data = OPENSSL_zalloc(sizeof(*data));
  if (!data) {
    return 0;
  }
  bio->ptr = data;
  return 1;
}

static const BIO_METHOD methods_dgramp = {
    .type = BIO_TYPE_DGRAM,
    .name = "datagram socket",
    .bwrite = dgram_write,
    .bread = dgram_read,
    .bputs = dgram_puts,
    .bgets = NULL,
    .ctrl = dgram_ctrl,
    .create = dgram_new,
    .destroy = dgram_free,
    .callback_ctrl = NULL,
};

const BIO_METHOD *BIO_s_datagram(void) { return &methods_dgramp; }

BIO *BIO_new_dgram(int fd, int close_flag)
{
  BIO *ret;

  ret = BIO_new(BIO_s_datagram());
  if (ret == NULL)
    return NULL;
  BIO_set_fd(ret, fd, close_flag);
  return ret;
}

int BIO_ctrl_dgram_connect(BIO *bp, const BIO_ADDR *peer) {
  long ret = BIO_ctrl(bp, BIO_CTRL_DGRAM_CONNECT, 0, (BIO_ADDR*)peer);
  if (ret < INT_MIN || ret > INT_MAX) {
    return 0;
  }
  return ret;
}

int BIO_ctrl_set_connected(BIO* bp, const BIO_ADDR *peer) {
  long ret = BIO_ctrl(bp, BIO_CTRL_DGRAM_SET_CONNECTED, 0, (BIO_ADDR*)peer);
  if (ret < INT_MIN || ret > INT_MAX) {
    return 0;
  }
  return ret;
}

int BIO_dgram_recv_timedout(BIO* bp) {
  long ret = BIO_ctrl(bp, BIO_CTRL_DGRAM_GET_RECV_TIMER_EXP, 0, NULL);
  if (ret < INT_MIN || ret > INT_MAX) {
    return 0;
  }
  return ret;
}

int BIO_dgram_send_timedout(BIO* bp) {
  long ret = BIO_ctrl(bp, BIO_CTRL_DGRAM_GET_SEND_TIMER_EXP, 0, NULL);
  if (ret < INT_MIN || ret > INT_MAX) {
    return 0;
  }
  return ret;
}

int BIO_dgram_get_peer(BIO* bp, BIO_ADDR *peer) {
  long ret = BIO_ctrl(bp, BIO_CTRL_DGRAM_GET_PEER, 0, peer);
  if (ret < INT_MIN || ret > INT_MAX) {
    return 0;
  }
  return ret;
}

int BIO_dgram_set_peer(BIO* bp, const BIO_ADDR *peer) {
  long ret = BIO_ctrl(bp, BIO_CTRL_DGRAM_SET_PEER, 0, (BIO_ADDR*)peer);
  if (ret < INT_MIN || ret > INT_MAX) {
    return 0;
  }
  return ret;
}
