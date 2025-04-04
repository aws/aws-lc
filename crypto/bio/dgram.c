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
static int BIO_ADDR_make(BIO_ADDR *ap, const struct sockaddr *sa) {
  if (sa->sa_family == AF_INET) {
    OPENSSL_memcpy(&ap->s_in, sa, sizeof(struct sockaddr_in));
    return 1;
  }
#ifdef AF_INET6
  if (sa->sa_family == AF_INET6) {
    OPENSSL_memcpy(&ap->s_in6, sa, sizeof(struct sockaddr_in6));
    return 1;
  }
#endif
#ifdef AF_UNIX
  if (sa->sa_family == AF_UNIX) {
    OPENSSL_memcpy(&ap->s_un, sa, sizeof(struct sockaddr_un));
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

static socklen_t BIO_ADDR_sockaddr_size(const BIO_ADDR *ap) {
  if (ap->sa.sa_family == AF_INET) {
    return sizeof(ap->s_in);
  }
#ifdef AF_INET6
  if (ap->sa.sa_family == AF_INET6) {
    return sizeof(ap->s_in6);
  }
#endif
#ifdef AF_UNIX
  if (ap->sa.sa_family == AF_UNIX) {
    return sizeof(ap->s_un);
  }
#endif
  return sizeof(*ap);
}

static struct sockaddr *BIO_ADDR_sockaddr_noconst(BIO_ADDR *ap) {
  return &ap->sa;
}

static const struct sockaddr *BIO_ADDR_sockaddr(const BIO_ADDR *ap) {
  return &ap->sa;
}

static int dgram_write(BIO *bp, const char *in, const int inl) {
  bio_dgram_data *data = bp->ptr;
  ssize_t result;

  errno = 0;
  if (data->connected) {
    // With a zero flags argument, send() is equivalent to write(2).
    result = send(bp->num, in, inl, 0);
  } else {
    // If sendto() is used on a connection-mode (SOCK_STREAM, SOCK_SEQPACKET)
    // socket, the arguments dest_addr and addrlen are ignored
    const socklen_t peerlen = BIO_ADDR_sockaddr_size(&data->peer);
    result = sendto(bp->num, in, inl, 0, BIO_ADDR_sockaddr(&data->peer), peerlen);
  }

  if (result < INT_MIN || result > INT_MAX) {
    abort();
  }
  const int ret = result;

  BIO_clear_retry_flags(bp);
  if (ret <= 0 && bio_errno_should_retry(ret)) {
    BIO_set_retry_write(bp);
    data->_errno = errno;
  }
  return ret;
}

static int dgram_read(BIO *bp, char *out, const int outl) {
  if (!out) {
    return 0;
  }

  bio_dgram_data *data = bp->ptr;
  BIO_ADDR peer = {0};
  socklen_t len = sizeof(peer);

  errno = 0;

  // recvfrom may be used to receive data on a socket whether or not it is
  // connection-oriented.
  const ssize_t result = recvfrom(bp->num, out, outl, 0,
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
  if (ret < 0 && bio_errno_should_retry(ret)) {
    BIO_set_retry_read(bp);
    data->_errno = errno;
  }

  return ret;
}

static int dgram_puts(BIO *bp, const char *str) {
  const size_t len = strlen(str);
  if (len > INT_MAX) {
    return 0;
  }
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
  return 1;
}

static long dgram_ctrl(BIO *b, const int cmd, const long num, void *ptr) {
  GUARD_PTR(b);
  bio_dgram_data *data = b->ptr;

  long ret = 1;

  switch (cmd) {
    case BIO_C_SET_FD:
      if (0 == dgram_free(b)) {
        assert(0);
      }
      b->num = *(int*)ptr;
      b->shutdown = (int)num;
      b->init = 1;
      break;
    case BIO_C_GET_FD:
      if (b->init) {
        int *ip = ptr;
        if (ip) {
          *ip = b->num;
        }
        ret = b->num;
      } else {
        ret = -1;
      }
      break;
    case BIO_CTRL_GET_CLOSE:
      ret = b->shutdown;
      break;
    case BIO_CTRL_SET_CLOSE:
      b->shutdown = (int)num;
      break;
    case BIO_CTRL_FLUSH:
      ret = 1;
      break;
    case BIO_CTRL_DGRAM_GET_MTU:
      ret = data->mtu;
      break;
    case BIO_CTRL_DGRAM_SET_MTU:
      data->mtu = num;
      ret = num;
      break;
    case BIO_CTRL_DGRAM_SET_CONNECTED:
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
      ret = BIO_ADDR_make(&data->peer, BIO_ADDR_sockaddr(ptr));
      break;
    case BIO_CTRL_DGRAM_GET_PEER: {
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
      ret = BIO_ADDR_make(&data->peer, BIO_ADDR_sockaddr(ptr));
      break;
    case BIO_CTRL_DGRAM_GET_SEND_TIMER_EXP:
    /* fall-through */
    case BIO_CTRL_DGRAM_GET_RECV_TIMER_EXP: {
      int d_errno = 0;
# ifdef OPENSSL_WINDOWS
      d_errno = (data->_errno == WSAETIMEDOUT);
# else
      d_errno = (data->_errno == EAGAIN);
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
