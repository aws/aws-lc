
/*
 * ssl_conn_transfer.c
 *
 * A deep dive into passing network sockets around. Utilizes control messages
 * to pass socket/file descriptors from server process to proxy process via
 * sendmsg and recvmsg over TCP socket.
 *
 * Connection transfer can be tested using openssl's client:
 * openssl s_client -connect localhost:3011
 *
 * This is an Openssl-style test implementation. As AWS-LC offers an extensive
 * test suite that's completely different from OpenSSL one. So this test is
 * ought to be rewritten to fit it and added, along with other tests, to cover
 * the implementation of SSL connection transfer.
 */

#include <netinet/in.h>
#include <stdio.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <unistd.h>
#include <assert.h>

#include <openssl/ssl.h>
#include <openssl/err.h>

#define MAX_BUF_SZ	1024
#define SRV_PORT	3011
typedef unsigned int uint;

SSL_CTX *ctx= NULL;
int sendfd(int socket, int fd);
int recvfd(int socket);
void server(int proxy);
void proxy(int server);

int
sendfd(int socket, int fd)
{
	int					ret;
	char				dummy = '$';
	struct				msghdr msg;
	struct				iovec iov;
	char				cmsgbuf[CMSG_SPACE(sizeof(int))];
	struct cmsghdr	   *cmsg;
        int *msg_data;
	iov.iov_base = &dummy;
	iov.iov_len = sizeof(dummy);

	msg.msg_name = NULL;
	msg.msg_namelen = 0;
	msg.msg_iov = &iov;
	msg.msg_iovlen = 1;
	msg.msg_flags = 0;
	msg.msg_control = cmsgbuf;
	msg.msg_controllen = CMSG_LEN(sizeof(int));

	cmsg = CMSG_FIRSTHDR(&msg);
	cmsg->cmsg_level = SOL_SOCKET;
	cmsg->cmsg_type = SCM_RIGHTS;
	cmsg->cmsg_len = CMSG_LEN(sizeof(int));

        msg_data=(int*) CMSG_DATA(cmsg);
        *msg_data= fd;
	ret = sendmsg(socket, &msg, 0);
	if (ret == -1)
	{
		perror("sendfd failed");
		exit(EXIT_FAILURE);
	}

	return ret;
}

int
recvfd(int socket)
{
	int	len;
	int	fd;
	char	buf[1];
	struct	iovec iov;
	struct	msghdr msg;
	struct	cmsghdr *cmsg;
	char	cms[CMSG_SPACE(sizeof(int))];

	iov.iov_base = buf;
	iov.iov_len = sizeof(buf);

	msg.msg_name = 0;
	msg.msg_namelen = 0;
	msg.msg_iov = &iov;
	msg.msg_iovlen = 1;
	msg.msg_flags = 0;
	msg.msg_control = (void*) cms;
	msg.msg_controllen = sizeof cms;

	len = recvmsg(socket, &msg, 0);

	if (len < 0)
	{
		perror("recvmsg failed");
		exit(EXIT_FAILURE);
	}

	if (len == 0)
	{
		perror("recvmsg failed with no data");
		exit(EXIT_FAILURE);
	}

	cmsg = CMSG_FIRSTHDR(&msg);
	memmove(&fd, CMSG_DATA(cmsg), sizeof(int));
	return fd;
}


//void bin_dump(unsigned char *ptr, uint len)
//{
//  int i;
//  for (i= 0; i < len; i++)
//  {
//    if ((i % 16) == 0)
//      printf("bin> ");
//    if ((i % 16) == 8)
//      printf(" ");
//    printf("%.2hhx ",ptr[i]);
//    if ((i % 16) == 15)
//      printf("\n");
//  }
//  printf("\n");
//}


void
server(int proxy)
{
	int	srvsock;
	int	clientsock;
	int	cnt;
	struct sockaddr_in	addr;
	int	opt = 1;
	int	addrlen = sizeof(addr);
	char	buf[MAX_BUF_SZ] = {0};
//        int ret;

	/* Create the server socket */
	if ((srvsock = socket(AF_INET, SOCK_STREAM, 0)) == 0)
	{
		perror("failed to create server socket");
		exit(EXIT_FAILURE);
	}

	/*
	 * Set socket options: https://linux.die.net/man/2/setsockopt
	 */
	if (setsockopt(srvsock, SOL_SOCKET, SO_REUSEADDR, &opt, sizeof(opt)))
	{
		perror("failed to set socket options");
		exit(EXIT_FAILURE);
	}

	addr.sin_family = AF_INET;
	addr.sin_addr.s_addr = INADDR_ANY;
	addr.sin_port = htons(SRV_PORT);

	/* Bind the socket to the address */
	if (bind(srvsock, (struct sockaddr *)&addr, sizeof(addr)) < 0)
	{
		perror("bind failed");
		exit(EXIT_FAILURE);
	}

	/* Start listening for incoming connections and take action */
	if (listen(srvsock, 3) < 0)
	{
		perror("failed to listen for incoming connections");
		exit(EXIT_FAILURE);
	}

	while (1)
	{
          SSL *ssl;
          const char reply[] = "server> (type)";
		printf("server> waiting to accept new connection ...\n");
		if ((clientsock = accept(srvsock, (struct sockaddr *)&addr, (socklen_t*)&addrlen))<0)
		{
			perror("failed to accept client connection");
			exit(EXIT_FAILURE);
		}
                // Start connection and do some reads/writes
                printf("server> accepted connection\n");
                ssl = SSL_new(ctx);
                SSL_set_fd(ssl, clientsock);
                SSL_set_encode_mode(ssl, 1);

                if (SSL_accept(ssl) <=0 )
                {
                  perror("failed to accept SSL connection");
                  exit(EXIT_FAILURE);
                }
                assert(ret > 0);
                SSL_write(ssl, reply, strlen(reply));

                cnt= SSL_read(ssl, buf, MAX_BUF_SZ);
                assert(cnt>=0);
                buf[cnt]=0;
		printf("server> received from client: '%s'\n", buf);
		printf("server> echo'ing back to client: '%s'\n", buf);
                SSL_write(ssl, buf, cnt);


		printf("server> transferring client socket to proxy, sock %u\n", clientsock);
                uint8_t *ssl_conn;
                // Serialize an alive SSL connection
                ssize_t conn_len= i2d_SSL(ssl, &ssl_conn);
                if (!conn_len)
                {
                  perror("failed to serialize SSL connection");
                  exit(EXIT_FAILURE);
                }
                printf("i2d_SSL %i\n", (int)conn_len);
                // Send it over to another process
		sendfd(proxy, clientsock);
                send(proxy, &conn_len, sizeof(conn_len), 0);
                send(proxy, ssl_conn, conn_len, 0);

		printf("server> closing client socket on server, ensure client is still connected\n");
                sleep(60);
                SSL_shutdown(ssl);
                SSL_free(ssl);
                close(clientsock);
	}
}

void
proxy(int server)
{
	int		fd;
        ssize_t         conn_len;
        unsigned char         *serialized_connection, *p;
	char	cbuf[MAX_BUF_SZ] = {0};
	char	sbuf[MAX_BUF_SZ] = {0};

	while(1)
	{
          SSL *ssl= NULL;
          SSL_SESSION *sess=NULL;
          printf("proxy started, sock %u\n",server);

          // Receive the serialized connection
          fd = recvfd(server);
          recv(server, &conn_len, sizeof(conn_len), 0);
          serialized_connection =
            (unsigned char*) malloc(sizeof(char) * conn_len);
          recv(server, serialized_connection, conn_len, 0);
          printf("proxy> received connection, fd %u,len %li\n", fd, conn_len);
//          bin_dump(serialized_connection, conn_len);
          p= serialized_connection;

          // Restore SSL connection
          ssl= d2i_SSL(&ssl, ctx, (const unsigned char**)&p, conn_len);
          SSL_set_fd(ssl, fd);
          int bytes_read;
          int bytes_written;

          // Do some reads/writes on the restored connection
	  printf("proxy> sending client greeting, SSL %p, SQL_SESSION %p\n",ssl, sess);
          if (!ssl)
            ERR_print_errors_fp(stderr);
	  snprintf(sbuf, MAX_BUF_SZ, "proxy has received your connection, greetings\nproxy> (type)");
          bytes_written = SSL_write(ssl, sbuf, strlen(sbuf));
          if (bytes_written < 0)
          {
            printf("proxy> SSL_write failed\n");
            goto err;
          }
          bytes_read = SSL_read(ssl, cbuf, MAX_BUF_SZ);
          if (bytes_read < 0)
          {
            printf("proxy> SSL_read failed\n");
            goto err;
          }
	  cbuf[bytes_read]=0;
	  printf("proxy> received from client: '%s'\n", cbuf);
	  snprintf(sbuf, MAX_BUF_SZ, "proxy: %s\n", cbuf);
	  printf("proxy> echo'ing back to client: '%s'\n", sbuf);
          SSL_write(ssl, sbuf, strlen("proxy:\n") + bytes_read);
	  printf("proxy> closing client connection\n");
err:
          SSL_shutdown(ssl);
          SSL_free(ssl);
          close(fd);
	}
}
#define SSL_CIPHER_LIST_SIZE 4096

int
main(int argc, char **argv)
{
	int		pid;
	int		socks[2];

        SSL_load_error_strings();
        OpenSSL_add_ssl_algorithms();

        long ssl_ctx_options= SSL_OP_NO_SSLv2 | SSL_OP_NO_SSLv3;
        ctx= SSL_CTX_new(SSLv23_server_method());


        assert(ctx);
        SSL_CTX_set_options(ctx, ssl_ctx_options);

        if (SSL_CTX_use_certificate_file(ctx, "certs/servercert.pem",
                                         SSL_FILETYPE_PEM) <= 0)
        {
		perror("failed to read server cert");
                goto err;

        }
        if (SSL_CTX_use_PrivateKey_file(ctx, "certs/serverkey.pem",
                                        SSL_FILETYPE_PEM) <= 0)
        {
		perror("failed to read server key");
                goto err;

        }
	/* Create a socket pair to be used by server and proxy to handoff client sockets */

	if (socketpair(PF_UNIX, SOCK_DGRAM, 0, socks) < 0)
	{
		perror("failed to create socket socks");
                goto err;
	}

	if ((pid = fork()) < 0)
	{
		perror("failed to fork proxy process");
                goto err;
	}

	/* Fork done, close off appropriate sockets and start services */
	if (pid != 0)
	{
		printf("server initializing ...\n");
		close(socks[1]);
		server(socks[0]);
	}
	else
	{
		printf("proxy initializing ...\n");
		close(socks[0]);
		proxy(socks[1]);
	}
        return 0;
err:
        exit(EXIT_FAILURE);

}
