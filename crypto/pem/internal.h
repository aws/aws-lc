#include <openssl/pem.h>

#define MIN_LENGTH 4

#if defined(__cplusplus)
extern "C" {
#endif

// PEM utility functions
// PEM_proc_type appends a Proc-Type header to |buf|, determined by |type|.
void PEM_proc_type(char buf[PEM_BUFSIZE], int type);

// PEM_dek_info appends a DEK-Info header to |buf|, with an algorithm of |type|
// and a single parameter, specified by hex-encoding |len| bytes from |str|.
void PEM_dek_info(char buf[PEM_BUFSIZE], const char *type, size_t len,
                  char *str);

// Console Management Functions
OPENSSL_EXPORT int openssl_console_open(void);
OPENSSL_EXPORT int openssl_console_close(void);
OPENSSL_EXPORT int openssl_console_write(const char *str);
OPENSSL_EXPORT int openssl_console_read(char *buf, int minsize, int maxsize, int echo);


#if defined(__cplusplus)
}  // extern C
#endif
