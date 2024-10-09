#include <openssl/bio.h>
#include <openssl/crypto.h>
#include <openssl/pem.h>
#include <openssl/pkcs7.h>
#include <openssl/stack.h>
#include <openssl/x509.h>

// run with gcc test.c -g3 -l:libcrypto.a -L/usr/lib/x86_64-linux-gnu/ -o test && gdb ./test

int main(int *argc, char **argv) {
    PKCS7 *p7 = PKCS7_new();
    BIO *bio = BIO_new(BIO_s_mem());

    PKCS7_set_type(p7, NID_pkcs7_digest);
    PKCS7_set_digest(p7, EVP_sha256());

    BIO_set_md(bio, EVP_sha256());
    BIO *chain = PKCS7_dataInit(p7, bio);
    printf("INIT:  %p\n", chain);
    BIO_set_md(chain, EVP_sha256());
    int ret = PKCS7_dataFinal(p7, chain);
    printf("FINAL: %d\n", ret);

    return 0;
}
