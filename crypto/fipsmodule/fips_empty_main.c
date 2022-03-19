#include <stdio.h>
#include <stdlib.h>

#include <openssl/crypto.h>

int main(int argc, char *argv[]) {
  fprintf(stderr, "This should never print!\n");
  // To ensure the linker links libcrypto call something
  fprintf(stderr, "FIPS mode is %d\n", FIPS_mode());

  exit(1);
}

