#ifndef RANDOMBYTES_H
#define RANDOMBYTES_H

#include "openssl/rand.h"

inline int randombytes(unsigned char* random_array, unsigned long long nbytes)
{
  return RAND_bytes(random_array, nbytes);
}

#endif
