#ifndef SYMMETRIC_H
#define SYMMETRIC_H

#include <stdint.h>
#include "params.h"
#include "../../fipsmodule/sha/internal.h"

typedef KECCAK1600_CTX stream128_state;
typedef KECCAK1600_CTX stream256_state;

#define STREAM128_BLOCKBYTES SHAKE128_RATE
#define STREAM256_BLOCKBYTES SHAKE256_RATE

#endif
