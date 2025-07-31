// The C files need to be included in fips_hashing.c rather than compiled separately through CMake because it maintains a 
// shared context for all files and preserves dependencies between them like bcm.c.

#include "../fipsmodule/delocate.h"


#include "../fipsmodule/digest/digest.c"
#include "../fipsmodule/digest/digests.c"
#include "../fipsmodule/hmac/hmac.c"
#include "../fipsmodule/md4/md4.c"
#include "../fipsmodule/md5/md5.c"
#include "../fipsmodule/sha/keccak1600.c"
#include "../fipsmodule/sha/sha1.c"
#include "../fipsmodule/sha/sha256.c"
#include "../fipsmodule/sha/sha3.c"
#include "../fipsmodule/sha/sha512.c"
