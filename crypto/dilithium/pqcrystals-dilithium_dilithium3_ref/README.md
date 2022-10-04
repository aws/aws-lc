This code in this directory was taken from the primary source of Dilithium in the public GitHub repository at https://github.com/pq-crystals/dilithium commit https://github.com/pq-crystals/dilithium/commit/3e9b9f1412f6c7435dbeb4e10692ea58f181ee51 as of 9th May 2022. It was introduced to AWS-LC on 23rd September 2022.

The following changes were made to the code:
- Line 329 of sign.c was modified from `*mlen = -1;` to `*mlen = 0;` within the `crypto_sign_open` function. This was modified as `*mlen = -1;` is attempting to assign `-1` to an unsigned integer, giving the warning: ` warning C4245: '=': conversion from 'int' to 'std::size_t'`. This warning would cause Windows x86 builds to fail.  https://github.com/pq-crystals/dilithium/blob/master/ref/sign.c#L329
- Line 11 of config.h was modified from `#define DILITHIUM_MODE 2` to `#define DILITHIUM_MODE 3`, as we have selected to use the Dilithium3 parameter set to meet the 128-bit security bar. https://github.com/pq-crystals/dilithium/blob/master/ref/config.h#L11
 
