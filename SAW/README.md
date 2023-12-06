# AWS libcrypto Verification using SAW
Proofs in this directory are carried out in [SAW](https://saw.galois.com/) using [Cryptol](https://cryptol.net/) specifications stored in the [Galois Cryptol spec repository](https://github.com/GaloisInc/cryptol-specs). The SAW proofs cover the verification of C and X86_64 assembly programs.

## Safety Guarantee in SAW proofs

* The function does not write to or read from memory outside of the allocated space pointed to by its parameters. Though an exception to this rule exists in cases where a function frees memory. In these cases, the verification would not fail if the function writes to memory after it is freed.
* The function does not write to memory within the allocated space pointed to by parameters that are intended to be read only.
* The function does not read from memory that has not been initialized with a value.
* If the function is written in C, then it is free from all other undefined behavior.
