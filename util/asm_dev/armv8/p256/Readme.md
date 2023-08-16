Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.<br />
SPDX-License-Identifier: Apache-2.0 OR ISC

#P256 Armv8 Assembly Functions
This application was used to develop the assembly functions committed to
[awsls:p256-armv8](https://github.com/aws/aws-lc/tree/p256-armv8)

The goal is bringing the P-256 performance on ARMv8 at par with x86_64.
The ARMv8 assembly code is taken from OpenSSL 1.1.1 (at [this commit](openssl/openssl@46a9ee8)).
The goal is achieved by reusing the AWS-LC P-256 implementation in `p256-x86_64.c` (nistz256) with ARMv8.
This is possible because the assembly functions required to support that code have their analogous functions in
the imported OpenSSL.
(Namely, the file [openss/crypto/ec/asm/ecp_nistz256-armv8.pl](https://github.com/openssl/openssl/blob/46a9ee8c796c8b5f8d95290676119b4f3d72be91/crypto/ec/asm/ecp_nistz256-armv8.pl)
was imported with slight modification in the first 2 commits.)
However, there are 3 x86_64 assembly functions that do not have corresponding functions in that file.
Those functions are `ecp_nistz256_select_w5` and `ecp_nistz256_select_w7` and `beeu_mod_inverse_vartime`.

###`ecp_nistz256_select_w5`
This function performs a constant-time table lookup by reading all entries, one at a time,
and using a mask based on the index to keep only the desired entry in the result destination.
* There are 16 entries in the table
* Each entry consists of 3 256-bit values which are the projective coordinates of a point
on the P-256 curve.
* The index is in the range [1,16].

###`ecp_nistz256_select_w7`
This function is almost identical to `ecp_nistz256_select_w5`. The differences are:
* There are 64 entries in the table
* Each entry consists of 2 256-bit values which are the affine coordinates of a point
on the P-256 curve.
* The index is in the range [1,64].

### `beeu_mod_inverse_vartime`
This function is an implementation of the Binary Extended GCD (Euclidean) Algorithm,
for a reference, see A. Menezes, P. vanOorschot, and S. Vanstone's Handbook of Applied Cryptography,
 Chapter 14, Algorithm 14.61 and Note 14.64
 http://cacr.uwaterloo.ca/hac/about/chap14.pdf

 The python model for this function is in `beeu.py`.
 It is used to compute the modular inverse of a value |a| modulo n, where n is odd.
 
 ## Tests
 The tests for the three described functions are performed in `main.c`
 
 ## Additional code
 The code in `beeu_scratch.c` is not directly used in the implementation; it was used
 to compile into ARMv8 assembly and experiment with the generated instructions for `beeu.S`. <br/>
 The Makefile, as inspired by [ARM SVE examples](https://developer.arm.com/documentation/dai0548/a/),
 when building, creates the assembly files from the C files, so it is easy to see the assembly
 instructions equivalent to the functions in this file.