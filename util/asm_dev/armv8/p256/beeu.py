# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

# Binary Extended GCD (Euclidean) Algorithm
# Inputs and outputs are 256-bit values.
# computes
#    |out| = |a|^-1 mod n,
# where n is odd
# See A. Menezes, P. vanOorschot, and S. Vanstone's Handbook of Applied Cryptography,
# Chapter 14, Algorithm 14.61 and Note 14.64
# http://cacr.uwaterloo.ca/hac/about/chap14.pdf

# Details:
# In Alg 14.61, let x and y be co-prime, this means that they have no common factor. Specifically,
#    v = gcd(x,y) = 1 = ax + by
# If we would like to calculate the inverse of x modulo y, we can use Alg. 14.61,
# where a would be that inverse. In other words,
#    ax == 1 (mod y) (where the symbol “==“ denotes ”congruent“)
# =>  a == x^{-1} (mod y)
# It can be shown that throughout all the iterations of the algorithm, the following holds:
#    u = Ax + By
#    v = Cx + Dy
# We are not interested in the values of B and D in this case,
# so they need not be computed by the algorithm.
# This means the following congruences hold through the iterations of the algorithm.
#    Ax == u (mod y)
#    Cx == v (mod y)

# Now we will modify the notation to match that of
# BN_mod_inverse_odd (http://ec2-34-223-251-4.us-west-2.compute.amazonaws.com/source/xref/boringssl/crypto/fipsmodule/bn/gcd.c?r=bb3a4569#116)
# on which beeu_mod_inverse_vartime (http://ec2-34-223-251-4.us-west-2.compute.amazonaws.com/source/xref/boringssl/crypto/fipsmodule/ec/asm/p256_beeu-x86_64-asm.pl?r=c1d8c5b0#35)
# is based. In those functions:
#    x, y -> a, n
#    u, v -> B, A
#    A, C -> X, Y’, where Y’ = -Y
# Hence, the following holds
#     Xa == B (mod n)
#    -Ya == A (mod n)

def beeu(a, n):
    X = 1
    Y = 0
    B = a
    A = n
    while (B != 0):
        while (B % 2) == 0:
            B >>= 1
            if (X % 2) == 1:
                X = X + n
            X >>= 1
        while (A % 2) == 0:
            A >>= 1
            if (Y % 2) == 1:
                Y = Y + n
            Y >>= 1
        if (B >= A):
            B = B - A
            X = X + Y
        else:
            A = A - B
            Y = Y + X
    if (A != 1):
        # error
        return 0
    else:
        while (Y > n):
            Y = Y - n
        Y = n - Y
        return Y

def test_beeu():
    a = 0x2
    n = 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551
    out_exp = 0x7fffffff800000007fffffffffffffffde737d56d38bcf4279dce5617e3192a9
    out = beeu(a,n)
    print(hex(out))
    assert beeu(a,n) == out_exp

test_beeu()
