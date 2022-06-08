# 1 "/Users/milaaws/Desktop/official_AWS-LC-SHA3/aws-lc/third_party/s2n-bignum/arm/p384/bignum_nonzero_6.S"
# 1 "<built-in>" 1
# 1 "/Users/milaaws/Desktop/official_AWS-LC-SHA3/aws-lc/third_party/s2n-bignum/arm/p384/bignum_nonzero_6.S" 2
# 25 "/Users/milaaws/Desktop/official_AWS-LC-SHA3/aws-lc/third_party/s2n-bignum/arm/p384/bignum_nonzero_6.S"
        .globl bignum_nonzero_6
        .globl _bignum_nonzero_6
        .text
        .balign 4







bignum_nonzero_6:
_bignum_nonzero_6:



        ldp x1, x2, [x0]
        orr x1, x1, x2
        ldp x3, x2, [x0, #16]
        orr x3, x3, x2
        orr x1, x1, x3
        ldp x3, x2, [x0, #32]
        orr x3, x3, x2
        orr x1, x1, x3



        cmp x1, xzr
        cset x0, ne

        ret
