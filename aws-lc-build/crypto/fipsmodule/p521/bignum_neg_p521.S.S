# 1 "/Users/milaaws/Desktop/official_AWS-LC-SHA3/aws-lc/third_party/s2n-bignum/arm/p521/bignum_neg_p521.S"
# 1 "<built-in>" 1
# 1 "/Users/milaaws/Desktop/official_AWS-LC-SHA3/aws-lc/third_party/s2n-bignum/arm/p521/bignum_neg_p521.S" 2
# 25 "/Users/milaaws/Desktop/official_AWS-LC-SHA3/aws-lc/third_party/s2n-bignum/arm/p521/bignum_neg_p521.S"
        .globl bignum_neg_p521
        .globl _bignum_neg_p521
        .text
        .balign 4
# 45 "/Users/milaaws/Desktop/official_AWS-LC-SHA3/aws-lc/third_party/s2n-bignum/arm/p521/bignum_neg_p521.S"
bignum_neg_p521:
_bignum_neg_p521:



        ldp x3, x4, [x1]
        orr x9, x3, x4
        ldp x5, x6, [x1, #16]
        orr x10, x5, x6
        orr x2, x9, x10
        ldp x7, x8, [x1, #32]
        orr x11, x7, x8
        orr x2, x2, x11
        ldp x9, x10, [x1, #48]
        orr x11, x9, x10
        orr x2, x2, x11
        ldr x11, [x1, #64]
        orr x2, x2, x11




        cmp x2, #0
        csetm x2, ne




        eor x3, x3, x2
        eor x4, x4, x2
        eor x5, x5, x2
        eor x6, x6, x2
        eor x7, x7, x2
        eor x8, x8, x2
        eor x9, x9, x2
        eor x10, x10, x2
        and x2, x2, #0x1FF
        eor x11, x11, x2



        stp x3, x4, [x0]
        stp x5, x6, [x0, #16]
        stp x7, x8, [x0, #32]
        stp x9, x10, [x0, #48]
        str x11, [x0, #64]
        ret
