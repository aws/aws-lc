# 1 "/Users/milaaws/Desktop/official_AWS-LC-SHA3/aws-lc/third_party/s2n-bignum/arm/p521/bignum_add_p521.S"
# 1 "<built-in>" 1
# 1 "/Users/milaaws/Desktop/official_AWS-LC-SHA3/aws-lc/third_party/s2n-bignum/arm/p521/bignum_add_p521.S" 2
# 26 "/Users/milaaws/Desktop/official_AWS-LC-SHA3/aws-lc/third_party/s2n-bignum/arm/p521/bignum_add_p521.S"
        .globl bignum_add_p521
        .globl _bignum_add_p521
        .text
        .balign 4
# 47 "/Users/milaaws/Desktop/official_AWS-LC-SHA3/aws-lc/third_party/s2n-bignum/arm/p521/bignum_add_p521.S"
bignum_add_p521:
_bignum_add_p521:




        subs xzr, xzr, xzr
        ldp x5, x6, [x1]
        ldp x4, x3, [x2]
        adcs x5, x5, x4
        adcs x6, x6, x3
        ldp x7, x8, [x1, #16]
        ldp x4, x3, [x2, #16]
        adcs x7, x7, x4
        adcs x8, x8, x3
        ldp x9, x10, [x1, #32]
        ldp x4, x3, [x2, #32]
        adcs x9, x9, x4
        adcs x10, x10, x3
        ldp x11, x12, [x1, #48]
        ldp x4, x3, [x2, #48]
        adcs x11, x11, x4
        adcs x12, x12, x3
        ldr x13, [x1, #64]
        ldr x4, [x2, #64]
        adc x13, x13, x4




        subs x4, x13, #512
        csetm x4, cs




        sbcs x5, x5, xzr
        and x4, x4, #512
        sbcs x6, x6, xzr
        sbcs x7, x7, xzr
        sbcs x8, x8, xzr
        sbcs x9, x9, xzr
        sbcs x10, x10, xzr
        sbcs x11, x11, xzr
        sbcs x12, x12, xzr
        sbc x13, x13, x4



        stp x5, x6, [x0]
        stp x7, x8, [x0, #16]
        stp x9, x10, [x0, #32]
        stp x11, x12, [x0, #48]
        str x13, [x0, #64]

        ret
