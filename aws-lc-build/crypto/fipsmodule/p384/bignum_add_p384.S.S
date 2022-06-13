# 1 "/Users/milaaws/Desktop/official_AWS-LC-SHA3/aws-lc/third_party/s2n-bignum/arm/p384/bignum_add_p384.S"
# 1 "<built-in>" 1
# 1 "/Users/milaaws/Desktop/official_AWS-LC-SHA3/aws-lc/third_party/s2n-bignum/arm/p384/bignum_add_p384.S" 2
# 26 "/Users/milaaws/Desktop/official_AWS-LC-SHA3/aws-lc/third_party/s2n-bignum/arm/p384/bignum_add_p384.S"
        .globl bignum_add_p384
        .globl _bignum_add_p384
        .text
        .balign 4
# 44 "/Users/milaaws/Desktop/official_AWS-LC-SHA3/aws-lc/third_party/s2n-bignum/arm/p384/bignum_add_p384.S"
bignum_add_p384:
_bignum_add_p384:



        ldp x5, x6, [x1]
        ldp x4, x3, [x2]
        adds x5, x5, x4
        adcs x6, x6, x3
        ldp x7, x8, [x1, #16]
        ldp x4, x3, [x2, #16]
        adcs x7, x7, x4
        adcs x8, x8, x3
        ldp x9, x10, [x1, #32]
        ldp x4, x3, [x2, #32]
        adcs x9, x9, x4
        adcs x10, x10, x3
        adc x3, xzr, xzr



        mov x4, #0x00000000ffffffff
        subs xzr, x5, x4
        mov x4, #0xffffffff00000000
        sbcs xzr, x6, x4
        mov x4, #0xfffffffffffffffe
        sbcs xzr, x7, x4
        adcs xzr, x8, xzr
        adcs xzr, x9, xzr
        adcs xzr, x10, xzr




        adcs x3, x3, xzr
        csetm x3, ne



        mov x4, #0x00000000ffffffff
        and x4, x4, x3
        subs x5, x5, x4
        eor x4, x4, x3
        sbcs x6, x6, x4
        mov x4, #0xfffffffffffffffe
        and x4, x4, x3
        sbcs x7, x7, x4
        sbcs x8, x8, x3
        sbcs x9, x9, x3
        sbc x10, x10, x3



        stp x5, x6, [x0]
        stp x7, x8, [x0, #16]
        stp x9, x10, [x0, #32]

        ret
