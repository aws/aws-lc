# 1 "/Users/milaaws/Desktop/official_AWS-LC-SHA3/aws-lc/third_party/s2n-bignum/arm/p384/bignum_montsqr_p384_alt.S"
# 1 "<built-in>" 1
# 1 "/Users/milaaws/Desktop/official_AWS-LC-SHA3/aws-lc/third_party/s2n-bignum/arm/p384/bignum_montsqr_p384_alt.S" 2
# 29 "/Users/milaaws/Desktop/official_AWS-LC-SHA3/aws-lc/third_party/s2n-bignum/arm/p384/bignum_montsqr_p384_alt.S"
        .globl bignum_montsqr_p384_alt
        .globl _bignum_montsqr_p384_alt
        .text
        .balign 4
# 93 "/Users/milaaws/Desktop/official_AWS-LC-SHA3/aws-lc/third_party/s2n-bignum/arm/p384/bignum_montsqr_p384_alt.S"
bignum_montsqr_p384_alt:
_bignum_montsqr_p384_alt:



        stp x19, x20, [sp, #-16]!






        ldp x2, x3, [x1]

        mul x9, x2, x3
        umulh x10, x2, x3

        ldp x4, x5, [x1, #16]

        mul x8, x2, x4
        adds x10, x10, x8

        mul x11, x2, x5
        mul x8, x3, x4
        adcs x11, x11, x8

        umulh x12, x2, x5
        mul x8, x3, x5
        adcs x12, x12, x8

        ldp x6, x7, [x1, #32]

        mul x13, x2, x7
        mul x8, x3, x6
        adcs x13, x13, x8

        umulh x14, x2, x7
        mul x8, x3, x7
        adcs x14, x14, x8

        mul x15, x5, x6
        adcs x15, x15, xzr

        umulh x16, x5, x6
        adc x16, x16, xzr

        umulh x8, x2, x4
        adds x11, x11, x8
        umulh x8, x3, x4
        adcs x12, x12, x8
        umulh x8, x3, x5
        adcs x13, x13, x8
        umulh x8, x3, x6
        adcs x14, x14, x8
        umulh x8, x3, x7
        adcs x15, x15, x8
        adc x16, x16, xzr



        mul x8, x2, x6
        adds x12, x12, x8
        mul x8, x4, x5
        adcs x13, x13, x8
        mul x8, x4, x6
        adcs x14, x14, x8
        mul x8, x4, x7
        adcs x15, x15, x8
        mul x8, x5, x7
        adcs x16, x16, x8
        mul x17, x6, x7
        adcs x17, x17, xzr
        umulh x19, x6, x7
        adc x19, x19, xzr

        umulh x8, x2, x6
        adds x13, x13, x8
        umulh x8, x4, x5
        adcs x14, x14, x8
        umulh x8, x4, x6
        adcs x15, x15, x8
        umulh x8, x4, x7
        adcs x16, x16, x8
        umulh x8, x5, x7
        adcs x17, x17, x8
        adc x19, x19, xzr



        adds x9, x9, x9
        adcs x10, x10, x10
        adcs x11, x11, x11
        adcs x12, x12, x12
        adcs x13, x13, x13
        adcs x14, x14, x14
        adcs x15, x15, x15
        adcs x16, x16, x16
        adcs x17, x17, x17
        adcs x19, x19, x19
        cset x20, cs



        umulh x8, x2, x2
        mul x2, x2, x2
        adds x9, x9, x8

        mul x8, x3, x3
        adcs x10, x10, x8
        umulh x8, x3, x3
        adcs x11, x11, x8

        mul x8, x4, x4
        adcs x12, x12, x8
        umulh x8, x4, x4
        adcs x13, x13, x8

        mul x8, x5, x5
        adcs x14, x14, x8
        umulh x8, x5, x5
        adcs x15, x15, x8

        mul x8, x6, x6
        adcs x16, x16, x8
        umulh x8, x6, x6
        adcs x17, x17, x8

        mul x8, x7, x7
        adcs x19, x19, x8
        umulh x8, x7, x7
        adc x20, x20, x8



        lsl x5, x2, #32
 add x2, x5, x2
 mov x5, #0xffffffff00000001
 umulh x5, x5, x2
 mov x4, #0x00000000ffffffff
 mul x3, x4, x2
 umulh x4, x4, x2
 adds x5, x5, x3
 adcs x4, x4, x2
 adc x3, xzr, xzr
 subs x9, x9, x5
 sbcs x10, x10, x4
 sbcs x11, x11, x3
 sbcs x12, x12, xzr
 sbcs x13, x13, xzr
 sbc x2, x2, xzr
        lsl x5, x9, #32
 add x9, x5, x9
 mov x5, #0xffffffff00000001
 umulh x5, x5, x9
 mov x4, #0x00000000ffffffff
 mul x3, x4, x9
 umulh x4, x4, x9
 adds x5, x5, x3
 adcs x4, x4, x9
 adc x3, xzr, xzr
 subs x10, x10, x5
 sbcs x11, x11, x4
 sbcs x12, x12, x3
 sbcs x13, x13, xzr
 sbcs x2, x2, xzr
 sbc x9, x9, xzr
        lsl x5, x10, #32
 add x10, x5, x10
 mov x5, #0xffffffff00000001
 umulh x5, x5, x10
 mov x4, #0x00000000ffffffff
 mul x3, x4, x10
 umulh x4, x4, x10
 adds x5, x5, x3
 adcs x4, x4, x10
 adc x3, xzr, xzr
 subs x11, x11, x5
 sbcs x12, x12, x4
 sbcs x13, x13, x3
 sbcs x2, x2, xzr
 sbcs x9, x9, xzr
 sbc x10, x10, xzr
        lsl x5, x11, #32
 add x11, x5, x11
 mov x5, #0xffffffff00000001
 umulh x5, x5, x11
 mov x4, #0x00000000ffffffff
 mul x3, x4, x11
 umulh x4, x4, x11
 adds x5, x5, x3
 adcs x4, x4, x11
 adc x3, xzr, xzr
 subs x12, x12, x5
 sbcs x13, x13, x4
 sbcs x2, x2, x3
 sbcs x9, x9, xzr
 sbcs x10, x10, xzr
 sbc x11, x11, xzr
        lsl x5, x12, #32
 add x12, x5, x12
 mov x5, #0xffffffff00000001
 umulh x5, x5, x12
 mov x4, #0x00000000ffffffff
 mul x3, x4, x12
 umulh x4, x4, x12
 adds x5, x5, x3
 adcs x4, x4, x12
 adc x3, xzr, xzr
 subs x13, x13, x5
 sbcs x2, x2, x4
 sbcs x9, x9, x3
 sbcs x10, x10, xzr
 sbcs x11, x11, xzr
 sbc x12, x12, xzr
        lsl x5, x13, #32
 add x13, x5, x13
 mov x5, #0xffffffff00000001
 umulh x5, x5, x13
 mov x4, #0x00000000ffffffff
 mul x3, x4, x13
 umulh x4, x4, x13
 adds x5, x5, x3
 adcs x4, x4, x13
 adc x3, xzr, xzr
 subs x2, x2, x5
 sbcs x9, x9, x4
 sbcs x10, x10, x3
 sbcs x11, x11, xzr
 sbcs x12, x12, xzr
 sbc x13, x13, xzr



        adds x2, x2, x14
        adcs x9, x9, x15
        adcs x10, x10, x16
        adcs x11, x11, x17
        adcs x12, x12, x19
        adcs x13, x13, x20
        adc x6, xzr, xzr



        mov x8, #0xffffffff00000001
        adds x14, x2, x8
        mov x8, #0x00000000ffffffff
        adcs x15, x9, x8
        mov x8, #0x0000000000000001
        adcs x16, x10, x8
        adcs x17, x11, xzr
        adcs x19, x12, xzr
        adcs x20, x13, xzr
        adcs x6, x6, xzr



        csel x2, x2, x14, eq
        csel x9, x9, x15, eq
        csel x10, x10, x16, eq
        csel x11, x11, x17, eq
        csel x12, x12, x19, eq
        csel x13, x13, x20, eq



        stp x2, x9, [x0]
        stp x10, x11, [x0, #16]
        stp x12, x13, [x0, #32]



        ldp x19, x20, [sp], #16

        ret
