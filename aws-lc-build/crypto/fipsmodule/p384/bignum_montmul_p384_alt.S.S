# 1 "/Users/milaaws/Desktop/official_AWS-LC-SHA3/aws-lc/third_party/s2n-bignum/arm/p384/bignum_montmul_p384_alt.S"
# 1 "<built-in>" 1
# 1 "/Users/milaaws/Desktop/official_AWS-LC-SHA3/aws-lc/third_party/s2n-bignum/arm/p384/bignum_montmul_p384_alt.S" 2
# 30 "/Users/milaaws/Desktop/official_AWS-LC-SHA3/aws-lc/third_party/s2n-bignum/arm/p384/bignum_montmul_p384_alt.S"
        .globl bignum_montmul_p384_alt
        .globl _bignum_montmul_p384_alt
        .text
        .balign 4
# 105 "/Users/milaaws/Desktop/official_AWS-LC-SHA3/aws-lc/third_party/s2n-bignum/arm/p384/bignum_montmul_p384_alt.S"
bignum_montmul_p384_alt:
_bignum_montmul_p384_alt:



        stp x19, x20, [sp, #-16]!
        stp x21, x22, [sp, #-16]!



        ldp x3, x4, [x1]
        ldp x5, x6, [x2]

        mul x12, x3, x5
        umulh x13, x3, x5
        mul x11, x3, x6
        umulh x14, x3, x6
        adds x13, x13, x11

        ldp x7, x8, [x2, #16]

        mul x11, x3, x7
        umulh x15, x3, x7
        adcs x14, x14, x11

        mul x11, x3, x8
        umulh x16, x3, x8
        adcs x15, x15, x11

        ldp x9, x10, [x2, #32]

        mul x11, x3, x9
        umulh x17, x3, x9
        adcs x16, x16, x11

        mul x11, x3, x10
        umulh x19, x3, x10
        adcs x17, x17, x11

        adc x19, x19, xzr



        mul x11, x4, x5
        adds x13, x13, x11
        mul x11, x4, x6
        adcs x14, x14, x11
        mul x11, x4, x7
        adcs x15, x15, x11
        mul x11, x4, x8
        adcs x16, x16, x11
        mul x11, x4, x9
        adcs x17, x17, x11
        mul x11, x4, x10
        adcs x19, x19, x11
        cset x20, cs

        umulh x11, x4, x5
        adds x14, x14, x11
        umulh x11, x4, x6
        adcs x15, x15, x11
        umulh x11, x4, x7
        adcs x16, x16, x11
        umulh x11, x4, x8
        adcs x17, x17, x11
        umulh x11, x4, x9
        adcs x19, x19, x11
        umulh x11, x4, x10
        adc x20, x20, x11



        ldp x3, x4, [x1, #16]

        mul x11, x3, x5
        adds x14, x14, x11
        mul x11, x3, x6
        adcs x15, x15, x11
        mul x11, x3, x7
        adcs x16, x16, x11
        mul x11, x3, x8
        adcs x17, x17, x11
        mul x11, x3, x9
        adcs x19, x19, x11
        mul x11, x3, x10
        adcs x20, x20, x11
        cset x21, cs

        umulh x11, x3, x5
        adds x15, x15, x11
        umulh x11, x3, x6
        adcs x16, x16, x11
        umulh x11, x3, x7
        adcs x17, x17, x11
        umulh x11, x3, x8
        adcs x19, x19, x11
        umulh x11, x3, x9
        adcs x20, x20, x11
        umulh x11, x3, x10
        adc x21, x21, x11



        mul x11, x4, x5
        adds x15, x15, x11
        mul x11, x4, x6
        adcs x16, x16, x11
        mul x11, x4, x7
        adcs x17, x17, x11
        mul x11, x4, x8
        adcs x19, x19, x11
        mul x11, x4, x9
        adcs x20, x20, x11
        mul x11, x4, x10
        adcs x21, x21, x11
        cset x22, cs

        umulh x11, x4, x5
        adds x16, x16, x11
        umulh x11, x4, x6
        adcs x17, x17, x11
        umulh x11, x4, x7
        adcs x19, x19, x11
        umulh x11, x4, x8
        adcs x20, x20, x11
        umulh x11, x4, x9
        adcs x21, x21, x11
        umulh x11, x4, x10
        adc x22, x22, x11



        ldp x3, x4, [x1, #32]

        mul x11, x3, x5
        adds x16, x16, x11
        mul x11, x3, x6
        adcs x17, x17, x11
        mul x11, x3, x7
        adcs x19, x19, x11
        mul x11, x3, x8
        adcs x20, x20, x11
        mul x11, x3, x9
        adcs x21, x21, x11
        mul x11, x3, x10
        adcs x22, x22, x11
        cset x2, cs

        umulh x11, x3, x5
        adds x17, x17, x11
        umulh x11, x3, x6
        adcs x19, x19, x11
        umulh x11, x3, x7
        adcs x20, x20, x11
        umulh x11, x3, x8
        adcs x21, x21, x11
        umulh x11, x3, x9
        adcs x22, x22, x11
        umulh x11, x3, x10
        adc x2, x2, x11



        mul x11, x4, x5
        adds x17, x17, x11
        mul x11, x4, x6
        adcs x19, x19, x11
        mul x11, x4, x7
        adcs x20, x20, x11
        mul x11, x4, x8
        adcs x21, x21, x11
        mul x11, x4, x9
        adcs x22, x22, x11
        mul x11, x4, x10
        adcs x2, x2, x11
        cset x1, cs

        umulh x11, x4, x5
        adds x19, x19, x11
        umulh x11, x4, x6
        adcs x20, x20, x11
        umulh x11, x4, x7
        adcs x21, x21, x11
        umulh x11, x4, x8
        adcs x22, x22, x11
        umulh x11, x4, x9
        adcs x2, x2, x11
        umulh x11, x4, x10
        adc x1, x1, x11



        lsl x7, x12, #32
 add x12, x7, x12
 mov x7, #0xffffffff00000001
 umulh x7, x7, x12
 mov x6, #0x00000000ffffffff
 mul x5, x6, x12
 umulh x6, x6, x12
 adds x7, x7, x5
 adcs x6, x6, x12
 adc x5, xzr, xzr
 subs x13, x13, x7
 sbcs x14, x14, x6
 sbcs x15, x15, x5
 sbcs x16, x16, xzr
 sbcs x17, x17, xzr
 sbc x12, x12, xzr
        lsl x7, x13, #32
 add x13, x7, x13
 mov x7, #0xffffffff00000001
 umulh x7, x7, x13
 mov x6, #0x00000000ffffffff
 mul x5, x6, x13
 umulh x6, x6, x13
 adds x7, x7, x5
 adcs x6, x6, x13
 adc x5, xzr, xzr
 subs x14, x14, x7
 sbcs x15, x15, x6
 sbcs x16, x16, x5
 sbcs x17, x17, xzr
 sbcs x12, x12, xzr
 sbc x13, x13, xzr
        lsl x7, x14, #32
 add x14, x7, x14
 mov x7, #0xffffffff00000001
 umulh x7, x7, x14
 mov x6, #0x00000000ffffffff
 mul x5, x6, x14
 umulh x6, x6, x14
 adds x7, x7, x5
 adcs x6, x6, x14
 adc x5, xzr, xzr
 subs x15, x15, x7
 sbcs x16, x16, x6
 sbcs x17, x17, x5
 sbcs x12, x12, xzr
 sbcs x13, x13, xzr
 sbc x14, x14, xzr
        lsl x7, x15, #32
 add x15, x7, x15
 mov x7, #0xffffffff00000001
 umulh x7, x7, x15
 mov x6, #0x00000000ffffffff
 mul x5, x6, x15
 umulh x6, x6, x15
 adds x7, x7, x5
 adcs x6, x6, x15
 adc x5, xzr, xzr
 subs x16, x16, x7
 sbcs x17, x17, x6
 sbcs x12, x12, x5
 sbcs x13, x13, xzr
 sbcs x14, x14, xzr
 sbc x15, x15, xzr
        lsl x7, x16, #32
 add x16, x7, x16
 mov x7, #0xffffffff00000001
 umulh x7, x7, x16
 mov x6, #0x00000000ffffffff
 mul x5, x6, x16
 umulh x6, x6, x16
 adds x7, x7, x5
 adcs x6, x6, x16
 adc x5, xzr, xzr
 subs x17, x17, x7
 sbcs x12, x12, x6
 sbcs x13, x13, x5
 sbcs x14, x14, xzr
 sbcs x15, x15, xzr
 sbc x16, x16, xzr
        lsl x7, x17, #32
 add x17, x7, x17
 mov x7, #0xffffffff00000001
 umulh x7, x7, x17
 mov x6, #0x00000000ffffffff
 mul x5, x6, x17
 umulh x6, x6, x17
 adds x7, x7, x5
 adcs x6, x6, x17
 adc x5, xzr, xzr
 subs x12, x12, x7
 sbcs x13, x13, x6
 sbcs x14, x14, x5
 sbcs x15, x15, xzr
 sbcs x16, x16, xzr
 sbc x17, x17, xzr



        adds x12, x12, x19
        adcs x13, x13, x20
        adcs x14, x14, x21
        adcs x15, x15, x22
        adcs x16, x16, x2
        adcs x17, x17, x1
        adc x10, xzr, xzr



        mov x11, #0xffffffff00000001
        adds x19, x12, x11
        mov x11, #0x00000000ffffffff
        adcs x20, x13, x11
        mov x11, #0x0000000000000001
        adcs x21, x14, x11
        adcs x22, x15, xzr
        adcs x2, x16, xzr
        adcs x1, x17, xzr
        adcs x10, x10, xzr



        csel x12, x12, x19, eq
        csel x13, x13, x20, eq
        csel x14, x14, x21, eq
        csel x15, x15, x22, eq
        csel x16, x16, x2, eq
        csel x17, x17, x1, eq



        stp x12, x13, [x0]
        stp x14, x15, [x0, #16]
        stp x16, x17, [x0, #32]



        ldp x21, x22, [sp], #16
        ldp x19, x20, [sp], #16

        ret
