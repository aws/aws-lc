# 1 "/Users/milaaws/Desktop/official_AWS-LC-SHA3/aws-lc/third_party/s2n-bignum/arm/p521/bignum_sqr_p521_alt.S"
# 1 "<built-in>" 1
# 1 "/Users/milaaws/Desktop/official_AWS-LC-SHA3/aws-lc/third_party/s2n-bignum/arm/p521/bignum_sqr_p521_alt.S" 2
# 25 "/Users/milaaws/Desktop/official_AWS-LC-SHA3/aws-lc/third_party/s2n-bignum/arm/p521/bignum_sqr_p521_alt.S"
        .globl bignum_sqr_p521_alt
        .globl _bignum_sqr_p521_alt
        .text
        .balign 4
# 63 "/Users/milaaws/Desktop/official_AWS-LC-SHA3/aws-lc/third_party/s2n-bignum/arm/p521/bignum_sqr_p521_alt.S"
bignum_sqr_p521_alt:
_bignum_sqr_p521_alt:



        stp x19, x20, [sp, #-16]!
        stp x21, x22, [sp, #-16]!
        stp x23, x24, [sp, #-16]!
        stp x25, x26, [sp, #-16]!
        stp x27, x29, [sp, #-16]!




        ldp x2, x3, [x1]

        mul x12, x2, x3
        umulh x13, x2, x3

        ldp x4, x5, [x1, #16]

        mul x10, x2, x4
        umulh x14, x2, x4
        adds x13, x13, x10

        ldp x6, x7, [x1, #32]

        mul x10, x2, x5
        umulh x15, x2, x5
        adcs x14, x14, x10

        ldp x8, x9, [x1, #48]

        mul x10, x2, x6
        umulh x16, x2, x6
        adcs x15, x15, x10

        mul x10, x2, x7
        umulh x17, x2, x7
        adcs x16, x16, x10

        mul x10, x2, x8
        umulh x19, x2, x8
        adcs x17, x17, x10

        mul x10, x2, x9
        umulh x20, x2, x9
        adcs x19, x19, x10

        adc x20, x20, xzr



        mul x10, x3, x4
        adds x14, x14, x10
        mul x10, x3, x5
        adcs x15, x15, x10
        mul x10, x3, x6
        adcs x16, x16, x10
        mul x10, x3, x7
        adcs x17, x17, x10
        mul x10, x3, x8
        adcs x19, x19, x10
        mul x10, x3, x9
        adcs x20, x20, x10
        cset x21, cs

        umulh x10, x3, x4
        adds x15, x15, x10
        umulh x10, x3, x5
        adcs x16, x16, x10
        umulh x10, x3, x6
        adcs x17, x17, x10
        umulh x10, x3, x7
        adcs x19, x19, x10
        umulh x10, x3, x8
        adcs x20, x20, x10
        umulh x10, x3, x9
        adc x21, x21, x10
        mul x10, x6, x7
        umulh x22, x6, x7
        adds x21, x21, x10
        adc x22, x22, xzr



        mul x10, x4, x5
        adds x16, x16, x10
        mul x10, x4, x6
        adcs x17, x17, x10
        mul x10, x4, x7
        adcs x19, x19, x10
        mul x10, x4, x8
        adcs x20, x20, x10
        mul x10, x4, x9
        adcs x21, x21, x10
        mul x10, x6, x8
        adcs x22, x22, x10
        cset x23, cs

        umulh x10, x4, x5
        adds x17, x17, x10
        umulh x10, x4, x6
        adcs x19, x19, x10
        umulh x10, x4, x7
        adcs x20, x20, x10
        umulh x10, x4, x8
        adcs x21, x21, x10
        umulh x10, x4, x9
        adcs x22, x22, x10
        umulh x10, x6, x8
        adc x23, x23, x10
        mul x10, x7, x8
        umulh x24, x7, x8
        adds x23, x23, x10
        adc x24, x24, xzr



        mul x10, x5, x6
        adds x19, x19, x10
        mul x10, x5, x7
        adcs x20, x20, x10
        mul x10, x5, x8
        adcs x21, x21, x10
        mul x10, x5, x9
        adcs x22, x22, x10
        mul x10, x6, x9
        adcs x23, x23, x10
        mul x10, x7, x9
        adcs x24, x24, x10
        cset x25, cs

        umulh x10, x5, x6
        adds x20, x20, x10
        umulh x10, x5, x7
        adcs x21, x21, x10
        umulh x10, x5, x8
        adcs x22, x22, x10
        umulh x10, x5, x9
        adcs x23, x23, x10
        umulh x10, x6, x9
        adcs x24, x24, x10
        umulh x10, x7, x9
        adc x25, x25, x10
        mul x10, x8, x9
        umulh x26, x8, x9
        adds x25, x25, x10
        adc x26, x26, xzr



        adds x12, x12, x12
        adcs x13, x13, x13
        adcs x14, x14, x14
        adcs x15, x15, x15
        adcs x16, x16, x16
        adcs x17, x17, x17
        adcs x19, x19, x19
        adcs x20, x20, x20
        adcs x21, x21, x21
        adcs x22, x22, x22
        adcs x23, x23, x23
        adcs x24, x24, x24
        adcs x25, x25, x25
        adcs x26, x26, x26
        cset x27, cs



        umulh x10, x2, x2
        mul x11, x2, x2
        adds x12, x12, x10

        mul x10, x3, x3
        adcs x13, x13, x10
        umulh x10, x3, x3
        adcs x14, x14, x10

        mul x10, x4, x4
        adcs x15, x15, x10
        umulh x10, x4, x4
        adcs x16, x16, x10

        mul x10, x5, x5
        adcs x17, x17, x10
        umulh x10, x5, x5
        adcs x19, x19, x10

        mul x10, x6, x6
        adcs x20, x20, x10
        umulh x10, x6, x6
        adcs x21, x21, x10

        mul x10, x7, x7
        adcs x22, x22, x10
        umulh x10, x7, x7
        adcs x23, x23, x10

        mul x10, x8, x8
        adcs x24, x24, x10
        umulh x10, x8, x8
        adcs x25, x25, x10

        mul x10, x9, x9
        adcs x26, x26, x10
        umulh x10, x9, x9
        adc x27, x27, x10



        ldr x1, [x1, #64]
        mul x29, x1, x1
        add x1, x1, x1



        mul x10, x1, x2
        adds x20, x20, x10
        mul x10, x1, x3
        adcs x21, x21, x10
        mul x10, x1, x4
        adcs x22, x22, x10
        mul x10, x1, x5
        adcs x23, x23, x10
        mul x10, x1, x6
        adcs x24, x24, x10
        mul x10, x1, x7
        adcs x25, x25, x10
        mul x10, x1, x8
        adcs x26, x26, x10
        mul x10, x1, x9
        adcs x27, x27, x10
        adc x29, x29, xzr

        umulh x10, x1, x2
        adds x21, x21, x10
        umulh x10, x1, x3
        adcs x22, x22, x10
        umulh x10, x1, x4
        adcs x23, x23, x10
        umulh x10, x1, x5
        adcs x24, x24, x10
        umulh x10, x1, x6
        adcs x25, x25, x10
        umulh x10, x1, x7
        adcs x26, x26, x10
        umulh x10, x1, x8
        adcs x27, x27, x10
        umulh x10, x1, x9
        adc x29, x29, x10




        subs xzr, xzr, xzr
        extr x10, x21, x20, #9
        adcs x11, x11, x10
        extr x10, x22, x21, #9
        adcs x12, x12, x10
        extr x10, x23, x22, #9
        adcs x13, x13, x10
        extr x10, x24, x23, #9
        adcs x14, x14, x10
        extr x10, x25, x24, #9
        adcs x15, x15, x10
        extr x10, x26, x25, #9
        adcs x16, x16, x10
        extr x10, x27, x26, #9
        adcs x17, x17, x10
        extr x10, x29, x27, #9
        adcs x19, x19, x10
        orr x20, x20, #~0x1FF
        lsr x10, x29, #9
        adcs x20, x20, x10





        sbcs x11, x11, xzr
        sbcs x12, x12, xzr
        sbcs x13, x13, xzr
        sbcs x14, x14, xzr
        sbcs x15, x15, xzr
        sbcs x16, x16, xzr
        sbcs x17, x17, xzr
        sbcs x19, x19, xzr
        sbc x20, x20, xzr
        and x20, x20, #0x1FF



        stp x11, x12, [x0]
        stp x13, x14, [x0, #16]
        stp x15, x16, [x0, #32]
        stp x17, x19, [x0, #48]
        str x20, [x0, #64]



        ldp x27, x29, [sp], #16
        ldp x25, x26, [sp], #16
        ldp x23, x24, [sp], #16
        ldp x21, x22, [sp], #16
        ldp x19, x20, [sp], #16

        ret
