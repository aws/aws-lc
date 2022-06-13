# 1 "/Users/milaaws/Desktop/official_AWS-LC-SHA3/aws-lc/third_party/s2n-bignum/arm/p521/bignum_mul_p521_alt.S"
# 1 "<built-in>" 1
# 1 "/Users/milaaws/Desktop/official_AWS-LC-SHA3/aws-lc/third_party/s2n-bignum/arm/p521/bignum_mul_p521_alt.S" 2
# 26 "/Users/milaaws/Desktop/official_AWS-LC-SHA3/aws-lc/third_party/s2n-bignum/arm/p521/bignum_mul_p521_alt.S"
        .globl bignum_mul_p521_alt
        .globl _bignum_mul_p521_alt
        .text
        .balign 4
# 80 "/Users/milaaws/Desktop/official_AWS-LC-SHA3/aws-lc/third_party/s2n-bignum/arm/p521/bignum_mul_p521_alt.S"
bignum_mul_p521_alt:
_bignum_mul_p521_alt:



        stp x19, x20, [sp, #-16]!
        stp x21, x22, [sp, #-16]!
        stp x23, x24, [sp, #-16]!
        stp x25, x26, [sp, #-16]!
        sub sp, sp, #64



        ldp x3, x4, [x1]
        ldp x5, x6, [x2]

        mul x15, x3, x5
        umulh x16, x3, x5
        mul x14, x3, x6
        umulh x17, x3, x6
        adds x16, x16, x14

        ldp x7, x8, [x2, #16]

        mul x14, x3, x7
        umulh x19, x3, x7
        adcs x17, x17, x14

        mul x14, x3, x8
        umulh x20, x3, x8
        adcs x19, x19, x14

        ldp x9, x10, [x2, #32]

        mul x14, x3, x9
        umulh x21, x3, x9
        adcs x20, x20, x14

        mul x14, x3, x10
        umulh x22, x3, x10
        adcs x21, x21, x14

        ldp x11, x12, [x2, #48]

        mul x14, x3, x11
        umulh x23, x3, x11
        adcs x22, x22, x14

        ldr x13, [x2, #64]

        mul x14, x3, x12
        umulh x24, x3, x12
        adcs x23, x23, x14

        mul x14, x3, x13
        umulh x25, x3, x13
        adcs x24, x24, x14

        adc x25, x25, xzr



        mul x14, x4, x5
        adds x16, x16, x14
        mul x14, x4, x6
        adcs x17, x17, x14
        mul x14, x4, x7
        adcs x19, x19, x14
        mul x14, x4, x8
        adcs x20, x20, x14
        mul x14, x4, x9
        adcs x21, x21, x14
        mul x14, x4, x10
        adcs x22, x22, x14
        mul x14, x4, x11
        adcs x23, x23, x14
        mul x14, x4, x12
        adcs x24, x24, x14
        mul x14, x4, x13
        adcs x25, x25, x14
        cset x26, cs

        umulh x14, x4, x5
        adds x17, x17, x14
        umulh x14, x4, x6
        adcs x19, x19, x14
        umulh x14, x4, x7
        adcs x20, x20, x14
        umulh x14, x4, x8
        adcs x21, x21, x14
        umulh x14, x4, x9
        adcs x22, x22, x14
        umulh x14, x4, x10
        adcs x23, x23, x14
        umulh x14, x4, x11
        adcs x24, x24, x14
        umulh x14, x4, x12
        adcs x25, x25, x14
        umulh x14, x4, x13
        adc x26, x26, x14

        stp x15, x16, [sp]



        ldp x3, x4, [x1, #16]

        mul x14, x3, x5
        adds x17, x17, x14
        mul x14, x3, x6
        adcs x19, x19, x14
        mul x14, x3, x7
        adcs x20, x20, x14
        mul x14, x3, x8
        adcs x21, x21, x14
        mul x14, x3, x9
        adcs x22, x22, x14
        mul x14, x3, x10
        adcs x23, x23, x14
        mul x14, x3, x11
        adcs x24, x24, x14
        mul x14, x3, x12
        adcs x25, x25, x14
        mul x14, x3, x13
        adcs x26, x26, x14
        cset x15, cs

        umulh x14, x3, x5
        adds x19, x19, x14
        umulh x14, x3, x6
        adcs x20, x20, x14
        umulh x14, x3, x7
        adcs x21, x21, x14
        umulh x14, x3, x8
        adcs x22, x22, x14
        umulh x14, x3, x9
        adcs x23, x23, x14
        umulh x14, x3, x10
        adcs x24, x24, x14
        umulh x14, x3, x11
        adcs x25, x25, x14
        umulh x14, x3, x12
        adcs x26, x26, x14
        umulh x14, x3, x13
        adc x15, x15, x14



        mul x14, x4, x5
        adds x19, x19, x14
        mul x14, x4, x6
        adcs x20, x20, x14
        mul x14, x4, x7
        adcs x21, x21, x14
        mul x14, x4, x8
        adcs x22, x22, x14
        mul x14, x4, x9
        adcs x23, x23, x14
        mul x14, x4, x10
        adcs x24, x24, x14
        mul x14, x4, x11
        adcs x25, x25, x14
        mul x14, x4, x12
        adcs x26, x26, x14
        mul x14, x4, x13
        adcs x15, x15, x14
        cset x16, cs

        umulh x14, x4, x5
        adds x20, x20, x14
        umulh x14, x4, x6
        adcs x21, x21, x14
        umulh x14, x4, x7
        adcs x22, x22, x14
        umulh x14, x4, x8
        adcs x23, x23, x14
        umulh x14, x4, x9
        adcs x24, x24, x14
        umulh x14, x4, x10
        adcs x25, x25, x14
        umulh x14, x4, x11
        adcs x26, x26, x14
        umulh x14, x4, x12
        adcs x15, x15, x14
        umulh x14, x4, x13
        adc x16, x16, x14

        stp x17, x19, [sp, #16]



        ldp x3, x4, [x1, #32]

        mul x14, x3, x5
        adds x20, x20, x14
        mul x14, x3, x6
        adcs x21, x21, x14
        mul x14, x3, x7
        adcs x22, x22, x14
        mul x14, x3, x8
        adcs x23, x23, x14
        mul x14, x3, x9
        adcs x24, x24, x14
        mul x14, x3, x10
        adcs x25, x25, x14
        mul x14, x3, x11
        adcs x26, x26, x14
        mul x14, x3, x12
        adcs x15, x15, x14
        mul x14, x3, x13
        adcs x16, x16, x14
        cset x17, cs

        umulh x14, x3, x5
        adds x21, x21, x14
        umulh x14, x3, x6
        adcs x22, x22, x14
        umulh x14, x3, x7
        adcs x23, x23, x14
        umulh x14, x3, x8
        adcs x24, x24, x14
        umulh x14, x3, x9
        adcs x25, x25, x14
        umulh x14, x3, x10
        adcs x26, x26, x14
        umulh x14, x3, x11
        adcs x15, x15, x14
        umulh x14, x3, x12
        adcs x16, x16, x14
        umulh x14, x3, x13
        adc x17, x17, x14



        mul x14, x4, x5
        adds x21, x21, x14
        mul x14, x4, x6
        adcs x22, x22, x14
        mul x14, x4, x7
        adcs x23, x23, x14
        mul x14, x4, x8
        adcs x24, x24, x14
        mul x14, x4, x9
        adcs x25, x25, x14
        mul x14, x4, x10
        adcs x26, x26, x14
        mul x14, x4, x11
        adcs x15, x15, x14
        mul x14, x4, x12
        adcs x16, x16, x14
        mul x14, x4, x13
        adcs x17, x17, x14
        cset x19, cs

        umulh x14, x4, x5
        adds x22, x22, x14
        umulh x14, x4, x6
        adcs x23, x23, x14
        umulh x14, x4, x7
        adcs x24, x24, x14
        umulh x14, x4, x8
        adcs x25, x25, x14
        umulh x14, x4, x9
        adcs x26, x26, x14
        umulh x14, x4, x10
        adcs x15, x15, x14
        umulh x14, x4, x11
        adcs x16, x16, x14
        umulh x14, x4, x12
        adcs x17, x17, x14
        umulh x14, x4, x13
        adc x19, x19, x14

        stp x20, x21, [sp, #32]



        ldp x3, x4, [x1, #48]

        mul x14, x3, x5
        adds x22, x22, x14
        mul x14, x3, x6
        adcs x23, x23, x14
        mul x14, x3, x7
        adcs x24, x24, x14
        mul x14, x3, x8
        adcs x25, x25, x14
        mul x14, x3, x9
        adcs x26, x26, x14
        mul x14, x3, x10
        adcs x15, x15, x14
        mul x14, x3, x11
        adcs x16, x16, x14
        mul x14, x3, x12
        adcs x17, x17, x14
        mul x14, x3, x13
        adcs x19, x19, x14
        cset x20, cs

        umulh x14, x3, x5
        adds x23, x23, x14
        umulh x14, x3, x6
        adcs x24, x24, x14
        umulh x14, x3, x7
        adcs x25, x25, x14
        umulh x14, x3, x8
        adcs x26, x26, x14
        umulh x14, x3, x9
        adcs x15, x15, x14
        umulh x14, x3, x10
        adcs x16, x16, x14
        umulh x14, x3, x11
        adcs x17, x17, x14
        umulh x14, x3, x12
        adcs x19, x19, x14
        umulh x14, x3, x13
        adc x20, x20, x14



        mul x14, x4, x5
        adds x23, x23, x14
        mul x14, x4, x6
        adcs x24, x24, x14
        mul x14, x4, x7
        adcs x25, x25, x14
        mul x14, x4, x8
        adcs x26, x26, x14
        mul x14, x4, x9
        adcs x15, x15, x14
        mul x14, x4, x10
        adcs x16, x16, x14
        mul x14, x4, x11
        adcs x17, x17, x14
        mul x14, x4, x12
        adcs x19, x19, x14
        mul x14, x4, x13
        adcs x20, x20, x14
        cset x21, cs

        umulh x14, x4, x5
        adds x24, x24, x14
        umulh x14, x4, x6
        adcs x25, x25, x14
        umulh x14, x4, x7
        adcs x26, x26, x14
        umulh x14, x4, x8
        adcs x15, x15, x14
        umulh x14, x4, x9
        adcs x16, x16, x14
        umulh x14, x4, x10
        adcs x17, x17, x14
        umulh x14, x4, x11
        adcs x19, x19, x14
        umulh x14, x4, x12
        adcs x20, x20, x14
        umulh x14, x4, x13
        adc x21, x21, x14

        stp x22, x23, [sp, #48]



        ldr x3, [x1, #64]

        mul x14, x3, x5
        adds x24, x24, x14
        mul x14, x3, x6
        adcs x25, x25, x14
        mul x14, x3, x7
        adcs x26, x26, x14
        mul x14, x3, x8
        adcs x15, x15, x14
        mul x14, x3, x9
        adcs x16, x16, x14
        mul x14, x3, x10
        adcs x17, x17, x14
        mul x14, x3, x11
        adcs x19, x19, x14
        mul x14, x3, x12
        adcs x20, x20, x14
        mul x14, x3, x13
        adc x21, x21, x14

        umulh x14, x3, x5
        adds x25, x25, x14
        umulh x14, x3, x6
        adcs x26, x26, x14
        umulh x14, x3, x7
        adcs x15, x15, x14
        umulh x14, x3, x8
        adcs x16, x16, x14
        umulh x14, x3, x9
        adcs x17, x17, x14
        umulh x14, x3, x10
        adcs x19, x19, x14
        umulh x14, x3, x11
        adcs x20, x20, x14
        umulh x14, x3, x12
        adc x21, x21, x14




        subs xzr, xzr, xzr
        ldp x5, x6, [sp]
        extr x14, x25, x24, #9
        adcs x5, x5, x14
        extr x14, x26, x25, #9
        adcs x6, x6, x14
        ldp x7, x8, [sp, #16]
        extr x14, x15, x26, #9
        adcs x7, x7, x14
        extr x14, x16, x15, #9
        adcs x8, x8, x14
        ldp x9, x10, [sp, #32]
        extr x14, x17, x16, #9
        adcs x9, x9, x14
        extr x14, x19, x17, #9
        adcs x10, x10, x14
        ldp x11, x12, [sp, #48]
        extr x14, x20, x19, #9
        adcs x11, x11, x14
        extr x14, x21, x20, #9
        adcs x12, x12, x14
        orr x13, x24, #~0x1FF
        lsr x14, x21, #9
        adcs x13, x13, x14





        sbcs x5, x5, xzr
        sbcs x6, x6, xzr
        sbcs x7, x7, xzr
        sbcs x8, x8, xzr
        sbcs x9, x9, xzr
        sbcs x10, x10, xzr
        sbcs x11, x11, xzr
        sbcs x12, x12, xzr
        sbc x13, x13, xzr
        and x13, x13, #0x1FF



        stp x5, x6, [x0]
        stp x7, x8, [x0, #16]
        stp x9, x10, [x0, #32]
        stp x11, x12, [x0, #48]
        str x13, [x0, #64]



        add sp, sp, #64
        ldp x25, x26, [sp], #16
        ldp x23, x24, [sp], #16
        ldp x21, x22, [sp], #16
        ldp x19, x20, [sp], #16

        ret
