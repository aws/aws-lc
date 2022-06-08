# 1 "/Users/milaaws/Desktop/official_AWS-LC-SHA3/aws-lc/third_party/s2n-bignum/arm/p521/bignum_sqr_p521.S"
# 1 "<built-in>" 1
# 1 "/Users/milaaws/Desktop/official_AWS-LC-SHA3/aws-lc/third_party/s2n-bignum/arm/p521/bignum_sqr_p521.S" 2
# 25 "/Users/milaaws/Desktop/official_AWS-LC-SHA3/aws-lc/third_party/s2n-bignum/arm/p521/bignum_sqr_p521.S"
        .globl bignum_sqr_p521
        .globl _bignum_sqr_p521
        .text
        .balign 4
# 70 "/Users/milaaws/Desktop/official_AWS-LC-SHA3/aws-lc/third_party/s2n-bignum/arm/p521/bignum_sqr_p521.S"
bignum_sqr_p521:
_bignum_sqr_p521:



        stp x19, x20, [sp, #-16]!
        stp x21, x22, [sp, #-16]!
        stp x23, x24, [sp, #-16]!



        ldp x2, x3, [x1]
        ldp x4, x5, [x1, #16]
        ldp x6, x7, [x1, #32]
        ldp x8, x9, [x1, #48]



        mul x12, x6, x8
        mul x17, x7, x9
        umulh x22, x6, x8
        subs x23, x6, x7
        cneg x23, x23, cc
        csetm x11, cc
        subs x10, x9, x8
        cneg x10, x10, cc
        mul x16, x23, x10
        umulh x10, x23, x10
        cinv x11, x11, cc
        eor x16, x16, x11
        eor x10, x10, x11
        adds x13, x12, x22
        adc x22, x22, xzr
        umulh x23, x7, x9
        adds x13, x13, x17
        adcs x22, x22, x23
        adc x23, x23, xzr
        adds x22, x22, x17
        adc x23, x23, xzr
        cmn x11, #0x1
        adcs x13, x13, x16
        adcs x22, x22, x10
        adc x23, x23, x11
        adds x12, x12, x12
        adcs x13, x13, x13
        adcs x22, x22, x22
        adcs x23, x23, x23
        adc x19, xzr, xzr
        mul x10, x6, x6
        mul x16, x7, x7
        mul x21, x6, x7
        umulh x11, x6, x6
        umulh x17, x7, x7
        umulh x20, x6, x7
        adds x11, x11, x21
        adcs x16, x16, x20
        adc x17, x17, xzr
        adds x11, x11, x21
        adcs x16, x16, x20
        adc x17, x17, xzr
        adds x12, x12, x16
        adcs x13, x13, x17
        adcs x22, x22, xzr
        adcs x23, x23, xzr
        adc x19, x19, xzr
        mul x14, x8, x8
        mul x16, x9, x9
        mul x21, x8, x9
        umulh x15, x8, x8
        umulh x17, x9, x9
        umulh x20, x8, x9
        adds x15, x15, x21
        adcs x16, x16, x20
        adc x17, x17, xzr
        adds x15, x15, x21
        adcs x16, x16, x20
        adc x17, x17, xzr
        adds x14, x14, x22
        adcs x15, x15, x23
        adcs x16, x16, x19
        adc x17, x17, xzr
# 165 "/Users/milaaws/Desktop/official_AWS-LC-SHA3/aws-lc/third_party/s2n-bignum/arm/p521/bignum_sqr_p521.S"
        ldr x19, [x1, #64]
        add x23, x19, x19
        mul x19, x19, x19



        and x21, x2, #0x000fffffffffffff
        mul x21, x23, x21



        extr x20, x3, x2, #52
        and x20, x20, #0x000fffffffffffff
        mul x20, x23, x20
        lsr x22, x21, #52
        add x20, x20, x22

        lsl x21, x21, #12
        extr x22, x20, x21, #12
        adds x10, x10, x22



        extr x21, x4, x3, #40
        and x21, x21, #0x000fffffffffffff
        mul x21, x23, x21
        lsr x22, x20, #52
        add x21, x21, x22

        lsl x20, x20, #12
        extr x22, x21, x20, #24
        adcs x11, x11, x22



        extr x20, x5, x4, #28
        and x20, x20, #0x000fffffffffffff
        mul x20, x23, x20
        lsr x22, x21, #52
        add x20, x20, x22

        lsl x21, x21, #12
        extr x22, x20, x21, #36
        adcs x12, x12, x22



        extr x21, x6, x5, #16
        and x21, x21, #0x000fffffffffffff
        mul x21, x23, x21
        lsr x22, x20, #52
        add x21, x21, x22

        lsl x20, x20, #12
        extr x22, x21, x20, #48
        adcs x13, x13, x22



        lsr x20, x6, #4
        and x20, x20, #0x000fffffffffffff
        mul x20, x23, x20
        lsr x22, x21, #52
        add x20, x20, x22

        lsl x21, x21, #12
        extr x24, x20, x21, #60



        extr x21, x7, x6, #56
        and x21, x21, #0x000fffffffffffff
        mul x21, x23, x21
        lsr x22, x20, #52
        add x21, x21, x22

        lsl x24, x24, #8
        extr x22, x21, x24, #8
        adcs x14, x14, x22



        extr x20, x8, x7, #44
        and x20, x20, #0x000fffffffffffff
        mul x20, x23, x20
        lsr x22, x21, #52
        add x20, x20, x22

        lsl x21, x21, #12
        extr x22, x20, x21, #20
        adcs x15, x15, x22



        extr x21, x9, x8, #32
        and x21, x21, #0x000fffffffffffff
        mul x21, x23, x21
        lsr x22, x20, #52
        add x21, x21, x22

        lsl x20, x20, #12
        extr x22, x21, x20, #32
        adcs x16, x16, x22



        lsr x20, x9, #20
        mul x20, x23, x20
        lsr x22, x21, #52
        add x20, x20, x22

        lsl x21, x21, #12
        extr x22, x20, x21, #44
        adcs x17, x17, x22



        lsr x20, x20, #44
        adc x19, x19, x20





        extr x21, x11, x10, #9
        extr x20, x12, x11, #9
        stp x21, x20, [x0]

        extr x21, x13, x12, #9
        extr x20, x14, x13, #9
        stp x21, x20, [x0, #16]

        extr x21, x15, x14, #9
        extr x20, x16, x15, #9
        stp x21, x20, [x0, #32]

        extr x21, x17, x16, #9
        extr x20, x19, x17, #9
        stp x21, x20, [x0, #48]

        and x22, x10, #0x1FF
        lsr x19, x19, #9
        add x22, x22, x19
        str x22, [x0, #64]



        mul x12, x2, x4
        mul x17, x3, x5
        umulh x22, x2, x4
        subs x23, x2, x3
        cneg x23, x23, cc
        csetm x11, cc
        subs x10, x5, x4
        cneg x10, x10, cc
        mul x16, x23, x10
        umulh x10, x23, x10
        cinv x11, x11, cc
        eor x16, x16, x11
        eor x10, x10, x11
        adds x13, x12, x22
        adc x22, x22, xzr
        umulh x23, x3, x5
        adds x13, x13, x17
        adcs x22, x22, x23
        adc x23, x23, xzr
        adds x22, x22, x17
        adc x23, x23, xzr
        cmn x11, #0x1
        adcs x13, x13, x16
        adcs x22, x22, x10
        adc x23, x23, x11
        adds x12, x12, x12
        adcs x13, x13, x13
        adcs x22, x22, x22
        adcs x23, x23, x23
        adc x19, xzr, xzr
        mul x10, x2, x2
        mul x16, x3, x3
        mul x21, x2, x3
        umulh x11, x2, x2
        umulh x17, x3, x3
        umulh x20, x2, x3
        adds x11, x11, x21
        adcs x16, x16, x20
        adc x17, x17, xzr
        adds x11, x11, x21
        adcs x16, x16, x20
        adc x17, x17, xzr
        adds x12, x12, x16
        adcs x13, x13, x17
        adcs x22, x22, xzr
        adcs x23, x23, xzr
        adc x19, x19, xzr
        mul x14, x4, x4
        mul x16, x5, x5
        mul x21, x4, x5
        umulh x15, x4, x4
        umulh x17, x5, x5
        umulh x20, x4, x5
        adds x15, x15, x21
        adcs x16, x16, x20
        adc x17, x17, xzr
        adds x15, x15, x21
        adcs x16, x16, x20
        adc x17, x17, xzr
        adds x14, x14, x22
        adcs x15, x15, x23
        adcs x16, x16, x19
        adc x17, x17, xzr



        ldp x21, x20, [x0]
        adds x21, x21, x10
        adcs x20, x20, x11
        stp x21, x20, [x0]

        ldp x21, x20, [x0, #16]
        adcs x21, x21, x12
        adcs x20, x20, x13
        stp x21, x20, [x0, #16]

        ldp x21, x20, [x0, #32]
        adcs x21, x21, x14
        adcs x20, x20, x15
        stp x21, x20, [x0, #32]

        ldp x21, x20, [x0, #48]
        adcs x21, x21, x16
        adcs x20, x20, x17
        stp x21, x20, [x0, #48]

        ldr x22, [x0, #64]
        adc x22, x22, xzr
        str x22, [x0, #64]



        mul x10, x2, x6
        mul x14, x3, x7
        mul x15, x4, x8
        mul x16, x5, x9
        umulh x17, x2, x6
        adds x14, x14, x17
        umulh x17, x3, x7
        adcs x15, x15, x17
        umulh x17, x4, x8
        adcs x16, x16, x17
        umulh x17, x5, x9
        adc x17, x17, xzr
        adds x11, x14, x10
        adcs x14, x15, x14
        adcs x15, x16, x15
        adcs x16, x17, x16
        adc x17, xzr, x17
        adds x12, x14, x10
        adcs x13, x15, x11
        adcs x14, x16, x14
        adcs x15, x17, x15
        adcs x16, xzr, x16
        adc x17, xzr, x17
        subs x22, x4, x5
        cneg x22, x22, cc
        csetm x19, cc
        subs x20, x9, x8
        cneg x20, x20, cc
        mul x21, x22, x20
        umulh x20, x22, x20
        cinv x19, x19, cc
        cmn x19, #0x1
        eor x21, x21, x19
        adcs x15, x15, x21
        eor x20, x20, x19
        adcs x16, x16, x20
        adc x17, x17, x19
        subs x22, x2, x3
        cneg x22, x22, cc
        csetm x19, cc
        subs x20, x7, x6
        cneg x20, x20, cc
        mul x21, x22, x20
        umulh x20, x22, x20
        cinv x19, x19, cc
        cmn x19, #0x1
        eor x21, x21, x19
        adcs x11, x11, x21
        eor x20, x20, x19
        adcs x12, x12, x20
        adcs x13, x13, x19
        adcs x14, x14, x19
        adcs x15, x15, x19
        adcs x16, x16, x19
        adc x17, x17, x19
        subs x22, x3, x5
        cneg x22, x22, cc
        csetm x19, cc
        subs x20, x9, x7
        cneg x20, x20, cc
        mul x21, x22, x20
        umulh x20, x22, x20
        cinv x19, x19, cc
        cmn x19, #0x1
        eor x21, x21, x19
        adcs x14, x14, x21
        eor x20, x20, x19
        adcs x15, x15, x20
        adcs x16, x16, x19
        adc x17, x17, x19
        subs x22, x2, x4
        cneg x22, x22, cc
        csetm x19, cc
        subs x20, x8, x6
        cneg x20, x20, cc
        mul x21, x22, x20
        umulh x20, x22, x20
        cinv x19, x19, cc
        cmn x19, #0x1
        eor x21, x21, x19
        adcs x12, x12, x21
        eor x20, x20, x19
        adcs x13, x13, x20
        adcs x14, x14, x19
        adcs x15, x15, x19
        adcs x16, x16, x19
        adc x17, x17, x19
        subs x22, x2, x5
        cneg x22, x22, cc
        csetm x19, cc
        subs x20, x9, x6
        cneg x20, x20, cc
        mul x21, x22, x20
        umulh x20, x22, x20
        cinv x19, x19, cc
        cmn x19, #0x1
        eor x21, x21, x19
        adcs x13, x13, x21
        eor x20, x20, x19
        adcs x14, x14, x20
        adcs x15, x15, x19
        adcs x16, x16, x19
        adc x17, x17, x19
        subs x22, x3, x4
        cneg x22, x22, cc
        csetm x19, cc
        subs x20, x8, x7
        cneg x20, x20, cc
        mul x21, x22, x20
        umulh x20, x22, x20
        cinv x19, x19, cc
        cmn x19, #0x1
        eor x21, x21, x19
        adcs x13, x13, x21
        eor x20, x20, x19
        adcs x14, x14, x20
        adcs x15, x15, x19
        adcs x16, x16, x19
        adc x17, x17, x19
# 531 "/Users/milaaws/Desktop/official_AWS-LC-SHA3/aws-lc/third_party/s2n-bignum/arm/p521/bignum_sqr_p521.S"
        ldp x21, x20, [x0]
        extr x2, x15, x14, #8
        adds x2, x2, x21
        extr x3, x16, x15, #8
        adcs x3, x3, x20

        ldp x21, x20, [x0, #16]
        extr x4, x17, x16, #8
        adcs x4, x4, x21
        and x22, x3, x4
        lsr x5, x17, #8
        adcs x5, x5, x20
        and x22, x22, x5

        ldp x21, x20, [x0, #32]
        lsl x6, x10, #1
        adcs x6, x6, x21
        and x22, x22, x6
        extr x7, x11, x10, #63
        adcs x7, x7, x20
        and x22, x22, x7

        ldp x21, x20, [x0, #48]
        extr x8, x12, x11, #63
        adcs x8, x8, x21
        and x22, x22, x8
        extr x9, x13, x12, #63
        adcs x9, x9, x20
        and x22, x22, x9

        ldr x21, [x0, #64]
        extr x10, x14, x13, #63
        and x10, x10, #0x1FF
        adc x10, x21, x10




        lsr x20, x10, #9
        orr x10, x10, #~0x1FF






        subs xzr, xzr, xzr
        adcs xzr, x2, x20
        adcs xzr, x22, xzr
        adcs xzr, x10, xzr





        adcs x2, x2, x20
        adcs x3, x3, xzr
        adcs x4, x4, xzr
        adcs x5, x5, xzr
        adcs x6, x6, xzr
        adcs x7, x7, xzr
        adcs x8, x8, xzr
        adcs x9, x9, xzr
        adc x10, x10, xzr
        and x10, x10, #0x1FF



        stp x2, x3, [x0]
        stp x4, x5, [x0, #16]
        stp x6, x7, [x0, #32]
        stp x8, x9, [x0, #48]
        str x10, [x0, #64]



        ldp x23, x24, [sp], #16
        ldp x21, x22, [sp], #16
        ldp x19, x20, [sp], #16

        ret
