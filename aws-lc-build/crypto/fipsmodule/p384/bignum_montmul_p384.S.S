# 1 "/Users/milaaws/Desktop/official_AWS-LC-SHA3/aws-lc/third_party/s2n-bignum/arm/p384/bignum_montmul_p384.S"
# 1 "<built-in>" 1
# 1 "/Users/milaaws/Desktop/official_AWS-LC-SHA3/aws-lc/third_party/s2n-bignum/arm/p384/bignum_montmul_p384.S" 2
# 30 "/Users/milaaws/Desktop/official_AWS-LC-SHA3/aws-lc/third_party/s2n-bignum/arm/p384/bignum_montmul_p384.S"
        .globl bignum_montmul_p384
        .globl _bignum_montmul_p384
        .text
        .balign 4
# 116 "/Users/milaaws/Desktop/official_AWS-LC-SHA3/aws-lc/third_party/s2n-bignum/arm/p384/bignum_montmul_p384.S"
bignum_montmul_p384:
_bignum_montmul_p384:



        stp x19, x20, [sp, -16]!
        stp x21, x22, [sp, -16]!
        stp x23, x24, [sp, -16]!



        ldp x3, x4, [x1]
        ldp x5, x6, [x1, #16]
        ldp x7, x8, [x1, #32]
        ldp x9, x10, [x2]
        ldp x11, x12, [x2, #16]
        ldp x13, x14, [x2, #32]



        mul x15, x3, x9
        mul x21, x4, x10
        mul x22, x5, x11
        umulh x23, x3, x9
        umulh x24, x4, x10
        umulh x1, x5, x11

        adds x23, x23, x21
        adcs x24, x24, x22
        adc x1, x1, xzr

        adds x16, x23, x15
        adcs x17, x24, x23
        adcs x19, x1, x24
        adc x20, x1, xzr

        adds x17, x17, x15
        adcs x19, x19, x23
        adcs x20, x20, x24
        adc x1, x1, xzr

        subs x24, x3, x4
 cneg x24, x24, cc
 csetm x23, cc
 subs x22, x10, x9
 cneg x22, x22, cc
 mul x21, x24, x22
 umulh x22, x24, x22
 cinv x23, x23, cc
 eor x21, x21, x23
 eor x22, x22, x23
        adds xzr, x23, #1
        adcs x16, x16, x21
        adcs x17, x17, x22
        adcs x19, x19, x23
        adcs x20, x20, x23
        adc x1, x1, x23

        subs x24, x3, x5
 cneg x24, x24, cc
 csetm x23, cc
 subs x22, x11, x9
 cneg x22, x22, cc
 mul x21, x24, x22
 umulh x22, x24, x22
 cinv x23, x23, cc
 eor x21, x21, x23
 eor x22, x22, x23
        adds xzr, x23, #1
        adcs x17, x17, x21
        adcs x19, x19, x22
        adcs x20, x20, x23
        adc x1, x1, x23

        subs x24, x4, x5
 cneg x24, x24, cc
 csetm x23, cc
 subs x22, x11, x10
 cneg x22, x22, cc
 mul x21, x24, x22
 umulh x22, x24, x22
 cinv x23, x23, cc
 eor x21, x21, x23
 eor x22, x22, x23
        adds xzr, x23, #1
        adcs x19, x19, x21
        adcs x20, x20, x22
        adc x1, x1, x23







        lsl x23, x15, #32
 add x15, x23, x15
 lsr x23, x15, #32
 subs x23, x23, x15
 sbc x22, x15, xzr
 extr x23, x22, x23, #32
 lsr x22, x22, #32
 adds x22, x22, x15
 adc x21, xzr, xzr
 subs x16, x16, x23
 sbcs x17, x17, x22
 sbcs x19, x19, x21
 sbcs x20, x20, xzr
 sbcs x1, x1, xzr
 sbc x15, x15, xzr

        lsl x23, x16, #32
 add x16, x23, x16
 lsr x23, x16, #32
 subs x23, x23, x16
 sbc x22, x16, xzr
 extr x23, x22, x23, #32
 lsr x22, x22, #32
 adds x22, x22, x16
 adc x21, xzr, xzr
 subs x17, x17, x23
 sbcs x19, x19, x22
 sbcs x20, x20, x21
 sbcs x1, x1, xzr
 sbcs x15, x15, xzr
 sbc x16, x16, xzr

        lsl x23, x17, #32
 add x17, x23, x17
 lsr x23, x17, #32
 subs x23, x23, x17
 sbc x22, x17, xzr
 extr x23, x22, x23, #32
 lsr x22, x22, #32
 adds x22, x22, x17
 adc x21, xzr, xzr
 subs x19, x19, x23
 sbcs x20, x20, x22
 sbcs x1, x1, x21
 sbcs x15, x15, xzr
 sbcs x16, x16, xzr
 sbc x17, x17, xzr

        stp x19, x20, [x0]
        stp x1, x15, [x0, #16]
        stp x16, x17, [x0, #32]



        mul x15, x6, x12
        mul x21, x7, x13
        mul x22, x8, x14
        umulh x23, x6, x12
        umulh x24, x7, x13
        umulh x1, x8, x14

        adds x23, x23, x21
        adcs x24, x24, x22
        adc x1, x1, xzr

        adds x16, x23, x15
        adcs x17, x24, x23
        adcs x19, x1, x24
        adc x20, x1, xzr

        adds x17, x17, x15
        adcs x19, x19, x23
        adcs x20, x20, x24
        adc x1, x1, xzr

        subs x24, x6, x7
 cneg x24, x24, cc
 csetm x23, cc
 subs x22, x13, x12
 cneg x22, x22, cc
 mul x21, x24, x22
 umulh x22, x24, x22
 cinv x23, x23, cc
 eor x21, x21, x23
 eor x22, x22, x23
        adds xzr, x23, #1
        adcs x16, x16, x21
        adcs x17, x17, x22
        adcs x19, x19, x23
        adcs x20, x20, x23
        adc x1, x1, x23

        subs x24, x6, x8
 cneg x24, x24, cc
 csetm x23, cc
 subs x22, x14, x12
 cneg x22, x22, cc
 mul x21, x24, x22
 umulh x22, x24, x22
 cinv x23, x23, cc
 eor x21, x21, x23
 eor x22, x22, x23
        adds xzr, x23, #1
        adcs x17, x17, x21
        adcs x19, x19, x22
        adcs x20, x20, x23
        adc x1, x1, x23

        subs x24, x7, x8
 cneg x24, x24, cc
 csetm x23, cc
 subs x22, x14, x13
 cneg x22, x22, cc
 mul x21, x24, x22
 umulh x22, x24, x22
 cinv x23, x23, cc
 eor x21, x21, x23
 eor x22, x22, x23
        adds xzr, x23, #1
        adcs x19, x19, x21
        adcs x20, x20, x22
        adc x1, x1, x23



        subs x6, x6, x3
        sbcs x7, x7, x4
        sbcs x8, x8, x5
        sbc x3, xzr, xzr
        adds xzr, x3, #1
        eor x6, x6, x3
        adcs x6, x6, xzr
        eor x7, x7, x3
        adcs x7, x7, xzr
        eor x8, x8, x3
        adc x8, x8, xzr



        subs x9, x9, x12
        sbcs x10, x10, x13
        sbcs x11, x11, x14
        sbc x14, xzr, xzr

        adds xzr, x14, #1
        eor x9, x9, x14
        adcs x9, x9, xzr
        eor x10, x10, x14
        adcs x10, x10, xzr
        eor x11, x11, x14
        adc x11, x11, xzr



        eor x14, x3, x14




        ldp x21, x22, [x0]
        adds x15, x15, x21
        adcs x16, x16, x22
        ldp x21, x22, [x0, #16]
        adcs x17, x17, x21
        adcs x19, x19, x22
        ldp x21, x22, [x0, #32]
        adcs x20, x20, x21
        adcs x1, x1, x22
        adc x2, xzr, xzr
        stp x15, x16, [x0]
        stp x17, x19, [x0, #16]
        stp x20, x1, [x0, #32]



        mul x15, x6, x9
        mul x21, x7, x10
        mul x22, x8, x11
        umulh x23, x6, x9
        umulh x24, x7, x10
        umulh x1, x8, x11

        adds x23, x23, x21
        adcs x24, x24, x22
        adc x1, x1, xzr

        adds x16, x23, x15
        adcs x17, x24, x23
        adcs x19, x1, x24
        adc x20, x1, xzr

        adds x17, x17, x15
        adcs x19, x19, x23
        adcs x20, x20, x24
        adc x1, x1, xzr

        subs x24, x6, x7
 cneg x24, x24, cc
 csetm x23, cc
 subs x22, x10, x9
 cneg x22, x22, cc
 mul x21, x24, x22
 umulh x22, x24, x22
 cinv x23, x23, cc
 eor x21, x21, x23
 eor x22, x22, x23
        adds xzr, x23, #1
        adcs x16, x16, x21
        adcs x17, x17, x22
        adcs x19, x19, x23
        adcs x20, x20, x23
        adc x1, x1, x23

        subs x24, x6, x8
 cneg x24, x24, cc
 csetm x23, cc
 subs x22, x11, x9
 cneg x22, x22, cc
 mul x21, x24, x22
 umulh x22, x24, x22
 cinv x23, x23, cc
 eor x21, x21, x23
 eor x22, x22, x23
        adds xzr, x23, #1
        adcs x17, x17, x21
        adcs x19, x19, x22
        adcs x20, x20, x23
        adc x1, x1, x23

        subs x24, x7, x8
 cneg x24, x24, cc
 csetm x23, cc
 subs x22, x11, x10
 cneg x22, x22, cc
 mul x21, x24, x22
 umulh x22, x24, x22
 cinv x23, x23, cc
 eor x21, x21, x23
 eor x22, x22, x23
        adds xzr, x23, #1
        adcs x19, x19, x21
        adcs x20, x20, x22
        adc x1, x1, x23



        ldp x3, x4, [x0]
        ldp x5, x6, [x0, #16]
        ldp x7, x8, [x0, #32]





        adds xzr, x14, #1
        eor x15, x15, x14
        adcs x15, x15, x3
        eor x16, x16, x14
        adcs x16, x16, x4
        eor x17, x17, x14
        adcs x17, x17, x5
        eor x19, x19, x14
        adcs x19, x19, x6
        eor x20, x20, x14
        adcs x20, x20, x7
        eor x1, x1, x14
        adcs x1, x1, x8
        adcs x9, x14, x2
        adcs x10, x14, xzr
        adcs x11, x14, xzr
        adc x12, x14, xzr



        adds x19, x19, x3
        adcs x20, x20, x4
        adcs x1, x1, x5
        adcs x9, x9, x6
        adcs x10, x10, x7
        adcs x11, x11, x8
        adc x12, x12, x2



        lsl x23, x15, #32
 add x15, x23, x15
 lsr x23, x15, #32
 subs x23, x23, x15
 sbc x22, x15, xzr
 extr x23, x22, x23, #32
 lsr x22, x22, #32
 adds x22, x22, x15
 adc x21, xzr, xzr
 subs x16, x16, x23
 sbcs x17, x17, x22
 sbcs x19, x19, x21
 sbcs x20, x20, xzr
 sbcs x1, x1, xzr
 sbc x15, x15, xzr
        lsl x23, x16, #32
 add x16, x23, x16
 lsr x23, x16, #32
 subs x23, x23, x16
 sbc x22, x16, xzr
 extr x23, x22, x23, #32
 lsr x22, x22, #32
 adds x22, x22, x16
 adc x21, xzr, xzr
 subs x17, x17, x23
 sbcs x19, x19, x22
 sbcs x20, x20, x21
 sbcs x1, x1, xzr
 sbcs x15, x15, xzr
 sbc x16, x16, xzr
        lsl x23, x17, #32
 add x17, x23, x17
 lsr x23, x17, #32
 subs x23, x23, x17
 sbc x22, x17, xzr
 extr x23, x22, x23, #32
 lsr x22, x22, #32
 adds x22, x22, x17
 adc x21, xzr, xzr
 subs x19, x19, x23
 sbcs x20, x20, x22
 sbcs x1, x1, x21
 sbcs x15, x15, xzr
 sbcs x16, x16, xzr
 sbc x17, x17, xzr

        adds x9, x9, x15
        adcs x10, x10, x16
        adcs x11, x11, x17
        adc x12, x12, xzr







        add x22, x12, #1
        lsl x21, x22, #32
        subs x24, x22, x21
        sbc x21, x21, xzr

        adds x19, x19, x24
        adcs x20, x20, x21
        adcs x1, x1, x22
        adcs x9, x9, xzr
        adcs x10, x10, xzr
        adcs x11, x11, xzr

        csetm x22, cc

        mov x23, #0x00000000ffffffff
        and x23, x23, x22
        adds x19, x19, x23
        eor x23, x23, x22
        adcs x20, x20, x23
        mov x23, #0xfffffffffffffffe
        and x23, x23, x22
        adcs x1, x1, x23
        adcs x9, x9, x22
        adcs x10, x10, x22
        adc x11, x11, x22



        stp x19, x20, [x0]
        stp x1, x9, [x0, #16]
        stp x10, x11, [x0, #32]



        ldp x23, x24, [sp], #16
        ldp x21, x22, [sp], #16
        ldp x19, x20, [sp], #16

        ret
