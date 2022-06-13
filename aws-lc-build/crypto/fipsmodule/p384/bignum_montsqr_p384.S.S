# 1 "/Users/milaaws/Desktop/official_AWS-LC-SHA3/aws-lc/third_party/s2n-bignum/arm/p384/bignum_montsqr_p384.S"
# 1 "<built-in>" 1
# 1 "/Users/milaaws/Desktop/official_AWS-LC-SHA3/aws-lc/third_party/s2n-bignum/arm/p384/bignum_montsqr_p384.S" 2
# 29 "/Users/milaaws/Desktop/official_AWS-LC-SHA3/aws-lc/third_party/s2n-bignum/arm/p384/bignum_montsqr_p384.S"
        .globl bignum_montsqr_p384
        .globl _bignum_montsqr_p384
        .text
        .balign 4
# 107 "/Users/milaaws/Desktop/official_AWS-LC-SHA3/aws-lc/third_party/s2n-bignum/arm/p384/bignum_montsqr_p384.S"
bignum_montsqr_p384:
_bignum_montsqr_p384:



        ldp x2, x3, [x1]
        ldp x4, x5, [x1, #16]
        ldp x6, x7, [x1, #32]



        mul x14, x2, x3
        mul x15, x2, x4
        mul x16, x3, x4
        mul x8, x2, x2
        mul x10, x3, x3
        mul x12, x4, x4

        umulh x17, x2, x3
        adds x15, x15, x17
        umulh x17, x2, x4
        adcs x16, x16, x17
        umulh x17, x3, x4
        adcs x17, x17, xzr

        umulh x9, x2, x2
        umulh x11, x3, x3
        umulh x13, x4, x4

        adds x14, x14, x14
        adcs x15, x15, x15
        adcs x16, x16, x16
        adcs x17, x17, x17
        adc x13, x13, xzr

        adds x9, x9, x14
        adcs x10, x10, x15
        adcs x11, x11, x16
        adcs x12, x12, x17
        adc x13, x13, xzr





        lsl x16, x8, #32
 add x8, x16, x8
 lsr x16, x8, #32
 subs x16, x16, x8
 sbc x15, x8, xzr
 extr x16, x15, x16, #32
 lsr x15, x15, #32
 adds x15, x15, x8
 adc x14, xzr, xzr
 subs x9, x9, x16
 sbcs x10, x10, x15
 sbcs x11, x11, x14
 sbcs x12, x12, xzr
 sbcs x13, x13, xzr
 sbc x8, x8, xzr

        lsl x16, x9, #32
 add x9, x16, x9
 lsr x16, x9, #32
 subs x16, x16, x9
 sbc x15, x9, xzr
 extr x16, x15, x16, #32
 lsr x15, x15, #32
 adds x15, x15, x9
 adc x14, xzr, xzr
 subs x10, x10, x16
 sbcs x11, x11, x15
 sbcs x12, x12, x14
 sbcs x13, x13, xzr
 sbcs x8, x8, xzr
 sbc x9, x9, xzr

        lsl x16, x10, #32
 add x10, x16, x10
 lsr x16, x10, #32
 subs x16, x16, x10
 sbc x15, x10, xzr
 extr x16, x15, x16, #32
 lsr x15, x15, #32
 adds x15, x15, x10
 adc x14, xzr, xzr
 subs x11, x11, x16
 sbcs x12, x12, x15
 sbcs x13, x13, x14
 sbcs x8, x8, xzr
 sbcs x9, x9, xzr
 sbc x10, x10, xzr

        stp x11, x12, [x0]
        stp x13, x8, [x0, #16]
        stp x9, x10, [x0, #32]
# 189 "/Users/milaaws/Desktop/official_AWS-LC-SHA3/aws-lc/third_party/s2n-bignum/arm/p384/bignum_montsqr_p384.S"
        mul x8, x2, x5
        mul x14, x3, x6
        mul x15, x4, x7
        umulh x16, x2, x5
        umulh x17, x3, x6
        umulh x1, x4, x7

        adds x16, x16, x14
        adcs x17, x17, x15
        adc x1, x1, xzr

        adds x9, x16, x8
        adcs x10, x17, x16
        adcs x11, x1, x17
        adc x12, x1, xzr

        adds x10, x10, x8
        adcs x11, x11, x16
        adcs x12, x12, x17
        adc x13, x1, xzr

        subs x17, x2, x3
 cneg x17, x17, cc
 csetm x14, cc
 subs x15, x6, x5
 cneg x15, x15, cc
 mul x16, x17, x15
 umulh x15, x17, x15
 cinv x14, x14, cc
 eor x16, x16, x14
 eor x15, x15, x14
        adds xzr, x14, #1
        adcs x9, x9, x16
        adcs x10, x10, x15
        adcs x11, x11, x14
        adcs x12, x12, x14
        adc x13, x13, x14

        subs x17, x2, x4
 cneg x17, x17, cc
 csetm x14, cc
 subs x15, x7, x5
 cneg x15, x15, cc
 mul x16, x17, x15
 umulh x15, x17, x15
 cinv x14, x14, cc
 eor x16, x16, x14
 eor x15, x15, x14
        adds xzr, x14, #1
        adcs x10, x10, x16
        adcs x11, x11, x15
        adcs x12, x12, x14
        adc x13, x13, x14

        subs x17, x3, x4
 cneg x17, x17, cc
 csetm x14, cc
 subs x15, x7, x6
 cneg x15, x15, cc
 mul x16, x17, x15
 umulh x15, x17, x15
 cinv x14, x14, cc
 eor x16, x16, x14
 eor x15, x15, x14
        adds xzr, x14, #1
        adcs x11, x11, x16
        adcs x12, x12, x15
        adc x13, x13, x14



        adds x8, x8, x8
        adcs x9, x9, x9
        adcs x10, x10, x10
        adcs x11, x11, x11
        adcs x12, x12, x12
        adcs x13, x13, x13
        adc x17, xzr, xzr

        ldp x2, x3, [x0]
        adds x8, x8, x2
        adcs x9, x9, x3
        ldp x2, x3, [x0, #16]
        adcs x10, x10, x2
        adcs x11, x11, x3
        ldp x2, x3, [x0, #32]
        adcs x12, x12, x2
        adcs x13, x13, x3
        adc x17, x17, xzr



        lsl x4, x8, #32
 add x8, x4, x8
 lsr x4, x8, #32
 subs x4, x4, x8
 sbc x3, x8, xzr
 extr x4, x3, x4, #32
 lsr x3, x3, #32
 adds x3, x3, x8
 adc x2, xzr, xzr
 subs x9, x9, x4
 sbcs x10, x10, x3
 sbcs x11, x11, x2
 sbcs x12, x12, xzr
 sbcs x13, x13, xzr
 sbc x8, x8, xzr

        lsl x4, x9, #32
 add x9, x4, x9
 lsr x4, x9, #32
 subs x4, x4, x9
 sbc x3, x9, xzr
 extr x4, x3, x4, #32
 lsr x3, x3, #32
 adds x3, x3, x9
 adc x2, xzr, xzr
 subs x10, x10, x4
 sbcs x11, x11, x3
 sbcs x12, x12, x2
 sbcs x13, x13, xzr
 sbcs x8, x8, xzr
 sbc x9, x9, xzr

        lsl x4, x10, #32
 add x10, x4, x10
 lsr x4, x10, #32
 subs x4, x4, x10
 sbc x3, x10, xzr
 extr x4, x3, x4, #32
 lsr x3, x3, #32
 adds x3, x3, x10
 adc x2, xzr, xzr
 subs x11, x11, x4
 sbcs x12, x12, x3
 sbcs x13, x13, x2
 sbcs x8, x8, xzr
 sbcs x9, x9, xzr
 sbc x10, x10, xzr

        adds x17, x17, x8
        adcs x8, x9, xzr
        adcs x9, x10, xzr
        adcs x10, xzr, xzr
# 291 "/Users/milaaws/Desktop/official_AWS-LC-SHA3/aws-lc/third_party/s2n-bignum/arm/p384/bignum_montsqr_p384.S"
        mul x1, x5, x5
        adds x11, x11, x1
        mul x14, x6, x6
        mul x15, x7, x7
        umulh x1, x5, x5
        adcs x12, x12, x1
        umulh x1, x6, x6
        adcs x13, x13, x14
        adcs x17, x17, x1
        umulh x1, x7, x7
        adcs x8, x8, x15
        adcs x9, x9, x1
        adc x10, x10, xzr



        mul x1, x5, x6
        mul x14, x5, x7
        mul x15, x6, x7
        umulh x16, x5, x6
        adds x14, x14, x16
        umulh x16, x5, x7
        adcs x15, x15, x16
        umulh x16, x6, x7
        adc x16, x16, xzr





        adds x1, x1, x1
        adcs x14, x14, x14
        adcs x15, x15, x15
        adcs x16, x16, x16
        adc x5, xzr, xzr

        adds x12, x12, x1
        adcs x13, x13, x14
        adcs x17, x17, x15
        adcs x8, x8, x16
        adcs x9, x9, x5
        adc x10, x10, xzr
# 341 "/Users/milaaws/Desktop/official_AWS-LC-SHA3/aws-lc/third_party/s2n-bignum/arm/p384/bignum_montsqr_p384.S"
        mov x1, #0xffffffff00000001
        mov x14, #0x00000000ffffffff
        mov x15, #0x0000000000000001




        adds xzr, x11, x1
        adcs xzr, x12, x14
        adcs xzr, x13, x15
        adcs xzr, x17, xzr
        adcs xzr, x8, xzr
        adcs xzr, x9, xzr




        adc x10, x10, xzr



        sub x10, xzr, x10



        and x1, x1, x10
        adds x11, x11, x1
        and x14, x14, x10
        adcs x12, x12, x14
        and x15, x15, x10
        adcs x13, x13, x15
        adcs x17, x17, xzr
        adcs x8, x8, xzr
        adc x9, x9, xzr



        stp x11, x12, [x0]
        stp x13, x17, [x0, #16]
        stp x8, x9, [x0, #32]

        ret
