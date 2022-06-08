# 1 "/Users/milaaws/Desktop/official_AWS-LC-SHA3/aws-lc/third_party/s2n-bignum/arm/p384/bignum_deamont_p384.S"
# 1 "<built-in>" 1
# 1 "/Users/milaaws/Desktop/official_AWS-LC-SHA3/aws-lc/third_party/s2n-bignum/arm/p384/bignum_deamont_p384.S" 2
# 29 "/Users/milaaws/Desktop/official_AWS-LC-SHA3/aws-lc/third_party/s2n-bignum/arm/p384/bignum_deamont_p384.S"
        .globl bignum_deamont_p384
        .globl _bignum_deamont_p384
        .globl bignum_deamont_p384_alt
        .globl _bignum_deamont_p384_alt
        .text
        .balign 4
# 93 "/Users/milaaws/Desktop/official_AWS-LC-SHA3/aws-lc/third_party/s2n-bignum/arm/p384/bignum_deamont_p384.S"
bignum_deamont_p384:
_bignum_deamont_p384:
bignum_deamont_p384_alt:
_bignum_deamont_p384_alt:



        ldp x2, x3, [x1]
        ldp x4, x5, [x1, #16]
        ldp x6, x7, [x1, #32]



        lsl x10, x2, #32
 add x2, x10, x2
 lsr x10, x2, #32
 subs x10, x10, x2
 sbc x9, x2, xzr
 extr x10, x9, x10, #32
 lsr x9, x9, #32
 adds x9, x9, x2
 adc x8, xzr, xzr
 subs x3, x3, x10
 sbcs x4, x4, x9
 sbcs x5, x5, x8
 sbcs x6, x6, xzr
 sbcs x7, x7, xzr
 sbc x2, x2, xzr

        lsl x10, x3, #32
 add x3, x10, x3
 lsr x10, x3, #32
 subs x10, x10, x3
 sbc x9, x3, xzr
 extr x10, x9, x10, #32
 lsr x9, x9, #32
 adds x9, x9, x3
 adc x8, xzr, xzr
 subs x4, x4, x10
 sbcs x5, x5, x9
 sbcs x6, x6, x8
 sbcs x7, x7, xzr
 sbcs x2, x2, xzr
 sbc x3, x3, xzr

        lsl x10, x4, #32
 add x4, x10, x4
 lsr x10, x4, #32
 subs x10, x10, x4
 sbc x9, x4, xzr
 extr x10, x9, x10, #32
 lsr x9, x9, #32
 adds x9, x9, x4
 adc x8, xzr, xzr
 subs x5, x5, x10
 sbcs x6, x6, x9
 sbcs x7, x7, x8
 sbcs x2, x2, xzr
 sbcs x3, x3, xzr
 sbc x4, x4, xzr

        lsl x10, x5, #32
 add x5, x10, x5
 lsr x10, x5, #32
 subs x10, x10, x5
 sbc x9, x5, xzr
 extr x10, x9, x10, #32
 lsr x9, x9, #32
 adds x9, x9, x5
 adc x8, xzr, xzr
 subs x6, x6, x10
 sbcs x7, x7, x9
 sbcs x2, x2, x8
 sbcs x3, x3, xzr
 sbcs x4, x4, xzr
 sbc x5, x5, xzr

        lsl x10, x6, #32
 add x6, x10, x6
 lsr x10, x6, #32
 subs x10, x10, x6
 sbc x9, x6, xzr
 extr x10, x9, x10, #32
 lsr x9, x9, #32
 adds x9, x9, x6
 adc x8, xzr, xzr
 subs x7, x7, x10
 sbcs x2, x2, x9
 sbcs x3, x3, x8
 sbcs x4, x4, xzr
 sbcs x5, x5, xzr
 sbc x6, x6, xzr

        lsl x10, x7, #32
 add x7, x10, x7
 lsr x10, x7, #32
 subs x10, x10, x7
 sbc x9, x7, xzr
 extr x10, x9, x10, #32
 lsr x9, x9, #32
 adds x9, x9, x7
 adc x8, xzr, xzr
 subs x2, x2, x10
 sbcs x3, x3, x9
 sbcs x4, x4, x8
 sbcs x5, x5, xzr
 sbcs x6, x6, xzr
 sbc x7, x7, xzr





        mov x8, #0xffffffff00000001
        mov x9, #0x00000000ffffffff
        mov x10, #0x0000000000000001

        adds xzr, x2, x8
        adcs xzr, x3, x9
        adcs xzr, x4, x10
        adcs xzr, x5, xzr
        adcs xzr, x6, xzr
        adcs xzr, x7, xzr




        csetm x10, cs
        and x8, x8, x10
        adds x2, x2, x8
        and x9, x9, x10
        adcs x3, x3, x9
        and x10, x10, #1
        adcs x4, x4, x10
        adcs x5, x5, xzr
        adcs x6, x6, xzr
        adc x7, x7, xzr



        stp x2, x3, [x0]
        stp x4, x5, [x0, #16]
        stp x6, x7, [x0, #32]

        ret
