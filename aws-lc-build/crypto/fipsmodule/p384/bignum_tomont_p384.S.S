# 1 "/Users/milaaws/Desktop/official_AWS-LC-SHA3/aws-lc/third_party/s2n-bignum/arm/p384/bignum_tomont_p384.S"
# 1 "<built-in>" 1
# 1 "/Users/milaaws/Desktop/official_AWS-LC-SHA3/aws-lc/third_party/s2n-bignum/arm/p384/bignum_tomont_p384.S" 2
# 26 "/Users/milaaws/Desktop/official_AWS-LC-SHA3/aws-lc/third_party/s2n-bignum/arm/p384/bignum_tomont_p384.S"
        .globl bignum_tomont_p384
        .globl _bignum_tomont_p384
        .globl bignum_tomont_p384_alt
        .globl _bignum_tomont_p384_alt
        .text
        .balign 4
# 75 "/Users/milaaws/Desktop/official_AWS-LC-SHA3/aws-lc/third_party/s2n-bignum/arm/p384/bignum_tomont_p384.S"
bignum_tomont_p384:
_bignum_tomont_p384:
bignum_tomont_p384_alt:
_bignum_tomont_p384_alt:
# 101 "/Users/milaaws/Desktop/official_AWS-LC-SHA3/aws-lc/third_party/s2n-bignum/arm/p384/bignum_tomont_p384.S"
        ldp x2, x3, [x1]
        ldp x4, x5, [x1, #16]
        ldp x6, x7, [x1, #32]





        mov x8, #0x00000000ffffffff
        mov x9, #0xffffffff00000000
        mov x10, #0xfffffffffffffffe
        subs x8, x2, x8
        sbcs x9, x3, x9
        sbcs x10, x4, x10
        adcs x11, x5, xzr
        adcs x12, x6, xzr
        adcs x1, x7, xzr
        csel x2, x2, x8, cc
        csel x3, x3, x9, cc
        csel x4, x4, x10, cc
        csel x5, x5, x11, cc
        csel x6, x6, x12, cc
        csel x7, x7, x1, cc



        adds x7, x7, #1
 csetm x11, cs
 add x7, x7, x11
 orn x11, xzr, x11
 sub x10, x7, #1
 sub x9, xzr, x7
 lsl x8, x9, #32
 extr x9, x10, x9, #32
 lsr x10, x10, #32
 adds x8, x8, x7
 adcs x9, x9, xzr
 adcs x10, x10, x7
 adc x7, xzr, xzr
 adds x2, x2, x9
 adcs x3, x3, x10
 adcs x4, x4, x7
 adcs x5, x5, xzr
 adcs x6, x6, xzr
 adc x11, x11, xzr
 mov x9, #0x00000000ffffffff
 and x9, x9, x11
 adds x8, x8, x9
 eor x9, x9, x11
 adcs x2, x2, x9
 mov x9, #0xfffffffffffffffe
 and x9, x9, x11
 adcs x3, x3, x9
 adcs x4, x4, x11
 adcs x5, x5, x11
 adc x6, x6, x11
        adds x6, x6, #1
 csetm x11, cs
 add x6, x6, x11
 orn x11, xzr, x11
 sub x10, x6, #1
 sub x9, xzr, x6
 lsl x7, x9, #32
 extr x9, x10, x9, #32
 lsr x10, x10, #32
 adds x7, x7, x6
 adcs x9, x9, xzr
 adcs x10, x10, x6
 adc x6, xzr, xzr
 adds x8, x8, x9
 adcs x2, x2, x10
 adcs x3, x3, x6
 adcs x4, x4, xzr
 adcs x5, x5, xzr
 adc x11, x11, xzr
 mov x9, #0x00000000ffffffff
 and x9, x9, x11
 adds x7, x7, x9
 eor x9, x9, x11
 adcs x8, x8, x9
 mov x9, #0xfffffffffffffffe
 and x9, x9, x11
 adcs x2, x2, x9
 adcs x3, x3, x11
 adcs x4, x4, x11
 adc x5, x5, x11
        adds x5, x5, #1
 csetm x11, cs
 add x5, x5, x11
 orn x11, xzr, x11
 sub x10, x5, #1
 sub x9, xzr, x5
 lsl x6, x9, #32
 extr x9, x10, x9, #32
 lsr x10, x10, #32
 adds x6, x6, x5
 adcs x9, x9, xzr
 adcs x10, x10, x5
 adc x5, xzr, xzr
 adds x7, x7, x9
 adcs x8, x8, x10
 adcs x2, x2, x5
 adcs x3, x3, xzr
 adcs x4, x4, xzr
 adc x11, x11, xzr
 mov x9, #0x00000000ffffffff
 and x9, x9, x11
 adds x6, x6, x9
 eor x9, x9, x11
 adcs x7, x7, x9
 mov x9, #0xfffffffffffffffe
 and x9, x9, x11
 adcs x8, x8, x9
 adcs x2, x2, x11
 adcs x3, x3, x11
 adc x4, x4, x11
        adds x4, x4, #1
 csetm x11, cs
 add x4, x4, x11
 orn x11, xzr, x11
 sub x10, x4, #1
 sub x9, xzr, x4
 lsl x5, x9, #32
 extr x9, x10, x9, #32
 lsr x10, x10, #32
 adds x5, x5, x4
 adcs x9, x9, xzr
 adcs x10, x10, x4
 adc x4, xzr, xzr
 adds x6, x6, x9
 adcs x7, x7, x10
 adcs x8, x8, x4
 adcs x2, x2, xzr
 adcs x3, x3, xzr
 adc x11, x11, xzr
 mov x9, #0x00000000ffffffff
 and x9, x9, x11
 adds x5, x5, x9
 eor x9, x9, x11
 adcs x6, x6, x9
 mov x9, #0xfffffffffffffffe
 and x9, x9, x11
 adcs x7, x7, x9
 adcs x8, x8, x11
 adcs x2, x2, x11
 adc x3, x3, x11
        adds x3, x3, #1
 csetm x11, cs
 add x3, x3, x11
 orn x11, xzr, x11
 sub x10, x3, #1
 sub x9, xzr, x3
 lsl x4, x9, #32
 extr x9, x10, x9, #32
 lsr x10, x10, #32
 adds x4, x4, x3
 adcs x9, x9, xzr
 adcs x10, x10, x3
 adc x3, xzr, xzr
 adds x5, x5, x9
 adcs x6, x6, x10
 adcs x7, x7, x3
 adcs x8, x8, xzr
 adcs x2, x2, xzr
 adc x11, x11, xzr
 mov x9, #0x00000000ffffffff
 and x9, x9, x11
 adds x4, x4, x9
 eor x9, x9, x11
 adcs x5, x5, x9
 mov x9, #0xfffffffffffffffe
 and x9, x9, x11
 adcs x6, x6, x9
 adcs x7, x7, x11
 adcs x8, x8, x11
 adc x2, x2, x11
        adds x2, x2, #1
 csetm x11, cs
 add x2, x2, x11
 orn x11, xzr, x11
 sub x10, x2, #1
 sub x9, xzr, x2
 lsl x3, x9, #32
 extr x9, x10, x9, #32
 lsr x10, x10, #32
 adds x3, x3, x2
 adcs x9, x9, xzr
 adcs x10, x10, x2
 adc x2, xzr, xzr
 adds x4, x4, x9
 adcs x5, x5, x10
 adcs x6, x6, x2
 adcs x7, x7, xzr
 adcs x8, x8, xzr
 adc x11, x11, xzr
 mov x9, #0x00000000ffffffff
 and x9, x9, x11
 adds x3, x3, x9
 eor x9, x9, x11
 adcs x4, x4, x9
 mov x9, #0xfffffffffffffffe
 and x9, x9, x11
 adcs x5, x5, x9
 adcs x6, x6, x11
 adcs x7, x7, x11
 adc x8, x8, x11



        stp x3, x4, [x0]
        stp x5, x6, [x0, #16]
        stp x7, x8, [x0, #32]

        ret
