# 1 "/Users/milaaws/Desktop/official_AWS-LC-SHA3/aws-lc/third_party/s2n-bignum/arm/p521/bignum_mul_p521.S"
# 1 "<built-in>" 1
# 1 "/Users/milaaws/Desktop/official_AWS-LC-SHA3/aws-lc/third_party/s2n-bignum/arm/p521/bignum_mul_p521.S" 2
# 26 "/Users/milaaws/Desktop/official_AWS-LC-SHA3/aws-lc/third_party/s2n-bignum/arm/p521/bignum_mul_p521.S"
        .globl bignum_mul_p521
        .globl _bignum_mul_p521
        .text
        .balign 4
# 156 "/Users/milaaws/Desktop/official_AWS-LC-SHA3/aws-lc/third_party/s2n-bignum/arm/p521/bignum_mul_p521.S"
bignum_mul_p521:
_bignum_mul_p521:



        stp x19, x20, [sp, #-16]!
        stp x21, x22, [sp, #-16]!
        stp x23, x24, [sp, #-16]!
        stp x25, x26, [sp, #-16]!
        sub sp, sp, #80



        ldp x3, x4, [x1]
        ldp x5, x6, [x1, #16]
        ldp x7, x8, [x2]
        ldp x9, x10, [x2, #16]
        mul x11, x3, x7
 mul x15, x4, x8
 mul x16, x5, x9
 mul x17, x6, x10
 umulh x19, x3, x7
 adds x15, x15, x19
 umulh x19, x4, x8
 adcs x16, x16, x19
 umulh x19, x5, x9
 adcs x17, x17, x19
 umulh x19, x6, x10
 adc x19, x19, xzr
 adds x12, x15, x11
 adcs x15, x16, x15
 adcs x16, x17, x16
 adcs x17, x19, x17
 adc x19, xzr, x19
 adds x13, x15, x11
 adcs x14, x16, x12
 adcs x15, x17, x15
 adcs x16, x19, x16
 adcs x17, xzr, x17
 adc x19, xzr, x19
 subs x24, x5, x6
 cneg x24, x24, cc
 csetm x21, cc
 subs x22, x10, x9
 cneg x22, x22, cc
 mul x23, x24, x22
 umulh x22, x24, x22
 cinv x21, x21, cc
 adds xzr, x21, #1
 eor x23, x23, x21
 adcs x16, x16, x23
 eor x22, x22, x21
 adcs x17, x17, x22
 adc x19, x19, x21
 subs x24, x3, x4
 cneg x24, x24, cc
 csetm x21, cc
 subs x22, x8, x7
 cneg x22, x22, cc
 mul x23, x24, x22
 umulh x22, x24, x22
 cinv x21, x21, cc
 adds xzr, x21, #1
 eor x23, x23, x21
 adcs x12, x12, x23
 eor x22, x22, x21
 adcs x13, x13, x22
 adcs x14, x14, x21
 adcs x15, x15, x21
 adcs x16, x16, x21
 adcs x17, x17, x21
 adc x19, x19, x21
 subs x24, x4, x6
 cneg x24, x24, cc
 csetm x21, cc
 subs x22, x10, x8
 cneg x22, x22, cc
 mul x23, x24, x22
 umulh x22, x24, x22
 cinv x21, x21, cc
 adds xzr, x21, #1
 eor x23, x23, x21
 adcs x15, x15, x23
 eor x22, x22, x21
 adcs x16, x16, x22
 adcs x17, x17, x21
 adc x19, x19, x21
 subs x24, x3, x5
 cneg x24, x24, cc
 csetm x21, cc
 subs x22, x9, x7
 cneg x22, x22, cc
 mul x23, x24, x22
 umulh x22, x24, x22
 cinv x21, x21, cc
 adds xzr, x21, #1
 eor x23, x23, x21
 adcs x13, x13, x23
 eor x22, x22, x21
 adcs x14, x14, x22
 adcs x15, x15, x21
 adcs x16, x16, x21
 adcs x17, x17, x21
 adc x19, x19, x21
 subs x24, x3, x6
 cneg x24, x24, cc
 csetm x21, cc
 subs x22, x10, x7
 cneg x22, x22, cc
 mul x23, x24, x22
 umulh x22, x24, x22
 cinv x21, x21, cc
 adds xzr, x21, #1
 eor x23, x23, x21
 adcs x14, x14, x23
 eor x22, x22, x21
 adcs x15, x15, x22
 adcs x16, x16, x21
 adcs x17, x17, x21
 adc x19, x19, x21
 subs x24, x4, x5
 cneg x24, x24, cc
 csetm x21, cc
 subs x22, x9, x8
 cneg x22, x22, cc
 mul x23, x24, x22
 umulh x22, x24, x22
 cinv x21, x21, cc
 adds xzr, x21, #1
 eor x23, x23, x21
 adcs x14, x14, x23
 eor x22, x22, x21
 adcs x15, x15, x22
 adcs x16, x16, x21
 adcs x17, x17, x21
 adc x19, x19, x21



        lsl x21, x11, #9
        extr x11, x12, x11, #55
        extr x12, x13, x12, #55
        extr x13, x14, x13, #55
        lsr x14, x14, #55
        stp x15, x16, [sp]
        stp x17, x19, [sp, #16]
        stp x21, x11, [sp, #32]
        stp x12, x13, [sp, #48]
        str x14, [sp, #64]



        ldp x3, x4, [x1, #32]
        ldp x5, x6, [x1, #48]
        ldp x7, x8, [x2, #32]
        ldp x9, x10, [x2, #48]
        mul x11, x3, x7
 mul x15, x4, x8
 mul x16, x5, x9
 mul x17, x6, x10
 umulh x19, x3, x7
 adds x15, x15, x19
 umulh x19, x4, x8
 adcs x16, x16, x19
 umulh x19, x5, x9
 adcs x17, x17, x19
 umulh x19, x6, x10
 adc x19, x19, xzr
 adds x12, x15, x11
 adcs x15, x16, x15
 adcs x16, x17, x16
 adcs x17, x19, x17
 adc x19, xzr, x19
 adds x13, x15, x11
 adcs x14, x16, x12
 adcs x15, x17, x15
 adcs x16, x19, x16
 adcs x17, xzr, x17
 adc x19, xzr, x19
 subs x24, x5, x6
 cneg x24, x24, cc
 csetm x21, cc
 subs x22, x10, x9
 cneg x22, x22, cc
 mul x23, x24, x22
 umulh x22, x24, x22
 cinv x21, x21, cc
 adds xzr, x21, #1
 eor x23, x23, x21
 adcs x16, x16, x23
 eor x22, x22, x21
 adcs x17, x17, x22
 adc x19, x19, x21
 subs x24, x3, x4
 cneg x24, x24, cc
 csetm x21, cc
 subs x22, x8, x7
 cneg x22, x22, cc
 mul x23, x24, x22
 umulh x22, x24, x22
 cinv x21, x21, cc
 adds xzr, x21, #1
 eor x23, x23, x21
 adcs x12, x12, x23
 eor x22, x22, x21
 adcs x13, x13, x22
 adcs x14, x14, x21
 adcs x15, x15, x21
 adcs x16, x16, x21
 adcs x17, x17, x21
 adc x19, x19, x21
 subs x24, x4, x6
 cneg x24, x24, cc
 csetm x21, cc
 subs x22, x10, x8
 cneg x22, x22, cc
 mul x23, x24, x22
 umulh x22, x24, x22
 cinv x21, x21, cc
 adds xzr, x21, #1
 eor x23, x23, x21
 adcs x15, x15, x23
 eor x22, x22, x21
 adcs x16, x16, x22
 adcs x17, x17, x21
 adc x19, x19, x21
 subs x24, x3, x5
 cneg x24, x24, cc
 csetm x21, cc
 subs x22, x9, x7
 cneg x22, x22, cc
 mul x23, x24, x22
 umulh x22, x24, x22
 cinv x21, x21, cc
 adds xzr, x21, #1
 eor x23, x23, x21
 adcs x13, x13, x23
 eor x22, x22, x21
 adcs x14, x14, x22
 adcs x15, x15, x21
 adcs x16, x16, x21
 adcs x17, x17, x21
 adc x19, x19, x21
 subs x24, x3, x6
 cneg x24, x24, cc
 csetm x21, cc
 subs x22, x10, x7
 cneg x22, x22, cc
 mul x23, x24, x22
 umulh x22, x24, x22
 cinv x21, x21, cc
 adds xzr, x21, #1
 eor x23, x23, x21
 adcs x14, x14, x23
 eor x22, x22, x21
 adcs x15, x15, x22
 adcs x16, x16, x21
 adcs x17, x17, x21
 adc x19, x19, x21
 subs x24, x4, x5
 cneg x24, x24, cc
 csetm x21, cc
 subs x22, x9, x8
 cneg x22, x22, cc
 mul x23, x24, x22
 umulh x22, x24, x22
 cinv x21, x21, cc
 adds xzr, x21, #1
 eor x23, x23, x21
 adcs x14, x14, x23
 eor x22, x22, x21
 adcs x15, x15, x22
 adcs x16, x16, x21
 adcs x17, x17, x21
 adc x19, x19, x21




        ldp x23, x22, [sp]
        adds x11, x11, x23
        adcs x12, x12, x22
        stp x11, x12, [sp]
        ldp x23, x22, [sp, #16]
        adcs x13, x13, x23
        adcs x14, x14, x22
        stp x13, x14, [sp, #16]
        ldp x23, x22, [sp, #32]
        adcs x15, x15, x23
        adcs x16, x16, x22
        stp x15, x16, [sp, #32]
        ldp x23, x22, [sp, #48]
        adcs x17, x17, x23
        adcs x19, x19, x22
        stp x17, x19, [sp, #48]
        ldr x21, [sp, #64]
        adc x21, x21, xzr
        str x21, [sp, #64]





        ldp x23, x22, [x1]
        subs x3, x3, x23
        sbcs x4, x4, x22
        ldp x23, x22, [x1, #16]
        sbcs x5, x5, x23
        sbcs x6, x6, x22
        csetm x24, cc
        ldp x23, x22, [x2]
        subs x7, x23, x7
        sbcs x8, x22, x8
        ldp x23, x22, [x2, #16]
        sbcs x9, x23, x9
        sbcs x10, x22, x10
        csetm x25, cc

        eor x3, x3, x24
        subs x3, x3, x24
        eor x4, x4, x24
        sbcs x4, x4, x24
        eor x5, x5, x24
        sbcs x5, x5, x24
        eor x6, x6, x24
        sbc x6, x6, x24

        eor x7, x7, x25
        subs x7, x7, x25
        eor x8, x8, x25
        sbcs x8, x8, x25
        eor x9, x9, x25
        sbcs x9, x9, x25
        eor x10, x10, x25
        sbc x10, x10, x25

        eor x25, x25, x24



        mul x11, x3, x7
 mul x15, x4, x8
 mul x16, x5, x9
 mul x17, x6, x10
 umulh x19, x3, x7
 adds x15, x15, x19
 umulh x19, x4, x8
 adcs x16, x16, x19
 umulh x19, x5, x9
 adcs x17, x17, x19
 umulh x19, x6, x10
 adc x19, x19, xzr
 adds x12, x15, x11
 adcs x15, x16, x15
 adcs x16, x17, x16
 adcs x17, x19, x17
 adc x19, xzr, x19
 adds x13, x15, x11
 adcs x14, x16, x12
 adcs x15, x17, x15
 adcs x16, x19, x16
 adcs x17, xzr, x17
 adc x19, xzr, x19
 subs x24, x5, x6
 cneg x24, x24, cc
 csetm x21, cc
 subs x22, x10, x9
 cneg x22, x22, cc
 mul x23, x24, x22
 umulh x22, x24, x22
 cinv x21, x21, cc
 adds xzr, x21, #1
 eor x23, x23, x21
 adcs x16, x16, x23
 eor x22, x22, x21
 adcs x17, x17, x22
 adc x19, x19, x21
 subs x24, x3, x4
 cneg x24, x24, cc
 csetm x21, cc
 subs x22, x8, x7
 cneg x22, x22, cc
 mul x23, x24, x22
 umulh x22, x24, x22
 cinv x21, x21, cc
 adds xzr, x21, #1
 eor x23, x23, x21
 adcs x12, x12, x23
 eor x22, x22, x21
 adcs x13, x13, x22
 adcs x14, x14, x21
 adcs x15, x15, x21
 adcs x16, x16, x21
 adcs x17, x17, x21
 adc x19, x19, x21
 subs x24, x4, x6
 cneg x24, x24, cc
 csetm x21, cc
 subs x22, x10, x8
 cneg x22, x22, cc
 mul x23, x24, x22
 umulh x22, x24, x22
 cinv x21, x21, cc
 adds xzr, x21, #1
 eor x23, x23, x21
 adcs x15, x15, x23
 eor x22, x22, x21
 adcs x16, x16, x22
 adcs x17, x17, x21
 adc x19, x19, x21
 subs x24, x3, x5
 cneg x24, x24, cc
 csetm x21, cc
 subs x22, x9, x7
 cneg x22, x22, cc
 mul x23, x24, x22
 umulh x22, x24, x22
 cinv x21, x21, cc
 adds xzr, x21, #1
 eor x23, x23, x21
 adcs x13, x13, x23
 eor x22, x22, x21
 adcs x14, x14, x22
 adcs x15, x15, x21
 adcs x16, x16, x21
 adcs x17, x17, x21
 adc x19, x19, x21
 subs x24, x3, x6
 cneg x24, x24, cc
 csetm x21, cc
 subs x22, x10, x7
 cneg x22, x22, cc
 mul x23, x24, x22
 umulh x22, x24, x22
 cinv x21, x21, cc
 adds xzr, x21, #1
 eor x23, x23, x21
 adcs x14, x14, x23
 eor x22, x22, x21
 adcs x15, x15, x22
 adcs x16, x16, x21
 adcs x17, x17, x21
 adc x19, x19, x21
 subs x24, x4, x5
 cneg x24, x24, cc
 csetm x21, cc
 subs x22, x9, x8
 cneg x22, x22, cc
 mul x23, x24, x22
 umulh x22, x24, x22
 cinv x21, x21, cc
 adds xzr, x21, #1
 eor x23, x23, x21
 adcs x14, x14, x23
 eor x22, x22, x21
 adcs x15, x15, x22
 adcs x16, x16, x21
 adcs x17, x17, x21
 adc x19, x19, x21
# 276 "/Users/milaaws/Desktop/official_AWS-LC-SHA3/aws-lc/third_party/s2n-bignum/arm/p521/bignum_mul_p521.S"
        ldp x3, x4, [sp]
        ldp x5, x6, [sp, #16]

        eor x11, x11, x25
        adds x11, x11, x3
        eor x12, x12, x25
        adcs x12, x12, x4
        eor x13, x13, x25
        adcs x13, x13, x5
        eor x14, x14, x25
        adcs x14, x14, x6
        eor x15, x15, x25

        ldp x7, x8, [sp, #32]
        ldp x9, x10, [sp, #48]
        ldr x20, [sp, #64]

        adcs x15, x15, x7
        eor x16, x16, x25
        adcs x16, x16, x8
        eor x17, x17, x25
        adcs x17, x17, x9
        eor x19, x19, x25
        adcs x19, x19, x10
        adc x21, x20, xzr

        adds x15, x15, x3
        adcs x16, x16, x4
        adcs x17, x17, x5
        adcs x19, x19, x6
        and x25, x25, #0x1FF
        lsl x24, x11, #9
        orr x24, x24, x25
        adcs x7, x7, x24
        extr x24, x12, x11, #55
        adcs x8, x8, x24
        extr x24, x13, x12, #55
        adcs x9, x9, x24
        extr x24, x14, x13, #55
        adcs x10, x10, x24
        lsr x24, x14, #55
        adc x20, x24, x20
# 364 "/Users/milaaws/Desktop/official_AWS-LC-SHA3/aws-lc/third_party/s2n-bignum/arm/p521/bignum_mul_p521.S"
        ldr x6, [x2, #64]
        ldp x3, x4, [x1]
        and x23, x3, #0x000fffffffffffff
        mul x23, x6, x23
        ldr x14, [x1, #64]
        ldp x11, x12, [x2]
        and x24, x11, #0x000fffffffffffff
        mul x24, x14, x24
        add x23, x23, x24



        extr x24, x4, x3, #52
        and x24, x24, #0x000fffffffffffff
        mul x22, x6, x24
        extr x24, x12, x11, #52
        and x24, x24, #0x000fffffffffffff
        mul x24, x14, x24
        add x22, x22, x24
        lsr x24, x23, #52
        add x22, x22, x24

        lsl x23, x23, #12
        extr x24, x22, x23, #12
        adds x15, x15, x24



        ldp x5, x3, [x1, #16]
        ldp x13, x11, [x2, #16]
        extr x24, x5, x4, #40
        and x24, x24, #0x000fffffffffffff
        mul x23, x6, x24
        extr x24, x13, x12, #40
        and x24, x24, #0x000fffffffffffff
        mul x24, x14, x24
        add x23, x23, x24
        lsr x24, x22, #52
        add x23, x23, x24

        lsl x22, x22, #12
        extr x24, x23, x22, #24
        adcs x16, x16, x24



        extr x24, x3, x5, #28
        and x24, x24, #0x000fffffffffffff
        mul x22, x6, x24
        extr x24, x11, x13, #28
        and x24, x24, #0x000fffffffffffff
        mul x24, x14, x24
        add x22, x22, x24
        lsr x24, x23, #52
        add x22, x22, x24

        lsl x23, x23, #12
        extr x24, x22, x23, #36
        adcs x17, x17, x24
        and x26, x16, x17





        ldp x4, x5, [x1, #32]
        ldp x12, x13, [x2, #32]
        extr x24, x4, x3, #16
        and x24, x24, #0x000fffffffffffff
        mul x23, x6, x24
        extr x24, x12, x11, #16
        and x24, x24, #0x000fffffffffffff
        mul x24, x14, x24
        add x23, x23, x24

        lsl x21, x21, #48
        add x23, x23, x21

        lsr x24, x22, #52
        add x23, x23, x24

        lsl x22, x22, #12
        extr x24, x23, x22, #48
        adcs x19, x19, x24
        and x26, x26, x19



        lsr x24, x4, #4
        and x24, x24, #0x000fffffffffffff
        mul x22, x6, x24
        lsr x24, x12, #4
        and x24, x24, #0x000fffffffffffff
        mul x24, x14, x24
        add x22, x22, x24

        lsr x24, x23, #52
        add x22, x22, x24

        lsl x23, x23, #12
        extr x25, x22, x23, #60



        extr x24, x5, x4, #56
        and x24, x24, #0x000fffffffffffff
        mul x23, x6, x24
        extr x24, x13, x12, #56
        and x24, x24, #0x000fffffffffffff
        mul x24, x14, x24
        add x23, x23, x24

        lsr x24, x22, #52
        add x23, x23, x24

        lsl x25, x25, #8
        extr x24, x23, x25, #8
        adcs x7, x7, x24
        and x26, x26, x7



        ldp x3, x4, [x1, #48]
        ldp x11, x12, [x2, #48]
        extr x24, x3, x5, #44
        and x24, x24, #0x000fffffffffffff
        mul x22, x6, x24
        extr x24, x11, x13, #44
        and x24, x24, #0x000fffffffffffff
        mul x24, x14, x24
        add x22, x22, x24

        lsr x24, x23, #52
        add x22, x22, x24

        lsl x23, x23, #12
        extr x24, x22, x23, #20
        adcs x8, x8, x24
        and x26, x26, x8



        extr x24, x4, x3, #32
        and x24, x24, #0x000fffffffffffff
        mul x23, x6, x24
        extr x24, x12, x11, #32
        and x24, x24, #0x000fffffffffffff
        mul x24, x14, x24
        add x23, x23, x24

        lsr x24, x22, #52
        add x23, x23, x24

        lsl x22, x22, #12
        extr x24, x23, x22, #32
        adcs x9, x9, x24
        and x26, x26, x9



        lsr x24, x4, #20
        mul x22, x6, x24
        lsr x24, x12, #20
        mul x24, x14, x24
        add x22, x22, x24

        lsr x24, x23, #52
        add x22, x22, x24

        lsl x23, x23, #12
        extr x24, x22, x23, #44
        adcs x10, x10, x24
        and x26, x26, x10



        mul x24, x6, x14
        lsr x22, x22, #44
        add x24, x24, x22
        adc x20, x20, x24




        lsr x22, x20, #9
        orr x20, x20, #~0x1FF






        subs xzr, xzr, xzr
        adcs xzr, x15, x22
        adcs xzr, x26, xzr
        adcs xzr, x20, xzr





        adcs x15, x15, x22
        adcs x16, x16, xzr
        adcs x17, x17, xzr
        adcs x19, x19, xzr
        adcs x7, x7, xzr
        adcs x8, x8, xzr
        adcs x9, x9, xzr
        adcs x10, x10, xzr
        adc x20, x20, xzr




        and x22, x15, #0x1FF
        extr x15, x16, x15, #9
        extr x16, x17, x16, #9
        stp x15, x16, [x0]
        extr x17, x19, x17, #9
        extr x19, x7, x19, #9
        stp x17, x19, [x0, #16]
        extr x7, x8, x7, #9
        extr x8, x9, x8, #9
        stp x7, x8, [x0, #32]
        extr x9, x10, x9, #9
        extr x10, x20, x10, #9
        stp x9, x10, [x0, #48]
        str x22, [x0, #64]



        add sp, sp, #80
        ldp x25, x26, [sp], #16
        ldp x23, x24, [sp], #16
        ldp x21, x22, [sp], #16
        ldp x19, x20, [sp], #16
        ret
