# 1 "/Users/milaaws/Desktop/official_AWS-LC-SHA3/aws-lc/third_party/s2n-bignum/arm/p521/bignum_tolebytes_p521.S"
# 1 "<built-in>" 1
# 1 "/Users/milaaws/Desktop/official_AWS-LC-SHA3/aws-lc/third_party/s2n-bignum/arm/p521/bignum_tolebytes_p521.S" 2
# 28 "/Users/milaaws/Desktop/official_AWS-LC-SHA3/aws-lc/third_party/s2n-bignum/arm/p521/bignum_tolebytes_p521.S"
        .globl bignum_tolebytes_p521
        .globl _bignum_tolebytes_p521
        .text
        .balign 4







bignum_tolebytes_p521:
_bignum_tolebytes_p521:



        ldr x2, [x1]
        strb w2, [x0]
        lsr x2, x2, #8
        strb w2, [x0, #1]
        lsr x2, x2, #8
        strb w2, [x0, #2]
        lsr x2, x2, #8
        strb w2, [x0, #3]
        lsr x2, x2, #8
        strb w2, [x0, #4]
        lsr x2, x2, #8
        strb w2, [x0, #5]
        lsr x2, x2, #8
        strb w2, [x0, #6]
        lsr x2, x2, #8
        strb w2, [x0, #7]



        ldr x2, [x1, #8]
        strb w2, [x0, #8]
        lsr x2, x2, #8
        strb w2, [x0, #9]
        lsr x2, x2, #8
        strb w2, [x0, #10]
        lsr x2, x2, #8
        strb w2, [x0, #11]
        lsr x2, x2, #8
        strb w2, [x0, #12]
        lsr x2, x2, #8
        strb w2, [x0, #13]
        lsr x2, x2, #8
        strb w2, [x0, #14]
        lsr x2, x2, #8
        strb w2, [x0, #15]



        ldr x2, [x1, #16]
        strb w2, [x0, #16]
        lsr x2, x2, #8
        strb w2, [x0, #17]
        lsr x2, x2, #8
        strb w2, [x0, #18]
        lsr x2, x2, #8
        strb w2, [x0, #19]
        lsr x2, x2, #8
        strb w2, [x0, #20]
        lsr x2, x2, #8
        strb w2, [x0, #21]
        lsr x2, x2, #8
        strb w2, [x0, #22]
        lsr x2, x2, #8
        strb w2, [x0, #23]



        ldr x2, [x1, #24]
        strb w2, [x0, #24]
        lsr x2, x2, #8
        strb w2, [x0, #25]
        lsr x2, x2, #8
        strb w2, [x0, #26]
        lsr x2, x2, #8
        strb w2, [x0, #27]
        lsr x2, x2, #8
        strb w2, [x0, #28]
        lsr x2, x2, #8
        strb w2, [x0, #29]
        lsr x2, x2, #8
        strb w2, [x0, #30]
        lsr x2, x2, #8
        strb w2, [x0, #31]



        ldr x2, [x1, #32]
        strb w2, [x0, #32]
        lsr x2, x2, #8
        strb w2, [x0, #33]
        lsr x2, x2, #8
        strb w2, [x0, #34]
        lsr x2, x2, #8
        strb w2, [x0, #35]
        lsr x2, x2, #8
        strb w2, [x0, #36]
        lsr x2, x2, #8
        strb w2, [x0, #37]
        lsr x2, x2, #8
        strb w2, [x0, #38]
        lsr x2, x2, #8
        strb w2, [x0, #39]



        ldr x2, [x1, #40]
        strb w2, [x0, #40]
        lsr x2, x2, #8
        strb w2, [x0, #41]
        lsr x2, x2, #8
        strb w2, [x0, #42]
        lsr x2, x2, #8
        strb w2, [x0, #43]
        lsr x2, x2, #8
        strb w2, [x0, #44]
        lsr x2, x2, #8
        strb w2, [x0, #45]
        lsr x2, x2, #8
        strb w2, [x0, #46]
        lsr x2, x2, #8
        strb w2, [x0, #47]



        ldr x2, [x1, #48]
        strb w2, [x0, #48]
        lsr x2, x2, #8
        strb w2, [x0, #49]
        lsr x2, x2, #8
        strb w2, [x0, #50]
        lsr x2, x2, #8
        strb w2, [x0, #51]
        lsr x2, x2, #8
        strb w2, [x0, #52]
        lsr x2, x2, #8
        strb w2, [x0, #53]
        lsr x2, x2, #8
        strb w2, [x0, #54]
        lsr x2, x2, #8
        strb w2, [x0, #55]



        ldr x2, [x1, #56]
        strb w2, [x0, #56]
        lsr x2, x2, #8
        strb w2, [x0, #57]
        lsr x2, x2, #8
        strb w2, [x0, #58]
        lsr x2, x2, #8
        strb w2, [x0, #59]
        lsr x2, x2, #8
        strb w2, [x0, #60]
        lsr x2, x2, #8
        strb w2, [x0, #61]
        lsr x2, x2, #8
        strb w2, [x0, #62]
        lsr x2, x2, #8
        strb w2, [x0, #63]



        ldr x2, [x1, #64]
        strb w2, [x0, #64]
        lsr x2, x2, #8
        strb w2, [x0, #65]

        ret
