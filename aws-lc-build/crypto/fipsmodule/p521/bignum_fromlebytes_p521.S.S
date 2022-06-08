# 1 "/Users/milaaws/Desktop/official_AWS-LC-SHA3/aws-lc/third_party/s2n-bignum/arm/p521/bignum_fromlebytes_p521.S"
# 1 "<built-in>" 1
# 1 "/Users/milaaws/Desktop/official_AWS-LC-SHA3/aws-lc/third_party/s2n-bignum/arm/p521/bignum_fromlebytes_p521.S" 2
# 28 "/Users/milaaws/Desktop/official_AWS-LC-SHA3/aws-lc/third_party/s2n-bignum/arm/p521/bignum_fromlebytes_p521.S"
        .globl bignum_fromlebytes_p521
        .globl _bignum_fromlebytes_p521
        .text
        .balign 4
# 40 "/Users/milaaws/Desktop/official_AWS-LC-SHA3/aws-lc/third_party/s2n-bignum/arm/p521/bignum_fromlebytes_p521.S"
bignum_fromlebytes_p521:
_bignum_fromlebytes_p521:



        ldrb w2, [x1]
        extr x3, x2, xzr, #8
        ldrb w2, [x1, #1]
        extr x3, x2, x3, #8
        ldrb w2, [x1, #2]
        extr x3, x2, x3, #8
        ldrb w2, [x1, #3]
        extr x3, x2, x3, #8
        ldrb w2, [x1, #4]
        extr x3, x2, x3, #8
        ldrb w2, [x1, #5]
        extr x3, x2, x3, #8
        ldrb w2, [x1, #6]
        extr x3, x2, x3, #8
        ldrb w2, [x1, #7]
        extr x3, x2, x3, #8
        str x3, [x0]



        ldrb w2, [x1, #8]
        extr x3, x2, xzr, #8
        ldrb w2, [x1, #9]
        extr x3, x2, x3, #8
        ldrb w2, [x1, #10]
        extr x3, x2, x3, #8
        ldrb w2, [x1, #11]
        extr x3, x2, x3, #8
        ldrb w2, [x1, #12]
        extr x3, x2, x3, #8
        ldrb w2, [x1, #13]
        extr x3, x2, x3, #8
        ldrb w2, [x1, #14]
        extr x3, x2, x3, #8
        ldrb w2, [x1, #15]
        extr x3, x2, x3, #8
        str x3, [x0, #8]



        ldrb w2, [x1, #16]
        extr x3, x2, xzr, #8
        ldrb w2, [x1, #17]
        extr x3, x2, x3, #8
        ldrb w2, [x1, #18]
        extr x3, x2, x3, #8
        ldrb w2, [x1, #19]
        extr x3, x2, x3, #8
        ldrb w2, [x1, #20]
        extr x3, x2, x3, #8
        ldrb w2, [x1, #21]
        extr x3, x2, x3, #8
        ldrb w2, [x1, #22]
        extr x3, x2, x3, #8
        ldrb w2, [x1, #23]
        extr x3, x2, x3, #8
        str x3, [x0, #16]



        ldrb w2, [x1, #24]
        extr x3, x2, xzr, #8
        ldrb w2, [x1, #25]
        extr x3, x2, x3, #8
        ldrb w2, [x1, #26]
        extr x3, x2, x3, #8
        ldrb w2, [x1, #27]
        extr x3, x2, x3, #8
        ldrb w2, [x1, #28]
        extr x3, x2, x3, #8
        ldrb w2, [x1, #29]
        extr x3, x2, x3, #8
        ldrb w2, [x1, #30]
        extr x3, x2, x3, #8
        ldrb w2, [x1, #31]
        extr x3, x2, x3, #8
        str x3, [x0, #24]



        ldrb w2, [x1, #32]
        extr x3, x2, xzr, #8
        ldrb w2, [x1, #33]
        extr x3, x2, x3, #8
        ldrb w2, [x1, #34]
        extr x3, x2, x3, #8
        ldrb w2, [x1, #35]
        extr x3, x2, x3, #8
        ldrb w2, [x1, #36]
        extr x3, x2, x3, #8
        ldrb w2, [x1, #37]
        extr x3, x2, x3, #8
        ldrb w2, [x1, #38]
        extr x3, x2, x3, #8
        ldrb w2, [x1, #39]
        extr x3, x2, x3, #8
        str x3, [x0, #32]



        ldrb w2, [x1, #40]
        extr x3, x2, xzr, #8
        ldrb w2, [x1, #41]
        extr x3, x2, x3, #8
        ldrb w2, [x1, #42]
        extr x3, x2, x3, #8
        ldrb w2, [x1, #43]
        extr x3, x2, x3, #8
        ldrb w2, [x1, #44]
        extr x3, x2, x3, #8
        ldrb w2, [x1, #45]
        extr x3, x2, x3, #8
        ldrb w2, [x1, #46]
        extr x3, x2, x3, #8
        ldrb w2, [x1, #47]
        extr x3, x2, x3, #8
        str x3, [x0, #40]



        ldrb w2, [x1, #48]
        extr x3, x2, xzr, #8
        ldrb w2, [x1, #49]
        extr x3, x2, x3, #8
        ldrb w2, [x1, #50]
        extr x3, x2, x3, #8
        ldrb w2, [x1, #51]
        extr x3, x2, x3, #8
        ldrb w2, [x1, #52]
        extr x3, x2, x3, #8
        ldrb w2, [x1, #53]
        extr x3, x2, x3, #8
        ldrb w2, [x1, #54]
        extr x3, x2, x3, #8
        ldrb w2, [x1, #55]
        extr x3, x2, x3, #8
        str x3, [x0, #48]



        ldrb w2, [x1, #56]
        extr x3, x2, xzr, #8
        ldrb w2, [x1, #57]
        extr x3, x2, x3, #8
        ldrb w2, [x1, #58]
        extr x3, x2, x3, #8
        ldrb w2, [x1, #59]
        extr x3, x2, x3, #8
        ldrb w2, [x1, #60]
        extr x3, x2, x3, #8
        ldrb w2, [x1, #61]
        extr x3, x2, x3, #8
        ldrb w2, [x1, #62]
        extr x3, x2, x3, #8
        ldrb w2, [x1, #63]
        extr x3, x2, x3, #8
        str x3, [x0, #56]



        ldrb w2, [x1, #64]
        extr x3, x2, xzr, #8
        ldrb w2, [x1, #65]
        extr x3, x2, x3, #56
        str x3, [x0, #64]

        ret
