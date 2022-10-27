//------------------------------------------------------------------------------------
// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC
//------------------------------------------------------------------------------------

// int beeu_mod_inverse_vartime(uint64_t out[4],
//                              uint64_t a[4],
//                              uint64_t n[4]);
// Inputs and outputs are 256-bit values.
// computes
//    |out| = |a|^-1 mod n,
// where n is odd

// (Binary Extended GCD (Euclidean) Algorithm.
//  See A. Menezes, P. vanOorschot, and S. Vanstone's Handbook of Applied Cryptography,
//  Chapter 14, Algorithm 14.61 and Note 14.64
//  http://cacr.uwaterloo.ca/hac/about/chap14.pdf)

    .text
    .align  4
    .global beeu_mod_inverse_vartime
    .type beeu_mod_inverse_vartime, %function

    // Function parameters (as per the Procedure Call Standard)
    // 64-bit registers
    out         .req x0
    a           .req x1
    n           .req x2
    ret_val     .req x0

    // internal variables
    // x0-x2, x30 are used to hold the modulus n
    // x3-x7 are used for parameters, which is not the case in this function, so they are corruptible
    // x8 is corruptible here
    // (the function doesn't return a struct, hence x8 doesn't contain a passed-in address
    //  for that struct).
    // x9-x15 are corruptible registers
    // x19-x28 are callee-saved registers

    n0          .req x0
    n1          .req x1
    n2          .req x2
    n3          .req x30
    // X/Y will hold the inverse parameter
    // Assumption: X,Y<2^(256)
    // Initially, X := 1, Y := 0
    // (X = k0-k4 since x_i are register names)
    k0          .req x3
    k1          .req x4
    k2          .req x5
    k3          .req x6
    k4          .req x7
    y0          .req x8
    y1          .req x9
    y2          .req x10
    y3          .req x11
    y4          .req x12
    shift       .req x13
    t0          .req x14
    t1          .req x15
    t2          .req x19
    t3          .req x20
    // Initially, A := n, B:= a
    // (B = f0-f3 since b_i caused interference with register names)
    a0          .req x21
    a1          .req x22
    a2          .req x23
    a3          .req x24
    f0          .req x25
    f1          .req x26
    f2          .req x27
    f3          .req x28

.macro  TEST_B_ZERO
    // if B == 0, jump to end of loop
    orr     t0, f0, f1
    orr     t0, t0, f2

    // reverse the bit order of f0. This is needed for clz after this macro
    rbit     t1, f0

    orr     t0, t0, f3
    cbz     t0,.Lbeeu_loop_end
.endm

.macro  SHIFT1 var0, var1, var2, var3, var4
    // if least_sig_bit(var0) == 0, goto shift1_<ctr>
    // else
    // add n and goto shift1_<ctr>
    // prerequisite: t0 = 0
    tbz     \var0, #0, .Lshift1_\@
    adds    \var0, \var0, n0
    adcs    \var1, \var1, n1
    adcs    \var2, \var2, n2
    adcs    \var3, \var3, n3
    adc     \var4, \var4, t0
.Lshift1_\@:
    // var0 := [var1|var0]<64..1>;
    // i.e. concatenate var1 and var0,
    //      extract bits <64..1> from the resulting 128-bit value
    //      and put them in var0
    extr    \var0, \var1, \var0, #1
    extr    \var1, \var2, \var1, #1
    extr    \var2, \var3, \var2, #1
    extr    \var3, \var4, \var3, #1
    lsr     \var4, \var4, #1
.endm

.macro SHIFT256 var0, var1, var2, var3
    // compilation by clang 10.0.0 with -O2/-O3 of
    //      a[0] = (a[0] >> count) | (a[1] << (64-count));
    //      a[1] = (a[1] >> count) | (a[2] << (64-count));
    //      a[2] = (a[2] >> count) | (a[3] << (64-count));
    //      a[3] >>= count;
    // EXTR instruction used in SHIFT1 is similar to x86_64's SHRDQ
    // except that the second source operand of EXTR is only immediate;
    // that's why it cannot be used here where the shift is variable

    // In the following,
    // t0 := 0 - shift
    //
    // then var0, for example, will be shifted right as follows:
    // var0 := (var0 >> (uint(shift) mod 64)) | (var1 << (uint(t0) mod 64))
    // "uint() mod 64" is from the definition of LSL and LSR instructions.
    //
    // What matters here is the order of instructions relative to certain other
    // instructions, i.e.
    // - lsr and lsl must precede orr of the corresponding registers.
    // - lsl must preced the lsr of the same register afterwards.
    // The chosen order of the instructions overall is to try and maximize
    // the pipeline usage.
    neg t0, shift
    lsr \var0, \var0, shift
    lsl t1, \var1, t0

    lsr \var1, \var1, shift
    lsl t2, \var2, t0

    orr \var0, \var0, t1

    lsr \var2, \var2, shift
    lsl t3, \var3, t0

    orr \var1, \var1, t2

    lsr \var3, \var3, shift

    orr \var2, \var2, t3
.endm

beeu_mod_inverse_vartime:
    // Reserve enough space for 14 8-byte registers on the stack
    // in the first stp call for x29, x30.
    // Then store the remaining callee-saved registers.
    //
    //    | x29 | x30 | x19 | x20 | ... | x27 | x28 |  x0 |  x2 |
    //    ^                                                     ^
    //    sp  <------------------- 112 bytes ----------------> old sp
    //   x29 (FP)
    //

    // Pointer authentication - store pointer
    .inst   0xd503233f      // paciasp
    stp     x29,x30,[sp,#-112]!
    add	    x29,sp,#0
    stp     x19,x20,[sp,#16]
    stp     x21,x22,[sp,#32]
    stp     x23,x24,[sp,#48]
    stp     x25,x26,[sp,#64]
    stp     x27,x28,[sp,#80]
    stp     x0,x2,[sp,#96]

    // B = f3-f0 := a
    ldp     f0,f1,[a]
    ldp     f2,f3,[a,#16]

    // n3-n0 := n
    // Note: the value of input params are changed in the following.
    ldp     n0,n1,[n]
    ldp     n2,n3,[n,#16]

    // A = a3-a0 := n
    mov     a0, n0
    mov     a1, n1
    mov     a2, n2
    mov     a3, n3

    // X = k4-k0 := 1
    mov     k0, #1
    eor     k1, k1, k1
    eor     k2, k2, k2
    eor     k3, k3, k3
    eor     k4, k4, k4

    // Y = y4-y0 := 0
    eor     y0, y0, y0
    eor     y1, y1, y1
    eor     y2, y2, y2
    eor     y3, y3, y3
    eor     y4, y4, y4

.Lbeeu_loop:
    // if B == 0, jump to .Lbeeu_loop_end
    TEST_B_ZERO

    // 0 < B < |n|,
    // 0 < A <= |n|,
    // (1)      X*a  ==  B   (mod |n|),
    // (2) (-1)*Y*a  ==  A   (mod |n|)

    // Now divide B by the maximum possible power of two in the
    // integers, and divide X by the same value mod |n|.
    // When we're done, (1) still holds.

    // shift := number of trailing 0s in b0
    // (      = number of leading 0s in t1; see the "rbit" instruction in TEST_B_ZERO)
    clz     shift, t1

    // If there is no shift, goto A,Y shift
    cbz     shift, .Lbeeu_shift_A_Y

    // Shift B right by "shift" bits
    SHIFT256    f0, f1, f2, f3

    // Shift X right by "shift" bits, adding n whenever X becomes odd.
    // shift--;
    // t0 := 0; needed in the addition to the most significant word in SHIFT1
    eor     t0, t0, t0
.Lbeeu_shift_loop_X:
    SHIFT1  k0, k1, k2, k3, k4
    subs    shift, shift, #1
    bne     .Lbeeu_shift_loop_X

    // Note: the steps above perform the same sequence as in p256_beeu-x86_64-asm.pl
    // with the following differences:
    // - "shift" is set directly to the number of trailing 0s in B
    //   (using rbit and clz instructions)
    // - The loop is only used to call SHIFT1(X)
    //   and shift is decreased while executing the X loop.
    // - SHIFT256(B, shift) is performed before right-shifting X; they are independent

.Lbeeu_shift_A_Y:
    // Same for A and Y.
    // Afterwards, (2) still holds.
    // Reverse the bit order of a0
    // shift := number of trailing 0s in a0 (= number of leading 0s in t1)
    rbit    t1, a0
    clz     shift, t1

    // If there is no shift, goto |B-A|, X+Y update
    cbz     shift, .Lbeeu_update_B_X_or_A_Y

    // Shift A right by "shift" bits
    SHIFT256    a0, a1, a2, a3

    // Shift Y right by "shift" bits, adding n whenever Y becomes odd.
    // shift--;
    // t0 := 0; needed in the addition to the most significant word in SHIFT1
    eor     t0, t0, t0
.Lbeeu_shift_loop_Y:
    SHIFT1  y0, y1, y2, y3, y4
    subs    shift, shift, #1
    bne     .Lbeeu_shift_loop_Y

.Lbeeu_update_B_X_or_A_Y:
    // Try T := B - A; if cs, continue with B > A (cs: carry-set = no borrow)
    subs    t0, f0, a0
    sbcs    t1, f1, a1
    sbcs    t2, f2, a2
    sbcs    t3, f3, a3
    bcs     .Lbeeu_B_greater_than_A

    // Else A > B =>
    // A := A - B; Y := Y + X; goto beginning of the loop
    subs    a0, a0, f0
    sbcs    a1, a1, f1
    sbcs    a2, a2, f2
    sbcs    a3, a3, f3

    adds    y0, y0, k0
    adcs    y1, y1, k1
    adcs    y2, y2, k2
    adcs    y3, y3, k3
    adc     y4, y4, k4
    b       .Lbeeu_loop

.Lbeeu_B_greater_than_A:
    // Continue with B > A =>
    // B := B - A; X := X + Y; goto beginning of the loop
    mov     f0, t0
    mov     f1, t1
    mov     f2, t2
    mov     f3, t3

    adds    k0, k0, y0
    adcs    k1, k1, y1
    adcs    k2, k2, y2
    adcs    k3, k3, y3
    adc     k4, k4, y4
    b       .Lbeeu_loop

.Lbeeu_loop_end:
    // The Euclid's algorithm loop ends when A == gcd(a,n);
    // this would be 1, when a and n are co-prime (i.e. do not have a common factor).
    // Since (-1)*Y*a == A (mod |n|), Y>0
    // then out = -Y mod n

    // Verify that A = 1 ==> (-1)*Y*a = A = 1  (mod |n|)
    // Is A-1 == 0?
    // If not, fail.
    sub     t0, a0, #1
    orr     t0, t0, a1
    orr     t0, t0, a2
    orr     t0, t0, a3
    cbnz    t0, .Lbeeu_err

    // If Y>n ==> Y:=Y-n
.Lbeeu_reduction_loop:
    // k_i := y_i - n_i (X is no longer needed, use it as temp)
    // (t0 = 0 from above)
    subs    k0, y0, n0
    sbcs    k1, y1, n1
    sbcs    k2, y2, n2
    sbcs    k3, y3, n3
    sbcs    k4, y4, t0

    // If result is non-negative (i.e., cs = carry set = no borrow),
    // y_i := k_i; goto reduce again
    // else
    // y_i := y_i; continue
    csel    y0, k0, y0, cs
    csel    y1, k1, y1, cs
    csel    y2, k2, y2, cs
    csel    y3, k3, y3, cs
    csel    y4, k4, y4, cs
    bcs     .Lbeeu_reduction_loop

    // Now Y < n (Y cannot be equal to n, since the inverse cannot be 0)
    // out = -Y = n-Y
    subs    y0, n0, y0
    sbcs    y1, n1, y1
    sbcs    y2, n2, y2
    sbcs    y3, n3, y3

    // Save Y in output (out (x0) was saved on the stack)
    ldr     x3, [sp,#96]
    stp     y0, y1, [x3]
    stp     y2, y3, [x3,#16]
    // return 1 (success)
    mov     x0, #1
    b       .Lbeeu_finish

.Lbeeu_err:
    // return 0 (error)
    eor     x0, x0, x0

.Lbeeu_finish:
    // Restore callee-saved registers.
    add 	sp,x29,#0
    ldp     x19,x20,[sp,#16]
    ldp     x21,x22,[sp,#32]
    ldp     x23,x24,[sp,#48]
    ldp     x25,x26,[sp,#64]
    ldp     x27,x28,[sp,#80]
    ldp     x29,x30,[sp],#112

    // Pointer authentication - authenticate pointer before return
    .inst   0xd50323bf      // autiasp
    ret

    .size beeu_mod_inverse_vartime, .-beeu_mod_inverse_vartime
