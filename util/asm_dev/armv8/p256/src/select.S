//------------------------------------------------------------------------------------
// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC
//------------------------------------------------------------------------------------

// void select_w5(uint64_t *val, uint64_t *in_t, int index);
    .text
    .align  4
    .global select_w5
    .type select_w5, %function

    // Function parameters (as per the Procedure Call Standard)
    val         .req x0 // 64-bit register
    in_t        .req x1 // 64-bit register
    idx         .req w2 // 32-bit (part of a) register
                        // $index in p256-armv8-asm.pl

    // internal variables
    // x9-x15 are corruptible registers, hence also their lower halves
    // w9-w15
    Ctr         .req w9     // 32-bit (part of a) register
    Val_in      .req x10    // internal pointer to the output
//    In_t_in     .req x11    // internal pointer to the input

    // The following registers are 128-bit long
    // and are used as vectors of elements.
    One         .req v0     // $ONE in p256-armv8-asm.pl
    M0          .req v1
    Idx_in      .req v2     // $INDEX in p256-armv8-asm.pl
    Mask        .req v3     // $TMP0 in p256-armv8-asm.pl
    // Each pair of the following registers holds a 256-bit value
    // (point coordinate).
    // Each 6 registers hold a table entry.
    Ra          .req v16
    Rb          .req v17
    Rc          .req v18
    Rd          .req v19
    Re          .req v20
    Rf          .req v21
    T0a         .req v22
    T0b         .req v23
    T0c         .req v24
    T0d         .req v25
    T0e         .req v26
    T0f         .req v27

select_w5:
    // Pointer authentication - store pointer
	.inst	0xd503233f		// paciasp
	stp	x29,x30,[sp,#-16]!
	add	x29,sp,#0

    // [Ra - Rf] := 0
    eor     Ra.16b, Ra.16b, Ra.16b
    eor     Rb.16b, Rb.16b, Rb.16b
    eor     Rc.16b, Rc.16b, Rc.16b
    eor     Rd.16b, Rd.16b, Rd.16b
    eor     Re.16b, Re.16b, Re.16b
    eor     Rf.16b, Rf.16b, Rf.16b

    movi    One.4s, #1      // One (vec_4*32) := | 1 | 1 | 1 | 1 |
    mov     M0.16b, One.16b // M0 := One
    dup     Idx_in.4s, idx  // Idx_in (vec_4*32) := | idx | idx | idx | idx |

    mov     Val_in, val     // Val_in := val
    mov     Ctr, #16        // Ctr := 16; loop counter

.Lselect_w5_loop:
    // [T0a-T0f] := Load a (3 * 256-bit = 6 * 128-bit) table entry pointed to by in_t
    //  and advance in_t to point to the next entry
    ld1     {T0a.2d, T0b.2d, T0c.2d, T0d.2d}, [in_t],#64
    ld1     {T0e.2d, T0f.2d}, [in_t],#32

    // Mask = (M0 == Idx_in)? All 1s : All 0s
    cmeq    Mask.4s, M0.4s, Idx_in.4s

    // Increment M0 lanes
    add     M0.4s, M0.4s, One.4s

    // [T0a-T0f] := [T0a-T0f] AND Mask;
    // values read from the table will be 0'd if M0 != Idx_in
    // [Ra-Rf] := [Ra-Rf] OR [T0a-T0f]
    // values in output registers will remain the same if M0 != Idx_in
    and     T0a.16b, T0a.16b, Mask.16b
    and     T0b.16b, T0b.16b, Mask.16b
    orr     Ra.16b, Ra.16b, T0a.16b
    orr     Rb.16b, Rb.16b, T0b.16b

    and     T0c.16b, T0c.16b, Mask.16b
    and     T0d.16b, T0d.16b, Mask.16b
    orr     Rc.16b, Rc.16b, T0c.16b
    orr     Rd.16b, Rd.16b, T0d.16b

    and     T0e.16b, T0e.16b, Mask.16b
    and     T0f.16b, T0f.16b, Mask.16b
    orr     Re.16b, Re.16b, T0e.16b
    orr     Rf.16b, Rf.16b, T0f.16b

    // Decrement loop counter; loop back if not 0
    subs    Ctr, Ctr, #1
    bne     .Lselect_w5_loop

    // Write [Ra-Rf] to memory at the output pointer
    st1     {Ra.2d, Rb.2d, Rc.2d, Rd.2d}, [Val_in],#64
    st1     {Re.2d, Rf.2d}, [Val_in]

    // Pointer authentication - authenticate pointer before return
    add	sp,x29,#0
    ldp	x29,x30,[sp],#16
    .inst	0xd50323bf		// autiasp
    ret

    .size select_w5, .-select_w5

// void ecp_nistz256_select_w7(uint64_t *val, uint64_t *in_t, int index);
.align  4
.global select_w7
.type select_w7, %function

select_w7:
    // Pointer authentication - store pointer
	.inst	0xd503233f		// paciasp
	stp	x29,x30,[sp,#-16]!
	add	x29,sp,#0

    // One (vec_4*32) := | 1 | 1 | 1 | 1 |
    // Idx_in (vec_4*32) := | idx | idx | idx | idx |
    movi    One.4s, #1
    dup     Idx_in.4s, idx

    // [Ra - Rd] := 0
    eor     Ra.16b, Ra.16b, Ra.16b
    eor     Rb.16b, Rb.16b, Rb.16b
    eor     Rc.16b, Rc.16b, Rc.16b
    eor     Rd.16b, Rd.16b, Rd.16b

    // M0 := One
    mov     M0.16b, One.16b

    // Ctr := 64; loop counter
    mov     Ctr, #64

.Lselect_w7_loop:
    // [T0a-T0d] := Load a (2 * 256-bit = 4 * 128-bit) table entry pointed to by in_t
    //  and advance in_t to point to the next entry
    ld1     {T0a.2d, T0b.2d, T0c.2d, T0d.2d}, [in_t],#64

    // Mask = (M0 == Idx_in)? All 1s : All 0s
    cmeq    Mask.4s, M0.4s, Idx_in.4s

    // Increment M0 lanes
    add     M0.4s, M0.4s, One.4s

    // [T0a-T0d] := [T0a-T0d] AND Mask;
    // values read from the table will be 0'd if M0 != Idx_in
    // [Ra-Rd] := [Ra-Rd] OR [T0a-T0d]
    // values in output registers will remain the same if M0 != Idx_in
    and     T0a.16b, T0a.16b, Mask.16b
    and     T0b.16b, T0b.16b, Mask.16b
    orr     Ra.16b, Ra.16b, T0a.16b
    orr     Rb.16b, Rb.16b, T0b.16b

    and     T0c.16b, T0c.16b, Mask.16b
    and     T0d.16b, T0d.16b, Mask.16b
    orr     Rc.16b, Rc.16b, T0c.16b
    orr     Rd.16b, Rd.16b, T0d.16b

    // Decrement loop counter; loop back if not 0
    subs    Ctr, Ctr, #1
    bne     .Lselect_w7_loop

    // Write [Ra-Rd] to memory at the output pointer
    st1     {Ra.2d, Rb.2d, Rc.2d, Rd.2d}, [val]

    // Pointer authentication - authenticate pointer before return
    ldp	x29,x30,[sp],#16
	.inst	0xd50323bf		// autiasp
    ret
    .size select_w7, .-select_w7
