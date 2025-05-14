# The following xts encrypt is from MacBook M3 build folder
# after moving around some instructions

.globl	_aes_hw_slothy_xts_encrypt
.private_extern	_aes_hw_slothy_xts_encrypt

_aes_hw_slothy_xts_encrypt:
 # AARCH64_VALID_CALL_TARGET
 cmp	x2,#16
    // Original input data size bigger than 16, jump to big size processing.
 b.ne	Lxts_enc_big_size
    // Encrypt the iv with key2, as the first XEX iv.
 ldr	w6,[x4,#240]
 ld1	{v0.16b},[x4],#16
 ld1	{v6.16b},[x5]
 sub	w6,w6,#2
 ld1	{v1.16b},[x4],#16

                // Instructions:    0
                // Expected cycles: 0
                // Expected IPC:    0.00
                //
                // Wall time:     0.00s
                // User time:     0.00s
                //
Loop_enc_iv_enc:
                                      // Instructions:    6
                                      // Expected cycles: 8
                                      // Expected IPC:    0.75
                                      //
                                      // Cycle bound:     8.0
                                      // IPC bound:       0.75
                                      //
                                      // Wall time:     0.03s
                                      // User time:     0.03s
                                      //
                                      // ----- cycle (expected) ------>
                                      // 0                        25
                                      // |------------------------|----
        aese v6.16b, v0.16b           // *.............................
        ld1 {v0.4S}, [x4], #16        // .*............................
        aesmc v6.16b, v6.16b          // ..*...........................
        aese v6.16b, v1.16b           // ....*.........................
        ld1 {v1.4S}, [x4], #16        // .....*........................
        aesmc v6.16b, v6.16b          // ......*.......................

                                     // ------ cycle (expected) ------>
                                     // 0                        25
                                     // |------------------------|-----
        // aese v6.16b,v0.16b        // *.......~.......~.......~......
        // aesmc v6.16b,v6.16b       // ..*.....'.~.....'.~.....'.~....
        // ld1 {v0.4s},[x4],#16      // .*......'~......'~......'~.....
        // aese v6.16b,v1.16b        // ....*...'...~...'...~...'...~..
        // aesmc v6.16b,v6.16b       // ......*.'.....~.'.....~.'......
        // ld1 {v1.4s},[x4],#16      // .....*..'....~..'....~..'....~.

        subs w6, w6, 2
        cbnz w6, Loop_enc_iv_enc
                // Instructions:    0
                // Expected cycles: 0
                // Expected IPC:    0.00
                //
                // Wall time:     0.00s
                // User time:     0.00s
                //

 aese	v6.16b,v0.16b
 aesmc	v6.16b,v6.16b
 ld1	{v0.4s},[x4]
 aese	v6.16b,v1.16b
 eor	v6.16b,v6.16b,v0.16b

 ld1	{v0.16b},[x0]
 eor	v0.16b,v6.16b,v0.16b

 ldr	w6,[x3,#240]
 ld1	{v28.4s,v29.4s},[x3],#32       // load key schedule...

 aese	v0.16b,v28.16b
 aesmc	v0.16b,v0.16b
 ld1	{v16.4s,v17.4s},[x3],#32         // load key schedule...
 aese	v0.16b,v29.16b
 aesmc	v0.16b,v0.16b
 subs	w6,w6,#10     // if rounds==10, jump to aes-128-xts processing
// b.eq    .Lxts_128_enc
Lxts_enc_round_loop:
 aese	v0.16b,v16.16b
 aesmc	v0.16b,v0.16b
 ld1	{v16.4s},[x3],#16            // load key schedule...
 aese	v0.16b,v17.16b
 aesmc	v0.16b,v0.16b
 ld1	{v17.4s},[x3],#16            // load key schedule...
 subs	w6,w6,#2          // bias
 b.gt	Lxts_enc_round_loop
// .Lxts_128_enc:
 ld1	{v18.4s,v19.4s},[x3],#32       // load key schedule...
 aese	v0.16b,v16.16b
 aesmc	v0.16b,v0.16b
 aese	v0.16b,v17.16b
 aesmc	v0.16b,v0.16b
 ld1	{v20.4s,v21.4s},[x3],#32       // load key schedule...
 aese	v0.16b,v18.16b
 aesmc	v0.16b,v0.16b
 aese	v0.16b,v19.16b
 aesmc	v0.16b,v0.16b
 ld1	{v22.4s,v23.4s},[x3],#32       // load key schedule...
 aese	v0.16b,v20.16b
 aesmc	v0.16b,v0.16b
 aese	v0.16b,v21.16b
 aesmc	v0.16b,v0.16b
 ld1	{v7.4s},[x3]
 aese	v0.16b,v22.16b
 aesmc	v0.16b,v0.16b
 aese	v0.16b,v23.16b
 eor	v0.16b,v0.16b,v7.16b
 eor	v0.16b,v0.16b,v6.16b
 st1	{v0.16b},[x1]
 b	Lxts_enc_final_abort

.align	4
Lxts_enc_big_size:
   // Encrypt input size > 16 bytes
 stp	x19,x20,[sp,#-64]!
 stp	x21,x22,[sp,#48]
 stp	d8,d9,[sp,#32]
 stp	d10,d11,[sp,#16]

    // tailcnt store the tail value of length%16.
 and	x21,x2,#0xf
 and	x2,x2,#-16    // len &= 0x1..110000, now divisible by 16
 subs	x2,x2,#16
 mov	x8,#16
 b.lo	Lxts_abort         // if !(len > 16): error
 csel	x8,xzr,x8,eq  // if (len == 16): step = 0

    // Firstly, encrypt the iv with key2, as the first iv of XEX.
 ldr	w6,[x4,#240]
 ld1	{v0.4s},[x4],#16
 ld1	{v6.16b},[x5]
 sub	w6,w6,#2
 ld1	{v1.4s},[x4],#16

Loop_iv_enc:
 aese	v6.16b,v0.16b
 aesmc	v6.16b,v6.16b
 ld1	{v0.4s},[x4],#16
 subs	w6,w6,#2
 aese	v6.16b,v1.16b
 aesmc	v6.16b,v6.16b
 ld1	{v1.4s},[x4],#16
 b.gt	Loop_iv_enc

 aese	v6.16b,v0.16b
 aesmc	v6.16b,v6.16b
 ld1	{v0.4s},[x4]
 aese	v6.16b,v1.16b
 eor	v6.16b,v6.16b,v0.16b

    // The iv for second block
    // x9- iv(low), x10 - iv(high)
    // the five ivs stored into, v6.16b,v8.16b,v9.16b,v10.16b,v11.16b
 fmov	x9,d6
 fmov	x10,v6.d[1]
 mov	w19,#0x87
 extr	x22,x10,x10,#32
 extr	x10,x10,x9,#63
 and	w11,w19,w22,asr#31
 eor	x9,x11,x9,lsl#1
 fmov	d8,x9
 fmov	v8.d[1],x10

 ldr	w5,[x3,#240]       // next starting point
 ld1	{v0.16b},[x0],x8

 ld1	{v16.4s,v17.4s},[x3]         // load key schedule...
 sub	w5,w5,#6
 add	x7,x3,x5,lsl#4  // pointer to last 7 round keys
 ld1	{v18.4s,v19.4s},[x7],#32
 ld1	{v20.4s,v21.4s},[x7],#32
 ld1	{v22.4s,v23.4s},[x7],#32
 ld1	{v7.4s},[x7]

 sub	w5,w5,#2
 add	x7,x3,#32
 mov	w6,w5

    // Encryption
Lxts_enc:
 ld1	{v24.16b},[x0],#16
 subs	x2,x2,#32           // bias
 add	w6,w5,#2
 orr	v3.16b,v0.16b,v0.16b
 orr	v1.16b,v0.16b,v0.16b
 orr	v28.16b,v0.16b,v0.16b
 orr	v27.16b,v24.16b,v24.16b
 orr	v29.16b,v24.16b,v24.16b
 b.lo	Lxts_inner_enc_tail    // when input size % 5 = 1 or 2
                                    // (with tail or not)
 eor	v0.16b,v0.16b,v6.16b          // before encryption, xor with iv
 eor	v24.16b,v24.16b,v8.16b

    // The iv for third block
 extr	x22,x10,x10,#32
 extr	x10,x10,x9,#63
 and	w11,w19,w22,asr#31
 eor	x9,x11,x9,lsl#1
 fmov	d9,x9
 fmov	v9.d[1],x10


 orr	v1.16b,v24.16b,v24.16b
 ld1	{v24.16b},[x0],#16
 orr	v2.16b,v0.16b,v0.16b
 orr	v3.16b,v1.16b,v1.16b
 eor	v27.16b,v24.16b,v9.16b         // the third block
 eor	v24.16b,v24.16b,v9.16b
 cmp	x2,#32
 b.lo	Lxts_outer_enc_tail

    // The iv for fourth block
 extr	x22,x10,x10,#32
 extr	x10,x10,x9,#63
 and	w11,w19,w22,asr#31
 eor	x9,x11,x9,lsl#1
 fmov	d10,x9
 fmov	v10.d[1],x10

 ld1	{v25.16b},[x0],#16
    // The iv for fifth block
 extr	x22,x10,x10,#32
 extr	x10,x10,x9,#63
 and	w11,w19,w22,asr#31
 eor	x9,x11,x9,lsl#1
 fmov	d11,x9
 fmov	v11.d[1],x10

 ld1	{v26.16b},[x0],#16
 eor	v25.16b,v25.16b,v10.16b        // the fourth block
 eor	v26.16b,v26.16b,v11.16b
 sub	x2,x2,#32           // bias
 mov	w6,w5
  // b       .Loop5x_xts_enc

.align	4
Loop5x_xts_enc:
 aese	v0.16b,v16.16b
 aesmc	v0.16b,v0.16b
 aese	v1.16b,v16.16b
 aesmc	v1.16b,v1.16b
 aese	v24.16b,v16.16b
 aesmc	v24.16b,v24.16b
 aese	v25.16b,v16.16b
 aesmc	v25.16b,v25.16b
 aese	v26.16b,v16.16b
 aesmc	v26.16b,v26.16b
 ld1	{v16.4s},[x7],#16
 subs	w6,w6,#2
 aese	v0.16b,v17.16b
 aesmc	v0.16b,v0.16b
 aese	v1.16b,v17.16b
 aesmc	v1.16b,v1.16b
 aese	v24.16b,v17.16b
 aesmc	v24.16b,v24.16b
 aese	v25.16b,v17.16b
 aesmc	v25.16b,v25.16b
 aese	v26.16b,v17.16b
 aesmc	v26.16b,v26.16b
 ld1	{v17.4s},[x7],#16
 b.gt	Loop5x_xts_enc

 aese	v0.16b,v16.16b
 aesmc	v0.16b,v0.16b
 aese	v1.16b,v16.16b
 aesmc	v1.16b,v1.16b
 aese	v24.16b,v16.16b
 aesmc	v24.16b,v24.16b
 aese	v25.16b,v16.16b
 aesmc	v25.16b,v25.16b
 aese	v26.16b,v16.16b
 aesmc	v26.16b,v26.16b
 subs	x2,x2,#0x50         // because Lxts_enc_tail4x

 aese	v0.16b,v17.16b
 aesmc	v0.16b,v0.16b
 aese	v1.16b,v17.16b
 aesmc	v1.16b,v1.16b
 aese	v24.16b,v17.16b
 aesmc	v24.16b,v24.16b
 aese	v25.16b,v17.16b
 aesmc	v25.16b,v25.16b
 aese	v26.16b,v17.16b
 aesmc	v26.16b,v26.16b
 csel	x6,xzr,x2,gt    // borrow x6, w6, "gt" is not typo
 mov	x7,x3

 aese	v0.16b,v18.16b
 aesmc	v0.16b,v0.16b
 aese	v1.16b,v18.16b
 aesmc	v1.16b,v1.16b
 aese	v24.16b,v18.16b
 aesmc	v24.16b,v24.16b
 aese	v25.16b,v18.16b
 aesmc	v25.16b,v25.16b
 aese	v26.16b,v18.16b
 aesmc	v26.16b,v26.16b
 add	x0,x0,x6  // x0 is adjusted in such way that
                                // at exit from the loop v1.16b-v26.16b
                                // are loaded with last "words"
 add	x6,x2,#0x60         // because Lxts_enc_tail4x

 aese	v0.16b,v19.16b
 aesmc	v0.16b,v0.16b
 aese	v1.16b,v19.16b
 aesmc	v1.16b,v1.16b
 aese	v24.16b,v19.16b
 aesmc	v24.16b,v24.16b
 aese	v25.16b,v19.16b
 aesmc	v25.16b,v25.16b
 aese	v26.16b,v19.16b
 aesmc	v26.16b,v26.16b

 aese	v0.16b,v20.16b
 aesmc	v0.16b,v0.16b
 aese	v1.16b,v20.16b
 aesmc	v1.16b,v1.16b
 aese	v24.16b,v20.16b
 aesmc	v24.16b,v24.16b
 aese	v25.16b,v20.16b
 aesmc	v25.16b,v25.16b
 aese	v26.16b,v20.16b
 aesmc	v26.16b,v26.16b

 aese	v0.16b,v21.16b
 aesmc	v0.16b,v0.16b
 aese	v1.16b,v21.16b
 aesmc	v1.16b,v1.16b
 aese	v24.16b,v21.16b
 aesmc	v24.16b,v24.16b
 aese	v25.16b,v21.16b
 aesmc	v25.16b,v25.16b
 aese	v26.16b,v21.16b
 aesmc	v26.16b,v26.16b

 aese	v0.16b,v22.16b
 aesmc	v0.16b,v0.16b
 aese	v1.16b,v22.16b
 aesmc	v1.16b,v1.16b
 aese	v24.16b,v22.16b
 aesmc	v24.16b,v24.16b
 aese	v25.16b,v22.16b
 aesmc	v25.16b,v25.16b
 aese	v26.16b,v22.16b
 aesmc	v26.16b,v26.16b

 aese	v0.16b,v23.16b
 aese	v1.16b,v23.16b
 aese	v24.16b,v23.16b
 aese	v25.16b,v23.16b
 aese	v26.16b,v23.16b

 eor	v4.16b,v7.16b,v6.16b
    // aese    v0.16b,v23.16b
    // The iv for first block of one iteration
 extr	x22,x10,x10,#32
 extr	x10,x10,x9,#63
 and	w11,w19,w22,asr#31
 eor	x9,x11,x9,lsl#1
 fmov	d6,x9
 fmov	v6.d[1],x10
 eor	v5.16b,v7.16b,v8.16b
 ld1	{v2.16b},[x0],#16
    // aese    v1.16b,v23.16b
    // The iv for second block
 extr	x22,x10,x10,#32
 extr	x10,x10,x9,#63
 and	w11,w19,w22,asr#31
 eor	x9,x11,x9,lsl#1
 fmov	d8,x9
 fmov	v8.d[1],x10
 eor	v17.16b,v7.16b,v9.16b
 ld1	{v3.16b},[x0],#16
    // aese    v24.16b,v23.16b
    // The iv for third block
 extr	x22,x10,x10,#32
 extr	x10,x10,x9,#63
 and	w11,w19,w22,asr#31
 eor	x9,x11,x9,lsl#1
 fmov	d9,x9
 fmov	v9.d[1],x10
 eor	v30.16b,v7.16b,v10.16b
 ld1	{v27.16b},[x0],#16
    // aese    v25.16b,v23.16b
    // The iv for fourth block
 extr	x22,x10,x10,#32
 extr	x10,x10,x9,#63
 and	w11,w19,w22,asr#31
 eor	x9,x11,x9,lsl#1
 fmov	d10,x9
 fmov	v10.d[1],x10
 eor	v31.16b,v7.16b,v11.16b
 ld1	{v28.16b},[x0],#16
    // aese    v26.16b,v23.16b

    // The iv for fifth block
 extr	x22,x10,x10,#32
 extr	x10,x10,x9,#63
 and	w11,w19,w22,asr #31
 eor	x9,x11,x9,lsl #1
 fmov	d11,x9
 fmov	v11.d[1],x10

 ld1	{v29.16b},[x0],#16
 cbz	x6,Lxts_enc_tail4x
// vld1 {v16.4s},[x7],#16         // re-pre-load rndkey[0]
 eor	v4.16b,v4.16b,v0.16b
 eor	v0.16b,v2.16b,v6.16b
 eor	v5.16b,v5.16b,v1.16b
 eor	v1.16b,v3.16b,v8.16b
 eor	v17.16b,v17.16b,v24.16b
 eor	v24.16b,v27.16b,v9.16b
 eor	v30.16b,v30.16b,v25.16b
 eor	v25.16b,v28.16b,v10.16b
 eor	v31.16b,v31.16b,v26.16b
    // vst1  {v4.16b},[x1],#16
 eor	v26.16b,v29.16b,v11.16b
    // vst1  {v5.16b},[x1],#16
 mov	w6,w5
 st1	{v4.16b,v5.16b},[x1],#32
 st1	{v17.16b},[x1],#16
// vld1 {v17.4s},[x7],#16         // re-pre-load rndkey[1]
// vst1  {v30.16b},[x1],#16
// vst1  {v31.16b},[x1],#16
 st1	{v30.16b,v31.16b},[x1],#32
 ld1	{v16.4s},[x7],#16        // re-pre-load rndkey[0]
 ld1	{v17.4s},[x7],#16        // re-pre-load rndkey[1]
 b.hs	Loop5x_xts_enc


    // If left 4 blocks, borrow the five block's processing.
    // This means if (x2 + 1 block) == 0, which is the case
    // when input size % 5 = 4, continue processing and do
    // another iteration in Loop5x_xts_enc which will exit from
    // cbz  x6,.Lxts_enc_tail4x.
    // Otherwise, this is the end of the loop continue processing
    // 0, 1, 2 or 3 blocks (with or without tail) starting at
    // Loop5x_enc_after
 cmn	x2,#0x10
 b.ne	Loop5x_enc_after
 orr	v11.16b,v10.16b,v10.16b
 orr	v10.16b,v9.16b,v9.16b
 orr	v9.16b,v8.16b,v8.16b
 orr	v8.16b,v6.16b,v6.16b
 fmov	x9,d11
 fmov	x10,v11.d[1]
 eor	v0.16b,v6.16b,v2.16b
 eor	v1.16b,v8.16b,v3.16b
 eor	v24.16b,v27.16b,v9.16b
 eor	v25.16b,v28.16b,v10.16b
 eor	v26.16b,v29.16b,v11.16b
 b.eq	Loop5x_xts_enc

Loop5x_enc_after:
 add	x2,x2,#0x50
 cbz	x2,Lxts_enc_done     // no blocks left

 add	w6,w5,#2
 subs	x2,x2,#0x30
 b.lo	Lxts_inner_enc_tail    // 1 or 2 blocks left
                                    // (with tail or not)

 eor	v0.16b,v6.16b,v27.16b         // 3 blocks left
 eor	v1.16b,v8.16b,v28.16b
 eor	v24.16b,v29.16b,v9.16b
 b	Lxts_outer_enc_tail

.align	4
Lxts_enc_tail4x:
 add	x0,x0,#16
 eor	v5.16b,v1.16b,v5.16b
 st1	{v5.16b},[x1],#16
 eor	v17.16b,v24.16b,v17.16b
 st1	{v17.16b},[x1],#16
 eor	v30.16b,v25.16b,v30.16b
 eor	v31.16b,v26.16b,v31.16b
 st1	{v30.16b,v31.16b},[x1],#32
 b	Lxts_enc_done
.align	4
Lxts_outer_enc_tail:
 aese	v0.16b,v16.16b
 aesmc	v0.16b,v0.16b
 aese	v1.16b,v16.16b
 aesmc	v1.16b,v1.16b
 aese	v24.16b,v16.16b
 aesmc	v24.16b,v24.16b
 ld1	{v16.4s},[x7],#16
 subs	w6,w6,#2
 aese	v0.16b,v17.16b
 aesmc	v0.16b,v0.16b
 aese	v1.16b,v17.16b
 aesmc	v1.16b,v1.16b
 aese	v24.16b,v17.16b
 aesmc	v24.16b,v24.16b
 ld1	{v17.4s},[x7],#16
 b.gt	Lxts_outer_enc_tail

 aese	v0.16b,v16.16b
 aesmc	v0.16b,v0.16b
 aese	v1.16b,v16.16b
 aesmc	v1.16b,v1.16b
 aese	v24.16b,v16.16b
 aesmc	v24.16b,v24.16b
 eor	v4.16b,v6.16b,v7.16b
 aese	v0.16b,v17.16b
 aesmc	v0.16b,v0.16b
 aese	v1.16b,v17.16b
 aesmc	v1.16b,v1.16b
 aese	v24.16b,v17.16b
 aesmc	v24.16b,v24.16b
 aese	v0.16b,v20.16b
 aesmc	v0.16b,v0.16b
 aese	v1.16b,v20.16b
 aesmc	v1.16b,v1.16b
 aese	v24.16b,v20.16b
 aesmc	v24.16b,v24.16b
 aese	v0.16b,v21.16b
 aesmc	v0.16b,v0.16b
 aese	v1.16b,v21.16b
 aesmc	v1.16b,v1.16b
 aese	v24.16b,v21.16b
 aesmc	v24.16b,v24.16b
 aese	v0.16b,v22.16b
 aesmc	v0.16b,v0.16b
 aese	v1.16b,v22.16b
 aesmc	v1.16b,v1.16b
 aese	v24.16b,v22.16b
 aesmc	v24.16b,v24.16b
 aese	v0.16b,v23.16b
 aese	v1.16b,v23.16b
 aese	v24.16b,v23.16b

 eor	v17.16b,v9.16b,v7.16b
 subs	x2,x2,#0x30
    // The iv for first block
 fmov	x9,d9
 fmov	x10,v9.d[1]
    // mov   w19,#0x87
 extr	x22,x10,x10,#32
 extr	x10,x10,x9,#63
 and	w11,w19,w22,asr#31
 eor	x9,x11,x9,lsl#1
 fmov	d6,x9
 fmov	v6.d[1],x10
 eor	v5.16b,v8.16b,v7.16b
 csel	x6,x2,x6,lo   // x6, w6, is zero at this point
// aese    v0.16b,v17.16b
// aesmc   v0.16b,v0.16b
// aese    v1.16b,v17.16b
// aesmc   v1.16b,v1.16b
// aese    v24.16b,v17.16b
// aesmc   v24.16b,v24.16b
// veor    v17.16b,v9.16b,v7.16b

 add	x6,x6,#0x20
 add	x0,x0,x6
 mov	x7,x3

// aese    v0.16b,v20.16b
// aesmc   v0.16b,v0.16b
// aese    v1.16b,v20.16b
// aesmc   v1.16b,v1.16b
// aese    v24.16b,v20.16b
// aesmc   v24.16b,v24.16b
// aese    v0.16b,v21.16b
// aesmc   v0.16b,v0.16b
// aese    v1.16b,v21.16b
// aesmc   v1.16b,v1.16b
// aese    v24.16b,v21.16b
// aesmc   v24.16b,v24.16b
// aese    v0.16b,v22.16b
// aesmc   v0.16b,v0.16b
// aese    v1.16b,v22.16b
// aesmc   v1.16b,v1.16b
// aese    v24.16b,v22.16b
// aesmc   v24.16b,v24.16b
// aese    v0.16b,v23.16b
// aese    v1.16b,v23.16b
// aese    v24.16b,v23.16b
 ld1	{v27.16b},[x0],#16
 add	w6,w5,#2
// vld1 {v16.4s},[x7],#16         // re-pre-load rndkey[0]
 eor	v4.16b,v4.16b,v0.16b
 eor	v5.16b,v5.16b,v1.16b
 eor	v24.16b,v24.16b,v17.16b
// vld1 {v17.4s},[x7],#16         // re-pre-load rndkey[1]
 ld1	{v16.4s,v17.4s},[x7],#32
// vst1  {v4.16b},[x1],#16
// vst1  {v5.16b},[x1],#16
 st1	{v4.16b,v5.16b},[x1],#32
 st1	{v24.16b},[x1],#16
 cmn	x2,#0x30
 b.eq	Lxts_enc_done
Lxts_encxor_one:
 orr	v28.16b,v3.16b,v3.16b
 orr	v29.16b,v27.16b,v27.16b
 nop

Lxts_inner_enc_tail:
 cmn	x2,#0x10
 eor	v1.16b,v28.16b,v6.16b
 eor	v24.16b,v29.16b,v8.16b
 b.eq	Lxts_enc_tail_loop
 eor	v24.16b,v29.16b,v6.16b
Lxts_enc_tail_loop:
 aese	v1.16b,v16.16b
 aesmc	v1.16b,v1.16b
 aese	v24.16b,v16.16b
 aesmc	v24.16b,v24.16b
 ld1	{v16.4s},[x7],#16
 subs	w6,w6,#2
 aese	v1.16b,v17.16b
 aesmc	v1.16b,v1.16b
 aese	v24.16b,v17.16b
 aesmc	v24.16b,v24.16b
 ld1	{v17.4s},[x7],#16
 b.gt	Lxts_enc_tail_loop

 aese	v1.16b,v16.16b
 aesmc	v1.16b,v1.16b
 aese	v24.16b,v16.16b
 aesmc	v24.16b,v24.16b
 aese	v1.16b,v17.16b
 aesmc	v1.16b,v1.16b
 aese	v24.16b,v17.16b
 aesmc	v24.16b,v24.16b
 aese	v1.16b,v20.16b
 aesmc	v1.16b,v1.16b
 aese	v24.16b,v20.16b
 aesmc	v24.16b,v24.16b
 cmn	x2,#0x20
 aese	v1.16b,v21.16b
 aesmc	v1.16b,v1.16b
 aese	v24.16b,v21.16b
 aesmc	v24.16b,v24.16b
 eor	v5.16b,v6.16b,v7.16b
 aese	v1.16b,v22.16b
 aesmc	v1.16b,v1.16b
 aese	v24.16b,v22.16b
 aesmc	v24.16b,v24.16b
 eor	v17.16b,v8.16b,v7.16b
 aese	v1.16b,v23.16b
 aese	v24.16b,v23.16b
 b.eq	Lxts_enc_one
 eor	v5.16b,v5.16b,v1.16b
 st1	{v5.16b},[x1],#16
 eor	v17.16b,v17.16b,v24.16b
 orr	v6.16b,v8.16b,v8.16b
 st1	{v17.16b},[x1],#16
 fmov	x9,d8
 fmov	x10,v8.d[1]
 mov	w19,#0x87
 extr	x22,x10,x10,#32
 extr	x10,x10,x9,#63
 and	w11,w19,w22,asr #31
 eor	x9,x11,x9,lsl #1
 fmov	d6,x9
 fmov	v6.d[1],x10
 b	Lxts_enc_done

Lxts_enc_one:
 eor	v5.16b,v5.16b,v24.16b
 orr	v6.16b,v6.16b,v6.16b
 st1	{v5.16b},[x1],#16
 fmov	x9,d6
 fmov	x10,v6.d[1]
 mov	w19,#0x87
 extr	x22,x10,x10,#32
 extr	x10,x10,x9,#63
 and	w11,w19,w22,asr #31
 eor	x9,x11,x9,lsl #1
 fmov	d6,x9
 fmov	v6.d[1],x10
 b	Lxts_enc_done
.align	5
Lxts_enc_done:
    // Process the tail block with cipher stealing.
 tst	x21,#0xf
 b.eq	Lxts_abort

 mov	x20,x0
 mov	x13,x1
 sub	x1,x1,#16
.composite_enc_loop:
 subs	x21,x21,#1
 ldrb	w15,[x1,x21]
 ldrb	w14,[x20,x21]
 strb	w15,[x13,x21]
 strb	w14,[x1,x21]
 b.gt	.composite_enc_loop
Lxts_enc_load_done:
 ld1	{v26.16b},[x1]
 eor	v26.16b,v26.16b,v6.16b

    // Encrypt the composite block to get the last second encrypted text block
 ldr	w6,[x3,#240]        // load key schedule...
 ld1	{v0.16b},[x3],#16
 sub	w6,w6,#2
 ld1	{v1.16b},[x3],#16     // load key schedule...
Loop_final_enc:
 aese	v26.16b,v0.16b
 aesmc	v26.16b,v26.16b
 ld1	{v0.4s},[x3],#16
 subs	w6,w6,#2
 aese	v26.16b,v1.16b
 aesmc	v26.16b,v26.16b
 ld1	{v1.4s},[x3],#16
 b.gt	Loop_final_enc

 aese	v26.16b,v0.16b
 aesmc	v26.16b,v26.16b
 ld1	{v0.4s},[x3]
 aese	v26.16b,v1.16b
 eor	v26.16b,v26.16b,v0.16b
 eor	v26.16b,v26.16b,v6.16b
 st1	{v26.16b},[x1]

Lxts_abort:
 ldp	x21,x22,[sp,#48]
 ldp	d8,d9,[sp,#32]
 ldp	d10,d11,[sp,#16]
 ldp	x19,x20,[sp],#64
Lxts_enc_final_abort:
 ret
