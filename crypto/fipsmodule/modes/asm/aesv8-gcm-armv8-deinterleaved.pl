#! /usr/bin/env perl

# Copyright (c) 2022, ARM Inc.
#
# Permission to use, copy, modify, and/or distribute this software for any
# purpose with or without fee is hereby granted, provided that the above
# copyright notice and this permission notice appear in all copies.
#
# THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
# WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
# MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
# SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
# WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION
# OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN
# CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE. */

#========================================================================
# Written by Fangming Fang <fangming.fang@arm.com> for the OpenSSL project,
# derived from https://github.com/ARM-software/AArch64cryptolib, original
# author Samuel Lee <Samuel.Lee@arm.com>.
#========================================================================

# This file contains a manually de-interleaved version of aesv8-gcm-armv8.pl.
# See aesv8-gcm-armv8.pl for details.

$flavour = shift;
$output  = shift;

$0 =~ m/(.*[\/\\])[^\/\\]+$/; $dir=$1;
( $xlate="${dir}arm-xlate.pl" and -f $xlate ) or
( $xlate="${dir}../../../perlasm/arm-xlate.pl" and -f $xlate) or
die "can't locate arm-xlate.pl";

open OUT,"| \"$^X\" $xlate $flavour $output";
*STDOUT=*OUT;

$code=<<___;
#include <openssl/arm_arch.h>
#if __ARM_MAX_ARCH__ >= 8

.arch armv8-a+crypto
.text
___

$input_ptr="x0";  #argument block
$bit_length="x1";
$output_ptr="x2";
$current_tag="x3";
$Htable="x6";
$counter="x16";
$cc="x8";

{
my ($end_input_ptr,$main_end_input_ptr,$input_l0,$input_h0)=map("x$_",(4..7));
my ($input_l1,$input_h1,$input_l2,$input_h2,$input_l3,$input_h3)=map("x$_",(19..24));
my ($output_l1,$output_h1,$output_l2,$output_h2,$output_l3,$output_h3)=map("x$_",(19..24));
my ($output_l0,$output_h0)=map("x$_",(6..7));

# rkN_l and rkN_h store the final round key, which is handled slightly
# differently because it is EORed through general-purpose registers.
my $ctr32w="w9";
my ($ctr32x,$ctr96_b64x,$ctr96_t32x,$rctr32x,$rkN_l,$rkN_h,$len)=map("x$_",(9..15));
my ($ctr96_t32w,$rctr32w)=map("w$_",(11..12));

my $rounds="x17";
my $roundsw="w17";

my ($ctr0b,$ctr1b,$ctr2b,$ctr3b,$res0b,$res1b,$res2b,$res3b)=map("v$_.16b",(0..7));
my ($ctr0,$ctr1,$ctr2,$ctr3,$res0,$res1,$res2,$res3)=map("v$_",(0..7));
my ($ctr0d,$ctr1d,$ctr2d,$ctr3d,$res0d,$res1d,$res2d,$res3d)=map("d$_",(0..7));
my ($res0q,$res1q,$res2q,$res3q)=map("q$_",(4..7));

my ($acc_hb,$acc_mb,$acc_lb)=map("v$_.16b",(9..11));
my ($acc_h,$acc_m,$acc_l)=map("v$_",(9..11));
my ($acc_hd,$acc_md,$acc_ld)=map("d$_",(9..11));

my ($h1,$h2,$h3,$h4,$h12k,$h34k)=map("v$_",(12..17));
my ($h1q,$h2q,$h3q,$h4q)=map("q$_",(12..15));
my ($h1b,$h2b,$h3b,$h4b)=map("v$_.16b",(12..15));

my $t0="v8";
my $t0d="d8";
my $t1="v4";
my $t1d="d4";
my $t2="v8";
my $t2d="d8";
my $t3="v4";
my $t3d="d4";
my $t4="v4";
my $t4d="d4";
my $t5="v5";
my $t5d="d5";
my $t6="v8";
my $t6d="d8";
my $t7="v5";
my $t7d="d5";
my $t8="v6";
my $t8d="d6";
my $t9="v4";
my $t9d="d4";

my ($ctr_t0,$ctr_t1,$ctr_t2,$ctr_t3)=map("v$_",(4..7));
my ($ctr_t0d,$ctr_t1d,$ctr_t2d,$ctr_t3d)=map("d$_",(4..7));
my ($ctr_t0b,$ctr_t1b,$ctr_t2b,$ctr_t3b)=map("v$_.16b",(4..7));

my $mod_constantd="d8";
my $mod_constant="v8";
my $mod_t="v7";

# rkNm1 stores the second-to-last round key, which is handled slightly
# differently because it uses plain AESE instead of an AESE + AESMC macro-op.
my ($rk0,$rk1,$rk2,$rk3,$rk4,$rk5,$rk6,$rk7,$rk8,$rk9,$rk10,$rk11,$rk12,$rkNm1)=map("v$_.16b",(18..31));
my ($rk0q,$rk1q,$rk2q,$rk3q,$rk4q,$rk5q,$rk6q,$rk7q,$rk8q,$rk9q,$rk10q,$rk11q,$rk12q,$rkNm1q)=map("q$_",(18..31));
my $rk2q1="v20.1q";
my $rk3q1="v21.1q";
my $rk4v="v22";
my $rk4d="d22";

################################################################################
# size_t aes_gcm_enc_kernel_deinterleaved(const uint8_t *in,
#                           size_t len_bits,
#                           uint8_t *out,
#                           u64 *Xi,
#                           uint8_t ivec[16],
#                           const void *key,
#                           const void *Htable);
#
$code.=<<___;
.global aes_gcm_enc_kernel_deinterleaved
.type   aes_gcm_enc_kernel_deinterleaved,%function
.align  4
aes_gcm_enc_kernel_deinterleaved:
#ifdef BORINGSSL_DISPATCH_TEST
.extern        BORINGSSL_function_hit
	adrp	x9,:pg_hi21:BORINGSSL_function_hit
	add     x9, x9, :lo12:BORINGSSL_function_hit
	mov     w10, #1
	strb    w10, [x9,#2] // kFlag_aes_gcm_enc_kernel_deinterleaved
#endif
	AARCH64_SIGN_LINK_REGISTER
	stp	x29, x30, [sp, #-128]!
	mov	x29, sp
	stp     x19, x20, [sp, #16]
	mov     $counter, x4
	mov     $cc, x5
	stp     x21, x22, [sp, #32]
	stp     x23, x24, [sp, #48]
	stp     d8, d9, [sp, #64]
	stp     d10, d11, [sp, #80]
	stp     d12, d13, [sp, #96]
	stp     d14, d15, [sp, #112]
	ldr	$roundsw, [$cc, #240]
	add	$input_l1, $cc, $rounds, lsl #4                   // borrow input_l1 for last key
	ldr     $rk0q, [$cc, #0]                                  // load rk0
	ldr     $rk1q, [$cc, #16]                                 // load rk1
	ldr     $rk2q, [$cc, #32]                                 // load rk2
	ldr     $rk3q, [$cc, #48]                                 // load rk3
	ldr     $rk4q, [$cc, #64]                                 // load rk4
	ldr     $rk5q, [$cc, #80]                                 // load rk5
	ldr     $rk6q, [$cc, #96]                                 // load rk6
	ldr     $rk7q, [$cc, #112]                                // load rk7
	ldr     $rk8q, [$cc, #128]                                // load rk8
	ldr     $rk9q, [$cc, #144]                                // load rk9
	ldr     $rk10q, [$cc, #160]                               // load rk10
	ldr     $rk11q, [$cc, #176]                               // load rk11
	ldr     $rk12q, [$cc, #192]                               // load rk12
	ldp     $rkN_l, $rkN_h, [$input_l1]                       // load round N keys
	ldr     $rkNm1q, [$input_l1, #-16]                        // load round N-1 keys
	add     $end_input_ptr, $input_ptr, $bit_length, lsr #3   // end_input_ptr
	lsr     $main_end_input_ptr, $bit_length, #3              // byte_len
	mov     $len, $main_end_input_ptr
	ldp     $ctr96_b64x, $ctr96_t32x, [$counter]              // ctr96_b64, ctr96_t32
	ld1     { $ctr0b}, [$counter]                             // special case vector load initial counter so we can start first AES block as quickly as possible
	sub     $main_end_input_ptr, $main_end_input_ptr, #1      // byte_len - 1
	and     $main_end_input_ptr, $main_end_input_ptr, #0xffffffffffffffc0 // number of bytes to be processed in main loop (at least 1 byte must be handled by tail)
	add     $main_end_input_ptr, $main_end_input_ptr, $input_ptr
	lsr     $rctr32x, $ctr96_t32x, #32
	orr     $ctr96_t32w, $ctr96_t32w, $ctr96_t32w
	rev     $rctr32w, $rctr32w                                // rev_ctr32
        add     $rctr32w, $rctr32w, #1                            // increment rev_ctr32

	fmov    $ctr1d, $ctr96_b64x                               // CTR block 1
	rev     $ctr32w, $rctr32w                                 // CTR block 1
	orr     $ctr32x, $ctr96_t32x, $ctr32x, lsl #32            // CTR block 1
	add     $rctr32w, $rctr32w, #1                            // CTR block 1
	fmov    $ctr1.d[1], $ctr32x                               // CTR block 1

	rev     $ctr32w, $rctr32w                                 // CTR block 2
	fmov    $ctr2d, $ctr96_b64x                               // CTR block 2
	add     $rctr32w, $rctr32w, #1                            // CTR block 2
	orr     $ctr32x, $ctr96_t32x, $ctr32x, lsl #32            // CTR block 2
	fmov    $ctr2.d[1], $ctr32x                               // CTR block 2

	fmov    $ctr3d, $ctr96_b64x                               // CTR block 3
	rev     $ctr32w, $rctr32w                                 // CTR block 3
	orr     $ctr32x, $ctr96_t32x, $ctr32x, lsl #32            // CTR block 3
	fmov    $ctr3.d[1], $ctr32x                               // CTR block 3
        add     $rctr32w, $rctr32w, #1                            // CTR block 3

	aese    $ctr0b, $rk0  \n  aesmc   $ctr0b, $ctr0b          // AES block 0 - round 0
	aese    $ctr0b, $rk1  \n  aesmc   $ctr0b, $ctr0b          // AES block 0 - round 1
	aese    $ctr0b, $rk2  \n  aesmc   $ctr0b, $ctr0b          // AES block 0 - round 2
	aese    $ctr0b, $rk3  \n  aesmc   $ctr0b, $ctr0b          // AES block 0 - round 3
	aese    $ctr0b, $rk4  \n  aesmc   $ctr0b, $ctr0b          // AES block 0 - round 4
	aese    $ctr0b, $rk5  \n  aesmc   $ctr0b, $ctr0b          // AES block 0 - round 5
	aese    $ctr0b, $rk6  \n  aesmc   $ctr0b, $ctr0b          // AES block 0 - round 6
	aese    $ctr0b, $rk7  \n  aesmc   $ctr0b, $ctr0b          // AES block 0 - round 7
	aese    $ctr0b, $rk8  \n  aesmc   $ctr0b, $ctr0b          // AES block 0 - round 8
	aese    $ctr1b, $rk0  \n  aesmc   $ctr1b, $ctr1b          // AES block 1 - round 0
	aese    $ctr1b, $rk1  \n  aesmc   $ctr1b, $ctr1b          // AES block 1 - round 1
	aese    $ctr1b, $rk2  \n  aesmc   $ctr1b, $ctr1b          // AES block 1 - round 2
	aese    $ctr1b, $rk3  \n  aesmc   $ctr1b, $ctr1b          // AES block 1 - round 3
	aese    $ctr1b, $rk4  \n  aesmc   $ctr1b, $ctr1b          // AES block 1 - round 4
	aese    $ctr1b, $rk5  \n  aesmc   $ctr1b, $ctr1b          // AES block 1 - round 5
	aese    $ctr1b, $rk6  \n  aesmc   $ctr1b, $ctr1b          // AES block 1 - round 6
	aese    $ctr1b, $rk7  \n  aesmc   $ctr1b, $ctr1b          // AES block 1 - round 7
	aese    $ctr1b, $rk8  \n  aesmc   $ctr1b, $ctr1b          // AES block 1 - round 8
	aese    $ctr2b, $rk0  \n  aesmc   $ctr2b, $ctr2b          // AES block 2 - round 0
	aese    $ctr2b, $rk1  \n  aesmc   $ctr2b, $ctr2b          // AES block 2 - round 1
	aese    $ctr2b, $rk2  \n  aesmc   $ctr2b, $ctr2b          // AES block 2 - round 2
	aese    $ctr2b, $rk3  \n  aesmc   $ctr2b, $ctr2b          // AES block 2 - round 3
	aese    $ctr2b, $rk4  \n  aesmc   $ctr2b, $ctr2b          // AES block 2 - round 4
	aese    $ctr2b, $rk5  \n  aesmc   $ctr2b, $ctr2b          // AES block 2 - round 5
	aese    $ctr2b, $rk6  \n  aesmc   $ctr2b, $ctr2b          // AES block 2 - round 6
	aese    $ctr2b, $rk7  \n  aesmc   $ctr2b, $ctr2b          // AES block 2 - round 7
	aese    $ctr2b, $rk8  \n  aesmc   $ctr2b, $ctr2b          // AES block 2 - round 8
	aese    $ctr3b, $rk0  \n  aesmc   $ctr3b, $ctr3b          // AES block 3 - round 0
	aese    $ctr3b, $rk1  \n  aesmc   $ctr3b, $ctr3b          // AES block 3 - round 1
	aese    $ctr3b, $rk2  \n  aesmc   $ctr3b, $ctr3b          // AES block 3 - round 2
	aese    $ctr3b, $rk3  \n  aesmc   $ctr3b, $ctr3b          // AES block 3 - round 3
	aese    $ctr3b, $rk4  \n  aesmc   $ctr3b, $ctr3b          // AES block 3 - round 4
	aese    $ctr3b, $rk5  \n  aesmc   $ctr3b, $ctr3b          // AES block 3 - round 5
	aese    $ctr3b, $rk6  \n  aesmc   $ctr3b, $ctr3b          // AES block 3 - round 6
	aese    $ctr3b, $rk7  \n  aesmc   $ctr3b, $ctr3b          // AES block 3 - round 7
	aese    $ctr3b, $rk8  \n  aesmc   $ctr3b, $ctr3b          // AES block 3 - round 8
	cmp     $rounds, #12                                      // setup flags for AES-128/192/256 check
	b.lt	.Lenc_finish_first_blocks                         // branch if AES-128

	aese    $ctr0b, $rk9  \n  aesmc   $ctr0b, $ctr0b          // AES block 0 - round 9
	aese    $ctr0b, $rk10 \n  aesmc   $ctr0b, $ctr0b          // AES block 0 - round 10
	aese    $ctr1b, $rk9  \n  aesmc   $ctr1b, $ctr1b          // AES block 1 - round 9
	aese    $ctr1b, $rk10 \n  aesmc   $ctr1b, $ctr1b          // AES block 1 - round 10
	aese    $ctr2b, $rk9  \n  aesmc   $ctr2b, $ctr2b          // AES block 2 - round 9
	aese    $ctr2b, $rk10 \n  aesmc   $ctr2b, $ctr2b          // AES block 2 - round 10
	aese    $ctr3b, $rk9  \n  aesmc   $ctr3b, $ctr3b          // AES block 3 - round 9
	aese    $ctr3b, $rk10 \n  aesmc   $ctr3b, $ctr3b          // AES block 3 - round 10
	b.eq	.Lenc_finish_first_blocks                         // branch if AES-192

	aese    $ctr0b, $rk11 \n  aesmc   $ctr0b, $ctr0b          // AES block 0 - round 11
	aese    $ctr0b, $rk12 \n  aesmc   $ctr0b, $ctr0b          // AES block 0 - round 12
	aese    $ctr1b, $rk11 \n  aesmc   $ctr1b, $ctr1b          // AES block 1 - round 11
	aese    $ctr1b, $rk12 \n  aesmc   $ctr1b, $ctr1b          // AES block 1 - round 12
	aese    $ctr2b, $rk11 \n  aesmc   $ctr2b, $ctr2b          // AES block 2 - round 11
	aese    $ctr2b, $rk12 \n  aesmc   $ctr2b, $ctr2b          // AES block 2 - round 12
	aese    $ctr3b, $rk11 \n  aesmc   $ctr3b, $ctr3b          // AES block 3 - round 11
	aese    $ctr3b, $rk12 \n  aesmc   $ctr3b, $ctr3b          // AES block 3 - round 12

.Lenc_finish_first_blocks:
	aese    $ctr0b, $rkNm1                                    // AES block 0 - round N-1
	aese    $ctr1b, $rkNm1                                    // AES block 1 - round N-1
	aese    $ctr2b, $rkNm1                                    // AES block 2 - round N-1
	aese    $ctr3b, $rkNm1                                    // AES block 3 - round N-1

	ldr     $h1q, [$Htable]                                   // load h1l | h1h
	ext     $h1b, $h1b, $h1b, #8
	ldr     $h3q, [$Htable, #48]                              // load h3l | h3h
	ext     $h3b, $h3b, $h3b, #8
	ldr     $h2q, [$Htable, #32]                              // load h2l | h2h
	ext     $h2b, $h2b, $h2b, #8
	ldr     $h4q, [$Htable, #80]                              // load h4l | h4h
	ext     $h4b, $h4b, $h4b, #8
	trn2    $h34k.2d,  $h3.2d,    $h4.2d                      // h4l | h3l
	trn1    $acc_h.2d, $h3.2d,    $h4.2d                      // h4h | h3h
	trn2    $h12k.2d,  $h1.2d,    $h2.2d                      // h2l | h1l
	eor     $h34k.16b, $h34k.16b, $acc_h.16b                  // h4k | h3k
	trn1    $t0.2d,    $h1.2d,    $h2.2d                      // h2h | h1h
	eor     $h12k.16b, $h12k.16b, $t0.16b                     // h2k | h1k

	ld1     { $acc_lb}, [$current_tag]
	ext     $acc_lb, $acc_lb, $acc_lb, #8
	rev64   $acc_lb, $acc_lb

        // At this point, have
        // - Computes N-1 rounds of AES, but not yet loaded+XOR'ed plaintext
        // - In consequence, not yet done any GHASH
        // - Not yet loaded CTR for next block

	cmp     $input_ptr, $main_end_input_ptr                   // check if we have <= 4 blocks
	b.ge    .Lenc_tail                                        // handle tail

	ldp     $input_l0, $input_h0, [$input_ptr, #0]            // AES block 0 - load plaintext
	eor     $input_l0, $input_l0, $rkN_l                      // AES block 0 - round N low
	eor     $input_h0, $input_h0, $rkN_h                      // AES block 0 - round N high
	fmov    $ctr_t0d, $input_l0                               // AES block 0 - mov low
	fmov    $ctr_t0.d[1], $input_h0                           // AES block 0 - mov high
	eor     $res0b, $ctr_t0b, $ctr0b                          // AES block 0 - result
	st1     { $res0b}, [$output_ptr], #16                     // AES block 0 - store result

	ldp     $input_l1, $input_h1, [$input_ptr, #16]           // AES block 1 - load plaintext
	eor     $input_l1, $input_l1, $rkN_l                      // AES block 1 - round N low
	eor     $input_h1, $input_h1, $rkN_h                      // AES block 1 - round N high
	fmov    $ctr_t1d, $input_l1                               // AES block 1 - mov low
	fmov    $ctr_t1.d[1], $input_h1                           // AES block 1 - mov high
	eor     $res1b, $ctr_t1b, $ctr1b                          // AES block 1 - result
	st1     { $res1b}, [$output_ptr], #16                     // AES block 1 - store result

	ldp     $input_l2, $input_h2, [$input_ptr, #32]           // AES block 2 - load plaintext
	eor     $input_l2, $input_l2, $rkN_l                      // AES block 2 - round N low
	fmov    $ctr_t2d, $input_l2                               // AES block 2 - mov low
	eor     $input_h2, $input_h2, $rkN_h                      // AES block 2 - round N high
	fmov    $ctr_t2.d[1], $input_h2                           // AES block 2 - mov high
	eor     $res2b, $ctr_t2b, $ctr2b                          // AES block 2 - result
	st1     { $res2b}, [$output_ptr], #16                     // AES block 2 - store result

	ldp     $input_l3, $input_h3, [$input_ptr, #48]           // AES block 3 - load plaintext
	eor     $input_h3, $input_h3, $rkN_h                      // AES block 3 - round N high
	eor     $input_l3, $input_l3, $rkN_l                      // AES block 3 - round N low
	fmov    $ctr_t3d, $input_l3                               // AES block 3 - mov low
	fmov    $ctr_t3.d[1], $input_h3                           // AES block 3 - mov high
	eor     $res3b, $ctr_t3b, $ctr3b                          // AES block 3 - result
	st1     { $res3b}, [$output_ptr], #16                     // AES block 3 - store result

	rev     $ctr32w, $rctr32w                                 // CTR block 4
	add     $rctr32w, $rctr32w, #1                            // CTR block 4
	orr     $ctr32x, $ctr96_t32x, $ctr32x, lsl #32            // CTR block 4
	fmov    $ctr0d, $ctr96_b64x                               // CTR block 4
	fmov    $ctr0.d[1], $ctr32x                               // CTR block 4

	rev     $ctr32w, $rctr32w                                 // CTR block 5
	add     $rctr32w, $rctr32w, #1                            // CTR block 5
	fmov    $ctr1d, $ctr96_b64x                               // CTR block 5
	orr     $ctr32x, $ctr96_t32x, $ctr32x, lsl #32            // CTR block 5
	fmov    $ctr1.d[1], $ctr32x                               // CTR block 5

	rev     $ctr32w, $rctr32w                                 // CTR block 6
	orr     $ctr32x, $ctr96_t32x, $ctr32x, lsl #32            // CTR block 6
	add     $rctr32w, $rctr32w, #1                            // CTR block 6
	fmov    $ctr2d, $ctr96_b64x                               // CTR block 6
	fmov    $ctr2.d[1], $ctr32x                               // CTR block 6

	rev     $ctr32w, $rctr32w                                 // CTR block 7
	orr     $ctr32x, $ctr96_t32x, $ctr32x, lsl #32            // CTR block 7
	add     $input_ptr, $input_ptr, #64                       // AES input_ptr update
	cmp     $input_ptr, $main_end_input_ptr                   // check if we have <= 8 blocks
	b.ge    .Lenc_prepretail                                  // do prepretail

        // At this point, we have
        // - Finalized and stored result of last x4-batched AES
        // - Prepared next 4 counters, except for 4k+3 (unclear why)
        // - Not yet done _any_ GHASH computation

.Lenc_main_loop:                                                  // main loop start
	fmov    $ctr3d, $ctr96_b64x                               // CTR block 4k+3
	fmov    $ctr3.d[1], $ctr32x                               // CTR block 4k+3
	add     $rctr32w, $rctr32w, #1                            // CTR block 4k+3
	rev64   $res0b, $res0b                                    // GHASH block 4k (only t0 is free)
	ext     $acc_lb, $acc_lb, $acc_lb, #8                     // PRE 0
	eor     $res0b, $res0b, $acc_lb                           // PRE 1
	mov     $acc_md, $h34k.d[1]                               // GHASH block 4k - mid
	pmull2  $acc_h.1q, $res0.2d, $h4.2d                       // GHASH block 4k - high
	mov     $t0d, $res0.d[1]                                  // GHASH block 4k - mid
	pmull   $acc_l.1q, $res0.1d, $h4.1d                       // GHASH block 4k - low
	eor     $t0.8b, $t0.8b, $res0.8b                          // GHASH block 4k - mid
	pmull   $acc_m.1q, $t0.1d, $acc_m.1d                      // GHASH block 4k - mid
	rev64   $res1b, $res1b                                    // GHASH block 4k+1 (t0 and t1 free)
	pmull2  $t1.1q, $res1.2d, $h3.2d                          // GHASH block 4k+1 - high
	pmull   $t2.1q, $res1.1d, $h3.1d                          // GHASH block 4k+1 - low
	eor     $acc_hb, $acc_hb, $t1.16b                         // GHASH block 4k+1 - high
	mov     $t3d, $res1.d[1]                                  // GHASH block 4k+1 - mid
	eor     $acc_lb, $acc_lb, $t2.16b                         // GHASH block 4k+1 - low
	eor     $t3.8b, $t3.8b, $res1.8b                          // GHASH block 4k+1 - mid
	pmull   $t3.1q, $t3.1d, $h34k.1d                          // GHASH block 4k+1 - mid
	eor     $acc_mb, $acc_mb, $t3.16b                         // GHASH block 4k+1 - mid
	rev64   $res2b, $res2b                                    // GHASH block 4k+2 (t0, t1, and t2 free)
	mov     $t6d, $res2.d[1]                                  // GHASH block 4k+2 - mid
	eor     $t6.8b, $t6.8b, $res2.8b                          // GHASH block 4k+2 - mid
	ins     $t6.d[1], $t6.d[0]                                // GHASH block 4k+2 - mid
	pmull2  $t4.1q, $res2.2d, $h2.2d                          // GHASH block 4k+2 - high
	pmull   $t5.1q, $res2.1d, $h2.1d                          // GHASH block 4k+2 - low
	eor     $acc_hb, $acc_hb, $t4.16b                         // GHASH block 4k+2 - high
	eor     $acc_lb, $acc_lb, $t5.16b                         // GHASH block 4k+2 - low
	pmull2  $t6.1q, $t6.2d, $h12k.2d                          // GHASH block 4k+2 - mid
	eor     $acc_mb, $acc_mb, $t6.16b                         // GHASH block 4k+2 - mid
	rev64   $res3b, $res3b                                    // GHASH block 4k+3 (t0, t1, t2 and t3 free)
	pmull   $t8.1q, $res3.1d, $h1.1d                          // GHASH block 4k+3 - low
	mov     $t9d, $res3.d[1]                                  // GHASH block 4k+3 - mid
	pmull2  $t7.1q, $res3.2d, $h1.2d                          // GHASH block 4k+3 - high
	eor     $t9.8b, $t9.8b, $res3.8b                          // GHASH block 4k+3 - mid
	pmull   $t9.1q, $t9.1d, $h12k.1d                          // GHASH block 4k+3 - mid
	eor     $acc_hb, $acc_hb, $t7.16b                         // GHASH block 4k+3 - high
	eor     $acc_lb, $acc_lb, $t8.16b                         // GHASH block 4k+3 - low
	eor     $acc_mb, $acc_mb, $t9.16b                         // GHASH block 4k+3 - mid
	movi    $mod_constant.8b, #0xc2
	shl     $mod_constantd, $mod_constantd, #56               // mod_constant
	eor     $t9.16b, $acc_lb, $acc_hb                         // MODULO - karatsuba tidy up
	pmull   $mod_t.1q, $acc_h.1d, $mod_constant.1d            // MODULO - top 64b align with mid
	ext     $acc_hb, $acc_hb, $acc_hb, #8                     // MODULO - other top alignment
	eor     $acc_mb, $acc_mb, $t9.16b                         // MODULO - karatsuba tidy up
	eor     $mod_t.16b, $acc_hb, $mod_t.16b                   // MODULO - fold into mid
	eor     $acc_mb, $acc_mb, $mod_t.16b                      // MODULO - fold into mid
	pmull   $acc_h.1q, $acc_m.1d, $mod_constant.1d            // MODULO - mid 64b align with low
	eor     $acc_lb, $acc_lb, $acc_hb                         // MODULO - fold into low
	ext     $acc_mb, $acc_mb, $acc_mb, #8                     // MODULO - other mid alignment
	eor     $acc_lb, $acc_lb, $acc_mb                         // MODULO - fold into low
	aese    $ctr0b, $rk0  \n  aesmc   $ctr0b, $ctr0b          // AES block 4k+4 - round 0
	aese    $ctr0b, $rk1  \n  aesmc   $ctr0b, $ctr0b          // AES block 4k+4 - round 1
	aese    $ctr0b, $rk2  \n  aesmc   $ctr0b, $ctr0b          // AES block 4k+4 - round 2
	aese    $ctr0b, $rk3  \n  aesmc   $ctr0b, $ctr0b          // AES block 4k+4 - round 3
	aese    $ctr0b, $rk4  \n  aesmc   $ctr0b, $ctr0b          // AES block 4k+4 - round 4
	aese    $ctr0b, $rk5  \n  aesmc   $ctr0b, $ctr0b          // AES block 4k+4 - round 5
	aese    $ctr0b, $rk6  \n  aesmc   $ctr0b, $ctr0b          // AES block 4k+4 - round 6
	aese    $ctr0b, $rk7  \n  aesmc   $ctr0b, $ctr0b          // AES block 4k+4 - round 7
	aese    $ctr0b, $rk8  \n  aesmc   $ctr0b, $ctr0b          // AES block 4k+4 - round 8
	ldp     $input_l0, $input_h0, [$input_ptr, #0]            // AES block 4k+4 - load plaintext
	aese    $ctr1b, $rk0  \n  aesmc   $ctr1b, $ctr1b          // AES block 4k+5 - round 0
	aese    $ctr1b, $rk1  \n  aesmc   $ctr1b, $ctr1b          // AES block 4k+5 - round 1
	aese    $ctr1b, $rk2  \n  aesmc   $ctr1b, $ctr1b          // AES block 4k+5 - round 2
	aese    $ctr1b, $rk3  \n  aesmc   $ctr1b, $ctr1b          // AES block 4k+5 - round 3
	aese    $ctr1b, $rk4  \n  aesmc   $ctr1b, $ctr1b          // AES block 4k+5 - round 4
	aese    $ctr1b, $rk5  \n  aesmc   $ctr1b, $ctr1b          // AES block 4k+5 - round 5
	aese    $ctr1b, $rk6  \n  aesmc   $ctr1b, $ctr1b          // AES block 4k+5 - round 6
	aese    $ctr1b, $rk7  \n  aesmc   $ctr1b, $ctr1b          // AES block 4k+5 - round 7
	ldp     $input_l1, $input_h1, [$input_ptr, #16]           // AES block 4k+5 - load plaintext
	aese    $ctr2b, $rk0  \n  aesmc   $ctr2b, $ctr2b          // AES block 4k+6 - round 0
	aese    $ctr2b, $rk1  \n  aesmc   $ctr2b, $ctr2b          // AES block 4k+6 - round 1
	aese    $ctr2b, $rk2  \n  aesmc   $ctr2b, $ctr2b          // AES block 4k+6 - round 2
	aese    $ctr2b, $rk3  \n  aesmc   $ctr2b, $ctr2b          // AES block 4k+6 - round 3
	aese    $ctr2b, $rk4  \n  aesmc   $ctr2b, $ctr2b          // AES block 4k+6 - round 4
	aese    $ctr2b, $rk5  \n  aesmc   $ctr2b, $ctr2b          // AES block 4k+6 - round 5
	aese    $ctr1b, $rk8  \n  aesmc   $ctr1b, $ctr1b          // AES block 4k+5 - round 8
	aese    $ctr2b, $rk6  \n  aesmc   $ctr2b, $ctr2b          // AES block 4k+6 - round 6
	aese    $ctr2b, $rk7  \n  aesmc   $ctr2b, $ctr2b          // AES block 4k+6 - round 7
	aese    $ctr2b, $rk8  \n  aesmc   $ctr2b, $ctr2b          // AES block 4k+6 - round 8
	ldp     $input_l2, $input_h2, [$input_ptr, #32]           // AES block 4k+6 - load plaintext
	aese    $ctr3b, $rk0  \n  aesmc   $ctr3b, $ctr3b          // AES block 4k+7 - round 0
	aese    $ctr3b, $rk1  \n  aesmc   $ctr3b, $ctr3b          // AES block 4k+7 - round 1
	aese    $ctr3b, $rk2  \n  aesmc   $ctr3b, $ctr3b          // AES block 4k+7 - round 2
	aese    $ctr3b, $rk3  \n  aesmc   $ctr3b, $ctr3b          // AES block 4k+7 - round 3
	aese    $ctr3b, $rk4  \n  aesmc   $ctr3b, $ctr3b          // AES block 4k+7 - round 4
	aese    $ctr3b, $rk5  \n  aesmc   $ctr3b, $ctr3b          // AES block 4k+7 - round 5
	aese    $ctr3b, $rk6  \n  aesmc   $ctr3b, $ctr3b          // AES block 4k+7 - round 6
	aese    $ctr3b, $rk7  \n  aesmc   $ctr3b, $ctr3b          // AES block 4k+7 - round 7
	aese    $ctr3b, $rk8  \n  aesmc   $ctr3b, $ctr3b          // AES block 4k+7 - round 8
	ldp     $input_l3, $input_h3, [$input_ptr, #48]           // AES block 4k+7 - load plaintext
	cmp     $rounds, #12                                      // setup flags for AES-128/192/256 check
	b.lt	.Lenc_main_loop_continue                          // branch if AES-128

	aese    $ctr0b, $rk9  \n  aesmc   $ctr0b, $ctr0b          // AES block 4k+4 - round 9
	aese    $ctr0b, $rk10 \n  aesmc   $ctr0b, $ctr0b          // AES block 4k+4 - round 10
	aese    $ctr1b, $rk9  \n  aesmc   $ctr1b, $ctr1b          // AES block 4k+5 - round 9
	aese    $ctr1b, $rk10 \n  aesmc   $ctr1b, $ctr1b          // AES block 4k+5 - round 10
	aese    $ctr2b, $rk9  \n  aesmc   $ctr2b, $ctr2b          // AES block 4k+6 - round 9
	aese    $ctr2b, $rk10 \n  aesmc   $ctr2b, $ctr2b          // AES block 4k+6 - round 10
	aese    $ctr3b, $rk9  \n  aesmc   $ctr3b, $ctr3b          // AES block 4k+7 - round 9
	aese    $ctr3b, $rk10 \n  aesmc   $ctr3b, $ctr3b          // AES block 4k+7 - round 10
	b.eq	.Lenc_main_loop_continue                          // branch if AES-192

	aese    $ctr0b, $rk11 \n  aesmc   $ctr0b, $ctr0b          // AES block 4k+4 - round 11
	aese    $ctr0b, $rk12 \n  aesmc   $ctr0b, $ctr0b          // AES block 4k+4 - round 12
	aese    $ctr1b, $rk11 \n  aesmc   $ctr1b, $ctr1b          // AES block 4k+5 - round 11
	aese    $ctr1b, $rk12 \n  aesmc   $ctr1b, $ctr1b          // AES block 4k+5 - round 12
	aese    $ctr2b, $rk11 \n  aesmc   $ctr2b, $ctr2b          // AES block 4k+6 - round 11
	aese    $ctr2b, $rk12 \n  aesmc   $ctr2b, $ctr2b          // AES block 4k+6 - round 12
	aese    $ctr3b, $rk11 \n  aesmc   $ctr3b, $ctr3b          // AES block 4k+7 - round 11
	aese    $ctr3b, $rk12 \n  aesmc   $ctr3b, $ctr3b          // AES block 4k+7 - round 12

.Lenc_main_loop_continue:
	aese    $ctr0b, $rkNm1                                    // AES block 4k+4 - round N-1
	eor     $input_l0, $input_l0, $rkN_l                      // AES block 4k+4 - round N low
	eor     $input_h0, $input_h0, $rkN_h                      // AES block 4k+4 - round N high
	fmov    $ctr_t0d, $input_l0                               // AES block 4k+4 - mov low
	fmov    $ctr_t0.d[1], $input_h0                           // AES block 4k+4 - mov high
	eor     $res0b, $ctr_t0b, $ctr0b                          // AES block 4k+4 - result
	st1     { $res0b}, [$output_ptr], #16                     // AES block 4k+4 - store result

	aese    $ctr1b, $rkNm1                                    // AES block 4k+5 - round N-1
	eor     $input_l1, $input_l1, $rkN_l                      // AES block 4k+5 - round N low
	eor     $input_h1, $input_h1, $rkN_h                      // AES block 4k+5 - round N high
	fmov    $ctr_t1d, $input_l1                               // AES block 4k+5 - mov low
	fmov    $ctr_t1.d[1], $input_h1                           // AES block 4k+5 - mov high
	eor     $res1b, $ctr_t1b, $ctr1b                          // AES block 4k+5 - result
	st1     { $res1b}, [$output_ptr], #16                     // AES block 4k+5 - store result

	aese    $ctr2b, $rkNm1                                    // AES block 4k+6 - round N-1
	eor     $input_h2, $input_h2, $rkN_h                      // AES block 4k+6 - round N high
	eor     $input_l2, $input_l2, $rkN_l                      // AES block 4k+6 - round N low
	fmov    $ctr_t2d, $input_l2                               // AES block 4k+6 - mov low
	fmov    $ctr_t2.d[1], $input_h2                           // AES block 4k+6 - mov high
	eor     $res2b, $ctr_t2b, $ctr2b                          // AES block 4k+6 - result
	st1     { $res2b}, [$output_ptr], #16                     // AES block 4k+6 - store result

	aese    $ctr3b, $rkNm1                                    // AES block 4k+7 - round N-1
	eor     $input_l3, $input_l3, $rkN_l                      // AES block 4k+7 - round N low
	eor     $input_h3, $input_h3, $rkN_h                      // AES block 4k+7 - round N high
	fmov    $ctr_t3d, $input_l3                               // AES block 4k+7 - mov low
	fmov    $ctr_t3.d[1], $input_h3                           // AES block 4k+7 - mov high
	eor     $res3b, $ctr_t3b, $ctr3b                          // AES block 4k+7 - result
	st1     { $res3b}, [$output_ptr], #16                     // AES block 4k+7 - store result

	rev     $ctr32w, $rctr32w                                 // CTR block 4k+8
	orr     $ctr32x, $ctr96_t32x, $ctr32x, lsl #32            // CTR block 4k+8
	add     $rctr32w, $rctr32w, #1                            // CTR block 4k+8
	fmov    $ctr0d, $ctr96_b64x                               // CTR block 4k+8
	fmov    $ctr0.d[1], $ctr32x                               // CTR block 4k+8

	rev     $ctr32w, $rctr32w                                 // CTR block 4k+9
	add     $rctr32w, $rctr32w, #1                            // CTR block 4k+9
	fmov    $ctr1d, $ctr96_b64x                               // CTR block 4k+9
	orr     $ctr32x, $ctr96_t32x, $ctr32x, lsl #32            // CTR block 4k+9
	fmov    $ctr1.d[1], $ctr32x                               // CTR block 4k+9

	rev     $ctr32w, $rctr32w                                 // CTR block 4k+10
	orr     $ctr32x, $ctr96_t32x, $ctr32x, lsl #32            // CTR block 4k+10
	add     $rctr32w, $rctr32w, #1                            // CTR block 4k+10
	fmov    $ctr2d, $ctr96_b64x                               // CTR block 4k+10
	fmov    $ctr2.d[1], $ctr32x                               // CTR block 4k+10

	rev     $ctr32w, $rctr32w                                 // CTR block 4k+11
	orr     $ctr32x, $ctr96_t32x, $ctr32x, lsl #32            // CTR block 4k+11
	add     $input_ptr, $input_ptr, #64                       // AES input_ptr update
	cmp     $input_ptr, $main_end_input_ptr                   // LOOP CONTROL
	b.lt    .Lenc_main_loop

.Lenc_prepretail:                                                 // PREPRETAIL

	fmov    $ctr3d, $ctr96_b64x                               // CTR block 4k+3
	fmov    $ctr3.d[1], $ctr32x                               // CTR block 4k+3
	add     $rctr32w, $rctr32w, #1                            // CTR block 4k+3

	rev64   $res0b, $res0b                                    // GHASH block 4k (only t0 is free)
	rev64   $res1b, $res1b                                    // GHASH block 4k+1 (t0 and t1 free)
	rev64   $res2b, $res2b                                    // GHASH block 4k+2 (t0, t1, and t2 free)
	rev64   $res3b, $res3b                                    // GHASH block 4k+3 (t0, t1, t2 and t3 free)

	ext     $acc_lb, $acc_lb, $acc_lb, #8                     // PRE 0
	eor     $res0b, $res0b, $acc_lb                           // PRE 1
	pmull   $acc_l.1q, $res0.1d, $h4.1d                       // GHASH block 4k - low
	mov     $acc_md, $h34k.d[1]                               // GHASH block 4k - mid
	mov     $t0d, $res0.d[1]                                  // GHASH block 4k - mid
	pmull2  $acc_h.1q, $res0.2d, $h4.2d                       // GHASH block 4k - high
	eor     $t0.8b, $t0.8b, $res0.8b                          // GHASH block 4k - mid
	pmull   $acc_m.1q, $t0.1d, $acc_m.1d                      // GHASH block 4k - mid
	pmull2  $t1.1q, $res1.2d, $h3.2d                          // GHASH block 4k+1 - high
	pmull   $t2.1q, $res1.1d, $h3.1d                          // GHASH block 4k+1 - low
	eor     $acc_hb, $acc_hb, $t1.16b                         // GHASH block 4k+1 - high
	mov     $t3d, $res1.d[1]                                  // GHASH block 4k+1 - mid
	eor     $acc_lb, $acc_lb, $t2.16b                         // GHASH block 4k+1 - low
	eor     $t3.8b, $t3.8b, $res1.8b                          // GHASH block 4k+1 - mid
	mov     $t6d, $res2.d[1]                                  // GHASH block 4k+2 - mid
	pmull   $t3.1q, $t3.1d, $h34k.1d                          // GHASH block 4k+1 - mid
	eor     $t6.8b, $t6.8b, $res2.8b                          // GHASH block 4k+2 - mid
	pmull   $t5.1q, $res2.1d, $h2.1d                          // GHASH block 4k+2 - low
	eor     $acc_mb, $acc_mb, $t3.16b                         // GHASH block 4k+1 - mid
	pmull2  $t4.1q, $res2.2d, $h2.2d                          // GHASH block 4k+2 - high
	eor     $acc_lb, $acc_lb, $t5.16b                         // GHASH block 4k+2 - low
	ins     $t6.d[1], $t6.d[0]                                // GHASH block 4k+2 - mid
	eor     $acc_hb, $acc_hb, $t4.16b                         // GHASH block 4k+2 - high
	mov     $t9d, $res3.d[1]                                  // GHASH block 4k+3 - mid
	pmull2  $t6.1q, $t6.2d, $h12k.2d                          // GHASH block 4k+2 - mid
	eor     $t9.8b, $t9.8b, $res3.8b                          // GHASH block 4k+3 - mid
	pmull2  $t7.1q, $res3.2d, $h1.2d                          // GHASH block 4k+3 - high
	pmull   $t9.1q, $t9.1d, $h12k.1d                          // GHASH block 4k+3 - mid
	eor     $acc_mb, $acc_mb, $t6.16b                         // GHASH block 4k+2 - mid
	eor     $acc_hb, $acc_hb, $t7.16b                         // GHASH block 4k+3 - high
	eor     $acc_mb, $acc_mb, $t9.16b                         // GHASH block 4k+3 - mid
	pmull   $t8.1q, $res3.1d, $h1.1d                          // GHASH block 4k+3 - low
	eor     $acc_lb, $acc_lb, $t8.16b                         // GHASH block 4k+3 - low

	movi    $mod_constant.8b, #0xc2
	shl     $mod_constantd, $mod_constantd, #56               // mod_constant
	eor     $acc_mb, $acc_mb, $acc_hb                         // karatsuba tidy up
	pmull   $t1.1q, $acc_h.1d, $mod_constant.1d
	ext     $acc_hb, $acc_hb, $acc_hb, #8
	eor     $acc_mb, $acc_mb, $acc_lb
	eor     $acc_mb, $acc_mb, $t1.16b
	eor     $acc_mb, $acc_mb, $acc_hb
	pmull   $t1.1q, $acc_m.1d, $mod_constant.1d
	ext     $acc_mb, $acc_mb, $acc_mb, #8
	eor     $acc_lb, $acc_lb, $t1.16b
	eor     $acc_lb, $acc_lb, $acc_mb

	aese    $ctr0b, $rk0  \n  aesmc   $ctr0b, $ctr0b          // AES block 4k+4 - round 0
	aese    $ctr0b, $rk1  \n  aesmc   $ctr0b, $ctr0b          // AES block 4k+4 - round 1
	aese    $ctr0b, $rk2  \n  aesmc   $ctr0b, $ctr0b          // AES block 4k+4 - round 2
	aese    $ctr0b, $rk3  \n  aesmc   $ctr0b, $ctr0b          // AES block 4k+4 - round 3
	aese    $ctr0b, $rk4  \n  aesmc   $ctr0b, $ctr0b          // AES block 4k+4 - round 4
	aese    $ctr0b, $rk5  \n  aesmc   $ctr0b, $ctr0b          // AES block 4k+4 - round 5
	aese    $ctr0b, $rk6  \n  aesmc   $ctr0b, $ctr0b          // AES block 4k+4 - round 6
	aese    $ctr0b, $rk7  \n  aesmc   $ctr0b, $ctr0b          // AES block 4k+4 - round 7
	aese    $ctr0b, $rk8  \n  aesmc   $ctr0b, $ctr0b          // AES block 4k+4 - round 8

	aese    $ctr1b, $rk0  \n  aesmc   $ctr1b, $ctr1b          // AES block 4k+5 - round 0
	aese    $ctr1b, $rk1  \n  aesmc   $ctr1b, $ctr1b          // AES block 4k+5 - round 1
	aese    $ctr1b, $rk2  \n  aesmc   $ctr1b, $ctr1b          // AES block 4k+5 - round 2
	aese    $ctr1b, $rk3  \n  aesmc   $ctr1b, $ctr1b          // AES block 4k+5 - round 3
	aese    $ctr1b, $rk4  \n  aesmc   $ctr1b, $ctr1b          // AES block 4k+5 - round 4
	aese    $ctr1b, $rk5  \n  aesmc   $ctr1b, $ctr1b          // AES block 4k+5 - round 5
	aese    $ctr1b, $rk6  \n  aesmc   $ctr1b, $ctr1b          // AES block 4k+5 - round 6
	aese    $ctr1b, $rk7  \n  aesmc   $ctr1b, $ctr1b          // AES block 4k+5 - round 7
	aese    $ctr1b, $rk8  \n  aesmc   $ctr1b, $ctr1b          // AES block 4k+5 - round 8

	aese    $ctr2b, $rk0  \n  aesmc   $ctr2b, $ctr2b          // AES block 4k+6 - round 0
	aese    $ctr2b, $rk1  \n  aesmc   $ctr2b, $ctr2b          // AES block 4k+6 - round 1
	aese    $ctr2b, $rk2  \n  aesmc   $ctr2b, $ctr2b          // AES block 4k+6 - round 2
	aese    $ctr2b, $rk3  \n  aesmc   $ctr2b, $ctr2b          // AES block 4k+6 - round 3
	aese    $ctr2b, $rk4  \n  aesmc   $ctr2b, $ctr2b          // AES block 4k+6 - round 4
	aese    $ctr2b, $rk5  \n  aesmc   $ctr2b, $ctr2b          // AES block 4k+6 - round 5
	aese    $ctr2b, $rk6  \n  aesmc   $ctr2b, $ctr2b          // AES block 4k+6 - round 6
	aese    $ctr3b, $rk0  \n  aesmc   $ctr3b, $ctr3b          // AES block 4k+7 - round 0
	aese    $ctr2b, $rk7  \n  aesmc   $ctr2b, $ctr2b          // AES block 4k+6 - round 7
	aese    $ctr2b, $rk8  \n  aesmc   $ctr2b, $ctr2b          // AES block 4k+6 - round 8

	aese    $ctr3b, $rk1  \n  aesmc   $ctr3b, $ctr3b          // AES block 4k+7 - round 1
	aese    $ctr3b, $rk2  \n  aesmc   $ctr3b, $ctr3b          // AES block 4k+7 - round 2
	aese    $ctr3b, $rk3  \n  aesmc   $ctr3b, $ctr3b          // AES block 4k+7 - round 3
	aese    $ctr3b, $rk4  \n  aesmc   $ctr3b, $ctr3b          // AES block 4k+7 - round 4
	aese    $ctr3b, $rk5  \n  aesmc   $ctr3b, $ctr3b          // AES block 4k+7 - round 5
	aese    $ctr3b, $rk6  \n  aesmc   $ctr3b, $ctr3b          // AES block 4k+7 - round 6
	aese    $ctr3b, $rk7  \n  aesmc   $ctr3b, $ctr3b          // AES block 4k+7 - round 7
	aese    $ctr3b, $rk8  \n  aesmc   $ctr3b, $ctr3b          // AES block 4k+7 - round 8

	cmp     $rounds, #12                                      // setup flags for AES-128/192/256 check
	b.lt	.Lenc_finish_prepretail                           // branch if AES-128

	aese    $ctr0b, $rk9  \n  aesmc   $ctr0b, $ctr0b          // AES block 4k+4 - round 9
	aese    $ctr0b, $rk10 \n  aesmc   $ctr0b, $ctr0b          // AES block 4k+4 - round 10
	aese    $ctr1b, $rk9  \n  aesmc   $ctr1b, $ctr1b          // AES block 4k+5 - round 9
	aese    $ctr1b, $rk10 \n  aesmc   $ctr1b, $ctr1b          // AES block 4k+5 - round 10
	aese    $ctr2b, $rk9  \n  aesmc   $ctr2b, $ctr2b          // AES block 4k+6 - round 9
	aese    $ctr2b, $rk10 \n  aesmc   $ctr2b, $ctr2b          // AES block 4k+6 - round 10
	aese    $ctr3b, $rk9  \n  aesmc   $ctr3b, $ctr3b          // AES block 4k+7 - round 9
	aese    $ctr3b, $rk10 \n  aesmc   $ctr3b, $ctr3b          // AES block 4k+7 - round 10
	b.eq	.Lenc_finish_prepretail                           // branch if AES-192

	aese    $ctr0b, $rk11 \n  aesmc   $ctr0b, $ctr0b          // AES block 4k+4 - round 11
	aese    $ctr0b, $rk12 \n  aesmc   $ctr0b, $ctr0b          // AES block 4k+4 - round 12
	aese    $ctr1b, $rk11 \n  aesmc   $ctr1b, $ctr1b          // AES block 4k+5 - round 11
	aese    $ctr1b, $rk12 \n  aesmc   $ctr1b, $ctr1b          // AES block 4k+5 - round 12
	aese    $ctr2b, $rk11 \n  aesmc   $ctr2b, $ctr2b          // AES block 4k+6 - round 11
	aese    $ctr2b, $rk12 \n  aesmc   $ctr2b, $ctr2b          // AES block 4k+6 - round 12
	aese    $ctr3b, $rk11 \n  aesmc   $ctr3b, $ctr3b          // AES block 4k+7 - round 11
	aese    $ctr3b, $rk12 \n  aesmc   $ctr3b, $ctr3b          // AES block 4k+7 - round 12

.Lenc_finish_prepretail:
	aese    $ctr1b, $rkNm1                                    // AES block 4k+5 - round N-1
	aese    $ctr3b, $rkNm1                                    // AES block 4k+7 - round N-1
	aese    $ctr0b, $rkNm1                                    // AES block 4k+4 - round N-1
	aese    $ctr2b, $rkNm1                                    // AES block 4k+6 - round N-1

.Lenc_tail:                                                       // TAIL
	ext     $t0.16b, $acc_lb, $acc_lb, #8                     // prepare final partial tag
	sub     $main_end_input_ptr, $end_input_ptr, $input_ptr   // main_end_input_ptr is number of bytes left to process
	ldp     $input_l0, $input_h0, [$input_ptr], #16           // AES block 4k+4 - load plaintext
	eor     $input_l0, $input_l0, $rkN_l                      // AES block 4k+4 - round N low
	eor     $input_h0, $input_h0, $rkN_h                      // AES block 4k+4 - round N high
	cmp     $main_end_input_ptr, #48
	fmov    $ctr_t0d, $input_l0                               // AES block 4k+4 - mov low
	fmov    $ctr_t0.d[1], $input_h0                           // AES block 4k+4 - mov high
	eor     $res1b, $ctr_t0b, $ctr0b                          // AES block 4k+4 - result
	b.gt    .Lenc_blocks_4_remaining
	cmp     $main_end_input_ptr, #32
	mov     $ctr3b, $ctr2b
	movi    $acc_l.8b, #0
	movi    $acc_h.8b, #0
	sub     $rctr32w, $rctr32w, #1
	mov     $ctr2b, $ctr1b
	movi    $acc_m.8b, #0
	b.gt    .Lenc_blocks_3_remaining
	mov     $ctr3b, $ctr1b
	sub     $rctr32w, $rctr32w, #1
	cmp     $main_end_input_ptr, #16
	b.gt    .Lenc_blocks_2_remaining
	sub     $rctr32w, $rctr32w, #1
	b       .Lenc_blocks_1_remaining
.Lenc_blocks_4_remaining:                                        // blocks left = 4
	st1     { $res1b}, [$output_ptr], #16                    // AES final-3 block  - store result
	rev64   $res0b, $res1b                                   // GHASH final-3 block
	eor     $res0b, $res0b, $t0.16b                          // feed in partial tag
	mov     $rk4d, $res0.d[1]                                // GHASH final-3 block - mid
	eor     $rk4v.8b, $rk4v.8b, $res0.8b                     // GHASH final-3 block - mid
	mov     $acc_md, $h34k.d[1]                              // GHASH final-3 block - mid
	pmull   $acc_l.1q, $res0.1d, $h4.1d                      // GHASH final-3 block - low
	pmull2  $acc_h.1q, $res0.2d, $h4.2d                      // GHASH final-3 block - high
	pmull   $acc_m.1q, $rk4v.1d, $acc_m.1d                   // GHASH final-3 block - mid
	movi    $t0.8b, #0                                       // suppress further partial tag feed in
	ldp     $input_l0, $input_h0, [$input_ptr], #16          // AES final-2 block - load input low & high
	eor     $input_l0, $input_l0, $rkN_l                     // AES final-2 block - round N low
	eor     $input_h0, $input_h0, $rkN_h                     // AES final-2 block - round N high
	fmov    $res1d, $input_l0                                // AES final-2 block - mov low
	fmov    $res1.d[1], $input_h0                            // AES final-2 block - mov high
	eor     $res1b, $res1b, $ctr1b                           // AES final-2 block - result
.Lenc_blocks_3_remaining:                                        // blocks left = 3
	st1     { $res1b}, [$output_ptr], #16                    // AES final-2 block - store result
	rev64   $res0b, $res1b                                   // GHASH final-2 block
	eor     $res0b, $res0b, $t0.16b                          // feed in partial tag
	pmull2  $rk2q1, $res0.2d, $h3.2d                         // GHASH final-2 block - high
	mov     $rk4d, $res0.d[1]                                // GHASH final-2 block - mid
	pmull   $rk3q1, $res0.1d, $h3.1d                         // GHASH final-2 block - low
	eor     $rk4v.8b, $rk4v.8b, $res0.8b                     // GHASH final-2 block - mid
	eor     $acc_hb, $acc_hb, $rk2                           // GHASH final-2 block - high
	pmull   $rk4v.1q, $rk4v.1d, $h34k.1d                     // GHASH final-2 block - mid
	eor     $acc_lb, $acc_lb, $rk3                           // GHASH final-2 block - low
	eor     $acc_mb, $acc_mb, $rk4v.16b                      // GHASH final-2 block - mid
	movi    $t0.8b, #0                                       // suppress further partial tag feed in
	ldp     $input_l0, $input_h0, [$input_ptr], #16          // AES final-1 block - load input low & high
	eor     $input_l0, $input_l0, $rkN_l                     // AES final-1 block - round N low
	fmov    $res1d, $input_l0                                // AES final-1 block - mov low
	eor     $input_h0, $input_h0, $rkN_h                     // AES final-1 block - round N high
	fmov    $res1.d[1], $input_h0                            // AES final-1 block - mov high
	eor     $res1b, $res1b, $ctr2b                           // AES final-1 block - result
.Lenc_blocks_2_remaining:                                        // blocks left = 2
	st1     { $res1b}, [$output_ptr], #16                    // AES final-1 block - store result
	rev64   $res0b, $res1b                                   // GHASH final-1 block
	eor     $res0b, $res0b, $t0.16b                          // feed in partial tag
	mov     $rk4d, $res0.d[1]                                // GHASH final-1 block - mid
	pmull2  $rk2q1, $res0.2d, $h2.2d                         // GHASH final-1 block - high
	eor     $rk4v.8b, $rk4v.8b, $res0.8b                     // GHASH final-1 block - mid
	eor     $acc_hb, $acc_hb, $rk2                           // GHASH final-1 block - high
	ins     $rk4v.d[1], $rk4v.d[0]                           // GHASH final-1 block - mid
	pmull2  $rk4v.1q, $rk4v.2d, $h12k.2d                     // GHASH final-1 block - mid
	pmull   $rk3q1, $res0.1d, $h2.1d                         // GHASH final-1 block - low
	eor     $acc_mb, $acc_mb, $rk4v.16b                      // GHASH final-1 block - mid
	eor     $acc_lb, $acc_lb, $rk3                           // GHASH final-1 block - low
	movi    $t0.8b, #0                                       // suppress further partial tag feed in
	ldp     $input_l0, $input_h0, [$input_ptr], #16          // AES final block - load input low & high
	eor     $input_l0, $input_l0, $rkN_l                     // AES final block - round N low
	eor     $input_h0, $input_h0, $rkN_h                     // AES final block - round N high
	fmov    $res1d, $input_l0                                // AES final block - mov low
	fmov    $res1.d[1], $input_h0                            // AES final block - mov high
	eor     $res1b, $res1b, $ctr3b                           // AES final block - result
.Lenc_blocks_1_remaining:                                        // blocks_left = 1
	rev64   $res0b, $res1b                                   // GHASH final block
	eor     $res0b, $res0b, $t0.16b                          // feed in partial tag
	pmull2  $rk2q1, $res0.2d, $h1.2d                         // GHASH final block - high
	mov     $t0d, $res0.d[1]                                 // GHASH final block - mid
	pmull   $rk3q1, $res0.1d, $h1.1d                         // GHASH final block - low
	eor     $acc_hb, $acc_hb, $rk2                           // GHASH final block - high
	eor     $t0.8b, $t0.8b, $res0.8b                         // GHASH final block - mid
	pmull   $t0.1q, $t0.1d, $h12k.1d                         // GHASH final block - mid
	eor     $acc_lb, $acc_lb, $rk3                           // GHASH final block - low
	eor     $acc_mb, $acc_mb, $t0.16b                        // GHASH final block - mid
	movi    $mod_constant.8b, #0xc2
	eor     $t9.16b, $acc_lb, $acc_hb                        // MODULO - karatsuba tidy up
	shl     $mod_constantd, $mod_constantd, #56              // mod_constant
	eor     $acc_mb, $acc_mb, $t9.16b                        // MODULO - karatsuba tidy up
	pmull   $mod_t.1q, $acc_h.1d, $mod_constant.1d           // MODULO - top 64b align with mid
	ext     $acc_hb, $acc_hb, $acc_hb, #8                    // MODULO - other top alignment
	eor     $acc_mb, $acc_mb, $mod_t.16b                     // MODULO - fold into mid
	eor     $acc_mb, $acc_mb, $acc_hb                        // MODULO - fold into mid
	pmull   $acc_h.1q, $acc_m.1d, $mod_constant.1d           // MODULO - mid 64b align with low
	ext     $acc_mb, $acc_mb, $acc_mb, #8                    // MODULO - other mid alignment
	eor     $acc_lb, $acc_lb, $acc_hb                        // MODULO - fold into low
	eor     $acc_lb, $acc_lb, $acc_mb                        // MODULO - fold into low
	ext     $acc_lb, $acc_lb, $acc_lb, #8
	rev64   $acc_lb, $acc_lb

	rev     $ctr32w, $rctr32w
	str     $ctr32w, [$counter, #12]                         // store the updated counter
	st1     { $res1b}, [$output_ptr]                         // store all 16B

	mov     x0, $len
	st1     { $acc_l.16b }, [$current_tag]
	ldp     x19, x20, [sp, #16]
	ldp     x21, x22, [sp, #32]
	ldp     x23, x24, [sp, #48]
	ldp     d8, d9, [sp, #64]
	ldp     d10, d11, [sp, #80]
	ldp     d12, d13, [sp, #96]
	ldp     d14, d15, [sp, #112]
	ldp     x29, x30, [sp], #128
	AARCH64_VALIDATE_LINK_REGISTER
	ret
.size aes_gcm_enc_kernel_deinterleaved,.-aes_gcm_enc_kernel_deinterleaved
___

{
my $t8="v4";
my $t8d="d4";
my $t9="v6";
my $t9d="d6";
################################################################################
# size_t aes_gcm_dec_kernel_deinterleaved(const uint8_t *in,
#                           size_t len_bits,
#                           uint8_t *out,
#                           u64 *Xi,
#                           uint8_t ivec[16],
#                           const void *key);
#
$code.=<<___;
.global aes_gcm_dec_kernel_deinterleaved
.type   aes_gcm_dec_kernel_deinterleaved,%function
.align  4
aes_gcm_dec_kernel_deinterleaved:
	AARCH64_SIGN_LINK_REGISTER
	stp	x29, x30, [sp, #-128]!
	mov	x29, sp
	stp     x19, x20, [sp, #16]
	mov     $counter, x4
	mov     $cc, x5
	stp     x21, x22, [sp, #32]
	stp     x23, x24, [sp, #48]
	stp     d8, d9, [sp, #64]
	stp     d10, d11, [sp, #80]
	stp     d12, d13, [sp, #96]
	stp     d14, d15, [sp, #112]
	ldr	$roundsw, [$cc, #240]
	add	$input_l1, $cc, $rounds, lsl #4                   // borrow input_l1 for last key
	ldp     $rkN_l, $rkN_h, [$input_l1]                       // load round N keys
	ldr     $rkNm1q, [$input_l1, #-16]                        // load round N-1 keys
	lsr     $main_end_input_ptr, $bit_length, #3              // byte_len
	mov     $len, $main_end_input_ptr
	ldp     $ctr96_b64x, $ctr96_t32x, [$counter]              // ctr96_b64, ctr96_t32
	ldr     $rk0q, [$cc, #0]                                  // load rk0
	ldr     $rk1q, [$cc, #16]                                 // load rk1
	ldr     $rk2q, [$cc, #32]                                 // load rk2
	ldr     $rk3q, [$cc, #48]                                 // load rk3
	ldr     $rk4q, [$cc, #64]                                 // load rk4
	ldr     $rk5q, [$cc, #80]                                 // load rk5
	ldr     $rk6q, [$cc, #96]                                 // load rk6
	ldr     $rk7q, [$cc, #112]                                // load rk7
	ldr     $rk8q, [$cc, #128]                                // load rk8
	ldr     $rk9q, [$cc, #144]                                // load rk9
	ldr     $rk10q, [$cc, #160]                               // load rk10
	ldr     $rk11q, [$cc, #176]                               // load rk11
	ldr     $rk12q, [$cc, #192]                               // load rk12
	sub     $main_end_input_ptr, $main_end_input_ptr, #1      // byte_len - 1
	and     $main_end_input_ptr, $main_end_input_ptr, #0xffffffffffffffc0 // number of bytes to be processed in main loop (at least 1 byte must be handled by tail)
	add     $end_input_ptr, $input_ptr, $bit_length, lsr #3   // end_input_ptr
	lsr     $rctr32x, $ctr96_t32x, #32
	orr     $ctr96_t32w, $ctr96_t32w, $ctr96_t32w
	add     $main_end_input_ptr, $main_end_input_ptr, $input_ptr
	rev     $rctr32w, $rctr32w                                // rev_ctr32
	add     $rctr32w, $rctr32w, #1                            // increment rev_ctr32
	fmov    $ctr3d, $ctr96_b64x                               // CTR block 3
	rev     $ctr32w, $rctr32w                                 // CTR block 1
	add     $rctr32w, $rctr32w, #1                            // CTR block 1
	fmov    $ctr1d, $ctr96_b64x                               // CTR block 1
	orr     $ctr32x, $ctr96_t32x, $ctr32x, lsl #32            // CTR block 1
	ld1     { $ctr0b}, [$counter]                             // special case vector load initial counter so we can start first AES block as quickly as possible
	fmov    $ctr1.d[1], $ctr32x                               // CTR block 1
	rev     $ctr32w, $rctr32w                                 // CTR block 2
	add     $rctr32w, $rctr32w, #1                            // CTR block 2
	fmov    $ctr2d, $ctr96_b64x                               // CTR block 2
	orr     $ctr32x, $ctr96_t32x, $ctr32x, lsl #32            // CTR block 2
	fmov    $ctr2.d[1], $ctr32x                               // CTR block 2
	rev     $ctr32w, $rctr32w                                 // CTR block 3
	orr     $ctr32x, $ctr96_t32x, $ctr32x, lsl #32            // CTR block 3
	fmov    $ctr3.d[1], $ctr32x                               // CTR block 3
	add     $rctr32w, $rctr32w, #1                            // CTR block 3

	aese    $ctr0b, $rk0  \n  aesmc   $ctr0b, $ctr0b          // AES block 0 - round 0
	aese    $ctr0b, $rk1  \n  aesmc   $ctr0b, $ctr0b          // AES block 0 - round 1
	aese    $ctr0b, $rk2  \n  aesmc   $ctr0b, $ctr0b          // AES block 0 - round 2
	aese    $ctr0b, $rk3  \n  aesmc   $ctr0b, $ctr0b          // AES block 0 - round 3
	aese    $ctr0b, $rk4  \n  aesmc   $ctr0b, $ctr0b          // AES block 0 - round 4
	aese    $ctr0b, $rk5  \n  aesmc   $ctr0b, $ctr0b          // AES block 0 - round 5
	aese    $ctr0b, $rk6  \n  aesmc   $ctr0b, $ctr0b          // AES block 0 - round 6
	aese    $ctr0b, $rk7  \n  aesmc   $ctr0b, $ctr0b          // AES block 0 - round 7
	aese    $ctr0b, $rk8  \n  aesmc   $ctr0b, $ctr0b          // AES block 0 - round 8

	aese    $ctr1b, $rk0  \n  aesmc   $ctr1b, $ctr1b          // AES block 1 - round 0
	aese    $ctr1b, $rk1  \n  aesmc   $ctr1b, $ctr1b          // AES block 1 - round 1
	aese    $ctr1b, $rk2  \n  aesmc   $ctr1b, $ctr1b          // AES block 1 - round 2
	aese    $ctr1b, $rk3  \n  aesmc   $ctr1b, $ctr1b          // AES block 1 - round 3
	aese    $ctr1b, $rk4  \n  aesmc   $ctr1b, $ctr1b          // AES block 1 - round 4
	aese    $ctr1b, $rk5  \n  aesmc   $ctr1b, $ctr1b          // AES block 1 - round 5
	aese    $ctr1b, $rk6  \n  aesmc   $ctr1b, $ctr1b          // AES block 1 - round 6
	aese    $ctr1b, $rk7  \n  aesmc   $ctr1b, $ctr1b          // AES block 1 - round 7
	aese    $ctr1b, $rk8  \n  aesmc   $ctr1b, $ctr1b          // AES block 1 - round 8

	aese    $ctr2b, $rk0  \n  aesmc   $ctr2b, $ctr2b          // AES block 2 - round 0
	aese    $ctr2b, $rk1  \n  aesmc   $ctr2b, $ctr2b          // AES block 2 - round 1
	aese    $ctr2b, $rk2  \n  aesmc   $ctr2b, $ctr2b          // AES block 2 - round 2
	aese    $ctr2b, $rk3  \n  aesmc   $ctr2b, $ctr2b          // AES block 2 - round 3
	aese    $ctr2b, $rk4  \n  aesmc   $ctr2b, $ctr2b          // AES block 2 - round 4
	aese    $ctr2b, $rk5  \n  aesmc   $ctr2b, $ctr2b          // AES block 2 - round 5
	aese    $ctr2b, $rk6  \n  aesmc   $ctr2b, $ctr2b          // AES block 2 - round 6
	aese    $ctr2b, $rk7  \n  aesmc   $ctr2b, $ctr2b          // AES block 2 - round 7
	aese    $ctr2b, $rk8  \n  aesmc   $ctr2b, $ctr2b          // AES block 2 - round 8

	aese    $ctr3b, $rk0  \n  aesmc   $ctr3b, $ctr3b          // AES block 3 - round 0
	aese    $ctr3b, $rk1  \n  aesmc   $ctr3b, $ctr3b          // AES block 3 - round 1
	aese    $ctr3b, $rk2  \n  aesmc   $ctr3b, $ctr3b          // AES block 3 - round 2
	aese    $ctr3b, $rk3  \n  aesmc   $ctr3b, $ctr3b          // AES block 3 - round 3
	aese    $ctr3b, $rk4  \n  aesmc   $ctr3b, $ctr3b          // AES block 3 - round 4
	aese    $ctr3b, $rk5  \n  aesmc   $ctr3b, $ctr3b          // AES block 3 - round 5
	aese    $ctr3b, $rk6  \n  aesmc   $ctr3b, $ctr3b          // AES block 3 - round 6
	aese    $ctr3b, $rk7  \n  aesmc   $ctr3b, $ctr3b          // AES block 3 - round 7
	aese    $ctr3b, $rk8  \n  aesmc   $ctr3b, $ctr3b          // AES block 3 - round 8

	cmp     $rounds, #12                                      // setup flags for AES-128/192/256 check
	b.lt	.Ldec_finish_first_blocks                         // branch if AES-128

	aese    $ctr0b, $rk9  \n  aesmc   $ctr0b, $ctr0b          // AES block 0 - round 9
	aese    $ctr0b, $rk10 \n  aesmc   $ctr0b, $ctr0b          // AES block 0 - round 10
	aese    $ctr1b, $rk9  \n  aesmc   $ctr1b, $ctr1b          // AES block 1 - round 9
	aese    $ctr1b, $rk10 \n  aesmc   $ctr1b, $ctr1b          // AES block 1 - round 10
	aese    $ctr2b, $rk9  \n  aesmc   $ctr2b, $ctr2b          // AES block 2 - round 9
	aese    $ctr2b, $rk10 \n  aesmc   $ctr2b, $ctr2b          // AES block 2 - round 10
	aese    $ctr3b, $rk9  \n  aesmc   $ctr3b, $ctr3b          // AES block 3 - round 9
	aese    $ctr3b, $rk10 \n  aesmc   $ctr3b, $ctr3b          // AES block 3 - round 10
	b.eq	.Ldec_finish_first_blocks                         // branch if AES-192

	aese    $ctr0b, $rk11 \n  aesmc   $ctr0b, $ctr0b          // AES block 0 - round 11
	aese    $ctr0b, $rk12 \n  aesmc   $ctr0b, $ctr0b          // AES block 0 - round 12
	aese    $ctr1b, $rk11 \n  aesmc   $ctr1b, $ctr1b          // AES block 1 - round 11
	aese    $ctr1b, $rk12 \n  aesmc   $ctr1b, $ctr1b          // AES block 1 - round 12
	aese    $ctr2b, $rk11 \n  aesmc   $ctr2b, $ctr2b          // AES block 2 - round 11
	aese    $ctr2b, $rk12 \n  aesmc   $ctr2b, $ctr2b          // AES block 2 - round 12
	aese    $ctr3b, $rk11 \n  aesmc   $ctr3b, $ctr3b          // AES block 3 - round 11
	aese    $ctr3b, $rk12 \n  aesmc   $ctr3b, $ctr3b          // AES block 3 - round 12

.Ldec_finish_first_blocks:

	aese    $ctr1b, $rkNm1                                    // AES block 1 - round N-1
	aese    $ctr2b, $rkNm1                                    // AES block 2 - round N-1
	aese    $ctr3b, $rkNm1                                    // AES block 3 - round N-1
	aese    $ctr0b, $rkNm1                                    // AES block 0 - round N-1

	ldr     $h1q, [$Htable]                                   // load h1l | h1h
	ext     $h1b, $h1b, $h1b, #8
	ldr     $h2q, [$Htable, #32]                              // load h2l | h2h
	ext     $h2b, $h2b, $h2b, #8
	ldr     $h3q, [$Htable, #48]                              // load h3l | h3h
	ext     $h3b, $h3b, $h3b, #8
	ldr     $h4q, [$Htable, #80]                              // load h4l | h4h
	ext     $h4b, $h4b, $h4b, #8

	trn1    $acc_h.2d, $h3.2d,    $h4.2d                      // h4h | h3h
	trn2    $h34k.2d,  $h3.2d,    $h4.2d                      // h4l | h3l
	trn1    $t0.2d,    $h1.2d,    $h2.2d                      // h2h | h1h
	trn2    $h12k.2d,  $h1.2d,    $h2.2d                      // h2l | h1l
	eor     $h34k.16b, $h34k.16b, $acc_h.16b                  // h4k | h3k
	eor     $h12k.16b, $h12k.16b, $t0.16b                     // h2k | h1k

	ld1     { $acc_lb}, [$current_tag]
	ext     $acc_lb, $acc_lb, $acc_lb, #8
	rev64   $acc_lb, $acc_lb

	cmp     $input_ptr, $main_end_input_ptr                   // check if we have <= 4 blocks
	b.ge    .Ldec_tail                                        // handle tail

	ldr     $res0q, [$input_ptr, #0]                          // AES block 0 - load ciphertext
	eor     $ctr0b, $res0b, $ctr0b                            // AES block 0 - result
	mov     $output_h0, $ctr0.d[1]                            // AES block 0 - mov high
	mov     $output_l0, $ctr0.d[0]                            // AES block 0 - mov low
	eor     $output_h0, $output_h0, $rkN_h                    // AES block 0 - round N high
	eor     $output_l0, $output_l0, $rkN_l                    // AES block 0 - round N low
	stp     $output_l0, $output_h0, [$output_ptr], #16        // AES block 0 - store result

	ldr     $res1q, [$input_ptr, #16]                         // AES block 1 - load ciphertext
	eor     $ctr1b, $res1b, $ctr1b                            // AES block 1 - result
	mov     $output_l1, $ctr1.d[0]                            // AES block 1 - mov low
	mov     $output_h1, $ctr1.d[1]                            // AES block 1 - mov high
	eor     $output_l1, $output_l1, $rkN_l                    // AES block 1 - round N low
	eor     $output_h1, $output_h1, $rkN_h                    // AES block 1 - round N high
	stp     $output_l1, $output_h1, [$output_ptr], #16        // AES block 1 - store result
	ldr     $res2q, [$input_ptr, #32]                         // AES block 2 - load ciphertext
	eor     $ctr2b, $res2b, $ctr2b                            // AES block 2 - result
	ldr     $res3q, [$input_ptr, #48]                         // AES block 3 - load ciphertext

	add     $input_ptr, $input_ptr, #64                       // AES input_ptr update

	rev64   $res0b, $res0b                                    // GHASH block 0
	rev64   $res1b, $res1b                                    // GHASH block 1

	rev     $ctr32w, $rctr32w                                 // CTR block 4
	add     $rctr32w, $rctr32w, #1                            // CTR block 4
	fmov    $ctr0d, $ctr96_b64x                               // CTR block 4
	orr     $ctr32x, $ctr96_t32x, $ctr32x, lsl #32            // CTR block 4
	fmov    $ctr0.d[1], $ctr32x                               // CTR block 4
	rev     $ctr32w, $rctr32w                                 // CTR block 5
	add     $rctr32w, $rctr32w, #1                            // CTR block 5
	orr     $ctr32x, $ctr96_t32x, $ctr32x, lsl #32            // CTR block 5
	fmov    $ctr1d, $ctr96_b64x                               // CTR block 5
	fmov    $ctr1.d[1], $ctr32x                               // CTR block 5
	rev     $ctr32w, $rctr32w                                 // CTR block 6
	add     $rctr32w, $rctr32w, #1                            // CTR block 6
	orr     $ctr32x, $ctr96_t32x, $ctr32x, lsl #32            // CTR block 6

	cmp     $input_ptr, $main_end_input_ptr                   // check if we have <= 8 blocks
	b.ge    .Ldec_prepretail                                  // do prepretail

.Ldec_main_loop:                                                  // main loop start
	mov     $output_l2, $ctr2.d[0]                            // AES block 4k+2 - mov low
	mov     $output_h2, $ctr2.d[1]                            // AES block 4k+2 - mov high
	eor     $output_h2, $output_h2, $rkN_h                    // AES block 4k+2 - round N high
	eor     $output_l2, $output_l2, $rkN_l                    // AES block 4k+2 - round N low
	stp     $output_l2, $output_h2, [$output_ptr], #16        // AES block 4k+2 - store result
	eor     $ctr3b, $res3b, $ctr3b                            // AES block 4k+3 - result
	mov     $output_h3, $ctr3.d[1]                            // AES block 4k+3 - mov high
	mov     $output_l3, $ctr3.d[0]                            // AES block 4k+3 - mov low

	ext     $acc_lb, $acc_lb, $acc_lb, #8                     // PRE 0
	eor     $res0b, $res0b, $acc_lb                           // PRE 1
	pmull2  $acc_h.1q, $res0.2d, $h4.2d                       // GHASH block 4k - high
	mov     $t0d, $res0.d[1]                                  // GHASH block 4k - mid
	eor     $t0.8b, $t0.8b, $res0.8b                          // GHASH block 4k - mid
	mov     $acc_md, $h34k.d[1]                               // GHASH block 4k - mid
	rev64   $res2b, $res2b                                    // GHASH block 4k+2
	pmull   $acc_l.1q, $res0.1d, $h4.1d                       // GHASH block 4k - low
	pmull2  $t1.1q, $res1.2d, $h3.2d                          // GHASH block 4k+1 - high
	rev64   $res3b, $res3b                                    // GHASH block 4k+3
	pmull   $acc_m.1q, $t0.1d, $acc_m.1d                      // GHASH block 4k - mid
	pmull   $t2.1q, $res1.1d, $h3.1d                          // GHASH block 4k+1 - low
	eor     $acc_hb, $acc_hb, $t1.16b                         // GHASH block 4k+1 - high
	mov     $t3d, $res1.d[1]                                  // GHASH block 4k+1 - mid
	eor     $acc_lb, $acc_lb, $t2.16b                         // GHASH block 4k+1 - low
	mov     $t6d, $res2.d[1]                                  // GHASH block 4k+2 - mid
	eor     $t3.8b, $t3.8b, $res1.8b                          // GHASH block 4k+1 - mid
	pmull   $t5.1q, $res2.1d, $h2.1d                          // GHASH block 4k+2 - low
	eor     $t6.8b, $t6.8b, $res2.8b                          // GHASH block 4k+2 - mid
	eor     $acc_lb, $acc_lb, $t5.16b                         // GHASH block 4k+2 - low
	pmull   $t3.1q, $t3.1d, $h34k.1d                          // GHASH block 4k+1 - mid
	ins     $t6.d[1], $t6.d[0]                                // GHASH block 4k+2 - mid
	eor     $acc_mb, $acc_mb, $t3.16b                         // GHASH block 4k+1 - mid
	pmull2  $t4.1q, $res2.2d, $h2.2d                          // GHASH block 4k+2 - high
	mov     $t9d, $res3.d[1]                                  // GHASH block 4k+3 - mid
	pmull2  $t6.1q, $t6.2d, $h12k.2d                          // GHASH block 4k+2 - mid
	eor     $acc_hb, $acc_hb, $t4.16b                         // GHASH block 4k+2 - high
	pmull   $t8.1q, $res3.1d, $h1.1d                          // GHASH block 4k+3 - low
	eor     $acc_mb, $acc_mb, $t6.16b                         // GHASH block 4k+2 - mid
	pmull2  $t7.1q, $res3.2d, $h1.2d                          // GHASH block 4k+3 - high
	eor     $t9.8b, $t9.8b, $res3.8b                          // GHASH block 4k+3 - mid
	eor     $acc_hb, $acc_hb, $t7.16b                         // GHASH block 4k+3 - high
	pmull   $t9.1q, $t9.1d, $h12k.1d                          // GHASH block 4k+3 - mid
	movi    $mod_constant.8b, #0xc2
	eor     $acc_lb, $acc_lb, $t8.16b                         // GHASH block 4k+3 - low
	shl     $mod_constantd, $mod_constantd, #56               // mod_constant
	eor     $acc_mb, $acc_mb, $t9.16b                         // GHASH block 4k+3 - mid
	pmull   $mod_t.1q, $acc_h.1d, $mod_constant.1d            // MODULO - top 64b align with mid
	eor     $t9.16b, $acc_lb, $acc_hb                         // MODULO - karatsuba tidy up
	ext     $acc_hb, $acc_hb, $acc_hb, #8                     // MODULO - other top alignment
	eor     $acc_mb, $acc_mb, $t9.16b                         // MODULO - karatsuba tidy up
	eor     $acc_mb, $acc_mb, $mod_t.16b                      // MODULO - fold into mid
	eor     $acc_mb, $acc_mb, $acc_hb                         // MODULO - fold into mid
	pmull   $mod_constant.1q, $acc_m.1d, $mod_constant.1d     // MODULO - mid 64b align with low
	eor     $acc_lb, $acc_lb, $mod_constant.16b               // MODULO - fold into low
	ext     $acc_mb, $acc_mb, $acc_mb, #8                     // MODULO - other mid alignment
	eor     $acc_lb, $acc_lb, $acc_mb                         // MODULO - fold into low

	fmov    $ctr2d, $ctr96_b64x                               // CTR block 4k+6
	fmov    $ctr2.d[1], $ctr32x                               // CTR block 4k+6
	rev     $ctr32w, $rctr32w                                 // CTR block 4k+7
	fmov    $ctr3d, $ctr96_b64x                               // CTR block 4k+7
	orr     $ctr32x, $ctr96_t32x, $ctr32x, lsl #32            // CTR block 4k+7
	fmov    $ctr3.d[1], $ctr32x                               // CTR block 4k+7
	add     $rctr32w, $rctr32w, #1                            // CTR block 4k+7

	eor     $output_l3, $output_l3, $rkN_l                    // AES block 4k+3 - round N low
	eor     $output_h3, $output_h3, $rkN_h                    // AES block 4k+3 - round N high

	aese    $ctr0b, $rk0  \n  aesmc   $ctr0b, $ctr0b          // AES block 4k+4 - round 0
	aese    $ctr0b, $rk1  \n  aesmc   $ctr0b, $ctr0b          // AES block 4k+4 - round 1
	aese    $ctr0b, $rk2  \n  aesmc   $ctr0b, $ctr0b          // AES block 4k+4 - round 2
	aese    $ctr0b, $rk3  \n  aesmc   $ctr0b, $ctr0b          // AES block 4k+4 - round 3
	aese    $ctr0b, $rk4  \n  aesmc   $ctr0b, $ctr0b          // AES block 4k+4 - round 4
	aese    $ctr0b, $rk5  \n  aesmc   $ctr0b, $ctr0b          // AES block 4k+4 - round 5
	aese    $ctr0b, $rk6  \n  aesmc   $ctr0b, $ctr0b          // AES block 4k+4 - round 6
	aese    $ctr0b, $rk7  \n  aesmc   $ctr0b, $ctr0b          // AES block 4k+4 - round 7

	aese    $ctr0b, $rk8  \n  aesmc   $ctr0b, $ctr0b          // AES block 4k+4 - round 8
	aese    $ctr1b, $rk0  \n  aesmc   $ctr1b, $ctr1b          // AES block 4k+5 - round 0
	aese    $ctr1b, $rk1  \n  aesmc   $ctr1b, $ctr1b          // AES block 4k+5 - round 1
	aese    $ctr1b, $rk2  \n  aesmc   $ctr1b, $ctr1b          // AES block 4k+5 - round 2
	aese    $ctr1b, $rk3  \n  aesmc   $ctr1b, $ctr1b          // AES block 4k+5 - round 3
	aese    $ctr1b, $rk4  \n  aesmc   $ctr1b, $ctr1b          // AES block 4k+5 - round 4
	aese    $ctr1b, $rk5  \n  aesmc   $ctr1b, $ctr1b          // AES block 4k+5 - round 5
	aese    $ctr1b, $rk6  \n  aesmc   $ctr1b, $ctr1b          // AES block 4k+5 - round 6
	aese    $ctr1b, $rk7  \n  aesmc   $ctr1b, $ctr1b          // AES block 4k+5 - round 7
	aese    $ctr1b, $rk8  \n  aesmc   $ctr1b, $ctr1b          // AES block 4k+5 - round 8

	aese    $ctr2b, $rk0  \n  aesmc   $ctr2b, $ctr2b          // AES block 4k+6 - round 0
	aese    $ctr2b, $rk1  \n  aesmc   $ctr2b, $ctr2b          // AES block 4k+6 - round 1
	aese    $ctr2b, $rk2  \n  aesmc   $ctr2b, $ctr2b          // AES block 4k+6 - round 2
	aese    $ctr2b, $rk3  \n  aesmc   $ctr2b, $ctr2b          // AES block 4k+6 - round 3
	aese    $ctr2b, $rk4  \n  aesmc   $ctr2b, $ctr2b          // AES block 4k+6 - round 4
	aese    $ctr2b, $rk5  \n  aesmc   $ctr2b, $ctr2b          // AES block 4k+6 - round 5
	aese    $ctr2b, $rk6  \n  aesmc   $ctr2b, $ctr2b          // AES block 4k+6 - round 6
	aese    $ctr2b, $rk7  \n  aesmc   $ctr2b, $ctr2b          // AES block 4k+6 - round 7
	aese    $ctr2b, $rk8  \n  aesmc   $ctr2b, $ctr2b          // AES block 4k+6 - round 8

	aese    $ctr3b, $rk0  \n  aesmc   $ctr3b, $ctr3b          // AES block 4k+7 - round 0
	aese    $ctr3b, $rk1  \n  aesmc   $ctr3b, $ctr3b          // AES block 4k+7 - round 1
	aese    $ctr3b, $rk2  \n  aesmc   $ctr3b, $ctr3b          // AES block 4k+7 - round 2
	aese    $ctr3b, $rk3  \n  aesmc   $ctr3b, $ctr3b          // AES block 4k+7 - round 3
	aese    $ctr3b, $rk4  \n  aesmc   $ctr3b, $ctr3b          // AES block 4k+7 - round 4
	aese    $ctr3b, $rk5  \n  aesmc   $ctr3b, $ctr3b          // AES block 4k+7 - round 5
	aese    $ctr3b, $rk6  \n  aesmc   $ctr3b, $ctr3b          // AES block 4k+7 - round 6
	aese    $ctr3b, $rk7  \n  aesmc   $ctr3b, $ctr3b          // AES block 4k+7 - round 7
	aese    $ctr3b, $rk8  \n  aesmc   $ctr3b, $ctr3b          // AES block 4k+7 - round 8

	cmp     $rounds, #12                                      // setup flags for AES-128/192/256 check
	b.lt	.Ldec_main_loop_continue                          // branch if AES-128

	aese    $ctr0b, $rk9  \n  aesmc   $ctr0b, $ctr0b          // AES block 4k+4 - round 9
	aese    $ctr0b, $rk10 \n  aesmc   $ctr0b, $ctr0b          // AES block 4k+4 - round 10
	aese    $ctr1b, $rk9  \n  aesmc   $ctr1b, $ctr1b          // AES block 4k+5 - round 9
	aese    $ctr1b, $rk10 \n  aesmc   $ctr1b, $ctr1b          // AES block 4k+5 - round 10
	aese    $ctr2b, $rk9  \n  aesmc   $ctr2b, $ctr2b          // AES block 4k+6 - round 9
	aese    $ctr2b, $rk10 \n  aesmc   $ctr2b, $ctr2b          // AES block 4k+6 - round 10
	aese    $ctr3b, $rk9  \n  aesmc   $ctr3b, $ctr3b          // AES block 4k+7 - round 9
	aese    $ctr3b, $rk10 \n  aesmc   $ctr3b, $ctr3b          // AES block 4k+7 - round 10
	b.eq	.Ldec_main_loop_continue                          // branch if AES-192

	aese    $ctr0b, $rk11 \n  aesmc   $ctr0b, $ctr0b          // AES block 4k+4 - round 11
	aese    $ctr0b, $rk12 \n  aesmc   $ctr0b, $ctr0b          // AES block 4k+4 - round 12
	aese    $ctr1b, $rk11 \n  aesmc   $ctr1b, $ctr1b          // AES block 4k+5 - round 11
	aese    $ctr1b, $rk12 \n  aesmc   $ctr1b, $ctr1b          // AES block 4k+5 - round 12
	aese    $ctr2b, $rk11 \n  aesmc   $ctr2b, $ctr2b          // AES block 4k+6 - round 11
	aese    $ctr2b, $rk12 \n  aesmc   $ctr2b, $ctr2b          // AES block 4k+6 - round 12
	aese    $ctr3b, $rk11 \n  aesmc   $ctr3b, $ctr3b          // AES block 4k+7 - round 11
	aese    $ctr3b, $rk12 \n  aesmc   $ctr3b, $ctr3b          // AES block 4k+7 - round 12

.Ldec_main_loop_continue:

	stp     $output_l3, $output_h3, [$output_ptr], #16        // AES block 4k+3 - store result

	ldr     $res0q, [$input_ptr, #0]                          // AES block 4k+4 - load ciphertext
	aese    $ctr0b, $rkNm1                                    // AES block 4k+4 - round N-1
	eor     $ctr0b, $res0b, $ctr0b                            // AES block 4k+4 - result
        mov     $output_h0, $ctr0.d[1]                            // AES block 4k+4 - mov high
	mov     $output_l0, $ctr0.d[0]                            // AES block 4k+4 - mov low
	eor     $output_l0, $output_l0, $rkN_l                    // AES block 4k+4 - round N low
	eor     $output_h0, $output_h0, $rkN_h                    // AES block 4k+4 - round N high
	stp     $output_l0, $output_h0, [$output_ptr], #16        // AES block 4k+4 - store result

	ldr     $res1q, [$input_ptr, #16]                         // AES block 4k+5 - load ciphertext
	aese    $ctr1b, $rkNm1                                    // AES block 4k+5 - round N-1
	eor     $ctr1b, $res1b, $ctr1b                            // AES block 4k+5 - result
	mov     $output_h1, $ctr1.d[1]                            // AES block 4k+5 - mov high
	mov     $output_l1, $ctr1.d[0]                            // AES block 4k+5 - mov low
	eor     $output_h1, $output_h1, $rkN_h                    // AES block 4k+5 - round N high
	eor     $output_l1, $output_l1, $rkN_l                    // AES block 4k+5 - round N low
	stp     $output_l1, $output_h1, [$output_ptr], #16        // AES block 4k+5 - store result

	ldr     $res2q, [$input_ptr, #32]                         // AES block 4k+6 - load ciphertext
	aese    $ctr2b, $rkNm1                                    // AES block 4k+6 - round N-1
	eor     $ctr2b, $res2b, $ctr2b                            // AES block 4k+6 - result

	ldr     $res3q, [$input_ptr, #48]                         // AES block 4k+7 - load ciphertext
	aese    $ctr3b, $rkNm1                                    // AES block 4k+7 - round N-1

	add     $input_ptr, $input_ptr, #64                       // AES input_ptr update

	rev64   $res1b, $res1b                                    // GHASH block 4k+5
	rev64   $res0b, $res0b                                    // GHASH block 4k+4

	rev     $ctr32w, $rctr32w                                 // CTR block 4k+8
	add     $rctr32w, $rctr32w, #1                            // CTR block 4k+8
	orr     $ctr32x, $ctr96_t32x, $ctr32x, lsl #32            // CTR block 4k+8
	fmov    $ctr0d, $ctr96_b64x                               // CTR block 4k+8
	fmov    $ctr0.d[1], $ctr32x                               // CTR block 4k+8
	rev     $ctr32w, $rctr32w                                 // CTR block 4k+9
	orr     $ctr32x, $ctr96_t32x, $ctr32x, lsl #32            // CTR block 4k+9
	add     $rctr32w, $rctr32w, #1                            // CTR block 4k+9
	fmov    $ctr1d, $ctr96_b64x                               // CTR block 4k+9
	fmov    $ctr1.d[1], $ctr32x                               // CTR block 4k+9
	rev     $ctr32w, $rctr32w                                 // CTR block 4k+10
	add     $rctr32w, $rctr32w, #1                            // CTR block 4k+10
	orr     $ctr32x, $ctr96_t32x, $ctr32x, lsl #32            // CTR block 4k+10

	cmp     $input_ptr, $main_end_input_ptr                   // LOOP CONTROL
	b.lt    .Ldec_main_loop

.Ldec_prepretail:                                                 // PREPRETAIL

	mov     $output_l2, $ctr2.d[0]                            // AES block 4k+2 - mov low
	mov     $output_h2, $ctr2.d[1]                            // AES block 4k+2 - mov high
	eor     $output_h2, $output_h2, $rkN_h                    // AES block 4k+2 - round N high
	eor     $output_l2, $output_l2, $rkN_l                    // AES block 4k+2 - round N low
	stp     $output_l2, $output_h2, [$output_ptr], #16        // AES block 4k+2 - store result
	eor     $ctr3b, $res3b, $ctr3b                            // AES block 4k+3 - result
	mov     $output_l3, $ctr3.d[0]                            // AES block 4k+3 - mov low
	mov     $output_h3, $ctr3.d[1]                            // AES block 4k+3 - mov high
	eor     $output_l3, $output_l3, $rkN_l                    // AES block 4k+3 - round N low
	eor     $output_h3, $output_h3, $rkN_h                    // AES block 4k+3 - round N high
	stp     $output_l3, $output_h3, [$output_ptr], #16        // AES block 4k+3 - store result

	ext     $acc_lb, $acc_lb, $acc_lb, #8                     // PRE 0
	eor     $res0b, $res0b, $acc_lb                           // PRE 1
	rev64   $res2b, $res2b                                    // GHASH block 4k+2
	pmull   $acc_l.1q, $res0.1d, $h4.1d                       // GHASH block 4k - low
	mov     $t0d, $res0.d[1]                                  // GHASH block 4k - mid
	pmull2  $acc_h.1q, $res0.2d, $h4.2d                       // GHASH block 4k - high
	mov     $acc_md, $h34k.d[1]                               // GHASH block 4k - mid
	eor     $t0.8b, $t0.8b, $res0.8b                          // GHASH block 4k - mid
	pmull2  $t1.1q, $res1.2d, $h3.2d                          // GHASH block 4k+1 - high
	rev64   $res3b, $res3b                                    // GHASH block 4k+3
	pmull   $acc_m.1q, $t0.1d, $acc_m.1d                      // GHASH block 4k - mid
	eor     $acc_hb, $acc_hb, $t1.16b                         // GHASH block 4k+1 - high
	pmull   $t2.1q, $res1.1d, $h3.1d                          // GHASH block 4k+1 - low
	mov     $t3d, $res1.d[1]                                  // GHASH block 4k+1 - mid
	eor     $acc_lb, $acc_lb, $t2.16b                         // GHASH block 4k+1 - low
	mov     $t6d, $res2.d[1]                                  // GHASH block 4k+2 - mid
	eor     $t3.8b, $t3.8b, $res1.8b                          // GHASH block 4k+1 - mid
	pmull   $t5.1q, $res2.1d, $h2.1d                          // GHASH block 4k+2 - low
	eor     $t6.8b, $t6.8b, $res2.8b                          // GHASH block 4k+2 - mid
	pmull   $t3.1q, $t3.1d, $h34k.1d                          // GHASH block 4k+1 - mid
	eor     $acc_lb, $acc_lb, $t5.16b                         // GHASH block 4k+2 - low
	pmull2  $t7.1q, $res3.2d, $h1.2d                          // GHASH block 4k+3 - high
	eor     $acc_mb, $acc_mb, $t3.16b                         // GHASH block 4k+1 - mid
	pmull2  $t4.1q, $res2.2d, $h2.2d                          // GHASH block 4k+2 - high
	ins     $t6.d[1], $t6.d[0]                                // GHASH block 4k+2 - mid
	eor     $acc_hb, $acc_hb, $t4.16b                         // GHASH block 4k+2 - high
	pmull   $t8.1q, $res3.1d, $h1.1d                          // GHASH block 4k+3 - low
	mov     $t9d, $res3.d[1]                                  // GHASH block 4k+3 - mid
	pmull2  $t6.1q, $t6.2d, $h12k.2d                          // GHASH block 4k+2 - mid
	eor     $t9.8b, $t9.8b, $res3.8b                          // GHASH block 4k+3 - mid
	eor     $acc_mb, $acc_mb, $t6.16b                         // GHASH block 4k+2 - mid
	eor     $acc_lb, $acc_lb, $t8.16b                         // GHASH block 4k+3 - low
	pmull   $t9.1q, $t9.1d, $h12k.1d                          // GHASH block 4k+3 - mid
	eor     $acc_hb, $acc_hb, $t7.16b                         // GHASH block 4k+3 - high
	eor     $acc_mb, $acc_mb, $t9.16b                         // GHASH block 4k+3 - mid
	eor     $t9.16b, $acc_lb, $acc_hb                         // MODULO - karatsuba tidy up
	movi    $mod_constant.8b, #0xc2
	shl     $mod_constantd, $mod_constantd, #56               // mod_constant
	eor     $acc_mb, $acc_mb, $t9.16b                         // MODULO - karatsuba tidy up
	pmull   $mod_t.1q, $acc_h.1d, $mod_constant.1d            // MODULO - top 64b align with mid
	ext     $acc_hb, $acc_hb, $acc_hb, #8                     // MODULO - other top alignment
	eor     $acc_mb, $acc_mb, $mod_t.16b                      // MODULO - fold into mid
	eor     $acc_mb, $acc_mb, $acc_hb                         // MODULO - fold into mid
	pmull   $mod_constant.1q, $acc_m.1d, $mod_constant.1d     // MODULO - mid 64b align with low
	ext     $acc_mb, $acc_mb, $acc_mb, #8                     // MODULO - other mid alignment
	eor     $acc_lb, $acc_lb, $mod_constant.16b               // MODULO - fold into low
	eor     $acc_lb, $acc_lb, $acc_mb                         // MODULO - fold into low

	fmov    $ctr2d, $ctr96_b64x                               // CTR block 4k+6
	fmov    $ctr2.d[1], $ctr32x                               // CTR block 4k+6
	rev     $ctr32w, $rctr32w                                 // CTR block 4k+7
	orr     $ctr32x, $ctr96_t32x, $ctr32x, lsl #32            // CTR block 4k+7
	fmov    $ctr3d, $ctr96_b64x                               // CTR block 4k+7
	fmov    $ctr3.d[1], $ctr32x                               // CTR block 4k+7
	add     $rctr32w, $rctr32w, #1                            // CTR block 4k+7

	aese    $ctr0b, $rk0  \n  aesmc   $ctr0b, $ctr0b          // AES block 4k+4 - round 0
	aese    $ctr0b, $rk1  \n  aesmc   $ctr0b, $ctr0b          // AES block 4k+4 - round 1
	aese    $ctr0b, $rk2  \n  aesmc   $ctr0b, $ctr0b          // AES block 4k+4 - round 2
	aese    $ctr0b, $rk3  \n  aesmc   $ctr0b, $ctr0b          // AES block 4k+4 - round 3
	aese    $ctr0b, $rk4  \n  aesmc   $ctr0b, $ctr0b          // AES block 4k+4 - round 4
	aese    $ctr0b, $rk5  \n  aesmc   $ctr0b, $ctr0b          // AES block 4k+4 - round 5
	aese    $ctr0b, $rk6  \n  aesmc   $ctr0b, $ctr0b          // AES block 4k+4 - round 6
	aese    $ctr0b, $rk7  \n  aesmc   $ctr0b, $ctr0b          // AES block 4k+4 - round 7
	aese    $ctr0b, $rk8  \n  aesmc   $ctr0b, $ctr0b          // AES block 4k+4 - round 8

	aese    $ctr1b, $rk0  \n  aesmc   $ctr1b, $ctr1b          // AES block 4k+5 - round 0
	aese    $ctr1b, $rk1  \n  aesmc   $ctr1b, $ctr1b          // AES block 4k+5 - round 1
	aese    $ctr1b, $rk2  \n  aesmc   $ctr1b, $ctr1b          // AES block 4k+5 - round 2
	aese    $ctr1b, $rk3  \n  aesmc   $ctr1b, $ctr1b          // AES block 4k+5 - round 3
	aese    $ctr1b, $rk4  \n  aesmc   $ctr1b, $ctr1b          // AES block 4k+5 - round 4
	aese    $ctr1b, $rk5  \n  aesmc   $ctr1b, $ctr1b          // AES block 4k+5 - round 5
	aese    $ctr1b, $rk6  \n  aesmc   $ctr1b, $ctr1b          // AES block 4k+5 - round 6
	aese    $ctr1b, $rk7  \n  aesmc   $ctr1b, $ctr1b          // AES block 4k+5 - round 7
	aese    $ctr1b, $rk8  \n  aesmc   $ctr1b, $ctr1b          // AES block 4k+5 - round 8

	aese    $ctr2b, $rk0  \n  aesmc   $ctr2b, $ctr2b          // AES block 4k+6 - round 0
	aese    $ctr2b, $rk1  \n  aesmc   $ctr2b, $ctr2b          // AES block 4k+6 - round 1
	aese    $ctr2b, $rk2  \n  aesmc   $ctr2b, $ctr2b          // AES block 4k+6 - round 2
	aese    $ctr2b, $rk3  \n  aesmc   $ctr2b, $ctr2b          // AES block 4k+6 - round 3
	aese    $ctr2b, $rk4  \n  aesmc   $ctr2b, $ctr2b          // AES block 4k+6 - round 4
	aese    $ctr2b, $rk5  \n  aesmc   $ctr2b, $ctr2b          // AES block 4k+6 - round 5
	aese    $ctr2b, $rk6  \n  aesmc   $ctr2b, $ctr2b          // AES block 4k+6 - round 6
	aese    $ctr2b, $rk7  \n  aesmc   $ctr2b, $ctr2b          // AES block 4k+6 - round 7
	aese    $ctr2b, $rk8  \n  aesmc   $ctr2b, $ctr2b          // AES block 4k+6 - round 8

	aese    $ctr3b, $rk0  \n  aesmc   $ctr3b, $ctr3b          // AES block 4k+7 - round 0
	aese    $ctr3b, $rk1  \n  aesmc   $ctr3b, $ctr3b          // AES block 4k+7 - round 1
	aese    $ctr3b, $rk2  \n  aesmc   $ctr3b, $ctr3b          // AES block 4k+7 - round 2
	aese    $ctr3b, $rk3  \n  aesmc   $ctr3b, $ctr3b          // AES block 4k+7 - round 3
	aese    $ctr3b, $rk4  \n  aesmc   $ctr3b, $ctr3b          // AES block 4k+7 - round 4
	aese    $ctr3b, $rk5  \n  aesmc   $ctr3b, $ctr3b          // AES block 4k+7 - round 5
	aese    $ctr3b, $rk6  \n  aesmc   $ctr3b, $ctr3b          // AES block 4k+7 - round 6
	aese    $ctr3b, $rk7  \n  aesmc   $ctr3b, $ctr3b          // AES block 4k+7 - round 7
	aese    $ctr3b, $rk8  \n  aesmc   $ctr3b, $ctr3b          // AES block 4k+7 - round 8

	cmp     $rounds, #12                                      // setup flags for AES-128/192/256 check
	b.lt	.Ldec_finish_prepretail                           // branch if AES-128

	aese    $ctr0b, $rk9  \n  aesmc   $ctr0b, $ctr0b          // AES block 4k+4 - round 9
	aese    $ctr0b, $rk10 \n  aesmc   $ctr0b, $ctr0b          // AES block 4k+4 - round 10
	aese    $ctr1b, $rk9  \n  aesmc   $ctr1b, $ctr1b          // AES block 4k+5 - round 9
	aese    $ctr1b, $rk10 \n  aesmc   $ctr1b, $ctr1b          // AES block 4k+5 - round 10
	aese    $ctr2b, $rk9  \n  aesmc   $ctr2b, $ctr2b          // AES block 4k+6 - round 9
	aese    $ctr2b, $rk10 \n  aesmc   $ctr2b, $ctr2b          // AES block 4k+6 - round 10
	aese    $ctr3b, $rk9  \n  aesmc   $ctr3b, $ctr3b          // AES block 4k+7 - round 9
	aese    $ctr3b, $rk10 \n  aesmc   $ctr3b, $ctr3b          // AES block 4k+7 - round 10
	b.eq	.Ldec_finish_prepretail                           // branch if AES-192

	aese    $ctr0b, $rk11 \n  aesmc   $ctr0b, $ctr0b          // AES block 4k+4 - round 11
	aese    $ctr0b, $rk12 \n  aesmc   $ctr0b, $ctr0b          // AES block 4k+4 - round 12
	aese    $ctr1b, $rk11 \n  aesmc   $ctr1b, $ctr1b          // AES block 4k+5 - round 11
	aese    $ctr1b, $rk12 \n  aesmc   $ctr1b, $ctr1b          // AES block 4k+5 - round 12
	aese    $ctr2b, $rk11 \n  aesmc   $ctr2b, $ctr2b          // AES block 4k+6 - round 11
	aese    $ctr2b, $rk12 \n  aesmc   $ctr2b, $ctr2b          // AES block 4k+6 - round 12
	aese    $ctr3b, $rk11 \n  aesmc   $ctr3b, $ctr3b          // AES block 4k+7 - round 11
	aese    $ctr3b, $rk12 \n  aesmc   $ctr3b, $ctr3b          // AES block 4k+7 - round 12

.Ldec_finish_prepretail:
	aese    $ctr1b, $rkNm1                                    // AES block 4k+5 - round N-1
	aese    $ctr0b, $rkNm1                                    // AES block 4k+4 - round N-1
	aese    $ctr3b, $rkNm1                                    // AES block 4k+7 - round N-1
	aese    $ctr2b, $rkNm1                                    // AES block 4k+6 - round N-1

.Ldec_tail:                                                       // TAIL
	sub     $main_end_input_ptr, $end_input_ptr, $input_ptr   // main_end_input_ptr is number of bytes left to process
	ld1     { $res1b}, [$input_ptr], #16                      // AES block 4k+4 - load ciphertext
	eor     $ctr0b, $res1b, $ctr0b                            // AES block 4k+4 - result
	mov     $output_l0, $ctr0.d[0]                            // AES block 4k+4 - mov low
	mov     $output_h0, $ctr0.d[1]                            // AES block 4k+4 - mov high
	ext     $t0.16b, $acc_lb, $acc_lb, #8                     // prepare final partial tag
	eor     $output_l0, $output_l0, $rkN_l                    // AES block 4k+4 - round N low
	eor     $output_h0, $output_h0, $rkN_h                    // AES block 4k+4 - round N high

	cmp     $main_end_input_ptr, #48
	b.gt    .Ldec_blocks_4_remaining
	sub     $rctr32w, $rctr32w, #1
	mov     $ctr3b, $ctr2b
	movi    $acc_m.8b, #0
	movi    $acc_l.8b, #0
	cmp     $main_end_input_ptr, #32
	movi    $acc_h.8b, #0
	mov     $ctr2b, $ctr1b
	b.gt    .Ldec_blocks_3_remaining
	sub     $rctr32w, $rctr32w, #1
	mov     $ctr3b, $ctr1b
	cmp     $main_end_input_ptr, #16
	b.gt    .Ldec_blocks_2_remaining
	sub     $rctr32w, $rctr32w, #1
	b       .Ldec_blocks_1_remaining
.Ldec_blocks_4_remaining:                                    // blocks left = 4
	stp     $output_l0, $output_h0, [$output_ptr], #16       // AES final-3 block  - store result
	rev64   $res0b, $res1b                                   // GHASH final-3 block
	mov     $acc_md, $h34k.d[1]                              // GHASH final-3 block - mid
	eor     $res0b, $res0b, $t0.16b                          // feed in partial tag
	mov     $rk4d, $res0.d[1]                                // GHASH final-3 block - mid
	eor     $rk4v.8b, $rk4v.8b, $res0.8b                     // GHASH final-3 block - mid
	movi    $t0.8b, #0                                       // suppress further partial tag feed in
	pmull2  $acc_h.1q, $res0.2d, $h4.2d                      // GHASH final-3 block - high
	pmull   $acc_m.1q, $rk4v.1d, $acc_m.1d                   // GHASH final-3 block - mid
	pmull   $acc_l.1q, $res0.1d, $h4.1d                      // GHASH final-3 block - low

	ld1     { $res1b}, [$input_ptr], #16                     // AES final-2 block - load ciphertext
	eor     $ctr0b, $res1b, $ctr1b                           // AES final-2 block - result
	mov     $output_l0, $ctr0.d[0]                           // AES final-2 block - mov low
	mov     $output_h0, $ctr0.d[1]                           // AES final-2 block - mov high
	eor     $output_l0, $output_l0, $rkN_l                   // AES final-2 block - round N low
	eor     $output_h0, $output_h0, $rkN_h                   // AES final-2 block - round N high
.Ldec_blocks_3_remaining:                                    // blocks left = 3
	stp     $output_l0, $output_h0, [$output_ptr], #16       // AES final-2 block  - store result
	rev64   $res0b, $res1b                                   // GHASH final-2 block
	eor     $res0b, $res0b, $t0.16b                          // feed in partial tag
	mov     $rk4d, $res0.d[1]                                // GHASH final-2 block - mid
	pmull   $rk3q1, $res0.1d, $h3.1d                         // GHASH final-2 block - low
	pmull2  $rk2q1, $res0.2d, $h3.2d                         // GHASH final-2 block - high
	eor     $rk4v.8b, $rk4v.8b, $res0.8b                     // GHASH final-2 block - mid
	eor     $acc_lb, $acc_lb, $rk3                           // GHASH final-2 block - low
	movi    $t0.8b, #0                                       // suppress further partial tag feed in
	pmull   $rk4v.1q, $rk4v.1d, $h34k.1d                     // GHASH final-2 block - mid
	eor     $acc_hb, $acc_hb, $rk2                           // GHASH final-2 block - high
	eor     $acc_mb, $acc_mb, $rk4v.16b                      // GHASH final-2 block - mid
	ld1     { $res1b}, [$input_ptr], #16                     // AES final-1 block - load ciphertext
	eor     $ctr0b, $res1b, $ctr2b                           // AES final-1 block - result
	mov     $output_l0, $ctr0.d[0]                           // AES final-1 block - mov low
	mov     $output_h0, $ctr0.d[1]                           // AES final-1 block - mov high
	eor     $output_l0, $output_l0, $rkN_l                   // AES final-1 block - round N low
	eor     $output_h0, $output_h0, $rkN_h                   // AES final-1 block - round N high
.Ldec_blocks_2_remaining:                                        // blocks left = 2
	stp     $output_l0, $output_h0, [$output_ptr], #16       // AES final-1 block  - store result
	rev64   $res0b, $res1b                                   // GHASH final-1 block
	eor     $res0b, $res0b, $t0.16b                          // feed in partial tag
	movi    $t0.8b, #0                                       // suppress further partial tag feed in
	mov     $rk4d, $res0.d[1]                                // GHASH final-1 block - mid
	pmull2  $rk2q1, $res0.2d, $h2.2d                         // GHASH final-1 block - high
	eor     $rk4v.8b, $rk4v.8b, $res0.8b                     // GHASH final-1 block - mid
	pmull   $rk3q1, $res0.1d, $h2.1d                         // GHASH final-1 block - low
	ins     $rk4v.d[1], $rk4v.d[0]                           // GHASH final-1 block - mid
	pmull2  $rk4v.1q, $rk4v.2d, $h12k.2d                     // GHASH final-1 block - mid
	eor     $acc_lb, $acc_lb, $rk3                           // GHASH final-1 block - low
	eor     $acc_hb, $acc_hb, $rk2                           // GHASH final-1 block - high
	eor     $acc_mb, $acc_mb, $rk4v.16b                      // GHASH final-1 block - mid
	ld1     { $res1b}, [$input_ptr], #16                     // AES final block - load ciphertext
	eor     $ctr0b, $res1b, $ctr3b                           // AES final block - result
	mov     $output_l0, $ctr0.d[0]                           // AES final block - mov low
	mov     $output_h0, $ctr0.d[1]                           // AES final block - mov high
	eor     $output_l0, $output_l0, $rkN_l                   // AES final block - round N low
	eor     $output_h0, $output_h0, $rkN_h                   // AES final block - round N high
.Ldec_blocks_1_remaining:                                        // blocks_left = 1
	rev     $ctr32w, $rctr32w
	rev64   $res0b, $res1b                                    // GHASH final block
	eor     $res0b, $res0b, $t0.16b                           // feed in partial tag
	pmull   $rk3q1, $res0.1d, $h1.1d                          // GHASH final block - low
	mov     $t0d, $res0.d[1]                                  // GHASH final block - mid
	eor     $t0.8b, $t0.8b, $res0.8b                          // GHASH final block - mid
	pmull2  $rk2q1, $res0.2d, $h1.2d                          // GHASH final block - high
	pmull   $t0.1q, $t0.1d, $h12k.1d                          // GHASH final block - mid
	eor     $acc_hb, $acc_hb, $rk2                            // GHASH final block - high
	eor     $acc_lb, $acc_lb, $rk3                            // GHASH final block - low
	eor     $acc_mb, $acc_mb, $t0.16b                         // GHASH final block - mid
	movi    $mod_constant.8b, #0xc2
	eor     $t9.16b, $acc_lb, $acc_hb                         // MODULO - karatsuba tidy up
	shl     $mod_constantd, $mod_constantd, #56               // mod_constant
	eor     $acc_mb, $acc_mb, $t9.16b                         // MODULO - karatsuba tidy up
	pmull   $mod_t.1q, $acc_h.1d, $mod_constant.1d            // MODULO - top 64b align with mid
	ext     $acc_hb, $acc_hb, $acc_hb, #8                     // MODULO - other top alignment
	eor     $acc_mb, $acc_mb, $mod_t.16b                      // MODULO - fold into mid
	eor     $acc_mb, $acc_mb, $acc_hb                         // MODULO - fold into mid
	pmull   $mod_constant.1q, $acc_m.1d, $mod_constant.1d     // MODULO - mid 64b align with low
	ext     $acc_mb, $acc_mb, $acc_mb, #8                     // MODULO - other mid alignment
	eor     $acc_lb, $acc_lb, $mod_constant.16b               // MODULO - fold into low
	stp     $output_l0, $output_h0, [$output_ptr]
	str     $ctr32w, [$counter, #12]                          // store the updated counter
	eor     $acc_lb, $acc_lb, $acc_mb                         // MODULO - fold into low
	ext     $acc_lb, $acc_lb, $acc_lb, #8
	rev64   $acc_lb, $acc_lb
	mov     x0, $len
	st1     { $acc_l.16b }, [$current_tag]
	ldp     x19, x20, [sp, #16]
	ldp     x21, x22, [sp, #32]
	ldp     x23, x24, [sp, #48]
	ldp     d8, d9, [sp, #64]
	ldp     d10, d11, [sp, #80]
	ldp     d12, d13, [sp, #96]
	ldp     d14, d15, [sp, #112]
	ldp     x29, x30, [sp], #128
	AARCH64_VALIDATE_LINK_REGISTER
	ret
.size aes_gcm_dec_kernel_deinterleaved,.-aes_gcm_dec_kernel_deinterleaved
___
}
}

$code.=<<___;
#endif
___

print $code;
close STDOUT or die "error closing STDOUT: $!"; # enforce flush
