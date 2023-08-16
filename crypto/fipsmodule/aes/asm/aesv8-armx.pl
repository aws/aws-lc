#! /usr/bin/env perl
# Copyright 2014-2016 The OpenSSL Project Authors. All Rights Reserved.
#
# Licensed under the OpenSSL license (the "License").  You may not use
# this file except in compliance with the License.  You can obtain a copy
# in the file LICENSE in the source distribution or at
# https://www.openssl.org/source/license.html

#
# ====================================================================
# Written by Andy Polyakov <appro@openssl.org> for the OpenSSL
# project. The module is, however, dual licensed under OpenSSL and
# CRYPTOGAMS licenses depending on where you obtain it. For further
# details see http://www.openssl.org/~appro/cryptogams/.
# ====================================================================
#
# This module implements support for ARMv8 AES instructions. The
# module is endian-agnostic in sense that it supports both big- and
# little-endian cases. As does it support both 32- and 64-bit modes
# of operation. Latter is achieved by limiting amount of utilized
# registers to 16, which implies additional NEON load and integer
# instructions. This has no effect on mighty Apple A7, where results
# are literally equal to the theoretical estimates based on AES
# instruction latencies and issue rates. On Cortex-A53, an in-order
# execution core, this costs up to 10-15%, which is partially
# compensated by implementing dedicated code path for 128-bit
# CBC encrypt case. On Cortex-A57 parallelizable mode performance
# seems to be limited by sheer amount of NEON instructions...
#
# Performance in cycles per byte processed with 128-bit key:
#
#		CBC enc		CBC dec		CTR
# Apple A7	2.39		1.20		1.20
# Cortex-A53	1.32		1.29		1.46
# Cortex-A57(*)	1.95		0.85		0.93
# Denver	1.96		0.86		0.80
# Mongoose	1.33		1.20		1.20
#
# (*)	original 3.64/1.34/1.32 results were for r0p0 revision
#	and are still same even for updated module;

if ($#ARGV < 1) { die "Not enough arguments provided.
  Two arguments are necessary: the flavour and the output file path."; }

$flavour = shift;
$output  = shift;

$0 =~ m/(.*[\/\\])[^\/\\]+$/; $dir=$1;
( $xlate="${dir}arm-xlate.pl" and -f $xlate ) or
( $xlate="${dir}../../../perlasm/arm-xlate.pl" and -f $xlate) or
die "can't locate arm-xlate.pl";

open OUT,"| \"$^X\" \"$xlate\" $flavour \"$output\"";
*STDOUT=*OUT;

$prefix="aes_hw";

$code=<<___;
#include <openssl/arm_arch.h>

#if __ARM_MAX_ARCH__>=7
.text
___
$code.=".arch	armv8-a+crypto\n"			if ($flavour =~ /64/);
$code.=<<___						if ($flavour !~ /64/);
.arch	armv7-a	// don't confuse not-so-latest binutils with argv8 :-)
.fpu	neon
.code	32
#undef	__thumb2__
___

# Assembler mnemonics are an eclectic mix of 32- and 64-bit syntax,
# NEON is mostly 32-bit mnemonics, integer - mostly 64. Goal is to
# maintain both 32- and 64-bit codes within single module and
# transliterate common code to either flavour with regex vodoo.
#
{{{
my ($inp,$bits,$out,$ptr,$rounds)=("x0","w1","x2","x3","w12");
my ($zero,$rcon,$mask,$in0,$in1,$tmp,$key)=
	$flavour=~/64/? map("q$_",(0..6)) : map("q$_",(0..3,8..10));


# On AArch64, put the data .rodata and use adrp + add for compatibility with
# execute-only memory. On AArch32, put it in .text and use adr.
$code.= ".section .rodata\n" if ($flavour =~ /64/);
$code.=<<___;
.align	5
.Lrcon:
.long	0x01,0x01,0x01,0x01
.long	0x0c0f0e0d,0x0c0f0e0d,0x0c0f0e0d,0x0c0f0e0d	// rotate-n-splat
.long	0x1b,0x1b,0x1b,0x1b

.text

.globl	${prefix}_set_encrypt_key
.type	${prefix}_set_encrypt_key,%function
.align	5
${prefix}_set_encrypt_key:
.Lenc_key:
___
$code.=<<___	if ($flavour =~ /64/);
#ifdef BORINGSSL_DISPATCH_TEST
.extern        BORINGSSL_function_hit
	adrp	x9,:pg_hi21:BORINGSSL_function_hit
	add     x9, x9, :lo12:BORINGSSL_function_hit
	mov     w10, #1
	strb    w10, [x9,#3] // kFlag_aes_hw_set_encrypt_key
#endif
	// Armv8.3-A PAuth: even though x30 is pushed to stack it is not popped later.
	AARCH64_VALID_CALL_TARGET
	stp	x29,x30,[sp,#-16]!
	add	x29,sp,#0
___
$code.=<<___;
	mov	$ptr,#-1
	cmp	$inp,#0
	b.eq	.Lenc_key_abort
	cmp	$out,#0
	b.eq	.Lenc_key_abort
	mov	$ptr,#-2
	cmp	$bits,#128
	b.lt	.Lenc_key_abort
	cmp	$bits,#256
	b.gt	.Lenc_key_abort
	tst	$bits,#0x3f
	b.ne	.Lenc_key_abort

___
$code.=<<___	if ($flavour =~ /64/);
	adrp	$ptr,:pg_hi21:.Lrcon
	add	$ptr,$ptr,:lo12:.Lrcon
___
$code.=<<___	if ($flavour !~ /64/);
	adr	$ptr,.Lrcon
___
$code.=<<___;
	cmp	$bits,#192

	veor	$zero,$zero,$zero
	vld1.8	{$in0},[$inp],#16
	mov	$bits,#8		// reuse $bits
	vld1.32	{$rcon,$mask},[$ptr],#32

	b.lt	.Loop128
	b.eq	.L192
	b	.L256

.align	4
.Loop128:
	vtbl.8	$key,{$in0},$mask
	vext.8	$tmp,$zero,$in0,#12
	vst1.32	{$in0},[$out],#16
	aese	$key,$zero
	subs	$bits,$bits,#1

	veor	$in0,$in0,$tmp
	vext.8	$tmp,$zero,$tmp,#12
	veor	$in0,$in0,$tmp
	vext.8	$tmp,$zero,$tmp,#12
	 veor	$key,$key,$rcon
	veor	$in0,$in0,$tmp
	vshl.u8	$rcon,$rcon,#1
	veor	$in0,$in0,$key
	b.ne	.Loop128

	vld1.32	{$rcon},[$ptr]

	vtbl.8	$key,{$in0},$mask
	vext.8	$tmp,$zero,$in0,#12
	vst1.32	{$in0},[$out],#16
	aese	$key,$zero

	veor	$in0,$in0,$tmp
	vext.8	$tmp,$zero,$tmp,#12
	veor	$in0,$in0,$tmp
	vext.8	$tmp,$zero,$tmp,#12
	 veor	$key,$key,$rcon
	veor	$in0,$in0,$tmp
	vshl.u8	$rcon,$rcon,#1
	veor	$in0,$in0,$key

	vtbl.8	$key,{$in0},$mask
	vext.8	$tmp,$zero,$in0,#12
	vst1.32	{$in0},[$out],#16
	aese	$key,$zero

	veor	$in0,$in0,$tmp
	vext.8	$tmp,$zero,$tmp,#12
	veor	$in0,$in0,$tmp
	vext.8	$tmp,$zero,$tmp,#12
	 veor	$key,$key,$rcon
	veor	$in0,$in0,$tmp
	veor	$in0,$in0,$key
	vst1.32	{$in0},[$out]
	add	$out,$out,#0x50

	mov	$rounds,#10
	b	.Ldone

.align	4
.L192:
	vld1.8	{$in1},[$inp],#8
	vmov.i8	$key,#8			// borrow $key
	vst1.32	{$in0},[$out],#16
	vsub.i8	$mask,$mask,$key	// adjust the mask

.Loop192:
	vtbl.8	$key,{$in1},$mask
	vext.8	$tmp,$zero,$in0,#12
	vst1.32	{$in1},[$out],#8
	aese	$key,$zero
	subs	$bits,$bits,#1

	veor	$in0,$in0,$tmp
	vext.8	$tmp,$zero,$tmp,#12
	veor	$in0,$in0,$tmp
	vext.8	$tmp,$zero,$tmp,#12
	veor	$in0,$in0,$tmp

	vdup.32	$tmp,${in0}[3]
	veor	$tmp,$tmp,$in1
	 veor	$key,$key,$rcon
	vext.8	$in1,$zero,$in1,#12
	vshl.u8	$rcon,$rcon,#1
	veor	$in1,$in1,$tmp
	veor	$in0,$in0,$key
	veor	$in1,$in1,$key
	vst1.32	{$in0},[$out],#16
	b.ne	.Loop192

	mov	$rounds,#12
	add	$out,$out,#0x20
	b	.Ldone

.align	4
.L256:
	vld1.8	{$in1},[$inp]
	mov	$bits,#7
	mov	$rounds,#14
	vst1.32	{$in0},[$out],#16

.Loop256:
	vtbl.8	$key,{$in1},$mask
	vext.8	$tmp,$zero,$in0,#12
	vst1.32	{$in1},[$out],#16
	aese	$key,$zero
	subs	$bits,$bits,#1

	veor	$in0,$in0,$tmp
	vext.8	$tmp,$zero,$tmp,#12
	veor	$in0,$in0,$tmp
	vext.8	$tmp,$zero,$tmp,#12
	 veor	$key,$key,$rcon
	veor	$in0,$in0,$tmp
	vshl.u8	$rcon,$rcon,#1
	veor	$in0,$in0,$key
	vst1.32	{$in0},[$out],#16
	b.eq	.Ldone

	vdup.32	$key,${in0}[3]		// just splat
	vext.8	$tmp,$zero,$in1,#12
	aese	$key,$zero

	veor	$in1,$in1,$tmp
	vext.8	$tmp,$zero,$tmp,#12
	veor	$in1,$in1,$tmp
	vext.8	$tmp,$zero,$tmp,#12
	veor	$in1,$in1,$tmp

	veor	$in1,$in1,$key
	b	.Loop256

.Ldone:
	str	$rounds,[$out]
	mov	$ptr,#0

.Lenc_key_abort:
	mov	x0,$ptr			// return value
	`"ldr	x29,[sp],#16"		if ($flavour =~ /64/)`
	ret
.size	${prefix}_set_encrypt_key,.-${prefix}_set_encrypt_key

.globl	${prefix}_set_decrypt_key
.type	${prefix}_set_decrypt_key,%function
.align	5
${prefix}_set_decrypt_key:
___
$code.=<<___	if ($flavour =~ /64/);
	AARCH64_SIGN_LINK_REGISTER
	stp	x29,x30,[sp,#-16]!
	add	x29,sp,#0
___
$code.=<<___	if ($flavour !~ /64/);
	stmdb	sp!,{r4,lr}
___
$code.=<<___;
	bl	.Lenc_key

	cmp	x0,#0
	b.ne	.Ldec_key_abort

	sub	$out,$out,#240		// restore original $out
	mov	x4,#-16
	add	$inp,$out,x12,lsl#4	// end of key schedule

	vld1.32	{v0.16b},[$out]
	vld1.32	{v1.16b},[$inp]
	vst1.32	{v0.16b},[$inp],x4
	vst1.32	{v1.16b},[$out],#16

.Loop_imc:
	vld1.32	{v0.16b},[$out]
	vld1.32	{v1.16b},[$inp]
	aesimc	v0.16b,v0.16b
	aesimc	v1.16b,v1.16b
	vst1.32	{v0.16b},[$inp],x4
	vst1.32	{v1.16b},[$out],#16
	cmp	$inp,$out
	b.hi	.Loop_imc

	vld1.32	{v0.16b},[$out]
	aesimc	v0.16b,v0.16b
	vst1.32	{v0.16b},[$inp]

	eor	x0,x0,x0		// return value
.Ldec_key_abort:
___
$code.=<<___	if ($flavour !~ /64/);
	ldmia	sp!,{r4,pc}
___
$code.=<<___	if ($flavour =~ /64/);
	ldp	x29,x30,[sp],#16
	AARCH64_VALIDATE_LINK_REGISTER
	ret
___
$code.=<<___;
.size	${prefix}_set_decrypt_key,.-${prefix}_set_decrypt_key
___
}}}
{{{
sub gen_block () {
my $dir = shift;
my ($e,$mc) = $dir eq "en" ? ("e","mc") : ("d","imc");
my ($inp,$out,$key)=map("x$_",(0..2));
my $rounds="w3";
my ($rndkey0,$rndkey1,$inout)=map("q$_",(0..3));

$code.=<<___;
.globl	${prefix}_${dir}crypt
.type	${prefix}_${dir}crypt,%function
.align	5
${prefix}_${dir}crypt:
___
$code.=<<___	if ($flavour =~ /64/);
#ifdef BORINGSSL_DISPATCH_TEST
.extern        BORINGSSL_function_hit
	adrp	x9,:pg_hi21:BORINGSSL_function_hit
	add     x9, x9, :lo12:BORINGSSL_function_hit
	mov     w10, #1
	strb    w10, [x9,#1] // kFlag_aes_hw_encrypt
#endif
___
$code.=<<___;
	AARCH64_VALID_CALL_TARGET
	ldr	$rounds,[$key,#240]
	vld1.32	{$rndkey0},[$key],#16
	vld1.8	{$inout},[$inp]
	sub	$rounds,$rounds,#2
	vld1.32	{$rndkey1},[$key],#16

.Loop_${dir}c:
	aes$e	$inout,$rndkey0
	aes$mc	$inout,$inout
	vld1.32	{$rndkey0},[$key],#16
	subs	$rounds,$rounds,#2
	aes$e	$inout,$rndkey1
	aes$mc	$inout,$inout
	vld1.32	{$rndkey1},[$key],#16
	b.gt	.Loop_${dir}c

	aes$e	$inout,$rndkey0
	aes$mc	$inout,$inout
	vld1.32	{$rndkey0},[$key]
	aes$e	$inout,$rndkey1
	veor	$inout,$inout,$rndkey0

	vst1.8	{$inout},[$out]
	ret
.size	${prefix}_${dir}crypt,.-${prefix}_${dir}crypt
___
}
&gen_block("en");
&gen_block("de");
}}}
{{{
my ($inp,$out,$len,$key,$ivp)=map("x$_",(0..4)); my $enc="w5";
my ($rounds,$cnt,$key_,$step,$step1)=($enc,"w6","x7","x8","x12");
my ($dat0,$dat1,$in0,$in1,$tmp0,$tmp1,$ivec,$rndlast)=map("q$_",(0..7));

my ($dat,$tmp,$rndzero_n_last)=($dat0,$tmp0,$tmp1);
my ($key4,$key5,$key6,$key7)=("x6","x12","x14",$key);

### q8-q15	preloaded key schedule

$code.=<<___;
.globl	${prefix}_cbc_encrypt
.type	${prefix}_cbc_encrypt,%function
.align	5
${prefix}_cbc_encrypt:
___
$code.=<<___	if ($flavour =~ /64/);
	// Armv8.3-A PAuth: even though x30 is pushed to stack it is not popped later.
	AARCH64_VALID_CALL_TARGET
	stp	x29,x30,[sp,#-16]!
	add	x29,sp,#0
___
$code.=<<___	if ($flavour !~ /64/);
	mov	ip,sp
	stmdb	sp!,{r4-r8,lr}
	vstmdb	sp!,{d8-d15}            @ ABI specification says so
	ldmia	ip,{r4-r5}		@ load remaining args
___
$code.=<<___;
	subs	$len,$len,#16
	mov	$step,#16
	b.lo	.Lcbc_abort
	cclr	$step,eq

	cmp	$enc,#0			// en- or decrypting?
	ldr	$rounds,[$key,#240]
	and	$len,$len,#-16
	vld1.8	{$ivec},[$ivp]
	vld1.8	{$dat},[$inp],$step

	vld1.32	{q8-q9},[$key]		// load key schedule...
	sub	$rounds,$rounds,#6
	add	$key_,$key,x5,lsl#4	// pointer to last 7 round keys
	sub	$rounds,$rounds,#2
	vld1.32	{q10-q11},[$key_],#32
	vld1.32	{q12-q13},[$key_],#32
	vld1.32	{q14-q15},[$key_],#32
	vld1.32	{$rndlast},[$key_]

	add	$key_,$key,#32
	mov	$cnt,$rounds
	b.eq	.Lcbc_dec

	cmp	$rounds,#2
	veor	$dat,$dat,$ivec
	veor	$rndzero_n_last,q8,$rndlast
	b.eq	.Lcbc_enc128

	vld1.32	{$in0-$in1},[$key_]
	add	$key_,$key,#16
	add	$key4,$key,#16*4
	add	$key5,$key,#16*5
	aese	$dat,q8
	aesmc	$dat,$dat
	add	$key6,$key,#16*6
	add	$key7,$key,#16*7
	b	.Lenter_cbc_enc

.align	4
.Loop_cbc_enc:
	aese	$dat,q8
	aesmc	$dat,$dat
	 vst1.8	{$ivec},[$out],#16
.Lenter_cbc_enc:
	aese	$dat,q9
	aesmc	$dat,$dat
	aese	$dat,$in0
	aesmc	$dat,$dat
	vld1.32	{q8},[$key4]
	cmp	$rounds,#4
	aese	$dat,$in1
	aesmc	$dat,$dat
	vld1.32	{q9},[$key5]
	b.eq	.Lcbc_enc192

	aese	$dat,q8
	aesmc	$dat,$dat
	vld1.32	{q8},[$key6]
	aese	$dat,q9
	aesmc	$dat,$dat
	vld1.32	{q9},[$key7]
	nop

.Lcbc_enc192:
	aese	$dat,q8
	aesmc	$dat,$dat
	 subs	$len,$len,#16
	aese	$dat,q9
	aesmc	$dat,$dat
	 cclr	$step,eq
	aese	$dat,q10
	aesmc	$dat,$dat
	aese	$dat,q11
	aesmc	$dat,$dat
	 vld1.8	{q8},[$inp],$step
	aese	$dat,q12
	aesmc	$dat,$dat
	 veor	q8,q8,$rndzero_n_last
	aese	$dat,q13
	aesmc	$dat,$dat
	 vld1.32 {q9},[$key_]		// re-pre-load rndkey[1]
	aese	$dat,q14
	aesmc	$dat,$dat
	aese	$dat,q15
	veor	$ivec,$dat,$rndlast
	b.hs	.Loop_cbc_enc

	vst1.8	{$ivec},[$out],#16
	b	.Lcbc_done

.align	5
.Lcbc_enc128:
	vld1.32	{$in0-$in1},[$key_]
	aese	$dat,q8
	aesmc	$dat,$dat
	b	.Lenter_cbc_enc128
.Loop_cbc_enc128:
	aese	$dat,q8
	aesmc	$dat,$dat
	 vst1.8	{$ivec},[$out],#16
.Lenter_cbc_enc128:
	aese	$dat,q9
	aesmc	$dat,$dat
	 subs	$len,$len,#16
	aese	$dat,$in0
	aesmc	$dat,$dat
	 cclr	$step,eq
	aese	$dat,$in1
	aesmc	$dat,$dat
	aese	$dat,q10
	aesmc	$dat,$dat
	aese	$dat,q11
	aesmc	$dat,$dat
	 vld1.8	{q8},[$inp],$step
	aese	$dat,q12
	aesmc	$dat,$dat
	aese	$dat,q13
	aesmc	$dat,$dat
	aese	$dat,q14
	aesmc	$dat,$dat
	 veor	q8,q8,$rndzero_n_last
	aese	$dat,q15
	veor	$ivec,$dat,$rndlast
	b.hs	.Loop_cbc_enc128

	vst1.8	{$ivec},[$out],#16
	b	.Lcbc_done
___
{
my ($dat2,$in2,$tmp2)=map("q$_",(10,11,9));
$code.=<<___;
.align	5
.Lcbc_dec:
	vld1.8	{$dat2},[$inp],#16
	subs	$len,$len,#32		// bias
	add	$cnt,$rounds,#2
	vorr	$in1,$dat,$dat
	vorr	$dat1,$dat,$dat
	vorr	$in2,$dat2,$dat2
	b.lo	.Lcbc_dec_tail

	vorr	$dat1,$dat2,$dat2
	vld1.8	{$dat2},[$inp],#16
	vorr	$in0,$dat,$dat
	vorr	$in1,$dat1,$dat1
	vorr	$in2,$dat2,$dat2

.Loop3x_cbc_dec:
	aesd	$dat0,q8
	aesimc	$dat0,$dat0
	aesd	$dat1,q8
	aesimc	$dat1,$dat1
	aesd	$dat2,q8
	aesimc	$dat2,$dat2
	vld1.32	{q8},[$key_],#16
	subs	$cnt,$cnt,#2
	aesd	$dat0,q9
	aesimc	$dat0,$dat0
	aesd	$dat1,q9
	aesimc	$dat1,$dat1
	aesd	$dat2,q9
	aesimc	$dat2,$dat2
	vld1.32	{q9},[$key_],#16
	b.gt	.Loop3x_cbc_dec

	aesd	$dat0,q8
	aesimc	$dat0,$dat0
	aesd	$dat1,q8
	aesimc	$dat1,$dat1
	aesd	$dat2,q8
	aesimc	$dat2,$dat2
	 veor	$tmp0,$ivec,$rndlast
	 subs	$len,$len,#0x30
	 veor	$tmp1,$in0,$rndlast
	 mov.lo	x6,$len			// x6, $cnt, is zero at this point
	aesd	$dat0,q9
	aesimc	$dat0,$dat0
	aesd	$dat1,q9
	aesimc	$dat1,$dat1
	aesd	$dat2,q9
	aesimc	$dat2,$dat2
	 veor	$tmp2,$in1,$rndlast
	 add	$inp,$inp,x6		// $inp is adjusted in such way that
					// at exit from the loop $dat1-$dat2
					// are loaded with last "words"
	 vorr	$ivec,$in2,$in2
	 mov	$key_,$key
	aesd	$dat0,q12
	aesimc	$dat0,$dat0
	aesd	$dat1,q12
	aesimc	$dat1,$dat1
	aesd	$dat2,q12
	aesimc	$dat2,$dat2
	 vld1.8	{$in0},[$inp],#16
	aesd	$dat0,q13
	aesimc	$dat0,$dat0
	aesd	$dat1,q13
	aesimc	$dat1,$dat1
	aesd	$dat2,q13
	aesimc	$dat2,$dat2
	 vld1.8	{$in1},[$inp],#16
	aesd	$dat0,q14
	aesimc	$dat0,$dat0
	aesd	$dat1,q14
	aesimc	$dat1,$dat1
	aesd	$dat2,q14
	aesimc	$dat2,$dat2
	 vld1.8	{$in2},[$inp],#16
	aesd	$dat0,q15
	aesd	$dat1,q15
	aesd	$dat2,q15
	 vld1.32 {q8},[$key_],#16	// re-pre-load rndkey[0]
	 add	$cnt,$rounds,#2
	veor	$tmp0,$tmp0,$dat0
	veor	$tmp1,$tmp1,$dat1
	veor	$dat2,$dat2,$tmp2
	 vld1.32 {q9},[$key_],#16	// re-pre-load rndkey[1]
	vst1.8	{$tmp0},[$out],#16
	 vorr	$dat0,$in0,$in0
	vst1.8	{$tmp1},[$out],#16
	 vorr	$dat1,$in1,$in1
	vst1.8	{$dat2},[$out],#16
	 vorr	$dat2,$in2,$in2
	b.hs	.Loop3x_cbc_dec

	cmn	$len,#0x30
	b.eq	.Lcbc_done
	nop

.Lcbc_dec_tail:
	aesd	$dat1,q8
	aesimc	$dat1,$dat1
	aesd	$dat2,q8
	aesimc	$dat2,$dat2
	vld1.32	{q8},[$key_],#16
	subs	$cnt,$cnt,#2
	aesd	$dat1,q9
	aesimc	$dat1,$dat1
	aesd	$dat2,q9
	aesimc	$dat2,$dat2
	vld1.32	{q9},[$key_],#16
	b.gt	.Lcbc_dec_tail

	aesd	$dat1,q8
	aesimc	$dat1,$dat1
	aesd	$dat2,q8
	aesimc	$dat2,$dat2
	aesd	$dat1,q9
	aesimc	$dat1,$dat1
	aesd	$dat2,q9
	aesimc	$dat2,$dat2
	aesd	$dat1,q12
	aesimc	$dat1,$dat1
	aesd	$dat2,q12
	aesimc	$dat2,$dat2
	 cmn	$len,#0x20
	aesd	$dat1,q13
	aesimc	$dat1,$dat1
	aesd	$dat2,q13
	aesimc	$dat2,$dat2
	 veor	$tmp1,$ivec,$rndlast
	aesd	$dat1,q14
	aesimc	$dat1,$dat1
	aesd	$dat2,q14
	aesimc	$dat2,$dat2
	 veor	$tmp2,$in1,$rndlast
	aesd	$dat1,q15
	aesd	$dat2,q15
	b.eq	.Lcbc_dec_one
	veor	$tmp1,$tmp1,$dat1
	veor	$tmp2,$tmp2,$dat2
	 vorr	$ivec,$in2,$in2
	vst1.8	{$tmp1},[$out],#16
	vst1.8	{$tmp2},[$out],#16
	b	.Lcbc_done

.Lcbc_dec_one:
	veor	$tmp1,$tmp1,$dat2
	 vorr	$ivec,$in2,$in2
	vst1.8	{$tmp1},[$out],#16

.Lcbc_done:
	vst1.8	{$ivec},[$ivp]
.Lcbc_abort:
___
}
$code.=<<___	if ($flavour !~ /64/);
	vldmia	sp!,{d8-d15}
	ldmia	sp!,{r4-r8,pc}
___
$code.=<<___	if ($flavour =~ /64/);
	ldr	x29,[sp],#16
	ret
___
$code.=<<___;
.size	${prefix}_cbc_encrypt,.-${prefix}_cbc_encrypt
___
}}}
{{{
my ($inp,$out,$len,$key,$ivp)=map("x$_",(0..4));
my ($rounds,$cnt,$key_)=("w5","w6","x7");
my ($ctr,$tctr0,$tctr1,$tctr2)=map("w$_",(8..10,12));
my $step="x12";		# aliases with $tctr2

my ($dat0,$dat1,$in0,$in1,$tmp0,$tmp1,$ivec,$rndlast)=map("q$_",(0..7));
my ($dat2,$in2,$tmp2)=map("q$_",(10,11,9));

my ($dat,$tmp)=($dat0,$tmp0);

### q8-q15	preloaded key schedule

$code.=<<___;
.globl	${prefix}_ctr32_encrypt_blocks
.type	${prefix}_ctr32_encrypt_blocks,%function
.align	5
${prefix}_ctr32_encrypt_blocks:
___
$code.=<<___	if ($flavour =~ /64/);
#ifdef BORINGSSL_DISPATCH_TEST
.extern        BORINGSSL_function_hit
	adrp	x9,:pg_hi21:BORINGSSL_function_hit
	add     x9, x9, :lo12:BORINGSSL_function_hit
	mov     w10, #1
	strb    w10, [x9] // kFlag_aes_hw_ctr32_encrypt_blocks
#endif
	// Armv8.3-A PAuth: even though x30 is pushed to stack it is not popped later.
	AARCH64_VALID_CALL_TARGET
	stp		x29,x30,[sp,#-16]!
	add		x29,sp,#0
___
$code.=<<___	if ($flavour !~ /64/);
	mov		ip,sp
	stmdb		sp!,{r4-r10,lr}
	vstmdb		sp!,{d8-d15}            @ ABI specification says so
	ldr		r4, [ip]		@ load remaining arg
___
$code.=<<___;
	ldr		$rounds,[$key,#240]

	ldr		$ctr, [$ivp, #12]
	vld1.32		{$dat0},[$ivp]

	vld1.32		{q8-q9},[$key]		// load key schedule...
	sub		$rounds,$rounds,#4
	mov		$step,#16
	cmp		$len,#2
	add		$key_,$key,x5,lsl#4	// pointer to last 5 round keys
	sub		$rounds,$rounds,#2
	vld1.32		{q12-q13},[$key_],#32
	vld1.32		{q14-q15},[$key_],#32
	vld1.32		{$rndlast},[$key_]
	add		$key_,$key,#32
	mov		$cnt,$rounds
	cclr		$step,lo

	// ARM Cortex-A57 and Cortex-A72 cores running in 32-bit mode are
	// affected by silicon errata #1742098 [0] and #1655431 [1],
	// respectively, where the second instruction of an aese/aesmc
	// instruction pair may execute twice if an interrupt is taken right
	// after the first instruction consumes an input register of which a
	// single 32-bit lane has been updated the last time it was modified.
	//
	// This function uses a counter in one 32-bit lane. The vmov.32 lines
	// could write to $dat1 and $dat2 directly, but that trips this bugs.
	// We write to $ivec and copy to the final register as a workaround.
	//
	// [0] ARM-EPM-049219 v23 Cortex-A57 MPCore Software Developers Errata Notice
	// [1] ARM-EPM-012079 v11.0 Cortex-A72 MPCore Software Developers Errata Notice
#ifndef __ARMEB__
	rev		$ctr, $ctr
#endif
	add		$tctr1, $ctr, #1
	vorr		$ivec,$dat0,$dat0
	rev		$tctr1, $tctr1
	vmov.32		${ivec}[3],$tctr1
	add		$ctr, $ctr, #2
	vorr		$dat1,$ivec,$ivec
	b.ls		.Lctr32_tail
	rev		$tctr2, $ctr
	vmov.32		${ivec}[3],$tctr2
	sub		$len,$len,#3		// bias
	vorr		$dat2,$ivec,$ivec
	b		.Loop3x_ctr32

.align	4
.Loop3x_ctr32:
	aese		$dat0,q8
	aesmc		$dat0,$dat0
	aese		$dat1,q8
	aesmc		$dat1,$dat1
	aese		$dat2,q8
	aesmc		$dat2,$dat2
	vld1.32		{q8},[$key_],#16
	subs		$cnt,$cnt,#2
	aese		$dat0,q9
	aesmc		$dat0,$dat0
	aese		$dat1,q9
	aesmc		$dat1,$dat1
	aese		$dat2,q9
	aesmc		$dat2,$dat2
	vld1.32		{q9},[$key_],#16
	b.gt		.Loop3x_ctr32

	aese		$dat0,q8
	aesmc		$tmp0,$dat0
	aese		$dat1,q8
	aesmc		$tmp1,$dat1
	 vld1.8		{$in0},[$inp],#16
	 add		$tctr0,$ctr,#1
	aese		$dat2,q8
	aesmc		$dat2,$dat2
	 vld1.8		{$in1},[$inp],#16
	 rev		$tctr0,$tctr0
	aese		$tmp0,q9
	aesmc		$tmp0,$tmp0
	aese		$tmp1,q9
	aesmc		$tmp1,$tmp1
	 vld1.8		{$in2},[$inp],#16
	 mov		$key_,$key
	aese		$dat2,q9
	aesmc		$tmp2,$dat2
	aese		$tmp0,q12
	aesmc		$tmp0,$tmp0
	aese		$tmp1,q12
	aesmc		$tmp1,$tmp1
	 veor		$in0,$in0,$rndlast
	 add		$tctr1,$ctr,#2
	aese		$tmp2,q12
	aesmc		$tmp2,$tmp2
	 veor		$in1,$in1,$rndlast
	 add		$ctr,$ctr,#3
	aese		$tmp0,q13
	aesmc		$tmp0,$tmp0
	aese		$tmp1,q13
	aesmc		$tmp1,$tmp1
	 // Note the logic to update $dat0, $dat1, and $dat1 is written to work
	 // around a bug in ARM Cortex-A57 and Cortex-A72 cores running in
	 // 32-bit mode. See the comment above.
	 veor		$in2,$in2,$rndlast
	 vmov.32	${ivec}[3], $tctr0
	aese		$tmp2,q13
	aesmc		$tmp2,$tmp2
	 vorr		$dat0,$ivec,$ivec
	 rev		$tctr1,$tctr1
	aese		$tmp0,q14
	aesmc		$tmp0,$tmp0
	 vmov.32	${ivec}[3], $tctr1
	 rev		$tctr2,$ctr
	aese		$tmp1,q14
	aesmc		$tmp1,$tmp1
	 vorr		$dat1,$ivec,$ivec
	 vmov.32	${ivec}[3], $tctr2
	aese		$tmp2,q14
	aesmc		$tmp2,$tmp2
	 vorr		$dat2,$ivec,$ivec
	 subs		$len,$len,#3
	aese		$tmp0,q15
	aese		$tmp1,q15
	aese		$tmp2,q15

	veor		$in0,$in0,$tmp0
	 vld1.32	 {q8},[$key_],#16	// re-pre-load rndkey[0]
	vst1.8		{$in0},[$out],#16
	veor		$in1,$in1,$tmp1
	 mov		$cnt,$rounds
	vst1.8		{$in1},[$out],#16
	veor		$in2,$in2,$tmp2
	 vld1.32	 {q9},[$key_],#16	// re-pre-load rndkey[1]
	vst1.8		{$in2},[$out],#16
	b.hs		.Loop3x_ctr32

	adds		$len,$len,#3
	b.eq		.Lctr32_done
	cmp		$len,#1
	mov		$step,#16
	cclr		$step,eq

.Lctr32_tail:
	aese		$dat0,q8
	aesmc		$dat0,$dat0
	aese		$dat1,q8
	aesmc		$dat1,$dat1
	vld1.32		{q8},[$key_],#16
	subs		$cnt,$cnt,#2
	aese		$dat0,q9
	aesmc		$dat0,$dat0
	aese		$dat1,q9
	aesmc		$dat1,$dat1
	vld1.32		{q9},[$key_],#16
	b.gt		.Lctr32_tail

	aese		$dat0,q8
	aesmc		$dat0,$dat0
	aese		$dat1,q8
	aesmc		$dat1,$dat1
	aese		$dat0,q9
	aesmc		$dat0,$dat0
	aese		$dat1,q9
	aesmc		$dat1,$dat1
	 vld1.8		{$in0},[$inp],$step
	aese		$dat0,q12
	aesmc		$dat0,$dat0
	aese		$dat1,q12
	aesmc		$dat1,$dat1
	 vld1.8		{$in1},[$inp]
	aese		$dat0,q13
	aesmc		$dat0,$dat0
	aese		$dat1,q13
	aesmc		$dat1,$dat1
	 veor		$in0,$in0,$rndlast
	aese		$dat0,q14
	aesmc		$dat0,$dat0
	aese		$dat1,q14
	aesmc		$dat1,$dat1
	 veor		$in1,$in1,$rndlast
	aese		$dat0,q15
	aese		$dat1,q15

	cmp		$len,#1
	veor		$in0,$in0,$dat0
	veor		$in1,$in1,$dat1
	vst1.8		{$in0},[$out],#16
	b.eq		.Lctr32_done
	vst1.8		{$in1},[$out]

.Lctr32_done:
___
$code.=<<___	if ($flavour !~ /64/);
	vldmia		sp!,{d8-d15}
	ldmia		sp!,{r4-r10,pc}
___
$code.=<<___	if ($flavour =~ /64/);
	ldr		x29,[sp],#16
	ret
___
$code.=<<___;
.size	${prefix}_ctr32_encrypt_blocks,.-${prefix}_ctr32_encrypt_blocks
___
}}}
# Performance in cycles per byte.
# Processed with AES-XTS different key size.
# It shows the value before and after optimization as below:
# (before/after):
#
#              AES-128-XTS     AES-256-XTS
# Cortex-A57    3.36/1.09       4.02/1.37
# Cortex-A72    3.03/1.02       3.28/1.33

# Optimization is implemented by loop unrolling and interleaving.
# Commonly, we choose the unrolling factor as 5, if the input
# data size smaller than 5 blocks, but not smaller than 3 blocks,
# choose 3 as the unrolling factor.
# If the input data size dsize >= 5*16 bytes, then take 5 blocks
# as one iteration, every loop the left size lsize -= 5*16.
# If lsize < 5*16 bytes, treat them as the tail. Note: left 4*16 bytes
# will be processed specially, which be integrated into the 5*16 bytes
# loop to improve the efficiency.
# There is one special case, if the original input data size dsize
# = 16 bytes, we will treat it seperately to improve the
# performance: one independent code block without LR, FP load and
# store.
# Encryption will process the (length -tailcnt) bytes as mentioned
# previously, then encrypt the composite block as last second
# cipher block.
# Decryption will process the (length -tailcnt -1) bytes as mentioned
# previously, then decrypt the last second cipher block to get the
# last plain block(tail), decrypt the composite block as last second
# plain text block.

{{{
my ($inp,$out,$len,$key1,$key2,$ivp)=map("x$_",(0..5));
my ($rounds0,$rounds,$key_,$step,$ivl,$ivh)=("w5","w6","x7","x8","x9","x10");
my ($tmpoutp,$loutp,$l2outp,$tmpinp)=("x13","w14","w15","x20");
my ($tailcnt,$midnum,$midnumx,$constnum,$constnumx)=("x21","w22","x22","w19","x19");
my ($xoffset,$tmpmx,$tmpmw)=("x6","x11","w11");
my ($dat0,$dat1,$in0,$in1,$tmp0,$tmp1,$tmp2,$rndlast)=map("q$_",(0..7));
my ($iv0,$iv1,$iv2,$iv3,$iv4)=("v6.16b","v8.16b","v9.16b","v10.16b","v11.16b");
my ($ivd00,$ivd01,$ivd20,$ivd21)=("d6","v6.d[1]","d9","v9.d[1]");
my ($ivd10,$ivd11,$ivd30,$ivd31,$ivd40,$ivd41)=("d8","v8.d[1]","d10","v10.d[1]","d11","v11.d[1]");

my ($tmpin)=("v26.16b");
my ($dat,$tmp,$rndzero_n_last)=($dat0,$tmp0,$tmp1);

# q7                last round key
# q10-q15, q7       Last 7 round keys
# q8-q9             preloaded round keys except last 7 keys for big size
# q20, q21, q8-q9   preloaded round keys except last 7 keys for only 16 byte


my ($dat2,$in2,$tmp2)=map("q$_",(10,11,9));

my ($dat3,$in3,$tmp3);  # used only in 64-bit mode
my ($dat4,$in4,$tmp4);
if ($flavour =~ /64/) {
    ($dat2,$dat3,$dat4,$in2,$in3,$in4,$tmp3,$tmp4)=map("q$_",(16..23));
}

$code.=<<___    if ($flavour =~ /64/);
.globl  ${prefix}_xts_encrypt
.type   ${prefix}_xts_encrypt,%function
.align  5
${prefix}_xts_encrypt:
___
$code.=<<___    if ($flavour =~ /64/);
    AARCH64_VALID_CALL_TARGET
    cmp $len,#16
    // Original input data size bigger than 16, jump to big size processing.
    b.ne    .Lxts_enc_big_size
    // Encrypt the iv with key2, as the first XEX iv.
    ldr $rounds,[$key2,#240]
    vld1.8  {$dat},[$key2],#16
    vld1.8  {$iv0},[$ivp]
    sub $rounds,$rounds,#2
    vld1.8  {$dat1},[$key2],#16

.Loop_enc_iv_enc:
    aese    $iv0,$dat
    aesmc   $iv0,$iv0
    vld1.32 {$dat},[$key2],#16
    subs    $rounds,$rounds,#2
    aese    $iv0,$dat1
    aesmc   $iv0,$iv0
    vld1.32 {$dat1},[$key2],#16
    b.gt    .Loop_enc_iv_enc

    aese    $iv0,$dat
    aesmc   $iv0,$iv0
    vld1.32 {$dat},[$key2]
    aese    $iv0,$dat1
    veor    $iv0,$iv0,$dat

    vld1.8  {$dat0},[$inp]
    veor    $dat0,$iv0,$dat0

    ldr $rounds,[$key1,#240]
    vld1.32 {q20-q21},[$key1],#32       // load key schedule...

    aese    $dat0,q20
    aesmc   $dat0,$dat0
    vld1.32 {q8-q9},[$key1],#32         // load key schedule...
    aese    $dat0,q21
    aesmc   $dat0,$dat0
    subs    $rounds,$rounds,#10     // if rounds==10, jump to aes-128-xts processing
    b.eq    .Lxts_128_enc
.Lxts_enc_round_loop:
    aese    $dat0,q8
    aesmc   $dat0,$dat0
    vld1.32 {q8},[$key1],#16            // load key schedule...
    aese    $dat0,q9
    aesmc   $dat0,$dat0
    vld1.32 {q9},[$key1],#16            // load key schedule...
    subs    $rounds,$rounds,#2          // bias
    b.gt    .Lxts_enc_round_loop
.Lxts_128_enc:
    vld1.32 {q10-q11},[$key1],#32       // load key schedule...
    aese    $dat0,q8
    aesmc   $dat0,$dat0
    aese    $dat0,q9
    aesmc   $dat0,$dat0
    vld1.32 {q12-q13},[$key1],#32       // load key schedule...
    aese    $dat0,q10
    aesmc   $dat0,$dat0
    aese    $dat0,q11
    aesmc   $dat0,$dat0
    vld1.32 {q14-q15},[$key1],#32       // load key schedule...
    aese    $dat0,q12
    aesmc   $dat0,$dat0
    aese    $dat0,q13
    aesmc   $dat0,$dat0
    vld1.32 {$rndlast},[$key1]
    aese    $dat0,q14
    aesmc   $dat0,$dat0
    aese    $dat0,q15
    veor    $dat0,$dat0,$rndlast
    veor    $dat0,$dat0,$iv0
    vst1.8  {$dat0},[$out]
    b   .Lxts_enc_final_abort

.align  4
.Lxts_enc_big_size:
   // Encrypt input size > 16 bytes
___
$code.=<<___    if ($flavour =~ /64/);
    stp $constnumx,$tmpinp,[sp,#-64]!
    stp $tailcnt,$midnumx,[sp,#48]
    stp $ivd10,$ivd20,[sp,#32]
    stp $ivd30,$ivd40,[sp,#16]

    // tailcnt store the tail value of length%16.
    and     $tailcnt,$len,#0xf
    and     $len,$len,#-16    // len &= 0x1..110000, now divisible by 16
    subs    $len,$len,#16
    mov     $step,#16
    b.lo    .Lxts_abort         // if !(len > 16): error
    csel    $step,xzr,$step,eq  // if (len == 16): step = 0

    // Firstly, encrypt the iv with key2, as the first iv of XEX.
    ldr     $rounds,[$key2,#240]
    vld1.32 {$dat},[$key2],#16
    vld1.8  {$iv0},[$ivp]
    sub     $rounds,$rounds,#2
    vld1.32 {$dat1},[$key2],#16

.Loop_iv_enc:
    aese    $iv0,$dat
    aesmc   $iv0,$iv0
    vld1.32 {$dat},[$key2],#16
    subs    $rounds,$rounds,#2
    aese    $iv0,$dat1
    aesmc   $iv0,$iv0
    vld1.32 {$dat1},[$key2],#16
    b.gt    .Loop_iv_enc

    aese    $iv0,$dat
    aesmc   $iv0,$iv0
    vld1.32 {$dat},[$key2]
    aese    $iv0,$dat1
    veor    $iv0,$iv0,$dat

    // The iv for second block
    // $ivl- iv(low), $ivh - iv(high)
    // the five ivs stored into, $iv0,$iv1,$iv2,$iv3,$iv4
    fmov    $ivl,$ivd00
    fmov    $ivh,$ivd01
    mov     $constnum,#0x87
    extr    $midnumx,$ivh,$ivh,#32
    extr    $ivh,$ivh,$ivl,#63
    and     $tmpmw,$constnum,$midnum,asr#31
    eor     $ivl,$tmpmx,$ivl,lsl#1
    fmov    $ivd10,$ivl
    fmov    $ivd11,$ivh

    ldr $rounds0,[$key1,#240]       // next starting point
    vld1.8  {$dat},[$inp],$step

    vld1.32 {q8-q9},[$key1]         // load key schedule...
    sub     $rounds0,$rounds0,#6
    add     $key_,$key1,$ivp,lsl#4  // pointer to last 7 round keys
    sub     $rounds0,$rounds0,#2
    vld1.32 {q10-q11},[$key_],#32
    vld1.32 {q12-q13},[$key_],#32
    vld1.32 {q14-q15},[$key_],#32
    vld1.32 {$rndlast},[$key_]

    add     $key_,$key1,#32
    mov     $rounds,$rounds0

    // Encryption
.Lxts_enc:
    vld1.8  {$dat2},[$inp],#16
    subs    $len,$len,#32           // bias
    add     $rounds,$rounds0,#2
    vorr    $in1,$dat,$dat
    vorr    $dat1,$dat,$dat
    vorr    $in3,$dat,$dat
    vorr    $in2,$dat2,$dat2
    vorr    $in4,$dat2,$dat2
    b.lo    .Lxts_inner_enc_tail    // when input size % 5 = 1 or 2
                                    // (with tail or not)
    veor    $dat,$dat,$iv0          // before encryption, xor with iv
    veor    $dat2,$dat2,$iv1

    // The iv for third block
    extr    $midnumx,$ivh,$ivh,#32
    extr    $ivh,$ivh,$ivl,#63
    and     $tmpmw,$constnum,$midnum,asr#31
    eor     $ivl,$tmpmx,$ivl,lsl#1
    fmov    $ivd20,$ivl
    fmov    $ivd21,$ivh


    vorr    $dat1,$dat2,$dat2
    vld1.8  {$dat2},[$inp],#16
    vorr    $in0,$dat,$dat
    vorr    $in1,$dat1,$dat1
    veor    $in2,$dat2,$iv2         // the third block
    veor    $dat2,$dat2,$iv2
    cmp     $len,#32
    b.lo    .Lxts_outer_enc_tail

    // The iv for fourth block
    extr    $midnumx,$ivh,$ivh,#32
    extr    $ivh,$ivh,$ivl,#63
    and     $tmpmw,$constnum,$midnum,asr#31
    eor     $ivl,$tmpmx,$ivl,lsl#1
    fmov    $ivd30,$ivl
    fmov    $ivd31,$ivh

    vld1.8  {$dat3},[$inp],#16
    // The iv for fifth block
    extr    $midnumx,$ivh,$ivh,#32
    extr    $ivh,$ivh,$ivl,#63
    and     $tmpmw,$constnum,$midnum,asr#31
    eor     $ivl,$tmpmx,$ivl,lsl#1
    fmov    $ivd40,$ivl
    fmov    $ivd41,$ivh

    vld1.8  {$dat4},[$inp],#16
    veor    $dat3,$dat3,$iv3        // the fourth block
    veor    $dat4,$dat4,$iv4
    sub     $len,$len,#32           // bias
    mov     $rounds,$rounds0
    b       .Loop5x_xts_enc

.align  4
.Loop5x_xts_enc:
    aese    $dat0,q8
    aesmc   $dat0,$dat0
    aese    $dat1,q8
    aesmc   $dat1,$dat1
    aese    $dat2,q8
    aesmc   $dat2,$dat2
    aese    $dat3,q8
    aesmc   $dat3,$dat3
    aese    $dat4,q8
    aesmc   $dat4,$dat4
    vld1.32 {q8},[$key_],#16
    subs    $rounds,$rounds,#2
    aese    $dat0,q9
    aesmc   $dat0,$dat0
    aese    $dat1,q9
    aesmc   $dat1,$dat1
    aese    $dat2,q9
    aesmc   $dat2,$dat2
    aese    $dat3,q9
    aesmc   $dat3,$dat3
    aese    $dat4,q9
    aesmc   $dat4,$dat4
    vld1.32 {q9},[$key_],#16
    b.gt    .Loop5x_xts_enc

    aese    $dat0,q8
    aesmc   $dat0,$dat0
    aese    $dat1,q8
    aesmc   $dat1,$dat1
    aese    $dat2,q8
    aesmc   $dat2,$dat2
    aese    $dat3,q8
    aesmc   $dat3,$dat3
    aese    $dat4,q8
    aesmc   $dat4,$dat4
    subs    $len,$len,#0x50         // because .Lxts_enc_tail4x

    aese    $dat0,q9
    aesmc   $dat0,$dat0
    aese    $dat1,q9
    aesmc   $dat1,$dat1
    aese    $dat2,q9
    aesmc   $dat2,$dat2
    aese    $dat3,q9
    aesmc   $dat3,$dat3
    aese    $dat4,q9
    aesmc   $dat4,$dat4
    csel    $xoffset,xzr,$len,gt    // borrow x6, w6, "gt" is not typo
    mov     $key_,$key1

    aese    $dat0,q10
    aesmc   $dat0,$dat0
    aese    $dat1,q10
    aesmc   $dat1,$dat1
    aese    $dat2,q10
    aesmc   $dat2,$dat2
    aese    $dat3,q10
    aesmc   $dat3,$dat3
    aese    $dat4,q10
    aesmc   $dat4,$dat4
    add     $inp,$inp,$xoffset  // x0 is adjusted in such way that
                                // at exit from the loop v1.16b-v26.16b
                                // are loaded with last "words"
    add $xoffset,$len,#0x60         // because .Lxts_enc_tail4x

    aese    $dat0,q11
    aesmc   $dat0,$dat0
    aese    $dat1,q11
    aesmc   $dat1,$dat1
    aese    $dat2,q11
    aesmc   $dat2,$dat2
    aese    $dat3,q11
    aesmc   $dat3,$dat3
    aese    $dat4,q11
    aesmc   $dat4,$dat4

    aese    $dat0,q12
    aesmc   $dat0,$dat0
    aese    $dat1,q12
    aesmc   $dat1,$dat1
    aese    $dat2,q12
    aesmc   $dat2,$dat2
    aese    $dat3,q12
    aesmc   $dat3,$dat3
    aese    $dat4,q12
    aesmc   $dat4,$dat4

    aese    $dat0,q13
    aesmc   $dat0,$dat0
    aese    $dat1,q13
    aesmc   $dat1,$dat1
    aese    $dat2,q13
    aesmc   $dat2,$dat2
    aese    $dat3,q13
    aesmc   $dat3,$dat3
    aese    $dat4,q13
    aesmc   $dat4,$dat4

    aese    $dat0,q14
    aesmc   $dat0,$dat0
    aese    $dat1,q14
    aesmc   $dat1,$dat1
    aese    $dat2,q14
    aesmc   $dat2,$dat2
    aese    $dat3,q14
    aesmc   $dat3,$dat3
    aese    $dat4,q14
    aesmc   $dat4,$dat4

    veor    $tmp0,$rndlast,$iv0
    aese    $dat0,q15
    // The iv for first block of one iteration
    extr    $midnumx,$ivh,$ivh,#32
    extr    $ivh,$ivh,$ivl,#63
    and     $tmpmw,$constnum,$midnum,asr#31
    eor     $ivl,$tmpmx,$ivl,lsl#1
    fmov    $ivd00,$ivl
    fmov    $ivd01,$ivh
    veor    $tmp1,$rndlast,$iv1
    vld1.8  {$in0},[$inp],#16
    aese    $dat1,q15
    // The iv for second block
    extr    $midnumx,$ivh,$ivh,#32
    extr    $ivh,$ivh,$ivl,#63
    and     $tmpmw,$constnum,$midnum,asr#31
    eor     $ivl,$tmpmx,$ivl,lsl#1
    fmov    $ivd10,$ivl
    fmov    $ivd11,$ivh
    veor    $tmp2,$rndlast,$iv2
    vld1.8  {$in1},[$inp],#16
    aese    $dat2,q15
    // The iv for third block
    extr    $midnumx,$ivh,$ivh,#32
    extr    $ivh,$ivh,$ivl,#63
    and     $tmpmw,$constnum,$midnum,asr#31
    eor     $ivl,$tmpmx,$ivl,lsl#1
    fmov    $ivd20,$ivl
    fmov    $ivd21,$ivh
    veor    $tmp3,$rndlast,$iv3
    vld1.8  {$in2},[$inp],#16
    aese    $dat3,q15
    // The iv for fourth block
    extr    $midnumx,$ivh,$ivh,#32
    extr    $ivh,$ivh,$ivl,#63
    and     $tmpmw,$constnum,$midnum,asr#31
    eor     $ivl,$tmpmx,$ivl,lsl#1
    fmov    $ivd30,$ivl
    fmov    $ivd31,$ivh
    veor    $tmp4,$rndlast,$iv4
    vld1.8  {$in3},[$inp],#16
    aese    $dat4,q15

    // The iv for fifth block
    extr    $midnumx,$ivh,$ivh,#32
    extr    $ivh,$ivh,$ivl,#63
    and     $tmpmw,$constnum,$midnum,asr #31
    eor     $ivl,$tmpmx,$ivl,lsl #1
    fmov    $ivd40,$ivl
    fmov    $ivd41,$ivh

    vld1.8  {$in4},[$inp],#16
    cbz     $xoffset,.Lxts_enc_tail4x
    vld1.32 {q8},[$key_],#16        // re-pre-load rndkey[0]
    veor    $tmp0,$tmp0,$dat0
    veor    $dat0,$in0,$iv0
    veor    $tmp1,$tmp1,$dat1
    veor    $dat1,$in1,$iv1
    veor    $tmp2,$tmp2,$dat2
    veor    $dat2,$in2,$iv2
    veor    $tmp3,$tmp3,$dat3
    veor    $dat3,$in3,$iv3
    veor    $tmp4,$tmp4,$dat4
    vst1.8  {$tmp0},[$out],#16
    veor    $dat4,$in4,$iv4
    vst1.8  {$tmp1},[$out],#16
    mov     $rounds,$rounds0
    vst1.8  {$tmp2},[$out],#16
    vld1.32 {q9},[$key_],#16        // re-pre-load rndkey[1]
    vst1.8  {$tmp3},[$out],#16
    vst1.8  {$tmp4},[$out],#16
    b.hs    .Loop5x_xts_enc


    // If left 4 blocks, borrow the five block's processing.
    // This means if ($len + 1 block) == 0, which is the case
    // when input size % 5 = 4, continue processing and do
    // another iteration in Loop5x_xts_enc which will exit from
    // cbz  $xoffset,.Lxts_enc_tail4x.
    // Otherwise, this is the end of the loop continue processing
    // 0, 1, 2 or 3 blocks (with or without tail) starting at
    // Loop5x_enc_after
    cmn $len,#0x10
    b.ne    .Loop5x_enc_after
    vorr    $iv4,$iv3,$iv3
    vorr    $iv3,$iv2,$iv2
    vorr    $iv2,$iv1,$iv1
    vorr    $iv1,$iv0,$iv0
    fmov    $ivl,$ivd40
    fmov    $ivh,$ivd41
    veor    $dat0,$iv0,$in0
    veor    $dat1,$iv1,$in1
    veor    $dat2,$in2,$iv2
    veor    $dat3,$in3,$iv3
    veor    $dat4,$in4,$iv4
    b.eq    .Loop5x_xts_enc

.Loop5x_enc_after:
    add     $len,$len,#0x50
    cbz     $len,.Lxts_enc_done     // no blocks left

    add $rounds,$rounds0,#2
    subs    $len,$len,#0x30
    b.lo    .Lxts_inner_enc_tail    // 1 or 2 blocks left
                                    // (with tail or not)

    veor    $dat0,$iv0,$in2         // 3 blocks left
    veor    $dat1,$iv1,$in3
    veor    $dat2,$in4,$iv2
    b       .Lxts_outer_enc_tail

.align  4
.Lxts_enc_tail4x:
    add $inp,$inp,#16
    veor    $tmp1,$dat1,$tmp1
    vst1.8  {$tmp1},[$out],#16
    veor    $tmp2,$dat2,$tmp2
    vst1.8  {$tmp2},[$out],#16
    veor    $tmp3,$dat3,$tmp3
    veor    $tmp4,$dat4,$tmp4
    vst1.8  {$tmp3-$tmp4},[$out],#32
    b      .Lxts_enc_done
.align  4
.Lxts_outer_enc_tail:
    aese    $dat0,q8
    aesmc   $dat0,$dat0
    aese    $dat1,q8
    aesmc   $dat1,$dat1
    aese    $dat2,q8
    aesmc   $dat2,$dat2
    vld1.32 {q8},[$key_],#16
    subs    $rounds,$rounds,#2
    aese    $dat0,q9
    aesmc   $dat0,$dat0
    aese    $dat1,q9
    aesmc   $dat1,$dat1
    aese    $dat2,q9
    aesmc   $dat2,$dat2
    vld1.32 {q9},[$key_],#16
    b.gt    .Lxts_outer_enc_tail

    aese    $dat0,q8
    aesmc   $dat0,$dat0
    aese    $dat1,q8
    aesmc   $dat1,$dat1
    aese    $dat2,q8
    aesmc   $dat2,$dat2
    veor    $tmp0,$iv0,$rndlast
    subs    $len,$len,#0x30
    // The iv for first block
    fmov    $ivl,$ivd20
    fmov    $ivh,$ivd21
    //mov   $constnum,#0x87
    extr    $midnumx,$ivh,$ivh,#32
    extr    $ivh,$ivh,$ivl,#63
    and     $tmpmw,$constnum,$midnum,asr#31
    eor     $ivl,$tmpmx,$ivl,lsl#1
    fmov    $ivd00,$ivl
    fmov    $ivd01,$ivh
    veor    $tmp1,$iv1,$rndlast
    csel    $xoffset,$len,$xoffset,lo   // x6, w6, is zero at this point
    aese    $dat0,q9
    aesmc   $dat0,$dat0
    aese    $dat1,q9
    aesmc   $dat1,$dat1
    aese    $dat2,q9
    aesmc   $dat2,$dat2
    veor    $tmp2,$iv2,$rndlast

    add     $xoffset,$xoffset,#0x20
    add     $inp,$inp,$xoffset
    mov     $key_,$key1

    aese    $dat0,q12
    aesmc   $dat0,$dat0
    aese    $dat1,q12
    aesmc   $dat1,$dat1
    aese    $dat2,q12
    aesmc   $dat2,$dat2
    aese    $dat0,q13
    aesmc   $dat0,$dat0
    aese    $dat1,q13
    aesmc   $dat1,$dat1
    aese    $dat2,q13
    aesmc   $dat2,$dat2
    aese    $dat0,q14
    aesmc   $dat0,$dat0
    aese    $dat1,q14
    aesmc   $dat1,$dat1
    aese    $dat2,q14
    aesmc   $dat2,$dat2
    aese    $dat0,q15
    aese    $dat1,q15
    aese    $dat2,q15
    vld1.8  {$in2},[$inp],#16
    add     $rounds,$rounds0,#2
    vld1.32 {q8},[$key_],#16        // re-pre-load rndkey[0]
    veor    $tmp0,$tmp0,$dat0
    veor    $tmp1,$tmp1,$dat1
    veor    $dat2,$dat2,$tmp2
    vld1.32 {q9},[$key_],#16        // re-pre-load rndkey[1]
    vst1.8  {$tmp0},[$out],#16
    vst1.8  {$tmp1},[$out],#16
    vst1.8  {$dat2},[$out],#16
    cmn     $len,#0x30
    b.eq    .Lxts_enc_done
.Lxts_encxor_one:
    vorr    $in3,$in1,$in1
    vorr    $in4,$in2,$in2
    nop

.Lxts_inner_enc_tail:
    cmn     $len,#0x10
    veor    $dat1,$in3,$iv0
    veor    $dat2,$in4,$iv1
    b.eq    .Lxts_enc_tail_loop
    veor    $dat2,$in4,$iv0
.Lxts_enc_tail_loop:
    aese    $dat1,q8
    aesmc   $dat1,$dat1
    aese    $dat2,q8
    aesmc   $dat2,$dat2
    vld1.32 {q8},[$key_],#16
    subs    $rounds,$rounds,#2
    aese    $dat1,q9
    aesmc   $dat1,$dat1
    aese    $dat2,q9
    aesmc   $dat2,$dat2
    vld1.32 {q9},[$key_],#16
    b.gt    .Lxts_enc_tail_loop

    aese    $dat1,q8
    aesmc   $dat1,$dat1
    aese    $dat2,q8
    aesmc   $dat2,$dat2
    aese    $dat1,q9
    aesmc   $dat1,$dat1
    aese    $dat2,q9
    aesmc   $dat2,$dat2
    aese    $dat1,q12
    aesmc   $dat1,$dat1
    aese    $dat2,q12
    aesmc   $dat2,$dat2
    cmn     $len,#0x20
    aese    $dat1,q13
    aesmc   $dat1,$dat1
    aese    $dat2,q13
    aesmc   $dat2,$dat2
    veor    $tmp1,$iv0,$rndlast
    aese    $dat1,q14
    aesmc   $dat1,$dat1
    aese    $dat2,q14
    aesmc   $dat2,$dat2
    veor    $tmp2,$iv1,$rndlast
    aese    $dat1,q15
    aese    $dat2,q15
    b.eq    .Lxts_enc_one
    veor    $tmp1,$tmp1,$dat1
    vst1.8  {$tmp1},[$out],#16
    veor    $tmp2,$tmp2,$dat2
    vorr    $iv0,$iv1,$iv1
    vst1.8  {$tmp2},[$out],#16
    fmov    $ivl,$ivd10
    fmov    $ivh,$ivd11
    mov     $constnum,#0x87
    extr    $midnumx,$ivh,$ivh,#32
    extr    $ivh,$ivh,$ivl,#63
    and     $tmpmw,$constnum,$midnum,asr #31
    eor     $ivl,$tmpmx,$ivl,lsl #1
    fmov    $ivd00,$ivl
    fmov    $ivd01,$ivh
    b       .Lxts_enc_done

.Lxts_enc_one:
    veor    $tmp1,$tmp1,$dat2
    vorr    $iv0,$iv0,$iv0
    vst1.8  {$tmp1},[$out],#16
    fmov    $ivl,$ivd00
    fmov    $ivh,$ivd01
    mov     $constnum,#0x87
    extr    $midnumx,$ivh,$ivh,#32
    extr    $ivh,$ivh,$ivl,#63
    and     $tmpmw,$constnum,$midnum,asr #31
    eor     $ivl,$tmpmx,$ivl,lsl #1
    fmov    $ivd00,$ivl
    fmov    $ivd01,$ivh
    b       .Lxts_enc_done
.align  5
.Lxts_enc_done:
    // Process the tail block with cipher stealing.
    tst     $tailcnt,#0xf
    b.eq    .Lxts_abort

    mov     $tmpinp,$inp
    mov     $tmpoutp,$out
    sub     $out,$out,#16
.composite_enc_loop:
    subs    $tailcnt,$tailcnt,#1
    ldrb    $l2outp,[$out,$tailcnt]
    ldrb    $loutp,[$tmpinp,$tailcnt]
    strb    $l2outp,[$tmpoutp,$tailcnt]
    strb    $loutp,[$out,$tailcnt]
    b.gt    .composite_enc_loop
.Lxts_enc_load_done:
    vld1.8  {$tmpin},[$out]
    veor    $tmpin,$tmpin,$iv0

    // Encrypt the composite block to get the last second encrypted text block
    ldr $rounds,[$key1,#240]        // load key schedule...
    vld1.8  {$dat},[$key1],#16
    sub     $rounds,$rounds,#2
    vld1.8  {$dat1},[$key1],#16     // load key schedule...
.Loop_final_enc:
    aese    $tmpin,$dat0
    aesmc   $tmpin,$tmpin
    vld1.32 {$dat0},[$key1],#16
    subs    $rounds,$rounds,#2
    aese    $tmpin,$dat1
    aesmc   $tmpin,$tmpin
    vld1.32 {$dat1},[$key1],#16
    b.gt    .Loop_final_enc

    aese    $tmpin,$dat0
    aesmc   $tmpin,$tmpin
    vld1.32 {$dat0},[$key1]
    aese    $tmpin,$dat1
    veor    $tmpin,$tmpin,$dat0
    veor    $tmpin,$tmpin,$iv0
    vst1.8  {$tmpin},[$out]

.Lxts_abort:
    ldp     $tailcnt,$midnumx,[sp,#48]
    ldp     $ivd10,$ivd20,[sp,#32]
    ldp     $ivd30,$ivd40,[sp,#16]
    ldp     $constnumx,$tmpinp,[sp],#64
.Lxts_enc_final_abort:
    ret
.size   ${prefix}_xts_encrypt,.-${prefix}_xts_encrypt
___

}}}
{{{
my ($inp,$out,$len,$key1,$key2,$ivp)=map("x$_",(0..5));
my ($rounds0,$rounds,$key_,$step,$ivl,$ivh)=("w5","w6","x7","x8","x9","x10");
my ($tmpoutp,$loutp,$l2outp,$tmpinp)=("x13","w14","w15","x20");
my ($tailcnt,$midnum,$midnumx,$constnum,$constnumx)=("x21","w22","x22","w19","x19");
my ($xoffset,$tmpmx,$tmpmw)=("x6","x11","w11");
my ($dat0,$dat1,$in0,$in1,$tmp0,$tmp1,$tmp2,$rndlast)=map("q$_",(0..7));
my ($iv0,$iv1,$iv2,$iv3,$iv4,$tmpin)=("v6.16b","v8.16b","v9.16b","v10.16b","v11.16b","v26.16b");
my ($ivd00,$ivd01,$ivd20,$ivd21)=("d6","v6.d[1]","d9","v9.d[1]");
my ($ivd10,$ivd11,$ivd30,$ivd31,$ivd40,$ivd41)=("d8","v8.d[1]","d10","v10.d[1]","d11","v11.d[1]");

my ($dat,$tmp,$rndzero_n_last)=($dat0,$tmp0,$tmp1);

# q7                last round key
# q10-q15, q7       Last 7 round keys
# q8-q9             preloaded round keys except last 7 keys for big size
# q20, q21, q8-q9   preloaded round keys except last 7 keys for only 16 byte

{
my ($dat2,$in2,$tmp2)=map("q$_",(10,11,9));

my ($dat3,$in3,$tmp3);  # used only in 64-bit mode
my ($dat4,$in4,$tmp4);
if ($flavour =~ /64/) {
    ($dat2,$dat3,$dat4,$in2,$in3,$in4,$tmp3,$tmp4)=map("q$_",(16..23));
}

$code.=<<___    if ($flavour =~ /64/);
.globl  ${prefix}_xts_decrypt
.type   ${prefix}_xts_decrypt,%function
.align  5
${prefix}_xts_decrypt:
___
$code.=<<___    if ($flavour =~ /64/);
    AARCH64_VALID_CALL_TARGET
    cmp $len,#16
    // Original input data size bigger than 16, jump to big size processing.
    b.ne    .Lxts_dec_big_size
    // Encrypt the iv with key2, as the first XEX iv.
    ldr     $rounds,[$key2,#240]
    vld1.8  {$dat},[$key2],#16
    vld1.8  {$iv0},[$ivp]
    sub     $rounds,$rounds,#2
    vld1.8  {$dat1},[$key2],#16

.Loop_dec_small_iv_enc:
    aese    $iv0,$dat
    aesmc   $iv0,$iv0
    vld1.32 {$dat},[$key2],#16
    subs    $rounds,$rounds,#2
    aese    $iv0,$dat1
    aesmc   $iv0,$iv0
    vld1.32 {$dat1},[$key2],#16
    b.gt    .Loop_dec_small_iv_enc

    aese    $iv0,$dat
    aesmc   $iv0,$iv0
    vld1.32 {$dat},[$key2]
    aese    $iv0,$dat1
    veor    $iv0,$iv0,$dat

    vld1.8  {$dat0},[$inp]
    veor    $dat0,$iv0,$dat0

    ldr $rounds,[$key1,#240]
    vld1.32 {q20-q21},[$key1],#32       // load key schedule...

    aesd    $dat0,q20
    aesimc  $dat0,$dat0
    vld1.32 {q8-q9},[$key1],#32         // load key schedule...
    aesd    $dat0,q21
    aesimc  $dat0,$dat0
    subs    $rounds,$rounds,#10         // bias
    b.eq    .Lxts_128_dec
.Lxts_dec_round_loop:
    aesd    $dat0,q8
    aesimc  $dat0,$dat0
    vld1.32 {q8},[$key1],#16            // load key schedule...
    aesd    $dat0,q9
    aesimc  $dat0,$dat0
    vld1.32 {q9},[$key1],#16            // load key schedule...
    subs    $rounds,$rounds,#2          // bias
    b.gt    .Lxts_dec_round_loop
.Lxts_128_dec:
    vld1.32 {q10-q11},[$key1],#32       // load key schedule...
    aesd    $dat0,q8
    aesimc  $dat0,$dat0
    aesd    $dat0,q9
    aesimc  $dat0,$dat0
    vld1.32 {q12-q13},[$key1],#32       // load key schedule...
    aesd    $dat0,q10
    aesimc  $dat0,$dat0
    aesd    $dat0,q11
    aesimc  $dat0,$dat0
    vld1.32 {q14-q15},[$key1],#32       // load key schedule...
    aesd    $dat0,q12
    aesimc  $dat0,$dat0
    aesd    $dat0,q13
    aesimc  $dat0,$dat0
    vld1.32 {$rndlast},[$key1]
    aesd    $dat0,q14
    aesimc  $dat0,$dat0
    aesd    $dat0,q15
    veor    $dat0,$dat0,$rndlast
    veor    $dat0,$iv0,$dat0
    vst1.8  {$dat0},[$out]
    b       .Lxts_dec_final_abort
.Lxts_dec_big_size:
___
$code.=<<___    if ($flavour =~ /64/);
    stp     $constnumx,$tmpinp,[sp,#-64]!
    stp     $tailcnt,$midnumx,[sp,#48]
    stp     $ivd10,$ivd20,[sp,#32]
    stp     $ivd30,$ivd40,[sp,#16]

    and     $tailcnt,$len,#0xf
    and     $len,$len,#-16
    subs    $len,$len,#16
    mov     $step,#16
    b.lo    .Lxts_dec_abort

    // Encrypt the iv with key2, as the first XEX iv
    ldr     $rounds,[$key2,#240]
    vld1.8  {$dat},[$key2],#16
    vld1.8  {$iv0},[$ivp]
    sub     $rounds,$rounds,#2
    vld1.8  {$dat1},[$key2],#16

.Loop_dec_iv_enc:
    aese    $iv0,$dat
    aesmc   $iv0,$iv0
    vld1.32 {$dat},[$key2],#16
    subs    $rounds,$rounds,#2
    aese    $iv0,$dat1
    aesmc   $iv0,$iv0
    vld1.32 {$dat1},[$key2],#16
    b.gt    .Loop_dec_iv_enc

    aese    $iv0,$dat
    aesmc   $iv0,$iv0
    vld1.32 {$dat},[$key2]
    aese    $iv0,$dat1
    veor    $iv0,$iv0,$dat

    // The iv for second block
    // $ivl- iv(low), $ivh - iv(high)
    // the five ivs stored into, $iv0,$iv1,$iv2,$iv3,$iv4
    fmov    $ivl,$ivd00
    fmov    $ivh,$ivd01
    mov     $constnum,#0x87
    extr    $midnumx,$ivh,$ivh,#32
    extr    $ivh,$ivh,$ivl,#63
    and     $tmpmw,$constnum,$midnum,asr #31
    eor     $ivl,$tmpmx,$ivl,lsl #1
    fmov    $ivd10,$ivl
    fmov    $ivd11,$ivh

    ldr $rounds0,[$key1,#240]       // load rounds number

    // The iv for third block
    extr    $midnumx,$ivh,$ivh,#32
    extr    $ivh,$ivh,$ivl,#63
    and     $tmpmw,$constnum,$midnum,asr #31
    eor     $ivl,$tmpmx,$ivl,lsl #1
    fmov    $ivd20,$ivl
    fmov    $ivd21,$ivh

    vld1.32 {q8-q9},[$key1]         // load key schedule...
    sub     $rounds0,$rounds0,#6
    add     $key_,$key1,$ivp,lsl#4  // pointer to last 7 round keys
    sub     $rounds0,$rounds0,#2
    vld1.32 {q10-q11},[$key_],#32   // load key schedule...
    vld1.32 {q12-q13},[$key_],#32
    vld1.32 {q14-q15},[$key_],#32
    vld1.32 {$rndlast},[$key_]

    // The iv for fourth block
    extr    $midnumx,$ivh,$ivh,#32
    extr    $ivh,$ivh,$ivl,#63
    and     $tmpmw,$constnum,$midnum,asr #31
    eor     $ivl,$tmpmx,$ivl,lsl #1
    fmov    $ivd30,$ivl
    fmov    $ivd31,$ivh

    add     $key_,$key1,#32
    mov     $rounds,$rounds0
    b       .Lxts_dec

    // Decryption
.align  5
.Lxts_dec:
    tst     $tailcnt,#0xf
    b.eq    .Lxts_dec_begin
    subs    $len,$len,#16
    csel    $step,xzr,$step,eq
    vld1.8  {$dat},[$inp],#16
    b.lo    .Lxts_done
    sub     $inp,$inp,#16
.Lxts_dec_begin:
    vld1.8  {$dat},[$inp],$step
    subs    $len,$len,#32           // bias
    add     $rounds,$rounds0,#2
    vorr    $in1,$dat,$dat
    vorr    $dat1,$dat,$dat
    vorr    $in3,$dat,$dat
    vld1.8  {$dat2},[$inp],#16
    vorr    $in2,$dat2,$dat2
    vorr    $in4,$dat2,$dat2
    b.lo    .Lxts_inner_dec_tail
    veor    $dat,$dat,$iv0          // before decryt, xor with iv
    veor    $dat2,$dat2,$iv1

    vorr    $dat1,$dat2,$dat2
    vld1.8  {$dat2},[$inp],#16
    vorr    $in0,$dat,$dat
    vorr    $in1,$dat1,$dat1
    veor    $in2,$dat2,$iv2         // third block xox with third iv
    veor    $dat2,$dat2,$iv2
    cmp     $len,#32
    b.lo    .Lxts_outer_dec_tail

    vld1.8  {$dat3},[$inp],#16

    // The iv for fifth block
    extr    $midnumx,$ivh,$ivh,#32
    extr    $ivh,$ivh,$ivl,#63
    and     $tmpmw,$constnum,$midnum,asr #31
    eor     $ivl,$tmpmx,$ivl,lsl #1
    fmov    $ivd40,$ivl
    fmov    $ivd41,$ivh

    vld1.8  {$dat4},[$inp],#16
    veor    $dat3,$dat3,$iv3        // the fourth block
    veor    $dat4,$dat4,$iv4
    sub     $len,$len,#32           // bias
    mov     $rounds,$rounds0
    b       .Loop5x_xts_dec

.align  4
.Loop5x_xts_dec:
    aesd    $dat0,q8
    aesimc  $dat0,$dat0
    aesd    $dat1,q8
    aesimc  $dat1,$dat1
    aesd    $dat2,q8
    aesimc  $dat2,$dat2
    aesd    $dat3,q8
    aesimc  $dat3,$dat3
    aesd    $dat4,q8
    aesimc  $dat4,$dat4
    vld1.32 {q8},[$key_],#16        // load key schedule...
    subs    $rounds,$rounds,#2
    aesd    $dat0,q9
    aesimc  $dat0,$dat0
    aesd    $dat1,q9
    aesimc  $dat1,$dat1
    aesd    $dat2,q9
    aesimc  $dat2,$dat2
    aesd    $dat3,q9
    aesimc  $dat3,$dat3
    aesd    $dat4,q9
    aesimc  $dat4,$dat4
    vld1.32 {q9},[$key_],#16        // load key schedule...
    b.gt    .Loop5x_xts_dec

    aesd    $dat0,q8
    aesimc  $dat0,$dat0
    aesd    $dat1,q8
    aesimc  $dat1,$dat1
    aesd    $dat2,q8
    aesimc  $dat2,$dat2
    aesd    $dat3,q8
    aesimc  $dat3,$dat3
    aesd    $dat4,q8
    aesimc  $dat4,$dat4
    subs    $len,$len,#0x50         // because .Lxts_dec_tail4x

    aesd    $dat0,q9
    aesimc  $dat0,$dat
    aesd    $dat1,q9
    aesimc  $dat1,$dat1
    aesd    $dat2,q9
    aesimc  $dat2,$dat2
    aesd    $dat3,q9
    aesimc  $dat3,$dat3
    aesd    $dat4,q9
    aesimc  $dat4,$dat4
    csel    $xoffset,xzr,$len,gt    // borrow x6, w6, "gt" is not typo
    mov     $key_,$key1

    aesd    $dat0,q10
    aesimc  $dat0,$dat0
    aesd    $dat1,q10
    aesimc  $dat1,$dat1
    aesd    $dat2,q10
    aesimc  $dat2,$dat2
    aesd    $dat3,q10
    aesimc  $dat3,$dat3
    aesd    $dat4,q10
    aesimc  $dat4,$dat4
    add     $inp,$inp,$xoffset  // x0 is adjusted in such way that
                                // at exit from the loop v1.16b-v26.16b
                                // are loaded with last "words"
    add $xoffset,$len,#0x60         // because .Lxts_dec_tail4x

    aesd    $dat0,q11
    aesimc  $dat0,$dat0
    aesd    $dat1,q11
    aesimc  $dat1,$dat1
    aesd    $dat2,q11
    aesimc  $dat2,$dat2
    aesd    $dat3,q11
    aesimc  $dat3,$dat3
    aesd    $dat4,q11
    aesimc  $dat4,$dat4

    aesd    $dat0,q12
    aesimc  $dat0,$dat0
    aesd    $dat1,q12
    aesimc  $dat1,$dat1
    aesd    $dat2,q12
    aesimc  $dat2,$dat2
    aesd    $dat3,q12
    aesimc  $dat3,$dat3
    aesd    $dat4,q12
    aesimc  $dat4,$dat4

    aesd    $dat0,q13
    aesimc  $dat0,$dat0
    aesd    $dat1,q13
    aesimc  $dat1,$dat1
    aesd    $dat2,q13
    aesimc  $dat2,$dat2
    aesd    $dat3,q13
    aesimc  $dat3,$dat3
    aesd    $dat4,q13
    aesimc  $dat4,$dat4

    aesd    $dat0,q14
    aesimc  $dat0,$dat0
    aesd    $dat1,q14
    aesimc  $dat1,$dat1
    aesd    $dat2,q14
    aesimc  $dat2,$dat2
    aesd    $dat3,q14
    aesimc  $dat3,$dat3
    aesd    $dat4,q14
    aesimc  $dat4,$dat4

    veor    $tmp0,$rndlast,$iv0
    aesd    $dat0,q15
    // The iv for first block of next iteration.
    extr    $midnumx,$ivh,$ivh,#32
    extr    $ivh,$ivh,$ivl,#63
    and     $tmpmw,$constnum,$midnum,asr #31
    eor     $ivl,$tmpmx,$ivl,lsl #1
    fmov    $ivd00,$ivl
    fmov    $ivd01,$ivh
    veor    $tmp1,$rndlast,$iv1
    vld1.8  {$in0},[$inp],#16
    aesd    $dat1,q15
    // The iv for second block
    extr    $midnumx,$ivh,$ivh,#32
    extr    $ivh,$ivh,$ivl,#63
    and     $tmpmw,$constnum,$midnum,asr #31
    eor     $ivl,$tmpmx,$ivl,lsl #1
    fmov    $ivd10,$ivl
    fmov    $ivd11,$ivh
    veor    $tmp2,$rndlast,$iv2
    vld1.8  {$in1},[$inp],#16
    aesd    $dat2,q15
    // The iv for third block
    extr    $midnumx,$ivh,$ivh,#32
    extr    $ivh,$ivh,$ivl,#63
    and     $tmpmw,$constnum,$midnum,asr #31
    eor     $ivl,$tmpmx,$ivl,lsl #1
    fmov    $ivd20,$ivl
    fmov    $ivd21,$ivh
    veor    $tmp3,$rndlast,$iv3
    vld1.8  {$in2},[$inp],#16
    aesd    $dat3,q15
    // The iv for fourth block
    extr    $midnumx,$ivh,$ivh,#32
    extr    $ivh,$ivh,$ivl,#63
    and     $tmpmw,$constnum,$midnum,asr #31
    eor     $ivl,$tmpmx,$ivl,lsl #1
    fmov    $ivd30,$ivl
    fmov    $ivd31,$ivh
    veor    $tmp4,$rndlast,$iv4
    vld1.8  {$in3},[$inp],#16
    aesd    $dat4,q15

    // The iv for fifth block
    extr    $midnumx,$ivh,$ivh,#32
    extr    $ivh,$ivh,$ivl,#63
    and     $tmpmw,$constnum,$midnum,asr #31
    eor     $ivl,$tmpmx,$ivl,lsl #1
    fmov    $ivd40,$ivl
    fmov    $ivd41,$ivh

    vld1.8  {$in4},[$inp],#16
    cbz     $xoffset,.Lxts_dec_tail4x
    vld1.32 {q8},[$key_],#16        // re-pre-load rndkey[0]
    veor    $tmp0,$tmp0,$dat0
    veor    $dat0,$in0,$iv0
    veor    $tmp1,$tmp1,$dat1
    veor    $dat1,$in1,$iv1
    veor    $tmp2,$tmp2,$dat2
    veor    $dat2,$in2,$iv2
    veor    $tmp3,$tmp3,$dat3
    veor    $dat3,$in3,$iv3
    veor    $tmp4,$tmp4,$dat4
    vst1.8  {$tmp0},[$out],#16
    veor    $dat4,$in4,$iv4
    vst1.8  {$tmp1},[$out],#16
    mov     $rounds,$rounds0
    vst1.8  {$tmp2},[$out],#16
    vld1.32 {q9},[$key_],#16        // re-pre-load rndkey[1]
    vst1.8  {$tmp3},[$out],#16
    vst1.8  {$tmp4},[$out],#16
    b.hs    .Loop5x_xts_dec

    cmn     $len,#0x10
    b.ne    .Loop5x_dec_after
    // If x2($len) equal to -0x10, the left blocks is 4.
    // After specially processing, utilize the five blocks processing again.
    // It will use the following IVs: $iv0,$iv0,$iv1,$iv2,$iv3.
    vorr    $iv4,$iv3,$iv3
    vorr    $iv3,$iv2,$iv2
    vorr    $iv2,$iv1,$iv1
    vorr    $iv1,$iv0,$iv0
    fmov    $ivl,$ivd40
    fmov    $ivh,$ivd41
    veor    $dat0,$iv0,$in0
    veor    $dat1,$iv1,$in1
    veor    $dat2,$in2,$iv2
    veor    $dat3,$in3,$iv3
    veor    $dat4,$in4,$iv4
    b.eq    .Loop5x_xts_dec

.Loop5x_dec_after:
    add     $len,$len,#0x50
    cbz     $len,.Lxts_done

    add     $rounds,$rounds0,#2
    subs    $len,$len,#0x30
    b.lo    .Lxts_inner_dec_tail

    veor    $dat0,$iv0,$in2
    veor    $dat1,$iv1,$in3
    veor    $dat2,$in4,$iv2
    b       .Lxts_outer_dec_tail

.align  4
.Lxts_dec_tail4x:
    add     $inp,$inp,#16
    tst     $tailcnt,#0xf
    veor    $tmp1,$dat1,$tmp0
    vst1.8  {$tmp1},[$out],#16
    veor    $tmp2,$dat2,$tmp2
    vst1.8  {$tmp2},[$out],#16
    veor    $tmp3,$dat3,$tmp3
    veor    $tmp4,$dat4,$tmp4
    vst1.8  {$tmp3-$tmp4},[$out],#32

    b.eq    .Lxts_dec_abort
    vld1.32 {$dat0},[$inp],#16
    b       .Lxts_done
.align  4
.Lxts_outer_dec_tail:
    aesd    $dat0,q8
    aesimc  $dat0,$dat0
    aesd    $dat1,q8
    aesimc  $dat1,$dat1
    aesd    $dat2,q8
    aesimc  $dat2,$dat2
    vld1.32 {q8},[$key_],#16
    subs    $rounds,$rounds,#2
    aesd    $dat0,q9
    aesimc  $dat0,$dat0
    aesd    $dat1,q9
    aesimc  $dat1,$dat1
    aesd    $dat2,q9
    aesimc  $dat2,$dat2
    vld1.32 {q9},[$key_],#16
    b.gt    .Lxts_outer_dec_tail

    aesd    $dat0,q8
    aesimc  $dat0,$dat0
    aesd    $dat1,q8
    aesimc  $dat1,$dat1
    aesd    $dat2,q8
    aesimc  $dat2,$dat2
    veor    $tmp0,$iv0,$rndlast
    subs    $len,$len,#0x30
    // The iv for first block
    fmov    $ivl,$ivd20
    fmov    $ivh,$ivd21
    mov     $constnum,#0x87
    extr    $midnumx,$ivh,$ivh,#32
    extr    $ivh,$ivh,$ivl,#63
    and     $tmpmw,$constnum,$midnum,asr #31
    eor     $ivl,$tmpmx,$ivl,lsl #1
    fmov    $ivd00,$ivl
    fmov    $ivd01,$ivh
    veor    $tmp1,$iv1,$rndlast
    csel    $xoffset,$len,$xoffset,lo   // x6, w6, is zero at this point
    aesd    $dat0,q9
    aesimc  $dat0,$dat0
    aesd    $dat1,q9
    aesimc  $dat1,$dat1
    aesd    $dat2,q9
    aesimc  $dat2,$dat2
    veor    $tmp2,$iv2,$rndlast
    // The iv for second block
    extr    $midnumx,$ivh,$ivh,#32
    extr    $ivh,$ivh,$ivl,#63
    and     $tmpmw,$constnum,$midnum,asr #31
    eor     $ivl,$tmpmx,$ivl,lsl #1
    fmov    $ivd10,$ivl
    fmov    $ivd11,$ivh

    add     $xoffset,$xoffset,#0x20
    add     $inp,$inp,$xoffset          // $inp is adjusted to the last data

    mov     $key_,$key1

    // The iv for third block
    extr    $midnumx,$ivh,$ivh,#32
    extr    $ivh,$ivh,$ivl,#63
    and     $tmpmw,$constnum,$midnum,asr #31
    eor     $ivl,$tmpmx,$ivl,lsl #1
    fmov    $ivd20,$ivl
    fmov    $ivd21,$ivh

    aesd    $dat0,q12
    aesimc  $dat0,$dat0
    aesd    $dat1,q12
    aesimc  $dat1,$dat1
    aesd    $dat2,q12
    aesimc  $dat2,$dat2
    aesd    $dat0,q13
    aesimc  $dat0,$dat0
    aesd    $dat1,q13
    aesimc  $dat1,$dat1
    aesd    $dat2,q13
    aesimc  $dat2,$dat2
    aesd    $dat0,q14
    aesimc  $dat0,$dat0
    aesd    $dat1,q14
    aesimc  $dat1,$dat1
    aesd    $dat2,q14
    aesimc  $dat2,$dat2
    vld1.8  {$in2},[$inp],#16
    aesd    $dat0,q15
    aesd    $dat1,q15
    aesd    $dat2,q15
    vld1.32 {q8},[$key_],#16        // re-pre-load rndkey[0]
    add     $rounds,$rounds0,#2
    veor    $tmp0,$tmp0,$dat0
    veor    $tmp1,$tmp1,$dat1
    veor    $dat2,$dat2,$tmp2
    vld1.32 {q9},[$key_],#16        // re-pre-load rndkey[1]
    vst1.8  {$tmp0},[$out],#16
    vst1.8  {$tmp1},[$out],#16
    vst1.8  {$dat2},[$out],#16

    cmn     $len,#0x30
    add     $len,$len,#0x30
    b.eq    .Lxts_done
    sub     $len,$len,#0x30
    vorr    $in3,$in1,$in1
    vorr    $in4,$in2,$in2
    nop

.Lxts_inner_dec_tail:
    // $len == -0x10 means two blocks left.
    cmn     $len,#0x10
    veor    $dat1,$in3,$iv0
    veor    $dat2,$in4,$iv1
    b.eq    .Lxts_dec_tail_loop
    veor    $dat2,$in4,$iv0
.Lxts_dec_tail_loop:
    aesd    $dat1,q8
    aesimc  $dat1,$dat1
    aesd    $dat2,q8
    aesimc  $dat2,$dat2
    vld1.32 {q8},[$key_],#16
    subs    $rounds,$rounds,#2
    aesd    $dat1,q9
    aesimc  $dat1,$dat1
    aesd    $dat2,q9
    aesimc  $dat2,$dat2
    vld1.32 {q9},[$key_],#16
    b.gt    .Lxts_dec_tail_loop

    aesd    $dat1,q8
    aesimc  $dat1,$dat1
    aesd    $dat2,q8
    aesimc  $dat2,$dat2
    aesd    $dat1,q9
    aesimc  $dat1,$dat1
    aesd    $dat2,q9
    aesimc  $dat2,$dat2
    aesd    $dat1,q12
    aesimc  $dat1,$dat1
    aesd    $dat2,q12
    aesimc  $dat2,$dat2
    cmn     $len,#0x20
    aesd    $dat1,q13
    aesimc  $dat1,$dat1
    aesd    $dat2,q13
    aesimc  $dat2,$dat2
    veor    $tmp1,$iv0,$rndlast
    aesd    $dat1,q14
    aesimc  $dat1,$dat1
    aesd    $dat2,q14
    aesimc  $dat2,$dat2
    veor    $tmp2,$iv1,$rndlast
    aesd    $dat1,q15
    aesd    $dat2,q15
    b.eq    .Lxts_dec_one
    veor    $tmp1,$tmp1,$dat1
    veor    $tmp2,$tmp2,$dat2
    vorr    $iv0,$iv2,$iv2
    vorr    $iv1,$iv3,$iv3
    vst1.8  {$tmp1},[$out],#16
    vst1.8  {$tmp2},[$out],#16
    add     $len,$len,#16
    b       .Lxts_done

.Lxts_dec_one:
    veor    $tmp1,$tmp1,$dat2
    vorr    $iv0,$iv1,$iv1
    vorr    $iv1,$iv2,$iv2
    vst1.8  {$tmp1},[$out],#16
    add     $len,$len,#32

.Lxts_done:
    tst $tailcnt,#0xf
    b.eq    .Lxts_dec_abort
    // Processing the last two blocks with cipher stealing.
    mov     x7,x3
    cbnz    x2,.Lxts_dec_1st_done
    vld1.32 {$dat0},[$inp],#16

    // Decrypt the last secod block to get the last plain text block
.Lxts_dec_1st_done:
    eor     $tmpin,$dat0,$iv1
    ldr     $rounds,[$key1,#240]
    vld1.32 {$dat0},[$key1],#16
    sub     $rounds,$rounds,#2
    vld1.32 {$dat1},[$key1],#16
.Loop_final_2nd_dec:
    aesd    $tmpin,$dat0
    aesimc  $tmpin,$tmpin
    vld1.32 {$dat0},[$key1],#16     // load key schedule...
    subs    $rounds,$rounds,#2
    aesd    $tmpin,$dat1
    aesimc  $tmpin,$tmpin
    vld1.32 {$dat1},[$key1],#16     // load key schedule...
    b.gt    .Loop_final_2nd_dec

    aesd    $tmpin,$dat0
    aesimc  $tmpin,$tmpin
    vld1.32 {$dat0},[$key1]
    aesd    $tmpin,$dat1
    veor    $tmpin,$tmpin,$dat0
    veor    $tmpin,$tmpin,$iv1
    vst1.8  {$tmpin},[$out]

    mov     $tmpinp,$inp
    add     $tmpoutp,$out,#16

    // Composite the tailcnt "16 byte not aligned block" into the last second plain blocks
    // to get the last encrypted block.
.composite_dec_loop:
    subs    $tailcnt,$tailcnt,#1
    ldrb    $l2outp,[$out,$tailcnt]
    ldrb    $loutp,[$tmpinp,$tailcnt]
    strb    $l2outp,[$tmpoutp,$tailcnt]
    strb    $loutp,[$out,$tailcnt]
    b.gt    .composite_dec_loop
.Lxts_dec_load_done:
    vld1.8  {$tmpin},[$out]
    veor    $tmpin,$tmpin,$iv0

    // Decrypt the composite block to get the last second plain text block
    ldr     $rounds,[$key_,#240]
    vld1.8  {$dat},[$key_],#16
    sub     $rounds,$rounds,#2
    vld1.8  {$dat1},[$key_],#16
.Loop_final_dec:
    aesd    $tmpin,$dat0
    aesimc  $tmpin,$tmpin
    vld1.32 {$dat0},[$key_],#16     // load key schedule...
    subs    $rounds,$rounds,#2
    aesd    $tmpin,$dat1
    aesimc  $tmpin,$tmpin
    vld1.32 {$dat1},[$key_],#16     // load key schedule...
    b.gt    .Loop_final_dec

    aesd    $tmpin,$dat0
    aesimc  $tmpin,$tmpin
    vld1.32 {$dat0},[$key_]
    aesd    $tmpin,$dat1
    veor    $tmpin,$tmpin,$dat0
    veor    $tmpin,$tmpin,$iv0
    vst1.8  {$tmpin},[$out]

.Lxts_dec_abort:
    ldp     $tailcnt,$midnumx,[sp,#48]
    ldp     $ivd10,$ivd20,[sp,#32]
    ldp     $ivd30,$ivd40,[sp,#16]
    ldp     $constnumx,$tmpinp,[sp],#64

.Lxts_dec_final_abort:
    ret
.size   ${prefix}_xts_decrypt,.-${prefix}_xts_decrypt
___
}
}}}
$code.=<<___;
#endif
___
########################################
if ($flavour =~ /64/) {			######## 64-bit code
    my %opcode = (
	"aesd"	=>	0x4e285800,	"aese"	=>	0x4e284800,
	"aesimc"=>	0x4e287800,	"aesmc"	=>	0x4e286800	);

    local *unaes = sub {
	my ($mnemonic,$arg)=@_;

	$arg =~ m/[qv]([0-9]+)[^,]*,\s*[qv]([0-9]+)/o	&&
	sprintf ".inst\t0x%08x\t//%s %s",
			$opcode{$mnemonic}|$1|($2<<5),
			$mnemonic,$arg;
    };

    foreach(split("\n",$code)) {
	s/\`([^\`]*)\`/eval($1)/geo;

	s/\bq([0-9]+)\b/"v".($1<8?$1:$1+8).".16b"/geo;	# old->new registers
	s/@\s/\/\//o;			# old->new style commentary

	#s/[v]?(aes\w+)\s+([qv].*)/unaes($1,$2)/geo	or
	s/cclr\s+([wx])([^,]+),\s*([a-z]+)/csel	$1$2,$1zr,$1$2,$3/o	or
	s/mov\.([a-z]+)\s+([wx][0-9]+),\s*([wx][0-9]+)/csel	$2,$3,$2,$1/o	or
	s/vmov\.i8/movi/o	or	# fix up legacy mnemonics
	s/vext\.8/ext/o		or
	s/vrev32\.8/rev32/o	or
	s/vtst\.8/cmtst/o	or
	s/vshr/ushr/o		or
	s/^(\s+)v/$1/o		or	# strip off v prefix
	s/\bbx\s+lr\b/ret/o;

	# fix up remaining legacy suffixes
	s/\.[ui]?8//o;
	m/\],#8/o and s/\.16b/\.8b/go;
	s/\.[ui]?32//o and s/\.16b/\.4s/go;
	s/\.[ui]?64//o and s/\.16b/\.2d/go;
	s/\.[42]([sd])\[([0-3])\]/\.$1\[$2\]/o;

	# Switch preprocessor checks to aarch64 versions.
	s/__ARME([BL])__/__AARCH64E$1__/go;

	print $_,"\n";
    }
} else {				######## 32-bit code
    my %opcode = (
	"aesd"	=>	0xf3b00340,	"aese"	=>	0xf3b00300,
	"aesimc"=>	0xf3b003c0,	"aesmc"	=>	0xf3b00380	);

    local *unaes = sub {
	my ($mnemonic,$arg)=@_;

	if ($arg =~ m/[qv]([0-9]+)[^,]*,\s*[qv]([0-9]+)/o) {
	    my $word = $opcode{$mnemonic}|(($1&7)<<13)|(($1&8)<<19)
					 |(($2&7)<<1) |(($2&8)<<2);
	    # since ARMv7 instructions are always encoded little-endian.
	    # correct solution is to use .inst directive, but older
	    # assemblers don't implement it:-(
	    sprintf ".byte\t0x%02x,0x%02x,0x%02x,0x%02x\t@ %s %s",
			$word&0xff,($word>>8)&0xff,
			($word>>16)&0xff,($word>>24)&0xff,
			$mnemonic,$arg;
	}
    };

    sub unvtbl {
	my $arg=shift;

	$arg =~ m/q([0-9]+),\s*\{q([0-9]+)\},\s*q([0-9]+)/o &&
	sprintf	"vtbl.8	d%d,{q%d},d%d\n\t".
		"vtbl.8	d%d,{q%d},d%d", 2*$1,$2,2*$3, 2*$1+1,$2,2*$3+1;
    }

    sub unvdup32 {
	my $arg=shift;

	$arg =~ m/q([0-9]+),\s*q([0-9]+)\[([0-3])\]/o &&
	sprintf	"vdup.32	q%d,d%d[%d]",$1,2*$2+($3>>1),$3&1;
    }

    sub unvmov32 {
	my $arg=shift;

	$arg =~ m/q([0-9]+)\[([0-3])\],(.*)/o &&
	sprintf	"vmov.32	d%d[%d],%s",2*$1+($2>>1),$2&1,$3;
    }

    foreach(split("\n",$code)) {
	s/\`([^\`]*)\`/eval($1)/geo;

	s/\b[wx]([0-9]+)\b/r$1/go;		# new->old registers
	s/\bv([0-9])\.[12468]+[bsd]\b/q$1/go;	# new->old registers
	s/\/\/\s?/@ /o;				# new->old style commentary

	# fix up remaining new-style suffixes
	s/\{q([0-9]+)\},\s*\[(.+)\],#8/sprintf "{d%d},[$2]!",2*$1/eo	or
	s/\],#[0-9]+/]!/o;

	s/[v]?(aes\w+)\s+([qv].*)/unaes($1,$2)/geo	or
	s/cclr\s+([^,]+),\s*([a-z]+)/mov$2	$1,#0/o	or
	s/vtbl\.8\s+(.*)/unvtbl($1)/geo			or
	s/vdup\.32\s+(.*)/unvdup32($1)/geo		or
	s/vmov\.32\s+(.*)/unvmov32($1)/geo		or
	s/^(\s+)b\./$1b/o				or
	s/^(\s+)mov\./$1mov/o				or
	s/^(\s+)ret/$1bx\tlr/o;

	print $_,"\n";
    }
}

close STDOUT or die "error closing STDOUT: $!";
