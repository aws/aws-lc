// This file is generated from a similarly-named Perl script in the BoringSSL
// source tree. Do not edit by hand.

#include <openssl/asm_base.h>

#if !defined(OPENSSL_NO_ASM) && defined(OPENSSL_X86_64) && defined(__APPLE__)
#ifndef MY_ASSEMBLER_IS_TOO_OLD_FOR_512AVX

.text	














.p2align	5
keccak_1600_permute:

.byte	243,15,30,250
	movl	$24,%r10d
	leaq	iotas_avx512(%rip),%r11

.p2align	5
L$keccak_rnd_loop:







	vmovdqa64	%ymm0,%ymm25
	vpternlogq	$0x96,%ymm5,%ymm10,%ymm25
	vmovdqa64	%ymm1,%ymm26
	vpternlogq	$0x96,%ymm11,%ymm6,%ymm26
	vmovdqa64	%ymm2,%ymm27
	vpternlogq	$0x96,%ymm12,%ymm7,%ymm27

	vmovdqa64	%ymm3,%ymm28
	vpternlogq	$0x96,%ymm13,%ymm8,%ymm28
	vmovdqa64	%ymm4,%ymm29
	vpternlogq	$0x96,%ymm14,%ymm9,%ymm29
	vpternlogq	$0x96,%ymm20,%ymm15,%ymm25

	vpternlogq	$0x96,%ymm21,%ymm16,%ymm26
	vpternlogq	$0x96,%ymm22,%ymm17,%ymm27
	vpternlogq	$0x96,%ymm23,%ymm18,%ymm28






	vprolq	$1,%ymm26,%ymm30
	vprolq	$1,%ymm27,%ymm31
	vpternlogq	$0x96,%ymm24,%ymm19,%ymm29






	vpternlogq	$0x96,%ymm30,%ymm29,%ymm0
	vpternlogq	$0x96,%ymm30,%ymm29,%ymm10
	vpternlogq	$0x96,%ymm30,%ymm29,%ymm20

	vpternlogq	$0x96,%ymm30,%ymm29,%ymm5
	vpternlogq	$0x96,%ymm30,%ymm29,%ymm15
	vprolq	$1,%ymm28,%ymm30

	vpternlogq	$0x96,%ymm31,%ymm25,%ymm6
	vpternlogq	$0x96,%ymm31,%ymm25,%ymm16
	vpternlogq	$0x96,%ymm31,%ymm25,%ymm1

	vpternlogq	$0x96,%ymm31,%ymm25,%ymm11
	vpternlogq	$0x96,%ymm31,%ymm25,%ymm21
	vprolq	$1,%ymm29,%ymm31

	vpbroadcastq	(%r11),%ymm29
	addq	$8,%r11

	vpternlogq	$0x96,%ymm30,%ymm26,%ymm12
	vpternlogq	$0x96,%ymm30,%ymm26,%ymm7
	vpternlogq	$0x96,%ymm30,%ymm26,%ymm22

	vpternlogq	$0x96,%ymm30,%ymm26,%ymm17
	vpternlogq	$0x96,%ymm30,%ymm26,%ymm2
	vprolq	$1,%ymm25,%ymm30















	vpternlogq	$0x96,%ymm31,%ymm27,%ymm3
	vpternlogq	$0x96,%ymm31,%ymm27,%ymm13
	vpternlogq	$0x96,%ymm31,%ymm27,%ymm23

	vprolq	$44,%ymm6,%ymm6
	vpternlogq	$0x96,%ymm31,%ymm27,%ymm18
	vpternlogq	$0x96,%ymm31,%ymm27,%ymm8

	vprolq	$43,%ymm12,%ymm12
	vprolq	$21,%ymm18,%ymm18
	vpternlogq	$0x96,%ymm30,%ymm28,%ymm24

	vprolq	$14,%ymm24,%ymm24
	vprolq	$28,%ymm3,%ymm3
	vpternlogq	$0x96,%ymm30,%ymm28,%ymm9

	vprolq	$20,%ymm9,%ymm9
	vprolq	$3,%ymm10,%ymm10
	vpternlogq	$0x96,%ymm30,%ymm28,%ymm19

	vprolq	$45,%ymm16,%ymm16
	vprolq	$61,%ymm22,%ymm22
	vpternlogq	$0x96,%ymm30,%ymm28,%ymm4

	vprolq	$1,%ymm1,%ymm1
	vprolq	$6,%ymm7,%ymm7
	vpternlogq	$0x96,%ymm30,%ymm28,%ymm14








	vprolq	$25,%ymm13,%ymm13
	vprolq	$8,%ymm19,%ymm19
	vmovdqa64	%ymm0,%ymm30
	vpternlogq	$0xD2,%ymm12,%ymm6,%ymm30

	vprolq	$18,%ymm20,%ymm20
	vprolq	$27,%ymm4,%ymm4
	vpxorq	%ymm29,%ymm30,%ymm30

	vprolq	$36,%ymm5,%ymm5
	vprolq	$10,%ymm11,%ymm11
	vmovdqa64	%ymm6,%ymm31
	vpternlogq	$0xD2,%ymm18,%ymm12,%ymm31

	vprolq	$15,%ymm17,%ymm17
	vprolq	$56,%ymm23,%ymm23
	vpternlogq	$0xD2,%ymm24,%ymm18,%ymm12

	vprolq	$62,%ymm2,%ymm2
	vprolq	$55,%ymm8,%ymm8
	vpternlogq	$0xD2,%ymm0,%ymm24,%ymm18

	vprolq	$39,%ymm14,%ymm14
	vprolq	$41,%ymm15,%ymm15
	vpternlogq	$0xD2,%ymm6,%ymm0,%ymm24
	vmovdqa64	%ymm30,%ymm0
	vmovdqa64	%ymm31,%ymm6

	vprolq	$2,%ymm21,%ymm21
	vmovdqa64	%ymm3,%ymm30
	vpternlogq	$0xD2,%ymm10,%ymm9,%ymm30
	vmovdqa64	%ymm9,%ymm31
	vpternlogq	$0xD2,%ymm16,%ymm10,%ymm31

	vpternlogq	$0xD2,%ymm22,%ymm16,%ymm10
	vpternlogq	$0xD2,%ymm3,%ymm22,%ymm16
	vpternlogq	$0xD2,%ymm9,%ymm3,%ymm22
	vmovdqa64	%ymm30,%ymm3
	vmovdqa64	%ymm31,%ymm9

	vmovdqa64	%ymm1,%ymm30
	vpternlogq	$0xD2,%ymm13,%ymm7,%ymm30
	vmovdqa64	%ymm7,%ymm31
	vpternlogq	$0xD2,%ymm19,%ymm13,%ymm31
	vpternlogq	$0xD2,%ymm20,%ymm19,%ymm13

	vpternlogq	$0xD2,%ymm1,%ymm20,%ymm19
	vpternlogq	$0xD2,%ymm7,%ymm1,%ymm20
	vmovdqa64	%ymm30,%ymm1
	vmovdqa64	%ymm31,%ymm7
	vmovdqa64	%ymm4,%ymm30
	vpternlogq	$0xD2,%ymm11,%ymm5,%ymm30

	vmovdqa64	%ymm5,%ymm31
	vpternlogq	$0xD2,%ymm17,%ymm11,%ymm31
	vpternlogq	$0xD2,%ymm23,%ymm17,%ymm11
	vpternlogq	$0xD2,%ymm4,%ymm23,%ymm17

	vpternlogq	$0xD2,%ymm5,%ymm4,%ymm23
	vmovdqa64	%ymm30,%ymm4
	vmovdqa64	%ymm31,%ymm5
	vmovdqa64	%ymm2,%ymm30
	vpternlogq	$0xD2,%ymm14,%ymm8,%ymm30
	vmovdqa64	%ymm8,%ymm31
	vpternlogq	$0xD2,%ymm15,%ymm14,%ymm31

	vpternlogq	$0xD2,%ymm21,%ymm15,%ymm14
	vpternlogq	$0xD2,%ymm2,%ymm21,%ymm15
	vpternlogq	$0xD2,%ymm8,%ymm2,%ymm21
	vmovdqa64	%ymm30,%ymm2
	vmovdqa64	%ymm31,%ymm8


	vmovdqa64	%ymm3,%ymm30
	vmovdqa64	%ymm18,%ymm3
	vmovdqa64	%ymm17,%ymm18
	vmovdqa64	%ymm11,%ymm17
	vmovdqa64	%ymm7,%ymm11
	vmovdqa64	%ymm10,%ymm7
	vmovdqa64	%ymm1,%ymm10
	vmovdqa64	%ymm6,%ymm1
	vmovdqa64	%ymm9,%ymm6
	vmovdqa64	%ymm22,%ymm9
	vmovdqa64	%ymm14,%ymm22
	vmovdqa64	%ymm20,%ymm14
	vmovdqa64	%ymm2,%ymm20
	vmovdqa64	%ymm12,%ymm2
	vmovdqa64	%ymm13,%ymm12
	vmovdqa64	%ymm19,%ymm13
	vmovdqa64	%ymm23,%ymm19
	vmovdqa64	%ymm15,%ymm23
	vmovdqa64	%ymm4,%ymm15
	vmovdqa64	%ymm24,%ymm4
	vmovdqa64	%ymm21,%ymm24
	vmovdqa64	%ymm8,%ymm21
	vmovdqa64	%ymm16,%ymm8
	vmovdqa64	%ymm5,%ymm16
	vmovdqa64	%ymm30,%ymm5

	decl	%r10d
	jnz	L$keccak_rnd_loop
	.byte	0xf3,0xc3


.globl	_KeccakF1600_avx512vl
.private_extern _KeccakF1600_avx512vl

.p2align	5
_KeccakF1600_avx512vl:

.byte	243,15,30,250
	vmovq	0(%rdi),%xmm0
	vmovq	8(%rdi),%xmm1
	vmovq	16(%rdi),%xmm2
	vmovq	24(%rdi),%xmm3
	vmovq	32(%rdi),%xmm4
	vmovq	40(%rdi),%xmm5
	vmovq	48(%rdi),%xmm6
	vmovq	56(%rdi),%xmm7
	vmovq	64(%rdi),%xmm8
	vmovq	72(%rdi),%xmm9
	vmovq	80(%rdi),%xmm10
	vmovq	88(%rdi),%xmm11
	vmovq	96(%rdi),%xmm12
	vmovq	104(%rdi),%xmm13
	vmovq	112(%rdi),%xmm14
	vmovq	120(%rdi),%xmm15
	vmovq	128(%rdi),%xmm16
	vmovq	136(%rdi),%xmm17
	vmovq	144(%rdi),%xmm18
	vmovq	152(%rdi),%xmm19
	vmovq	160(%rdi),%xmm20
	vmovq	168(%rdi),%xmm21
	vmovq	176(%rdi),%xmm22
	vmovq	184(%rdi),%xmm23
	vmovq	192(%rdi),%xmm24

	call	keccak_1600_permute

	vmovq	%xmm0,0(%rdi)
	vmovq	%xmm1,8(%rdi)
	vmovq	%xmm2,16(%rdi)
	vmovq	%xmm3,24(%rdi)
	vmovq	%xmm4,32(%rdi)
	vmovq	%xmm5,40(%rdi)
	vmovq	%xmm6,48(%rdi)
	vmovq	%xmm7,56(%rdi)
	vmovq	%xmm8,64(%rdi)
	vmovq	%xmm9,72(%rdi)
	vmovq	%xmm10,80(%rdi)
	vmovq	%xmm11,88(%rdi)
	vmovq	%xmm12,96(%rdi)
	vmovq	%xmm13,104(%rdi)
	vmovq	%xmm14,112(%rdi)
	vmovq	%xmm15,120(%rdi)
	vmovq	%xmm16,128(%rdi)
	vmovq	%xmm17,136(%rdi)
	vmovq	%xmm18,144(%rdi)
	vmovq	%xmm19,152(%rdi)
	vmovq	%xmm20,160(%rdi)
	vmovq	%xmm21,168(%rdi)
	vmovq	%xmm22,176(%rdi)
	vmovq	%xmm23,184(%rdi)
	vmovq	%xmm24,192(%rdi)
	vzeroupper
	.byte	0xf3,0xc3


.globl	_KeccakF1600_x4_avx512vl
.private_extern _KeccakF1600_x4_avx512vl

.p2align	5
_KeccakF1600_x4_avx512vl:

.byte	243,15,30,250
	vmovdqu64	0+0(%rdi),%ymm25
	vmovdqu64	0+200(%rdi),%ymm26
	vmovdqu64	0+400(%rdi),%ymm27
	vmovdqu64	0+600(%rdi),%ymm28
	vpunpcklqdq	%ymm26,%ymm25,%ymm29
	vpunpckhqdq	%ymm26,%ymm25,%ymm30
	vpunpcklqdq	%ymm28,%ymm27,%ymm25
	vpunpckhqdq	%ymm28,%ymm27,%ymm26
	vshufi64x2	$0,%ymm25,%ymm29,%ymm0
	vshufi64x2	$0,%ymm26,%ymm30,%ymm1
	vshufi64x2	$3,%ymm25,%ymm29,%ymm2
	vshufi64x2	$3,%ymm26,%ymm30,%ymm3
	vmovdqu64	32+0(%rdi),%ymm25
	vmovdqu64	32+200(%rdi),%ymm26
	vmovdqu64	32+400(%rdi),%ymm27
	vmovdqu64	32+600(%rdi),%ymm28
	vpunpcklqdq	%ymm26,%ymm25,%ymm29
	vpunpckhqdq	%ymm26,%ymm25,%ymm30
	vpunpcklqdq	%ymm28,%ymm27,%ymm25
	vpunpckhqdq	%ymm28,%ymm27,%ymm26
	vshufi64x2	$0,%ymm25,%ymm29,%ymm4
	vshufi64x2	$0,%ymm26,%ymm30,%ymm5
	vshufi64x2	$3,%ymm25,%ymm29,%ymm6
	vshufi64x2	$3,%ymm26,%ymm30,%ymm7
	vmovdqu64	64+0(%rdi),%ymm25
	vmovdqu64	64+200(%rdi),%ymm26
	vmovdqu64	64+400(%rdi),%ymm27
	vmovdqu64	64+600(%rdi),%ymm28
	vpunpcklqdq	%ymm26,%ymm25,%ymm29
	vpunpckhqdq	%ymm26,%ymm25,%ymm30
	vpunpcklqdq	%ymm28,%ymm27,%ymm25
	vpunpckhqdq	%ymm28,%ymm27,%ymm26
	vshufi64x2	$0,%ymm25,%ymm29,%ymm8
	vshufi64x2	$0,%ymm26,%ymm30,%ymm9
	vshufi64x2	$3,%ymm25,%ymm29,%ymm10
	vshufi64x2	$3,%ymm26,%ymm30,%ymm11
	vmovdqu64	96+0(%rdi),%ymm25
	vmovdqu64	96+200(%rdi),%ymm26
	vmovdqu64	96+400(%rdi),%ymm27
	vmovdqu64	96+600(%rdi),%ymm28
	vpunpcklqdq	%ymm26,%ymm25,%ymm29
	vpunpckhqdq	%ymm26,%ymm25,%ymm30
	vpunpcklqdq	%ymm28,%ymm27,%ymm25
	vpunpckhqdq	%ymm28,%ymm27,%ymm26
	vshufi64x2	$0,%ymm25,%ymm29,%ymm12
	vshufi64x2	$0,%ymm26,%ymm30,%ymm13
	vshufi64x2	$3,%ymm25,%ymm29,%ymm14
	vshufi64x2	$3,%ymm26,%ymm30,%ymm15
	vmovdqu64	128+0(%rdi),%ymm25
	vmovdqu64	128+200(%rdi),%ymm26
	vmovdqu64	128+400(%rdi),%ymm27
	vmovdqu64	128+600(%rdi),%ymm28
	vpunpcklqdq	%ymm26,%ymm25,%ymm29
	vpunpckhqdq	%ymm26,%ymm25,%ymm30
	vpunpcklqdq	%ymm28,%ymm27,%ymm25
	vpunpckhqdq	%ymm28,%ymm27,%ymm26
	vshufi64x2	$0,%ymm25,%ymm29,%ymm16
	vshufi64x2	$0,%ymm26,%ymm30,%ymm17
	vshufi64x2	$3,%ymm25,%ymm29,%ymm18
	vshufi64x2	$3,%ymm26,%ymm30,%ymm19
	vmovdqu64	160+0(%rdi),%ymm25
	vmovdqu64	160+200(%rdi),%ymm26
	vmovdqu64	160+400(%rdi),%ymm27
	vmovdqu64	160+600(%rdi),%ymm28
	vpunpcklqdq	%ymm26,%ymm25,%ymm29
	vpunpckhqdq	%ymm26,%ymm25,%ymm30
	vpunpcklqdq	%ymm28,%ymm27,%ymm25
	vpunpckhqdq	%ymm28,%ymm27,%ymm26
	vshufi64x2	$0,%ymm25,%ymm29,%ymm20
	vshufi64x2	$0,%ymm26,%ymm30,%ymm21
	vshufi64x2	$3,%ymm25,%ymm29,%ymm22
	vshufi64x2	$3,%ymm26,%ymm30,%ymm23
	vmovq	192+0(%rdi),%xmm24
	vpinsrq	$1,192+200(%rdi),%xmm24,%xmm24
	vmovq	192+400(%rdi),%xmm25
	vpinsrq	$1,192+600(%rdi),%xmm25,%xmm25
	vinserti32x4	$1,%xmm25,%ymm24,%ymm24

	call	keccak_1600_permute

	vpunpcklqdq	%ymm1,%ymm0,%ymm25
	vpunpckhqdq	%ymm1,%ymm0,%ymm26
	vpunpcklqdq	%ymm3,%ymm2,%ymm27
	vpunpckhqdq	%ymm3,%ymm2,%ymm28
	vshufi64x2	$0,%ymm27,%ymm25,%ymm0
	vshufi64x2	$0,%ymm28,%ymm26,%ymm1
	vshufi64x2	$3,%ymm27,%ymm25,%ymm2
	vshufi64x2	$3,%ymm28,%ymm26,%ymm3
	vmovdqu64	%ymm0,0+0(%rdi)
	vmovdqu64	%ymm1,0+200(%rdi)
	vmovdqu64	%ymm2,0+400(%rdi)
	vmovdqu64	%ymm3,0+600(%rdi)
	vpunpcklqdq	%ymm5,%ymm4,%ymm25
	vpunpckhqdq	%ymm5,%ymm4,%ymm26
	vpunpcklqdq	%ymm7,%ymm6,%ymm27
	vpunpckhqdq	%ymm7,%ymm6,%ymm28
	vshufi64x2	$0,%ymm27,%ymm25,%ymm4
	vshufi64x2	$0,%ymm28,%ymm26,%ymm5
	vshufi64x2	$3,%ymm27,%ymm25,%ymm6
	vshufi64x2	$3,%ymm28,%ymm26,%ymm7
	vmovdqu64	%ymm4,32+0(%rdi)
	vmovdqu64	%ymm5,32+200(%rdi)
	vmovdqu64	%ymm6,32+400(%rdi)
	vmovdqu64	%ymm7,32+600(%rdi)
	vpunpcklqdq	%ymm9,%ymm8,%ymm25
	vpunpckhqdq	%ymm9,%ymm8,%ymm26
	vpunpcklqdq	%ymm11,%ymm10,%ymm27
	vpunpckhqdq	%ymm11,%ymm10,%ymm28
	vshufi64x2	$0,%ymm27,%ymm25,%ymm8
	vshufi64x2	$0,%ymm28,%ymm26,%ymm9
	vshufi64x2	$3,%ymm27,%ymm25,%ymm10
	vshufi64x2	$3,%ymm28,%ymm26,%ymm11
	vmovdqu64	%ymm8,64+0(%rdi)
	vmovdqu64	%ymm9,64+200(%rdi)
	vmovdqu64	%ymm10,64+400(%rdi)
	vmovdqu64	%ymm11,64+600(%rdi)
	vpunpcklqdq	%ymm13,%ymm12,%ymm25
	vpunpckhqdq	%ymm13,%ymm12,%ymm26
	vpunpcklqdq	%ymm15,%ymm14,%ymm27
	vpunpckhqdq	%ymm15,%ymm14,%ymm28
	vshufi64x2	$0,%ymm27,%ymm25,%ymm12
	vshufi64x2	$0,%ymm28,%ymm26,%ymm13
	vshufi64x2	$3,%ymm27,%ymm25,%ymm14
	vshufi64x2	$3,%ymm28,%ymm26,%ymm15
	vmovdqu64	%ymm12,96+0(%rdi)
	vmovdqu64	%ymm13,96+200(%rdi)
	vmovdqu64	%ymm14,96+400(%rdi)
	vmovdqu64	%ymm15,96+600(%rdi)
	vpunpcklqdq	%ymm17,%ymm16,%ymm25
	vpunpckhqdq	%ymm17,%ymm16,%ymm26
	vpunpcklqdq	%ymm19,%ymm18,%ymm27
	vpunpckhqdq	%ymm19,%ymm18,%ymm28
	vshufi64x2	$0,%ymm27,%ymm25,%ymm16
	vshufi64x2	$0,%ymm28,%ymm26,%ymm17
	vshufi64x2	$3,%ymm27,%ymm25,%ymm18
	vshufi64x2	$3,%ymm28,%ymm26,%ymm19
	vmovdqu64	%ymm16,128+0(%rdi)
	vmovdqu64	%ymm17,128+200(%rdi)
	vmovdqu64	%ymm18,128+400(%rdi)
	vmovdqu64	%ymm19,128+600(%rdi)
	vpunpcklqdq	%ymm21,%ymm20,%ymm25
	vpunpckhqdq	%ymm21,%ymm20,%ymm26
	vpunpcklqdq	%ymm23,%ymm22,%ymm27
	vpunpckhqdq	%ymm23,%ymm22,%ymm28
	vshufi64x2	$0,%ymm27,%ymm25,%ymm20
	vshufi64x2	$0,%ymm28,%ymm26,%ymm21
	vshufi64x2	$3,%ymm27,%ymm25,%ymm22
	vshufi64x2	$3,%ymm28,%ymm26,%ymm23
	vmovdqu64	%ymm20,160+0(%rdi)
	vmovdqu64	%ymm21,160+200(%rdi)
	vmovdqu64	%ymm22,160+400(%rdi)
	vmovdqu64	%ymm23,160+600(%rdi)
	vextracti32x4	$1,%ymm24,%xmm25
	vmovq	%xmm24,192+0(%rdi)
	vpextrq	$1,%xmm24,192+200(%rdi)
	vmovq	%xmm25,192+400(%rdi)
	vpextrq	$1,%xmm25,192+600(%rdi)
	vzeroupper
	.byte	0xf3,0xc3


.section	__DATA,__const

.p2align	6
iotas_avx512:
.quad	0x0000000000000001, 0x0000000000008082
.quad	0x800000000000808a, 0x8000000080008000
.quad	0x000000000000808b, 0x0000000080000001
.quad	0x8000000080008081, 0x8000000000008009
.quad	0x000000000000008a, 0x0000000000000088
.quad	0x0000000080008009, 0x000000008000000a
.quad	0x000000008000808b, 0x800000000000008b
.quad	0x8000000000008089, 0x8000000000008003
.quad	0x8000000000008002, 0x8000000000000080
.quad	0x000000000000800a, 0x800000008000000a
.quad	0x8000000080008081, 0x8000000000008080
.quad	0x0000000080000001, 0x8000000080008008

#endif

.text	
#endif
