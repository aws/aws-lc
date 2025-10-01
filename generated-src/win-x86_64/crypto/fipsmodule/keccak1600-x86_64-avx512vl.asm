; This file is generated from a similarly-named Perl script in the BoringSSL
; source tree. Do not edit by hand.

%ifidn __OUTPUT_FORMAT__, win64
default	rel
%define XMMWORD
%define YMMWORD
%define ZMMWORD
%define _CET_ENDBR

%include "openssl/boringssl_prefix_symbols_nasm.inc"
%ifndef MY_ASSEMBLER_IS_TOO_OLD_FOR_512AVX

section	.text code align=64















ALIGN	32
keccak_1600_permute:

DB	243,15,30,250
	mov	r10d,24
	lea	r11,[iotas_avx512]

ALIGN	32
$L$keccak_rnd_loop:







	vmovdqa64	ymm25,ymm0
	vpternlogq	ymm25,ymm10,ymm5,0x96
	vmovdqa64	ymm26,ymm1
	vpternlogq	ymm26,ymm6,ymm11,0x96
	vmovdqa64	ymm27,ymm2
	vpternlogq	ymm27,ymm7,ymm12,0x96

	vmovdqa64	ymm28,ymm3
	vpternlogq	ymm28,ymm8,ymm13,0x96
	vmovdqa64	ymm29,ymm4
	vpternlogq	ymm29,ymm9,ymm14,0x96
	vpternlogq	ymm25,ymm15,ymm20,0x96

	vpternlogq	ymm26,ymm16,ymm21,0x96
	vpternlogq	ymm27,ymm17,ymm22,0x96
	vpternlogq	ymm28,ymm18,ymm23,0x96






	vprolq	ymm30,ymm26,1
	vprolq	ymm31,ymm27,1
	vpternlogq	ymm29,ymm19,ymm24,0x96






	vpternlogq	ymm0,ymm29,ymm30,0x96
	vpternlogq	ymm10,ymm29,ymm30,0x96
	vpternlogq	ymm20,ymm29,ymm30,0x96

	vpternlogq	ymm5,ymm29,ymm30,0x96
	vpternlogq	ymm15,ymm29,ymm30,0x96
	vprolq	ymm30,ymm28,1

	vpternlogq	ymm6,ymm25,ymm31,0x96
	vpternlogq	ymm16,ymm25,ymm31,0x96
	vpternlogq	ymm1,ymm25,ymm31,0x96

	vpternlogq	ymm11,ymm25,ymm31,0x96
	vpternlogq	ymm21,ymm25,ymm31,0x96
	vprolq	ymm31,ymm29,1

	vpbroadcastq	ymm29,QWORD[r11]
	add	r11,8

	vpternlogq	ymm12,ymm26,ymm30,0x96
	vpternlogq	ymm7,ymm26,ymm30,0x96
	vpternlogq	ymm22,ymm26,ymm30,0x96

	vpternlogq	ymm17,ymm26,ymm30,0x96
	vpternlogq	ymm2,ymm26,ymm30,0x96
	vprolq	ymm30,ymm25,1















	vpternlogq	ymm3,ymm27,ymm31,0x96
	vpternlogq	ymm13,ymm27,ymm31,0x96
	vpternlogq	ymm23,ymm27,ymm31,0x96

	vprolq	ymm6,ymm6,44
	vpternlogq	ymm18,ymm27,ymm31,0x96
	vpternlogq	ymm8,ymm27,ymm31,0x96

	vprolq	ymm12,ymm12,43
	vprolq	ymm18,ymm18,21
	vpternlogq	ymm24,ymm28,ymm30,0x96

	vprolq	ymm24,ymm24,14
	vprolq	ymm3,ymm3,28
	vpternlogq	ymm9,ymm28,ymm30,0x96

	vprolq	ymm9,ymm9,20
	vprolq	ymm10,ymm10,3
	vpternlogq	ymm19,ymm28,ymm30,0x96

	vprolq	ymm16,ymm16,45
	vprolq	ymm22,ymm22,61
	vpternlogq	ymm4,ymm28,ymm30,0x96

	vprolq	ymm1,ymm1,1
	vprolq	ymm7,ymm7,6
	vpternlogq	ymm14,ymm28,ymm30,0x96








	vprolq	ymm13,ymm13,25
	vprolq	ymm19,ymm19,8
	vmovdqa64	ymm30,ymm0
	vpternlogq	ymm30,ymm6,ymm12,0xD2

	vprolq	ymm20,ymm20,18
	vprolq	ymm4,ymm4,27
	vpxorq	ymm30,ymm30,ymm29

	vprolq	ymm5,ymm5,36
	vprolq	ymm11,ymm11,10
	vmovdqa64	ymm31,ymm6
	vpternlogq	ymm31,ymm12,ymm18,0xD2

	vprolq	ymm17,ymm17,15
	vprolq	ymm23,ymm23,56
	vpternlogq	ymm12,ymm18,ymm24,0xD2

	vprolq	ymm2,ymm2,62
	vprolq	ymm8,ymm8,55
	vpternlogq	ymm18,ymm24,ymm0,0xD2

	vprolq	ymm14,ymm14,39
	vprolq	ymm15,ymm15,41
	vpternlogq	ymm24,ymm0,ymm6,0xD2
	vmovdqa64	ymm0,ymm30
	vmovdqa64	ymm6,ymm31

	vprolq	ymm21,ymm21,2
	vmovdqa64	ymm30,ymm3
	vpternlogq	ymm30,ymm9,ymm10,0xD2
	vmovdqa64	ymm31,ymm9
	vpternlogq	ymm31,ymm10,ymm16,0xD2

	vpternlogq	ymm10,ymm16,ymm22,0xD2
	vpternlogq	ymm16,ymm22,ymm3,0xD2
	vpternlogq	ymm22,ymm3,ymm9,0xD2
	vmovdqa64	ymm3,ymm30
	vmovdqa64	ymm9,ymm31

	vmovdqa64	ymm30,ymm1
	vpternlogq	ymm30,ymm7,ymm13,0xD2
	vmovdqa64	ymm31,ymm7
	vpternlogq	ymm31,ymm13,ymm19,0xD2
	vpternlogq	ymm13,ymm19,ymm20,0xD2

	vpternlogq	ymm19,ymm20,ymm1,0xD2
	vpternlogq	ymm20,ymm1,ymm7,0xD2
	vmovdqa64	ymm1,ymm30
	vmovdqa64	ymm7,ymm31
	vmovdqa64	ymm30,ymm4
	vpternlogq	ymm30,ymm5,ymm11,0xD2

	vmovdqa64	ymm31,ymm5
	vpternlogq	ymm31,ymm11,ymm17,0xD2
	vpternlogq	ymm11,ymm17,ymm23,0xD2
	vpternlogq	ymm17,ymm23,ymm4,0xD2

	vpternlogq	ymm23,ymm4,ymm5,0xD2
	vmovdqa64	ymm4,ymm30
	vmovdqa64	ymm5,ymm31
	vmovdqa64	ymm30,ymm2
	vpternlogq	ymm30,ymm8,ymm14,0xD2
	vmovdqa64	ymm31,ymm8
	vpternlogq	ymm31,ymm14,ymm15,0xD2

	vpternlogq	ymm14,ymm15,ymm21,0xD2
	vpternlogq	ymm15,ymm21,ymm2,0xD2
	vpternlogq	ymm21,ymm2,ymm8,0xD2
	vmovdqa64	ymm2,ymm30
	vmovdqa64	ymm8,ymm31


	vmovdqa64	ymm30,ymm3
	vmovdqa64	ymm3,ymm18
	vmovdqa64	ymm18,ymm17
	vmovdqa64	ymm17,ymm11
	vmovdqa64	ymm11,ymm7
	vmovdqa64	ymm7,ymm10
	vmovdqa64	ymm10,ymm1
	vmovdqa64	ymm1,ymm6
	vmovdqa64	ymm6,ymm9
	vmovdqa64	ymm9,ymm22
	vmovdqa64	ymm22,ymm14
	vmovdqa64	ymm14,ymm20
	vmovdqa64	ymm20,ymm2
	vmovdqa64	ymm2,ymm12
	vmovdqa64	ymm12,ymm13
	vmovdqa64	ymm13,ymm19
	vmovdqa64	ymm19,ymm23
	vmovdqa64	ymm23,ymm15
	vmovdqa64	ymm15,ymm4
	vmovdqa64	ymm4,ymm24
	vmovdqa64	ymm24,ymm21
	vmovdqa64	ymm21,ymm8
	vmovdqa64	ymm8,ymm16
	vmovdqa64	ymm16,ymm5
	vmovdqa64	ymm5,ymm30

	dec	r10d
	jnz	NEAR $L$keccak_rnd_loop
	DB	0F3h,0C3h		;repret


global	KeccakF1600_avx512vl

ALIGN	32
KeccakF1600_avx512vl:
	mov	QWORD[8+rsp],rdi	;WIN64 prologue
	mov	QWORD[16+rsp],rsi
	mov	rax,rsp
$L$SEH_begin_KeccakF1600_avx512vl:
	mov	rdi,rcx



DB	243,15,30,250
	sub	rsp,10*16
	vmovdqu	XMMWORD[rsp],xmm6
	vmovdqu	XMMWORD[16+rsp],xmm7
	vmovdqu	XMMWORD[32+rsp],xmm8
	vmovdqu	XMMWORD[48+rsp],xmm9
	vmovdqu	XMMWORD[64+rsp],xmm10
	vmovdqu	XMMWORD[80+rsp],xmm11
	vmovdqu	XMMWORD[96+rsp],xmm12
	vmovdqu	XMMWORD[112+rsp],xmm13
	vmovdqu	XMMWORD[128+rsp],xmm14
	vmovdqu	XMMWORD[144+rsp],xmm15
	vmovq	xmm0,QWORD[rdi]
	vmovq	xmm1,QWORD[8+rdi]
	vmovq	xmm2,QWORD[16+rdi]
	vmovq	xmm3,QWORD[24+rdi]
	vmovq	xmm4,QWORD[32+rdi]
	vmovq	xmm5,QWORD[40+rdi]
	vmovq	xmm6,QWORD[48+rdi]
	vmovq	xmm7,QWORD[56+rdi]
	vmovq	xmm8,QWORD[64+rdi]
	vmovq	xmm9,QWORD[72+rdi]
	vmovq	xmm10,QWORD[80+rdi]
	vmovq	xmm11,QWORD[88+rdi]
	vmovq	xmm12,QWORD[96+rdi]
	vmovq	xmm13,QWORD[104+rdi]
	vmovq	xmm14,QWORD[112+rdi]
	vmovq	xmm15,QWORD[120+rdi]
	vmovq	xmm16,QWORD[128+rdi]
	vmovq	xmm17,QWORD[136+rdi]
	vmovq	xmm18,QWORD[144+rdi]
	vmovq	xmm19,QWORD[152+rdi]
	vmovq	xmm20,QWORD[160+rdi]
	vmovq	xmm21,QWORD[168+rdi]
	vmovq	xmm22,QWORD[176+rdi]
	vmovq	xmm23,QWORD[184+rdi]
	vmovq	xmm24,QWORD[192+rdi]

	call	keccak_1600_permute

	vmovq	QWORD[rdi],xmm0
	vmovq	QWORD[8+rdi],xmm1
	vmovq	QWORD[16+rdi],xmm2
	vmovq	QWORD[24+rdi],xmm3
	vmovq	QWORD[32+rdi],xmm4
	vmovq	QWORD[40+rdi],xmm5
	vmovq	QWORD[48+rdi],xmm6
	vmovq	QWORD[56+rdi],xmm7
	vmovq	QWORD[64+rdi],xmm8
	vmovq	QWORD[72+rdi],xmm9
	vmovq	QWORD[80+rdi],xmm10
	vmovq	QWORD[88+rdi],xmm11
	vmovq	QWORD[96+rdi],xmm12
	vmovq	QWORD[104+rdi],xmm13
	vmovq	QWORD[112+rdi],xmm14
	vmovq	QWORD[120+rdi],xmm15
	vmovq	QWORD[128+rdi],xmm16
	vmovq	QWORD[136+rdi],xmm17
	vmovq	QWORD[144+rdi],xmm18
	vmovq	QWORD[152+rdi],xmm19
	vmovq	QWORD[160+rdi],xmm20
	vmovq	QWORD[168+rdi],xmm21
	vmovq	QWORD[176+rdi],xmm22
	vmovq	QWORD[184+rdi],xmm23
	vmovq	QWORD[192+rdi],xmm24
	vmovdqu	xmm6,XMMWORD[rsp]
	vmovdqu	xmm7,XMMWORD[16+rsp]
	vmovdqu	xmm8,XMMWORD[32+rsp]
	vmovdqu	xmm9,XMMWORD[48+rsp]
	vmovdqu	xmm10,XMMWORD[64+rsp]
	vmovdqu	xmm11,XMMWORD[80+rsp]
	vmovdqu	xmm12,XMMWORD[96+rsp]
	vmovdqu	xmm13,XMMWORD[112+rsp]
	vmovdqu	xmm14,XMMWORD[128+rsp]
	vmovdqu	xmm15,XMMWORD[144+rsp]
	add	rsp,10*16
	vzeroupper
	mov	rdi,QWORD[8+rsp]	;WIN64 epilogue
	mov	rsi,QWORD[16+rsp]
	DB	0F3h,0C3h		;repret


global	KeccakF1600_x4_avx512vl

ALIGN	32
KeccakF1600_x4_avx512vl:
	mov	QWORD[8+rsp],rdi	;WIN64 prologue
	mov	QWORD[16+rsp],rsi
	mov	rax,rsp
$L$SEH_begin_KeccakF1600_x4_avx512vl:
	mov	rdi,rcx



DB	243,15,30,250
	sub	rsp,10*16
	vmovdqu	XMMWORD[rsp],xmm6
	vmovdqu	XMMWORD[16+rsp],xmm7
	vmovdqu	XMMWORD[32+rsp],xmm8
	vmovdqu	XMMWORD[48+rsp],xmm9
	vmovdqu	XMMWORD[64+rsp],xmm10
	vmovdqu	XMMWORD[80+rsp],xmm11
	vmovdqu	XMMWORD[96+rsp],xmm12
	vmovdqu	XMMWORD[112+rsp],xmm13
	vmovdqu	XMMWORD[128+rsp],xmm14
	vmovdqu	XMMWORD[144+rsp],xmm15
	vmovdqu64	ymm25,YMMWORD[((0+0))+rdi]
	vmovdqu64	ymm26,YMMWORD[((0+200))+rdi]
	vmovdqu64	ymm27,YMMWORD[((0+400))+rdi]
	vmovdqu64	ymm28,YMMWORD[((0+600))+rdi]
	vpunpcklqdq	ymm29,ymm25,ymm26
	vpunpckhqdq	ymm30,ymm25,ymm26
	vpunpcklqdq	ymm25,ymm27,ymm28
	vpunpckhqdq	ymm26,ymm27,ymm28
	vshufi64x2	ymm0,ymm29,ymm25,0
	vshufi64x2	ymm1,ymm30,ymm26,0
	vshufi64x2	ymm2,ymm29,ymm25,3
	vshufi64x2	ymm3,ymm30,ymm26,3
	vmovdqu64	ymm25,YMMWORD[((32+0))+rdi]
	vmovdqu64	ymm26,YMMWORD[((32+200))+rdi]
	vmovdqu64	ymm27,YMMWORD[((32+400))+rdi]
	vmovdqu64	ymm28,YMMWORD[((32+600))+rdi]
	vpunpcklqdq	ymm29,ymm25,ymm26
	vpunpckhqdq	ymm30,ymm25,ymm26
	vpunpcklqdq	ymm25,ymm27,ymm28
	vpunpckhqdq	ymm26,ymm27,ymm28
	vshufi64x2	ymm4,ymm29,ymm25,0
	vshufi64x2	ymm5,ymm30,ymm26,0
	vshufi64x2	ymm6,ymm29,ymm25,3
	vshufi64x2	ymm7,ymm30,ymm26,3
	vmovdqu64	ymm25,YMMWORD[((64+0))+rdi]
	vmovdqu64	ymm26,YMMWORD[((64+200))+rdi]
	vmovdqu64	ymm27,YMMWORD[((64+400))+rdi]
	vmovdqu64	ymm28,YMMWORD[((64+600))+rdi]
	vpunpcklqdq	ymm29,ymm25,ymm26
	vpunpckhqdq	ymm30,ymm25,ymm26
	vpunpcklqdq	ymm25,ymm27,ymm28
	vpunpckhqdq	ymm26,ymm27,ymm28
	vshufi64x2	ymm8,ymm29,ymm25,0
	vshufi64x2	ymm9,ymm30,ymm26,0
	vshufi64x2	ymm10,ymm29,ymm25,3
	vshufi64x2	ymm11,ymm30,ymm26,3
	vmovdqu64	ymm25,YMMWORD[((96+0))+rdi]
	vmovdqu64	ymm26,YMMWORD[((96+200))+rdi]
	vmovdqu64	ymm27,YMMWORD[((96+400))+rdi]
	vmovdqu64	ymm28,YMMWORD[((96+600))+rdi]
	vpunpcklqdq	ymm29,ymm25,ymm26
	vpunpckhqdq	ymm30,ymm25,ymm26
	vpunpcklqdq	ymm25,ymm27,ymm28
	vpunpckhqdq	ymm26,ymm27,ymm28
	vshufi64x2	ymm12,ymm29,ymm25,0
	vshufi64x2	ymm13,ymm30,ymm26,0
	vshufi64x2	ymm14,ymm29,ymm25,3
	vshufi64x2	ymm15,ymm30,ymm26,3
	vmovdqu64	ymm25,YMMWORD[((128+0))+rdi]
	vmovdqu64	ymm26,YMMWORD[((128+200))+rdi]
	vmovdqu64	ymm27,YMMWORD[((128+400))+rdi]
	vmovdqu64	ymm28,YMMWORD[((128+600))+rdi]
	vpunpcklqdq	ymm29,ymm25,ymm26
	vpunpckhqdq	ymm30,ymm25,ymm26
	vpunpcklqdq	ymm25,ymm27,ymm28
	vpunpckhqdq	ymm26,ymm27,ymm28
	vshufi64x2	ymm16,ymm29,ymm25,0
	vshufi64x2	ymm17,ymm30,ymm26,0
	vshufi64x2	ymm18,ymm29,ymm25,3
	vshufi64x2	ymm19,ymm30,ymm26,3
	vmovdqu64	ymm25,YMMWORD[((160+0))+rdi]
	vmovdqu64	ymm26,YMMWORD[((160+200))+rdi]
	vmovdqu64	ymm27,YMMWORD[((160+400))+rdi]
	vmovdqu64	ymm28,YMMWORD[((160+600))+rdi]
	vpunpcklqdq	ymm29,ymm25,ymm26
	vpunpckhqdq	ymm30,ymm25,ymm26
	vpunpcklqdq	ymm25,ymm27,ymm28
	vpunpckhqdq	ymm26,ymm27,ymm28
	vshufi64x2	ymm20,ymm29,ymm25,0
	vshufi64x2	ymm21,ymm30,ymm26,0
	vshufi64x2	ymm22,ymm29,ymm25,3
	vshufi64x2	ymm23,ymm30,ymm26,3
	vmovq	xmm24,QWORD[((192+0))+rdi]
	vpinsrq	xmm24,xmm24,QWORD[((192+200))+rdi],1
	vmovq	xmm25,QWORD[((192+400))+rdi]
	vpinsrq	xmm25,xmm25,QWORD[((192+600))+rdi],1
	vinserti32x4	ymm24,ymm24,xmm25,1

	call	keccak_1600_permute

	vpunpcklqdq	ymm25,ymm0,ymm1
	vpunpckhqdq	ymm26,ymm0,ymm1
	vpunpcklqdq	ymm27,ymm2,ymm3
	vpunpckhqdq	ymm28,ymm2,ymm3
	vshufi64x2	ymm0,ymm25,ymm27,0
	vshufi64x2	ymm1,ymm26,ymm28,0
	vshufi64x2	ymm2,ymm25,ymm27,3
	vshufi64x2	ymm3,ymm26,ymm28,3
	vmovdqu64	YMMWORD[(0+0)+rdi],ymm0
	vmovdqu64	YMMWORD[(0+200)+rdi],ymm1
	vmovdqu64	YMMWORD[(0+400)+rdi],ymm2
	vmovdqu64	YMMWORD[(0+600)+rdi],ymm3
	vpunpcklqdq	ymm25,ymm4,ymm5
	vpunpckhqdq	ymm26,ymm4,ymm5
	vpunpcklqdq	ymm27,ymm6,ymm7
	vpunpckhqdq	ymm28,ymm6,ymm7
	vshufi64x2	ymm4,ymm25,ymm27,0
	vshufi64x2	ymm5,ymm26,ymm28,0
	vshufi64x2	ymm6,ymm25,ymm27,3
	vshufi64x2	ymm7,ymm26,ymm28,3
	vmovdqu64	YMMWORD[(32+0)+rdi],ymm4
	vmovdqu64	YMMWORD[(32+200)+rdi],ymm5
	vmovdqu64	YMMWORD[(32+400)+rdi],ymm6
	vmovdqu64	YMMWORD[(32+600)+rdi],ymm7
	vpunpcklqdq	ymm25,ymm8,ymm9
	vpunpckhqdq	ymm26,ymm8,ymm9
	vpunpcklqdq	ymm27,ymm10,ymm11
	vpunpckhqdq	ymm28,ymm10,ymm11
	vshufi64x2	ymm8,ymm25,ymm27,0
	vshufi64x2	ymm9,ymm26,ymm28,0
	vshufi64x2	ymm10,ymm25,ymm27,3
	vshufi64x2	ymm11,ymm26,ymm28,3
	vmovdqu64	YMMWORD[(64+0)+rdi],ymm8
	vmovdqu64	YMMWORD[(64+200)+rdi],ymm9
	vmovdqu64	YMMWORD[(64+400)+rdi],ymm10
	vmovdqu64	YMMWORD[(64+600)+rdi],ymm11
	vpunpcklqdq	ymm25,ymm12,ymm13
	vpunpckhqdq	ymm26,ymm12,ymm13
	vpunpcklqdq	ymm27,ymm14,ymm15
	vpunpckhqdq	ymm28,ymm14,ymm15
	vshufi64x2	ymm12,ymm25,ymm27,0
	vshufi64x2	ymm13,ymm26,ymm28,0
	vshufi64x2	ymm14,ymm25,ymm27,3
	vshufi64x2	ymm15,ymm26,ymm28,3
	vmovdqu64	YMMWORD[(96+0)+rdi],ymm12
	vmovdqu64	YMMWORD[(96+200)+rdi],ymm13
	vmovdqu64	YMMWORD[(96+400)+rdi],ymm14
	vmovdqu64	YMMWORD[(96+600)+rdi],ymm15
	vpunpcklqdq	ymm25,ymm16,ymm17
	vpunpckhqdq	ymm26,ymm16,ymm17
	vpunpcklqdq	ymm27,ymm18,ymm19
	vpunpckhqdq	ymm28,ymm18,ymm19
	vshufi64x2	ymm16,ymm25,ymm27,0
	vshufi64x2	ymm17,ymm26,ymm28,0
	vshufi64x2	ymm18,ymm25,ymm27,3
	vshufi64x2	ymm19,ymm26,ymm28,3
	vmovdqu64	YMMWORD[(128+0)+rdi],ymm16
	vmovdqu64	YMMWORD[(128+200)+rdi],ymm17
	vmovdqu64	YMMWORD[(128+400)+rdi],ymm18
	vmovdqu64	YMMWORD[(128+600)+rdi],ymm19
	vpunpcklqdq	ymm25,ymm20,ymm21
	vpunpckhqdq	ymm26,ymm20,ymm21
	vpunpcklqdq	ymm27,ymm22,ymm23
	vpunpckhqdq	ymm28,ymm22,ymm23
	vshufi64x2	ymm20,ymm25,ymm27,0
	vshufi64x2	ymm21,ymm26,ymm28,0
	vshufi64x2	ymm22,ymm25,ymm27,3
	vshufi64x2	ymm23,ymm26,ymm28,3
	vmovdqu64	YMMWORD[(160+0)+rdi],ymm20
	vmovdqu64	YMMWORD[(160+200)+rdi],ymm21
	vmovdqu64	YMMWORD[(160+400)+rdi],ymm22
	vmovdqu64	YMMWORD[(160+600)+rdi],ymm23
	vextracti32x4	xmm25,ymm24,1
	vmovq	QWORD[(192+0)+rdi],xmm24
	vpextrq	XMMWORD[(192+200)+rdi],xmm24,1
	vmovq	QWORD[(192+400)+rdi],xmm25
	vpextrq	XMMWORD[(192+600)+rdi],xmm25,1
	vmovdqu	xmm6,XMMWORD[rsp]
	vmovdqu	xmm7,XMMWORD[16+rsp]
	vmovdqu	xmm8,XMMWORD[32+rsp]
	vmovdqu	xmm9,XMMWORD[48+rsp]
	vmovdqu	xmm10,XMMWORD[64+rsp]
	vmovdqu	xmm11,XMMWORD[80+rsp]
	vmovdqu	xmm12,XMMWORD[96+rsp]
	vmovdqu	xmm13,XMMWORD[112+rsp]
	vmovdqu	xmm14,XMMWORD[128+rsp]
	vmovdqu	xmm15,XMMWORD[144+rsp]
	add	rsp,10*16
	vzeroupper
	mov	rdi,QWORD[8+rsp]	;WIN64 epilogue
	mov	rsi,QWORD[16+rsp]
	DB	0F3h,0C3h		;repret


section	.rdata rdata align=8

ALIGN	64
iotas_avx512:
	DQ	0x0000000000000001,0x0000000000008082
	DQ	0x800000000000808a,0x8000000080008000
	DQ	0x000000000000808b,0x0000000080000001
	DQ	0x8000000080008081,0x8000000000008009
	DQ	0x000000000000008a,0x0000000000000088
	DQ	0x0000000080008009,0x000000008000000a
	DQ	0x000000008000808b,0x800000000000008b
	DQ	0x8000000000008089,0x8000000000008003
	DQ	0x8000000000008002,0x8000000000000080
	DQ	0x000000000000800a,0x800000008000000a
	DQ	0x8000000080008081,0x8000000000008080
	DQ	0x0000000080000001,0x8000000080008008

%endif

section	.text

%else
; Work around https://bugzilla.nasm.us/show_bug.cgi?id=3392738
ret
%endif
