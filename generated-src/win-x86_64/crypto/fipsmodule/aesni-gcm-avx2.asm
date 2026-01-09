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
section	.rdata rdata align=8
ALIGN	16


$L$bswap_mask:
	DQ	0x08090a0b0c0d0e0f,0x0001020304050607








$L$gfpoly:
	DQ	1,0xc200000000000000


$L$gfpoly_and_internal_carrybit:
	DQ	1,0xc200000000000001

ALIGN	32

$L$ctr_pattern:
	DQ	0,0
	DQ	1,0
$L$inc_2blocks:
	DQ	2,0
	DQ	2,0

section	.text code align=64

global	gcm_init_vpclmulqdq_avx2

ALIGN	32
gcm_init_vpclmulqdq_avx2:

$L$SEH_begin_gcm_init_vpclmulqdq_avx2_1:
_CET_ENDBR
	sub	rsp,24
$L$SEH_prolog_gcm_init_vpclmulqdq_avx2_2:
	vmovdqa	XMMWORD[rsp],xmm6
$L$SEH_prolog_gcm_init_vpclmulqdq_avx2_3:




	vpshufd	xmm3,XMMWORD[rdx],0x4e





	vpshufd	xmm0,xmm3,0xd3
	vpsrad	xmm0,xmm0,31
	vpaddq	xmm3,xmm3,xmm3
	vpand	xmm0,xmm0,XMMWORD[$L$gfpoly_and_internal_carrybit]
	vpxor	xmm3,xmm3,xmm0

	vbroadcasti128	ymm6,XMMWORD[$L$gfpoly]


	DB	196,227,97,68,195,0
	DB	196,227,97,68,235,17
	DB	196,227,73,68,200,1
	vpshufd	xmm0,xmm0,0x4e
	vpxor	xmm1,xmm1,xmm0
	DB	196,227,73,68,193,1
	vpshufd	xmm1,xmm1,0x4e
	vpxor	xmm5,xmm5,xmm1
	vpxor	xmm5,xmm5,xmm0



	vinserti128	ymm3,ymm5,xmm3,1
	vinserti128	ymm5,ymm5,xmm5,1


	DB	196,227,101,68,197,0
	DB	196,227,101,68,205,1
	DB	196,227,101,68,213,16
	vpxor	ymm1,ymm1,ymm2
	DB	196,227,77,68,208,1
	vpshufd	ymm0,ymm0,0x4e
	vpxor	ymm1,ymm1,ymm0
	vpxor	ymm1,ymm1,ymm2
	DB	196,227,101,68,229,17
	DB	196,227,77,68,193,1
	vpshufd	ymm1,ymm1,0x4e
	vpxor	ymm4,ymm4,ymm1
	vpxor	ymm4,ymm4,ymm0



	vmovdqu	YMMWORD[96+rcx],ymm3
	vmovdqu	YMMWORD[64+rcx],ymm4



	vpunpcklqdq	ymm0,ymm4,ymm3
	vpunpckhqdq	ymm1,ymm4,ymm3
	vpxor	ymm0,ymm0,ymm1
	vmovdqu	YMMWORD[(128+32)+rcx],ymm0


	DB	196,227,93,68,197,0
	DB	196,227,93,68,205,1
	DB	196,227,93,68,213,16
	vpxor	ymm1,ymm1,ymm2
	DB	196,227,77,68,208,1
	vpshufd	ymm0,ymm0,0x4e
	vpxor	ymm1,ymm1,ymm0
	vpxor	ymm1,ymm1,ymm2
	DB	196,227,93,68,221,17
	DB	196,227,77,68,193,1
	vpshufd	ymm1,ymm1,0x4e
	vpxor	ymm3,ymm3,ymm1
	vpxor	ymm3,ymm3,ymm0

	DB	196,227,101,68,197,0
	DB	196,227,101,68,205,1
	DB	196,227,101,68,213,16
	vpxor	ymm1,ymm1,ymm2
	DB	196,227,77,68,208,1
	vpshufd	ymm0,ymm0,0x4e
	vpxor	ymm1,ymm1,ymm0
	vpxor	ymm1,ymm1,ymm2
	DB	196,227,101,68,229,17
	DB	196,227,77,68,193,1
	vpshufd	ymm1,ymm1,0x4e
	vpxor	ymm4,ymm4,ymm1
	vpxor	ymm4,ymm4,ymm0

	vmovdqu	YMMWORD[32+rcx],ymm3
	vmovdqu	YMMWORD[rcx],ymm4



	vpunpcklqdq	ymm0,ymm4,ymm3
	vpunpckhqdq	ymm1,ymm4,ymm3
	vpxor	ymm0,ymm0,ymm1
	vmovdqu	YMMWORD[128+rcx],ymm0

	vzeroupper
	vmovdqa	xmm6,XMMWORD[rsp]
	add	rsp,24
	DB	0F3h,0C3h		;repret
$L$SEH_end_gcm_init_vpclmulqdq_avx2_4:


global	gcm_gmult_vpclmulqdq_avx2

ALIGN	32
gcm_gmult_vpclmulqdq_avx2:

$L$SEH_begin_gcm_gmult_vpclmulqdq_avx2_1:
_CET_ENDBR
	sub	rsp,24
$L$SEH_prolog_gcm_gmult_vpclmulqdq_avx2_2:
	vmovdqa	XMMWORD[rsp],xmm6
$L$SEH_prolog_gcm_gmult_vpclmulqdq_avx2_3:


	vmovdqu	xmm0,XMMWORD[rcx]
	vmovdqu	xmm1,XMMWORD[$L$bswap_mask]
	vmovdqu	xmm2,XMMWORD[((128-16))+rdx]
	vmovdqu	xmm3,XMMWORD[$L$gfpoly]
	vpshufb	xmm0,xmm0,xmm1

	DB	196,227,121,68,226,0
	DB	196,227,121,68,234,1
	DB	196,227,121,68,242,16
	vpxor	xmm5,xmm5,xmm6
	DB	196,227,97,68,244,1
	vpshufd	xmm4,xmm4,0x4e
	vpxor	xmm5,xmm5,xmm4
	vpxor	xmm5,xmm5,xmm6
	DB	196,227,121,68,194,17
	DB	196,227,97,68,229,1
	vpshufd	xmm5,xmm5,0x4e
	vpxor	xmm0,xmm0,xmm5
	vpxor	xmm0,xmm0,xmm4


	vpshufb	xmm0,xmm0,xmm1
	vmovdqu	XMMWORD[rcx],xmm0


	vmovdqa	xmm6,XMMWORD[rsp]
	add	rsp,24
	DB	0F3h,0C3h		;repret
$L$SEH_end_gcm_gmult_vpclmulqdq_avx2_4:


global	gcm_ghash_vpclmulqdq_avx2

ALIGN	32
gcm_ghash_vpclmulqdq_avx2:

$L$SEH_begin_gcm_ghash_vpclmulqdq_avx2_1:
_CET_ENDBR
	sub	rsp,72
$L$SEH_prolog_gcm_ghash_vpclmulqdq_avx2_2:
	vmovdqa	XMMWORD[rsp],xmm6
$L$SEH_prolog_gcm_ghash_vpclmulqdq_avx2_3:
	vmovdqa	XMMWORD[16+rsp],xmm7
$L$SEH_prolog_gcm_ghash_vpclmulqdq_avx2_4:
	vmovdqa	XMMWORD[32+rsp],xmm8
$L$SEH_prolog_gcm_ghash_vpclmulqdq_avx2_5:
	vmovdqa	XMMWORD[48+rsp],xmm9
$L$SEH_prolog_gcm_ghash_vpclmulqdq_avx2_6:





	vmovdqu	xmm6,XMMWORD[$L$bswap_mask]
	vmovdqu	xmm7,XMMWORD[$L$gfpoly]


	vmovdqu	xmm5,XMMWORD[rcx]
	vpshufb	xmm5,xmm5,xmm6


	cmp	r9,32
	jb	NEAR $L$ghash_lastblock



	vinserti128	ymm6,ymm6,xmm6,1
	vinserti128	ymm7,ymm7,xmm7,1

	cmp	r9,127
	jbe	NEAR $L$ghash_loop_1x


	vmovdqu	ymm8,YMMWORD[128+rdx]
	vmovdqu	ymm9,YMMWORD[((128+32))+rdx]
$L$ghash_loop_4x:

	vmovdqu	ymm1,YMMWORD[r8]
	vpshufb	ymm1,ymm1,ymm6
	vmovdqu	ymm2,YMMWORD[rdx]
	vpxor	ymm1,ymm1,ymm5
	DB	196,227,117,68,218,0
	DB	196,227,117,68,234,17
	vpunpckhqdq	ymm0,ymm1,ymm1
	vpxor	ymm0,ymm0,ymm1
	DB	196,195,125,68,224,0

	vmovdqu	ymm1,YMMWORD[32+r8]
	vpshufb	ymm1,ymm1,ymm6
	vmovdqu	ymm2,YMMWORD[32+rdx]
	DB	196,227,117,68,194,0
	vpxor	ymm3,ymm3,ymm0
	DB	196,227,117,68,194,17
	vpxor	ymm5,ymm5,ymm0
	vpunpckhqdq	ymm0,ymm1,ymm1
	vpxor	ymm0,ymm0,ymm1
	DB	196,195,125,68,192,16
	vpxor	ymm4,ymm4,ymm0

	vmovdqu	ymm1,YMMWORD[64+r8]
	vpshufb	ymm1,ymm1,ymm6
	vmovdqu	ymm2,YMMWORD[64+rdx]
	DB	196,227,117,68,194,0
	vpxor	ymm3,ymm3,ymm0
	DB	196,227,117,68,194,17
	vpxor	ymm5,ymm5,ymm0
	vpunpckhqdq	ymm0,ymm1,ymm1
	vpxor	ymm0,ymm0,ymm1
	DB	196,195,125,68,193,0
	vpxor	ymm4,ymm4,ymm0


	vmovdqu	ymm1,YMMWORD[96+r8]
	vpshufb	ymm1,ymm1,ymm6
	vmovdqu	ymm2,YMMWORD[96+rdx]
	DB	196,227,117,68,194,0
	vpxor	ymm3,ymm3,ymm0
	DB	196,227,117,68,194,17
	vpxor	ymm5,ymm5,ymm0
	vpunpckhqdq	ymm0,ymm1,ymm1
	vpxor	ymm0,ymm0,ymm1
	DB	196,195,125,68,193,16
	vpxor	ymm4,ymm4,ymm0

	vpxor	ymm4,ymm4,ymm3
	vpxor	ymm4,ymm4,ymm5


	vbroadcasti128	ymm2,XMMWORD[$L$gfpoly]
	DB	196,227,109,68,195,1
	vpshufd	ymm3,ymm3,0x4e
	vpxor	ymm4,ymm4,ymm3
	vpxor	ymm4,ymm4,ymm0

	DB	196,227,109,68,196,1
	vpshufd	ymm4,ymm4,0x4e
	vpxor	ymm5,ymm5,ymm4
	vpxor	ymm5,ymm5,ymm0
	vextracti128	xmm0,ymm5,1
	vpxor	xmm5,xmm5,xmm0

	sub	r8,-128
	add	r9,-128
	cmp	r9,127
	ja	NEAR $L$ghash_loop_4x


	cmp	r9,32
	jb	NEAR $L$ghash_loop_1x_done
$L$ghash_loop_1x:
	vmovdqu	ymm0,YMMWORD[r8]
	vpshufb	ymm0,ymm0,ymm6
	vpxor	ymm5,ymm5,ymm0
	vmovdqu	ymm0,YMMWORD[((128-32))+rdx]
	DB	196,227,85,68,200,0
	DB	196,227,85,68,208,1
	DB	196,227,85,68,216,16
	vpxor	ymm2,ymm2,ymm3
	DB	196,227,69,68,217,1
	vpshufd	ymm1,ymm1,0x4e
	vpxor	ymm2,ymm2,ymm1
	vpxor	ymm2,ymm2,ymm3
	DB	196,227,85,68,232,17
	DB	196,227,69,68,202,1
	vpshufd	ymm2,ymm2,0x4e
	vpxor	ymm5,ymm5,ymm2
	vpxor	ymm5,ymm5,ymm1

	vextracti128	xmm0,ymm5,1
	vpxor	xmm5,xmm5,xmm0
	add	r8,32
	sub	r9,32
	cmp	r9,32
	jae	NEAR $L$ghash_loop_1x
$L$ghash_loop_1x_done:


$L$ghash_lastblock:
	test	r9,r9
	jz	NEAR $L$ghash_done
	vmovdqu	xmm0,XMMWORD[r8]
	vpshufb	xmm0,xmm0,xmm6
	vpxor	xmm5,xmm5,xmm0
	vmovdqu	xmm0,XMMWORD[((128-16))+rdx]
	DB	196,227,81,68,200,0
	DB	196,227,81,68,208,1
	DB	196,227,81,68,216,16
	vpxor	xmm2,xmm2,xmm3
	DB	196,227,65,68,217,1
	vpshufd	xmm1,xmm1,0x4e
	vpxor	xmm2,xmm2,xmm1
	vpxor	xmm2,xmm2,xmm3
	DB	196,227,81,68,232,17
	DB	196,227,65,68,202,1
	vpshufd	xmm2,xmm2,0x4e
	vpxor	xmm5,xmm5,xmm2
	vpxor	xmm5,xmm5,xmm1


$L$ghash_done:

	vpshufb	xmm5,xmm5,xmm6
	vmovdqu	XMMWORD[rcx],xmm5

	vzeroupper
	vmovdqa	xmm6,XMMWORD[rsp]
	vmovdqa	xmm7,XMMWORD[16+rsp]
	vmovdqa	xmm8,XMMWORD[32+rsp]
	vmovdqa	xmm9,XMMWORD[48+rsp]
	add	rsp,72
	DB	0F3h,0C3h		;repret
$L$SEH_end_gcm_ghash_vpclmulqdq_avx2_7:


global	aes_gcm_enc_update_vaes_avx2

ALIGN	32
aes_gcm_enc_update_vaes_avx2:

$L$SEH_begin_aes_gcm_enc_update_vaes_avx2_1:
_CET_ENDBR
	push	rsi
$L$SEH_prolog_aes_gcm_enc_update_vaes_avx2_2:
	push	rdi
$L$SEH_prolog_aes_gcm_enc_update_vaes_avx2_3:
	push	r12
$L$SEH_prolog_aes_gcm_enc_update_vaes_avx2_4:

	mov	rsi,QWORD[64+rsp]
	mov	rdi,QWORD[72+rsp]
	mov	r12,QWORD[80+rsp]
	sub	rsp,160
$L$SEH_prolog_aes_gcm_enc_update_vaes_avx2_5:
	vmovdqa	XMMWORD[rsp],xmm6
$L$SEH_prolog_aes_gcm_enc_update_vaes_avx2_6:
	vmovdqa	XMMWORD[16+rsp],xmm7
$L$SEH_prolog_aes_gcm_enc_update_vaes_avx2_7:
	vmovdqa	XMMWORD[32+rsp],xmm8
$L$SEH_prolog_aes_gcm_enc_update_vaes_avx2_8:
	vmovdqa	XMMWORD[48+rsp],xmm9
$L$SEH_prolog_aes_gcm_enc_update_vaes_avx2_9:
	vmovdqa	XMMWORD[64+rsp],xmm10
$L$SEH_prolog_aes_gcm_enc_update_vaes_avx2_10:
	vmovdqa	XMMWORD[80+rsp],xmm11
$L$SEH_prolog_aes_gcm_enc_update_vaes_avx2_11:
	vmovdqa	XMMWORD[96+rsp],xmm12
$L$SEH_prolog_aes_gcm_enc_update_vaes_avx2_12:
	vmovdqa	XMMWORD[112+rsp],xmm13
$L$SEH_prolog_aes_gcm_enc_update_vaes_avx2_13:
	vmovdqa	XMMWORD[128+rsp],xmm14
$L$SEH_prolog_aes_gcm_enc_update_vaes_avx2_14:
	vmovdqa	XMMWORD[144+rsp],xmm15
$L$SEH_prolog_aes_gcm_enc_update_vaes_avx2_15:

%ifdef BORINGSSL_DISPATCH_TEST
EXTERN	BORINGSSL_function_hit
	mov	BYTE[((BORINGSSL_function_hit+9))],1
%endif
	vbroadcasti128	ymm0,XMMWORD[$L$bswap_mask]



	vmovdqu	xmm1,XMMWORD[r12]
	vpshufb	xmm1,xmm1,xmm0
	vbroadcasti128	ymm11,XMMWORD[rsi]
	vpshufb	ymm11,ymm11,ymm0



	mov	r10d,DWORD[240+r9]
	lea	r10d,[((-20))+r10*4]




	lea	r11,[96+r10*4+r9]
	vbroadcasti128	ymm9,XMMWORD[r9]
	vbroadcasti128	ymm10,XMMWORD[r11]


	vpaddd	ymm11,ymm11,YMMWORD[$L$ctr_pattern]



	cmp	r8,127
	jbe	NEAR $L$crypt_loop_4x_done__func1

	vmovdqu	ymm7,YMMWORD[128+rdi]
	vmovdqu	ymm8,YMMWORD[((128+32))+rdi]



	vmovdqu	ymm2,YMMWORD[$L$inc_2blocks]
	vpshufb	ymm12,ymm11,ymm0
	vpaddd	ymm11,ymm11,ymm2
	vpshufb	ymm13,ymm11,ymm0
	vpaddd	ymm11,ymm11,ymm2
	vpshufb	ymm14,ymm11,ymm0
	vpaddd	ymm11,ymm11,ymm2
	vpshufb	ymm15,ymm11,ymm0
	vpaddd	ymm11,ymm11,ymm2


	vpxor	ymm12,ymm12,ymm9
	vpxor	ymm13,ymm13,ymm9
	vpxor	ymm14,ymm14,ymm9
	vpxor	ymm15,ymm15,ymm9

	lea	rax,[16+r9]
$L$vaesenc_loop_first_4_vecs__func1:
	vbroadcasti128	ymm2,XMMWORD[rax]
	DB	196,98,29,220,226
	DB	196,98,21,220,234
	DB	196,98,13,220,242
	DB	196,98,5,220,250

	add	rax,16
	cmp	r11,rax
	jne	NEAR $L$vaesenc_loop_first_4_vecs__func1
	vpxor	ymm2,ymm10,YMMWORD[rcx]
	vpxor	ymm3,ymm10,YMMWORD[32+rcx]
	vpxor	ymm5,ymm10,YMMWORD[64+rcx]
	vpxor	ymm6,ymm10,YMMWORD[96+rcx]
	DB	196,98,29,221,226
	DB	196,98,21,221,235
	DB	196,98,13,221,245
	DB	196,98,5,221,254
	vmovdqu	YMMWORD[rdx],ymm12
	vmovdqu	YMMWORD[32+rdx],ymm13
	vmovdqu	YMMWORD[64+rdx],ymm14
	vmovdqu	YMMWORD[96+rdx],ymm15

	sub	rcx,-128
	add	r8,-128
	cmp	r8,127
	jbe	NEAR $L$ghash_last_ciphertext_4x__func1
ALIGN	16
$L$crypt_loop_4x__func1:




	vmovdqu	ymm2,YMMWORD[$L$inc_2blocks]
	vpshufb	ymm12,ymm11,ymm0
	vpaddd	ymm11,ymm11,ymm2
	vpshufb	ymm13,ymm11,ymm0
	vpaddd	ymm11,ymm11,ymm2
	vpshufb	ymm14,ymm11,ymm0
	vpaddd	ymm11,ymm11,ymm2
	vpshufb	ymm15,ymm11,ymm0
	vpaddd	ymm11,ymm11,ymm2


	vpxor	ymm12,ymm12,ymm9
	vpxor	ymm13,ymm13,ymm9
	vpxor	ymm14,ymm14,ymm9
	vpxor	ymm15,ymm15,ymm9

	cmp	r10d,24
	jl	NEAR $L$aes128__func1
	je	NEAR $L$aes192__func1

	vbroadcasti128	ymm2,XMMWORD[((-208))+r11]
	DB	196,98,29,220,226
	DB	196,98,21,220,234
	DB	196,98,13,220,242
	DB	196,98,5,220,250

	vbroadcasti128	ymm2,XMMWORD[((-192))+r11]
	DB	196,98,29,220,226
	DB	196,98,21,220,234
	DB	196,98,13,220,242
	DB	196,98,5,220,250

$L$aes192__func1:
	vbroadcasti128	ymm2,XMMWORD[((-176))+r11]
	DB	196,98,29,220,226
	DB	196,98,21,220,234
	DB	196,98,13,220,242
	DB	196,98,5,220,250

	vbroadcasti128	ymm2,XMMWORD[((-160))+r11]
	DB	196,98,29,220,226
	DB	196,98,21,220,234
	DB	196,98,13,220,242
	DB	196,98,5,220,250

$L$aes128__func1:
	prefetcht0	[512+rcx]
	prefetcht0	[((512+64))+rcx]

	vmovdqu	ymm3,YMMWORD[rdx]
	vpshufb	ymm3,ymm3,ymm0
	vmovdqu	ymm4,YMMWORD[rdi]
	vpxor	ymm3,ymm3,ymm1
	DB	196,227,101,68,236,0
	DB	196,227,101,68,204,17
	vpunpckhqdq	ymm2,ymm3,ymm3
	vpxor	ymm2,ymm2,ymm3
	DB	196,227,109,68,247,0

	vbroadcasti128	ymm2,XMMWORD[((-144))+r11]
	DB	196,98,29,220,226
	DB	196,98,21,220,234
	DB	196,98,13,220,242
	DB	196,98,5,220,250


	vbroadcasti128	ymm2,XMMWORD[((-128))+r11]
	DB	196,98,29,220,226
	DB	196,98,21,220,234
	DB	196,98,13,220,242
	DB	196,98,5,220,250


	vmovdqu	ymm3,YMMWORD[32+rdx]
	vpshufb	ymm3,ymm3,ymm0
	vmovdqu	ymm4,YMMWORD[32+rdi]
	DB	196,227,101,68,212,0
	vpxor	ymm5,ymm5,ymm2
	DB	196,227,101,68,212,17
	vpxor	ymm1,ymm1,ymm2
	vpunpckhqdq	ymm2,ymm3,ymm3
	vpxor	ymm2,ymm2,ymm3
	DB	196,227,109,68,215,16
	vpxor	ymm6,ymm6,ymm2

	vbroadcasti128	ymm2,XMMWORD[((-112))+r11]
	DB	196,98,29,220,226
	DB	196,98,21,220,234
	DB	196,98,13,220,242
	DB	196,98,5,220,250


	vmovdqu	ymm3,YMMWORD[64+rdx]
	vpshufb	ymm3,ymm3,ymm0
	vmovdqu	ymm4,YMMWORD[64+rdi]

	vbroadcasti128	ymm2,XMMWORD[((-96))+r11]
	DB	196,98,29,220,226
	DB	196,98,21,220,234
	DB	196,98,13,220,242
	DB	196,98,5,220,250

	DB	196,227,101,68,212,0
	vpxor	ymm5,ymm5,ymm2
	DB	196,227,101,68,212,17
	vpxor	ymm1,ymm1,ymm2

	vbroadcasti128	ymm2,XMMWORD[((-80))+r11]
	DB	196,98,29,220,226
	DB	196,98,21,220,234
	DB	196,98,13,220,242
	DB	196,98,5,220,250

	vpunpckhqdq	ymm2,ymm3,ymm3
	vpxor	ymm2,ymm2,ymm3
	DB	196,195,109,68,208,0
	vpxor	ymm6,ymm6,ymm2


	vmovdqu	ymm3,YMMWORD[96+rdx]
	vpshufb	ymm3,ymm3,ymm0

	vbroadcasti128	ymm2,XMMWORD[((-64))+r11]
	DB	196,98,29,220,226
	DB	196,98,21,220,234
	DB	196,98,13,220,242
	DB	196,98,5,220,250

	vmovdqu	ymm4,YMMWORD[96+rdi]
	DB	196,227,101,68,212,0
	vpxor	ymm5,ymm5,ymm2
	DB	196,227,101,68,212,17
	vpxor	ymm1,ymm1,ymm2
	vpunpckhqdq	ymm2,ymm3,ymm3
	vpxor	ymm2,ymm2,ymm3
	DB	196,195,109,68,208,16
	vpxor	ymm6,ymm6,ymm2

	vbroadcasti128	ymm2,XMMWORD[((-48))+r11]
	DB	196,98,29,220,226
	DB	196,98,21,220,234
	DB	196,98,13,220,242
	DB	196,98,5,220,250


	vpxor	ymm6,ymm6,ymm5
	vpxor	ymm6,ymm6,ymm1


	vbroadcasti128	ymm4,XMMWORD[$L$gfpoly]
	DB	196,227,93,68,213,1
	vpshufd	ymm5,ymm5,0x4e
	vpxor	ymm6,ymm6,ymm5
	vpxor	ymm6,ymm6,ymm2

	vbroadcasti128	ymm2,XMMWORD[((-32))+r11]
	DB	196,98,29,220,226
	DB	196,98,21,220,234
	DB	196,98,13,220,242
	DB	196,98,5,220,250


	DB	196,227,93,68,214,1
	vpshufd	ymm6,ymm6,0x4e
	vpxor	ymm1,ymm1,ymm6
	vpxor	ymm1,ymm1,ymm2

	vbroadcasti128	ymm2,XMMWORD[((-16))+r11]
	DB	196,98,29,220,226
	DB	196,98,21,220,234
	DB	196,98,13,220,242
	DB	196,98,5,220,250

	vextracti128	xmm2,ymm1,1
	vpxor	xmm1,xmm1,xmm2


	sub	rdx,-128
	vpxor	ymm2,ymm10,YMMWORD[rcx]
	vpxor	ymm3,ymm10,YMMWORD[32+rcx]
	vpxor	ymm5,ymm10,YMMWORD[64+rcx]
	vpxor	ymm6,ymm10,YMMWORD[96+rcx]
	DB	196,98,29,221,226
	DB	196,98,21,221,235
	DB	196,98,13,221,245
	DB	196,98,5,221,254
	vmovdqu	YMMWORD[rdx],ymm12
	vmovdqu	YMMWORD[32+rdx],ymm13
	vmovdqu	YMMWORD[64+rdx],ymm14
	vmovdqu	YMMWORD[96+rdx],ymm15

	sub	rcx,-128

	add	r8,-128
	cmp	r8,127
	ja	NEAR $L$crypt_loop_4x__func1
$L$ghash_last_ciphertext_4x__func1:

	vmovdqu	ymm3,YMMWORD[rdx]
	vpshufb	ymm3,ymm3,ymm0
	vmovdqu	ymm4,YMMWORD[rdi]
	vpxor	ymm3,ymm3,ymm1
	DB	196,227,101,68,236,0
	DB	196,227,101,68,204,17
	vpunpckhqdq	ymm2,ymm3,ymm3
	vpxor	ymm2,ymm2,ymm3
	DB	196,227,109,68,247,0

	vmovdqu	ymm3,YMMWORD[32+rdx]
	vpshufb	ymm3,ymm3,ymm0
	vmovdqu	ymm4,YMMWORD[32+rdi]
	DB	196,227,101,68,212,0
	vpxor	ymm5,ymm5,ymm2
	DB	196,227,101,68,212,17
	vpxor	ymm1,ymm1,ymm2
	vpunpckhqdq	ymm2,ymm3,ymm3
	vpxor	ymm2,ymm2,ymm3
	DB	196,227,109,68,215,16
	vpxor	ymm6,ymm6,ymm2

	vmovdqu	ymm3,YMMWORD[64+rdx]
	vpshufb	ymm3,ymm3,ymm0
	vmovdqu	ymm4,YMMWORD[64+rdi]
	DB	196,227,101,68,212,0
	vpxor	ymm5,ymm5,ymm2
	DB	196,227,101,68,212,17
	vpxor	ymm1,ymm1,ymm2
	vpunpckhqdq	ymm2,ymm3,ymm3
	vpxor	ymm2,ymm2,ymm3
	DB	196,195,109,68,208,0
	vpxor	ymm6,ymm6,ymm2


	vmovdqu	ymm3,YMMWORD[96+rdx]
	vpshufb	ymm3,ymm3,ymm0
	vmovdqu	ymm4,YMMWORD[96+rdi]
	DB	196,227,101,68,212,0
	vpxor	ymm5,ymm5,ymm2
	DB	196,227,101,68,212,17
	vpxor	ymm1,ymm1,ymm2
	vpunpckhqdq	ymm2,ymm3,ymm3
	vpxor	ymm2,ymm2,ymm3
	DB	196,195,109,68,208,16
	vpxor	ymm6,ymm6,ymm2

	vpxor	ymm6,ymm6,ymm5
	vpxor	ymm6,ymm6,ymm1


	vbroadcasti128	ymm4,XMMWORD[$L$gfpoly]
	DB	196,227,93,68,213,1
	vpshufd	ymm5,ymm5,0x4e
	vpxor	ymm6,ymm6,ymm5
	vpxor	ymm6,ymm6,ymm2

	DB	196,227,93,68,214,1
	vpshufd	ymm6,ymm6,0x4e
	vpxor	ymm1,ymm1,ymm6
	vpxor	ymm1,ymm1,ymm2
	vextracti128	xmm2,ymm1,1
	vpxor	xmm1,xmm1,xmm2

	sub	rdx,-128
$L$crypt_loop_4x_done__func1:

	test	r8,r8
	jz	NEAR $L$done__func1





	lea	rsi,[128+rdi]
	sub	rsi,r8


	vpxor	xmm5,xmm5,xmm5
	vpxor	xmm6,xmm6,xmm6
	vpxor	xmm7,xmm7,xmm7

	cmp	r8,64
	jb	NEAR $L$lessthan64bytes__func1


	vpshufb	ymm12,ymm11,ymm0
	vpaddd	ymm11,ymm11,YMMWORD[$L$inc_2blocks]
	vpshufb	ymm13,ymm11,ymm0
	vpaddd	ymm11,ymm11,YMMWORD[$L$inc_2blocks]
	vpxor	ymm12,ymm12,ymm9
	vpxor	ymm13,ymm13,ymm9
	lea	rax,[16+r9]
$L$vaesenc_loop_tail_1__func1:
	vbroadcasti128	ymm2,XMMWORD[rax]
	DB	196,98,29,220,226
	DB	196,98,21,220,234
	add	rax,16
	cmp	r11,rax
	jne	NEAR $L$vaesenc_loop_tail_1__func1
	DB	196,66,29,221,226
	DB	196,66,21,221,234


	vmovdqu	ymm2,YMMWORD[rcx]
	vmovdqu	ymm3,YMMWORD[32+rcx]
	vpxor	ymm12,ymm12,ymm2
	vpxor	ymm13,ymm13,ymm3
	vmovdqu	YMMWORD[rdx],ymm12
	vmovdqu	YMMWORD[32+rdx],ymm13


	vpshufb	ymm12,ymm12,ymm0
	vpshufb	ymm13,ymm13,ymm0
	vpxor	ymm12,ymm12,ymm1
	vmovdqu	ymm2,YMMWORD[rsi]
	vmovdqu	ymm3,YMMWORD[32+rsi]
	DB	196,227,29,68,234,0
	DB	196,227,29,68,242,1
	DB	196,227,29,68,226,16
	vpxor	ymm6,ymm6,ymm4
	DB	196,227,29,68,250,17
	DB	196,227,21,68,227,0
	vpxor	ymm5,ymm5,ymm4
	DB	196,227,21,68,227,1
	vpxor	ymm6,ymm6,ymm4
	DB	196,227,21,68,227,16
	vpxor	ymm6,ymm6,ymm4
	DB	196,227,21,68,227,17
	vpxor	ymm7,ymm7,ymm4

	add	rsi,64
	add	rcx,64
	add	rdx,64
	sub	r8,64
	jz	NEAR $L$reduce__func1

	vpxor	xmm1,xmm1,xmm1


$L$lessthan64bytes__func1:
	vpshufb	ymm12,ymm11,ymm0
	vpaddd	ymm11,ymm11,YMMWORD[$L$inc_2blocks]
	vpshufb	ymm13,ymm11,ymm0
	vpxor	ymm12,ymm12,ymm9
	vpxor	ymm13,ymm13,ymm9
	lea	rax,[16+r9]
$L$vaesenc_loop_tail_2__func1:
	vbroadcasti128	ymm2,XMMWORD[rax]
	DB	196,98,29,220,226
	DB	196,98,21,220,234
	add	rax,16
	cmp	r11,rax
	jne	NEAR $L$vaesenc_loop_tail_2__func1
	DB	196,66,29,221,226
	DB	196,66,21,221,234




	cmp	r8,32
	jb	NEAR $L$xor_one_block__func1
	je	NEAR $L$xor_two_blocks__func1

$L$xor_three_blocks__func1:
	vmovdqu	ymm2,YMMWORD[rcx]
	vmovdqu	xmm3,XMMWORD[32+rcx]
	vpxor	ymm12,ymm12,ymm2
	vpxor	xmm13,xmm13,xmm3
	vmovdqu	YMMWORD[rdx],ymm12
	vmovdqu	XMMWORD[32+rdx],xmm13

	vpshufb	ymm12,ymm12,ymm0
	vpshufb	xmm13,xmm13,xmm0
	vpxor	ymm12,ymm12,ymm1
	vmovdqu	ymm2,YMMWORD[rsi]
	vmovdqu	xmm3,XMMWORD[32+rsi]
	DB	196,227,17,68,227,0
	vpxor	ymm5,ymm5,ymm4
	DB	196,227,17,68,227,1
	vpxor	ymm6,ymm6,ymm4
	DB	196,227,17,68,227,16
	vpxor	ymm6,ymm6,ymm4
	DB	196,227,17,68,227,17
	vpxor	ymm7,ymm7,ymm4
	jmp	NEAR $L$ghash_mul_one_vec_unreduced__func1

$L$xor_two_blocks__func1:
	vmovdqu	ymm2,YMMWORD[rcx]
	vpxor	ymm12,ymm12,ymm2
	vmovdqu	YMMWORD[rdx],ymm12
	vpshufb	ymm12,ymm12,ymm0
	vpxor	ymm12,ymm12,ymm1
	vmovdqu	ymm2,YMMWORD[rsi]
	jmp	NEAR $L$ghash_mul_one_vec_unreduced__func1

$L$xor_one_block__func1:
	vmovdqu	xmm2,XMMWORD[rcx]
	vpxor	xmm12,xmm12,xmm2
	vmovdqu	XMMWORD[rdx],xmm12
	vpshufb	xmm12,xmm12,xmm0
	vpxor	xmm12,xmm12,xmm1
	vmovdqu	xmm2,XMMWORD[rsi]

$L$ghash_mul_one_vec_unreduced__func1:
	DB	196,227,29,68,226,0
	vpxor	ymm5,ymm5,ymm4
	DB	196,227,29,68,226,1
	vpxor	ymm6,ymm6,ymm4
	DB	196,227,29,68,226,16
	vpxor	ymm6,ymm6,ymm4
	DB	196,227,29,68,226,17
	vpxor	ymm7,ymm7,ymm4

$L$reduce__func1:

	vbroadcasti128	ymm2,XMMWORD[$L$gfpoly]
	DB	196,227,109,68,221,1
	vpshufd	ymm5,ymm5,0x4e
	vpxor	ymm6,ymm6,ymm5
	vpxor	ymm6,ymm6,ymm3
	DB	196,227,109,68,222,1
	vpshufd	ymm6,ymm6,0x4e
	vpxor	ymm7,ymm7,ymm6
	vpxor	ymm7,ymm7,ymm3
	vextracti128	xmm1,ymm7,1
	vpxor	xmm1,xmm1,xmm7

$L$done__func1:

	vpshufb	xmm1,xmm1,xmm0
	vmovdqu	XMMWORD[r12],xmm1

	vzeroupper
	vmovdqa	xmm6,XMMWORD[rsp]
	vmovdqa	xmm7,XMMWORD[16+rsp]
	vmovdqa	xmm8,XMMWORD[32+rsp]
	vmovdqa	xmm9,XMMWORD[48+rsp]
	vmovdqa	xmm10,XMMWORD[64+rsp]
	vmovdqa	xmm11,XMMWORD[80+rsp]
	vmovdqa	xmm12,XMMWORD[96+rsp]
	vmovdqa	xmm13,XMMWORD[112+rsp]
	vmovdqa	xmm14,XMMWORD[128+rsp]
	vmovdqa	xmm15,XMMWORD[144+rsp]
	add	rsp,160
	pop	r12
	pop	rdi
	pop	rsi
	DB	0F3h,0C3h		;repret
$L$SEH_end_aes_gcm_enc_update_vaes_avx2_16:


global	aes_gcm_dec_update_vaes_avx2

ALIGN	32
aes_gcm_dec_update_vaes_avx2:

$L$SEH_begin_aes_gcm_dec_update_vaes_avx2_1:
_CET_ENDBR
	push	rsi
$L$SEH_prolog_aes_gcm_dec_update_vaes_avx2_2:
	push	rdi
$L$SEH_prolog_aes_gcm_dec_update_vaes_avx2_3:
	push	r12
$L$SEH_prolog_aes_gcm_dec_update_vaes_avx2_4:

	mov	rsi,QWORD[64+rsp]
	mov	rdi,QWORD[72+rsp]
	mov	r12,QWORD[80+rsp]
	sub	rsp,160
$L$SEH_prolog_aes_gcm_dec_update_vaes_avx2_5:
	vmovdqa	XMMWORD[rsp],xmm6
$L$SEH_prolog_aes_gcm_dec_update_vaes_avx2_6:
	vmovdqa	XMMWORD[16+rsp],xmm7
$L$SEH_prolog_aes_gcm_dec_update_vaes_avx2_7:
	vmovdqa	XMMWORD[32+rsp],xmm8
$L$SEH_prolog_aes_gcm_dec_update_vaes_avx2_8:
	vmovdqa	XMMWORD[48+rsp],xmm9
$L$SEH_prolog_aes_gcm_dec_update_vaes_avx2_9:
	vmovdqa	XMMWORD[64+rsp],xmm10
$L$SEH_prolog_aes_gcm_dec_update_vaes_avx2_10:
	vmovdqa	XMMWORD[80+rsp],xmm11
$L$SEH_prolog_aes_gcm_dec_update_vaes_avx2_11:
	vmovdqa	XMMWORD[96+rsp],xmm12
$L$SEH_prolog_aes_gcm_dec_update_vaes_avx2_12:
	vmovdqa	XMMWORD[112+rsp],xmm13
$L$SEH_prolog_aes_gcm_dec_update_vaes_avx2_13:
	vmovdqa	XMMWORD[128+rsp],xmm14
$L$SEH_prolog_aes_gcm_dec_update_vaes_avx2_14:
	vmovdqa	XMMWORD[144+rsp],xmm15
$L$SEH_prolog_aes_gcm_dec_update_vaes_avx2_15:

	vbroadcasti128	ymm0,XMMWORD[$L$bswap_mask]



	vmovdqu	xmm1,XMMWORD[r12]
	vpshufb	xmm1,xmm1,xmm0
	vbroadcasti128	ymm11,XMMWORD[rsi]
	vpshufb	ymm11,ymm11,ymm0



	mov	r10d,DWORD[240+r9]
	lea	r10d,[((-20))+r10*4]




	lea	r11,[96+r10*4+r9]
	vbroadcasti128	ymm9,XMMWORD[r9]
	vbroadcasti128	ymm10,XMMWORD[r11]


	vpaddd	ymm11,ymm11,YMMWORD[$L$ctr_pattern]



	cmp	r8,127
	jbe	NEAR $L$crypt_loop_4x_done__func2

	vmovdqu	ymm7,YMMWORD[128+rdi]
	vmovdqu	ymm8,YMMWORD[((128+32))+rdi]
ALIGN	16
$L$crypt_loop_4x__func2:




	vmovdqu	ymm2,YMMWORD[$L$inc_2blocks]
	vpshufb	ymm12,ymm11,ymm0
	vpaddd	ymm11,ymm11,ymm2
	vpshufb	ymm13,ymm11,ymm0
	vpaddd	ymm11,ymm11,ymm2
	vpshufb	ymm14,ymm11,ymm0
	vpaddd	ymm11,ymm11,ymm2
	vpshufb	ymm15,ymm11,ymm0
	vpaddd	ymm11,ymm11,ymm2


	vpxor	ymm12,ymm12,ymm9
	vpxor	ymm13,ymm13,ymm9
	vpxor	ymm14,ymm14,ymm9
	vpxor	ymm15,ymm15,ymm9

	cmp	r10d,24
	jl	NEAR $L$aes128__func2
	je	NEAR $L$aes192__func2

	vbroadcasti128	ymm2,XMMWORD[((-208))+r11]
	DB	196,98,29,220,226
	DB	196,98,21,220,234
	DB	196,98,13,220,242
	DB	196,98,5,220,250

	vbroadcasti128	ymm2,XMMWORD[((-192))+r11]
	DB	196,98,29,220,226
	DB	196,98,21,220,234
	DB	196,98,13,220,242
	DB	196,98,5,220,250

$L$aes192__func2:
	vbroadcasti128	ymm2,XMMWORD[((-176))+r11]
	DB	196,98,29,220,226
	DB	196,98,21,220,234
	DB	196,98,13,220,242
	DB	196,98,5,220,250

	vbroadcasti128	ymm2,XMMWORD[((-160))+r11]
	DB	196,98,29,220,226
	DB	196,98,21,220,234
	DB	196,98,13,220,242
	DB	196,98,5,220,250

$L$aes128__func2:
	prefetcht0	[512+rcx]
	prefetcht0	[((512+64))+rcx]

	vmovdqu	ymm3,YMMWORD[rcx]
	vpshufb	ymm3,ymm3,ymm0
	vmovdqu	ymm4,YMMWORD[rdi]
	vpxor	ymm3,ymm3,ymm1
	DB	196,227,101,68,236,0
	DB	196,227,101,68,204,17
	vpunpckhqdq	ymm2,ymm3,ymm3
	vpxor	ymm2,ymm2,ymm3
	DB	196,227,109,68,247,0

	vbroadcasti128	ymm2,XMMWORD[((-144))+r11]
	DB	196,98,29,220,226
	DB	196,98,21,220,234
	DB	196,98,13,220,242
	DB	196,98,5,220,250


	vbroadcasti128	ymm2,XMMWORD[((-128))+r11]
	DB	196,98,29,220,226
	DB	196,98,21,220,234
	DB	196,98,13,220,242
	DB	196,98,5,220,250


	vmovdqu	ymm3,YMMWORD[32+rcx]
	vpshufb	ymm3,ymm3,ymm0
	vmovdqu	ymm4,YMMWORD[32+rdi]
	DB	196,227,101,68,212,0
	vpxor	ymm5,ymm5,ymm2
	DB	196,227,101,68,212,17
	vpxor	ymm1,ymm1,ymm2
	vpunpckhqdq	ymm2,ymm3,ymm3
	vpxor	ymm2,ymm2,ymm3
	DB	196,227,109,68,215,16
	vpxor	ymm6,ymm6,ymm2

	vbroadcasti128	ymm2,XMMWORD[((-112))+r11]
	DB	196,98,29,220,226
	DB	196,98,21,220,234
	DB	196,98,13,220,242
	DB	196,98,5,220,250


	vmovdqu	ymm3,YMMWORD[64+rcx]
	vpshufb	ymm3,ymm3,ymm0
	vmovdqu	ymm4,YMMWORD[64+rdi]

	vbroadcasti128	ymm2,XMMWORD[((-96))+r11]
	DB	196,98,29,220,226
	DB	196,98,21,220,234
	DB	196,98,13,220,242
	DB	196,98,5,220,250

	DB	196,227,101,68,212,0
	vpxor	ymm5,ymm5,ymm2
	DB	196,227,101,68,212,17
	vpxor	ymm1,ymm1,ymm2

	vbroadcasti128	ymm2,XMMWORD[((-80))+r11]
	DB	196,98,29,220,226
	DB	196,98,21,220,234
	DB	196,98,13,220,242
	DB	196,98,5,220,250

	vpunpckhqdq	ymm2,ymm3,ymm3
	vpxor	ymm2,ymm2,ymm3
	DB	196,195,109,68,208,0
	vpxor	ymm6,ymm6,ymm2


	vmovdqu	ymm3,YMMWORD[96+rcx]
	vpshufb	ymm3,ymm3,ymm0

	vbroadcasti128	ymm2,XMMWORD[((-64))+r11]
	DB	196,98,29,220,226
	DB	196,98,21,220,234
	DB	196,98,13,220,242
	DB	196,98,5,220,250

	vmovdqu	ymm4,YMMWORD[96+rdi]
	DB	196,227,101,68,212,0
	vpxor	ymm5,ymm5,ymm2
	DB	196,227,101,68,212,17
	vpxor	ymm1,ymm1,ymm2
	vpunpckhqdq	ymm2,ymm3,ymm3
	vpxor	ymm2,ymm2,ymm3
	DB	196,195,109,68,208,16
	vpxor	ymm6,ymm6,ymm2

	vbroadcasti128	ymm2,XMMWORD[((-48))+r11]
	DB	196,98,29,220,226
	DB	196,98,21,220,234
	DB	196,98,13,220,242
	DB	196,98,5,220,250


	vpxor	ymm6,ymm6,ymm5
	vpxor	ymm6,ymm6,ymm1


	vbroadcasti128	ymm4,XMMWORD[$L$gfpoly]
	DB	196,227,93,68,213,1
	vpshufd	ymm5,ymm5,0x4e
	vpxor	ymm6,ymm6,ymm5
	vpxor	ymm6,ymm6,ymm2

	vbroadcasti128	ymm2,XMMWORD[((-32))+r11]
	DB	196,98,29,220,226
	DB	196,98,21,220,234
	DB	196,98,13,220,242
	DB	196,98,5,220,250


	DB	196,227,93,68,214,1
	vpshufd	ymm6,ymm6,0x4e
	vpxor	ymm1,ymm1,ymm6
	vpxor	ymm1,ymm1,ymm2

	vbroadcasti128	ymm2,XMMWORD[((-16))+r11]
	DB	196,98,29,220,226
	DB	196,98,21,220,234
	DB	196,98,13,220,242
	DB	196,98,5,220,250

	vextracti128	xmm2,ymm1,1
	vpxor	xmm1,xmm1,xmm2



	vpxor	ymm2,ymm10,YMMWORD[rcx]
	vpxor	ymm3,ymm10,YMMWORD[32+rcx]
	vpxor	ymm5,ymm10,YMMWORD[64+rcx]
	vpxor	ymm6,ymm10,YMMWORD[96+rcx]
	DB	196,98,29,221,226
	DB	196,98,21,221,235
	DB	196,98,13,221,245
	DB	196,98,5,221,254
	vmovdqu	YMMWORD[rdx],ymm12
	vmovdqu	YMMWORD[32+rdx],ymm13
	vmovdqu	YMMWORD[64+rdx],ymm14
	vmovdqu	YMMWORD[96+rdx],ymm15

	sub	rcx,-128
	sub	rdx,-128
	add	r8,-128
	cmp	r8,127
	ja	NEAR $L$crypt_loop_4x__func2
$L$crypt_loop_4x_done__func2:

	test	r8,r8
	jz	NEAR $L$done__func2





	lea	rsi,[128+rdi]
	sub	rsi,r8


	vpxor	xmm5,xmm5,xmm5
	vpxor	xmm6,xmm6,xmm6
	vpxor	xmm7,xmm7,xmm7

	cmp	r8,64
	jb	NEAR $L$lessthan64bytes__func2


	vpshufb	ymm12,ymm11,ymm0
	vpaddd	ymm11,ymm11,YMMWORD[$L$inc_2blocks]
	vpshufb	ymm13,ymm11,ymm0
	vpaddd	ymm11,ymm11,YMMWORD[$L$inc_2blocks]
	vpxor	ymm12,ymm12,ymm9
	vpxor	ymm13,ymm13,ymm9
	lea	rax,[16+r9]
$L$vaesenc_loop_tail_1__func2:
	vbroadcasti128	ymm2,XMMWORD[rax]
	DB	196,98,29,220,226
	DB	196,98,21,220,234
	add	rax,16
	cmp	r11,rax
	jne	NEAR $L$vaesenc_loop_tail_1__func2
	DB	196,66,29,221,226
	DB	196,66,21,221,234


	vmovdqu	ymm2,YMMWORD[rcx]
	vmovdqu	ymm3,YMMWORD[32+rcx]
	vpxor	ymm12,ymm12,ymm2
	vpxor	ymm13,ymm13,ymm3
	vmovdqu	YMMWORD[rdx],ymm12
	vmovdqu	YMMWORD[32+rdx],ymm13


	vpshufb	ymm12,ymm2,ymm0
	vpshufb	ymm13,ymm3,ymm0
	vpxor	ymm12,ymm12,ymm1
	vmovdqu	ymm2,YMMWORD[rsi]
	vmovdqu	ymm3,YMMWORD[32+rsi]
	DB	196,227,29,68,234,0
	DB	196,227,29,68,242,1
	DB	196,227,29,68,226,16
	vpxor	ymm6,ymm6,ymm4
	DB	196,227,29,68,250,17
	DB	196,227,21,68,227,0
	vpxor	ymm5,ymm5,ymm4
	DB	196,227,21,68,227,1
	vpxor	ymm6,ymm6,ymm4
	DB	196,227,21,68,227,16
	vpxor	ymm6,ymm6,ymm4
	DB	196,227,21,68,227,17
	vpxor	ymm7,ymm7,ymm4

	add	rsi,64
	add	rcx,64
	add	rdx,64
	sub	r8,64
	jz	NEAR $L$reduce__func2

	vpxor	xmm1,xmm1,xmm1


$L$lessthan64bytes__func2:
	vpshufb	ymm12,ymm11,ymm0
	vpaddd	ymm11,ymm11,YMMWORD[$L$inc_2blocks]
	vpshufb	ymm13,ymm11,ymm0
	vpxor	ymm12,ymm12,ymm9
	vpxor	ymm13,ymm13,ymm9
	lea	rax,[16+r9]
$L$vaesenc_loop_tail_2__func2:
	vbroadcasti128	ymm2,XMMWORD[rax]
	DB	196,98,29,220,226
	DB	196,98,21,220,234
	add	rax,16
	cmp	r11,rax
	jne	NEAR $L$vaesenc_loop_tail_2__func2
	DB	196,66,29,221,226
	DB	196,66,21,221,234




	cmp	r8,32
	jb	NEAR $L$xor_one_block__func2
	je	NEAR $L$xor_two_blocks__func2

$L$xor_three_blocks__func2:
	vmovdqu	ymm2,YMMWORD[rcx]
	vmovdqu	xmm3,XMMWORD[32+rcx]
	vpxor	ymm12,ymm12,ymm2
	vpxor	xmm13,xmm13,xmm3
	vmovdqu	YMMWORD[rdx],ymm12
	vmovdqu	XMMWORD[32+rdx],xmm13

	vpshufb	ymm12,ymm2,ymm0
	vpshufb	xmm13,xmm3,xmm0
	vpxor	ymm12,ymm12,ymm1
	vmovdqu	ymm2,YMMWORD[rsi]
	vmovdqu	xmm3,XMMWORD[32+rsi]
	DB	196,227,17,68,227,0
	vpxor	ymm5,ymm5,ymm4
	DB	196,227,17,68,227,1
	vpxor	ymm6,ymm6,ymm4
	DB	196,227,17,68,227,16
	vpxor	ymm6,ymm6,ymm4
	DB	196,227,17,68,227,17
	vpxor	ymm7,ymm7,ymm4
	jmp	NEAR $L$ghash_mul_one_vec_unreduced__func2

$L$xor_two_blocks__func2:
	vmovdqu	ymm2,YMMWORD[rcx]
	vpxor	ymm12,ymm12,ymm2
	vmovdqu	YMMWORD[rdx],ymm12
	vpshufb	ymm12,ymm2,ymm0
	vpxor	ymm12,ymm12,ymm1
	vmovdqu	ymm2,YMMWORD[rsi]
	jmp	NEAR $L$ghash_mul_one_vec_unreduced__func2

$L$xor_one_block__func2:
	vmovdqu	xmm2,XMMWORD[rcx]
	vpxor	xmm12,xmm12,xmm2
	vmovdqu	XMMWORD[rdx],xmm12
	vpshufb	xmm12,xmm2,xmm0
	vpxor	xmm12,xmm12,xmm1
	vmovdqu	xmm2,XMMWORD[rsi]

$L$ghash_mul_one_vec_unreduced__func2:
	DB	196,227,29,68,226,0
	vpxor	ymm5,ymm5,ymm4
	DB	196,227,29,68,226,1
	vpxor	ymm6,ymm6,ymm4
	DB	196,227,29,68,226,16
	vpxor	ymm6,ymm6,ymm4
	DB	196,227,29,68,226,17
	vpxor	ymm7,ymm7,ymm4

$L$reduce__func2:

	vbroadcasti128	ymm2,XMMWORD[$L$gfpoly]
	DB	196,227,109,68,221,1
	vpshufd	ymm5,ymm5,0x4e
	vpxor	ymm6,ymm6,ymm5
	vpxor	ymm6,ymm6,ymm3
	DB	196,227,109,68,222,1
	vpshufd	ymm6,ymm6,0x4e
	vpxor	ymm7,ymm7,ymm6
	vpxor	ymm7,ymm7,ymm3
	vextracti128	xmm1,ymm7,1
	vpxor	xmm1,xmm1,xmm7

$L$done__func2:

	vpshufb	xmm1,xmm1,xmm0
	vmovdqu	XMMWORD[r12],xmm1

	vzeroupper
	vmovdqa	xmm6,XMMWORD[rsp]
	vmovdqa	xmm7,XMMWORD[16+rsp]
	vmovdqa	xmm8,XMMWORD[32+rsp]
	vmovdqa	xmm9,XMMWORD[48+rsp]
	vmovdqa	xmm10,XMMWORD[64+rsp]
	vmovdqa	xmm11,XMMWORD[80+rsp]
	vmovdqa	xmm12,XMMWORD[96+rsp]
	vmovdqa	xmm13,XMMWORD[112+rsp]
	vmovdqa	xmm14,XMMWORD[128+rsp]
	vmovdqa	xmm15,XMMWORD[144+rsp]
	add	rsp,160
	pop	r12
	pop	rdi
	pop	rsi
	DB	0F3h,0C3h		;repret
$L$SEH_end_aes_gcm_dec_update_vaes_avx2_16:


%endif
section	.pdata rdata align=4
ALIGN	4
	DD	$L$SEH_begin_gcm_init_vpclmulqdq_avx2_1 wrt ..imagebase
	DD	$L$SEH_end_gcm_init_vpclmulqdq_avx2_4 wrt ..imagebase
	DD	$L$SEH_info_gcm_init_vpclmulqdq_avx2_0 wrt ..imagebase

	DD	$L$SEH_begin_gcm_gmult_vpclmulqdq_avx2_1 wrt ..imagebase
	DD	$L$SEH_end_gcm_gmult_vpclmulqdq_avx2_4 wrt ..imagebase
	DD	$L$SEH_info_gcm_gmult_vpclmulqdq_avx2_0 wrt ..imagebase

	DD	$L$SEH_begin_gcm_ghash_vpclmulqdq_avx2_1 wrt ..imagebase
	DD	$L$SEH_end_gcm_ghash_vpclmulqdq_avx2_7 wrt ..imagebase
	DD	$L$SEH_info_gcm_ghash_vpclmulqdq_avx2_0 wrt ..imagebase

	DD	$L$SEH_begin_aes_gcm_enc_update_vaes_avx2_1 wrt ..imagebase
	DD	$L$SEH_end_aes_gcm_enc_update_vaes_avx2_16 wrt ..imagebase
	DD	$L$SEH_info_aes_gcm_enc_update_vaes_avx2_0 wrt ..imagebase

	DD	$L$SEH_begin_aes_gcm_dec_update_vaes_avx2_1 wrt ..imagebase
	DD	$L$SEH_end_aes_gcm_dec_update_vaes_avx2_16 wrt ..imagebase
	DD	$L$SEH_info_aes_gcm_dec_update_vaes_avx2_0 wrt ..imagebase


section	.xdata rdata align=4
ALIGN	4
$L$SEH_info_gcm_init_vpclmulqdq_avx2_0:
	DB	1
	DB	$L$SEH_prolog_gcm_init_vpclmulqdq_avx2_3-$L$SEH_begin_gcm_init_vpclmulqdq_avx2_1
	DB	3
	DB	0
	DB	$L$SEH_prolog_gcm_init_vpclmulqdq_avx2_3-$L$SEH_begin_gcm_init_vpclmulqdq_avx2_1
	DB	104
	DW	0
	DB	$L$SEH_prolog_gcm_init_vpclmulqdq_avx2_2-$L$SEH_begin_gcm_init_vpclmulqdq_avx2_1
	DB	34

ALIGN	4
$L$SEH_info_gcm_gmult_vpclmulqdq_avx2_0:
	DB	1
	DB	$L$SEH_prolog_gcm_gmult_vpclmulqdq_avx2_3-$L$SEH_begin_gcm_gmult_vpclmulqdq_avx2_1
	DB	3
	DB	0
	DB	$L$SEH_prolog_gcm_gmult_vpclmulqdq_avx2_3-$L$SEH_begin_gcm_gmult_vpclmulqdq_avx2_1
	DB	104
	DW	0
	DB	$L$SEH_prolog_gcm_gmult_vpclmulqdq_avx2_2-$L$SEH_begin_gcm_gmult_vpclmulqdq_avx2_1
	DB	34

ALIGN	4
$L$SEH_info_gcm_ghash_vpclmulqdq_avx2_0:
	DB	1
	DB	$L$SEH_prolog_gcm_ghash_vpclmulqdq_avx2_6-$L$SEH_begin_gcm_ghash_vpclmulqdq_avx2_1
	DB	9
	DB	0
	DB	$L$SEH_prolog_gcm_ghash_vpclmulqdq_avx2_6-$L$SEH_begin_gcm_ghash_vpclmulqdq_avx2_1
	DB	152
	DW	3
	DB	$L$SEH_prolog_gcm_ghash_vpclmulqdq_avx2_5-$L$SEH_begin_gcm_ghash_vpclmulqdq_avx2_1
	DB	136
	DW	2
	DB	$L$SEH_prolog_gcm_ghash_vpclmulqdq_avx2_4-$L$SEH_begin_gcm_ghash_vpclmulqdq_avx2_1
	DB	120
	DW	1
	DB	$L$SEH_prolog_gcm_ghash_vpclmulqdq_avx2_3-$L$SEH_begin_gcm_ghash_vpclmulqdq_avx2_1
	DB	104
	DW	0
	DB	$L$SEH_prolog_gcm_ghash_vpclmulqdq_avx2_2-$L$SEH_begin_gcm_ghash_vpclmulqdq_avx2_1
	DB	130

ALIGN	4
$L$SEH_info_aes_gcm_enc_update_vaes_avx2_0:
	DB	1
	DB	$L$SEH_prolog_aes_gcm_enc_update_vaes_avx2_15-$L$SEH_begin_aes_gcm_enc_update_vaes_avx2_1
	DB	25
	DB	0
	DB	$L$SEH_prolog_aes_gcm_enc_update_vaes_avx2_15-$L$SEH_begin_aes_gcm_enc_update_vaes_avx2_1
	DB	248
	DW	9
	DB	$L$SEH_prolog_aes_gcm_enc_update_vaes_avx2_14-$L$SEH_begin_aes_gcm_enc_update_vaes_avx2_1
	DB	232
	DW	8
	DB	$L$SEH_prolog_aes_gcm_enc_update_vaes_avx2_13-$L$SEH_begin_aes_gcm_enc_update_vaes_avx2_1
	DB	216
	DW	7
	DB	$L$SEH_prolog_aes_gcm_enc_update_vaes_avx2_12-$L$SEH_begin_aes_gcm_enc_update_vaes_avx2_1
	DB	200
	DW	6
	DB	$L$SEH_prolog_aes_gcm_enc_update_vaes_avx2_11-$L$SEH_begin_aes_gcm_enc_update_vaes_avx2_1
	DB	184
	DW	5
	DB	$L$SEH_prolog_aes_gcm_enc_update_vaes_avx2_10-$L$SEH_begin_aes_gcm_enc_update_vaes_avx2_1
	DB	168
	DW	4
	DB	$L$SEH_prolog_aes_gcm_enc_update_vaes_avx2_9-$L$SEH_begin_aes_gcm_enc_update_vaes_avx2_1
	DB	152
	DW	3
	DB	$L$SEH_prolog_aes_gcm_enc_update_vaes_avx2_8-$L$SEH_begin_aes_gcm_enc_update_vaes_avx2_1
	DB	136
	DW	2
	DB	$L$SEH_prolog_aes_gcm_enc_update_vaes_avx2_7-$L$SEH_begin_aes_gcm_enc_update_vaes_avx2_1
	DB	120
	DW	1
	DB	$L$SEH_prolog_aes_gcm_enc_update_vaes_avx2_6-$L$SEH_begin_aes_gcm_enc_update_vaes_avx2_1
	DB	104
	DW	0
	DB	$L$SEH_prolog_aes_gcm_enc_update_vaes_avx2_5-$L$SEH_begin_aes_gcm_enc_update_vaes_avx2_1
	DB	1
	DW	20
	DB	$L$SEH_prolog_aes_gcm_enc_update_vaes_avx2_4-$L$SEH_begin_aes_gcm_enc_update_vaes_avx2_1
	DB	192
	DB	$L$SEH_prolog_aes_gcm_enc_update_vaes_avx2_3-$L$SEH_begin_aes_gcm_enc_update_vaes_avx2_1
	DB	112
	DB	$L$SEH_prolog_aes_gcm_enc_update_vaes_avx2_2-$L$SEH_begin_aes_gcm_enc_update_vaes_avx2_1
	DB	96

ALIGN	4
$L$SEH_info_aes_gcm_dec_update_vaes_avx2_0:
	DB	1
	DB	$L$SEH_prolog_aes_gcm_dec_update_vaes_avx2_15-$L$SEH_begin_aes_gcm_dec_update_vaes_avx2_1
	DB	25
	DB	0
	DB	$L$SEH_prolog_aes_gcm_dec_update_vaes_avx2_15-$L$SEH_begin_aes_gcm_dec_update_vaes_avx2_1
	DB	248
	DW	9
	DB	$L$SEH_prolog_aes_gcm_dec_update_vaes_avx2_14-$L$SEH_begin_aes_gcm_dec_update_vaes_avx2_1
	DB	232
	DW	8
	DB	$L$SEH_prolog_aes_gcm_dec_update_vaes_avx2_13-$L$SEH_begin_aes_gcm_dec_update_vaes_avx2_1
	DB	216
	DW	7
	DB	$L$SEH_prolog_aes_gcm_dec_update_vaes_avx2_12-$L$SEH_begin_aes_gcm_dec_update_vaes_avx2_1
	DB	200
	DW	6
	DB	$L$SEH_prolog_aes_gcm_dec_update_vaes_avx2_11-$L$SEH_begin_aes_gcm_dec_update_vaes_avx2_1
	DB	184
	DW	5
	DB	$L$SEH_prolog_aes_gcm_dec_update_vaes_avx2_10-$L$SEH_begin_aes_gcm_dec_update_vaes_avx2_1
	DB	168
	DW	4
	DB	$L$SEH_prolog_aes_gcm_dec_update_vaes_avx2_9-$L$SEH_begin_aes_gcm_dec_update_vaes_avx2_1
	DB	152
	DW	3
	DB	$L$SEH_prolog_aes_gcm_dec_update_vaes_avx2_8-$L$SEH_begin_aes_gcm_dec_update_vaes_avx2_1
	DB	136
	DW	2
	DB	$L$SEH_prolog_aes_gcm_dec_update_vaes_avx2_7-$L$SEH_begin_aes_gcm_dec_update_vaes_avx2_1
	DB	120
	DW	1
	DB	$L$SEH_prolog_aes_gcm_dec_update_vaes_avx2_6-$L$SEH_begin_aes_gcm_dec_update_vaes_avx2_1
	DB	104
	DW	0
	DB	$L$SEH_prolog_aes_gcm_dec_update_vaes_avx2_5-$L$SEH_begin_aes_gcm_dec_update_vaes_avx2_1
	DB	1
	DW	20
	DB	$L$SEH_prolog_aes_gcm_dec_update_vaes_avx2_4-$L$SEH_begin_aes_gcm_dec_update_vaes_avx2_1
	DB	192
	DB	$L$SEH_prolog_aes_gcm_dec_update_vaes_avx2_3-$L$SEH_begin_aes_gcm_dec_update_vaes_avx2_1
	DB	112
	DB	$L$SEH_prolog_aes_gcm_dec_update_vaes_avx2_2-$L$SEH_begin_aes_gcm_dec_update_vaes_avx2_1
	DB	96
%else
; Work around https://bugzilla.nasm.us/show_bug.cgi?id=3392738
ret
%endif
