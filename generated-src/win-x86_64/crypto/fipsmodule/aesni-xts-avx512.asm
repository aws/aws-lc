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

global	aes_hw_xts_encrypt_avx512


ALIGN	32
aes_hw_xts_encrypt_avx512:
	mov	QWORD[8+rsp],rdi	;WIN64 prologue
	mov	QWORD[16+rsp],rsi
	mov	rax,rsp
$L$SEH_begin_aes_hw_xts_encrypt_avx512:
	mov	rdi,rcx
	mov	rsi,rdx
	mov	rdx,r8
	mov	rcx,r9
	mov	r8,QWORD[40+rsp]
	mov	r9,QWORD[48+rsp]



DB	243,15,30,250
	push	rbp
	mov	rbp,rsp
	sub	rsp,312
	and	rsp,0xffffffffffffffc0
	mov	QWORD[288+rsp],rbx
	mov	QWORD[((288 + 8))+rsp],rdi
	mov	QWORD[((288 + 16))+rsp],rsi
	vmovdqa	XMMWORD[(128 + 0)+rsp],xmm6
	vmovdqa	XMMWORD[(128 + 16)+rsp],xmm7
	vmovdqa	XMMWORD[(128 + 32)+rsp],xmm8
	vmovdqa	XMMWORD[(128 + 48)+rsp],xmm9
	vmovdqa	XMMWORD[(128 + 64)+rsp],xmm10
	vmovdqa	XMMWORD[(128 + 80)+rsp],xmm11
	vmovdqa	XMMWORD[(128 + 96)+rsp],xmm12
	vmovdqa	XMMWORD[(128 + 112)+rsp],xmm13
	vmovdqa	XMMWORD[(128 + 128)+rsp],xmm14
	vmovdqa	XMMWORD[(128 + 144)+rsp],xmm15
	mov	r10,0x87
	vmovdqu	xmm1,XMMWORD[r9]
	vpxor	xmm1,xmm1,XMMWORD[r8]
	vaesenc	xmm1,xmm1,XMMWORD[16+r8]
	vaesenc	xmm1,xmm1,XMMWORD[32+r8]
	vaesenc	xmm1,xmm1,XMMWORD[48+r8]
	vaesenc	xmm1,xmm1,XMMWORD[64+r8]
	vaesenc	xmm1,xmm1,XMMWORD[80+r8]
	vaesenc	xmm1,xmm1,XMMWORD[96+r8]
	vaesenc	xmm1,xmm1,XMMWORD[112+r8]
	vaesenc	xmm1,xmm1,XMMWORD[128+r8]
	vaesenc	xmm1,xmm1,XMMWORD[144+r8]
	vaesenc	xmm1,xmm1,XMMWORD[160+r8]
	vaesenc	xmm1,xmm1,XMMWORD[176+r8]
	vaesenc	xmm1,xmm1,XMMWORD[192+r8]
	vaesenc	xmm1,xmm1,XMMWORD[208+r8]
	vaesenclast	xmm1,xmm1,XMMWORD[224+r8]
	vmovdqa	XMMWORD[rsp],xmm1
	mov	QWORD[((8 + 40))+rbp],rdi
	mov	QWORD[((8 + 48))+rbp],rsi

	cmp	rdx,0x80
	jl	NEAR $L$_less_than_128_bytes_hEgxyDlCngwrfFe
	vpbroadcastq	zmm25,r10
	cmp	rdx,0x100
	jge	NEAR $L$_start_by16_hEgxyDlCngwrfFe
	cmp	rdx,0x80
	jge	NEAR $L$_start_by8_hEgxyDlCngwrfFe

$L$_do_n_blocks_hEgxyDlCngwrfFe:
	cmp	rdx,0x0
	je	NEAR $L$_ret_hEgxyDlCngwrfFe
	cmp	rdx,0x70
	jge	NEAR $L$_remaining_num_blocks_is_7_hEgxyDlCngwrfFe
	cmp	rdx,0x60
	jge	NEAR $L$_remaining_num_blocks_is_6_hEgxyDlCngwrfFe
	cmp	rdx,0x50
	jge	NEAR $L$_remaining_num_blocks_is_5_hEgxyDlCngwrfFe
	cmp	rdx,0x40
	jge	NEAR $L$_remaining_num_blocks_is_4_hEgxyDlCngwrfFe
	cmp	rdx,0x30
	jge	NEAR $L$_remaining_num_blocks_is_3_hEgxyDlCngwrfFe
	cmp	rdx,0x20
	jge	NEAR $L$_remaining_num_blocks_is_2_hEgxyDlCngwrfFe
	cmp	rdx,0x10
	jge	NEAR $L$_remaining_num_blocks_is_1_hEgxyDlCngwrfFe
	vmovdqa	xmm8,xmm0
	vmovdqa	xmm0,xmm9
	jmp	NEAR $L$_steal_cipher_hEgxyDlCngwrfFe

$L$_remaining_num_blocks_is_7_hEgxyDlCngwrfFe:
	mov	r8,0x0000ffffffffffff
	kmovq	k1,r8
	vmovdqu8	zmm1,ZMMWORD[rdi]
	vmovdqu8	zmm2{k1},[64+rdi]
	add	rdi,0x70
	vbroadcasti32x4	zmm0,ZMMWORD[rcx]
	vpternlogq	zmm1,zmm9,zmm0,0x96
	vpternlogq	zmm2,zmm10,zmm0,0x96
	vbroadcasti32x4	zmm0,ZMMWORD[16+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[32+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[48+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208

	vbroadcasti32x4	zmm0,ZMMWORD[64+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[80+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[96+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[112+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[128+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[144+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[160+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[176+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[192+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[208+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[224+rcx]
	DB	98,242,117,72,221,200
	DB	98,242,109,72,221,208
	vpxorq	zmm1,zmm1,zmm9
	vpxorq	zmm2,zmm2,zmm10
	vmovdqu8	ZMMWORD[rsi],zmm1
	vmovdqu8	ZMMWORD[64+rsi]{k1},zmm2
	add	rsi,0x70
	vextracti32x4	xmm8,zmm2,0x2
	vextracti32x4	xmm0,zmm10,0x3
	and	rdx,0xf
	je	NEAR $L$_ret_hEgxyDlCngwrfFe
	jmp	NEAR $L$_steal_cipher_hEgxyDlCngwrfFe

$L$_remaining_num_blocks_is_6_hEgxyDlCngwrfFe:
	vmovdqu8	zmm1,ZMMWORD[rdi]
	vmovdqu8	ymm2,YMMWORD[64+rdi]
	add	rdi,0x60
	vbroadcasti32x4	zmm0,ZMMWORD[rcx]
	vpternlogq	zmm1,zmm9,zmm0,0x96
	vpternlogq	zmm2,zmm10,zmm0,0x96
	vbroadcasti32x4	zmm0,ZMMWORD[16+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[32+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[48+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208

	vbroadcasti32x4	zmm0,ZMMWORD[64+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[80+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[96+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[112+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[128+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[144+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[160+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[176+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[192+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[208+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[224+rcx]
	DB	98,242,117,72,221,200
	DB	98,242,109,72,221,208
	vpxorq	zmm1,zmm1,zmm9
	vpxorq	zmm2,zmm2,zmm10
	vmovdqu8	ZMMWORD[rsi],zmm1
	vmovdqu8	YMMWORD[64+rsi],ymm2
	add	rsi,0x60
	vextracti32x4	xmm8,zmm2,0x1
	vextracti32x4	xmm0,zmm10,0x2
	and	rdx,0xf
	je	NEAR $L$_ret_hEgxyDlCngwrfFe
	jmp	NEAR $L$_steal_cipher_hEgxyDlCngwrfFe

$L$_remaining_num_blocks_is_5_hEgxyDlCngwrfFe:
	vmovdqu8	zmm1,ZMMWORD[rdi]
	vmovdqu	xmm2,XMMWORD[64+rdi]
	add	rdi,0x50
	vbroadcasti32x4	zmm0,ZMMWORD[rcx]
	vpternlogq	zmm1,zmm9,zmm0,0x96
	vpternlogq	zmm2,zmm10,zmm0,0x96
	vbroadcasti32x4	zmm0,ZMMWORD[16+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[32+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[48+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208

	vbroadcasti32x4	zmm0,ZMMWORD[64+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[80+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[96+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[112+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[128+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[144+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[160+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[176+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[192+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[208+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[224+rcx]
	DB	98,242,117,72,221,200
	DB	98,242,109,72,221,208
	vpxorq	zmm1,zmm1,zmm9
	vpxorq	zmm2,zmm2,zmm10
	vmovdqu8	ZMMWORD[rsi],zmm1
	vmovdqu	XMMWORD[64+rsi],xmm2
	add	rsi,0x50
	vmovdqa	xmm8,xmm2
	vextracti32x4	xmm0,zmm10,0x1
	and	rdx,0xf
	je	NEAR $L$_ret_hEgxyDlCngwrfFe
	jmp	NEAR $L$_steal_cipher_hEgxyDlCngwrfFe

$L$_remaining_num_blocks_is_4_hEgxyDlCngwrfFe:
	vmovdqu8	zmm1,ZMMWORD[rdi]
	add	rdi,0x40
	vbroadcasti32x4	zmm0,ZMMWORD[rcx]
	vpternlogq	zmm1,zmm9,zmm0,0x96
	vbroadcasti32x4	zmm0,ZMMWORD[16+rcx]
	DB	98,242,117,72,220,200
	vbroadcasti32x4	zmm0,ZMMWORD[32+rcx]
	DB	98,242,117,72,220,200
	vbroadcasti32x4	zmm0,ZMMWORD[48+rcx]
	DB	98,242,117,72,220,200
	vbroadcasti32x4	zmm0,ZMMWORD[64+rcx]
	DB	98,242,117,72,220,200
	vbroadcasti32x4	zmm0,ZMMWORD[80+rcx]
	DB	98,242,117,72,220,200
	vbroadcasti32x4	zmm0,ZMMWORD[96+rcx]
	DB	98,242,117,72,220,200
	vbroadcasti32x4	zmm0,ZMMWORD[112+rcx]
	DB	98,242,117,72,220,200
	vbroadcasti32x4	zmm0,ZMMWORD[128+rcx]
	DB	98,242,117,72,220,200
	vbroadcasti32x4	zmm0,ZMMWORD[144+rcx]
	DB	98,242,117,72,220,200
	vbroadcasti32x4	zmm0,ZMMWORD[160+rcx]
	DB	98,242,117,72,220,200
	vbroadcasti32x4	zmm0,ZMMWORD[176+rcx]
	DB	98,242,117,72,220,200
	vbroadcasti32x4	zmm0,ZMMWORD[192+rcx]
	DB	98,242,117,72,220,200
	vbroadcasti32x4	zmm0,ZMMWORD[208+rcx]
	DB	98,242,117,72,220,200
	vbroadcasti32x4	zmm0,ZMMWORD[224+rcx]
	DB	98,242,117,72,221,200
	vpxorq	zmm1,zmm1,zmm9
	vmovdqu8	ZMMWORD[rsi],zmm1
	add	rsi,0x40
	vextracti32x4	xmm8,zmm1,0x3
	vmovdqa64	xmm0,xmm10
	and	rdx,0xf
	je	NEAR $L$_ret_hEgxyDlCngwrfFe
	jmp	NEAR $L$_steal_cipher_hEgxyDlCngwrfFe
$L$_remaining_num_blocks_is_3_hEgxyDlCngwrfFe:
	mov	r8,-1
	shr	r8,0x10
	kmovq	k1,r8
	vmovdqu8	zmm1{k1},[rdi]
	add	rdi,0x30
	vbroadcasti32x4	zmm0,ZMMWORD[rcx]
	vpternlogq	zmm1,zmm9,zmm0,0x96
	vbroadcasti32x4	zmm0,ZMMWORD[16+rcx]
	DB	98,242,117,72,220,200
	vbroadcasti32x4	zmm0,ZMMWORD[32+rcx]
	DB	98,242,117,72,220,200
	vbroadcasti32x4	zmm0,ZMMWORD[48+rcx]
	DB	98,242,117,72,220,200
	vbroadcasti32x4	zmm0,ZMMWORD[64+rcx]
	DB	98,242,117,72,220,200
	vbroadcasti32x4	zmm0,ZMMWORD[80+rcx]
	DB	98,242,117,72,220,200
	vbroadcasti32x4	zmm0,ZMMWORD[96+rcx]
	DB	98,242,117,72,220,200
	vbroadcasti32x4	zmm0,ZMMWORD[112+rcx]
	DB	98,242,117,72,220,200
	vbroadcasti32x4	zmm0,ZMMWORD[128+rcx]
	DB	98,242,117,72,220,200
	vbroadcasti32x4	zmm0,ZMMWORD[144+rcx]
	DB	98,242,117,72,220,200
	vbroadcasti32x4	zmm0,ZMMWORD[160+rcx]
	DB	98,242,117,72,220,200
	vbroadcasti32x4	zmm0,ZMMWORD[176+rcx]
	DB	98,242,117,72,220,200
	vbroadcasti32x4	zmm0,ZMMWORD[192+rcx]
	DB	98,242,117,72,220,200
	vbroadcasti32x4	zmm0,ZMMWORD[208+rcx]
	DB	98,242,117,72,220,200
	vbroadcasti32x4	zmm0,ZMMWORD[224+rcx]
	DB	98,242,117,72,221,200
	vpxorq	zmm1,zmm1,zmm9
	vmovdqu8	ZMMWORD[rsi]{k1},zmm1
	add	rsi,0x30
	vextracti32x4	xmm8,zmm1,0x2
	vextracti32x4	xmm0,zmm9,0x3
	and	rdx,0xf
	je	NEAR $L$_ret_hEgxyDlCngwrfFe
	jmp	NEAR $L$_steal_cipher_hEgxyDlCngwrfFe
$L$_remaining_num_blocks_is_2_hEgxyDlCngwrfFe:
	vmovdqu8	ymm1,YMMWORD[rdi]
	add	rdi,0x20
	vbroadcasti32x4	ymm0,YMMWORD[rcx]
	vpternlogq	ymm1,ymm9,ymm0,0x96
	vbroadcasti32x4	ymm0,YMMWORD[16+rcx]
	DB	98,242,117,40,220,200
	vbroadcasti32x4	ymm0,YMMWORD[32+rcx]
	DB	98,242,117,40,220,200
	vbroadcasti32x4	ymm0,YMMWORD[48+rcx]
	DB	98,242,117,40,220,200
	vbroadcasti32x4	ymm0,YMMWORD[64+rcx]
	DB	98,242,117,40,220,200
	vbroadcasti32x4	ymm0,YMMWORD[80+rcx]
	DB	98,242,117,40,220,200
	vbroadcasti32x4	ymm0,YMMWORD[96+rcx]
	DB	98,242,117,40,220,200
	vbroadcasti32x4	ymm0,YMMWORD[112+rcx]
	DB	98,242,117,40,220,200
	vbroadcasti32x4	ymm0,YMMWORD[128+rcx]
	DB	98,242,117,40,220,200
	vbroadcasti32x4	ymm0,YMMWORD[144+rcx]
	DB	98,242,117,40,220,200
	vbroadcasti32x4	ymm0,YMMWORD[160+rcx]
	DB	98,242,117,40,220,200
	vbroadcasti32x4	ymm0,YMMWORD[176+rcx]
	DB	98,242,117,40,220,200
	vbroadcasti32x4	ymm0,YMMWORD[192+rcx]
	DB	98,242,117,40,220,200
	vbroadcasti32x4	ymm0,YMMWORD[208+rcx]
	DB	98,242,117,40,220,200
	vbroadcasti32x4	ymm0,YMMWORD[224+rcx]
	DB	98,242,117,40,221,200
	vpxorq	ymm1,ymm1,ymm9
	vmovdqu	YMMWORD[rsi],ymm1
	add	rsi,0x20
	vextracti32x4	xmm8,zmm1,0x1
	vextracti32x4	xmm0,zmm9,0x2
	and	rdx,0xf
	je	NEAR $L$_ret_hEgxyDlCngwrfFe
	jmp	NEAR $L$_steal_cipher_hEgxyDlCngwrfFe
$L$_remaining_num_blocks_is_1_hEgxyDlCngwrfFe:
	vmovdqu	xmm1,XMMWORD[rdi]
	add	rdi,0x10
	vpxor	xmm1,xmm1,xmm9
	vpxor	xmm1,xmm1,XMMWORD[rcx]
	vaesenc	xmm1,xmm1,XMMWORD[16+rcx]
	vaesenc	xmm1,xmm1,XMMWORD[32+rcx]
	vaesenc	xmm1,xmm1,XMMWORD[48+rcx]
	vaesenc	xmm1,xmm1,XMMWORD[64+rcx]
	vaesenc	xmm1,xmm1,XMMWORD[80+rcx]
	vaesenc	xmm1,xmm1,XMMWORD[96+rcx]
	vaesenc	xmm1,xmm1,XMMWORD[112+rcx]
	vaesenc	xmm1,xmm1,XMMWORD[128+rcx]
	vaesenc	xmm1,xmm1,XMMWORD[144+rcx]
	vaesenc	xmm1,xmm1,XMMWORD[160+rcx]
	vaesenc	xmm1,xmm1,XMMWORD[176+rcx]
	vaesenc	xmm1,xmm1,XMMWORD[192+rcx]
	vaesenc	xmm1,xmm1,XMMWORD[208+rcx]
	vaesenclast	xmm1,xmm1,XMMWORD[224+rcx]
	vpxor	xmm1,xmm1,xmm9
	vmovdqu	XMMWORD[rsi],xmm1
	add	rsi,0x10
	vmovdqa	xmm8,xmm1
	vextracti32x4	xmm0,zmm9,0x1
	and	rdx,0xf
	je	NEAR $L$_ret_hEgxyDlCngwrfFe
	jmp	NEAR $L$_steal_cipher_hEgxyDlCngwrfFe



$L$_start_by16_hEgxyDlCngwrfFe:
	vbroadcasti32x4	zmm0,ZMMWORD[rsp]
	vbroadcasti32x4	zmm8,ZMMWORD[shufb_15_7]
	mov	r8,0xaa
	kmovq	k2,r8
	vpshufb	zmm1,zmm0,zmm8


	vpsllvq	zmm4,zmm0,ZMMWORD[const_dq3210]
	vpsrlvq	zmm2,zmm1,ZMMWORD[const_dq5678]
	DB	98,147,109,72,68,217,0
	vpxorq	zmm4{k2},zmm4,zmm2
	vpxord	zmm9,zmm3,zmm4


	vpsllvq	zmm5,zmm0,ZMMWORD[const_dq7654]
	vpsrlvq	zmm6,zmm1,ZMMWORD[const_dq1234]
	DB	98,147,77,72,68,249,0
	vpxorq	zmm5{k2},zmm5,zmm6
	vpxord	zmm10,zmm7,zmm5


	vpsrldq	zmm13,zmm9,0xf
	DB	98,19,21,72,68,241,0
	vpslldq	zmm11,zmm9,0x1
	vpxord	zmm11,zmm11,zmm14


	vpsrldq	zmm15,zmm10,0xf
	DB	98,131,5,72,68,193,0
	vpslldq	zmm12,zmm10,0x1
	vpxord	zmm12,zmm12,zmm16

$L$_main_loop_run_16_hEgxyDlCngwrfFe:
	vmovdqu8	zmm1,ZMMWORD[rdi]
	vmovdqu8	zmm2,ZMMWORD[64+rdi]
	vmovdqu8	zmm3,ZMMWORD[128+rdi]
	vmovdqu8	zmm4,ZMMWORD[192+rdi]
	add	rdi,0x100
	vpxorq	zmm1,zmm1,zmm9
	vpxorq	zmm2,zmm2,zmm10
	vpxorq	zmm3,zmm3,zmm11
	vpxorq	zmm4,zmm4,zmm12
	vbroadcasti32x4	zmm0,ZMMWORD[rcx]
	vpxorq	zmm1,zmm1,zmm0
	vpxorq	zmm2,zmm2,zmm0
	vpxorq	zmm3,zmm3,zmm0
	vpxorq	zmm4,zmm4,zmm0
	vpsrldq	zmm13,zmm11,0xf
	DB	98,19,21,72,68,241,0
	vpslldq	zmm15,zmm11,0x1
	vpxord	zmm15,zmm15,zmm14
	vbroadcasti32x4	zmm0,ZMMWORD[16+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208
	DB	98,242,101,72,220,216
	DB	98,242,93,72,220,224
	vbroadcasti32x4	zmm0,ZMMWORD[32+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208
	DB	98,242,101,72,220,216
	DB	98,242,93,72,220,224
	vbroadcasti32x4	zmm0,ZMMWORD[48+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208
	DB	98,242,101,72,220,216
	DB	98,242,93,72,220,224
	vpsrldq	zmm13,zmm12,0xf
	DB	98,19,21,72,68,241,0
	vpslldq	zmm16,zmm12,0x1
	vpxord	zmm16,zmm16,zmm14
	vbroadcasti32x4	zmm0,ZMMWORD[64+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208
	DB	98,242,101,72,220,216
	DB	98,242,93,72,220,224
	vbroadcasti32x4	zmm0,ZMMWORD[80+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208
	DB	98,242,101,72,220,216
	DB	98,242,93,72,220,224
	vbroadcasti32x4	zmm0,ZMMWORD[96+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208
	DB	98,242,101,72,220,216
	DB	98,242,93,72,220,224
	vpsrldq	zmm13,zmm15,0xf
	DB	98,19,21,72,68,241,0
	vpslldq	zmm17,zmm15,0x1
	vpxord	zmm17,zmm17,zmm14
	vbroadcasti32x4	zmm0,ZMMWORD[112+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208
	DB	98,242,101,72,220,216
	DB	98,242,93,72,220,224
	vbroadcasti32x4	zmm0,ZMMWORD[128+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208
	DB	98,242,101,72,220,216
	DB	98,242,93,72,220,224
	vbroadcasti32x4	zmm0,ZMMWORD[144+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208
	DB	98,242,101,72,220,216
	DB	98,242,93,72,220,224
	vpsrldq	zmm13,zmm16,0xf
	DB	98,19,21,72,68,241,0
	vpslldq	zmm18,zmm16,0x1
	vpxord	zmm18,zmm18,zmm14
	vbroadcasti32x4	zmm0,ZMMWORD[160+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208
	DB	98,242,101,72,220,216
	DB	98,242,93,72,220,224
	vbroadcasti32x4	zmm0,ZMMWORD[176+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208
	DB	98,242,101,72,220,216
	DB	98,242,93,72,220,224
	vbroadcasti32x4	zmm0,ZMMWORD[192+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208
	DB	98,242,101,72,220,216
	DB	98,242,93,72,220,224
	vbroadcasti32x4	zmm0,ZMMWORD[208+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208
	DB	98,242,101,72,220,216
	DB	98,242,93,72,220,224
	vbroadcasti32x4	zmm0,ZMMWORD[224+rcx]
	DB	98,242,117,72,221,200
	DB	98,242,109,72,221,208
	DB	98,242,101,72,221,216
	DB	98,242,93,72,221,224
	vpxorq	zmm1,zmm1,zmm9
	vpxorq	zmm2,zmm2,zmm10
	vpxorq	zmm3,zmm3,zmm11
	vpxorq	zmm4,zmm4,zmm12

	vmovdqa32	zmm9,zmm15
	vmovdqa32	zmm10,zmm16
	vmovdqa32	zmm11,zmm17
	vmovdqa32	zmm12,zmm18
	vmovdqu8	ZMMWORD[rsi],zmm1
	vmovdqu8	ZMMWORD[64+rsi],zmm2
	vmovdqu8	ZMMWORD[128+rsi],zmm3
	vmovdqu8	ZMMWORD[192+rsi],zmm4
	add	rsi,0x100
	sub	rdx,0x100
	cmp	rdx,0x100
	jae	NEAR $L$_main_loop_run_16_hEgxyDlCngwrfFe
	cmp	rdx,0x80
	jae	NEAR $L$_main_loop_run_8_hEgxyDlCngwrfFe
	vextracti32x4	xmm0,zmm4,0x3
	jmp	NEAR $L$_do_n_blocks_hEgxyDlCngwrfFe

$L$_start_by8_hEgxyDlCngwrfFe:
	vbroadcasti32x4	zmm0,ZMMWORD[rsp]
	vbroadcasti32x4	zmm8,ZMMWORD[shufb_15_7]
	mov	r8,0xaa
	kmovq	k2,r8
	vpshufb	zmm1,zmm0,zmm8
	vpsllvq	zmm4,zmm0,ZMMWORD[const_dq3210]
	vpsrlvq	zmm2,zmm1,ZMMWORD[const_dq5678]
	DB	98,147,109,72,68,217,0
	vpxorq	zmm4{k2},zmm4,zmm2
	vpxord	zmm9,zmm3,zmm4
	vpsllvq	zmm5,zmm0,ZMMWORD[const_dq7654]
	vpsrlvq	zmm6,zmm1,ZMMWORD[const_dq1234]
	DB	98,147,77,72,68,249,0
	vpxorq	zmm5{k2},zmm5,zmm6
	vpxord	zmm10,zmm7,zmm5

$L$_main_loop_run_8_hEgxyDlCngwrfFe:
	vmovdqu8	zmm1,ZMMWORD[rdi]
	vmovdqu8	zmm2,ZMMWORD[64+rdi]
	add	rdi,0x80
	vbroadcasti32x4	zmm0,ZMMWORD[rcx]
	vpternlogq	zmm1,zmm9,zmm0,0x96
	vpternlogq	zmm2,zmm10,zmm0,0x96
	vpsrldq	zmm13,zmm9,0xf
	DB	98,19,21,72,68,241,0
	vpslldq	zmm15,zmm9,0x1
	vpxord	zmm15,zmm15,zmm14
	vbroadcasti32x4	zmm0,ZMMWORD[16+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[32+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[48+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208
	vpsrldq	zmm13,zmm10,0xf
	DB	98,19,21,72,68,241,0
	vpslldq	zmm16,zmm10,0x1
	vpxord	zmm16,zmm16,zmm14

	vbroadcasti32x4	zmm0,ZMMWORD[64+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[80+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[96+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[112+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[128+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[144+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[160+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[176+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[192+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[208+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[224+rcx]
	DB	98,242,117,72,221,200
	DB	98,242,109,72,221,208
	vpxorq	zmm1,zmm1,zmm9
	vpxorq	zmm2,zmm2,zmm10
	vmovdqa32	zmm9,zmm15
	vmovdqa32	zmm10,zmm16
	vmovdqu8	ZMMWORD[rsi],zmm1
	vmovdqu8	ZMMWORD[64+rsi],zmm2
	add	rsi,0x80
	sub	rdx,0x80
	cmp	rdx,0x80
	jae	NEAR $L$_main_loop_run_8_hEgxyDlCngwrfFe
	vextracti32x4	xmm0,zmm2,0x3
	jmp	NEAR $L$_do_n_blocks_hEgxyDlCngwrfFe

$L$_steal_cipher_hEgxyDlCngwrfFe:
	vmovdqa	xmm2,xmm8
	lea	rax,[vpshufb_shf_table]
	vmovdqu	xmm10,XMMWORD[rdx*1+rax]
	vpshufb	xmm8,xmm8,xmm10
	vmovdqu	xmm3,XMMWORD[((-16))+rdx*1+rdi]
	vmovdqu	XMMWORD[(-16)+rdx*1+rsi],xmm8
	lea	rax,[vpshufb_shf_table]
	add	rax,16
	sub	rax,rdx
	vmovdqu	xmm10,XMMWORD[rax]
	vpxor	xmm10,xmm10,XMMWORD[mask1]
	vpshufb	xmm3,xmm3,xmm10
	vpblendvb	xmm3,xmm3,xmm2,xmm10
	vpxor	xmm8,xmm3,xmm0
	vpxor	xmm8,xmm8,XMMWORD[rcx]
	vaesenc	xmm8,xmm8,XMMWORD[16+rcx]
	vaesenc	xmm8,xmm8,XMMWORD[32+rcx]
	vaesenc	xmm8,xmm8,XMMWORD[48+rcx]
	vaesenc	xmm8,xmm8,XMMWORD[64+rcx]
	vaesenc	xmm8,xmm8,XMMWORD[80+rcx]
	vaesenc	xmm8,xmm8,XMMWORD[96+rcx]
	vaesenc	xmm8,xmm8,XMMWORD[112+rcx]
	vaesenc	xmm8,xmm8,XMMWORD[128+rcx]
	vaesenc	xmm8,xmm8,XMMWORD[144+rcx]
	vaesenc	xmm8,xmm8,XMMWORD[160+rcx]
	vaesenc	xmm8,xmm8,XMMWORD[176+rcx]
	vaesenc	xmm8,xmm8,XMMWORD[192+rcx]
	vaesenc	xmm8,xmm8,XMMWORD[208+rcx]
	vaesenclast	xmm8,xmm8,XMMWORD[224+rcx]
	vpxor	xmm8,xmm8,xmm0
	vmovdqu	XMMWORD[(-16)+rsi],xmm8

$L$_ret_hEgxyDlCngwrfFe:
	mov	rbx,QWORD[288+rsp]
	xor	r8,r8
	mov	QWORD[288+rsp],r8
	vpxorq	zmm0,zmm0,zmm0
	mov	rdi,QWORD[((288 + 8))+rsp]
	mov	QWORD[((288 + 8))+rsp],r8
	mov	rsi,QWORD[((288 + 16))+rsp]
	mov	QWORD[((288 + 16))+rsp],r8

	vmovdqa	xmm6,XMMWORD[((128 + 0))+rsp]
	vmovdqa	xmm7,XMMWORD[((128 + 16))+rsp]
	vmovdqa	xmm8,XMMWORD[((128 + 32))+rsp]
	vmovdqa	xmm9,XMMWORD[((128 + 48))+rsp]


	vmovdqa64	ZMMWORD[128+rsp],zmm0

	vmovdqa	xmm10,XMMWORD[((128 + 64))+rsp]
	vmovdqa	xmm11,XMMWORD[((128 + 80))+rsp]
	vmovdqa	xmm12,XMMWORD[((128 + 96))+rsp]
	vmovdqa	xmm13,XMMWORD[((128 + 112))+rsp]


	vmovdqa64	ZMMWORD[(128 + 64)+rsp],zmm0

	vmovdqa	xmm14,XMMWORD[((128 + 128))+rsp]
	vmovdqa	xmm15,XMMWORD[((128 + 144))+rsp]



	vmovdqa	YMMWORD[(128 + 128)+rsp],ymm0
	mov	rsp,rbp
	pop	rbp
	vzeroupper
	mov	rdi,QWORD[8+rsp]	;WIN64 epilogue
	mov	rsi,QWORD[16+rsp]
	DB	0F3h,0C3h		;repret

$L$_less_than_128_bytes_hEgxyDlCngwrfFe:
	vpbroadcastq	zmm25,r10
	cmp	rdx,0x10
	jb	NEAR $L$_ret_hEgxyDlCngwrfFe
	vbroadcasti32x4	zmm0,ZMMWORD[rsp]
	vbroadcasti32x4	zmm8,ZMMWORD[shufb_15_7]
	mov	r8d,0xaa
	kmovq	k2,r8
	mov	r8,rdx
	and	r8,0x70
	cmp	r8,0x60
	je	NEAR $L$_num_blocks_is_6_hEgxyDlCngwrfFe
	cmp	r8,0x50
	je	NEAR $L$_num_blocks_is_5_hEgxyDlCngwrfFe
	cmp	r8,0x40
	je	NEAR $L$_num_blocks_is_4_hEgxyDlCngwrfFe
	cmp	r8,0x30
	je	NEAR $L$_num_blocks_is_3_hEgxyDlCngwrfFe
	cmp	r8,0x20
	je	NEAR $L$_num_blocks_is_2_hEgxyDlCngwrfFe
	cmp	r8,0x10
	je	NEAR $L$_num_blocks_is_1_hEgxyDlCngwrfFe

$L$_num_blocks_is_7_hEgxyDlCngwrfFe:
	vpshufb	zmm1,zmm0,zmm8
	vpsllvq	zmm4,zmm0,ZMMWORD[const_dq3210]
	vpsrlvq	zmm2,zmm1,ZMMWORD[const_dq5678]
	DB	98,147,109,72,68,217,0
	vpxorq	zmm4{k2},zmm4,zmm2
	vpxord	zmm9,zmm3,zmm4
	vpsllvq	zmm5,zmm0,ZMMWORD[const_dq7654]
	vpsrlvq	zmm6,zmm1,ZMMWORD[const_dq1234]
	DB	98,147,77,72,68,249,0
	vpxorq	zmm5{k2},zmm5,zmm6
	vpxord	zmm10,zmm7,zmm5
	mov	r8,0x0000ffffffffffff
	kmovq	k1,r8
	vmovdqu8	zmm1,ZMMWORD[rdi]
	vmovdqu8	zmm2{k1},[64+rdi]

	add	rdi,0x70
	vbroadcasti32x4	zmm0,ZMMWORD[rcx]
	vpternlogq	zmm1,zmm9,zmm0,0x96
	vpternlogq	zmm2,zmm10,zmm0,0x96
	vbroadcasti32x4	zmm0,ZMMWORD[16+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[32+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[48+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208

	vbroadcasti32x4	zmm0,ZMMWORD[64+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[80+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[96+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[112+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[128+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[144+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[160+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[176+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[192+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[208+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[224+rcx]
	DB	98,242,117,72,221,200
	DB	98,242,109,72,221,208
	vpxorq	zmm1,zmm1,zmm9
	vpxorq	zmm2,zmm2,zmm10
	vmovdqu8	ZMMWORD[rsi],zmm1
	vmovdqu8	ZMMWORD[64+rsi]{k1},zmm2
	add	rsi,0x70
	vextracti32x4	xmm8,zmm2,0x2
	vextracti32x4	xmm0,zmm10,0x3
	and	rdx,0xf
	je	NEAR $L$_ret_hEgxyDlCngwrfFe
	jmp	NEAR $L$_steal_cipher_hEgxyDlCngwrfFe
$L$_num_blocks_is_6_hEgxyDlCngwrfFe:
	vpshufb	zmm1,zmm0,zmm8
	vpsllvq	zmm4,zmm0,ZMMWORD[const_dq3210]
	vpsrlvq	zmm2,zmm1,ZMMWORD[const_dq5678]
	DB	98,147,109,72,68,217,0
	vpxorq	zmm4{k2},zmm4,zmm2
	vpxord	zmm9,zmm3,zmm4
	vpsllvq	zmm5,zmm0,ZMMWORD[const_dq7654]
	vpsrlvq	zmm6,zmm1,ZMMWORD[const_dq1234]
	DB	98,147,77,72,68,249,0
	vpxorq	zmm5{k2},zmm5,zmm6
	vpxord	zmm10,zmm7,zmm5
	vmovdqu8	zmm1,ZMMWORD[rdi]
	vmovdqu8	ymm2,YMMWORD[64+rdi]
	add	rdi,96
	vbroadcasti32x4	zmm0,ZMMWORD[rcx]
	vpternlogq	zmm1,zmm9,zmm0,0x96
	vpternlogq	zmm2,zmm10,zmm0,0x96
	vbroadcasti32x4	zmm0,ZMMWORD[16+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[32+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[48+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208

	vbroadcasti32x4	zmm0,ZMMWORD[64+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[80+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[96+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[112+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[128+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[144+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[160+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[176+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[192+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[208+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[224+rcx]
	DB	98,242,117,72,221,200
	DB	98,242,109,72,221,208
	vpxorq	zmm1,zmm1,zmm9
	vpxorq	zmm2,zmm2,zmm10
	vmovdqu8	ZMMWORD[rsi],zmm1
	vmovdqu8	YMMWORD[64+rsi],ymm2
	add	rsi,96

	vextracti32x4	xmm8,ymm2,0x1
	vextracti32x4	xmm0,zmm10,0x2
	and	rdx,0xf
	je	NEAR $L$_ret_hEgxyDlCngwrfFe
	jmp	NEAR $L$_steal_cipher_hEgxyDlCngwrfFe
$L$_num_blocks_is_5_hEgxyDlCngwrfFe:
	vpshufb	zmm1,zmm0,zmm8
	vpsllvq	zmm4,zmm0,ZMMWORD[const_dq3210]
	vpsrlvq	zmm2,zmm1,ZMMWORD[const_dq5678]
	DB	98,147,109,72,68,217,0
	vpxorq	zmm4{k2},zmm4,zmm2
	vpxord	zmm9,zmm3,zmm4
	vpsllvq	zmm5,zmm0,ZMMWORD[const_dq7654]
	vpsrlvq	zmm6,zmm1,ZMMWORD[const_dq1234]
	DB	98,147,77,72,68,249,0
	vpxorq	zmm5{k2},zmm5,zmm6
	vpxord	zmm10,zmm7,zmm5
	vmovdqu8	zmm1,ZMMWORD[rdi]
	vmovdqu8	xmm2,XMMWORD[64+rdi]
	add	rdi,80
	vbroadcasti32x4	zmm0,ZMMWORD[rcx]
	vpternlogq	zmm1,zmm9,zmm0,0x96
	vpternlogq	zmm2,zmm10,zmm0,0x96
	vbroadcasti32x4	zmm0,ZMMWORD[16+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[32+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[48+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208

	vbroadcasti32x4	zmm0,ZMMWORD[64+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[80+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[96+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[112+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[128+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[144+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[160+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[176+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[192+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[208+rcx]
	DB	98,242,117,72,220,200
	DB	98,242,109,72,220,208


	vbroadcasti32x4	zmm0,ZMMWORD[224+rcx]
	DB	98,242,117,72,221,200
	DB	98,242,109,72,221,208
	vpxorq	zmm1,zmm1,zmm9
	vpxorq	zmm2,zmm2,zmm10
	vmovdqu8	ZMMWORD[rsi],zmm1
	vmovdqu8	XMMWORD[64+rsi],xmm2
	add	rsi,80

	vmovdqa	xmm8,xmm2
	vextracti32x4	xmm0,zmm10,0x1
	and	rdx,0xf
	je	NEAR $L$_ret_hEgxyDlCngwrfFe
	jmp	NEAR $L$_steal_cipher_hEgxyDlCngwrfFe
$L$_num_blocks_is_4_hEgxyDlCngwrfFe:
	vpshufb	zmm1,zmm0,zmm8
	vpsllvq	zmm4,zmm0,ZMMWORD[const_dq3210]
	vpsrlvq	zmm2,zmm1,ZMMWORD[const_dq5678]
	DB	98,147,109,72,68,217,0
	vpxorq	zmm4{k2},zmm4,zmm2
	vpxord	zmm9,zmm3,zmm4
	vpsllvq	zmm5,zmm0,ZMMWORD[const_dq7654]
	vpsrlvq	zmm6,zmm1,ZMMWORD[const_dq1234]
	DB	98,147,77,72,68,249,0
	vpxorq	zmm5{k2},zmm5,zmm6
	vpxord	zmm10,zmm7,zmm5
	vmovdqu8	zmm1,ZMMWORD[rdi]
	add	rdi,64
	vbroadcasti32x4	zmm0,ZMMWORD[rcx]
	vpternlogq	zmm1,zmm9,zmm0,0x96
	vbroadcasti32x4	zmm0,ZMMWORD[16+rcx]
	DB	98,242,117,72,220,200
	vbroadcasti32x4	zmm0,ZMMWORD[32+rcx]
	DB	98,242,117,72,220,200
	vbroadcasti32x4	zmm0,ZMMWORD[48+rcx]
	DB	98,242,117,72,220,200
	vbroadcasti32x4	zmm0,ZMMWORD[64+rcx]
	DB	98,242,117,72,220,200
	vbroadcasti32x4	zmm0,ZMMWORD[80+rcx]
	DB	98,242,117,72,220,200
	vbroadcasti32x4	zmm0,ZMMWORD[96+rcx]
	DB	98,242,117,72,220,200
	vbroadcasti32x4	zmm0,ZMMWORD[112+rcx]
	DB	98,242,117,72,220,200
	vbroadcasti32x4	zmm0,ZMMWORD[128+rcx]
	DB	98,242,117,72,220,200
	vbroadcasti32x4	zmm0,ZMMWORD[144+rcx]
	DB	98,242,117,72,220,200
	vbroadcasti32x4	zmm0,ZMMWORD[160+rcx]
	DB	98,242,117,72,220,200
	vbroadcasti32x4	zmm0,ZMMWORD[176+rcx]
	DB	98,242,117,72,220,200
	vbroadcasti32x4	zmm0,ZMMWORD[192+rcx]
	DB	98,242,117,72,220,200
	vbroadcasti32x4	zmm0,ZMMWORD[208+rcx]
	DB	98,242,117,72,220,200
	vbroadcasti32x4	zmm0,ZMMWORD[224+rcx]
	DB	98,242,117,72,221,200
	vpxorq	zmm1,zmm1,zmm9
	vmovdqu8	ZMMWORD[rsi],zmm1
	add	rsi,64
	vextracti32x4	xmm8,zmm1,0x3
	vmovdqa	xmm0,xmm10
	and	rdx,0xf
	je	NEAR $L$_ret_hEgxyDlCngwrfFe
	jmp	NEAR $L$_steal_cipher_hEgxyDlCngwrfFe
$L$_num_blocks_is_3_hEgxyDlCngwrfFe:
	vpshufb	zmm1,zmm0,zmm8
	vpsllvq	zmm4,zmm0,ZMMWORD[const_dq3210]
	vpsrlvq	zmm2,zmm1,ZMMWORD[const_dq5678]
	DB	98,147,109,72,68,217,0
	vpxorq	zmm4{k2},zmm4,zmm2
	vpxord	zmm9,zmm3,zmm4
	mov	r8,0x0000ffffffffffff
	kmovq	k1,r8
	vmovdqu8	zmm1{k1},[rdi]
	add	rdi,48
	vbroadcasti32x4	zmm0,ZMMWORD[rcx]
	vpternlogq	zmm1,zmm9,zmm0,0x96
	vbroadcasti32x4	zmm0,ZMMWORD[16+rcx]
	DB	98,242,117,72,220,200
	vbroadcasti32x4	zmm0,ZMMWORD[32+rcx]
	DB	98,242,117,72,220,200
	vbroadcasti32x4	zmm0,ZMMWORD[48+rcx]
	DB	98,242,117,72,220,200
	vbroadcasti32x4	zmm0,ZMMWORD[64+rcx]
	DB	98,242,117,72,220,200
	vbroadcasti32x4	zmm0,ZMMWORD[80+rcx]
	DB	98,242,117,72,220,200
	vbroadcasti32x4	zmm0,ZMMWORD[96+rcx]
	DB	98,242,117,72,220,200
	vbroadcasti32x4	zmm0,ZMMWORD[112+rcx]
	DB	98,242,117,72,220,200
	vbroadcasti32x4	zmm0,ZMMWORD[128+rcx]
	DB	98,242,117,72,220,200
	vbroadcasti32x4	zmm0,ZMMWORD[144+rcx]
	DB	98,242,117,72,220,200
	vbroadcasti32x4	zmm0,ZMMWORD[160+rcx]
	DB	98,242,117,72,220,200
	vbroadcasti32x4	zmm0,ZMMWORD[176+rcx]
	DB	98,242,117,72,220,200
	vbroadcasti32x4	zmm0,ZMMWORD[192+rcx]
	DB	98,242,117,72,220,200
	vbroadcasti32x4	zmm0,ZMMWORD[208+rcx]
	DB	98,242,117,72,220,200
	vbroadcasti32x4	zmm0,ZMMWORD[224+rcx]
	DB	98,242,117,72,221,200
	vpxorq	zmm1,zmm1,zmm9
	vmovdqu8	ZMMWORD[rsi]{k1},zmm1
	add	rsi,48
	vextracti32x4	xmm8,zmm1,2
	vextracti32x4	xmm0,zmm9,3
	and	rdx,0xf
	je	NEAR $L$_ret_hEgxyDlCngwrfFe
	jmp	NEAR $L$_steal_cipher_hEgxyDlCngwrfFe
$L$_num_blocks_is_2_hEgxyDlCngwrfFe:
	vpshufb	zmm1,zmm0,zmm8
	vpsllvq	zmm4,zmm0,ZMMWORD[const_dq3210]
	vpsrlvq	zmm2,zmm1,ZMMWORD[const_dq5678]
	DB	98,147,109,72,68,217,0
	vpxorq	zmm4{k2},zmm4,zmm2
	vpxord	zmm9,zmm3,zmm4

	vmovdqu8	ymm1,YMMWORD[rdi]
	add	rdi,32
	vbroadcasti32x4	ymm0,YMMWORD[rcx]
	vpternlogq	ymm1,ymm9,ymm0,0x96
	vbroadcasti32x4	ymm0,YMMWORD[16+rcx]
	DB	98,242,117,40,220,200
	vbroadcasti32x4	ymm0,YMMWORD[32+rcx]
	DB	98,242,117,40,220,200
	vbroadcasti32x4	ymm0,YMMWORD[48+rcx]
	DB	98,242,117,40,220,200
	vbroadcasti32x4	ymm0,YMMWORD[64+rcx]
	DB	98,242,117,40,220,200
	vbroadcasti32x4	ymm0,YMMWORD[80+rcx]
	DB	98,242,117,40,220,200
	vbroadcasti32x4	ymm0,YMMWORD[96+rcx]
	DB	98,242,117,40,220,200
	vbroadcasti32x4	ymm0,YMMWORD[112+rcx]
	DB	98,242,117,40,220,200
	vbroadcasti32x4	ymm0,YMMWORD[128+rcx]
	DB	98,242,117,40,220,200
	vbroadcasti32x4	ymm0,YMMWORD[144+rcx]
	DB	98,242,117,40,220,200
	vbroadcasti32x4	ymm0,YMMWORD[160+rcx]
	DB	98,242,117,40,220,200
	vbroadcasti32x4	ymm0,YMMWORD[176+rcx]
	DB	98,242,117,40,220,200
	vbroadcasti32x4	ymm0,YMMWORD[192+rcx]
	DB	98,242,117,40,220,200
	vbroadcasti32x4	ymm0,YMMWORD[208+rcx]
	DB	98,242,117,40,220,200
	vbroadcasti32x4	ymm0,YMMWORD[224+rcx]
	DB	98,242,117,40,221,200
	vpxorq	ymm1,ymm1,ymm9
	vmovdqu8	YMMWORD[rsi],ymm1
	add	rsi,32

	vextracti32x4	xmm8,ymm1,1
	vextracti32x4	xmm0,zmm9,2
	and	rdx,0xf
	je	NEAR $L$_ret_hEgxyDlCngwrfFe
	jmp	NEAR $L$_steal_cipher_hEgxyDlCngwrfFe
$L$_num_blocks_is_1_hEgxyDlCngwrfFe:
	vpshufb	zmm1,zmm0,zmm8
	vpsllvq	zmm4,zmm0,ZMMWORD[const_dq3210]
	vpsrlvq	zmm2,zmm1,ZMMWORD[const_dq5678]
	DB	98,147,109,72,68,217,0
	vpxorq	zmm4{k2},zmm4,zmm2
	vpxord	zmm9,zmm3,zmm4

	vmovdqu8	xmm1,XMMWORD[rdi]
	add	rdi,16
	vbroadcasti32x4	ymm0,YMMWORD[rcx]
	vpternlogq	ymm1,ymm9,ymm0,0x96
	vbroadcasti32x4	ymm0,YMMWORD[16+rcx]
	DB	98,242,117,40,220,200
	vbroadcasti32x4	ymm0,YMMWORD[32+rcx]
	DB	98,242,117,40,220,200
	vbroadcasti32x4	ymm0,YMMWORD[48+rcx]
	DB	98,242,117,40,220,200
	vbroadcasti32x4	ymm0,YMMWORD[64+rcx]
	DB	98,242,117,40,220,200
	vbroadcasti32x4	ymm0,YMMWORD[80+rcx]
	DB	98,242,117,40,220,200
	vbroadcasti32x4	ymm0,YMMWORD[96+rcx]
	DB	98,242,117,40,220,200
	vbroadcasti32x4	ymm0,YMMWORD[112+rcx]
	DB	98,242,117,40,220,200
	vbroadcasti32x4	ymm0,YMMWORD[128+rcx]
	DB	98,242,117,40,220,200
	vbroadcasti32x4	ymm0,YMMWORD[144+rcx]
	DB	98,242,117,40,220,200
	vbroadcasti32x4	ymm0,YMMWORD[160+rcx]
	DB	98,242,117,40,220,200
	vbroadcasti32x4	ymm0,YMMWORD[176+rcx]
	DB	98,242,117,40,220,200
	vbroadcasti32x4	ymm0,YMMWORD[192+rcx]
	DB	98,242,117,40,220,200
	vbroadcasti32x4	ymm0,YMMWORD[208+rcx]
	DB	98,242,117,40,220,200
	vbroadcasti32x4	ymm0,YMMWORD[224+rcx]
	DB	98,242,117,40,221,200
	vpxorq	ymm1,ymm1,ymm9
	vmovdqu8	XMMWORD[rsi],xmm1
	add	rsi,16

	vmovdqa	xmm8,xmm1
	vextracti32x4	xmm0,zmm9,1
	and	rdx,0xf
	je	NEAR $L$_ret_hEgxyDlCngwrfFe
	jmp	NEAR $L$_steal_cipher_hEgxyDlCngwrfFe

global	aes_hw_xts_decrypt_avx512


ALIGN	32
aes_hw_xts_decrypt_avx512:
	mov	QWORD[8+rsp],rdi	;WIN64 prologue
	mov	QWORD[16+rsp],rsi
	mov	rax,rsp
$L$SEH_begin_aes_hw_xts_decrypt_avx512:
	mov	rdi,rcx
	mov	rsi,rdx
	mov	rdx,r8
	mov	rcx,r9
	mov	r8,QWORD[40+rsp]
	mov	r9,QWORD[48+rsp]



DB	243,15,30,250
	push	rbp
	mov	rbp,rsp
	sub	rsp,312
	and	rsp,0xffffffffffffffc0
	mov	QWORD[288+rsp],rbx
	mov	QWORD[((288 + 8))+rsp],rdi
	mov	QWORD[((288 + 16))+rsp],rsi
	vmovdqa	XMMWORD[(128 + 0)+rsp],xmm6
	vmovdqa	XMMWORD[(128 + 16)+rsp],xmm7
	vmovdqa	XMMWORD[(128 + 32)+rsp],xmm8
	vmovdqa	XMMWORD[(128 + 48)+rsp],xmm9
	vmovdqa	XMMWORD[(128 + 64)+rsp],xmm10
	vmovdqa	XMMWORD[(128 + 80)+rsp],xmm11
	vmovdqa	XMMWORD[(128 + 96)+rsp],xmm12
	vmovdqa	XMMWORD[(128 + 112)+rsp],xmm13
	vmovdqa	XMMWORD[(128 + 128)+rsp],xmm14
	vmovdqa	XMMWORD[(128 + 144)+rsp],xmm15
	mov	r10,0x87
	vmovdqu	xmm1,XMMWORD[r9]
	vpxor	xmm1,xmm1,XMMWORD[r8]
	vaesenc	xmm1,xmm1,XMMWORD[16+r8]
	vaesenc	xmm1,xmm1,XMMWORD[32+r8]
	vaesenc	xmm1,xmm1,XMMWORD[48+r8]
	vaesenc	xmm1,xmm1,XMMWORD[64+r8]
	vaesenc	xmm1,xmm1,XMMWORD[80+r8]
	vaesenc	xmm1,xmm1,XMMWORD[96+r8]
	vaesenc	xmm1,xmm1,XMMWORD[112+r8]
	vaesenc	xmm1,xmm1,XMMWORD[128+r8]
	vaesenc	xmm1,xmm1,XMMWORD[144+r8]
	vaesenc	xmm1,xmm1,XMMWORD[160+r8]
	vaesenc	xmm1,xmm1,XMMWORD[176+r8]
	vaesenc	xmm1,xmm1,XMMWORD[192+r8]
	vaesenc	xmm1,xmm1,XMMWORD[208+r8]
	vaesenclast	xmm1,xmm1,XMMWORD[224+r8]
	vmovdqa	XMMWORD[rsp],xmm1
	mov	QWORD[((8 + 40))+rbp],rdi
	mov	QWORD[((8 + 48))+rbp],rsi


	cmp	rdx,0x20
	jl	NEAR $L$_final_block_is_only_block_amivrujEyduiFoi




	mov	r11,rdx
	and	r11,0xfffffffffffffff0
	sub	r11,16
	cmp	r11,0x80
	jl	NEAR $L$_less_than_128_bytes_amivrujEyduiFoi
	vpbroadcastq	zmm25,r10
	cmp	r11,0x100
	jge	NEAR $L$_start_by16_amivrujEyduiFoi
	cmp	r11,0x80
	jge	NEAR $L$_start_by8_amivrujEyduiFoi

$L$_do_n_blocks_amivrujEyduiFoi:
	cmp	r11,0x70
	je	NEAR $L$_remaining_num_blocks_is_7_amivrujEyduiFoi
	cmp	r11,0x60
	je	NEAR $L$_remaining_num_blocks_is_6_amivrujEyduiFoi
	cmp	r11,0x50
	je	NEAR $L$_remaining_num_blocks_is_5_amivrujEyduiFoi
	cmp	r11,0x40
	je	NEAR $L$_remaining_num_blocks_is_4_amivrujEyduiFoi
	cmp	r11,0x30
	je	NEAR $L$_remaining_num_blocks_is_3_amivrujEyduiFoi
	cmp	r11,0x20
	je	NEAR $L$_remaining_num_blocks_is_2_amivrujEyduiFoi
	cmp	r11,0x10
	je	NEAR $L$_remaining_num_blocks_is_1_amivrujEyduiFoi
	and	rdx,0xf
	je	NEAR $L$_final_block_amivrujEyduiFoi
	vextracti32x4	xmm0,zmm9,0x0
	vextracti32x4	xmm15,zmm9,0x1
	jmp	NEAR $L$_steal_cipher_amivrujEyduiFoi

$L$_remaining_num_blocks_is_7_amivrujEyduiFoi:
	mov	r8,0x0000ffffffffffff
	kmovq	k1,r8
	vmovdqu8	zmm1,ZMMWORD[rdi]
	vmovdqu8	zmm2{k1},[64+rdi]
	add	rdi,0x70
	vbroadcasti32x4	zmm0,ZMMWORD[rcx]
	vpternlogq	zmm1,zmm9,zmm0,0x96
	vpternlogq	zmm2,zmm10,zmm0,0x96
	vbroadcasti32x4	zmm0,ZMMWORD[16+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[32+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[48+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208

	vbroadcasti32x4	zmm0,ZMMWORD[64+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[80+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[96+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[112+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[128+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[144+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[160+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[176+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[192+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[208+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[224+rcx]
	DB	98,242,117,72,223,200
	DB	98,242,109,72,223,208
	vpxorq	zmm1,zmm1,zmm9
	vpxorq	zmm2,zmm2,zmm10
	vmovdqu8	ZMMWORD[rsi],zmm1
	vmovdqu8	ZMMWORD[64+rsi]{k1},zmm2
	add	rsi,0x70
	vextracti32x4	xmm0,zmm10,0x3
	and	rdx,0xf
	je	NEAR $L$_final_block_amivrujEyduiFoi
	vpsrldq	zmm13,zmm9,0xf
	DB	98,19,21,72,68,241,0
	vpslldq	zmm11,zmm9,0x1
	vpxord	zmm11,zmm11,zmm14
	vextracti32x4	xmm15,zmm11,0x0
	jmp	NEAR $L$_steal_cipher_amivrujEyduiFoi

$L$_remaining_num_blocks_is_6_amivrujEyduiFoi:
	vmovdqu8	zmm1,ZMMWORD[rdi]
	vmovdqu8	ymm2,YMMWORD[64+rdi]
	add	rdi,0x60
	vbroadcasti32x4	zmm0,ZMMWORD[rcx]
	vpternlogq	zmm1,zmm9,zmm0,0x96
	vpternlogq	zmm2,zmm10,zmm0,0x96
	vbroadcasti32x4	zmm0,ZMMWORD[16+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[32+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[48+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208

	vbroadcasti32x4	zmm0,ZMMWORD[64+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[80+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[96+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[112+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[128+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[144+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[160+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[176+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[192+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[208+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[224+rcx]
	DB	98,242,117,72,223,200
	DB	98,242,109,72,223,208
	vpxorq	zmm1,zmm1,zmm9
	vpxorq	zmm2,zmm2,zmm10
	vmovdqu8	ZMMWORD[rsi],zmm1
	vmovdqu8	YMMWORD[64+rsi],ymm2
	add	rsi,0x60
	vextracti32x4	xmm0,zmm10,0x2
	vextracti32x4	xmm15,zmm10,0x3
	and	rdx,0xf
	je	NEAR $L$_final_block_amivrujEyduiFoi
	jmp	NEAR $L$_steal_cipher_amivrujEyduiFoi

$L$_remaining_num_blocks_is_5_amivrujEyduiFoi:
	vmovdqu8	zmm1,ZMMWORD[rdi]
	vmovdqu	xmm2,XMMWORD[64+rdi]
	add	rdi,0x50
	vbroadcasti32x4	zmm0,ZMMWORD[rcx]
	vpternlogq	zmm1,zmm9,zmm0,0x96
	vpternlogq	zmm2,zmm10,zmm0,0x96
	vbroadcasti32x4	zmm0,ZMMWORD[16+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[32+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[48+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208

	vbroadcasti32x4	zmm0,ZMMWORD[64+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[80+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[96+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[112+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[128+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[144+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[160+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[176+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[192+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[208+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[224+rcx]
	DB	98,242,117,72,223,200
	DB	98,242,109,72,223,208
	vpxorq	zmm1,zmm1,zmm9
	vpxorq	zmm2,zmm2,zmm10
	vmovdqu8	ZMMWORD[rsi],zmm1
	vmovdqu	XMMWORD[64+rsi],xmm2
	add	rsi,0x50
	vextracti32x4	xmm0,zmm10,0x1
	vextracti32x4	xmm15,zmm10,0x2
	and	rdx,0xf
	je	NEAR $L$_final_block_amivrujEyduiFoi
	jmp	NEAR $L$_steal_cipher_amivrujEyduiFoi

$L$_remaining_num_blocks_is_4_amivrujEyduiFoi:
	vmovdqu8	zmm1,ZMMWORD[rdi]
	add	rdi,0x40
	vbroadcasti32x4	zmm0,ZMMWORD[rcx]
	vpternlogq	zmm1,zmm9,zmm0,0x96
	vbroadcasti32x4	zmm0,ZMMWORD[16+rcx]
	DB	98,242,117,72,222,200
	vbroadcasti32x4	zmm0,ZMMWORD[32+rcx]
	DB	98,242,117,72,222,200
	vbroadcasti32x4	zmm0,ZMMWORD[48+rcx]
	DB	98,242,117,72,222,200
	vbroadcasti32x4	zmm0,ZMMWORD[64+rcx]
	DB	98,242,117,72,222,200
	vbroadcasti32x4	zmm0,ZMMWORD[80+rcx]
	DB	98,242,117,72,222,200
	vbroadcasti32x4	zmm0,ZMMWORD[96+rcx]
	DB	98,242,117,72,222,200
	vbroadcasti32x4	zmm0,ZMMWORD[112+rcx]
	DB	98,242,117,72,222,200
	vbroadcasti32x4	zmm0,ZMMWORD[128+rcx]
	DB	98,242,117,72,222,200
	vbroadcasti32x4	zmm0,ZMMWORD[144+rcx]
	DB	98,242,117,72,222,200
	vbroadcasti32x4	zmm0,ZMMWORD[160+rcx]
	DB	98,242,117,72,222,200
	vbroadcasti32x4	zmm0,ZMMWORD[176+rcx]
	DB	98,242,117,72,222,200
	vbroadcasti32x4	zmm0,ZMMWORD[192+rcx]
	DB	98,242,117,72,222,200
	vbroadcasti32x4	zmm0,ZMMWORD[208+rcx]
	DB	98,242,117,72,222,200
	vbroadcasti32x4	zmm0,ZMMWORD[224+rcx]
	DB	98,242,117,72,223,200
	vpxorq	zmm1,zmm1,zmm9
	vmovdqu8	ZMMWORD[rsi],zmm1
	add	rsi,0x40
	vextracti32x4	xmm0,zmm10,0x0
	vextracti32x4	xmm15,zmm10,0x1
	and	rdx,0xf
	je	NEAR $L$_final_block_amivrujEyduiFoi
	jmp	NEAR $L$_steal_cipher_amivrujEyduiFoi
$L$_remaining_num_blocks_is_3_amivrujEyduiFoi:
	mov	r8,-1
	shr	r8,0x10
	kmovq	k1,r8
	vmovdqu8	zmm1{k1},[rdi]
	add	rdi,0x30
	vbroadcasti32x4	zmm0,ZMMWORD[rcx]
	vpternlogq	zmm1,zmm9,zmm0,0x96
	vbroadcasti32x4	zmm0,ZMMWORD[16+rcx]
	DB	98,242,117,72,222,200
	vbroadcasti32x4	zmm0,ZMMWORD[32+rcx]
	DB	98,242,117,72,222,200
	vbroadcasti32x4	zmm0,ZMMWORD[48+rcx]
	DB	98,242,117,72,222,200
	vbroadcasti32x4	zmm0,ZMMWORD[64+rcx]
	DB	98,242,117,72,222,200
	vbroadcasti32x4	zmm0,ZMMWORD[80+rcx]
	DB	98,242,117,72,222,200
	vbroadcasti32x4	zmm0,ZMMWORD[96+rcx]
	DB	98,242,117,72,222,200
	vbroadcasti32x4	zmm0,ZMMWORD[112+rcx]
	DB	98,242,117,72,222,200
	vbroadcasti32x4	zmm0,ZMMWORD[128+rcx]
	DB	98,242,117,72,222,200
	vbroadcasti32x4	zmm0,ZMMWORD[144+rcx]
	DB	98,242,117,72,222,200
	vbroadcasti32x4	zmm0,ZMMWORD[160+rcx]
	DB	98,242,117,72,222,200
	vbroadcasti32x4	zmm0,ZMMWORD[176+rcx]
	DB	98,242,117,72,222,200
	vbroadcasti32x4	zmm0,ZMMWORD[192+rcx]
	DB	98,242,117,72,222,200
	vbroadcasti32x4	zmm0,ZMMWORD[208+rcx]
	DB	98,242,117,72,222,200
	vbroadcasti32x4	zmm0,ZMMWORD[224+rcx]
	DB	98,242,117,72,223,200
	vpxorq	zmm1,zmm1,zmm9
	vmovdqu8	ZMMWORD[rsi]{k1},zmm1
	add	rsi,0x30
	vextracti32x4	xmm0,zmm9,0x3
	vextracti32x4	xmm15,zmm10,0x0
	and	rdx,0xf
	je	NEAR $L$_final_block_amivrujEyduiFoi
	jmp	NEAR $L$_steal_cipher_amivrujEyduiFoi
$L$_remaining_num_blocks_is_2_amivrujEyduiFoi:
	vmovdqu8	ymm1,YMMWORD[rdi]
	add	rdi,0x20
	vbroadcasti32x4	ymm0,YMMWORD[rcx]
	vpternlogq	ymm1,ymm9,ymm0,0x96
	vbroadcasti32x4	ymm0,YMMWORD[16+rcx]
	DB	98,242,117,40,222,200
	vbroadcasti32x4	ymm0,YMMWORD[32+rcx]
	DB	98,242,117,40,222,200
	vbroadcasti32x4	ymm0,YMMWORD[48+rcx]
	DB	98,242,117,40,222,200
	vbroadcasti32x4	ymm0,YMMWORD[64+rcx]
	DB	98,242,117,40,222,200
	vbroadcasti32x4	ymm0,YMMWORD[80+rcx]
	DB	98,242,117,40,222,200
	vbroadcasti32x4	ymm0,YMMWORD[96+rcx]
	DB	98,242,117,40,222,200
	vbroadcasti32x4	ymm0,YMMWORD[112+rcx]
	DB	98,242,117,40,222,200
	vbroadcasti32x4	ymm0,YMMWORD[128+rcx]
	DB	98,242,117,40,222,200
	vbroadcasti32x4	ymm0,YMMWORD[144+rcx]
	DB	98,242,117,40,222,200
	vbroadcasti32x4	ymm0,YMMWORD[160+rcx]
	DB	98,242,117,40,222,200
	vbroadcasti32x4	ymm0,YMMWORD[176+rcx]
	DB	98,242,117,40,222,200
	vbroadcasti32x4	ymm0,YMMWORD[192+rcx]
	DB	98,242,117,40,222,200
	vbroadcasti32x4	ymm0,YMMWORD[208+rcx]
	DB	98,242,117,40,222,200
	vbroadcasti32x4	ymm0,YMMWORD[224+rcx]
	DB	98,242,117,40,223,200
	vpxorq	ymm1,ymm1,ymm9
	vmovdqu	YMMWORD[rsi],ymm1
	add	rsi,0x20
	vextracti32x4	xmm0,zmm9,0x2
	vextracti32x4	xmm15,zmm9,0x3
	and	rdx,0xf
	je	NEAR $L$_final_block_amivrujEyduiFoi
	jmp	NEAR $L$_steal_cipher_amivrujEyduiFoi
$L$_remaining_num_blocks_is_1_amivrujEyduiFoi:
	vmovdqu	xmm1,XMMWORD[rdi]
	add	rdi,0x10
	vpxor	xmm1,xmm1,xmm9
	vpxor	xmm1,xmm1,XMMWORD[rcx]
	vaesdec	xmm1,xmm1,XMMWORD[16+rcx]
	vaesdec	xmm1,xmm1,XMMWORD[32+rcx]
	vaesdec	xmm1,xmm1,XMMWORD[48+rcx]
	vaesdec	xmm1,xmm1,XMMWORD[64+rcx]
	vaesdec	xmm1,xmm1,XMMWORD[80+rcx]
	vaesdec	xmm1,xmm1,XMMWORD[96+rcx]
	vaesdec	xmm1,xmm1,XMMWORD[112+rcx]
	vaesdec	xmm1,xmm1,XMMWORD[128+rcx]
	vaesdec	xmm1,xmm1,XMMWORD[144+rcx]
	vaesdec	xmm1,xmm1,XMMWORD[160+rcx]
	vaesdec	xmm1,xmm1,XMMWORD[176+rcx]
	vaesdec	xmm1,xmm1,XMMWORD[192+rcx]
	vaesdec	xmm1,xmm1,XMMWORD[208+rcx]
	vaesdeclast	xmm1,xmm1,XMMWORD[224+rcx]
	vpxor	xmm1,xmm1,xmm9
	vmovdqu	XMMWORD[rsi],xmm1
	add	rsi,0x10
	vextracti32x4	xmm0,zmm9,0x1
	vextracti32x4	xmm15,zmm9,0x2
	and	rdx,0xf
	je	NEAR $L$_final_block_amivrujEyduiFoi
	jmp	NEAR $L$_steal_cipher_amivrujEyduiFoi


$L$_start_by16_amivrujEyduiFoi:
	vbroadcasti32x4	zmm0,ZMMWORD[rsp]
	vbroadcasti32x4	zmm8,ZMMWORD[shufb_15_7]
	mov	r8,0xaa
	kmovq	k2,r8
	vpshufb	zmm1,zmm0,zmm8


	vpsllvq	zmm4,zmm0,ZMMWORD[const_dq3210]
	vpsrlvq	zmm2,zmm1,ZMMWORD[const_dq5678]
	DB	98,147,109,72,68,217,0
	vpxorq	zmm4{k2},zmm4,zmm2
	vpxord	zmm9,zmm3,zmm4


	vpsllvq	zmm5,zmm0,ZMMWORD[const_dq7654]
	vpsrlvq	zmm6,zmm1,ZMMWORD[const_dq1234]
	DB	98,147,77,72,68,249,0
	vpxorq	zmm5{k2},zmm5,zmm6
	vpxord	zmm10,zmm7,zmm5


	vpsrldq	zmm13,zmm9,0xf
	DB	98,19,21,72,68,241,0
	vpslldq	zmm11,zmm9,0x1
	vpxord	zmm11,zmm11,zmm14


	vpsrldq	zmm15,zmm10,0xf
	DB	98,131,5,72,68,193,0
	vpslldq	zmm12,zmm10,0x1
	vpxord	zmm12,zmm12,zmm16

$L$_main_loop_run_16_amivrujEyduiFoi:
	vmovdqu8	zmm1,ZMMWORD[rdi]
	vmovdqu8	zmm2,ZMMWORD[64+rdi]
	vmovdqu8	zmm3,ZMMWORD[128+rdi]
	vmovdqu8	zmm4,ZMMWORD[192+rdi]
	add	rdi,0x100
	vpxorq	zmm1,zmm1,zmm9
	vpxorq	zmm2,zmm2,zmm10
	vpxorq	zmm3,zmm3,zmm11
	vpxorq	zmm4,zmm4,zmm12
	vbroadcasti32x4	zmm0,ZMMWORD[rcx]
	vpxorq	zmm1,zmm1,zmm0
	vpxorq	zmm2,zmm2,zmm0
	vpxorq	zmm3,zmm3,zmm0
	vpxorq	zmm4,zmm4,zmm0
	vpsrldq	zmm13,zmm11,0xf
	DB	98,19,21,72,68,241,0
	vpslldq	zmm15,zmm11,0x1
	vpxord	zmm15,zmm15,zmm14
	vbroadcasti32x4	zmm0,ZMMWORD[16+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208
	DB	98,242,101,72,222,216
	DB	98,242,93,72,222,224
	vbroadcasti32x4	zmm0,ZMMWORD[32+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208
	DB	98,242,101,72,222,216
	DB	98,242,93,72,222,224
	vbroadcasti32x4	zmm0,ZMMWORD[48+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208
	DB	98,242,101,72,222,216
	DB	98,242,93,72,222,224
	vpsrldq	zmm13,zmm12,0xf
	DB	98,19,21,72,68,241,0
	vpslldq	zmm16,zmm12,0x1
	vpxord	zmm16,zmm16,zmm14
	vbroadcasti32x4	zmm0,ZMMWORD[64+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208
	DB	98,242,101,72,222,216
	DB	98,242,93,72,222,224
	vbroadcasti32x4	zmm0,ZMMWORD[80+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208
	DB	98,242,101,72,222,216
	DB	98,242,93,72,222,224
	vbroadcasti32x4	zmm0,ZMMWORD[96+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208
	DB	98,242,101,72,222,216
	DB	98,242,93,72,222,224
	vpsrldq	zmm13,zmm15,0xf
	DB	98,19,21,72,68,241,0
	vpslldq	zmm17,zmm15,0x1
	vpxord	zmm17,zmm17,zmm14
	vbroadcasti32x4	zmm0,ZMMWORD[112+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208
	DB	98,242,101,72,222,216
	DB	98,242,93,72,222,224
	vbroadcasti32x4	zmm0,ZMMWORD[128+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208
	DB	98,242,101,72,222,216
	DB	98,242,93,72,222,224
	vbroadcasti32x4	zmm0,ZMMWORD[144+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208
	DB	98,242,101,72,222,216
	DB	98,242,93,72,222,224
	vpsrldq	zmm13,zmm16,0xf
	DB	98,19,21,72,68,241,0
	vpslldq	zmm18,zmm16,0x1
	vpxord	zmm18,zmm18,zmm14
	vbroadcasti32x4	zmm0,ZMMWORD[160+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208
	DB	98,242,101,72,222,216
	DB	98,242,93,72,222,224
	vbroadcasti32x4	zmm0,ZMMWORD[176+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208
	DB	98,242,101,72,222,216
	DB	98,242,93,72,222,224
	vbroadcasti32x4	zmm0,ZMMWORD[192+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208
	DB	98,242,101,72,222,216
	DB	98,242,93,72,222,224
	vbroadcasti32x4	zmm0,ZMMWORD[208+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208
	DB	98,242,101,72,222,216
	DB	98,242,93,72,222,224
	vbroadcasti32x4	zmm0,ZMMWORD[224+rcx]
	DB	98,242,117,72,223,200
	DB	98,242,109,72,223,208
	DB	98,242,101,72,223,216
	DB	98,242,93,72,223,224
	vpxorq	zmm1,zmm1,zmm9
	vpxorq	zmm2,zmm2,zmm10
	vpxorq	zmm3,zmm3,zmm11
	vpxorq	zmm4,zmm4,zmm12

	vmovdqa32	zmm9,zmm15
	vmovdqa32	zmm10,zmm16
	vmovdqa32	zmm11,zmm17
	vmovdqa32	zmm12,zmm18
	vmovdqu8	ZMMWORD[rsi],zmm1
	vmovdqu8	ZMMWORD[64+rsi],zmm2
	vmovdqu8	ZMMWORD[128+rsi],zmm3
	vmovdqu8	ZMMWORD[192+rsi],zmm4
	add	rsi,0x100
	sub	r11,0x100
	cmp	r11,0x100
	jae	NEAR $L$_main_loop_run_16_amivrujEyduiFoi
	cmp	r11,0x80
	jae	NEAR $L$_main_loop_run_8_amivrujEyduiFoi
	jmp	NEAR $L$_do_n_blocks_amivrujEyduiFoi

$L$_start_by8_amivrujEyduiFoi:
	vbroadcasti32x4	zmm0,ZMMWORD[rsp]
	vbroadcasti32x4	zmm8,ZMMWORD[shufb_15_7]
	mov	r8,0xaa
	kmovq	k2,r8
	vpshufb	zmm1,zmm0,zmm8
	vpsllvq	zmm4,zmm0,ZMMWORD[const_dq3210]
	vpsrlvq	zmm2,zmm1,ZMMWORD[const_dq5678]
	DB	98,147,109,72,68,217,0
	vpxorq	zmm4{k2},zmm4,zmm2
	vpxord	zmm9,zmm3,zmm4
	vpsllvq	zmm5,zmm0,ZMMWORD[const_dq7654]
	vpsrlvq	zmm6,zmm1,ZMMWORD[const_dq1234]
	DB	98,147,77,72,68,249,0
	vpxorq	zmm5{k2},zmm5,zmm6
	vpxord	zmm10,zmm7,zmm5

$L$_main_loop_run_8_amivrujEyduiFoi:
	vmovdqu8	zmm1,ZMMWORD[rdi]
	vmovdqu8	zmm2,ZMMWORD[64+rdi]
	add	rdi,0x80
	vbroadcasti32x4	zmm0,ZMMWORD[rcx]
	vpternlogq	zmm1,zmm9,zmm0,0x96
	vpternlogq	zmm2,zmm10,zmm0,0x96
	vpsrldq	zmm13,zmm9,0xf
	DB	98,19,21,72,68,241,0
	vpslldq	zmm15,zmm9,0x1
	vpxord	zmm15,zmm15,zmm14
	vbroadcasti32x4	zmm0,ZMMWORD[16+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[32+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[48+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208
	vpsrldq	zmm13,zmm10,0xf
	DB	98,19,21,72,68,241,0
	vpslldq	zmm16,zmm10,0x1
	vpxord	zmm16,zmm16,zmm14

	vbroadcasti32x4	zmm0,ZMMWORD[64+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[80+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[96+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[112+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[128+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[144+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[160+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[176+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[192+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[208+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[224+rcx]
	DB	98,242,117,72,223,200
	DB	98,242,109,72,223,208
	vpxorq	zmm1,zmm1,zmm9
	vpxorq	zmm2,zmm2,zmm10
	vmovdqa32	zmm9,zmm15
	vmovdqa32	zmm10,zmm16
	vmovdqu8	ZMMWORD[rsi],zmm1
	vmovdqu8	ZMMWORD[64+rsi],zmm2
	add	rsi,0x80
	sub	r11,0x80
	cmp	r11,0x80
	jae	NEAR $L$_main_loop_run_8_amivrujEyduiFoi
	vextracti32x4	xmm0,zmm9,0x0
	vextracti32x4	xmm15,zmm9,0x1
	jmp	NEAR $L$_do_n_blocks_amivrujEyduiFoi

$L$_steal_cipher_with_tweak_amivrujEyduiFoi:

	vmovdqa	xmm11,XMMWORD[shufb_15_7]
	vpshufb	xmm12,xmm0,xmm11
	vpsllq	xmm13,xmm0,0x1
	vpsrlq	xmm14,xmm12,0x7
	DB	98,19,13,8,68,249,0
	vpxord	xmm15,xmm15,xmm13

$L$_steal_cipher_amivrujEyduiFoi:

	vmovdqu	xmm8,XMMWORD[rdi]
	vpxor	xmm8,xmm8,xmm15
	vpxor	xmm8,xmm8,XMMWORD[rcx]
	vaesdec	xmm8,xmm8,XMMWORD[16+rcx]
	vaesdec	xmm8,xmm8,XMMWORD[32+rcx]
	vaesdec	xmm8,xmm8,XMMWORD[48+rcx]
	vaesdec	xmm8,xmm8,XMMWORD[64+rcx]
	vaesdec	xmm8,xmm8,XMMWORD[80+rcx]
	vaesdec	xmm8,xmm8,XMMWORD[96+rcx]
	vaesdec	xmm8,xmm8,XMMWORD[112+rcx]
	vaesdec	xmm8,xmm8,XMMWORD[128+rcx]
	vaesdec	xmm8,xmm8,XMMWORD[144+rcx]
	vaesdec	xmm8,xmm8,XMMWORD[160+rcx]
	vaesdec	xmm8,xmm8,XMMWORD[176+rcx]
	vaesdec	xmm8,xmm8,XMMWORD[192+rcx]
	vaesdec	xmm8,xmm8,XMMWORD[208+rcx]
	vaesdeclast	xmm8,xmm8,XMMWORD[224+rcx]
	vpxor	xmm8,xmm8,xmm15




	mov	r11,1
	mov	r8,rcx
	mov	rcx,rdx
	shl	r11,cl
	sub	r11,1
	kmovq	k1,r11
	vmovdqu8	xmm9{k1}{z},[16+rdi]
	vmovdqu8	xmm10{k1}{z},xmm8
	vpblendmb	xmm9{k1},xmm8,xmm9


	mov	rcx,r8
	vpxor	xmm9,xmm9,xmm0
	vpxor	xmm9,xmm9,XMMWORD[rcx]
	vaesdec	xmm9,xmm9,XMMWORD[16+rcx]
	vaesdec	xmm9,xmm9,XMMWORD[32+rcx]
	vaesdec	xmm9,xmm9,XMMWORD[48+rcx]
	vaesdec	xmm9,xmm9,XMMWORD[64+rcx]
	vaesdec	xmm9,xmm9,XMMWORD[80+rcx]
	vaesdec	xmm9,xmm9,XMMWORD[96+rcx]
	vaesdec	xmm9,xmm9,XMMWORD[112+rcx]
	vaesdec	xmm9,xmm9,XMMWORD[128+rcx]
	vaesdec	xmm9,xmm9,XMMWORD[144+rcx]
	vaesdec	xmm9,xmm9,XMMWORD[160+rcx]
	vaesdec	xmm9,xmm9,XMMWORD[176+rcx]
	vaesdec	xmm9,xmm9,XMMWORD[192+rcx]
	vaesdec	xmm9,xmm9,XMMWORD[208+rcx]
	vaesdeclast	xmm9,xmm9,XMMWORD[224+rcx]
	vpxor	xmm9,xmm9,xmm0



	vmovdqu	XMMWORD[rsi],xmm9
	vmovdqu8	XMMWORD[16+rsi]{k1},xmm10
	jmp	NEAR $L$_ret_amivrujEyduiFoi

$L$_final_block_is_only_block_amivrujEyduiFoi:
	vmovdqa	xmm0,XMMWORD[rsp]
	and	rdx,0xf
	jne	NEAR $L$_steal_cipher_with_tweak_amivrujEyduiFoi

$L$_final_block_amivrujEyduiFoi:
	vmovdqa	xmm8,XMMWORD[rdi]
	vpxor	xmm8,xmm8,xmm0
	vpxor	xmm8,xmm8,XMMWORD[rcx]
	vaesdec	xmm8,xmm8,XMMWORD[16+rcx]
	vaesdec	xmm8,xmm8,XMMWORD[32+rcx]
	vaesdec	xmm8,xmm8,XMMWORD[48+rcx]
	vaesdec	xmm8,xmm8,XMMWORD[64+rcx]
	vaesdec	xmm8,xmm8,XMMWORD[80+rcx]
	vaesdec	xmm8,xmm8,XMMWORD[96+rcx]
	vaesdec	xmm8,xmm8,XMMWORD[112+rcx]
	vaesdec	xmm8,xmm8,XMMWORD[128+rcx]
	vaesdec	xmm8,xmm8,XMMWORD[144+rcx]
	vaesdec	xmm8,xmm8,XMMWORD[160+rcx]
	vaesdec	xmm8,xmm8,XMMWORD[176+rcx]
	vaesdec	xmm8,xmm8,XMMWORD[192+rcx]
	vaesdec	xmm8,xmm8,XMMWORD[208+rcx]
	vaesdeclast	xmm8,xmm8,XMMWORD[224+rcx]
	vpxor	xmm8,xmm8,xmm0
	vmovdqa	XMMWORD[rsi],xmm8

$L$_ret_amivrujEyduiFoi:
	mov	rbx,QWORD[288+rsp]
	xor	r8,r8
	mov	QWORD[288+rsp],r8
	vpxorq	zmm0,zmm0,zmm0
	mov	rdi,QWORD[((288 + 8))+rsp]
	mov	QWORD[((288 + 8))+rsp],r8
	mov	rsi,QWORD[((288 + 16))+rsp]
	mov	QWORD[((288 + 16))+rsp],r8

	vmovdqa	xmm6,XMMWORD[((128 + 0))+rsp]
	vmovdqa	xmm7,XMMWORD[((128 + 16))+rsp]
	vmovdqa	xmm8,XMMWORD[((128 + 32))+rsp]
	vmovdqa	xmm9,XMMWORD[((128 + 48))+rsp]


	vmovdqa64	ZMMWORD[128+rsp],zmm0

	vmovdqa	xmm10,XMMWORD[((128 + 64))+rsp]
	vmovdqa	xmm11,XMMWORD[((128 + 80))+rsp]
	vmovdqa	xmm12,XMMWORD[((128 + 96))+rsp]
	vmovdqa	xmm13,XMMWORD[((128 + 112))+rsp]


	vmovdqa64	ZMMWORD[(128 + 64)+rsp],zmm0

	vmovdqa	xmm14,XMMWORD[((128 + 128))+rsp]
	vmovdqa	xmm15,XMMWORD[((128 + 144))+rsp]



	vmovdqa	YMMWORD[(128 + 128)+rsp],ymm0
	mov	rsp,rbp
	pop	rbp
	vzeroupper
	mov	rdi,QWORD[8+rsp]	;WIN64 epilogue
	mov	rsi,QWORD[16+rsp]
	DB	0F3h,0C3h		;repret

$L$_less_than_128_bytes_amivrujEyduiFoi:
	vpbroadcastq	zmm25,r10
	cmp	r11,0x10
	jb	NEAR $L$_ret_amivrujEyduiFoi
	vbroadcasti32x4	zmm0,ZMMWORD[rsp]
	vbroadcasti32x4	zmm8,ZMMWORD[shufb_15_7]
	mov	r8d,0xaa
	kmovq	k2,r8
	mov	r8,r11
	and	r8,0x70
	cmp	r8,0x60
	je	NEAR $L$_num_blocks_is_6_amivrujEyduiFoi
	cmp	r8,0x50
	je	NEAR $L$_num_blocks_is_5_amivrujEyduiFoi
	cmp	r8,0x40
	je	NEAR $L$_num_blocks_is_4_amivrujEyduiFoi
	cmp	r8,0x30
	je	NEAR $L$_num_blocks_is_3_amivrujEyduiFoi
	cmp	r8,0x20
	je	NEAR $L$_num_blocks_is_2_amivrujEyduiFoi
	cmp	r8,0x10
	je	NEAR $L$_num_blocks_is_1_amivrujEyduiFoi

$L$_num_blocks_is_7_amivrujEyduiFoi:
	vpshufb	zmm1,zmm0,zmm8
	vpsllvq	zmm4,zmm0,ZMMWORD[const_dq3210]
	vpsrlvq	zmm2,zmm1,ZMMWORD[const_dq5678]
	DB	98,147,109,72,68,217,0
	vpxorq	zmm4{k2},zmm4,zmm2
	vpxord	zmm9,zmm3,zmm4
	vpsllvq	zmm5,zmm0,ZMMWORD[const_dq7654]
	vpsrlvq	zmm6,zmm1,ZMMWORD[const_dq1234]
	DB	98,147,77,72,68,249,0
	vpxorq	zmm5{k2},zmm5,zmm6
	vpxord	zmm10,zmm7,zmm5
	mov	r8,0x0000ffffffffffff
	kmovq	k1,r8
	vmovdqu8	zmm1,ZMMWORD[rdi]
	vmovdqu8	zmm2{k1},[64+rdi]

	add	rdi,0x70
	vbroadcasti32x4	zmm0,ZMMWORD[rcx]
	vpternlogq	zmm1,zmm9,zmm0,0x96
	vpternlogq	zmm2,zmm10,zmm0,0x96
	vbroadcasti32x4	zmm0,ZMMWORD[16+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[32+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[48+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208

	vbroadcasti32x4	zmm0,ZMMWORD[64+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[80+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[96+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[112+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[128+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[144+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[160+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[176+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[192+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[208+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[224+rcx]
	DB	98,242,117,72,223,200
	DB	98,242,109,72,223,208
	vpxorq	zmm1,zmm1,zmm9
	vpxorq	zmm2,zmm2,zmm10
	vmovdqu8	ZMMWORD[rsi],zmm1
	vmovdqu8	ZMMWORD[64+rsi]{k1},zmm2
	add	rsi,0x70

	vextracti32x4	xmm0,zmm10,0x3

	and	rdx,0xf
	je	NEAR $L$_final_block_amivrujEyduiFoi

	vpsrldq	zmm13,zmm9,0xf
	DB	98,19,21,72,68,241,0
	vpslldq	zmm11,zmm9,0x1
	vpxord	zmm11,zmm11,zmm14
	vextracti32x4	xmm15,zmm11,0x0
	jmp	NEAR $L$_steal_cipher_amivrujEyduiFoi
$L$_num_blocks_is_6_amivrujEyduiFoi:
	vpshufb	zmm1,zmm0,zmm8
	vpsllvq	zmm4,zmm0,ZMMWORD[const_dq3210]
	vpsrlvq	zmm2,zmm1,ZMMWORD[const_dq5678]
	DB	98,147,109,72,68,217,0
	vpxorq	zmm4{k2},zmm4,zmm2
	vpxord	zmm9,zmm3,zmm4
	vpsllvq	zmm5,zmm0,ZMMWORD[const_dq7654]
	vpsrlvq	zmm6,zmm1,ZMMWORD[const_dq1234]
	DB	98,147,77,72,68,249,0
	vpxorq	zmm5{k2},zmm5,zmm6
	vpxord	zmm10,zmm7,zmm5
	vmovdqu8	zmm1,ZMMWORD[rdi]
	vmovdqu8	ymm2,YMMWORD[64+rdi]
	add	rdi,96
	vbroadcasti32x4	zmm0,ZMMWORD[rcx]
	vpternlogq	zmm1,zmm9,zmm0,0x96
	vpternlogq	zmm2,zmm10,zmm0,0x96
	vbroadcasti32x4	zmm0,ZMMWORD[16+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[32+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[48+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208

	vbroadcasti32x4	zmm0,ZMMWORD[64+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[80+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[96+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[112+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[128+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[144+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[160+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[176+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[192+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[208+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[224+rcx]
	DB	98,242,117,72,223,200
	DB	98,242,109,72,223,208
	vpxorq	zmm1,zmm1,zmm9
	vpxorq	zmm2,zmm2,zmm10
	vmovdqu8	ZMMWORD[rsi],zmm1
	vmovdqu8	YMMWORD[64+rsi],ymm2
	add	rsi,96

	vextracti32x4	xmm0,zmm10,0x2
	vextracti32x4	xmm15,zmm10,0x3
	and	rdx,0xf
	je	NEAR $L$_final_block_amivrujEyduiFoi
	jmp	NEAR $L$_steal_cipher_amivrujEyduiFoi
$L$_num_blocks_is_5_amivrujEyduiFoi:
	vpshufb	zmm1,zmm0,zmm8
	vpsllvq	zmm4,zmm0,ZMMWORD[const_dq3210]
	vpsrlvq	zmm2,zmm1,ZMMWORD[const_dq5678]
	DB	98,147,109,72,68,217,0
	vpxorq	zmm4{k2},zmm4,zmm2
	vpxord	zmm9,zmm3,zmm4
	vpsllvq	zmm5,zmm0,ZMMWORD[const_dq7654]
	vpsrlvq	zmm6,zmm1,ZMMWORD[const_dq1234]
	DB	98,147,77,72,68,249,0
	vpxorq	zmm5{k2},zmm5,zmm6
	vpxord	zmm10,zmm7,zmm5
	vmovdqu8	zmm1,ZMMWORD[rdi]
	vmovdqu8	xmm2,XMMWORD[64+rdi]
	add	rdi,80
	vbroadcasti32x4	zmm0,ZMMWORD[rcx]
	vpternlogq	zmm1,zmm9,zmm0,0x96
	vpternlogq	zmm2,zmm10,zmm0,0x96
	vbroadcasti32x4	zmm0,ZMMWORD[16+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[32+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[48+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208

	vbroadcasti32x4	zmm0,ZMMWORD[64+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[80+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[96+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[112+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[128+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[144+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[160+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[176+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[192+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[208+rcx]
	DB	98,242,117,72,222,200
	DB	98,242,109,72,222,208


	vbroadcasti32x4	zmm0,ZMMWORD[224+rcx]
	DB	98,242,117,72,223,200
	DB	98,242,109,72,223,208
	vpxorq	zmm1,zmm1,zmm9
	vpxorq	zmm2,zmm2,zmm10
	vmovdqu8	ZMMWORD[rsi],zmm1
	vmovdqu8	XMMWORD[64+rsi],xmm2
	add	rsi,80

	vmovdqa	xmm8,xmm2
	vextracti32x4	xmm0,zmm10,0x1
	vextracti32x4	xmm15,zmm10,0x2
	and	rdx,0xf
	je	NEAR $L$_final_block_amivrujEyduiFoi
	jmp	NEAR $L$_steal_cipher_amivrujEyduiFoi
$L$_num_blocks_is_4_amivrujEyduiFoi:
	vpshufb	zmm1,zmm0,zmm8
	vpsllvq	zmm4,zmm0,ZMMWORD[const_dq3210]
	vpsrlvq	zmm2,zmm1,ZMMWORD[const_dq5678]
	DB	98,147,109,72,68,217,0
	vpxorq	zmm4{k2},zmm4,zmm2
	vpxord	zmm9,zmm3,zmm4
	vpsllvq	zmm5,zmm0,ZMMWORD[const_dq7654]
	vpsrlvq	zmm6,zmm1,ZMMWORD[const_dq1234]
	DB	98,147,77,72,68,249,0
	vpxorq	zmm5{k2},zmm5,zmm6
	vpxord	zmm10,zmm7,zmm5
	vmovdqu8	zmm1,ZMMWORD[rdi]
	add	rdi,64
	vbroadcasti32x4	zmm0,ZMMWORD[rcx]
	vpternlogq	zmm1,zmm9,zmm0,0x96
	vbroadcasti32x4	zmm0,ZMMWORD[16+rcx]
	DB	98,242,117,72,222,200
	vbroadcasti32x4	zmm0,ZMMWORD[32+rcx]
	DB	98,242,117,72,222,200
	vbroadcasti32x4	zmm0,ZMMWORD[48+rcx]
	DB	98,242,117,72,222,200
	vbroadcasti32x4	zmm0,ZMMWORD[64+rcx]
	DB	98,242,117,72,222,200
	vbroadcasti32x4	zmm0,ZMMWORD[80+rcx]
	DB	98,242,117,72,222,200
	vbroadcasti32x4	zmm0,ZMMWORD[96+rcx]
	DB	98,242,117,72,222,200
	vbroadcasti32x4	zmm0,ZMMWORD[112+rcx]
	DB	98,242,117,72,222,200
	vbroadcasti32x4	zmm0,ZMMWORD[128+rcx]
	DB	98,242,117,72,222,200
	vbroadcasti32x4	zmm0,ZMMWORD[144+rcx]
	DB	98,242,117,72,222,200
	vbroadcasti32x4	zmm0,ZMMWORD[160+rcx]
	DB	98,242,117,72,222,200
	vbroadcasti32x4	zmm0,ZMMWORD[176+rcx]
	DB	98,242,117,72,222,200
	vbroadcasti32x4	zmm0,ZMMWORD[192+rcx]
	DB	98,242,117,72,222,200
	vbroadcasti32x4	zmm0,ZMMWORD[208+rcx]
	DB	98,242,117,72,222,200
	vbroadcasti32x4	zmm0,ZMMWORD[224+rcx]
	DB	98,242,117,72,223,200
	vpxorq	zmm1,zmm1,zmm9
	vmovdqu8	ZMMWORD[rsi],zmm1
	add	rsi,64
	vmovdqa	xmm0,xmm10
	vextracti32x4	xmm15,zmm10,0x1
	and	rdx,0xf
	je	NEAR $L$_final_block_amivrujEyduiFoi
	jmp	NEAR $L$_steal_cipher_amivrujEyduiFoi
$L$_num_blocks_is_3_amivrujEyduiFoi:
	vpshufb	zmm1,zmm0,zmm8
	vpsllvq	zmm4,zmm0,ZMMWORD[const_dq3210]
	vpsrlvq	zmm2,zmm1,ZMMWORD[const_dq5678]
	DB	98,147,109,72,68,217,0
	vpxorq	zmm4{k2},zmm4,zmm2
	vpxord	zmm9,zmm3,zmm4
	vpsllvq	zmm5,zmm0,ZMMWORD[const_dq7654]
	vpsrlvq	zmm6,zmm1,ZMMWORD[const_dq1234]
	DB	98,147,77,72,68,249,0
	vpxorq	zmm5{k2},zmm5,zmm6
	vpxord	zmm10,zmm7,zmm5
	mov	r8,0x0000ffffffffffff
	kmovq	k1,r8
	vmovdqu8	zmm1{k1},[rdi]
	add	rdi,48
	vbroadcasti32x4	zmm0,ZMMWORD[rcx]
	vpternlogq	zmm1,zmm9,zmm0,0x96
	vbroadcasti32x4	zmm0,ZMMWORD[16+rcx]
	DB	98,242,117,72,222,200
	vbroadcasti32x4	zmm0,ZMMWORD[32+rcx]
	DB	98,242,117,72,222,200
	vbroadcasti32x4	zmm0,ZMMWORD[48+rcx]
	DB	98,242,117,72,222,200
	vbroadcasti32x4	zmm0,ZMMWORD[64+rcx]
	DB	98,242,117,72,222,200
	vbroadcasti32x4	zmm0,ZMMWORD[80+rcx]
	DB	98,242,117,72,222,200
	vbroadcasti32x4	zmm0,ZMMWORD[96+rcx]
	DB	98,242,117,72,222,200
	vbroadcasti32x4	zmm0,ZMMWORD[112+rcx]
	DB	98,242,117,72,222,200
	vbroadcasti32x4	zmm0,ZMMWORD[128+rcx]
	DB	98,242,117,72,222,200
	vbroadcasti32x4	zmm0,ZMMWORD[144+rcx]
	DB	98,242,117,72,222,200
	vbroadcasti32x4	zmm0,ZMMWORD[160+rcx]
	DB	98,242,117,72,222,200
	vbroadcasti32x4	zmm0,ZMMWORD[176+rcx]
	DB	98,242,117,72,222,200
	vbroadcasti32x4	zmm0,ZMMWORD[192+rcx]
	DB	98,242,117,72,222,200
	vbroadcasti32x4	zmm0,ZMMWORD[208+rcx]
	DB	98,242,117,72,222,200
	vbroadcasti32x4	zmm0,ZMMWORD[224+rcx]
	DB	98,242,117,72,223,200
	vpxorq	zmm1,zmm1,zmm9
	vmovdqu8	ZMMWORD[rsi]{k1},zmm1
	add	rsi,48
	vextracti32x4	xmm0,zmm9,3
	vextracti32x4	xmm15,zmm10,0
	and	rdx,0xf
	je	NEAR $L$_final_block_amivrujEyduiFoi
	jmp	NEAR $L$_steal_cipher_amivrujEyduiFoi
$L$_num_blocks_is_2_amivrujEyduiFoi:
	vpshufb	zmm1,zmm0,zmm8
	vpsllvq	zmm4,zmm0,ZMMWORD[const_dq3210]
	vpsrlvq	zmm2,zmm1,ZMMWORD[const_dq5678]
	DB	98,147,109,72,68,217,0
	vpxorq	zmm4{k2},zmm4,zmm2
	vpxord	zmm9,zmm3,zmm4

	vmovdqu8	ymm1,YMMWORD[rdi]
	add	rdi,32
	vbroadcasti32x4	ymm0,YMMWORD[rcx]
	vpternlogq	ymm1,ymm9,ymm0,0x96
	vbroadcasti32x4	ymm0,YMMWORD[16+rcx]
	DB	98,242,117,40,222,200
	vbroadcasti32x4	ymm0,YMMWORD[32+rcx]
	DB	98,242,117,40,222,200
	vbroadcasti32x4	ymm0,YMMWORD[48+rcx]
	DB	98,242,117,40,222,200
	vbroadcasti32x4	ymm0,YMMWORD[64+rcx]
	DB	98,242,117,40,222,200
	vbroadcasti32x4	ymm0,YMMWORD[80+rcx]
	DB	98,242,117,40,222,200
	vbroadcasti32x4	ymm0,YMMWORD[96+rcx]
	DB	98,242,117,40,222,200
	vbroadcasti32x4	ymm0,YMMWORD[112+rcx]
	DB	98,242,117,40,222,200
	vbroadcasti32x4	ymm0,YMMWORD[128+rcx]
	DB	98,242,117,40,222,200
	vbroadcasti32x4	ymm0,YMMWORD[144+rcx]
	DB	98,242,117,40,222,200
	vbroadcasti32x4	ymm0,YMMWORD[160+rcx]
	DB	98,242,117,40,222,200
	vbroadcasti32x4	ymm0,YMMWORD[176+rcx]
	DB	98,242,117,40,222,200
	vbroadcasti32x4	ymm0,YMMWORD[192+rcx]
	DB	98,242,117,40,222,200
	vbroadcasti32x4	ymm0,YMMWORD[208+rcx]
	DB	98,242,117,40,222,200
	vbroadcasti32x4	ymm0,YMMWORD[224+rcx]
	DB	98,242,117,40,223,200
	vpxorq	ymm1,ymm1,ymm9
	vmovdqu8	YMMWORD[rsi],ymm1
	add	rsi,32

	vextracti32x4	xmm0,zmm9,2
	vextracti32x4	xmm15,zmm9,3
	and	rdx,0xf
	je	NEAR $L$_final_block_amivrujEyduiFoi
	jmp	NEAR $L$_steal_cipher_amivrujEyduiFoi
$L$_num_blocks_is_1_amivrujEyduiFoi:
	vpshufb	zmm1,zmm0,zmm8
	vpsllvq	zmm4,zmm0,ZMMWORD[const_dq3210]
	vpsrlvq	zmm2,zmm1,ZMMWORD[const_dq5678]
	DB	98,147,109,72,68,217,0
	vpxorq	zmm4{k2},zmm4,zmm2
	vpxord	zmm9,zmm3,zmm4

	vmovdqu8	xmm1,XMMWORD[rdi]
	add	rdi,16
	vbroadcasti32x4	ymm0,YMMWORD[rcx]
	vpternlogq	ymm1,ymm9,ymm0,0x96
	vbroadcasti32x4	ymm0,YMMWORD[16+rcx]
	DB	98,242,117,40,222,200
	vbroadcasti32x4	ymm0,YMMWORD[32+rcx]
	DB	98,242,117,40,222,200
	vbroadcasti32x4	ymm0,YMMWORD[48+rcx]
	DB	98,242,117,40,222,200
	vbroadcasti32x4	ymm0,YMMWORD[64+rcx]
	DB	98,242,117,40,222,200
	vbroadcasti32x4	ymm0,YMMWORD[80+rcx]
	DB	98,242,117,40,222,200
	vbroadcasti32x4	ymm0,YMMWORD[96+rcx]
	DB	98,242,117,40,222,200
	vbroadcasti32x4	ymm0,YMMWORD[112+rcx]
	DB	98,242,117,40,222,200
	vbroadcasti32x4	ymm0,YMMWORD[128+rcx]
	DB	98,242,117,40,222,200
	vbroadcasti32x4	ymm0,YMMWORD[144+rcx]
	DB	98,242,117,40,222,200
	vbroadcasti32x4	ymm0,YMMWORD[160+rcx]
	DB	98,242,117,40,222,200
	vbroadcasti32x4	ymm0,YMMWORD[176+rcx]
	DB	98,242,117,40,222,200
	vbroadcasti32x4	ymm0,YMMWORD[192+rcx]
	DB	98,242,117,40,222,200
	vbroadcasti32x4	ymm0,YMMWORD[208+rcx]
	DB	98,242,117,40,222,200
	vbroadcasti32x4	ymm0,YMMWORD[224+rcx]
	DB	98,242,117,40,223,200
	vpxorq	ymm1,ymm1,ymm9
	vmovdqu8	XMMWORD[rsi],xmm1
	add	rsi,16

	vmovdqa	xmm8,xmm1
	vextracti32x4	xmm0,zmm9,1
	vextracti32x4	xmm15,zmm9,2
	and	rdx,0xf
	je	NEAR $L$_final_block_amivrujEyduiFoi
	jmp	NEAR $L$_steal_cipher_amivrujEyduiFoi

section	.rdata rdata align=8
ALIGN	16

vpshufb_shf_table:
	DQ	0x8786858483828100,0x8f8e8d8c8b8a8988
	DQ	0x0706050403020100,0x000e0d0c0b0a0908

mask1:
	DQ	0x8080808080808080,0x8080808080808080

const_dq3210:
	DQ	0,0,1,1,2,2,3,3
const_dq5678:
	DQ	8,8,7,7,6,6,5,5
const_dq7654:
	DQ	4,4,5,5,6,6,7,7
const_dq1234:
	DQ	4,4,3,3,2,2,1,1

shufb_15_7:
	DB	15,0xff,0xff,0xff,0xff,0xff,0xff,0xff,7,0xff,0xff
	DB	0xff,0xff,0xff,0xff,0xff

section	.text

%endif
%else
; Work around https://bugzilla.nasm.us/show_bug.cgi?id=3392738
ret
%endif
