// This file is generated from a similarly-named Perl script in the BoringSSL
// source tree. Do not edit by hand.

#include <openssl/asm_base.h>

#if !defined(OPENSSL_NO_ASM) && defined(OPENSSL_X86_64) && defined(__ELF__)
#ifndef MY_ASSEMBLER_IS_TOO_OLD_FOR_512AVX
.text	
.globl	aes_hw_xts_encrypt_avx512
.hidden aes_hw_xts_encrypt_avx512
.hidden	aes_hw_xts_encrypt_avx512
.type	aes_hw_xts_encrypt_avx512,@function
.align	32
aes_hw_xts_encrypt_avx512:
.cfi_startproc	
.byte	243,15,30,250
	pushq	%rbp
	movq	%rsp,%rbp
	subq	$136,%rsp
	andq	$0xffffffffffffffc0,%rsp
	movq	%rbx,128(%rsp)
	movq	$0x87,%r10
	vmovdqu	(%r9),%xmm1
	vpxor	(%r8),%xmm1,%xmm1
	vaesenc	16(%r8),%xmm1,%xmm1
	vaesenc	32(%r8),%xmm1,%xmm1
	vaesenc	48(%r8),%xmm1,%xmm1
	vaesenc	64(%r8),%xmm1,%xmm1
	vaesenc	80(%r8),%xmm1,%xmm1
	vaesenc	96(%r8),%xmm1,%xmm1
	vaesenc	112(%r8),%xmm1,%xmm1
	vaesenc	128(%r8),%xmm1,%xmm1
	vaesenc	144(%r8),%xmm1,%xmm1
	vaesenc	160(%r8),%xmm1,%xmm1
	vaesenc	176(%r8),%xmm1,%xmm1
	vaesenc	192(%r8),%xmm1,%xmm1
	vaesenc	208(%r8),%xmm1,%xmm1
	vaesenclast	224(%r8),%xmm1,%xmm1
	vmovdqa	%xmm1,(%rsp)

	cmpq	$0x80,%rdx
	jl	.L_less_than_128_bytes_hEgxyDlCngwrfFe
	vpbroadcastq	%r10,%zmm25
	cmpq	$0x100,%rdx
	jge	.L_start_by16_hEgxyDlCngwrfFe
	cmpq	$0x80,%rdx
	jge	.L_start_by8_hEgxyDlCngwrfFe

.L_do_n_blocks_hEgxyDlCngwrfFe:
	cmpq	$0x0,%rdx
	je	.L_ret_hEgxyDlCngwrfFe
	cmpq	$0x70,%rdx
	jge	.L_remaining_num_blocks_is_7_hEgxyDlCngwrfFe
	cmpq	$0x60,%rdx
	jge	.L_remaining_num_blocks_is_6_hEgxyDlCngwrfFe
	cmpq	$0x50,%rdx
	jge	.L_remaining_num_blocks_is_5_hEgxyDlCngwrfFe
	cmpq	$0x40,%rdx
	jge	.L_remaining_num_blocks_is_4_hEgxyDlCngwrfFe
	cmpq	$0x30,%rdx
	jge	.L_remaining_num_blocks_is_3_hEgxyDlCngwrfFe
	cmpq	$0x20,%rdx
	jge	.L_remaining_num_blocks_is_2_hEgxyDlCngwrfFe
	cmpq	$0x10,%rdx
	jge	.L_remaining_num_blocks_is_1_hEgxyDlCngwrfFe
	vmovdqa	%xmm0,%xmm8
	vmovdqa	%xmm9,%xmm0
	jmp	.L_steal_cipher_hEgxyDlCngwrfFe

.L_remaining_num_blocks_is_7_hEgxyDlCngwrfFe:
	movq	$0x0000ffffffffffff,%r8
	kmovq	%r8,%k1
	vmovdqu8	(%rdi),%zmm1
	vmovdqu8	64(%rdi),%zmm2{%k1}
	addq	$0x70,%rdi
	vbroadcasti32x4	(%rcx),%zmm0
	vpternlogq	$0x96,%zmm0,%zmm9,%zmm1
	vpternlogq	$0x96,%zmm0,%zmm10,%zmm2
	vbroadcasti32x4	16(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	32(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	48(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208

	vbroadcasti32x4	64(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	80(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	96(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	112(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	128(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	144(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	160(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	176(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	192(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	208(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	224(%rcx),%zmm0
.byte	98,242,117,72,221,200
.byte	98,242,109,72,221,208
	vpxorq	%zmm9,%zmm1,%zmm1
	vpxorq	%zmm10,%zmm2,%zmm2
	vmovdqu8	%zmm1,(%rsi)
	vmovdqu8	%zmm2,64(%rsi){%k1}
	addq	$0x70,%rsi
	vextracti32x4	$0x2,%zmm2,%xmm8
	vextracti32x4	$0x3,%zmm10,%xmm0
	andq	$0xf,%rdx
	je	.L_ret_hEgxyDlCngwrfFe
	jmp	.L_steal_cipher_hEgxyDlCngwrfFe

.L_remaining_num_blocks_is_6_hEgxyDlCngwrfFe:
	vmovdqu8	(%rdi),%zmm1
	vmovdqu8	64(%rdi),%ymm2
	addq	$0x60,%rdi
	vbroadcasti32x4	(%rcx),%zmm0
	vpternlogq	$0x96,%zmm0,%zmm9,%zmm1
	vpternlogq	$0x96,%zmm0,%zmm10,%zmm2
	vbroadcasti32x4	16(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	32(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	48(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208

	vbroadcasti32x4	64(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	80(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	96(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	112(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	128(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	144(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	160(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	176(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	192(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	208(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	224(%rcx),%zmm0
.byte	98,242,117,72,221,200
.byte	98,242,109,72,221,208
	vpxorq	%zmm9,%zmm1,%zmm1
	vpxorq	%zmm10,%zmm2,%zmm2
	vmovdqu8	%zmm1,(%rsi)
	vmovdqu8	%ymm2,64(%rsi)
	addq	$0x60,%rsi
	vextracti32x4	$0x1,%zmm2,%xmm8
	vextracti32x4	$0x2,%zmm10,%xmm0
	andq	$0xf,%rdx
	je	.L_ret_hEgxyDlCngwrfFe
	jmp	.L_steal_cipher_hEgxyDlCngwrfFe

.L_remaining_num_blocks_is_5_hEgxyDlCngwrfFe:
	vmovdqu8	(%rdi),%zmm1
	vmovdqu	64(%rdi),%xmm2
	addq	$0x50,%rdi
	vbroadcasti32x4	(%rcx),%zmm0
	vpternlogq	$0x96,%zmm0,%zmm9,%zmm1
	vpternlogq	$0x96,%zmm0,%zmm10,%zmm2
	vbroadcasti32x4	16(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	32(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	48(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208

	vbroadcasti32x4	64(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	80(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	96(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	112(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	128(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	144(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	160(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	176(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	192(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	208(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	224(%rcx),%zmm0
.byte	98,242,117,72,221,200
.byte	98,242,109,72,221,208
	vpxorq	%zmm9,%zmm1,%zmm1
	vpxorq	%zmm10,%zmm2,%zmm2
	vmovdqu8	%zmm1,(%rsi)
	vmovdqu	%xmm2,64(%rsi)
	addq	$0x50,%rsi
	vmovdqa	%xmm2,%xmm8
	vextracti32x4	$0x1,%zmm10,%xmm0
	andq	$0xf,%rdx
	je	.L_ret_hEgxyDlCngwrfFe
	jmp	.L_steal_cipher_hEgxyDlCngwrfFe

.L_remaining_num_blocks_is_4_hEgxyDlCngwrfFe:
	vmovdqu8	(%rdi),%zmm1
	addq	$0x40,%rdi
	vbroadcasti32x4	(%rcx),%zmm0
	vpternlogq	$0x96,%zmm0,%zmm9,%zmm1
	vbroadcasti32x4	16(%rcx),%zmm0
.byte	98,242,117,72,220,200
	vbroadcasti32x4	32(%rcx),%zmm0
.byte	98,242,117,72,220,200
	vbroadcasti32x4	48(%rcx),%zmm0
.byte	98,242,117,72,220,200
	vbroadcasti32x4	64(%rcx),%zmm0
.byte	98,242,117,72,220,200
	vbroadcasti32x4	80(%rcx),%zmm0
.byte	98,242,117,72,220,200
	vbroadcasti32x4	96(%rcx),%zmm0
.byte	98,242,117,72,220,200
	vbroadcasti32x4	112(%rcx),%zmm0
.byte	98,242,117,72,220,200
	vbroadcasti32x4	128(%rcx),%zmm0
.byte	98,242,117,72,220,200
	vbroadcasti32x4	144(%rcx),%zmm0
.byte	98,242,117,72,220,200
	vbroadcasti32x4	160(%rcx),%zmm0
.byte	98,242,117,72,220,200
	vbroadcasti32x4	176(%rcx),%zmm0
.byte	98,242,117,72,220,200
	vbroadcasti32x4	192(%rcx),%zmm0
.byte	98,242,117,72,220,200
	vbroadcasti32x4	208(%rcx),%zmm0
.byte	98,242,117,72,220,200
	vbroadcasti32x4	224(%rcx),%zmm0
.byte	98,242,117,72,221,200
	vpxorq	%zmm9,%zmm1,%zmm1
	vmovdqu8	%zmm1,(%rsi)
	addq	$0x40,%rsi
	vextracti32x4	$0x3,%zmm1,%xmm8
	vmovdqa64	%xmm10,%xmm0
	andq	$0xf,%rdx
	je	.L_ret_hEgxyDlCngwrfFe
	jmp	.L_steal_cipher_hEgxyDlCngwrfFe
.L_remaining_num_blocks_is_3_hEgxyDlCngwrfFe:
	movq	$-1,%r8
	shrq	$0x10,%r8
	kmovq	%r8,%k1
	vmovdqu8	(%rdi),%zmm1{%k1}
	addq	$0x30,%rdi
	vbroadcasti32x4	(%rcx),%zmm0
	vpternlogq	$0x96,%zmm0,%zmm9,%zmm1
	vbroadcasti32x4	16(%rcx),%zmm0
.byte	98,242,117,72,220,200
	vbroadcasti32x4	32(%rcx),%zmm0
.byte	98,242,117,72,220,200
	vbroadcasti32x4	48(%rcx),%zmm0
.byte	98,242,117,72,220,200
	vbroadcasti32x4	64(%rcx),%zmm0
.byte	98,242,117,72,220,200
	vbroadcasti32x4	80(%rcx),%zmm0
.byte	98,242,117,72,220,200
	vbroadcasti32x4	96(%rcx),%zmm0
.byte	98,242,117,72,220,200
	vbroadcasti32x4	112(%rcx),%zmm0
.byte	98,242,117,72,220,200
	vbroadcasti32x4	128(%rcx),%zmm0
.byte	98,242,117,72,220,200
	vbroadcasti32x4	144(%rcx),%zmm0
.byte	98,242,117,72,220,200
	vbroadcasti32x4	160(%rcx),%zmm0
.byte	98,242,117,72,220,200
	vbroadcasti32x4	176(%rcx),%zmm0
.byte	98,242,117,72,220,200
	vbroadcasti32x4	192(%rcx),%zmm0
.byte	98,242,117,72,220,200
	vbroadcasti32x4	208(%rcx),%zmm0
.byte	98,242,117,72,220,200
	vbroadcasti32x4	224(%rcx),%zmm0
.byte	98,242,117,72,221,200
	vpxorq	%zmm9,%zmm1,%zmm1
	vmovdqu8	%zmm1,(%rsi){%k1}
	addq	$0x30,%rsi
	vextracti32x4	$0x2,%zmm1,%xmm8
	vextracti32x4	$0x3,%zmm9,%xmm0
	andq	$0xf,%rdx
	je	.L_ret_hEgxyDlCngwrfFe
	jmp	.L_steal_cipher_hEgxyDlCngwrfFe
.L_remaining_num_blocks_is_2_hEgxyDlCngwrfFe:
	vmovdqu8	(%rdi),%ymm1
	addq	$0x20,%rdi
	vbroadcasti32x4	(%rcx),%ymm0
	vpternlogq	$0x96,%ymm0,%ymm9,%ymm1
	vbroadcasti32x4	16(%rcx),%ymm0
.byte	98,242,117,40,220,200
	vbroadcasti32x4	32(%rcx),%ymm0
.byte	98,242,117,40,220,200
	vbroadcasti32x4	48(%rcx),%ymm0
.byte	98,242,117,40,220,200
	vbroadcasti32x4	64(%rcx),%ymm0
.byte	98,242,117,40,220,200
	vbroadcasti32x4	80(%rcx),%ymm0
.byte	98,242,117,40,220,200
	vbroadcasti32x4	96(%rcx),%ymm0
.byte	98,242,117,40,220,200
	vbroadcasti32x4	112(%rcx),%ymm0
.byte	98,242,117,40,220,200
	vbroadcasti32x4	128(%rcx),%ymm0
.byte	98,242,117,40,220,200
	vbroadcasti32x4	144(%rcx),%ymm0
.byte	98,242,117,40,220,200
	vbroadcasti32x4	160(%rcx),%ymm0
.byte	98,242,117,40,220,200
	vbroadcasti32x4	176(%rcx),%ymm0
.byte	98,242,117,40,220,200
	vbroadcasti32x4	192(%rcx),%ymm0
.byte	98,242,117,40,220,200
	vbroadcasti32x4	208(%rcx),%ymm0
.byte	98,242,117,40,220,200
	vbroadcasti32x4	224(%rcx),%ymm0
.byte	98,242,117,40,221,200
	vpxorq	%ymm9,%ymm1,%ymm1
	vmovdqu	%ymm1,(%rsi)
	addq	$0x20,%rsi
	vextracti32x4	$0x1,%zmm1,%xmm8
	vextracti32x4	$0x2,%zmm9,%xmm0
	andq	$0xf,%rdx
	je	.L_ret_hEgxyDlCngwrfFe
	jmp	.L_steal_cipher_hEgxyDlCngwrfFe
.L_remaining_num_blocks_is_1_hEgxyDlCngwrfFe:
	vmovdqu	(%rdi),%xmm1
	addq	$0x10,%rdi
	vpxor	%xmm9,%xmm1,%xmm1
	vpxor	(%rcx),%xmm1,%xmm1
	vaesenc	16(%rcx),%xmm1,%xmm1
	vaesenc	32(%rcx),%xmm1,%xmm1
	vaesenc	48(%rcx),%xmm1,%xmm1
	vaesenc	64(%rcx),%xmm1,%xmm1
	vaesenc	80(%rcx),%xmm1,%xmm1
	vaesenc	96(%rcx),%xmm1,%xmm1
	vaesenc	112(%rcx),%xmm1,%xmm1
	vaesenc	128(%rcx),%xmm1,%xmm1
	vaesenc	144(%rcx),%xmm1,%xmm1
	vaesenc	160(%rcx),%xmm1,%xmm1
	vaesenc	176(%rcx),%xmm1,%xmm1
	vaesenc	192(%rcx),%xmm1,%xmm1
	vaesenc	208(%rcx),%xmm1,%xmm1
	vaesenclast	224(%rcx),%xmm1,%xmm1
	vpxor	%xmm9,%xmm1,%xmm1
	vmovdqu	%xmm1,(%rsi)
	addq	$0x10,%rsi
	vmovdqa	%xmm1,%xmm8
	vextracti32x4	$0x1,%zmm9,%xmm0
	andq	$0xf,%rdx
	je	.L_ret_hEgxyDlCngwrfFe
	jmp	.L_steal_cipher_hEgxyDlCngwrfFe



.L_start_by16_hEgxyDlCngwrfFe:
	vbroadcasti32x4	(%rsp),%zmm0
	vbroadcasti32x4	shufb_15_7(%rip),%zmm8
	movq	$0xaa,%r8
	kmovq	%r8,%k2
	vpshufb	%zmm8,%zmm0,%zmm1


	vpsllvq	const_dq3210(%rip),%zmm0,%zmm4
	vpsrlvq	const_dq5678(%rip),%zmm1,%zmm2
.byte	98,147,109,72,68,217,0
	vpxorq	%zmm2,%zmm4,%zmm4{%k2}
	vpxord	%zmm4,%zmm3,%zmm9


	vpsllvq	const_dq7654(%rip),%zmm0,%zmm5
	vpsrlvq	const_dq1234(%rip),%zmm1,%zmm6
.byte	98,147,77,72,68,249,0
	vpxorq	%zmm6,%zmm5,%zmm5{%k2}
	vpxord	%zmm5,%zmm7,%zmm10


	vpsrldq	$0xf,%zmm9,%zmm13
.byte	98,19,21,72,68,241,0
	vpslldq	$0x1,%zmm9,%zmm11
	vpxord	%zmm14,%zmm11,%zmm11


	vpsrldq	$0xf,%zmm10,%zmm15
.byte	98,131,5,72,68,193,0
	vpslldq	$0x1,%zmm10,%zmm12
	vpxord	%zmm16,%zmm12,%zmm12

.L_main_loop_run_16_hEgxyDlCngwrfFe:
	vmovdqu8	(%rdi),%zmm1
	vmovdqu8	64(%rdi),%zmm2
	vmovdqu8	128(%rdi),%zmm3
	vmovdqu8	192(%rdi),%zmm4
	addq	$0x100,%rdi
	vpxorq	%zmm9,%zmm1,%zmm1
	vpxorq	%zmm10,%zmm2,%zmm2
	vpxorq	%zmm11,%zmm3,%zmm3
	vpxorq	%zmm12,%zmm4,%zmm4
	vbroadcasti32x4	(%rcx),%zmm0
	vpxorq	%zmm0,%zmm1,%zmm1
	vpxorq	%zmm0,%zmm2,%zmm2
	vpxorq	%zmm0,%zmm3,%zmm3
	vpxorq	%zmm0,%zmm4,%zmm4
	vpsrldq	$0xf,%zmm11,%zmm13
.byte	98,19,21,72,68,241,0
	vpslldq	$0x1,%zmm11,%zmm15
	vpxord	%zmm14,%zmm15,%zmm15
	vbroadcasti32x4	16(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208
.byte	98,242,101,72,220,216
.byte	98,242,93,72,220,224
	vbroadcasti32x4	32(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208
.byte	98,242,101,72,220,216
.byte	98,242,93,72,220,224
	vbroadcasti32x4	48(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208
.byte	98,242,101,72,220,216
.byte	98,242,93,72,220,224
	vpsrldq	$0xf,%zmm12,%zmm13
.byte	98,19,21,72,68,241,0
	vpslldq	$0x1,%zmm12,%zmm16
	vpxord	%zmm14,%zmm16,%zmm16
	vbroadcasti32x4	64(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208
.byte	98,242,101,72,220,216
.byte	98,242,93,72,220,224
	vbroadcasti32x4	80(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208
.byte	98,242,101,72,220,216
.byte	98,242,93,72,220,224
	vbroadcasti32x4	96(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208
.byte	98,242,101,72,220,216
.byte	98,242,93,72,220,224
	vpsrldq	$0xf,%zmm15,%zmm13
.byte	98,19,21,72,68,241,0
	vpslldq	$0x1,%zmm15,%zmm17
	vpxord	%zmm14,%zmm17,%zmm17
	vbroadcasti32x4	112(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208
.byte	98,242,101,72,220,216
.byte	98,242,93,72,220,224
	vbroadcasti32x4	128(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208
.byte	98,242,101,72,220,216
.byte	98,242,93,72,220,224
	vbroadcasti32x4	144(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208
.byte	98,242,101,72,220,216
.byte	98,242,93,72,220,224
	vpsrldq	$0xf,%zmm16,%zmm13
.byte	98,19,21,72,68,241,0
	vpslldq	$0x1,%zmm16,%zmm18
	vpxord	%zmm14,%zmm18,%zmm18
	vbroadcasti32x4	160(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208
.byte	98,242,101,72,220,216
.byte	98,242,93,72,220,224
	vbroadcasti32x4	176(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208
.byte	98,242,101,72,220,216
.byte	98,242,93,72,220,224
	vbroadcasti32x4	192(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208
.byte	98,242,101,72,220,216
.byte	98,242,93,72,220,224
	vbroadcasti32x4	208(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208
.byte	98,242,101,72,220,216
.byte	98,242,93,72,220,224
	vbroadcasti32x4	224(%rcx),%zmm0
.byte	98,242,117,72,221,200
.byte	98,242,109,72,221,208
.byte	98,242,101,72,221,216
.byte	98,242,93,72,221,224
	vpxorq	%zmm9,%zmm1,%zmm1
	vpxorq	%zmm10,%zmm2,%zmm2
	vpxorq	%zmm11,%zmm3,%zmm3
	vpxorq	%zmm12,%zmm4,%zmm4

	vmovdqa32	%zmm15,%zmm9
	vmovdqa32	%zmm16,%zmm10
	vmovdqa32	%zmm17,%zmm11
	vmovdqa32	%zmm18,%zmm12
	vmovdqu8	%zmm1,(%rsi)
	vmovdqu8	%zmm2,64(%rsi)
	vmovdqu8	%zmm3,128(%rsi)
	vmovdqu8	%zmm4,192(%rsi)
	addq	$0x100,%rsi
	subq	$0x100,%rdx
	cmpq	$0x100,%rdx
	jae	.L_main_loop_run_16_hEgxyDlCngwrfFe
	cmpq	$0x80,%rdx
	jae	.L_main_loop_run_8_hEgxyDlCngwrfFe
	vextracti32x4	$0x3,%zmm4,%xmm0
	jmp	.L_do_n_blocks_hEgxyDlCngwrfFe

.L_start_by8_hEgxyDlCngwrfFe:
	vbroadcasti32x4	(%rsp),%zmm0
	vbroadcasti32x4	shufb_15_7(%rip),%zmm8
	movq	$0xaa,%r8
	kmovq	%r8,%k2
	vpshufb	%zmm8,%zmm0,%zmm1
	vpsllvq	const_dq3210(%rip),%zmm0,%zmm4
	vpsrlvq	const_dq5678(%rip),%zmm1,%zmm2
.byte	98,147,109,72,68,217,0
	vpxorq	%zmm2,%zmm4,%zmm4{%k2}
	vpxord	%zmm4,%zmm3,%zmm9
	vpsllvq	const_dq7654(%rip),%zmm0,%zmm5
	vpsrlvq	const_dq1234(%rip),%zmm1,%zmm6
.byte	98,147,77,72,68,249,0
	vpxorq	%zmm6,%zmm5,%zmm5{%k2}
	vpxord	%zmm5,%zmm7,%zmm10

.L_main_loop_run_8_hEgxyDlCngwrfFe:
	vmovdqu8	(%rdi),%zmm1
	vmovdqu8	64(%rdi),%zmm2
	addq	$0x80,%rdi
	vbroadcasti32x4	(%rcx),%zmm0
	vpternlogq	$0x96,%zmm0,%zmm9,%zmm1
	vpternlogq	$0x96,%zmm0,%zmm10,%zmm2
	vpsrldq	$0xf,%zmm9,%zmm13
.byte	98,19,21,72,68,241,0
	vpslldq	$0x1,%zmm9,%zmm15
	vpxord	%zmm14,%zmm15,%zmm15
	vbroadcasti32x4	16(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	32(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	48(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208
	vpsrldq	$0xf,%zmm10,%zmm13
.byte	98,19,21,72,68,241,0
	vpslldq	$0x1,%zmm10,%zmm16
	vpxord	%zmm14,%zmm16,%zmm16

	vbroadcasti32x4	64(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	80(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	96(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	112(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	128(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	144(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	160(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	176(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	192(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	208(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	224(%rcx),%zmm0
.byte	98,242,117,72,221,200
.byte	98,242,109,72,221,208
	vpxorq	%zmm9,%zmm1,%zmm1
	vpxorq	%zmm10,%zmm2,%zmm2
	vmovdqa32	%zmm15,%zmm9
	vmovdqa32	%zmm16,%zmm10
	vmovdqu8	%zmm1,(%rsi)
	vmovdqu8	%zmm2,64(%rsi)
	addq	$0x80,%rsi
	subq	$0x80,%rdx
	cmpq	$0x80,%rdx
	jae	.L_main_loop_run_8_hEgxyDlCngwrfFe
	vextracti32x4	$0x3,%zmm2,%xmm0
	jmp	.L_do_n_blocks_hEgxyDlCngwrfFe

.L_steal_cipher_hEgxyDlCngwrfFe:
	vmovdqa	%xmm8,%xmm2
	leaq	vpshufb_shf_table(%rip),%rax
	vmovdqu	(%rax,%rdx,1),%xmm10
	vpshufb	%xmm10,%xmm8,%xmm8
	vmovdqu	-16(%rdi,%rdx,1),%xmm3
	vmovdqu	%xmm8,-16(%rsi,%rdx,1)
	leaq	vpshufb_shf_table(%rip),%rax
	addq	$16,%rax
	subq	%rdx,%rax
	vmovdqu	(%rax),%xmm10
	vpxor	mask1(%rip),%xmm10,%xmm10
	vpshufb	%xmm10,%xmm3,%xmm3
	vpblendvb	%xmm10,%xmm2,%xmm3,%xmm3
	vpxor	%xmm0,%xmm3,%xmm8
	vpxor	(%rcx),%xmm8,%xmm8
	vaesenc	16(%rcx),%xmm8,%xmm8
	vaesenc	32(%rcx),%xmm8,%xmm8
	vaesenc	48(%rcx),%xmm8,%xmm8
	vaesenc	64(%rcx),%xmm8,%xmm8
	vaesenc	80(%rcx),%xmm8,%xmm8
	vaesenc	96(%rcx),%xmm8,%xmm8
	vaesenc	112(%rcx),%xmm8,%xmm8
	vaesenc	128(%rcx),%xmm8,%xmm8
	vaesenc	144(%rcx),%xmm8,%xmm8
	vaesenc	160(%rcx),%xmm8,%xmm8
	vaesenc	176(%rcx),%xmm8,%xmm8
	vaesenc	192(%rcx),%xmm8,%xmm8
	vaesenc	208(%rcx),%xmm8,%xmm8
	vaesenclast	224(%rcx),%xmm8,%xmm8
	vpxor	%xmm0,%xmm8,%xmm8
	vmovdqu	%xmm8,-16(%rsi)

.L_ret_hEgxyDlCngwrfFe:
	movq	128(%rsp),%rbx
	xorq	%r8,%r8
	movq	%r8,128(%rsp)
	vpxorq	%zmm0,%zmm0,%zmm0
	movq	%rbp,%rsp
	popq	%rbp
	vzeroupper
	.byte	0xf3,0xc3

.L_less_than_128_bytes_hEgxyDlCngwrfFe:
	vpbroadcastq	%r10,%zmm25
	cmpq	$0x10,%rdx
	jb	.L_ret_hEgxyDlCngwrfFe
	vbroadcasti32x4	(%rsp),%zmm0
	vbroadcasti32x4	shufb_15_7(%rip),%zmm8
	movl	$0xaa,%r8d
	kmovq	%r8,%k2
	movq	%rdx,%r8
	andq	$0x70,%r8
	cmpq	$0x60,%r8
	je	.L_num_blocks_is_6_hEgxyDlCngwrfFe
	cmpq	$0x50,%r8
	je	.L_num_blocks_is_5_hEgxyDlCngwrfFe
	cmpq	$0x40,%r8
	je	.L_num_blocks_is_4_hEgxyDlCngwrfFe
	cmpq	$0x30,%r8
	je	.L_num_blocks_is_3_hEgxyDlCngwrfFe
	cmpq	$0x20,%r8
	je	.L_num_blocks_is_2_hEgxyDlCngwrfFe
	cmpq	$0x10,%r8
	je	.L_num_blocks_is_1_hEgxyDlCngwrfFe

.L_num_blocks_is_7_hEgxyDlCngwrfFe:
	vpshufb	%zmm8,%zmm0,%zmm1
	vpsllvq	const_dq3210(%rip),%zmm0,%zmm4
	vpsrlvq	const_dq5678(%rip),%zmm1,%zmm2
.byte	98,147,109,72,68,217,0
	vpxorq	%zmm2,%zmm4,%zmm4{%k2}
	vpxord	%zmm4,%zmm3,%zmm9
	vpsllvq	const_dq7654(%rip),%zmm0,%zmm5
	vpsrlvq	const_dq1234(%rip),%zmm1,%zmm6
.byte	98,147,77,72,68,249,0
	vpxorq	%zmm6,%zmm5,%zmm5{%k2}
	vpxord	%zmm5,%zmm7,%zmm10
	movq	$0x0000ffffffffffff,%r8
	kmovq	%r8,%k1
	vmovdqu8	0(%rdi),%zmm1
	vmovdqu8	64(%rdi),%zmm2{%k1}

	addq	$0x70,%rdi
	vbroadcasti32x4	(%rcx),%zmm0
	vpternlogq	$0x96,%zmm0,%zmm9,%zmm1
	vpternlogq	$0x96,%zmm0,%zmm10,%zmm2
	vbroadcasti32x4	16(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	32(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	48(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208

	vbroadcasti32x4	64(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	80(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	96(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	112(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	128(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	144(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	160(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	176(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	192(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	208(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	224(%rcx),%zmm0
.byte	98,242,117,72,221,200
.byte	98,242,109,72,221,208
	vpxorq	%zmm9,%zmm1,%zmm1
	vpxorq	%zmm10,%zmm2,%zmm2
	vmovdqu8	%zmm1,0(%rsi)
	vmovdqu8	%zmm2,64(%rsi){%k1}
	addq	$0x70,%rsi
	vextracti32x4	$0x2,%zmm2,%xmm8
	vextracti32x4	$0x3,%zmm10,%xmm0
	andq	$0xf,%rdx
	je	.L_ret_hEgxyDlCngwrfFe
	jmp	.L_steal_cipher_hEgxyDlCngwrfFe
.L_num_blocks_is_6_hEgxyDlCngwrfFe:
	vpshufb	%zmm8,%zmm0,%zmm1
	vpsllvq	const_dq3210(%rip),%zmm0,%zmm4
	vpsrlvq	const_dq5678(%rip),%zmm1,%zmm2
.byte	98,147,109,72,68,217,0
	vpxorq	%zmm2,%zmm4,%zmm4{%k2}
	vpxord	%zmm4,%zmm3,%zmm9
	vpsllvq	const_dq7654(%rip),%zmm0,%zmm5
	vpsrlvq	const_dq1234(%rip),%zmm1,%zmm6
.byte	98,147,77,72,68,249,0
	vpxorq	%zmm6,%zmm5,%zmm5{%k2}
	vpxord	%zmm5,%zmm7,%zmm10
	vmovdqu8	0(%rdi),%zmm1
	vmovdqu8	64(%rdi),%ymm2
	addq	$96,%rdi
	vbroadcasti32x4	(%rcx),%zmm0
	vpternlogq	$0x96,%zmm0,%zmm9,%zmm1
	vpternlogq	$0x96,%zmm0,%zmm10,%zmm2
	vbroadcasti32x4	16(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	32(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	48(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208

	vbroadcasti32x4	64(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	80(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	96(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	112(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	128(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	144(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	160(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	176(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	192(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	208(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	224(%rcx),%zmm0
.byte	98,242,117,72,221,200
.byte	98,242,109,72,221,208
	vpxorq	%zmm9,%zmm1,%zmm1
	vpxorq	%zmm10,%zmm2,%zmm2
	vmovdqu8	%zmm1,0(%rsi)
	vmovdqu8	%ymm2,64(%rsi)
	addq	$96,%rsi

	vextracti32x4	$0x1,%ymm2,%xmm8
	vextracti32x4	$0x2,%zmm10,%xmm0
	andq	$0xf,%rdx
	je	.L_ret_hEgxyDlCngwrfFe
	jmp	.L_steal_cipher_hEgxyDlCngwrfFe
.L_num_blocks_is_5_hEgxyDlCngwrfFe:
	vpshufb	%zmm8,%zmm0,%zmm1
	vpsllvq	const_dq3210(%rip),%zmm0,%zmm4
	vpsrlvq	const_dq5678(%rip),%zmm1,%zmm2
.byte	98,147,109,72,68,217,0
	vpxorq	%zmm2,%zmm4,%zmm4{%k2}
	vpxord	%zmm4,%zmm3,%zmm9
	vpsllvq	const_dq7654(%rip),%zmm0,%zmm5
	vpsrlvq	const_dq1234(%rip),%zmm1,%zmm6
.byte	98,147,77,72,68,249,0
	vpxorq	%zmm6,%zmm5,%zmm5{%k2}
	vpxord	%zmm5,%zmm7,%zmm10
	vmovdqu8	0(%rdi),%zmm1
	vmovdqu8	64(%rdi),%xmm2
	addq	$80,%rdi
	vbroadcasti32x4	(%rcx),%zmm0
	vpternlogq	$0x96,%zmm0,%zmm9,%zmm1
	vpternlogq	$0x96,%zmm0,%zmm10,%zmm2
	vbroadcasti32x4	16(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	32(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	48(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208

	vbroadcasti32x4	64(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	80(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	96(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	112(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	128(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	144(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	160(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	176(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	192(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	208(%rcx),%zmm0
.byte	98,242,117,72,220,200
.byte	98,242,109,72,220,208


	vbroadcasti32x4	224(%rcx),%zmm0
.byte	98,242,117,72,221,200
.byte	98,242,109,72,221,208
	vpxorq	%zmm9,%zmm1,%zmm1
	vpxorq	%zmm10,%zmm2,%zmm2
	vmovdqu8	%zmm1,0(%rsi)
	vmovdqu8	%xmm2,64(%rsi)
	addq	$80,%rsi

	vmovdqa	%xmm2,%xmm8
	vextracti32x4	$0x1,%zmm10,%xmm0
	andq	$0xf,%rdx
	je	.L_ret_hEgxyDlCngwrfFe
	jmp	.L_steal_cipher_hEgxyDlCngwrfFe
.L_num_blocks_is_4_hEgxyDlCngwrfFe:
	vpshufb	%zmm8,%zmm0,%zmm1
	vpsllvq	const_dq3210(%rip),%zmm0,%zmm4
	vpsrlvq	const_dq5678(%rip),%zmm1,%zmm2
.byte	98,147,109,72,68,217,0
	vpxorq	%zmm2,%zmm4,%zmm4{%k2}
	vpxord	%zmm4,%zmm3,%zmm9
	vpsllvq	const_dq7654(%rip),%zmm0,%zmm5
	vpsrlvq	const_dq1234(%rip),%zmm1,%zmm6
.byte	98,147,77,72,68,249,0
	vpxorq	%zmm6,%zmm5,%zmm5{%k2}
	vpxord	%zmm5,%zmm7,%zmm10
	vmovdqu8	0(%rdi),%zmm1
	addq	$64,%rdi
	vbroadcasti32x4	(%rcx),%zmm0
	vpternlogq	$0x96,%zmm0,%zmm9,%zmm1
	vbroadcasti32x4	16(%rcx),%zmm0
.byte	98,242,117,72,220,200
	vbroadcasti32x4	32(%rcx),%zmm0
.byte	98,242,117,72,220,200
	vbroadcasti32x4	48(%rcx),%zmm0
.byte	98,242,117,72,220,200
	vbroadcasti32x4	64(%rcx),%zmm0
.byte	98,242,117,72,220,200
	vbroadcasti32x4	80(%rcx),%zmm0
.byte	98,242,117,72,220,200
	vbroadcasti32x4	96(%rcx),%zmm0
.byte	98,242,117,72,220,200
	vbroadcasti32x4	112(%rcx),%zmm0
.byte	98,242,117,72,220,200
	vbroadcasti32x4	128(%rcx),%zmm0
.byte	98,242,117,72,220,200
	vbroadcasti32x4	144(%rcx),%zmm0
.byte	98,242,117,72,220,200
	vbroadcasti32x4	160(%rcx),%zmm0
.byte	98,242,117,72,220,200
	vbroadcasti32x4	176(%rcx),%zmm0
.byte	98,242,117,72,220,200
	vbroadcasti32x4	192(%rcx),%zmm0
.byte	98,242,117,72,220,200
	vbroadcasti32x4	208(%rcx),%zmm0
.byte	98,242,117,72,220,200
	vbroadcasti32x4	224(%rcx),%zmm0
.byte	98,242,117,72,221,200
	vpxorq	%zmm9,%zmm1,%zmm1
	vmovdqu8	%zmm1,0(%rsi)
	addq	$64,%rsi
	vextracti32x4	$0x3,%zmm1,%xmm8
	vmovdqa	%xmm10,%xmm0
	andq	$0xf,%rdx
	je	.L_ret_hEgxyDlCngwrfFe
	jmp	.L_steal_cipher_hEgxyDlCngwrfFe
.L_num_blocks_is_3_hEgxyDlCngwrfFe:
	vpshufb	%zmm8,%zmm0,%zmm1
	vpsllvq	const_dq3210(%rip),%zmm0,%zmm4
	vpsrlvq	const_dq5678(%rip),%zmm1,%zmm2
.byte	98,147,109,72,68,217,0
	vpxorq	%zmm2,%zmm4,%zmm4{%k2}
	vpxord	%zmm4,%zmm3,%zmm9
	movq	$0x0000ffffffffffff,%r8
	kmovq	%r8,%k1
	vmovdqu8	0(%rdi),%zmm1{%k1}
	addq	$48,%rdi
	vbroadcasti32x4	(%rcx),%zmm0
	vpternlogq	$0x96,%zmm0,%zmm9,%zmm1
	vbroadcasti32x4	16(%rcx),%zmm0
.byte	98,242,117,72,220,200
	vbroadcasti32x4	32(%rcx),%zmm0
.byte	98,242,117,72,220,200
	vbroadcasti32x4	48(%rcx),%zmm0
.byte	98,242,117,72,220,200
	vbroadcasti32x4	64(%rcx),%zmm0
.byte	98,242,117,72,220,200
	vbroadcasti32x4	80(%rcx),%zmm0
.byte	98,242,117,72,220,200
	vbroadcasti32x4	96(%rcx),%zmm0
.byte	98,242,117,72,220,200
	vbroadcasti32x4	112(%rcx),%zmm0
.byte	98,242,117,72,220,200
	vbroadcasti32x4	128(%rcx),%zmm0
.byte	98,242,117,72,220,200
	vbroadcasti32x4	144(%rcx),%zmm0
.byte	98,242,117,72,220,200
	vbroadcasti32x4	160(%rcx),%zmm0
.byte	98,242,117,72,220,200
	vbroadcasti32x4	176(%rcx),%zmm0
.byte	98,242,117,72,220,200
	vbroadcasti32x4	192(%rcx),%zmm0
.byte	98,242,117,72,220,200
	vbroadcasti32x4	208(%rcx),%zmm0
.byte	98,242,117,72,220,200
	vbroadcasti32x4	224(%rcx),%zmm0
.byte	98,242,117,72,221,200
	vpxorq	%zmm9,%zmm1,%zmm1
	vmovdqu8	%zmm1,0(%rsi){%k1}
	addq	$48,%rsi
	vextracti32x4	$2,%zmm1,%xmm8
	vextracti32x4	$3,%zmm9,%xmm0
	andq	$0xf,%rdx
	je	.L_ret_hEgxyDlCngwrfFe
	jmp	.L_steal_cipher_hEgxyDlCngwrfFe
.L_num_blocks_is_2_hEgxyDlCngwrfFe:
	vpshufb	%zmm8,%zmm0,%zmm1
	vpsllvq	const_dq3210(%rip),%zmm0,%zmm4
	vpsrlvq	const_dq5678(%rip),%zmm1,%zmm2
.byte	98,147,109,72,68,217,0
	vpxorq	%zmm2,%zmm4,%zmm4{%k2}
	vpxord	%zmm4,%zmm3,%zmm9

	vmovdqu8	0(%rdi),%ymm1
	addq	$32,%rdi
	vbroadcasti32x4	(%rcx),%ymm0
	vpternlogq	$0x96,%ymm0,%ymm9,%ymm1
	vbroadcasti32x4	16(%rcx),%ymm0
.byte	98,242,117,40,220,200
	vbroadcasti32x4	32(%rcx),%ymm0
.byte	98,242,117,40,220,200
	vbroadcasti32x4	48(%rcx),%ymm0
.byte	98,242,117,40,220,200
	vbroadcasti32x4	64(%rcx),%ymm0
.byte	98,242,117,40,220,200
	vbroadcasti32x4	80(%rcx),%ymm0
.byte	98,242,117,40,220,200
	vbroadcasti32x4	96(%rcx),%ymm0
.byte	98,242,117,40,220,200
	vbroadcasti32x4	112(%rcx),%ymm0
.byte	98,242,117,40,220,200
	vbroadcasti32x4	128(%rcx),%ymm0
.byte	98,242,117,40,220,200
	vbroadcasti32x4	144(%rcx),%ymm0
.byte	98,242,117,40,220,200
	vbroadcasti32x4	160(%rcx),%ymm0
.byte	98,242,117,40,220,200
	vbroadcasti32x4	176(%rcx),%ymm0
.byte	98,242,117,40,220,200
	vbroadcasti32x4	192(%rcx),%ymm0
.byte	98,242,117,40,220,200
	vbroadcasti32x4	208(%rcx),%ymm0
.byte	98,242,117,40,220,200
	vbroadcasti32x4	224(%rcx),%ymm0
.byte	98,242,117,40,221,200
	vpxorq	%ymm9,%ymm1,%ymm1
	vmovdqu8	%ymm1,0(%rsi)
	addq	$32,%rsi

	vextracti32x4	$1,%ymm1,%xmm8
	vextracti32x4	$2,%zmm9,%xmm0
	andq	$0xf,%rdx
	je	.L_ret_hEgxyDlCngwrfFe
	jmp	.L_steal_cipher_hEgxyDlCngwrfFe
.L_num_blocks_is_1_hEgxyDlCngwrfFe:
	vpshufb	%zmm8,%zmm0,%zmm1
	vpsllvq	const_dq3210(%rip),%zmm0,%zmm4
	vpsrlvq	const_dq5678(%rip),%zmm1,%zmm2
.byte	98,147,109,72,68,217,0
	vpxorq	%zmm2,%zmm4,%zmm4{%k2}
	vpxord	%zmm4,%zmm3,%zmm9

	vmovdqu8	0(%rdi),%xmm1
	addq	$16,%rdi
	vbroadcasti32x4	(%rcx),%ymm0
	vpternlogq	$0x96,%ymm0,%ymm9,%ymm1
	vbroadcasti32x4	16(%rcx),%ymm0
.byte	98,242,117,40,220,200
	vbroadcasti32x4	32(%rcx),%ymm0
.byte	98,242,117,40,220,200
	vbroadcasti32x4	48(%rcx),%ymm0
.byte	98,242,117,40,220,200
	vbroadcasti32x4	64(%rcx),%ymm0
.byte	98,242,117,40,220,200
	vbroadcasti32x4	80(%rcx),%ymm0
.byte	98,242,117,40,220,200
	vbroadcasti32x4	96(%rcx),%ymm0
.byte	98,242,117,40,220,200
	vbroadcasti32x4	112(%rcx),%ymm0
.byte	98,242,117,40,220,200
	vbroadcasti32x4	128(%rcx),%ymm0
.byte	98,242,117,40,220,200
	vbroadcasti32x4	144(%rcx),%ymm0
.byte	98,242,117,40,220,200
	vbroadcasti32x4	160(%rcx),%ymm0
.byte	98,242,117,40,220,200
	vbroadcasti32x4	176(%rcx),%ymm0
.byte	98,242,117,40,220,200
	vbroadcasti32x4	192(%rcx),%ymm0
.byte	98,242,117,40,220,200
	vbroadcasti32x4	208(%rcx),%ymm0
.byte	98,242,117,40,220,200
	vbroadcasti32x4	224(%rcx),%ymm0
.byte	98,242,117,40,221,200
	vpxorq	%ymm9,%ymm1,%ymm1
	vmovdqu8	%xmm1,0(%rsi)
	addq	$16,%rsi

	vmovdqa	%xmm1,%xmm8
	vextracti32x4	$1,%zmm9,%xmm0
	andq	$0xf,%rdx
	je	.L_ret_hEgxyDlCngwrfFe
	jmp	.L_steal_cipher_hEgxyDlCngwrfFe
.cfi_endproc	
.globl	aes_hw_xts_decrypt_avx512
.hidden aes_hw_xts_decrypt_avx512
.hidden	aes_hw_xts_decrypt_avx512
.type	aes_hw_xts_decrypt_avx512,@function
.align	32
aes_hw_xts_decrypt_avx512:
.cfi_startproc	
.byte	243,15,30,250
	pushq	%rbp
	movq	%rsp,%rbp
	subq	$136,%rsp
	andq	$0xffffffffffffffc0,%rsp
	movq	%rbx,128(%rsp)
	movq	$0x87,%r10
	vmovdqu	(%r9),%xmm1
	vpxor	(%r8),%xmm1,%xmm1
	vaesenc	16(%r8),%xmm1,%xmm1
	vaesenc	32(%r8),%xmm1,%xmm1
	vaesenc	48(%r8),%xmm1,%xmm1
	vaesenc	64(%r8),%xmm1,%xmm1
	vaesenc	80(%r8),%xmm1,%xmm1
	vaesenc	96(%r8),%xmm1,%xmm1
	vaesenc	112(%r8),%xmm1,%xmm1
	vaesenc	128(%r8),%xmm1,%xmm1
	vaesenc	144(%r8),%xmm1,%xmm1
	vaesenc	160(%r8),%xmm1,%xmm1
	vaesenc	176(%r8),%xmm1,%xmm1
	vaesenc	192(%r8),%xmm1,%xmm1
	vaesenc	208(%r8),%xmm1,%xmm1
	vaesenclast	224(%r8),%xmm1,%xmm1
	vmovdqa	%xmm1,(%rsp)


	cmpq	$0x20,%rdx
	jl	.L_final_block_is_only_block_amivrujEyduiFoi




	movq	%rdx,%r11
	andq	$0xfffffffffffffff0,%r11
	subq	$16,%r11
	cmpq	$0x80,%r11
	jl	.L_less_than_128_bytes_amivrujEyduiFoi
	vpbroadcastq	%r10,%zmm25
	cmpq	$0x100,%r11
	jge	.L_start_by16_amivrujEyduiFoi
	cmpq	$0x80,%r11
	jge	.L_start_by8_amivrujEyduiFoi

.L_do_n_blocks_amivrujEyduiFoi:
	cmpq	$0x70,%r11
	je	.L_remaining_num_blocks_is_7_amivrujEyduiFoi
	cmpq	$0x60,%r11
	je	.L_remaining_num_blocks_is_6_amivrujEyduiFoi
	cmpq	$0x50,%r11
	je	.L_remaining_num_blocks_is_5_amivrujEyduiFoi
	cmpq	$0x40,%r11
	je	.L_remaining_num_blocks_is_4_amivrujEyduiFoi
	cmpq	$0x30,%r11
	je	.L_remaining_num_blocks_is_3_amivrujEyduiFoi
	cmpq	$0x20,%r11
	je	.L_remaining_num_blocks_is_2_amivrujEyduiFoi
	cmpq	$0x10,%r11
	je	.L_remaining_num_blocks_is_1_amivrujEyduiFoi
	andq	$0xf,%rdx
	je	.L_final_block_amivrujEyduiFoi
	vextracti32x4	$0x0,%zmm9,%xmm0
	vextracti32x4	$0x1,%zmm9,%xmm15
	jmp	.L_steal_cipher_amivrujEyduiFoi

.L_remaining_num_blocks_is_7_amivrujEyduiFoi:
	movq	$0x0000ffffffffffff,%r8
	kmovq	%r8,%k1
	vmovdqu8	(%rdi),%zmm1
	vmovdqu8	64(%rdi),%zmm2{%k1}
	addq	$0x70,%rdi
	vbroadcasti32x4	(%rcx),%zmm0
	vpternlogq	$0x96,%zmm0,%zmm9,%zmm1
	vpternlogq	$0x96,%zmm0,%zmm10,%zmm2
	vbroadcasti32x4	16(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	32(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	48(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208

	vbroadcasti32x4	64(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	80(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	96(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	112(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	128(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	144(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	160(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	176(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	192(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	208(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	224(%rcx),%zmm0
.byte	98,242,117,72,223,200
.byte	98,242,109,72,223,208
	vpxorq	%zmm9,%zmm1,%zmm1
	vpxorq	%zmm10,%zmm2,%zmm2
	vmovdqu8	%zmm1,(%rsi)
	vmovdqu8	%zmm2,64(%rsi){%k1}
	addq	$0x70,%rsi
	vextracti32x4	$0x3,%zmm10,%xmm0
	andq	$0xf,%rdx
	je	.L_final_block_amivrujEyduiFoi
	vpsrldq	$0xf,%zmm9,%zmm13
.byte	98,19,21,72,68,241,0
	vpslldq	$0x1,%zmm9,%zmm11
	vpxord	%zmm14,%zmm11,%zmm11
	vextracti32x4	$0x0,%zmm11,%xmm15
	jmp	.L_steal_cipher_amivrujEyduiFoi

.L_remaining_num_blocks_is_6_amivrujEyduiFoi:
	vmovdqu8	(%rdi),%zmm1
	vmovdqu8	64(%rdi),%ymm2
	addq	$0x60,%rdi
	vbroadcasti32x4	(%rcx),%zmm0
	vpternlogq	$0x96,%zmm0,%zmm9,%zmm1
	vpternlogq	$0x96,%zmm0,%zmm10,%zmm2
	vbroadcasti32x4	16(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	32(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	48(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208

	vbroadcasti32x4	64(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	80(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	96(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	112(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	128(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	144(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	160(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	176(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	192(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	208(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	224(%rcx),%zmm0
.byte	98,242,117,72,223,200
.byte	98,242,109,72,223,208
	vpxorq	%zmm9,%zmm1,%zmm1
	vpxorq	%zmm10,%zmm2,%zmm2
	vmovdqu8	%zmm1,(%rsi)
	vmovdqu8	%ymm2,64(%rsi)
	addq	$0x60,%rsi
	vextracti32x4	$0x2,%zmm10,%xmm0
	vextracti32x4	$0x3,%zmm10,%xmm15
	andq	$0xf,%rdx
	je	.L_final_block_amivrujEyduiFoi
	jmp	.L_steal_cipher_amivrujEyduiFoi

.L_remaining_num_blocks_is_5_amivrujEyduiFoi:
	vmovdqu8	(%rdi),%zmm1
	vmovdqu	64(%rdi),%xmm2
	addq	$0x50,%rdi
	vbroadcasti32x4	(%rcx),%zmm0
	vpternlogq	$0x96,%zmm0,%zmm9,%zmm1
	vpternlogq	$0x96,%zmm0,%zmm10,%zmm2
	vbroadcasti32x4	16(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	32(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	48(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208

	vbroadcasti32x4	64(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	80(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	96(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	112(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	128(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	144(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	160(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	176(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	192(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	208(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	224(%rcx),%zmm0
.byte	98,242,117,72,223,200
.byte	98,242,109,72,223,208
	vpxorq	%zmm9,%zmm1,%zmm1
	vpxorq	%zmm10,%zmm2,%zmm2
	vmovdqu8	%zmm1,(%rsi)
	vmovdqu	%xmm2,64(%rsi)
	addq	$0x50,%rsi
	vextracti32x4	$0x1,%zmm10,%xmm0
	vextracti32x4	$0x2,%zmm10,%xmm15
	andq	$0xf,%rdx
	je	.L_final_block_amivrujEyduiFoi
	jmp	.L_steal_cipher_amivrujEyduiFoi

.L_remaining_num_blocks_is_4_amivrujEyduiFoi:
	vmovdqu8	(%rdi),%zmm1
	addq	$0x40,%rdi
	vbroadcasti32x4	(%rcx),%zmm0
	vpternlogq	$0x96,%zmm0,%zmm9,%zmm1
	vbroadcasti32x4	16(%rcx),%zmm0
.byte	98,242,117,72,222,200
	vbroadcasti32x4	32(%rcx),%zmm0
.byte	98,242,117,72,222,200
	vbroadcasti32x4	48(%rcx),%zmm0
.byte	98,242,117,72,222,200
	vbroadcasti32x4	64(%rcx),%zmm0
.byte	98,242,117,72,222,200
	vbroadcasti32x4	80(%rcx),%zmm0
.byte	98,242,117,72,222,200
	vbroadcasti32x4	96(%rcx),%zmm0
.byte	98,242,117,72,222,200
	vbroadcasti32x4	112(%rcx),%zmm0
.byte	98,242,117,72,222,200
	vbroadcasti32x4	128(%rcx),%zmm0
.byte	98,242,117,72,222,200
	vbroadcasti32x4	144(%rcx),%zmm0
.byte	98,242,117,72,222,200
	vbroadcasti32x4	160(%rcx),%zmm0
.byte	98,242,117,72,222,200
	vbroadcasti32x4	176(%rcx),%zmm0
.byte	98,242,117,72,222,200
	vbroadcasti32x4	192(%rcx),%zmm0
.byte	98,242,117,72,222,200
	vbroadcasti32x4	208(%rcx),%zmm0
.byte	98,242,117,72,222,200
	vbroadcasti32x4	224(%rcx),%zmm0
.byte	98,242,117,72,223,200
	vpxorq	%zmm9,%zmm1,%zmm1
	vmovdqu8	%zmm1,(%rsi)
	addq	$0x40,%rsi
	vextracti32x4	$0x0,%zmm10,%xmm0
	vextracti32x4	$0x1,%zmm10,%xmm15
	andq	$0xf,%rdx
	je	.L_final_block_amivrujEyduiFoi
	jmp	.L_steal_cipher_amivrujEyduiFoi
.L_remaining_num_blocks_is_3_amivrujEyduiFoi:
	movq	$-1,%r8
	shrq	$0x10,%r8
	kmovq	%r8,%k1
	vmovdqu8	(%rdi),%zmm1{%k1}
	addq	$0x30,%rdi
	vbroadcasti32x4	(%rcx),%zmm0
	vpternlogq	$0x96,%zmm0,%zmm9,%zmm1
	vbroadcasti32x4	16(%rcx),%zmm0
.byte	98,242,117,72,222,200
	vbroadcasti32x4	32(%rcx),%zmm0
.byte	98,242,117,72,222,200
	vbroadcasti32x4	48(%rcx),%zmm0
.byte	98,242,117,72,222,200
	vbroadcasti32x4	64(%rcx),%zmm0
.byte	98,242,117,72,222,200
	vbroadcasti32x4	80(%rcx),%zmm0
.byte	98,242,117,72,222,200
	vbroadcasti32x4	96(%rcx),%zmm0
.byte	98,242,117,72,222,200
	vbroadcasti32x4	112(%rcx),%zmm0
.byte	98,242,117,72,222,200
	vbroadcasti32x4	128(%rcx),%zmm0
.byte	98,242,117,72,222,200
	vbroadcasti32x4	144(%rcx),%zmm0
.byte	98,242,117,72,222,200
	vbroadcasti32x4	160(%rcx),%zmm0
.byte	98,242,117,72,222,200
	vbroadcasti32x4	176(%rcx),%zmm0
.byte	98,242,117,72,222,200
	vbroadcasti32x4	192(%rcx),%zmm0
.byte	98,242,117,72,222,200
	vbroadcasti32x4	208(%rcx),%zmm0
.byte	98,242,117,72,222,200
	vbroadcasti32x4	224(%rcx),%zmm0
.byte	98,242,117,72,223,200
	vpxorq	%zmm9,%zmm1,%zmm1
	vmovdqu8	%zmm1,(%rsi){%k1}
	addq	$0x30,%rsi
	vextracti32x4	$0x3,%zmm9,%xmm0
	vextracti32x4	$0x0,%zmm10,%xmm15
	andq	$0xf,%rdx
	je	.L_final_block_amivrujEyduiFoi
	jmp	.L_steal_cipher_amivrujEyduiFoi
.L_remaining_num_blocks_is_2_amivrujEyduiFoi:
	vmovdqu8	(%rdi),%ymm1
	addq	$0x20,%rdi
	vbroadcasti32x4	(%rcx),%ymm0
	vpternlogq	$0x96,%ymm0,%ymm9,%ymm1
	vbroadcasti32x4	16(%rcx),%ymm0
.byte	98,242,117,40,222,200
	vbroadcasti32x4	32(%rcx),%ymm0
.byte	98,242,117,40,222,200
	vbroadcasti32x4	48(%rcx),%ymm0
.byte	98,242,117,40,222,200
	vbroadcasti32x4	64(%rcx),%ymm0
.byte	98,242,117,40,222,200
	vbroadcasti32x4	80(%rcx),%ymm0
.byte	98,242,117,40,222,200
	vbroadcasti32x4	96(%rcx),%ymm0
.byte	98,242,117,40,222,200
	vbroadcasti32x4	112(%rcx),%ymm0
.byte	98,242,117,40,222,200
	vbroadcasti32x4	128(%rcx),%ymm0
.byte	98,242,117,40,222,200
	vbroadcasti32x4	144(%rcx),%ymm0
.byte	98,242,117,40,222,200
	vbroadcasti32x4	160(%rcx),%ymm0
.byte	98,242,117,40,222,200
	vbroadcasti32x4	176(%rcx),%ymm0
.byte	98,242,117,40,222,200
	vbroadcasti32x4	192(%rcx),%ymm0
.byte	98,242,117,40,222,200
	vbroadcasti32x4	208(%rcx),%ymm0
.byte	98,242,117,40,222,200
	vbroadcasti32x4	224(%rcx),%ymm0
.byte	98,242,117,40,223,200
	vpxorq	%ymm9,%ymm1,%ymm1
	vmovdqu	%ymm1,(%rsi)
	addq	$0x20,%rsi
	vextracti32x4	$0x2,%zmm9,%xmm0
	vextracti32x4	$0x3,%zmm9,%xmm15
	andq	$0xf,%rdx
	je	.L_final_block_amivrujEyduiFoi
	jmp	.L_steal_cipher_amivrujEyduiFoi
.L_remaining_num_blocks_is_1_amivrujEyduiFoi:
	vmovdqu	(%rdi),%xmm1
	addq	$0x10,%rdi
	vpxor	%xmm9,%xmm1,%xmm1
	vpxor	(%rcx),%xmm1,%xmm1
	vaesdec	16(%rcx),%xmm1,%xmm1
	vaesdec	32(%rcx),%xmm1,%xmm1
	vaesdec	48(%rcx),%xmm1,%xmm1
	vaesdec	64(%rcx),%xmm1,%xmm1
	vaesdec	80(%rcx),%xmm1,%xmm1
	vaesdec	96(%rcx),%xmm1,%xmm1
	vaesdec	112(%rcx),%xmm1,%xmm1
	vaesdec	128(%rcx),%xmm1,%xmm1
	vaesdec	144(%rcx),%xmm1,%xmm1
	vaesdec	160(%rcx),%xmm1,%xmm1
	vaesdec	176(%rcx),%xmm1,%xmm1
	vaesdec	192(%rcx),%xmm1,%xmm1
	vaesdec	208(%rcx),%xmm1,%xmm1
	vaesdeclast	224(%rcx),%xmm1,%xmm1
	vpxor	%xmm9,%xmm1,%xmm1
	vmovdqu	%xmm1,(%rsi)
	addq	$0x10,%rsi
	vextracti32x4	$0x1,%zmm9,%xmm0
	vextracti32x4	$0x2,%zmm9,%xmm15
	andq	$0xf,%rdx
	je	.L_final_block_amivrujEyduiFoi
	jmp	.L_steal_cipher_amivrujEyduiFoi


.L_start_by16_amivrujEyduiFoi:
	vbroadcasti32x4	(%rsp),%zmm0
	vbroadcasti32x4	shufb_15_7(%rip),%zmm8
	movq	$0xaa,%r8
	kmovq	%r8,%k2
	vpshufb	%zmm8,%zmm0,%zmm1


	vpsllvq	const_dq3210(%rip),%zmm0,%zmm4
	vpsrlvq	const_dq5678(%rip),%zmm1,%zmm2
.byte	98,147,109,72,68,217,0
	vpxorq	%zmm2,%zmm4,%zmm4{%k2}
	vpxord	%zmm4,%zmm3,%zmm9


	vpsllvq	const_dq7654(%rip),%zmm0,%zmm5
	vpsrlvq	const_dq1234(%rip),%zmm1,%zmm6
.byte	98,147,77,72,68,249,0
	vpxorq	%zmm6,%zmm5,%zmm5{%k2}
	vpxord	%zmm5,%zmm7,%zmm10


	vpsrldq	$0xf,%zmm9,%zmm13
.byte	98,19,21,72,68,241,0
	vpslldq	$0x1,%zmm9,%zmm11
	vpxord	%zmm14,%zmm11,%zmm11


	vpsrldq	$0xf,%zmm10,%zmm15
.byte	98,131,5,72,68,193,0
	vpslldq	$0x1,%zmm10,%zmm12
	vpxord	%zmm16,%zmm12,%zmm12

.L_main_loop_run_16_amivrujEyduiFoi:
	vmovdqu8	(%rdi),%zmm1
	vmovdqu8	64(%rdi),%zmm2
	vmovdqu8	128(%rdi),%zmm3
	vmovdqu8	192(%rdi),%zmm4
	addq	$0x100,%rdi
	vpxorq	%zmm9,%zmm1,%zmm1
	vpxorq	%zmm10,%zmm2,%zmm2
	vpxorq	%zmm11,%zmm3,%zmm3
	vpxorq	%zmm12,%zmm4,%zmm4
	vbroadcasti32x4	(%rcx),%zmm0
	vpxorq	%zmm0,%zmm1,%zmm1
	vpxorq	%zmm0,%zmm2,%zmm2
	vpxorq	%zmm0,%zmm3,%zmm3
	vpxorq	%zmm0,%zmm4,%zmm4
	vpsrldq	$0xf,%zmm11,%zmm13
.byte	98,19,21,72,68,241,0
	vpslldq	$0x1,%zmm11,%zmm15
	vpxord	%zmm14,%zmm15,%zmm15
	vbroadcasti32x4	16(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208
.byte	98,242,101,72,222,216
.byte	98,242,93,72,222,224
	vbroadcasti32x4	32(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208
.byte	98,242,101,72,222,216
.byte	98,242,93,72,222,224
	vbroadcasti32x4	48(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208
.byte	98,242,101,72,222,216
.byte	98,242,93,72,222,224
	vpsrldq	$0xf,%zmm12,%zmm13
.byte	98,19,21,72,68,241,0
	vpslldq	$0x1,%zmm12,%zmm16
	vpxord	%zmm14,%zmm16,%zmm16
	vbroadcasti32x4	64(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208
.byte	98,242,101,72,222,216
.byte	98,242,93,72,222,224
	vbroadcasti32x4	80(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208
.byte	98,242,101,72,222,216
.byte	98,242,93,72,222,224
	vbroadcasti32x4	96(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208
.byte	98,242,101,72,222,216
.byte	98,242,93,72,222,224
	vpsrldq	$0xf,%zmm15,%zmm13
.byte	98,19,21,72,68,241,0
	vpslldq	$0x1,%zmm15,%zmm17
	vpxord	%zmm14,%zmm17,%zmm17
	vbroadcasti32x4	112(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208
.byte	98,242,101,72,222,216
.byte	98,242,93,72,222,224
	vbroadcasti32x4	128(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208
.byte	98,242,101,72,222,216
.byte	98,242,93,72,222,224
	vbroadcasti32x4	144(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208
.byte	98,242,101,72,222,216
.byte	98,242,93,72,222,224
	vpsrldq	$0xf,%zmm16,%zmm13
.byte	98,19,21,72,68,241,0
	vpslldq	$0x1,%zmm16,%zmm18
	vpxord	%zmm14,%zmm18,%zmm18
	vbroadcasti32x4	160(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208
.byte	98,242,101,72,222,216
.byte	98,242,93,72,222,224
	vbroadcasti32x4	176(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208
.byte	98,242,101,72,222,216
.byte	98,242,93,72,222,224
	vbroadcasti32x4	192(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208
.byte	98,242,101,72,222,216
.byte	98,242,93,72,222,224
	vbroadcasti32x4	208(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208
.byte	98,242,101,72,222,216
.byte	98,242,93,72,222,224
	vbroadcasti32x4	224(%rcx),%zmm0
.byte	98,242,117,72,223,200
.byte	98,242,109,72,223,208
.byte	98,242,101,72,223,216
.byte	98,242,93,72,223,224
	vpxorq	%zmm9,%zmm1,%zmm1
	vpxorq	%zmm10,%zmm2,%zmm2
	vpxorq	%zmm11,%zmm3,%zmm3
	vpxorq	%zmm12,%zmm4,%zmm4

	vmovdqa32	%zmm15,%zmm9
	vmovdqa32	%zmm16,%zmm10
	vmovdqa32	%zmm17,%zmm11
	vmovdqa32	%zmm18,%zmm12
	vmovdqu8	%zmm1,(%rsi)
	vmovdqu8	%zmm2,64(%rsi)
	vmovdqu8	%zmm3,128(%rsi)
	vmovdqu8	%zmm4,192(%rsi)
	addq	$0x100,%rsi
	subq	$0x100,%r11
	cmpq	$0x100,%r11
	jae	.L_main_loop_run_16_amivrujEyduiFoi
	cmpq	$0x80,%r11
	jae	.L_main_loop_run_8_amivrujEyduiFoi
	jmp	.L_do_n_blocks_amivrujEyduiFoi

.L_start_by8_amivrujEyduiFoi:
	vbroadcasti32x4	(%rsp),%zmm0
	vbroadcasti32x4	shufb_15_7(%rip),%zmm8
	movq	$0xaa,%r8
	kmovq	%r8,%k2
	vpshufb	%zmm8,%zmm0,%zmm1
	vpsllvq	const_dq3210(%rip),%zmm0,%zmm4
	vpsrlvq	const_dq5678(%rip),%zmm1,%zmm2
.byte	98,147,109,72,68,217,0
	vpxorq	%zmm2,%zmm4,%zmm4{%k2}
	vpxord	%zmm4,%zmm3,%zmm9
	vpsllvq	const_dq7654(%rip),%zmm0,%zmm5
	vpsrlvq	const_dq1234(%rip),%zmm1,%zmm6
.byte	98,147,77,72,68,249,0
	vpxorq	%zmm6,%zmm5,%zmm5{%k2}
	vpxord	%zmm5,%zmm7,%zmm10

.L_main_loop_run_8_amivrujEyduiFoi:
	vmovdqu8	(%rdi),%zmm1
	vmovdqu8	64(%rdi),%zmm2
	addq	$0x80,%rdi
	vbroadcasti32x4	(%rcx),%zmm0
	vpternlogq	$0x96,%zmm0,%zmm9,%zmm1
	vpternlogq	$0x96,%zmm0,%zmm10,%zmm2
	vpsrldq	$0xf,%zmm9,%zmm13
.byte	98,19,21,72,68,241,0
	vpslldq	$0x1,%zmm9,%zmm15
	vpxord	%zmm14,%zmm15,%zmm15
	vbroadcasti32x4	16(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	32(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	48(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208
	vpsrldq	$0xf,%zmm10,%zmm13
.byte	98,19,21,72,68,241,0
	vpslldq	$0x1,%zmm10,%zmm16
	vpxord	%zmm14,%zmm16,%zmm16

	vbroadcasti32x4	64(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	80(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	96(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	112(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	128(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	144(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	160(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	176(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	192(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	208(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	224(%rcx),%zmm0
.byte	98,242,117,72,223,200
.byte	98,242,109,72,223,208
	vpxorq	%zmm9,%zmm1,%zmm1
	vpxorq	%zmm10,%zmm2,%zmm2
	vmovdqa32	%zmm15,%zmm9
	vmovdqa32	%zmm16,%zmm10
	vmovdqu8	%zmm1,(%rsi)
	vmovdqu8	%zmm2,64(%rsi)
	addq	$0x80,%rsi
	subq	$0x80,%r11
	cmpq	$0x80,%r11
	jae	.L_main_loop_run_8_amivrujEyduiFoi
	vextracti32x4	$0x0,%zmm9,%xmm0
	vextracti32x4	$0x1,%zmm9,%xmm15
	jmp	.L_do_n_blocks_amivrujEyduiFoi

.L_steal_cipher_with_tweak_amivrujEyduiFoi:

	vmovdqa	shufb_15_7(%rip),%xmm11
	vpshufb	%xmm11,%xmm0,%xmm12
	vpsllq	$0x1,%xmm0,%xmm13
	vpsrlq	$0x7,%xmm12,%xmm14
.byte	98,19,13,8,68,249,0
	vpxord	%xmm13,%xmm15,%xmm15

.L_steal_cipher_amivrujEyduiFoi:

	vmovdqu	(%rdi),%xmm8
	vpxor	%xmm15,%xmm8,%xmm8
	vpxor	(%rcx),%xmm8,%xmm8
	vaesdec	16(%rcx),%xmm8,%xmm8
	vaesdec	32(%rcx),%xmm8,%xmm8
	vaesdec	48(%rcx),%xmm8,%xmm8
	vaesdec	64(%rcx),%xmm8,%xmm8
	vaesdec	80(%rcx),%xmm8,%xmm8
	vaesdec	96(%rcx),%xmm8,%xmm8
	vaesdec	112(%rcx),%xmm8,%xmm8
	vaesdec	128(%rcx),%xmm8,%xmm8
	vaesdec	144(%rcx),%xmm8,%xmm8
	vaesdec	160(%rcx),%xmm8,%xmm8
	vaesdec	176(%rcx),%xmm8,%xmm8
	vaesdec	192(%rcx),%xmm8,%xmm8
	vaesdec	208(%rcx),%xmm8,%xmm8
	vaesdeclast	224(%rcx),%xmm8,%xmm8
	vpxor	%xmm15,%xmm8,%xmm8




	movq	$1,%r11
	movq	%rcx,%r8
	movq	%rdx,%rcx
	shlq	%cl,%r11
	subq	$1,%r11
	kmovq	%r11,%k1
	vmovdqu8	16(%rdi),%xmm9{%k1}{z}
	vmovdqu8	%xmm8,%xmm10{%k1}{z}
	vpblendmb	%xmm9,%xmm8,%xmm9{%k1}


	movq	%r8,%rcx
	vpxor	%xmm0,%xmm9,%xmm9
	vpxor	(%rcx),%xmm9,%xmm9
	vaesdec	16(%rcx),%xmm9,%xmm9
	vaesdec	32(%rcx),%xmm9,%xmm9
	vaesdec	48(%rcx),%xmm9,%xmm9
	vaesdec	64(%rcx),%xmm9,%xmm9
	vaesdec	80(%rcx),%xmm9,%xmm9
	vaesdec	96(%rcx),%xmm9,%xmm9
	vaesdec	112(%rcx),%xmm9,%xmm9
	vaesdec	128(%rcx),%xmm9,%xmm9
	vaesdec	144(%rcx),%xmm9,%xmm9
	vaesdec	160(%rcx),%xmm9,%xmm9
	vaesdec	176(%rcx),%xmm9,%xmm9
	vaesdec	192(%rcx),%xmm9,%xmm9
	vaesdec	208(%rcx),%xmm9,%xmm9
	vaesdeclast	224(%rcx),%xmm9,%xmm9
	vpxor	%xmm0,%xmm9,%xmm9



	vmovdqu	%xmm9,(%rsi)
	vmovdqu8	%xmm10,16(%rsi){%k1}
	jmp	.L_ret_amivrujEyduiFoi

.L_final_block_is_only_block_amivrujEyduiFoi:
	vmovdqa	(%rsp),%xmm0
	andq	$0xf,%rdx
	jne	.L_steal_cipher_with_tweak_amivrujEyduiFoi

.L_final_block_amivrujEyduiFoi:
	vmovdqa	(%rdi),%xmm8
	vpxor	%xmm0,%xmm8,%xmm8
	vpxor	(%rcx),%xmm8,%xmm8
	vaesdec	16(%rcx),%xmm8,%xmm8
	vaesdec	32(%rcx),%xmm8,%xmm8
	vaesdec	48(%rcx),%xmm8,%xmm8
	vaesdec	64(%rcx),%xmm8,%xmm8
	vaesdec	80(%rcx),%xmm8,%xmm8
	vaesdec	96(%rcx),%xmm8,%xmm8
	vaesdec	112(%rcx),%xmm8,%xmm8
	vaesdec	128(%rcx),%xmm8,%xmm8
	vaesdec	144(%rcx),%xmm8,%xmm8
	vaesdec	160(%rcx),%xmm8,%xmm8
	vaesdec	176(%rcx),%xmm8,%xmm8
	vaesdec	192(%rcx),%xmm8,%xmm8
	vaesdec	208(%rcx),%xmm8,%xmm8
	vaesdeclast	224(%rcx),%xmm8,%xmm8
	vpxor	%xmm0,%xmm8,%xmm8
	vmovdqa	%xmm8,(%rsi)

.L_ret_amivrujEyduiFoi:
	movq	128(%rsp),%rbx
	xorq	%r8,%r8
	movq	%r8,128(%rsp)
	vpxorq	%zmm0,%zmm0,%zmm0
	movq	%rbp,%rsp
	popq	%rbp
	vzeroupper
	.byte	0xf3,0xc3

.L_less_than_128_bytes_amivrujEyduiFoi:
	vpbroadcastq	%r10,%zmm25
	cmpq	$0x10,%r11
	jb	.L_ret_amivrujEyduiFoi
	vbroadcasti32x4	(%rsp),%zmm0
	vbroadcasti32x4	shufb_15_7(%rip),%zmm8
	movl	$0xaa,%r8d
	kmovq	%r8,%k2
	movq	%r11,%r8
	andq	$0x70,%r8
	cmpq	$0x60,%r8
	je	.L_num_blocks_is_6_amivrujEyduiFoi
	cmpq	$0x50,%r8
	je	.L_num_blocks_is_5_amivrujEyduiFoi
	cmpq	$0x40,%r8
	je	.L_num_blocks_is_4_amivrujEyduiFoi
	cmpq	$0x30,%r8
	je	.L_num_blocks_is_3_amivrujEyduiFoi
	cmpq	$0x20,%r8
	je	.L_num_blocks_is_2_amivrujEyduiFoi
	cmpq	$0x10,%r8
	je	.L_num_blocks_is_1_amivrujEyduiFoi

.L_num_blocks_is_7_amivrujEyduiFoi:
	vpshufb	%zmm8,%zmm0,%zmm1
	vpsllvq	const_dq3210(%rip),%zmm0,%zmm4
	vpsrlvq	const_dq5678(%rip),%zmm1,%zmm2
.byte	98,147,109,72,68,217,0
	vpxorq	%zmm2,%zmm4,%zmm4{%k2}
	vpxord	%zmm4,%zmm3,%zmm9
	vpsllvq	const_dq7654(%rip),%zmm0,%zmm5
	vpsrlvq	const_dq1234(%rip),%zmm1,%zmm6
.byte	98,147,77,72,68,249,0
	vpxorq	%zmm6,%zmm5,%zmm5{%k2}
	vpxord	%zmm5,%zmm7,%zmm10
	movq	$0x0000ffffffffffff,%r8
	kmovq	%r8,%k1
	vmovdqu8	0(%rdi),%zmm1
	vmovdqu8	64(%rdi),%zmm2{%k1}

	addq	$0x70,%rdi
	vbroadcasti32x4	(%rcx),%zmm0
	vpternlogq	$0x96,%zmm0,%zmm9,%zmm1
	vpternlogq	$0x96,%zmm0,%zmm10,%zmm2
	vbroadcasti32x4	16(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	32(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	48(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208

	vbroadcasti32x4	64(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	80(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	96(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	112(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	128(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	144(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	160(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	176(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	192(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	208(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	224(%rcx),%zmm0
.byte	98,242,117,72,223,200
.byte	98,242,109,72,223,208
	vpxorq	%zmm9,%zmm1,%zmm1
	vpxorq	%zmm10,%zmm2,%zmm2
	vmovdqu8	%zmm1,0(%rsi)
	vmovdqu8	%zmm2,64(%rsi){%k1}
	addq	$0x70,%rsi

	vextracti32x4	$0x3,%zmm10,%xmm0

	andq	$0xf,%rdx
	je	.L_final_block_amivrujEyduiFoi

	vpsrldq	$0xf,%zmm9,%zmm13
.byte	98,19,21,72,68,241,0
	vpslldq	$0x1,%zmm9,%zmm11
	vpxord	%zmm14,%zmm11,%zmm11
	vextracti32x4	$0x0,%zmm11,%xmm15
	jmp	.L_steal_cipher_amivrujEyduiFoi
.L_num_blocks_is_6_amivrujEyduiFoi:
	vpshufb	%zmm8,%zmm0,%zmm1
	vpsllvq	const_dq3210(%rip),%zmm0,%zmm4
	vpsrlvq	const_dq5678(%rip),%zmm1,%zmm2
.byte	98,147,109,72,68,217,0
	vpxorq	%zmm2,%zmm4,%zmm4{%k2}
	vpxord	%zmm4,%zmm3,%zmm9
	vpsllvq	const_dq7654(%rip),%zmm0,%zmm5
	vpsrlvq	const_dq1234(%rip),%zmm1,%zmm6
.byte	98,147,77,72,68,249,0
	vpxorq	%zmm6,%zmm5,%zmm5{%k2}
	vpxord	%zmm5,%zmm7,%zmm10
	vmovdqu8	0(%rdi),%zmm1
	vmovdqu8	64(%rdi),%ymm2
	addq	$96,%rdi
	vbroadcasti32x4	(%rcx),%zmm0
	vpternlogq	$0x96,%zmm0,%zmm9,%zmm1
	vpternlogq	$0x96,%zmm0,%zmm10,%zmm2
	vbroadcasti32x4	16(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	32(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	48(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208

	vbroadcasti32x4	64(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	80(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	96(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	112(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	128(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	144(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	160(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	176(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	192(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	208(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	224(%rcx),%zmm0
.byte	98,242,117,72,223,200
.byte	98,242,109,72,223,208
	vpxorq	%zmm9,%zmm1,%zmm1
	vpxorq	%zmm10,%zmm2,%zmm2
	vmovdqu8	%zmm1,0(%rsi)
	vmovdqu8	%ymm2,64(%rsi)
	addq	$96,%rsi

	vextracti32x4	$0x2,%zmm10,%xmm0
	vextracti32x4	$0x3,%zmm10,%xmm15
	andq	$0xf,%rdx
	je	.L_final_block_amivrujEyduiFoi
	jmp	.L_steal_cipher_amivrujEyduiFoi
.L_num_blocks_is_5_amivrujEyduiFoi:
	vpshufb	%zmm8,%zmm0,%zmm1
	vpsllvq	const_dq3210(%rip),%zmm0,%zmm4
	vpsrlvq	const_dq5678(%rip),%zmm1,%zmm2
.byte	98,147,109,72,68,217,0
	vpxorq	%zmm2,%zmm4,%zmm4{%k2}
	vpxord	%zmm4,%zmm3,%zmm9
	vpsllvq	const_dq7654(%rip),%zmm0,%zmm5
	vpsrlvq	const_dq1234(%rip),%zmm1,%zmm6
.byte	98,147,77,72,68,249,0
	vpxorq	%zmm6,%zmm5,%zmm5{%k2}
	vpxord	%zmm5,%zmm7,%zmm10
	vmovdqu8	0(%rdi),%zmm1
	vmovdqu8	64(%rdi),%xmm2
	addq	$80,%rdi
	vbroadcasti32x4	(%rcx),%zmm0
	vpternlogq	$0x96,%zmm0,%zmm9,%zmm1
	vpternlogq	$0x96,%zmm0,%zmm10,%zmm2
	vbroadcasti32x4	16(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	32(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	48(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208

	vbroadcasti32x4	64(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	80(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	96(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	112(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	128(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	144(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	160(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	176(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	192(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	208(%rcx),%zmm0
.byte	98,242,117,72,222,200
.byte	98,242,109,72,222,208


	vbroadcasti32x4	224(%rcx),%zmm0
.byte	98,242,117,72,223,200
.byte	98,242,109,72,223,208
	vpxorq	%zmm9,%zmm1,%zmm1
	vpxorq	%zmm10,%zmm2,%zmm2
	vmovdqu8	%zmm1,0(%rsi)
	vmovdqu8	%xmm2,64(%rsi)
	addq	$80,%rsi

	vmovdqa	%xmm2,%xmm8
	vextracti32x4	$0x1,%zmm10,%xmm0
	vextracti32x4	$0x2,%zmm10,%xmm15
	andq	$0xf,%rdx
	je	.L_final_block_amivrujEyduiFoi
	jmp	.L_steal_cipher_amivrujEyduiFoi
.L_num_blocks_is_4_amivrujEyduiFoi:
	vpshufb	%zmm8,%zmm0,%zmm1
	vpsllvq	const_dq3210(%rip),%zmm0,%zmm4
	vpsrlvq	const_dq5678(%rip),%zmm1,%zmm2
.byte	98,147,109,72,68,217,0
	vpxorq	%zmm2,%zmm4,%zmm4{%k2}
	vpxord	%zmm4,%zmm3,%zmm9
	vpsllvq	const_dq7654(%rip),%zmm0,%zmm5
	vpsrlvq	const_dq1234(%rip),%zmm1,%zmm6
.byte	98,147,77,72,68,249,0
	vpxorq	%zmm6,%zmm5,%zmm5{%k2}
	vpxord	%zmm5,%zmm7,%zmm10
	vmovdqu8	0(%rdi),%zmm1
	addq	$64,%rdi
	vbroadcasti32x4	(%rcx),%zmm0
	vpternlogq	$0x96,%zmm0,%zmm9,%zmm1
	vbroadcasti32x4	16(%rcx),%zmm0
.byte	98,242,117,72,222,200
	vbroadcasti32x4	32(%rcx),%zmm0
.byte	98,242,117,72,222,200
	vbroadcasti32x4	48(%rcx),%zmm0
.byte	98,242,117,72,222,200
	vbroadcasti32x4	64(%rcx),%zmm0
.byte	98,242,117,72,222,200
	vbroadcasti32x4	80(%rcx),%zmm0
.byte	98,242,117,72,222,200
	vbroadcasti32x4	96(%rcx),%zmm0
.byte	98,242,117,72,222,200
	vbroadcasti32x4	112(%rcx),%zmm0
.byte	98,242,117,72,222,200
	vbroadcasti32x4	128(%rcx),%zmm0
.byte	98,242,117,72,222,200
	vbroadcasti32x4	144(%rcx),%zmm0
.byte	98,242,117,72,222,200
	vbroadcasti32x4	160(%rcx),%zmm0
.byte	98,242,117,72,222,200
	vbroadcasti32x4	176(%rcx),%zmm0
.byte	98,242,117,72,222,200
	vbroadcasti32x4	192(%rcx),%zmm0
.byte	98,242,117,72,222,200
	vbroadcasti32x4	208(%rcx),%zmm0
.byte	98,242,117,72,222,200
	vbroadcasti32x4	224(%rcx),%zmm0
.byte	98,242,117,72,223,200
	vpxorq	%zmm9,%zmm1,%zmm1
	vmovdqu8	%zmm1,0(%rsi)
	addq	$64,%rsi
	vmovdqa	%xmm10,%xmm0
	vextracti32x4	$0x1,%zmm10,%xmm15
	andq	$0xf,%rdx
	je	.L_final_block_amivrujEyduiFoi
	jmp	.L_steal_cipher_amivrujEyduiFoi
.L_num_blocks_is_3_amivrujEyduiFoi:
	vpshufb	%zmm8,%zmm0,%zmm1
	vpsllvq	const_dq3210(%rip),%zmm0,%zmm4
	vpsrlvq	const_dq5678(%rip),%zmm1,%zmm2
.byte	98,147,109,72,68,217,0
	vpxorq	%zmm2,%zmm4,%zmm4{%k2}
	vpxord	%zmm4,%zmm3,%zmm9
	vpsllvq	const_dq7654(%rip),%zmm0,%zmm5
	vpsrlvq	const_dq1234(%rip),%zmm1,%zmm6
.byte	98,147,77,72,68,249,0
	vpxorq	%zmm6,%zmm5,%zmm5{%k2}
	vpxord	%zmm5,%zmm7,%zmm10
	movq	$0x0000ffffffffffff,%r8
	kmovq	%r8,%k1
	vmovdqu8	0(%rdi),%zmm1{%k1}
	addq	$48,%rdi
	vbroadcasti32x4	(%rcx),%zmm0
	vpternlogq	$0x96,%zmm0,%zmm9,%zmm1
	vbroadcasti32x4	16(%rcx),%zmm0
.byte	98,242,117,72,222,200
	vbroadcasti32x4	32(%rcx),%zmm0
.byte	98,242,117,72,222,200
	vbroadcasti32x4	48(%rcx),%zmm0
.byte	98,242,117,72,222,200
	vbroadcasti32x4	64(%rcx),%zmm0
.byte	98,242,117,72,222,200
	vbroadcasti32x4	80(%rcx),%zmm0
.byte	98,242,117,72,222,200
	vbroadcasti32x4	96(%rcx),%zmm0
.byte	98,242,117,72,222,200
	vbroadcasti32x4	112(%rcx),%zmm0
.byte	98,242,117,72,222,200
	vbroadcasti32x4	128(%rcx),%zmm0
.byte	98,242,117,72,222,200
	vbroadcasti32x4	144(%rcx),%zmm0
.byte	98,242,117,72,222,200
	vbroadcasti32x4	160(%rcx),%zmm0
.byte	98,242,117,72,222,200
	vbroadcasti32x4	176(%rcx),%zmm0
.byte	98,242,117,72,222,200
	vbroadcasti32x4	192(%rcx),%zmm0
.byte	98,242,117,72,222,200
	vbroadcasti32x4	208(%rcx),%zmm0
.byte	98,242,117,72,222,200
	vbroadcasti32x4	224(%rcx),%zmm0
.byte	98,242,117,72,223,200
	vpxorq	%zmm9,%zmm1,%zmm1
	vmovdqu8	%zmm1,0(%rsi){%k1}
	addq	$48,%rsi
	vextracti32x4	$3,%zmm9,%xmm0
	vextracti32x4	$0,%zmm10,%xmm15
	andq	$0xf,%rdx
	je	.L_final_block_amivrujEyduiFoi
	jmp	.L_steal_cipher_amivrujEyduiFoi
.L_num_blocks_is_2_amivrujEyduiFoi:
	vpshufb	%zmm8,%zmm0,%zmm1
	vpsllvq	const_dq3210(%rip),%zmm0,%zmm4
	vpsrlvq	const_dq5678(%rip),%zmm1,%zmm2
.byte	98,147,109,72,68,217,0
	vpxorq	%zmm2,%zmm4,%zmm4{%k2}
	vpxord	%zmm4,%zmm3,%zmm9

	vmovdqu8	0(%rdi),%ymm1
	addq	$32,%rdi
	vbroadcasti32x4	(%rcx),%ymm0
	vpternlogq	$0x96,%ymm0,%ymm9,%ymm1
	vbroadcasti32x4	16(%rcx),%ymm0
.byte	98,242,117,40,222,200
	vbroadcasti32x4	32(%rcx),%ymm0
.byte	98,242,117,40,222,200
	vbroadcasti32x4	48(%rcx),%ymm0
.byte	98,242,117,40,222,200
	vbroadcasti32x4	64(%rcx),%ymm0
.byte	98,242,117,40,222,200
	vbroadcasti32x4	80(%rcx),%ymm0
.byte	98,242,117,40,222,200
	vbroadcasti32x4	96(%rcx),%ymm0
.byte	98,242,117,40,222,200
	vbroadcasti32x4	112(%rcx),%ymm0
.byte	98,242,117,40,222,200
	vbroadcasti32x4	128(%rcx),%ymm0
.byte	98,242,117,40,222,200
	vbroadcasti32x4	144(%rcx),%ymm0
.byte	98,242,117,40,222,200
	vbroadcasti32x4	160(%rcx),%ymm0
.byte	98,242,117,40,222,200
	vbroadcasti32x4	176(%rcx),%ymm0
.byte	98,242,117,40,222,200
	vbroadcasti32x4	192(%rcx),%ymm0
.byte	98,242,117,40,222,200
	vbroadcasti32x4	208(%rcx),%ymm0
.byte	98,242,117,40,222,200
	vbroadcasti32x4	224(%rcx),%ymm0
.byte	98,242,117,40,223,200
	vpxorq	%ymm9,%ymm1,%ymm1
	vmovdqu8	%ymm1,0(%rsi)
	addq	$32,%rsi

	vextracti32x4	$2,%zmm9,%xmm0
	vextracti32x4	$3,%zmm9,%xmm15
	andq	$0xf,%rdx
	je	.L_final_block_amivrujEyduiFoi
	jmp	.L_steal_cipher_amivrujEyduiFoi
.L_num_blocks_is_1_amivrujEyduiFoi:
	vpshufb	%zmm8,%zmm0,%zmm1
	vpsllvq	const_dq3210(%rip),%zmm0,%zmm4
	vpsrlvq	const_dq5678(%rip),%zmm1,%zmm2
.byte	98,147,109,72,68,217,0
	vpxorq	%zmm2,%zmm4,%zmm4{%k2}
	vpxord	%zmm4,%zmm3,%zmm9

	vmovdqu8	0(%rdi),%xmm1
	addq	$16,%rdi
	vbroadcasti32x4	(%rcx),%ymm0
	vpternlogq	$0x96,%ymm0,%ymm9,%ymm1
	vbroadcasti32x4	16(%rcx),%ymm0
.byte	98,242,117,40,222,200
	vbroadcasti32x4	32(%rcx),%ymm0
.byte	98,242,117,40,222,200
	vbroadcasti32x4	48(%rcx),%ymm0
.byte	98,242,117,40,222,200
	vbroadcasti32x4	64(%rcx),%ymm0
.byte	98,242,117,40,222,200
	vbroadcasti32x4	80(%rcx),%ymm0
.byte	98,242,117,40,222,200
	vbroadcasti32x4	96(%rcx),%ymm0
.byte	98,242,117,40,222,200
	vbroadcasti32x4	112(%rcx),%ymm0
.byte	98,242,117,40,222,200
	vbroadcasti32x4	128(%rcx),%ymm0
.byte	98,242,117,40,222,200
	vbroadcasti32x4	144(%rcx),%ymm0
.byte	98,242,117,40,222,200
	vbroadcasti32x4	160(%rcx),%ymm0
.byte	98,242,117,40,222,200
	vbroadcasti32x4	176(%rcx),%ymm0
.byte	98,242,117,40,222,200
	vbroadcasti32x4	192(%rcx),%ymm0
.byte	98,242,117,40,222,200
	vbroadcasti32x4	208(%rcx),%ymm0
.byte	98,242,117,40,222,200
	vbroadcasti32x4	224(%rcx),%ymm0
.byte	98,242,117,40,223,200
	vpxorq	%ymm9,%ymm1,%ymm1
	vmovdqu8	%xmm1,0(%rsi)
	addq	$16,%rsi

	vmovdqa	%xmm1,%xmm8
	vextracti32x4	$1,%zmm9,%xmm0
	vextracti32x4	$2,%zmm9,%xmm15
	andq	$0xf,%rdx
	je	.L_final_block_amivrujEyduiFoi
	jmp	.L_steal_cipher_amivrujEyduiFoi
.cfi_endproc	
.section	.rodata
.align	16

vpshufb_shf_table:
.quad	0x8786858483828100, 0x8f8e8d8c8b8a8988
.quad	0x0706050403020100, 0x000e0d0c0b0a0908

mask1:
.quad	0x8080808080808080, 0x8080808080808080

const_dq3210:
.quad	0, 0, 1, 1, 2, 2, 3, 3
const_dq5678:
.quad	8, 8, 7, 7, 6, 6, 5, 5
const_dq7654:
.quad	4, 4, 5, 5, 6, 6, 7, 7
const_dq1234:
.quad	4, 4, 3, 3, 2, 2, 1, 1

shufb_15_7:
.byte	15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 7, 0xff, 0xff
.byte	0xff, 0xff, 0xff, 0xff, 0xff

.text	
#endif
#endif
