; This file is generated from a similarly-named Perl script in the BoringSSL
; source tree. Do not edit by hand.

%ifidn __OUTPUT_FORMAT__, win64
default	rel
%define XMMWORD
%define YMMWORD
%define ZMMWORD

%ifdef BORINGSSL_PREFIX
%include "boringssl_prefix_symbols_nasm.inc"
%endif
section	.text code align=64





global	CRYPTO_rdrand

ALIGN	16
CRYPTO_rdrand:

	xor	rax,rax
DB	73,15,199,240
	test	r8,r8
	jz	NEAR $L$err
	cmp	r8,-1
	je	NEAR $L$err

	adc	rax,rax
	mov	QWORD[rcx],r8
	DB	0F3h,0C3h		;repret
$L$err:
	xor	rax,rax
	DB	0F3h,0C3h		;repret







global	CRYPTO_rdrand_multiple8_buf

ALIGN	16
CRYPTO_rdrand_multiple8_buf:

	test	rdx,rdx
	jz	NEAR $L$out
	mov	r8,8
$L$loop:
DB	73,15,199,241
	jnc	NEAR $L$err_multiple
	test	r9,r9
	jz	NEAR $L$err_multiple
	cmp	r9,-1
	je	NEAR $L$err_multiple
	mov	QWORD[rcx],r9
	add	rcx,r8
	sub	rdx,r8
	jnz	NEAR $L$loop
$L$out:
	mov	rax,1
	DB	0F3h,0C3h		;repret
$L$err_multiple:
	xor	rax,rax
	DB	0F3h,0C3h		;repret


%else
; Work around https://bugzilla.nasm.us/show_bug.cgi?id=3392738
ret
%endif
