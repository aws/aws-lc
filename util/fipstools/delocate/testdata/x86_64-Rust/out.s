.text
.file 2 "inserted_by_delocate.c"
.loc 2 1 0
.type BORINGSSL_bcm_text_hash, @object
.size BORINGSSL_bcm_text_hash, 32
BORINGSSL_bcm_text_hash:
.byte 0xae
.byte 0x2c
.byte 0xea
.byte 0x2a
.byte 0xbd
.byte 0xa6
.byte 0xf3
.byte 0xec
.byte 0x97
.byte 0x7f
.byte 0x9b
.byte 0xf6
.byte 0x94
.byte 0x9a
.byte 0xfc
.byte 0x83
.byte 0x68
.byte 0x27
.byte 0xcb
.byte 0xa0
.byte 0xa0
.byte 0x9f
.byte 0x6b
.byte 0x6f
.byte 0xde
.byte 0x52
.byte 0xcd
.byte 0xe2
.byte 0xcd
.byte 0xff
.byte 0x31
.byte 0x80
BORINGSSL_bcm_text_start:
	.text
	.file 1 "bcm.c"
	.globl c_func
	.type c_func, @function
.Lc_func_local_target:
c_func:
	.loc 1 2 0
# WAS call bcm_rust_func@PLT
	call	.Lbcm_rust_func_local_target
	ret
	.file	"bcm_rust.cgu.0"
# WAS .section	.text.bcm_rust_func,"ax",@progbits
.text
# WAS .prefalign	4, .Lfunc_end0, nop
	.p2align 4
	.type	bcm_rust_func,@function
.Lbcm_rust_func_local_target:
bcm_rust_func:
.Lfunc_begin0_BCM_1:

	.cfi_startproc
	pushq	%rax
	.cfi_def_cfa_offset 16
# WAS callq	bcm_rust_counter_bss_get@PLT
	callq	bcm_rust_counter_bss_get
	movq	%rax, %rdi
	movl	$64, %edx
# WAS callq	*memcpy@GOTPCREL(%rip)
	callq	.Lbcm_redirector_memcpy
	popq	%rax
	.cfi_def_cfa_offset 8
# WAS jmpq	*c_func@GOTPCREL(%rip)
	jmp	.Lc_func_local_target
.Lfunc_end0_BCM_1:

# WAS .size	bcm_rust_func, .Lfunc_end0-bcm_rust_func
	.size	bcm_rust_func, .Lfunc_end0_BCM_1-bcm_rust_func
	.cfi_endproc

	.type	bcm_rust_counter,@object
	.section	.bss.bcm_rust_counter,"aw",@nobits
	.p2align	2, 0x0
bcm_rust_counter:
.Lbcm_rust_counter_local_target:

	.zero	4
	.size	bcm_rust_counter, 4

	.section	.bss.bcm_rust_counter,"aw",@nobits
.Lsec_end0_BCM_1:
	.section	".note.GNU-stack","",@progbits
.text
.loc 2 2 0
BORINGSSL_bcm_text_end:
.type .Lbcm_redirector_memcpy, @function
.Lbcm_redirector_memcpy:
	jmp	memcpy@PLT
.type bcm_rust_counter_bss_get, @function
bcm_rust_counter_bss_get:
	leaq	.Lbcm_rust_counter_local_target(%rip), %rax
	ret
.type OPENSSL_ia32cap_get, @function
.globl OPENSSL_ia32cap_get
.LOPENSSL_ia32cap_get_local_target:
OPENSSL_ia32cap_get:
	leaq OPENSSL_ia32cap_P(%rip), %rax
	ret
