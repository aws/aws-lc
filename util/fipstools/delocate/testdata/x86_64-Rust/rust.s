	.file	"bcm_rust.cgu.0"
	.section	.text.bcm_rust_func,"ax",@progbits
	.globl	bcm_rust_func
	.prefalign	4, .Lfunc_end0, nop
	.type	bcm_rust_func,@function
bcm_rust_func:
.Lfunc_begin0:
	.file	1 "/rustc/0000" "library/core/src/ptr/mod.rs"
	.loc	1 10 5 prologue_end
	.cfi_startproc
	pushq	%rax
	.cfi_def_cfa_offset 16
	callq	bcm_rust_counter_bss_get@PLT
	movq	%rax, %rdi
	movl	$64, %edx
	callq	*memcpy@GOTPCREL(%rip)
	popq	%rax
	.cfi_def_cfa_offset 8
	jmpq	*c_func@GOTPCREL(%rip)
.Lfunc_end0:
	.size	bcm_rust_func, .Lfunc_end0-bcm_rust_func
	.cfi_endproc

	.type	bcm_rust_counter,@object
	.section	.bss.bcm_rust_counter,"aw",@nobits
	.globl	bcm_rust_counter
	.p2align	2, 0x0
bcm_rust_counter:
	.zero	4
	.size	bcm_rust_counter, 4

	.section	.debug_abbrev,"",@progbits
	.byte	1
	.byte	17
	.section	.debug_info,"",@progbits
.Lcu_begin0:
	.long	.Ldebug_info_end0-.Ldebug_info_start0
.Ldebug_info_start0:
	.quad	.Lfunc_begin0
	.quad	.Lsec_end0
.Ldebug_info_end0:
	.section	.bss.bcm_rust_counter,"aw",@nobits
.Lsec_end0:
	.section	".note.GNU-stack","",@progbits
