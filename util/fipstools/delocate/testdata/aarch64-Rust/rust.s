	.file	"bcm_rust.cgu.0"
	.section	.text.bcm_rust_func,"ax",@progbits
	.globl	bcm_rust_func
	.p2align	2
	.type	bcm_rust_func,@function
bcm_rust_func:
.Lfunc_begin0:
	.file	1 "/rustc/0000" "library/core/src/ptr/mod.rs"
	.loc	1 10 5 prologue_end
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	adrp	x3, :got:BORINGSSL_bcm_rust_text_start
	adrp	x8, :got:BORINGSSL_bcm_rust_text_end
	ldr	x3, [x3, :got_lo12:BORINGSSL_bcm_rust_text_start]
	ldr	x8, [x8, :got_lo12:BORINGSSL_bcm_rust_text_end]
	adrp	x9, :got:BORINGSSL_bcm_rust_text_hash
	ldr	x9, [x9, :got_lo12:BORINGSSL_bcm_rust_text_hash]
	adrp	x10, :got:OPENSSL_armcap_P
	ldr	x10, [x10, :got_lo12:OPENSSL_armcap_P]
	adrp	x1, .Lanon.0
	add	x1, x1, :lo12:.Lanon.0
	mov	w2, #64
	bl	memcpy
	bl	bcm_rust_counter_bss_get
	bl	bcm_rust_asm_func
	ldp	x29, x30, [sp], #16
	ret
.Lfunc_end0:
	.size	bcm_rust_func, .Lfunc_end0-bcm_rust_func
	.cfi_endproc

	.type	.Lanon.0,@object
	.section	.rodata..Lanon.0,"a",@progbits
.Lanon.0:
	.ascii	"0123456789abcdef"
	.size	.Lanon.0, 16

	.type	bcm_rust_counter,@object
	.section	.bss.bcm_rust_counter,"aw",@nobits
	.globl	bcm_rust_counter
	.p2align	2, 0x0
bcm_rust_counter:
	.zero	4
	.size	bcm_rust_counter, 4

	.section	.init_array,"awR",@init_array,unique,1
	.p2align	3, 0x0
	.xword	bcm_rust_func

	.section	.debug_abbrev,"",@progbits
	.byte	1
	.section	.debug_info,"",@progbits
	.xword	.Lfunc_begin0
	.section	".note.GNU-stack","",@progbits
