	.text
	.globl	bcm_rust_asm_func
	.type	bcm_rust_asm_func, %function
bcm_rust_asm_func:
	adrp	x2, .LK
	add	x2, x2, :lo12:.LK
	ldr	x0, [x2]
	ret
	.section	.rodata
	.align	3
.LK:
	.quad	1
