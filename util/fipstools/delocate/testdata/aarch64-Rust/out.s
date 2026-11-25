.text
.global BORINGSSL_bcm_rust_text_hash
.type BORINGSSL_bcm_rust_text_hash, @function
BORINGSSL_bcm_rust_text_hash:
.byte 0xeb
.byte 0xa0
.byte 0xdc
.byte 0x87
.byte 0x3f
.byte 0x90
.byte 0x5a
.byte 0x73
.byte 0xae
.byte 0x32
.byte 0xd8
.byte 0xb2
.byte 0x74
.byte 0xd9
.byte 0x4c
.byte 0x7c
.byte 0x50
.byte 0x48
.byte 0x0
.byte 0xe1
.byte 0xb2
.byte 0xee
.byte 0x1c
.byte 0x96
.byte 0x64
.byte 0x35
.byte 0x99
.byte 0x82
.byte 0xae
.byte 0xfc
.byte 0x2d
.byte 0xd8
.global BORINGSSL_bcm_rust_text_start
.type BORINGSSL_bcm_rust_text_start, @function
BORINGSSL_bcm_rust_text_start:
	.text
	.globl	bcm_rust_asm_func
	.type	bcm_rust_asm_func, %function
.Lbcm_rust_asm_func_local_target:
bcm_rust_asm_func:
// WAS adrp	x2, .LK
	adr x2, .LK
// WAS add	x2, x2, :lo12:.LK
	ldr	x0, [x2]
	ret
// WAS .section	.rodata
.text
	.align	3
.LK:

	.quad	1
	.file	"bcm_rust.cgu.0"
// WAS .section	.text.bcm_rust_func,"ax",@progbits
.text
	.globl	bcm_rust_func
	.p2align	2
	.type	bcm_rust_func,@function
.Lbcm_rust_func_local_target:
bcm_rust_func:
.Lfunc_begin0_BCM_1:

	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
// WAS adrp	x3, :got:BORINGSSL_bcm_rust_text_start
	sub sp, sp, 128
	stp x0, x30, [sp, #-16]!
	bl .Lboringssl_loadgot_BORINGSSL_bcm_rust_text_start
	mov x3, x0
	ldp x0, x30, [sp], #16
	add sp, sp, 128
// WAS adrp	x8, :got:BORINGSSL_bcm_rust_text_end
	sub sp, sp, 128
	stp x0, x30, [sp, #-16]!
	bl .Lboringssl_loadgot_BORINGSSL_bcm_rust_text_end
	mov x8, x0
	ldp x0, x30, [sp], #16
	add sp, sp, 128
// WAS ldr	x3, [x3, :got_lo12:BORINGSSL_bcm_rust_text_start]
// WAS ldr	x8, [x8, :got_lo12:BORINGSSL_bcm_rust_text_end]
// WAS adrp	x9, :got:BORINGSSL_bcm_rust_text_hash
	sub sp, sp, 128
	stp x0, x30, [sp, #-16]!
	bl .Lboringssl_loadgot_BORINGSSL_bcm_rust_text_hash
	mov x9, x0
	ldp x0, x30, [sp], #16
	add sp, sp, 128
// WAS ldr	x9, [x9, :got_lo12:BORINGSSL_bcm_rust_text_hash]
// WAS adrp	x10, :got:OPENSSL_armcap_P
	sub sp, sp, 128
	stp x0, x30, [sp, #-16]!
	bl .LOPENSSL_armcap_P_addr
	mov x10, x0
	ldp x0, x30, [sp], #16
	add sp, sp, 128
// WAS ldr	x10, [x10, :got_lo12:OPENSSL_armcap_P]
// WAS adrp	x1, .Lanon.0
	adr x1, .Lanon.0_BCM_1
// WAS add	x1, x1, :lo12:.Lanon.0
	mov	w2, #64
// WAS bl	memcpy
	bl	.Lbcm_redirector_memcpy
	bl	bcm_rust_counter_bss_get
// WAS bl	bcm_rust_asm_func
	bl	.Lbcm_rust_asm_func_local_target
	ldp	x29, x30, [sp], #16
	ret
.Lfunc_end0_BCM_1:

// WAS .size	bcm_rust_func, .Lfunc_end0-bcm_rust_func
	.size	bcm_rust_func, .Lfunc_end0_BCM_1-bcm_rust_func
	.cfi_endproc

// WAS .type	.Lanon.0,@object
	.type	.Lanon.0_BCM_1, @object
// WAS .section	.rodata..Lanon.0,"a",@progbits
.text
.Lanon.0_BCM_1:

	.ascii	"0123456789abcdef"
// WAS .size	.Lanon.0, 16
	.size	.Lanon.0_BCM_1, 16

	.type	bcm_rust_counter,@object
	.section	.bss.bcm_rust_counter,"aw",@nobits
	.globl	bcm_rust_counter
	.p2align	2, 0x0
bcm_rust_counter:
.Lbcm_rust_counter_local_target:

	.zero	4
	.size	bcm_rust_counter, 4

// WAS .section	.init_array,"awR",@init_array,unique,1
	.section .init_array,"aw",@init_array
	.p2align	3, 0x0
	.xword	bcm_rust_func

	.section	".note.GNU-stack","",@progbits
.text
.global BORINGSSL_bcm_rust_text_end
.type BORINGSSL_bcm_rust_text_end, @function
BORINGSSL_bcm_rust_text_end:
.p2align 2
.hidden .Lbcm_redirector_memcpy
.type .Lbcm_redirector_memcpy, @function
.Lbcm_redirector_memcpy:
.cfi_startproc
	hint #34 // bti c
	b memcpy
.cfi_endproc
.size .Lbcm_redirector_memcpy, .-.Lbcm_redirector_memcpy
.p2align 2
.hidden bcm_rust_counter_bss_get
.type bcm_rust_counter_bss_get, @function
bcm_rust_counter_bss_get:
.cfi_startproc
	hint #34 // bti c
	adrp x0, .Lbcm_rust_counter_local_target
	add x0, x0, :lo12:.Lbcm_rust_counter_local_target
	ret
.cfi_endproc
.size bcm_rust_counter_bss_get, .-bcm_rust_counter_bss_get
.p2align 2
.hidden .Lboringssl_loadgot_BORINGSSL_bcm_rust_text_end
.type .Lboringssl_loadgot_BORINGSSL_bcm_rust_text_end, @function
.Lboringssl_loadgot_BORINGSSL_bcm_rust_text_end:
.cfi_startproc
	hint #34 // bti c
	adrp x0, :got:BORINGSSL_bcm_rust_text_end
	ldr x0, [x0, :got_lo12:BORINGSSL_bcm_rust_text_end]
	ret
.cfi_endproc
.size .Lboringssl_loadgot_BORINGSSL_bcm_rust_text_end, .-.Lboringssl_loadgot_BORINGSSL_bcm_rust_text_end
.p2align 2
.hidden .Lboringssl_loadgot_BORINGSSL_bcm_rust_text_hash
.type .Lboringssl_loadgot_BORINGSSL_bcm_rust_text_hash, @function
.Lboringssl_loadgot_BORINGSSL_bcm_rust_text_hash:
.cfi_startproc
	hint #34 // bti c
	adrp x0, :got:BORINGSSL_bcm_rust_text_hash
	ldr x0, [x0, :got_lo12:BORINGSSL_bcm_rust_text_hash]
	ret
.cfi_endproc
.size .Lboringssl_loadgot_BORINGSSL_bcm_rust_text_hash, .-.Lboringssl_loadgot_BORINGSSL_bcm_rust_text_hash
.p2align 2
.hidden .Lboringssl_loadgot_BORINGSSL_bcm_rust_text_start
.type .Lboringssl_loadgot_BORINGSSL_bcm_rust_text_start, @function
.Lboringssl_loadgot_BORINGSSL_bcm_rust_text_start:
.cfi_startproc
	hint #34 // bti c
	adrp x0, :got:BORINGSSL_bcm_rust_text_start
	ldr x0, [x0, :got_lo12:BORINGSSL_bcm_rust_text_start]
	ret
.cfi_endproc
.size .Lboringssl_loadgot_BORINGSSL_bcm_rust_text_start, .-.Lboringssl_loadgot_BORINGSSL_bcm_rust_text_start
.p2align 2
.hidden .LOPENSSL_armcap_P_addr
.type .LOPENSSL_armcap_P_addr, @function
.LOPENSSL_armcap_P_addr:
.cfi_startproc
	hint #34 // bti c
	adrp x0, OPENSSL_armcap_P
	add x0, x0, :lo12:OPENSSL_armcap_P
	ret
.cfi_endproc
.size .LOPENSSL_armcap_P_addr, .-.LOPENSSL_armcap_P_addr
