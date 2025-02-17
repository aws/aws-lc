.text
.file 1 "inserted_by_delocate.c"
.loc 1 1 0
.global BORINGSSL_bcm_text_hash
.type BORINGSSL_bcm_text_hash, @function
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
.global BORINGSSL_bcm_text_start
.type BORINGSSL_bcm_text_start, @function
BORINGSSL_bcm_text_start:
	.type foo, %function
	.globl foo
.Lfoo_local_target:
foo:
	// GOT load
// WAS adrp x1, :got:stderr
	sub sp, sp, 128
	stp x0, x30, [sp, #-16]!
	bl .Lboringssl_loadgot_stderr
	mov x1, x0
	ldp x0, x30, [sp], #16
	add sp, sp, 128
// WAS ldr x0, [x1, :got_lo12:stderr]
	mov x0, x1

	// GOT load to x0
// WAS adrp x0, :got:stderr
	sub sp, sp, 128
	stp x0, x30, [sp, #-16]!
	bl .Lboringssl_loadgot_stderr
	ldp xzr, x30, [sp], #16
	add sp, sp, 128
// WAS ldr x1, [x0, :got_lo12:stderr]
	mov x1, x0

	// GOT load with no register move
// WAS adrp x0, :got:stderr
	sub sp, sp, 128
	stp x0, x30, [sp, #-16]!
	bl .Lboringssl_loadgot_stderr
	ldp xzr, x30, [sp], #16
	add sp, sp, 128
// WAS ldr x0, [x0, :got_lo12:stderr]

	// Address load
// WAS adrp x0, .Llocal_data
	adr x0, .Llocal_data
// WAS add x1, x0, :lo12:.Llocal_data
	add	x1, x0, #0

	// Address of local symbol with offset
// WAS adrp x10, .Llocal_data2+16
	adr x10, .Llocal_data2+16
// WAS add x11, x10, :lo12:.Llocal_data2+16
	add	x11, x10, #0

	// Address load with no-op add instruction
// WAS adrp x0, .Llocal_data
	adr x0, .Llocal_data
// WAS add x0, x0, :lo12:.Llocal_data

	// armcap
// WAS adrp x1, OPENSSL_armcap_P
	sub sp, sp, 128
	stp x0, x30, [sp, #-16]!
	bl .LOPENSSL_armcap_P_addr
	mov x1, x0
	ldp x0, x30, [sp], #16
	add sp, sp, 128
// WAS ldr w2, [x1, :lo12:OPENSSL_armcap_P]
	ldr	w2, [x1]

	// armcap to x30
// WAS adrp x30, OPENSSL_armcap_P
	sub sp, sp, 128
	stp x0, x30, [sp, #-16]!
	bl .LOPENSSL_armcap_P_addr
	mov x30, x0
	ldp x0, xzr, [sp], #16
	add sp, sp, 128
// WAS ldr w2, [x30, :lo12:OPENSSL_armcap_P]
	ldr	w2, [x30]

	// armcap to w0
// WAS adrp x0, OPENSSL_armcap_P
	sub sp, sp, 128
	stp x0, x30, [sp, #-16]!
	bl .LOPENSSL_armcap_P_addr
	ldp xzr, x30, [sp], #16
	add sp, sp, 128
// WAS ldr w1, [x1, :lo12:OPENSSL_armcap_P]
	ldr	w1, [x1]

	// Load from local symbol
// WAS adrp x10, .Llocal_data2
	adr x10, .Llocal_data2
// WAS ldr q0, [x10, :lo12:.Llocal_data2]
	ldr	q0, [x10]

	// Load from local symbol with sign extension
// WAS adrp x10, .Llocal_data2
	adr x10, .Llocal_data2
// WAS ldrsw x0, [x10, :lo12:.Llocal_data2]
	ldrsw	x0, [x10]

// WAS bl local_function
	bl	.Llocal_function_local_target

// WAS bl remote_function
	bl	.Lbcm_redirector_remote_function

	bl bss_symbol_bss_get

	// Regression test for a two-digit index.
	ld1 { v1.b }[10], [x9]

	// Ensure that registers aren't interpreted as symbols.
	add x0, x0
	add x12, x12
	add w0, x0
	add w12, x12
	add d0, d0
	add d12, d12
	add q0, q0
	add q12, q12
	add s0, s0
	add s12, s12
	add h0, h0
	add h12, h12
	add b0, b0
	add b12, b12

	// But 'y' is not a register prefix so far, so these should be
	// processed as symbols.
// WAS add y0, y0
	add	.Lbcm_redirector_y0, .Lbcm_redirector_y0
// WAS add y12, y12
	add	.Lbcm_redirector_y12, .Lbcm_redirector_y12

	// Make sure that the magic extension constants are recognised rather
	// than being interpreted as symbols.
	add w0, w1, b2, uxtb
	add w0, w1, b2, uxth
	add w0, w1, b2, uxtw
	add w0, w1, b2, uxtx
	add w0, w1, b2, sxtb
	add w0, w1, b2, sxth
	add w0, w1, b2, sxtw
	add w0, w1, b2, sxtx

	// Test other shifts
	add x0, x1, x2, lsl #2
	add x0, x1, x2, lsr #2
	ldr x0, [x1, x2, asl #3]
	add x0, x1, x2, asr #2
	add x0, x1, x2, ror #2
	add x0, x1, x2, rol #2

	// Make sure we can parse different immediates
	add x22, sp, #(13*32)
	add x22, sp, #(13*32)+96
	add x22, sp, #(13*32)+96*32

	// Ensure BORINGSSL_bcm_text_[end,start] are loaded through GOT
// WAS adrp x4, :got:BORINGSSL_bcm_text_start
	sub sp, sp, 128
	stp x0, x30, [sp, #-16]!
	bl .Lboringssl_loadgot_BORINGSSL_bcm_text_start
	mov x4, x0
	ldp x0, x30, [sp], #16
	add sp, sp, 128
// WAS adrp x5, :got:BORINGSSL_bcm_text_end
	sub sp, sp, 128
	stp x0, x30, [sp, #-16]!
	bl .Lboringssl_loadgot_BORINGSSL_bcm_text_end
	mov x5, x0
	ldp x0, x30, [sp], #16
	add sp, sp, 128

	// Aarch64 SVE2 added these forms:
	ld1d { z1.d }, p0/z, [x13, x11, lsl #3]
	ld1b { z11.b }, p15/z, [x10, #1, mul vl]

	// Test msl special argument handling
	movi v0.2d, #0xff, msl #8
	movi v1.2d, #0x42, msl #16
	movi v2.2d, #0x1, msl #0

.Llocal_function_local_target:
local_function:

// BSS data
.type bss_symbol,@object
.section .bss.bss_symbol,"aw",@nobits
bss_symbol:
.Lbss_symbol_local_target:

.word 0
.size bss_symbol, 4
.text
.loc 1 2 0
.global BORINGSSL_bcm_text_end
.type BORINGSSL_bcm_text_end, @function
BORINGSSL_bcm_text_end:
.p2align 2
.hidden .Lbcm_redirector_remote_function
.type .Lbcm_redirector_remote_function, @function
.Lbcm_redirector_remote_function:
.cfi_startproc
	hint #34 // bti c
	b remote_function
.cfi_endproc
.size .Lbcm_redirector_remote_function, .-.Lbcm_redirector_remote_function
.p2align 2
.hidden .Lbcm_redirector_y0
.type .Lbcm_redirector_y0, @function
.Lbcm_redirector_y0:
.cfi_startproc
	hint #34 // bti c
	b y0
.cfi_endproc
.size .Lbcm_redirector_y0, .-.Lbcm_redirector_y0
.p2align 2
.hidden .Lbcm_redirector_y12
.type .Lbcm_redirector_y12, @function
.Lbcm_redirector_y12:
.cfi_startproc
	hint #34 // bti c
	b y12
.cfi_endproc
.size .Lbcm_redirector_y12, .-.Lbcm_redirector_y12
.p2align 2
.hidden bss_symbol_bss_get
.type bss_symbol_bss_get, @function
bss_symbol_bss_get:
.cfi_startproc
	hint #34 // bti c
	adrp x0, .Lbss_symbol_local_target
	add x0, x0, :lo12:.Lbss_symbol_local_target
	ret
.cfi_endproc
.size bss_symbol_bss_get, .-bss_symbol_bss_get
.p2align 2
.hidden .Lboringssl_loadgot_BORINGSSL_bcm_text_end
.type .Lboringssl_loadgot_BORINGSSL_bcm_text_end, @function
.Lboringssl_loadgot_BORINGSSL_bcm_text_end:
.cfi_startproc
	hint #34 // bti c
	adrp x0, :got:BORINGSSL_bcm_text_end
	ldr x0, [x0, :got_lo12:BORINGSSL_bcm_text_end]
	ret
.cfi_endproc
.size .Lboringssl_loadgot_BORINGSSL_bcm_text_end, .-.Lboringssl_loadgot_BORINGSSL_bcm_text_end
.p2align 2
.hidden .Lboringssl_loadgot_BORINGSSL_bcm_text_start
.type .Lboringssl_loadgot_BORINGSSL_bcm_text_start, @function
.Lboringssl_loadgot_BORINGSSL_bcm_text_start:
.cfi_startproc
	hint #34 // bti c
	adrp x0, :got:BORINGSSL_bcm_text_start
	ldr x0, [x0, :got_lo12:BORINGSSL_bcm_text_start]
	ret
.cfi_endproc
.size .Lboringssl_loadgot_BORINGSSL_bcm_text_start, .-.Lboringssl_loadgot_BORINGSSL_bcm_text_start
.p2align 2
.hidden .Lboringssl_loadgot_stderr
.type .Lboringssl_loadgot_stderr, @function
.Lboringssl_loadgot_stderr:
.cfi_startproc
	hint #34 // bti c
	adrp x0, :got:stderr
	ldr x0, [x0, :got_lo12:stderr]
	ret
.cfi_endproc
.size .Lboringssl_loadgot_stderr, .-.Lboringssl_loadgot_stderr
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
