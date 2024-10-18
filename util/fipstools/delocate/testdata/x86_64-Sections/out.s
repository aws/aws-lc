.text
.file 1 "inserted_by_delocate.c"
.loc 1 1 0
BORINGSSL_bcm_text_start:
	# .text stays in .text
	.text
	movq %rax, %rax

	# -ffunction-sections is undone.
# WAS .section .text.foo,"ax",@progbits
.text
	.globl foo
.Lfoo_local_target:
foo:
	ret

	# .rodata is moved to .text.
# WAS .section .rodata
.text
	.long 42
	.string "Hello world, esc\ape characters are \"fun\"\\"

	# Compilers sometimes emit extra rodata sections.
# WAS .section .rodata.str1.1,"aMS",@progbits,1
.text
	.string "NIST P-256"
	.text

	# A number of sections are left alone.
	.section	.init_array,"aw"
	.align 8
	.quad	foo
# WAS .section	.rodata
.text
	.align 16
	.section	.debug_info,"",@progbits
.Ldebug_info0:

	.long	0x1b35e
	.value	0x4
	.long	.L1
	.byte	0x8
	.uleb128 0x1
	.long	.L2
	.byte	0x1
	.long	.L3
.text
.loc 1 2 0
BORINGSSL_bcm_text_end:
.type OPENSSL_ia32cap_get, @function
.globl OPENSSL_ia32cap_get
.LOPENSSL_ia32cap_get_local_target:
OPENSSL_ia32cap_get:
	leaq OPENSSL_ia32cap_P(%rip), %rax
	ret
