.text
.file 1 "inserted_by_delocate.c"
.loc 1 1 0
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
	.globl foo
.Lfoo_local_target:
foo:
	ret
	.globl foofoo
.Lfoofoo_local_target:
foofoo:
	ret

	# relro references.
	movq  %rdx, %xmm1
	movl  $419, (%rax)
	movups  %xmm0, 4(%rax)
# WAS movq .L00(%rip), %xmm0
	leaq -128(%rsp), %rsp
	pushq %rax
	leaq	.Lfoo_local_target(%rip), %rax
	movq	%rax, %xmm0
	popq %rax
	leaq 128(%rsp), %rsp
	movl  $2, 20(%rax)
	punpcklqdq  %xmm1, %xmm0
	movups  %xmm0, 24(%rax)
	addq  $8, %rsp

# WAS movq .LC02(%rip), %xmm2
	leaq -128(%rsp), %rsp
	pushq %rax
	leaq	.Lfoofoo_local_target(%rip), %rax
	movq	%rax, %xmm2
	popq %rax
	leaq 128(%rsp), %rsp

# SKIPPED 	.section .data.rel.ro.local,"aw"

# SKIPPED 	.align 8

# SKIPPED .L00:
# SKIPPED newline
# SKIPPED 	.quad foo

# SKIPPED .LC02:
# SKIPPED newline
# SKIPPED 	.quad foofoo

# SKIPPED newline
	# Should be left alone.
	.section  .init_array,"aw"
	.align 8
	.quad oof

# SKIPPED 	.section .data.rel.ro

# SKIPPED 	.align 8

# SKIPPED .LD100:
# SKIPPED newline
# SKIPPED 	.quad foofoofoo

# SKIPPED newline
	# Should be left alone.
# WAS .section .rodata
.text
	.align 16

	.text
# WAS movq .LD100(%rip), %xmm1
	leaq -128(%rsp), %rsp
	pushq %rax
	leaq	.Lfoofoofoo_local_target(%rip), %rax
	movq	%rax, %xmm1
	popq %rax
	leaq 128(%rsp), %rsp

	.globl foofoofoo
.Lfoofoofoo_local_target:
foofoofoo:
	ret
.text
.loc 1 2 0
BORINGSSL_bcm_text_end:
.type OPENSSL_ia32cap_get, @function
.globl OPENSSL_ia32cap_get
.LOPENSSL_ia32cap_get_local_target:
OPENSSL_ia32cap_get:
	leaq OPENSSL_ia32cap_P(%rip), %rax
	ret
