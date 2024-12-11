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
	.type foo, @function
	.globl foo
.Lfoo_local_target:
foo:
	movq  %rbx, %rbx # instruction allowing delocator to detect architecture
# WAS vpinsrq $0x08, kBoringSSLRSASqrtTwo@GOTPCREL(%rip), %xmm1, %xmm0
	leaq -128(%rsp), %rsp
	pushq %rax
	leaq	.LkBoringSSLRSASqrtTwo_local_target(%rip), %rax
	vpinsrq $0x08, %rax, %xmm1, %xmm0
	popq %rax
	leaq 128(%rsp), %rsp
# WAS vpinsrq $1, fooExternal@GOTPCREL(%rip), %xmm14, %xmm15
	leaq -128(%rsp), %rsp
	pushq %rax
	pushf
	leaq fooExternal_GOTPCREL_external(%rip), %rax
	addq (%rax), %rax
	movq (%rax), %rax
	popf
	vpinsrq $1, %rax, %xmm14, %xmm15
	popq %rax
	leaq 128(%rsp), %rsp

	.type kBoringSSLRSASqrtTwo,@object # @kBoringSSLRSASqrtTwo
# WAS .section  .rodata,"a",@progbits,unique,760
.text
	.globl  kBoringSSLRSASqrtTwo
	.p2align  4
.LkBoringSSLRSASqrtTwo_local_target:
kBoringSSLRSASqrtTwo:
	.quad -2404814165548301886    # 0xdea06241f7aa81c2
.text
.loc 1 2 0
BORINGSSL_bcm_text_end:
.type fooExternal_GOTPCREL_external, @object
.size fooExternal_GOTPCREL_external, 8
fooExternal_GOTPCREL_external:
	.long fooExternal@GOTPCREL
	.long 0
.type OPENSSL_ia32cap_get, @function
.globl OPENSSL_ia32cap_get
.LOPENSSL_ia32cap_get_local_target:
OPENSSL_ia32cap_get:
	leaq OPENSSL_ia32cap_P(%rip), %rax
	ret
