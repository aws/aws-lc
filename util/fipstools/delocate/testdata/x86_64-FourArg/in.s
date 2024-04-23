	.type foo, @function
	.globl foo
foo:
	movq  %rbx, %rbx # instruction allowing delocator to detect architecture
	vpinsrq $0x08, kBoringSSLRSASqrtTwo@GOTPCREL(%rip), %xmm1, %xmm0
	vpinsrq $1, fooExternal@GOTPCREL(%rip), %xmm14, %xmm15

	.type kBoringSSLRSASqrtTwo,@object # @kBoringSSLRSASqrtTwo
	.section  .rodata,"a",@progbits,unique,760
	.globl  kBoringSSLRSASqrtTwo
	.p2align  4
kBoringSSLRSASqrtTwo:
	.quad -2404814165548301886    # 0xdea06241f7aa81c2
