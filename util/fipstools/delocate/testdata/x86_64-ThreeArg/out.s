.text
.file 1 "inserted_by_delocate.c"
.loc 1 1 0
BORINGSSL_bcm_text_start:
	.type foo, @function
	.globl foo
.Lfoo_local_target:
foo:
	movq	%rax, %rax
# WAS shrxq	%rbx, kBoringSSLRSASqrtTwo@GOTPCREL(%rip), %rax
	leaq -128(%rsp), %rsp
	pushq %rcx
	leaq	.LkBoringSSLRSASqrtTwo_local_target(%rip), %rcx
	shrxq %rbx, %rcx, %rax
	popq %rcx
	leaq 128(%rsp), %rsp
# WAS shrxq	kBoringSSLRSASqrtTwo@GOTPCREL(%rip), %rbx, %rax
	leaq -128(%rsp), %rsp
	pushq %rcx
	leaq	.LkBoringSSLRSASqrtTwo_local_target(%rip), %rcx
	shrxq %rcx, %rbx, %rax
	popq %rcx
	leaq 128(%rsp), %rsp


	.type	kBoringSSLRSASqrtTwo,@object # @kBoringSSLRSASqrtTwo
# WAS .section	.rodata,"a",@progbits,unique,760
.text
	.globl	kBoringSSLRSASqrtTwo
	.p2align	4
.LkBoringSSLRSASqrtTwo_local_target:
kBoringSSLRSASqrtTwo:
	.quad	-2404814165548301886    # 0xdea06241f7aa81c2
.text
.loc 1 2 0
BORINGSSL_bcm_text_end:
.type OPENSSL_ia32cap_get, @function
.globl OPENSSL_ia32cap_get
.LOPENSSL_ia32cap_get_local_target:
OPENSSL_ia32cap_get:
	leaq OPENSSL_ia32cap_P(%rip), %rax
	ret
