	.text
	.globl foo
foo:
	ret
	.globl foofoo
foofoo:
	ret

	# relro references.
	movq  %rdx, %xmm1
	movl  $419, (%rax)
	movups  %xmm0, 4(%rax)
	movq .L00(%rip), %xmm0
	movl  $2, 20(%rax)
	punpcklqdq  %xmm1, %xmm0
	movups  %xmm0, 24(%rax)
	addq  $8, %rsp

	movq .LC02(%rip), %xmm2

	.section .data.rel.ro.local,"aw"
	.align 8
.L00:
	.quad foo
.LC02:
	.quad foofoo

	# Should be left alone.
	.section  .init_array,"aw"
	.align 8
	.quad oof

	.section .data.rel.ro
	.align 8
.LD100:
	.quad foofoofoo

	# Should be left alone.
	.section .rodata
	.align 16

	.text
	movq .LD100(%rip), %xmm1

	.globl foofoofoo
foofoofoo:
	ret
