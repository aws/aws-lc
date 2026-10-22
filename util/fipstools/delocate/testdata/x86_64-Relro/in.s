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
	movq .LC03(%rip), %xmm3
	movq .LC04(%rip), %xmm4
	movq .LC05(%rip), %xmm5
	movq .LC06(%rip), %xmm6
	movdqa .LC07(%rip), %xmm7

	# GCC 16 may emit relro and .rodata aliases in the same relro section.
	.section .data.rel.ro.local,"aw"
	.align 8
.L00:
	.quad foo
	.set .LC03,.L00
	.set .LC05,.LC03
	.set .LC06,.LD100
	.set	.LC07,.LC34
.LC02:
	.quad foofoo
	.set	.LC04,.LC02

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
.LC34:
	.long 1
	.long 0

	.text
	movq .LD100(%rip), %xmm1

	.globl foofoofoo
foofoofoo:
	ret
