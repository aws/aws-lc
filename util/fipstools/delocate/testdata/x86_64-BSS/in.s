// Copyright (c) 2017, Google Inc.
//
// Permission to use, copy, modify, and/or distribute this software for any
// purpose with or without fee is hereby granted, provided that the above
// copyright notice and this permission notice appear in all copies.
//
// THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
// WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
// MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
// SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
// WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION
// OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN
// CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.

	.text
	movq %rax, %rax
	
	# BSS declarations emit accessors.
	.comm	aes_128_ctr_generic_storage,64,32
	.lcomm	aes_128_ctr_generic_storage2,64,32
	
	# BSS symbols may also be emitted in .bss sections.
	.section .bss,"awT",@nobits
	.align 4
	.globl x
	.type   x, @object
	.size   x, 4
x:
	.zero 4
.Llocal:
	.quad 0
	.size .Llocal, 4

	# .bss handling is terminated by a .text directive.
	.text
	.section .bss,"awT",@nobits
y:
	.quad 0

	# Or a .section directive.
	.section .rodata
	.quad 0

	# Or the end of the file.
	.section .bss,"awT",@nobits
z:
	.quad 0
