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

	# .text stays in .text
	.text
	movq %rax, %rax

	# -ffunction-sections is undone.
	.section .text.foo,"ax",@progbits
	.globl foo
foo:
	ret

	# .rodata is moved to .text.
	.section .rodata
	.long 42
	.string "Hello world, esc\ape characters are \"fun\"\\"

	# Compilers sometimes emit extra rodata sections.
	.section .rodata.str1.1,"aMS",@progbits,1
	.string "NIST P-256"
	.text

	# A number of sections are left alone.
	.section	.init_array,"aw"
	.align 8
	.quad	foo
	.section	.rodata
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
