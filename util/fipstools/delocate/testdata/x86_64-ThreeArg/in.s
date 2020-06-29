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

	.type foo, @function
	.globl foo
foo:
	movq	%rax, %rax
	shrxq	%rbx, kBoringSSLRSASqrtTwo@GOTPCREL(%rip), %rax
	shrxq	kBoringSSLRSASqrtTwo@GOTPCREL(%rip), %rbx, %rax


	.type	kBoringSSLRSASqrtTwo,@object # @kBoringSSLRSASqrtTwo
	.section	.rodata,"a",@progbits,unique,760
	.globl	kBoringSSLRSASqrtTwo
	.p2align	4
kBoringSSLRSASqrtTwo:
	.quad	-2404814165548301886    # 0xdea06241f7aa81c2
