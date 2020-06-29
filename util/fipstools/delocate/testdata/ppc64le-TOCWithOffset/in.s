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
foo:
	# TOC references may have offsets.
	addis 3, 2, 5+foo@toc@ha
	addi 3, 3, 10+foo@toc@l

	addis 3, 2, 15+foo@toc@ha
	addi 3, 3, 20+foo@toc@l

	addis 4, 2, foo@toc@ha
	addi 4, 4, foo@toc@l

	addis 5, 2, 5+foo@toc@ha
	ld 5, 10+foo@toc@l(5)

	addis 4, 2, foo-10@toc@ha
	addi 4, 4, foo-10@toc@l

	addis 4, 2, foo@toc@ha+25
	addi 4, 4, foo@toc@l+25

	addis 4, 2, 1+foo-2@toc@ha+3
	addi 4, 4, 1+foo-2@toc@l+3
