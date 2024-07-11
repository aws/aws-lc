#!/usr/bin/env perl

# Copyright (c) 2015, Google Inc.
#
# Permission to use, copy, modify, and/or distribute this software for any
# purpose with or without fee is hereby granted, provided that the above
# copyright notice and this permission notice appear in all copies.
#
# THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
# WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
# MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
# SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
# WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION
# OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN
# CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE. */

use strict;

# The first two arguments should always be the flavour and output file path.
if ($#ARGV < 1) { die "Not enough arguments provided.
  Two arguments are necessary: the flavour and the output file path."; }

my $flavour = shift;
my $output  = shift;

my $win64 = 0;
$win64 = 1 if ($flavour =~ /[nm]asm|mingw64/ || $output =~ /\.asm$/);

$0 =~ m/(.*[\/\\])[^\/\\]+$/;
my $dir = $1;
my $xlate;
( $xlate="${dir}../../../perlasm/x86_64-xlate.pl" and -f $xlate) or
die "can't locate x86_64-xlate.pl";

open OUT,"| \"$^X\" \"$xlate\" $flavour \"$output\"";
*STDOUT=*OUT;

my ($out, $len, $tmp1, $tmp2) = $win64 ? ("%rcx", "%rdx", "%r8", "%r9")
                                       : ("%rdi", "%rsi", "%rdx", "%rcx");

print<<___;
.text

# CRYPTO_rdrand writes eight bytes of random data from the hardware RNG to
# |out|. It returns one on success or zero on hardware failure.
# int CRYPTO_rdrand(uint8_t out[8]);
.globl	CRYPTO_rdrand
.type	CRYPTO_rdrand,\@abi-omnipotent
.align	16
CRYPTO_rdrand:
.cfi_startproc
	xorq %rax, %rax
	rdrand $tmp1
	test $tmp1, $tmp1 # OLD cpu's: can use all 0s in output as error signal
	jz .Lerr
	cmp \$-1, $tmp1 # AMD bug: check if all returned bits by RDRAND is stuck on 1
	je .Lerr
	# An add-with-carry of zero effectively sets %rax to the carry flag.
	adcq %rax, %rax
	movq $tmp1, 0($out)
	retq
.Lerr:
	xorq %rax, %rax
	retq
.cfi_endproc
.size CRYPTO_rdrand,.-CRYPTO_rdrand

# CRYPTO_rdrand_multiple8_buf fills |len| bytes at |buf| with random data from
# the hardware RNG. The |len| argument must be a multiple of eight. It returns
# one on success and zero on hardware failure.
# int CRYPTO_rdrand_multiple8_buf(uint8_t *buf, size_t len);
.globl CRYPTO_rdrand_multiple8_buf
.type CRYPTO_rdrand_multiple8_buf,\@abi-omnipotent
.align 16
CRYPTO_rdrand_multiple8_buf:
.cfi_startproc
	test $len, $len
	jz .Lout
	movq \$8, $tmp1
.Lloop:
	rdrand $tmp2
	jnc .Lerr_multiple
	test $tmp2, $tmp2 # OLD cpu's: can use all 0s in output as error signal
	jz .Lerr_multiple
	cmp \$-1, $tmp2 # AMD bug: check if all returned bits by RDRAND is stuck on 1
	je .Lerr_multiple
	movq $tmp2, 0($out)
	addq $tmp1, $out
	subq $tmp1, $len
	jnz .Lloop
.Lout:
	movq \$1, %rax
	retq
.Lerr_multiple:
	xorq %rax, %rax
	retq
.cfi_endproc
.size CRYPTO_rdrand_multiple8_buf,.-CRYPTO_rdrand_multiple8_buf
___

close STDOUT or die "error closing STDOUT: $!";	# flush
