#! /usr/bin/env perl

# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

# RNDR from ARMv8.5-A.
# System register encoding: s3_3_c2_c4_0
# see https://developer.arm.com/documentation/ddi0601/2024-09/AArch64-Registers/RNDR--Random-Number

# The first two arguments should always be the flavour and output file path.
if ($#ARGV < 1) { die "Not enough arguments provided.
  Two arguments are necessary: the flavour and the output file path."; }

my $flavour = shift;
my $output  = shift;

$0 =~ m/(.*[\/\\])[^\/\\]+$/; $dir=$1;
( $xlate="${dir}arm-xlate.pl" and -f $xlate ) or
( $xlate="${dir}../../../perlasm/arm-xlate.pl" and -f $xlate) or
die "can't locate arm-xlate.pl";

open OUT,"| \"$^X\" $xlate $flavour $output";
*STDOUT=*OUT;

$code.=<<___;
#include <openssl/arm_arch.h>

.arch armv8-a
.text

# size_t CRYPTO_rndr(uint8_t *out, size_t out_len)
.globl CRYPTO_rndr
.type CRYPTO_rndr,%function
.align 4
CRYPTO_rndr:
  cbz x1, .Lrndr_error        // out_len = 0 is not supported
  mov x4, x1                  // out_len: requested number of bytes
  mov x2, #0                  // Counts number of bytes generated

.Lrndr_loop:
  mrs x3, s3_3_c2_c4_0        // rndr instruction
  cbz x3, .Lrndr_error        // Check if RNDR failed

  cmp x1, #8                  // Sets N if strictly less than 8 bytes left
  blt .Lrndr_less_than_8_bytes

  str x3, [x0], #8            // Copy 8 bytes to *out and increment pointer by 8
  add x2, x2, #8              // Adds 8 to counter
  sub x1, x1, #8
  cbz x1, .Lrndr_done         // If multiple of 8 this will be 0 eventually
  b .Lrndr_loop

.Lrndr_less_than_8_bytes:
  // Copy remaining bytes one by one
  strb  w3, [x0]
  lsr x3, x3, #8
  add x2, x2, #1
  add x0, x0, #1
  sub  x1, x1, #1
  cbnz x1, .Lrndr_less_than_8_bytes

.Lrndr_done:
  cmp x2, x4                  // Ensure correct number of bytes were generated
  bne .Lrndr_error
  mov x0, #1                  // Return value success
  ret

.Lrndr_error:
  mov x0, #0                  // Return value error
  ret
.size CRYPTO_rndr,.-CRYPTO_rndr
___

print $code;
close STDOUT or die "error closing STDOUT: $!"; # enforce flush
