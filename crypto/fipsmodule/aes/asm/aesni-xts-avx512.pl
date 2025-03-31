#! /usr/bin/env perl
# Copyright (C) 2025 Intel Corporation
#
# Licensed under the OpenSSL license (the "License").  You may not use
# this file except in compliance with the License.  You can obtain a copy
# in the file LICENSE in the source distribution or at
# https://www.openssl.org/source/license.html

# This implementation is based on the AES-XTS code (AVX512VAES + VPCLMULQDQ)
# from Intel(R) Intelligent Storage Acceleration Library Crypto Version
# (https://github.com/intel/isa-l_crypto).
#
######################################################################
# The main building block of the loop is code that encrypts/decrypts
# 8/16 blocks of data stitching with generation of tweak for the next
# 8/16 blocks, utilizing VAES and VPCLMULQDQ instructions with full width
# of ZMM registers. The main loop is selected based on the input length.
# main_loop_run_16 encrypts/decrypts 16 blocks in parallel and it's selected
# when input length >= 256 bytes (16 blocks)
# main_loop_run_8 encrypts/decrypts 8 blocks in parallel and it's selected
# when 128 bytes <= input length < 256 bytes (8-15 blocks)
# Input length < 128 bytes (8 blocks) is handled by do_n_blocks.
#
# This implementation mainly uses vpshrdq from AVX-512-VBMI2 family and vaesenc,
# vaesdec, vpclmulqdq from AVX-512F family.

# The first two arguments should always be the flavour and output file path.
if ($#ARGV < 1) { die "Not enough arguments provided.
  Two arguments are necessary: the flavour and the output file path."; }

$flavour = shift;
$output  = shift;

$win64=0; $win64=1 if ($flavour =~ /[nm]asm|mingw64/ || $output =~ /\.asm$/);

$avx512vaes = 1;
for (@ARGV) { $avx512vaes = 0 if (/-DMY_ASSEMBLER_IS_TOO_OLD_FOR_512AVX/); }

$0 =~ m/(.*[\/\\])[^\/\\]+$/; $dir=$1;
( $xlate="${dir}x86_64-xlate.pl" and -f $xlate ) or
( $xlate="${dir}../../../perlasm/x86_64-xlate.pl" and -f $xlate) or
die "can't locate x86_64-xlate.pl";

open OUT,"| \"$^X\" \"$xlate\" $flavour \"$output\"";
*STDOUT=*OUT;

#======================================================================

if ($avx512vaes) {

  my $GP_STORAGE  = $win64 ? (16 * 18)  : (16 * 8);    # store rbx
  my $XMM_STORAGE = $win64 ? (16 * 8) : 0;     # store xmm6:xmm15
  my $VARIABLE_OFFSET = $win64 ? (16*8 + 16*10 + 8*3) :
                                 (16*8 + 8*1);

  # All usages of rsp should be invoked via $TW, not shadowed by any
  # other name or used directly.
  my $TW = "%rsp";
  my $TEMPHIGH = "%rbx";
  my $TEMPLOW = "%rax";
  my $ZPOLY = "%zmm25";

  # ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  # ;;; Function arguments abstraction
  # ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  my ($key2, $key1, $tweak, $length, $input, $output);
  $input    = "%rdi";
  $output   = "%rsi";
  $length   = "%rdx";
  $key1     = "%rcx";
  $key2     = "%r8";
  $tweak    = "%r9";

  # arguments for temp parameters
  my $tmp1       = "%r8";
  my $gf_poly_8b = "%r10";
  my $decLength  = "%r11";

  # ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  # ;;; Helper functions
  # ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  # Generates "random" local labels
  sub random_string() {
    my @chars  = ('a' .. 'z', 'A' .. 'Z', '0' .. '9', '_');
    my $length = 15;
    my $str;
    map { $str .= $chars[rand(33)] } 1 .. $length;
    return $str;
  }

  # ; Seed the RNG so the labels are generated deterministically
  srand(12345);

  sub encrypt_tweak {
    my $state_tweak = $_[0];

    $code.=<<___;
    vpxor	($key2), $state_tweak, $state_tweak
    vaesenc	0x10($key2), $state_tweak, $state_tweak
    vaesenc	0x20($key2), $state_tweak, $state_tweak
    vaesenc	0x30($key2), $state_tweak, $state_tweak
    vaesenc	0x40($key2), $state_tweak, $state_tweak
    vaesenc	0x50($key2), $state_tweak, $state_tweak
    vaesenc	0x60($key2), $state_tweak, $state_tweak
    vaesenc	0x70($key2), $state_tweak, $state_tweak
    vaesenc	0x80($key2), $state_tweak, $state_tweak
    vaesenc	0x90($key2), $state_tweak, $state_tweak
    vaesenc	0xa0($key2), $state_tweak, $state_tweak
    vaesenc	0xb0($key2), $state_tweak, $state_tweak
    vaesenc	0xc0($key2), $state_tweak, $state_tweak
    vaesenc	0xd0($key2), $state_tweak, $state_tweak
    vaesenclast	0xe0($key2), $state_tweak, $state_tweak
    vmovdqa	$state_tweak, ($TW)
___
  }

  sub encrypt_final {
    my $st = $_[0];
    my $tw = $_[1];

    # xor Tweak value
    $code .= "vpxor	$tw, $st, $st\n";
    $code .= "vpxor	($key1), $st, $st\n";

    for (my $i = 1; $i < 14; $i++) {
      $code .= "vaesenc	16*$i($key1), $st, $st\n";
    }

    $code .=<<___;
    vaesenclast 16*14($key1), $st, $st
    vpxor	$tw, $st, $st
___
  }

  sub decrypt_final {
    my $st = $_[0];
    my $tw = $_[1];

    # xor Tweak value
    $code .= "vpxor	$tw, $st, $st\n";
    $code .= "vpxor	($key1), $st, $st\n";

    for (my $i = 1; $i < 14; $i++) {
      $code .= "vaesdec	16*$i($key1), $st, $st\n";
    }

    $code .=<<___;
    vaesdeclast 16*14($key1), $st, $st
    vpxor	$tw, $st, $st
___
  }

  # Encrypt 4 blocks in parallel
  sub encrypt_by_four {
    my $st1 = $_[0]; # state 1
    my $tw1 = $_[1]; # tweak 1
    my $tmp = $_[2];

    $code .= "vbroadcasti32x4 ($key1), $tmp\n";
    $code .= "vpternlogq      \$0x96, $tmp, $tw1, $st1\n";

    for (my $i = 1; $i < 14; $i++) {
      $code .= "vbroadcasti32x4 16*$i($key1), $tmp\n";
      $code .= "vaesenc  $tmp, $st1, $st1\n";
    }

    $code .= "vbroadcasti32x4 16*14($key1), $tmp\n";
    $code .= "vaesenclast  $tmp, $st1, $st1\n";

    $code .= "vpxorq $tw1, $st1, $st1\n";
  }

  sub decrypt_by_four {
    my $st1 = $_[0]; # state 1
    my $tw1 = $_[1]; # tweak 1
    my $tmp = $_[2];

    $code .= "vbroadcasti32x4 ($key1), $tmp\n";
    $code .= "vpternlogq      \$0x96, $tmp, $tw1, $st1\n";

    for (my $i = 1; $i < 14; $i++) {
      $code .= "vbroadcasti32x4 16*$i($key1), $tmp\n";
      $code .= "vaesdec  $tmp, $st1, $st1\n";
    }

    $code .= "vbroadcasti32x4 16*14($key1), $tmp\n";
    $code .= "vaesdeclast  $tmp, $st1, $st1\n";

    $code .= "vpxorq $tw1, $st1, $st1\n";
  }

  # Encrypt 8 blocks in parallel
  # generate next 8 tweak values
  sub encrypt_by_eight {
    my $st1 = $_[0];
    my $st2 = $_[1];
    my $tw1 = $_[2];
    my $tw2 = $_[3];
    my $t0 = $_[4];
    my $last_eight = $_[5];

    $code .= <<___;
	vbroadcasti32x4 ($key1), $t0
	vpternlogq    \$0x96, $t0, $tw1, $st1
	vpternlogq    \$0x96, $t0, $tw2, $st2
___

    if (0 == $last_eight) {
      $code .= <<___;
      vpsrldq		\$0xf, $tw1, %zmm13
      vpclmulqdq	\$0x0, $ZPOLY, %zmm13, %zmm14
      vpslldq		\$0x1, $tw1, %zmm15
      vpxord		%zmm14, %zmm15, %zmm15
___
    }
    # round 1
    $code .= <<___;
    vbroadcasti32x4 0x10($key1), $t0
    vaesenc  $t0, $st1, $st1
    vaesenc  $t0, $st2, $st2

    # round 2
    vbroadcasti32x4 0x20($key1), $t0
    vaesenc  $t0, $st1, $st1
    vaesenc  $t0, $st2, $st2

    # round 3
    vbroadcasti32x4 0x30($key1), $t0
    vaesenc  $t0, $st1, $st1
    vaesenc  $t0, $st2, $st2
___

    if (0 == $last_eight) {
      $code .= <<___;
      vpsrldq		\$0xf, $tw2, %zmm13
      vpclmulqdq	\$0x0, $ZPOLY, %zmm13, %zmm14
      vpslldq		\$0x1, $tw2, %zmm16
      vpxord		%zmm14, %zmm16, %zmm16
___
    }

    $code .= <<___;
    # round 4
    vbroadcasti32x4 0x40($key1), $t0
    vaesenc  $t0, $st1, $st1
    vaesenc  $t0, $st2, $st2

    # round 5
    vbroadcasti32x4 0x50($key1), $t0
    vaesenc  $t0, $st1, $st1
    vaesenc  $t0, $st2, $st2

    # round 6
    vbroadcasti32x4 0x60($key1), $t0
    vaesenc  $t0, $st1, $st1
    vaesenc  $t0, $st2, $st2

    # round 7
    vbroadcasti32x4 0x70($key1), $t0
    vaesenc  $t0, $st1, $st1
    vaesenc  $t0, $st2, $st2

    # round 8
    vbroadcasti32x4 0x80($key1), $t0
    vaesenc  $t0, $st1, $st1
    vaesenc  $t0, $st2, $st2

    # round 9
    vbroadcasti32x4 0x90($key1), $t0
    vaesenc  $t0, $st1, $st1
    vaesenc  $t0, $st2, $st2

    # round 10
    vbroadcasti32x4 0xa0($key1), $t0
    vaesenc  $t0, $st1, $st1
    vaesenc  $t0, $st2, $st2

    # round 11
    vbroadcasti32x4 0xb0($key1), $t0
    vaesenc  $t0, $st1, $st1
    vaesenc  $t0, $st2, $st2

    # round 12
    vbroadcasti32x4 0xc0($key1), $t0
    vaesenc  $t0, $st1, $st1
    vaesenc  $t0, $st2, $st2

    # round 13
    vbroadcasti32x4 0xd0($key1), $t0
    vaesenc  $t0, $st1, $st1
    vaesenc  $t0, $st2, $st2

    # round 14
    vbroadcasti32x4 0xe0($key1), $t0
    vaesenclast $t0, $st1, $st1
    vaesenclast $t0, $st2, $st2
    vpxorq  $tw1, $st1, $st1
    vpxorq  $tw2, $st2, $st2
___
    # xor Tweak values
    if (0 == $last_eight) {
      # load next Tweak values
      $code .= <<___;
      vmovdqa32  %zmm15, $tw1
      vmovdqa32  %zmm16, $tw2
___
    }
  }

  # Decrypt 8 blocks in paralle and generate next 8 tweak values.
  sub decrypt_by_eight {
    my $st1 = $_[0];
    my $st2 = $_[1];
    my $tw1 = $_[2];
    my $tw2 = $_[3];
    my $t0 = $_[4];
    my $last_eight = $_[5];

    $code .= <<___;
	vbroadcasti32x4 ($key1), $t0
	vpternlogq    \$0x96, $t0, $tw1, $st1
	vpternlogq    \$0x96, $t0, $tw2, $st2
___

    if (0 == $last_eight) {
      $code .= <<___;
      vpsrldq		\$0xf, $tw1, %zmm13
      vpclmulqdq	\$0x0, $ZPOLY, %zmm13, %zmm14
      vpslldq		\$0x1, $tw1, %zmm15
      vpxord		%zmm14, %zmm15, %zmm15
___
    }
    # round 1
    $code .= <<___;
    vbroadcasti32x4 0x10($key1), $t0
    vaesdec  $t0, $st1, $st1
    vaesdec  $t0, $st2, $st2

    # round 2
    vbroadcasti32x4 0x20($key1), $t0
    vaesdec  $t0, $st1, $st1
    vaesdec  $t0, $st2, $st2

    # round 3
    vbroadcasti32x4 0x30($key1), $t0
    vaesdec  $t0, $st1, $st1
    vaesdec  $t0, $st2, $st2
___

    if (0 == $last_eight) {
      $code .= <<___;
      vpsrldq		\$0xf, $tw2, %zmm13
      vpclmulqdq	\$0x0, $ZPOLY, %zmm13, %zmm14
      vpslldq		\$0x1, $tw2, %zmm16
      vpxord		%zmm14, %zmm16, %zmm16
___
    }

    $code .= <<___;
    # round 4
    vbroadcasti32x4 0x40($key1), $t0
    vaesdec  $t0, $st1, $st1
    vaesdec  $t0, $st2, $st2

    # round 5
    vbroadcasti32x4 0x50($key1), $t0
    vaesdec  $t0, $st1, $st1
    vaesdec  $t0, $st2, $st2

    # round 6
    vbroadcasti32x4 0x60($key1), $t0
    vaesdec  $t0, $st1, $st1
    vaesdec  $t0, $st2, $st2

    # round 7
    vbroadcasti32x4 0x70($key1), $t0
    vaesdec  $t0, $st1, $st1
    vaesdec  $t0, $st2, $st2

    # round 8
    vbroadcasti32x4 0x80($key1), $t0
    vaesdec  $t0, $st1, $st1
    vaesdec  $t0, $st2, $st2

    # round 9
    vbroadcasti32x4 0x90($key1), $t0
    vaesdec  $t0, $st1, $st1
    vaesdec  $t0, $st2, $st2

    # round 10
    vbroadcasti32x4 0xa0($key1), $t0
    vaesdec  $t0, $st1, $st1
    vaesdec  $t0, $st2, $st2

    # round 11
    vbroadcasti32x4 0xb0($key1), $t0
    vaesdec  $t0, $st1, $st1
    vaesdec  $t0, $st2, $st2

    # round 12
    vbroadcasti32x4 0xc0($key1), $t0
    vaesdec  $t0, $st1, $st1
    vaesdec  $t0, $st2, $st2

    # round 13
    vbroadcasti32x4 0xd0($key1), $t0
    vaesdec  $t0, $st1, $st1
    vaesdec  $t0, $st2, $st2

    # round 14
    vbroadcasti32x4 0xe0($key1), $t0
    vaesdeclast $t0, $st1, $st1
    vaesdeclast $t0, $st2, $st2
    vpxorq  $tw1, $st1, $st1
    vpxorq  $tw2, $st2, $st2
___
    # xor Tweak values
    if (0 == $last_eight) {
      # load next Tweak values
      $code .= <<___;
      vmovdqa32  %zmm15, $tw1
      vmovdqa32  %zmm16, $tw2
___
    }
  }

  # Encrypt 16 blocks in parallel and generate next 16 tweak values.
  sub encrypt_by_16 {
    my @st;
    $st[0] = $_[0];
    $st[1] = $_[1];
    $st[2] = $_[2];
    $st[3] = $_[3];

    my @tw;
    $tw[0] = $_[4];
    $tw[1] = $_[5];
    $tw[2] = $_[6];
    $tw[3] = $_[7];

    my $t0 = $_[8];
    my $last_eight = $_[9];

    # xor Tweak values
    for (my $i = 0; $i < 4; $i++) {
      $code .= "vpxorq    $tw[$i], $st[$i], $st[$i]\n";
    }

    # ARK
    $code .= "vbroadcasti32x4 ($key1), $t0\n";
    for (my $i = 0; $i < 4; $i++) {
      $code .= "vpxorq $t0, $st[$i], $st[$i]\n";
    }

    if (0 == $last_eight) {
      $code .= <<___;
      vpsrldq		\$0xf, $tw[2], %zmm13
      vpclmulqdq	\$0x0,$ZPOLY, %zmm13, %zmm14
      vpslldq		\$0x1, $tw[2], %zmm15
      vpxord		%zmm14, %zmm15, %zmm15
___
    }

    # round 1
    $code .= "vbroadcasti32x4 0x10($key1), $t0\n";
    for (my $i = 0; $i < 4; $i++) {
      $code .= "vaesenc $t0, $st[$i], $st[$i]\n";
    }

    # round 2
    $code .= "vbroadcasti32x4 0x20($key1), $t0\n";
    for (my $i = 0; $i < 4; $i++) {
      $code .= "vaesenc $t0, $st[$i], $st[$i]\n";
    }

    # round 3
    $code .= "vbroadcasti32x4 0x30($key1), $t0\n";
    for (my $i = 0; $i < 4; $i++) {
      $code .= "vaesenc $t0, $st[$i], $st[$i]\n";
    }

    if (0 == $last_eight) {
      $code .= <<___;
      vpsrldq		\$0xf, $tw[3], %zmm13
      vpclmulqdq	\$0x0,$ZPOLY, %zmm13, %zmm14
      vpslldq		\$0x1, $tw[3], %zmm16
      vpxord		%zmm14, %zmm16, %zmm16
___
    }
    # round 4
    $code .= "vbroadcasti32x4 0x40($key1), $t0\n";
    for (my $i = 0; $i < 4; $i++) {
      $code .= "vaesenc $t0, $st[$i], $st[$i]\n";
    }

    # round 5
    $code .= "vbroadcasti32x4 0x50($key1), $t0\n";
    for (my $i = 0; $i < 4; $i++) {
      $code .= "vaesenc $t0, $st[$i], $st[$i]\n";
    }

    # round 6
    $code .= "vbroadcasti32x4 0x60($key1), $t0\n";
    for (my $i = 0; $i < 4; $i++) {
      $code .= "vaesenc $t0, $st[$i], $st[$i]\n";
    }

    if (0 == $last_eight) {
      $code .= <<___;
      vpsrldq		\$0xf, %zmm15, %zmm13
      vpclmulqdq	\$0x0,$ZPOLY, %zmm13, %zmm14
      vpslldq		\$0x1, %zmm15, %zmm17
      vpxord		%zmm14, %zmm17, %zmm17
___
    }
    # round 7
    $code .= "vbroadcasti32x4 0x70($key1), $t0\n";
    for (my $i = 0; $i < 4; $i++) {
      $code .= "vaesenc $t0, $st[$i], $st[$i]\n";
    }

    # round 8
    $code .= "vbroadcasti32x4 0x80($key1), $t0\n";
    for (my $i = 0; $i < 4; $i++) {
      $code .= "vaesenc $t0, $st[$i], $st[$i]\n";
    }

    # round 9
    $code .= "vbroadcasti32x4 0x90($key1), $t0\n";
    for (my $i = 0; $i < 4; $i++) {
      $code .= "vaesenc $t0, $st[$i], $st[$i]\n";
    }

    if (0 == $last_eight) {
      $code .= <<___;
      vpsrldq		\$0xf, %zmm16, %zmm13
      vpclmulqdq	\$0x0,$ZPOLY, %zmm13, %zmm14
      vpslldq		\$0x1, %zmm16, %zmm18
      vpxord		%zmm14, %zmm18, %zmm18
___
    }
    # round 10
    $code .= "vbroadcasti32x4 0xa0($key1), $t0\n";
    for (my $i = 0; $i < 4; $i++) {
      $code .= "vaesenc $t0, $st[$i], $st[$i]\n";
    }
    # round 11
    $code .= "vbroadcasti32x4 0xb0($key1), $t0\n";
    for (my $i = 0; $i < 4; $i++) {
      $code .= "vaesenc $t0, $st[$i], $st[$i]\n";
    }
    # round 12
    $code .= "vbroadcasti32x4 0xc0($key1), $t0\n";
    for (my $i = 0; $i < 4; $i++) {
      $code .= "vaesenc $t0, $st[$i], $st[$i]\n";
    }
    # round 13
    $code .= "vbroadcasti32x4 0xd0($key1), $t0\n";
    for (my $i = 0; $i < 4; $i++) {
      $code .= "vaesenc $t0, $st[$i], $st[$i]\n";
    }
    # round 14
    $code .= "vbroadcasti32x4 0xe0($key1), $t0\n";
    for (my $i = 0; $i < 4; $i++) {
      $code .= "vaesenclast $t0, $st[$i], $st[$i]\n";
    }

    # xor Tweak values
    for (my $i = 0; $i < 4; $i++) {
      $code .= "vpxorq    $tw[$i], $st[$i], $st[$i]\n";
    }

    $code .= <<___;
    # load next Tweak values
    vmovdqa32  %zmm15, $tw[0]
    vmovdqa32  %zmm16, $tw[1]
    vmovdqa32  %zmm17, $tw[2]
    vmovdqa32  %zmm18, $tw[3]
___
  }

  # Decrypt 16 blocks in parallel and generate next 16 tweak values.
  sub decrypt_by_16 {
    my @st;
    $st[0] = $_[0];
    $st[1] = $_[1];
    $st[2] = $_[2];
    $st[3] = $_[3];

    my @tw;
    $tw[0] = $_[4];
    $tw[1] = $_[5];
    $tw[2] = $_[6];
    $tw[3] = $_[7];

    my $t0 = $_[8];
    my $last_eight = $_[9];

    # xor Tweak values
    for (my $i = 0; $i < 4; $i++) {
      $code .= "vpxorq    $tw[$i], $st[$i], $st[$i]\n";
    }

    # ARK
    $code .= "vbroadcasti32x4 ($key1), $t0\n";
    for (my $i = 0; $i < 4; $i++) {
      $code .= "vpxorq $t0, $st[$i], $st[$i]\n";
    }

    if (0 == $last_eight) {
      $code .= <<___;
      vpsrldq		\$0xf, $tw[2], %zmm13
      vpclmulqdq	\$0x0,$ZPOLY, %zmm13, %zmm14
      vpslldq		\$0x1, $tw[2], %zmm15
      vpxord		%zmm14, %zmm15, %zmm15
___
    }

    # round 1
    $code .= "vbroadcasti32x4 0x10($key1), $t0\n";
    for (my $i = 0; $i < 4; $i++) {
      $code .= "vaesdec $t0, $st[$i], $st[$i]\n";
    }

    # round 2
    $code .= "vbroadcasti32x4 0x20($key1), $t0\n";
    for (my $i = 0; $i < 4; $i++) {
      $code .= "vaesdec $t0, $st[$i], $st[$i]\n";
    }

    # round 3
    $code .= "vbroadcasti32x4 0x30($key1), $t0\n";
    for (my $i = 0; $i < 4; $i++) {
      $code .= "vaesdec $t0, $st[$i], $st[$i]\n";
    }

    if (0 == $last_eight) {
      $code .= <<___;
      vpsrldq		\$0xf, $tw[3], %zmm13
      vpclmulqdq	\$0x0,$ZPOLY, %zmm13, %zmm14
      vpslldq		\$0x1, $tw[3], %zmm16
      vpxord		%zmm14, %zmm16, %zmm16
___
    }
    # round 4
    $code .= "vbroadcasti32x4 0x40($key1), $t0\n";
    for (my $i = 0; $i < 4; $i++) {
      $code .= "vaesdec $t0, $st[$i], $st[$i]\n";
    }

    # round 5
    $code .= "vbroadcasti32x4 0x50($key1), $t0\n";
    for (my $i = 0; $i < 4; $i++) {
      $code .= "vaesdec $t0, $st[$i], $st[$i]\n";
    }

    # round 6
    $code .= "vbroadcasti32x4 0x60($key1), $t0\n";
    for (my $i = 0; $i < 4; $i++) {
      $code .= "vaesdec $t0, $st[$i], $st[$i]\n";
    }

    if (0 == $last_eight) {
      $code .= <<___;
      vpsrldq		\$0xf, %zmm15, %zmm13
      vpclmulqdq	\$0x0,$ZPOLY, %zmm13, %zmm14
      vpslldq		\$0x1, %zmm15, %zmm17
      vpxord		%zmm14, %zmm17, %zmm17
___
    }
    # round 7
    $code .= "vbroadcasti32x4 0x70($key1), $t0\n";
    for (my $i = 0; $i < 4; $i++) {
      $code .= "vaesdec $t0, $st[$i], $st[$i]\n";
    }

    # round 8
    $code .= "vbroadcasti32x4 0x80($key1), $t0\n";
    for (my $i = 0; $i < 4; $i++) {
      $code .= "vaesdec $t0, $st[$i], $st[$i]\n";
    }

    # round 9
    $code .= "vbroadcasti32x4 0x90($key1), $t0\n";
    for (my $i = 0; $i < 4; $i++) {
      $code .= "vaesdec $t0, $st[$i], $st[$i]\n";
    }

    if (0 == $last_eight) {
      $code .= <<___;
      vpsrldq		\$0xf, %zmm16, %zmm13
      vpclmulqdq	\$0x0,$ZPOLY, %zmm13, %zmm14
      vpslldq		\$0x1, %zmm16, %zmm18
      vpxord		%zmm14, %zmm18, %zmm18
___
    }
    # round 10
    $code .= "vbroadcasti32x4 0xa0($key1), $t0\n";
    for (my $i = 0; $i < 4; $i++) {
      $code .= "vaesdec $t0, $st[$i], $st[$i]\n";
    }
    # round 11
    $code .= "vbroadcasti32x4 0xb0($key1), $t0\n";
    for (my $i = 0; $i < 4; $i++) {
      $code .= "vaesdec $t0, $st[$i], $st[$i]\n";
    }
    # round 12
    $code .= "vbroadcasti32x4 0xc0($key1), $t0\n";
    for (my $i = 0; $i < 4; $i++) {
      $code .= "vaesdec $t0, $st[$i], $st[$i]\n";
    }
    # round 13
    $code .= "vbroadcasti32x4 0xd0($key1), $t0\n";
    for (my $i = 0; $i < 4; $i++) {
      $code .= "vaesdec $t0, $st[$i], $st[$i]\n";
    }
    # round 14
    $code .= "vbroadcasti32x4 0xe0($key1), $t0\n";
    for (my $i = 0; $i < 4; $i++) {
      $code .= "vaesdeclast $t0, $st[$i], $st[$i]\n";
    }

    # xor Tweak values
    for (my $i = 0; $i < 4; $i++) {
      $code .= "vpxorq    $tw[$i], $st[$i], $st[$i]\n";
    }

    $code .= <<___;
    # load next Tweak values
    vmovdqa32  %zmm15, $tw[0]
    vmovdqa32  %zmm16, $tw[1]
    vmovdqa32  %zmm17, $tw[2]
    vmovdqa32  %zmm18, $tw[3]
___
  }

  $code .= ".text\n";

  # ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  # ;void aes_hw_xts_encrypt_avx512(
  # ;               const uint8_t *in,        // input data
  # ;               uint8_t *out,             // output data
  # ;               size_t length,            // sector size, in bytes
  # ;               const AES_KEY *key1,      // key used for "ECB" encryption
  # ;               const AES_KEY *key2,      // key used for tweaking
  # ;               const uint8_t iv[16])     // initial tweak value, 16 bytes
  # ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  sub enc {
    my $rndsuffix = &random_string();

    $code.=<<___;
    .globl	aes_hw_xts_encrypt_avx512
    .hidden	aes_hw_xts_encrypt_avx512
    .type	aes_hw_xts_encrypt_avx512,\@function,6
    .align	32
    aes_hw_xts_encrypt_avx512:
    .cfi_startproc
    endbranch
___
    $code .= "push 	 %rbp\n";
    $code .= "mov 	 $TW,%rbp\n";
    $code .= "sub 	 \$$VARIABLE_OFFSET,$TW\n";
    $code .= "and 	 \$0xffffffffffffffc0,$TW\n";
    $code .= "mov 	 %rbx,$GP_STORAGE($TW)\n";

    if ($win64) {
      $code .= "mov 	 %rdi,$GP_STORAGE + 8*1($TW)\n";
      $code .= "mov 	 %rsi,$GP_STORAGE + 8*2($TW)\n";
      $code .= "vmovdqa      %xmm6, $XMM_STORAGE + 16*0($TW)\n";
      $code .= "vmovdqa      %xmm7, $XMM_STORAGE + 16*1($TW)\n";
      $code .= "vmovdqa      %xmm8, $XMM_STORAGE + 16*2($TW)\n";
      $code .= "vmovdqa      %xmm9, $XMM_STORAGE + 16*3($TW)\n";
      $code .= "vmovdqa      %xmm10, $XMM_STORAGE + 16*4($TW)\n";
      $code .= "vmovdqa      %xmm11, $XMM_STORAGE + 16*5($TW)\n";
      $code .= "vmovdqa      %xmm12, $XMM_STORAGE + 16*6($TW)\n";
      $code .= "vmovdqa      %xmm13, $XMM_STORAGE + 16*7($TW)\n";
      $code .= "vmovdqa      %xmm14, $XMM_STORAGE + 16*8($TW)\n";
      $code .= "vmovdqa      %xmm15, $XMM_STORAGE + 16*9($TW)\n";
    }

    $code .= "mov 	 \$0x87, $gf_poly_8b\n";
    $code .= "vmovdqu 	 ($tweak),%xmm1\n";      # read initial tweak values

    encrypt_tweak("%xmm1");

    if ($win64) {
      $code .= "mov	 $input, 8 + 8*5(%rbp)\n";  # ciphertext pointer
      $code .= "mov        $output, 8 + 8*6(%rbp)\n"; # plaintext pointer
    }

    {
    $code.=<<___;

    cmp 	 \$0x80,$length
    jl 	 .L_less_than_128_bytes_${rndsuffix}
    vpbroadcastq 	 $gf_poly_8b,$ZPOLY
    cmp 	 \$0x100,$length
    jge 	 .L_start_by16_${rndsuffix}
    cmp 	 \$0x80,$length
    jge 	 .L_start_by8_${rndsuffix}

    .L_do_n_blocks_${rndsuffix}:
    cmp 	 \$0x0,$length
    je 	 .L_ret_${rndsuffix}
    cmp 	 \$0x70,$length
    jge 	 .L_remaining_num_blocks_is_7_${rndsuffix}
    cmp 	 \$0x60,$length
    jge 	 .L_remaining_num_blocks_is_6_${rndsuffix}
    cmp 	 \$0x50,$length
    jge 	 .L_remaining_num_blocks_is_5_${rndsuffix}
    cmp 	 \$0x40,$length
    jge 	 .L_remaining_num_blocks_is_4_${rndsuffix}
    cmp 	 \$0x30,$length
    jge 	 .L_remaining_num_blocks_is_3_${rndsuffix}
    cmp 	 \$0x20,$length
    jge 	 .L_remaining_num_blocks_is_2_${rndsuffix}
    cmp 	 \$0x10,$length
    jge 	 .L_remaining_num_blocks_is_1_${rndsuffix}
    vmovdqa 	 %xmm0,%xmm8
    vmovdqa 	 %xmm9,%xmm0
    jmp 	 .L_steal_cipher_${rndsuffix}

    .L_remaining_num_blocks_is_7_${rndsuffix}:
    mov 	 \$0x0000ffffffffffff,$tmp1
    kmovq 	 $tmp1,%k1
    vmovdqu8 	 ($input),%zmm1
    vmovdqu8 	 0x40($input),%zmm2{%k1}
    add 	 \$0x70,$input
___
    }

    encrypt_by_eight("%zmm1", "%zmm2", "%zmm9", "%zmm10", "%zmm0", 1);

    {
    $code .= <<___;
    vmovdqu8 	 %zmm1,($output)
    vmovdqu8 	 %zmm2,0x40($output){%k1}
    add 	 \$0x70,$output
    vextracti32x4 	 \$0x2,%zmm2,%xmm8
    vextracti32x4 	 \$0x3,%zmm10,%xmm0
    and 	 \$0xf,$length
    je 	 .L_ret_${rndsuffix}
    jmp 	 .L_steal_cipher_${rndsuffix}

    .L_remaining_num_blocks_is_6_${rndsuffix}:
    vmovdqu8 	 ($input),%zmm1
    vmovdqu8 	 0x40($input),%ymm2
    add 	 \$0x60,$input
___
    }

    encrypt_by_eight("%zmm1", "%zmm2", "%zmm9", "%zmm10", "%zmm0", 1);

    {
    $code .= <<___;
    vmovdqu8 	 %zmm1,($output)
    vmovdqu8 	 %ymm2,0x40($output)
    add 	 \$0x60,$output
    vextracti32x4 	 \$0x1,%zmm2,%xmm8
    vextracti32x4 	 \$0x2,%zmm10,%xmm0
    and 	 \$0xf,$length
    je 	 .L_ret_${rndsuffix}
    jmp 	 .L_steal_cipher_${rndsuffix}

    .L_remaining_num_blocks_is_5_${rndsuffix}:
    vmovdqu8 	 ($input),%zmm1
    vmovdqu 	 0x40($input),%xmm2
    add 	 \$0x50,$input
___
    }

    encrypt_by_eight("%zmm1", "%zmm2", "%zmm9", "%zmm10", "%zmm0", 1);

    {
    $code .= <<___;
    vmovdqu8 	 %zmm1,($output)
    vmovdqu 	 %xmm2,0x40($output)
    add 	 \$0x50,$output
    vmovdqa 	 %xmm2,%xmm8
    vextracti32x4 	 \$0x1,%zmm10,%xmm0
    and 	 \$0xf,$length
    je 	 .L_ret_${rndsuffix}
    jmp 	 .L_steal_cipher_${rndsuffix}

    .L_remaining_num_blocks_is_4_${rndsuffix}:
    vmovdqu8 	 ($input),%zmm1
    add 	 \$0x40,$input
___
    }

    encrypt_by_four("%zmm1", "%zmm9", "%zmm0");

    {
    $code .= <<___;
    vmovdqu8	%zmm1,($output)
    add	\$0x40,$output
    vextracti32x4	\$0x3,%zmm1,%xmm8
    vmovdqa64	%xmm10, %xmm0
    and	\$0xf,$length
    je	.L_ret_${rndsuffix}
    jmp	.L_steal_cipher_${rndsuffix}
___
    }

    {
    $code .= <<___;
    .L_remaining_num_blocks_is_3_${rndsuffix}:
    mov	\$-1, $tmp1
    shr	\$0x10, $tmp1
    kmovq	$tmp1, %k1
    vmovdqu8	($input), %zmm1{%k1}
    add	\$0x30, $input
___
    }

    encrypt_by_four("%zmm1", "%zmm9", "%zmm0");

    {
    $code .= <<___;
    vmovdqu8	%zmm1, ($output){%k1}
    add	\$0x30, $output
    vextracti32x4	\$0x2, %zmm1, %xmm8
    vextracti32x4	\$0x3, %zmm9, %xmm0
    and	\$0xf, $length
    je	.L_ret_${rndsuffix}
    jmp	.L_steal_cipher_${rndsuffix}
___
    }

    {
    $code .= <<___;
    .L_remaining_num_blocks_is_2_${rndsuffix}:
    vmovdqu8	($input), %ymm1
    add	\$0x20, $input
___
    }

    encrypt_by_four("%ymm1", "%ymm9", "%ymm0");

    {
    $code .= <<___;
    vmovdqu 	 %ymm1,($output)
    add 	 \$0x20,$output
    vextracti32x4	\$0x1, %zmm1, %xmm8
    vextracti32x4	\$0x2,%zmm9,%xmm0
    and 	 \$0xf,$length
    je 	 .L_ret_${rndsuffix}
    jmp 	 .L_steal_cipher_${rndsuffix}
___
    }

    {
    $code .= <<___;
    .L_remaining_num_blocks_is_1_${rndsuffix}:
    vmovdqu 	 ($input),%xmm1
    add 	 \$0x10,$input
___
    }

    encrypt_final("%xmm1", "%xmm9");

    {
    $code .= <<___;
    vmovdqu 	 %xmm1,($output)
    add 	 \$0x10,$output
    vmovdqa 	 %xmm1,%xmm8
    vextracti32x4 	 \$0x1,%zmm9,%xmm0
    and 	 \$0xf,$length
    je 	 .L_ret_${rndsuffix}
    jmp 	 .L_steal_cipher_${rndsuffix}


    # Set up for and then generation of 16 tweaks.
    .L_start_by16_${rndsuffix}:
    vbroadcasti32x4 	 ($TW),%zmm0
    vbroadcasti32x4 shufb_15_7(%rip),%zmm8
    mov 	 \$0xaa,$tmp1
    kmovq 	 $tmp1,%k2
    vpshufb 	 %zmm8,%zmm0,%zmm1

    # Tweaks 0-3
    vpsllvq const_dq3210(%rip),%zmm0,%zmm4
    vpsrlvq const_dq5678(%rip),%zmm1,%zmm2
    vpclmulqdq 	 \$0x0,$ZPOLY,%zmm2,%zmm3
    vpxorq 	 %zmm2,%zmm4,%zmm4{%k2}
    vpxord 	 %zmm4,%zmm3,%zmm9

    # Tweaks 4-7
    vpsllvq const_dq7654(%rip),%zmm0,%zmm5
    vpsrlvq const_dq1234(%rip),%zmm1,%zmm6
    vpclmulqdq 	 \$0x0,$ZPOLY,%zmm6,%zmm7
    vpxorq 	 %zmm6,%zmm5,%zmm5{%k2}
    vpxord 	 %zmm5,%zmm7,%zmm10

    # Tweaks 8-11
    vpsrldq 	 \$0xf,%zmm9,%zmm13
    vpclmulqdq 	 \$0x0,$ZPOLY,%zmm13,%zmm14
    vpslldq 	 \$0x1,%zmm9,%zmm11
    vpxord 	 %zmm14,%zmm11,%zmm11

    # Tweaks 12-15
    vpsrldq 	 \$0xf,%zmm10,%zmm15
    vpclmulqdq 	 \$0x0,$ZPOLY,%zmm15,%zmm16
    vpslldq 	 \$0x1,%zmm10,%zmm12
    vpxord 	 %zmm16,%zmm12,%zmm12

    .L_main_loop_run_16_${rndsuffix}:
    vmovdqu8 	 ($input),%zmm1
    vmovdqu8 	 0x40($input),%zmm2
    vmovdqu8 	 0x80($input),%zmm3
    vmovdqu8 	 0xc0($input),%zmm4
    add 	 \$0x100,$input
___
    }

    encrypt_by_16("%zmm1", "%zmm2", "%zmm3", "%zmm4", "%zmm9",
                      "%zmm10", "%zmm11", "%zmm12", "%zmm0", 0);

    {
    $code .= <<___;
    vmovdqu8 	 %zmm1,($output)
    vmovdqu8 	 %zmm2,0x40($output)
    vmovdqu8 	 %zmm3,0x80($output)
    vmovdqu8 	 %zmm4,0xc0($output)
    add 	 \$0x100,$output
    sub 	 \$0x100,$length
    cmp 	 \$0x100,$length
    jae 	 .L_main_loop_run_16_${rndsuffix}
    cmp 	 \$0x80,$length
    jae 	 .L_main_loop_run_8_${rndsuffix}
    vextracti32x4 	 \$0x3,%zmm4,%xmm0
    jmp 	 .L_do_n_blocks_${rndsuffix}

    .L_start_by8_${rndsuffix}:
    vbroadcasti32x4 	 ($TW),%zmm0
    vbroadcasti32x4 shufb_15_7(%rip),%zmm8
    mov 	 \$0xaa,$tmp1
    kmovq 	 $tmp1,%k2
    vpshufb 	 %zmm8,%zmm0,%zmm1
    vpsllvq const_dq3210(%rip),%zmm0,%zmm4
    vpsrlvq const_dq5678(%rip),%zmm1,%zmm2
    vpclmulqdq 	 \$0x0,%zmm25,%zmm2,%zmm3
    vpxorq 	 %zmm2,%zmm4,%zmm4{%k2}
    vpxord 	 %zmm4,%zmm3,%zmm9
    vpsllvq const_dq7654(%rip),%zmm0,%zmm5
    vpsrlvq const_dq1234(%rip),%zmm1,%zmm6
    vpclmulqdq 	 \$0x0,%zmm25,%zmm6,%zmm7
    vpxorq 	 %zmm6,%zmm5,%zmm5{%k2}
    vpxord 	 %zmm5,%zmm7,%zmm10

    .L_main_loop_run_8_${rndsuffix}:
    vmovdqu8 	 ($input),%zmm1
    vmovdqu8 	 0x40($input),%zmm2
    add 	 \$0x80,$input
___
    }

    encrypt_by_eight("%zmm1", "%zmm2", "%zmm9", "%zmm10", "%zmm0", 0);

    {
    $code .= <<___;
    vmovdqu8 	 %zmm1,($output)
    vmovdqu8 	 %zmm2,0x40($output)
    add 	 \$0x80,$output
    sub 	 \$0x80,$length
    cmp 	 \$0x80,$length
    jae 	 .L_main_loop_run_8_${rndsuffix}
    vextracti32x4 	 \$0x3,%zmm2,%xmm0
    jmp 	 .L_do_n_blocks_${rndsuffix}

    .L_steal_cipher_${rndsuffix}:
    vmovdqa	%xmm8,%xmm2
    lea	vpshufb_shf_table(%rip),$TEMPLOW
    vmovdqu	($TEMPLOW,$length,1),%xmm10
    vpshufb	%xmm10,%xmm8,%xmm8
    vmovdqu	-0x10($input,$length,1),%xmm3
    vmovdqu	%xmm8,-0x10($output,$length,1)
    lea	vpshufb_shf_table(%rip),$TEMPLOW
    add	\$16, $TEMPLOW
    sub	$length,$TEMPLOW
    vmovdqu	($TEMPLOW),%xmm10
    vpxor	mask1(%rip),%xmm10,%xmm10
    vpshufb	%xmm10,%xmm3,%xmm3
    vpblendvb	%xmm10,%xmm2,%xmm3,%xmm3
    vpxor	%xmm0,%xmm3,%xmm8
    vpxor	($key1),%xmm8,%xmm8
    vaesenc	0x10($key1),%xmm8,%xmm8
    vaesenc	0x20($key1),%xmm8,%xmm8
    vaesenc	0x30($key1),%xmm8,%xmm8
    vaesenc	0x40($key1),%xmm8,%xmm8
    vaesenc	0x50($key1),%xmm8,%xmm8
    vaesenc	0x60($key1),%xmm8,%xmm8
    vaesenc	0x70($key1),%xmm8,%xmm8
    vaesenc	0x80($key1),%xmm8,%xmm8
    vaesenc	0x90($key1),%xmm8,%xmm8
    vaesenc	0xa0($key1),%xmm8,%xmm8
    vaesenc	0xb0($key1),%xmm8,%xmm8
    vaesenc	0xc0($key1),%xmm8,%xmm8
    vaesenc	0xd0($key1),%xmm8,%xmm8
    vaesenclast	0xe0($key1),%xmm8,%xmm8
    vpxor	%xmm0,%xmm8,%xmm8
    vmovdqu	%xmm8,-0x10($output)

    .L_ret_${rndsuffix}:
    mov 	 $GP_STORAGE($TW),%rbx
    xor    $tmp1,$tmp1
    mov    $tmp1,$GP_STORAGE($TW)
    vpxorq %zmm0,%zmm0,%zmm0
___
    }

    if ($win64) {
      $code .= <<___;
      mov $GP_STORAGE + 8*1($TW),%rdi
      mov $tmp1,$GP_STORAGE + 8*1($TW)
      mov $GP_STORAGE + 8*2($TW),%rsi
      mov $tmp1,$GP_STORAGE + 8*2($TW)

      vmovdqa $XMM_STORAGE + 16 * 0($TW), %xmm6
      vmovdqa $XMM_STORAGE + 16 * 1($TW), %xmm7
      vmovdqa $XMM_STORAGE + 16 * 2($TW), %xmm8
      vmovdqa $XMM_STORAGE + 16 * 3($TW), %xmm9

      # Zero the 64 bytes we just restored to the xmm registers.
      vmovdqa64 %zmm0,$XMM_STORAGE($TW)

      vmovdqa $XMM_STORAGE + 16 * 4($TW), %xmm10
      vmovdqa $XMM_STORAGE + 16 * 5($TW), %xmm11
      vmovdqa $XMM_STORAGE + 16 * 6($TW), %xmm12
      vmovdqa $XMM_STORAGE + 16 * 7($TW), %xmm13

      # And again.
      vmovdqa64 %zmm0,$XMM_STORAGE + 16 * 4($TW)

      vmovdqa $XMM_STORAGE + 16 * 8($TW), %xmm14
      vmovdqa $XMM_STORAGE + 16 * 9($TW), %xmm15

      # Last round is only 32 bytes (256-bits), so we use `%ymm` as the
      # source operand.
      vmovdqa %ymm0,$XMM_STORAGE + 16 * 8($TW)
___
    }

    {
    $code .= <<___;
    mov %rbp,$TW
    pop %rbp
    vzeroupper
    ret

    .L_less_than_128_bytes_${rndsuffix}:
    vpbroadcastq	$gf_poly_8b, $ZPOLY
    cmp 	 \$0x10,$length
    jb 	 .L_ret_${rndsuffix}
    vbroadcasti32x4	($TW), %zmm0
    vbroadcasti32x4	shufb_15_7(%rip), %zmm8
    movl    \$0xaa, %r8d
    kmovq	%r8, %k2
    mov	$length,$tmp1
    and	\$0x70,$tmp1
    cmp	\$0x60,$tmp1
    je	.L_num_blocks_is_6_${rndsuffix}
    cmp	\$0x50,$tmp1
    je	.L_num_blocks_is_5_${rndsuffix}
    cmp	\$0x40,$tmp1
    je	.L_num_blocks_is_4_${rndsuffix}
    cmp	\$0x30,$tmp1
    je	.L_num_blocks_is_3_${rndsuffix}
    cmp	\$0x20,$tmp1
    je	.L_num_blocks_is_2_${rndsuffix}
    cmp	\$0x10,$tmp1
    je	.L_num_blocks_is_1_${rndsuffix}

    .L_num_blocks_is_7_${rndsuffix}:
    vpshufb	%zmm8, %zmm0, %zmm1
    vpsllvq	const_dq3210(%rip), %zmm0, %zmm4
    vpsrlvq	const_dq5678(%rip), %zmm1, %zmm2
    vpclmulqdq	\$0x00, $ZPOLY, %zmm2, %zmm3
    vpxorq	%zmm2, %zmm4, %zmm4{%k2}
    vpxord	%zmm4, %zmm3, %zmm9
    vpsllvq	const_dq7654(%rip), %zmm0, %zmm5
    vpsrlvq	const_dq1234(%rip), %zmm1, %zmm6
    vpclmulqdq	\$0x00, $ZPOLY, %zmm6, %zmm7
    vpxorq	%zmm6, %zmm5, %zmm5{%k2}
    vpxord	%zmm5, %zmm7, %zmm10
    mov	\$0x0000ffffffffffff, $tmp1
    kmovq	$tmp1, %k1
    vmovdqu8	16*0($input), %zmm1
    vmovdqu8	16*4($input), %zmm2{%k1}

    add	\$0x70,$input
___
    }

    encrypt_by_eight("%zmm1", "%zmm2", "%zmm9", "%zmm10", "%zmm0", 1);

    {
    $code .= <<___;
    vmovdqu8	%zmm1, 16*0($output)
    vmovdqu8	%zmm2, 16*4($output){%k1}
    add	\$0x70,$output
    vextracti32x4	\$0x2, %zmm2, %xmm8
    vextracti32x4	\$0x3, %zmm10, %xmm0
    and	\$0xf,$length
    je	.L_ret_${rndsuffix}
    jmp	.L_steal_cipher_${rndsuffix}
___
    }

    {
    $code .= <<___;
    .L_num_blocks_is_6_${rndsuffix}:
    vpshufb	%zmm8, %zmm0, %zmm1
    vpsllvq	const_dq3210(%rip), %zmm0, %zmm4
    vpsrlvq	const_dq5678(%rip), %zmm1, %zmm2
    vpclmulqdq	\$0x00, $ZPOLY, %zmm2, %zmm3
    vpxorq	%zmm2, %zmm4, %zmm4{%k2}
    vpxord	%zmm4, %zmm3, %zmm9
    vpsllvq	const_dq7654(%rip), %zmm0, %zmm5
    vpsrlvq	const_dq1234(%rip), %zmm1, %zmm6
    vpclmulqdq	\$0x00, $ZPOLY, %zmm6, %zmm7
    vpxorq	%zmm6, %zmm5, %zmm5{%k2}
    vpxord	%zmm5, %zmm7, %zmm10
    vmovdqu8	16*0($input), %zmm1
    vmovdqu8	16*4($input), %ymm2
    add	\$96, $input
___
    }

    encrypt_by_eight("%zmm1", "%zmm2", "%zmm9", "%zmm10", "%zmm0", 1);

    {
    $code .= <<___;
    vmovdqu8	%zmm1, 16*0($output)
    vmovdqu8	%ymm2, 16*4($output)
    add	\$96, $output

    vextracti32x4	\$0x1, %ymm2, %xmm8
    vextracti32x4	\$0x2, %zmm10, %xmm0
    and	\$0xf,$length
    je	.L_ret_${rndsuffix}
    jmp	.L_steal_cipher_${rndsuffix}
___
    }

    {
    $code .= <<___;
    .L_num_blocks_is_5_${rndsuffix}:
    vpshufb	%zmm8, %zmm0, %zmm1
    vpsllvq	const_dq3210(%rip), %zmm0, %zmm4
    vpsrlvq	const_dq5678(%rip), %zmm1, %zmm2
    vpclmulqdq	\$0x00, $ZPOLY, %zmm2, %zmm3
    vpxorq	%zmm2, %zmm4, %zmm4{%k2}
    vpxord	%zmm4, %zmm3, %zmm9
    vpsllvq	const_dq7654(%rip), %zmm0, %zmm5
    vpsrlvq	const_dq1234(%rip), %zmm1, %zmm6
    vpclmulqdq	\$0x00, $ZPOLY, %zmm6, %zmm7
    vpxorq	%zmm6, %zmm5, %zmm5{%k2}
    vpxord	%zmm5, %zmm7, %zmm10
    vmovdqu8	16*0($input), %zmm1
    vmovdqu8	16*4($input), %xmm2
    add	\$80, $input
___
    }

    encrypt_by_eight("%zmm1", "%zmm2", "%zmm9", "%zmm10", "%zmm0", 1);

    {
    $code .= <<___;
    vmovdqu8	%zmm1, 16*0($output)
    vmovdqu8	%xmm2, 16*4($output)
    add	\$80, $output

    vmovdqa	%xmm2, %xmm8
    vextracti32x4	\$0x1, %zmm10, %xmm0
    and	\$0xf,$length
    je	.L_ret_${rndsuffix}
    jmp	.L_steal_cipher_${rndsuffix}
___
    }

    {
    $code .= <<___;
    .L_num_blocks_is_4_${rndsuffix}:
    vpshufb	%zmm8, %zmm0, %zmm1
    vpsllvq	const_dq3210(%rip), %zmm0, %zmm4
    vpsrlvq	const_dq5678(%rip), %zmm1, %zmm2
    vpclmulqdq	\$0x00, $ZPOLY, %zmm2, %zmm3
    vpxorq	%zmm2, %zmm4, %zmm4{%k2}
    vpxord	%zmm4, %zmm3, %zmm9
    vpsllvq	const_dq7654(%rip), %zmm0, %zmm5
    vpsrlvq	const_dq1234(%rip), %zmm1, %zmm6
    vpclmulqdq	\$0x00, $ZPOLY, %zmm6, %zmm7
    vpxorq	%zmm6, %zmm5, %zmm5{%k2}
    vpxord	%zmm5, %zmm7, %zmm10
    vmovdqu8	16*0($input), %zmm1
    add	\$64, $input
___
    }

    encrypt_by_four("%zmm1", "%zmm9", "%zmm0");

    {
    $code .= <<___;
    vmovdqu8	%zmm1, 16*0($output)
    add	\$64, $output
    vextracti32x4	\$0x3, %zmm1, %xmm8
    vmovdqa	%xmm10, %xmm0
    and	\$0xf,$length
    je	.L_ret_${rndsuffix}
    jmp	.L_steal_cipher_${rndsuffix}
___
    }

    {
    $code .= <<___;
    .L_num_blocks_is_3_${rndsuffix}:
    vpshufb	%zmm8, %zmm0, %zmm1
    vpsllvq	const_dq3210(%rip), %zmm0, %zmm4
    vpsrlvq	const_dq5678(%rip), %zmm1, %zmm2
    vpclmulqdq	\$0x00, $ZPOLY, %zmm2, %zmm3
    vpxorq	%zmm2, %zmm4, %zmm4{%k2}
    vpxord	%zmm4, %zmm3, %zmm9
    mov	\$0x0000ffffffffffff, $tmp1
    kmovq	$tmp1, %k1
    vmovdqu8	16*0($input), %zmm1{%k1}
    add	\$48, $input
___
    }

    encrypt_by_four("%zmm1", "%zmm9", "%zmm0");

    {
    $code .= <<___;
    vmovdqu8	%zmm1, 16*0($output){%k1}
    add	\$48, $output
    vextracti32x4	\$2, %zmm1, %xmm8
    vextracti32x4	\$3, %zmm9, %xmm0
    and	\$0xf,$length
    je	.L_ret_${rndsuffix}
    jmp	.L_steal_cipher_${rndsuffix}
___
    }

    {
    $code .= <<___;
    .L_num_blocks_is_2_${rndsuffix}:
    vpshufb	%zmm8, %zmm0, %zmm1
    vpsllvq	const_dq3210(%rip), %zmm0, %zmm4
    vpsrlvq	const_dq5678(%rip), %zmm1, %zmm2
    vpclmulqdq	\$0x00, $ZPOLY, %zmm2, %zmm3
    vpxorq	%zmm2, %zmm4, %zmm4{%k2}
    vpxord	%zmm4, %zmm3, %zmm9

    vmovdqu8	16*0($input), %ymm1
    add	\$32, $input
___
    }

    encrypt_by_four("%ymm1", "%ymm9", "%ymm0");

    {
    $code .= <<___;
    vmovdqu8	%ymm1, 16*0($output)
    add	\$32, $output

    vextracti32x4	\$1, %ymm1, %xmm8
    vextracti32x4	\$2, %zmm9, %xmm0
    and	\$0xf,$length
    je	.L_ret_${rndsuffix}
    jmp	.L_steal_cipher_${rndsuffix}
___
    }

    {
    $code .= <<___;
    .L_num_blocks_is_1_${rndsuffix}:
    vpshufb	%zmm8, %zmm0, %zmm1
    vpsllvq	const_dq3210(%rip), %zmm0, %zmm4
    vpsrlvq	const_dq5678(%rip), %zmm1, %zmm2
    vpclmulqdq	\$0x00, $ZPOLY, %zmm2, %zmm3
    vpxorq	%zmm2, %zmm4, %zmm4{%k2}
    vpxord	%zmm4, %zmm3, %zmm9

    vmovdqu8	16*0($input), %xmm1
    add	\$16, $input
___
    }

    encrypt_by_four("%ymm1", "%ymm9", "%ymm0");

    {
    $code .= <<___;
    vmovdqu8	%xmm1, 16*0($output)
    add	\$16, $output

    vmovdqa	%xmm1, %xmm8
    vextracti32x4	\$1, %zmm9, %xmm0
    and	\$0xf,$length
    je	.L_ret_${rndsuffix}
    jmp	.L_steal_cipher_${rndsuffix}
    .cfi_endproc
___
    }
  }

  # ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  # ;void aes_hw_xts_decrypt_avx512(
  # ;               const uint8_t *in,        // input data
  # ;               uint8_t *out,             // output data
  # ;               size_t length,            // sector size, in bytes
  # ;               const AES_KEY *key1,      // key used for "ECB" encryption, 16*2 bytes
  # ;               const AES_KEY *key2,      // key used for tweaking, 16*2 bytes
  # ;               const uint8_t iv[16])      // initial tweak value, 16 bytes
  # ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  sub dec {
    my $rndsuffix = &random_string();

    $code.=<<___;
    .globl	aes_hw_xts_decrypt_avx512
    .hidden	aes_hw_xts_decrypt_avx512
    .type	aes_hw_xts_decrypt_avx512,\@function,6
    .align	32
    aes_hw_xts_decrypt_avx512:
    .cfi_startproc
    endbranch
___
    $code .= "push 	 %rbp\n";
    $code .= "mov 	 $TW,%rbp\n";
    $code .= "sub 	 \$$VARIABLE_OFFSET,$TW\n";
    $code .= "and 	 \$0xffffffffffffffc0,$TW\n";
    $code .= "mov 	 %rbx,$GP_STORAGE($TW)\n";

    if ($win64) {
      $code .= "mov 	 %rdi,$GP_STORAGE + 8*1($TW)\n";
      $code .= "mov 	 %rsi,$GP_STORAGE + 8*2($TW)\n";
      $code .= "vmovdqa      %xmm6, $XMM_STORAGE + 16*0($TW)\n";
      $code .= "vmovdqa      %xmm7, $XMM_STORAGE + 16*1($TW)\n";
      $code .= "vmovdqa      %xmm8, $XMM_STORAGE + 16*2($TW)\n";
      $code .= "vmovdqa      %xmm9, $XMM_STORAGE + 16*3($TW)\n";
      $code .= "vmovdqa      %xmm10, $XMM_STORAGE + 16*4($TW)\n";
      $code .= "vmovdqa      %xmm11, $XMM_STORAGE + 16*5($TW)\n";
      $code .= "vmovdqa      %xmm12, $XMM_STORAGE + 16*6($TW)\n";
      $code .= "vmovdqa      %xmm13, $XMM_STORAGE + 16*7($TW)\n";
      $code .= "vmovdqa      %xmm14, $XMM_STORAGE + 16*8($TW)\n";
      $code .= "vmovdqa      %xmm15, $XMM_STORAGE + 16*9($TW)\n";
    }

    $code .= "mov 	 \$0x87, $gf_poly_8b\n";
    $code .= "vmovdqu 	 ($tweak),%xmm1\n";      # read initial tweak values

    encrypt_tweak("%xmm1");

    if ($win64) {
      $code .= "mov	 $input, 8 + 8*5(%rbp)\n";  # ciphertext pointer
      $code .= "mov        $output, 8 + 8*6(%rbp)\n"; # plaintext pointer
    }

    {
    $code.=<<___;
    # XTS decryption involves special tweak handling for the final block, so if
    # there is /only/ one block, we just jump straight to that handling.
    cmp	\$0x20,$length
    jl	.L_final_block_is_only_block_${rndsuffix}

    # Otherwise, we reduce length by `to the (nearest multple of 16) - 16`,
    # leaving the final block + any bytes that need cipher stealing and leave
    # those for the special tweak handling.
    mov $length, $decLength
    and \$0xfffffffffffffff0,$decLength
    sub	\$16,$decLength
    cmp 	 \$0x80,$decLength
    jl 	 .L_less_than_128_bytes_${rndsuffix}
    vpbroadcastq 	 $gf_poly_8b,$ZPOLY
    cmp 	 \$0x100,$decLength
    jge 	 .L_start_by16_${rndsuffix}
    cmp 	 \$0x80,$decLength
    jge 	 .L_start_by8_${rndsuffix}

    .L_do_n_blocks_${rndsuffix}:
    cmp	\$0x70,$decLength
    je	.L_remaining_num_blocks_is_7_${rndsuffix}
    cmp	\$0x60,$decLength
    je	.L_remaining_num_blocks_is_6_${rndsuffix}
    cmp	\$0x50,$decLength
    je	.L_remaining_num_blocks_is_5_${rndsuffix}
    cmp	\$0x40,$decLength
    je	.L_remaining_num_blocks_is_4_${rndsuffix}
    cmp	\$0x30,$decLength
    je	.L_remaining_num_blocks_is_3_${rndsuffix}
    cmp	\$0x20,$decLength
    je	.L_remaining_num_blocks_is_2_${rndsuffix}
    cmp	\$0x10,$decLength
    je	.L_remaining_num_blocks_is_1_${rndsuffix}
    and	\$0xf,$length
    je	.L_final_block_${rndsuffix}
    vextracti32x4 	 \$0x0,%zmm9,%xmm0
    vextracti32x4 	 \$0x1,%zmm9,%xmm15
    jmp	.L_steal_cipher_${rndsuffix}

    .L_remaining_num_blocks_is_7_${rndsuffix}:
    mov 	 \$0x0000ffffffffffff,$tmp1
    kmovq 	 $tmp1,%k1
    vmovdqu8 	 ($input),%zmm1
    vmovdqu8 	 0x40($input),%zmm2{%k1}
    add 	 \$0x70,$input
___
    }

    decrypt_by_eight("%zmm1", "%zmm2", "%zmm9", "%zmm10", "%zmm0", 1);

    {
    $code .= <<___;
    vmovdqu8	%zmm1,($output)
    vmovdqu8	%zmm2,0x40($output){%k1}
    add	\$0x70,$output
    vextracti32x4	\$0x3,%zmm10,%xmm0
    and	\$0xf,$length
    je	.L_final_block_${rndsuffix}
    vpsrldq 	 \$0xf,%zmm9,%zmm13
    vpclmulqdq 	 \$0x0,$ZPOLY,%zmm13,%zmm14
    vpslldq 	 \$0x1,%zmm9,%zmm11
    vpxord 	 %zmm14,%zmm11,%zmm11
    vextracti32x4	\$0x0,%zmm11,%xmm15
    jmp	.L_steal_cipher_${rndsuffix}

    .L_remaining_num_blocks_is_6_${rndsuffix}:
    vmovdqu8 	 ($input),%zmm1
    vmovdqu8 	 0x40($input),%ymm2
    add 	 \$0x60,$input
___
    }

    decrypt_by_eight("%zmm1", "%zmm2", "%zmm9", "%zmm10", "%zmm0", 1);

    {
    $code .= <<___;
    vmovdqu8	%zmm1,($output)
    vmovdqu8	%ymm2,0x40($output)
    add	\$0x60,$output
    vextracti32x4	\$0x2,%zmm10,%xmm0
    vextracti32x4	\$0x3,%zmm10,%xmm15
    and	\$0xf,$length
    je	.L_final_block_${rndsuffix}
    jmp	.L_steal_cipher_${rndsuffix}

    .L_remaining_num_blocks_is_5_${rndsuffix}:
    vmovdqu8	($input),%zmm1
    vmovdqu	0x40($input),%xmm2
    add	\$0x50,$input
___
    }

    decrypt_by_eight("%zmm1", "%zmm2", "%zmm9", "%zmm10", "%zmm0", 1);

    {
    $code .= <<___;
    vmovdqu8	%zmm1,($output)
    vmovdqu	%xmm2,0x40($output)
    add	\$0x50,$output
    vextracti32x4	\$0x1,%zmm10,%xmm0
    vextracti32x4	\$0x2,%zmm10,%xmm15
    and	\$0xf,$length
    je	.L_final_block_${rndsuffix}
    jmp	.L_steal_cipher_${rndsuffix}

    .L_remaining_num_blocks_is_4_${rndsuffix}:
    vmovdqu8	($input),%zmm1
    add	\$0x40,$input
___
    }

    decrypt_by_four("%zmm1", "%zmm9", "%zmm0");

    {
    $code .= <<___;
    vmovdqu8	%zmm1,($output)
    add	\$0x40,$output
    vextracti32x4	\$0x0,%zmm10,%xmm0
    vextracti32x4	\$0x1,%zmm10,%xmm15
    and	\$0xf,$length
    je	.L_final_block_${rndsuffix}
    jmp	.L_steal_cipher_${rndsuffix}
___
    }

    {
    $code .= <<___;
    .L_remaining_num_blocks_is_3_${rndsuffix}:
    mov	\$-1, $tmp1
    shr	\$0x10, $tmp1
    kmovq	$tmp1, %k1
    vmovdqu8	($input), %zmm1{%k1}
    add	\$0x30, $input
___
    }

    decrypt_by_four("%zmm1", "%zmm9", "%zmm0");

    {
    $code .= <<___;
    vmovdqu8	%zmm1, ($output){%k1}
    add	\$0x30, $output
    vextracti32x4	\$0x3, %zmm9, %xmm0
    vextracti32x4	\$0x0, %zmm10, %xmm15
    and	\$0xf, $length
    je	.L_final_block_${rndsuffix}
    jmp	.L_steal_cipher_${rndsuffix}
___
    }

    {
    $code .= <<___;
    .L_remaining_num_blocks_is_2_${rndsuffix}:
    vmovdqu8	($input), %ymm1
    add	\$0x20, $input
___
    }

    decrypt_by_four("%ymm1", "%ymm9", "%ymm0");

    {
    $code .= <<___;
    vmovdqu	%ymm1,($output)
    add	\$0x20,$output
    vextracti32x4	\$0x2,%zmm9,%xmm0
    vextracti32x4	\$0x3,%zmm9,%xmm15
    and	\$0xf,$length
    je	.L_final_block_${rndsuffix}
    jmp	.L_steal_cipher_${rndsuffix}
___
    }

    {
    $code .= <<___;
    .L_remaining_num_blocks_is_1_${rndsuffix}:
    vmovdqu	($input),%xmm1
    add	\$0x10,$input
___
    }

    decrypt_final("%xmm1", "%xmm9");

    {
    $code .= <<___;
    vmovdqu	%xmm1,($output)
    add	\$0x10,$output
    vextracti32x4	\$0x1,%zmm9,%xmm0
    vextracti32x4	\$0x2,%zmm9,%xmm15
    and	\$0xf,$length
    je	.L_final_block_${rndsuffix}
    jmp	.L_steal_cipher_${rndsuffix}

    # Setup for and then generation of 16 tweaks.
    .L_start_by16_${rndsuffix}:
    vbroadcasti32x4 	 ($TW),%zmm0
    vbroadcasti32x4 shufb_15_7(%rip),%zmm8
    mov 	 \$0xaa,$tmp1
    kmovq 	 $tmp1,%k2
    vpshufb 	 %zmm8,%zmm0,%zmm1

    # Tweaks 0-3
    vpsllvq const_dq3210(%rip),%zmm0,%zmm4
    vpsrlvq const_dq5678(%rip),%zmm1,%zmm2
    vpclmulqdq 	 \$0x0,$ZPOLY,%zmm2,%zmm3
    vpxorq 	 %zmm2,%zmm4,%zmm4{%k2}
    vpxord 	 %zmm4,%zmm3,%zmm9

    # Tweaks 4-7
    vpsllvq const_dq7654(%rip),%zmm0,%zmm5
    vpsrlvq const_dq1234(%rip),%zmm1,%zmm6
    vpclmulqdq 	 \$0x0,$ZPOLY,%zmm6,%zmm7
    vpxorq 	 %zmm6,%zmm5,%zmm5{%k2}
    vpxord 	 %zmm5,%zmm7,%zmm10

    # Tweaks 8-11
    vpsrldq 	 \$0xf,%zmm9,%zmm13
    vpclmulqdq 	 \$0x0,$ZPOLY,%zmm13,%zmm14
    vpslldq 	 \$0x1,%zmm9,%zmm11
    vpxord 	 %zmm14,%zmm11,%zmm11

    # Tweaks 12-15
    vpsrldq 	 \$0xf,%zmm10,%zmm15
    vpclmulqdq 	 \$0x0,$ZPOLY,%zmm15,%zmm16
    vpslldq 	 \$0x1,%zmm10,%zmm12
    vpxord 	 %zmm16,%zmm12,%zmm12

    .L_main_loop_run_16_${rndsuffix}:
    vmovdqu8 	 ($input),%zmm1
    vmovdqu8 	 0x40($input),%zmm2
    vmovdqu8 	 0x80($input),%zmm3
    vmovdqu8 	 0xc0($input),%zmm4
    add 	 \$0x100,$input
___
    }

    decrypt_by_16("%zmm1", "%zmm2", "%zmm3", "%zmm4", "%zmm9",
                  "%zmm10", "%zmm11", "%zmm12", "%zmm0", 0);

    {
    $code .= <<___;
    vmovdqu8 	 %zmm1,($output)
    vmovdqu8 	 %zmm2,0x40($output)
    vmovdqu8 	 %zmm3,0x80($output)
    vmovdqu8 	 %zmm4,0xc0($output)
    add 	 \$0x100,$output
    sub 	 \$0x100,$decLength
    cmp 	 \$0x100,$decLength
    jae 	 .L_main_loop_run_16_${rndsuffix}
    cmp 	 \$0x80,$decLength
    jae 	 .L_main_loop_run_8_${rndsuffix}
    jmp 	 .L_do_n_blocks_${rndsuffix}

    .L_start_by8_${rndsuffix}:
    vbroadcasti32x4 	 ($TW),%zmm0
    vbroadcasti32x4 shufb_15_7(%rip),%zmm8
    mov 	 \$0xaa,$tmp1
    kmovq 	 $tmp1,%k2
    vpshufb 	 %zmm8,%zmm0,%zmm1
    vpsllvq const_dq3210(%rip),%zmm0,%zmm4
    vpsrlvq const_dq5678(%rip),%zmm1,%zmm2
    vpclmulqdq 	 \$0x0,%zmm25,%zmm2,%zmm3
    vpxorq 	 %zmm2,%zmm4,%zmm4{%k2}
    vpxord 	 %zmm4,%zmm3,%zmm9
    vpsllvq const_dq7654(%rip),%zmm0,%zmm5
    vpsrlvq const_dq1234(%rip),%zmm1,%zmm6
    vpclmulqdq 	 \$0x0,%zmm25,%zmm6,%zmm7
    vpxorq 	 %zmm6,%zmm5,%zmm5{%k2}
    vpxord 	 %zmm5,%zmm7,%zmm10

    .L_main_loop_run_8_${rndsuffix}:
    vmovdqu8 	 ($input),%zmm1
    vmovdqu8 	 0x40($input),%zmm2
    add 	 \$0x80,$input
___
    }

    decrypt_by_eight("%zmm1", "%zmm2", "%zmm9", "%zmm10", "%zmm0", 0);

    {
    $code .= <<___;
    vmovdqu8 	 %zmm1,($output)
    vmovdqu8 	 %zmm2,0x40($output)
    add 	 \$0x80,$output
    sub 	 \$0x80,$decLength
    cmp 	 \$0x80,$decLength
    jae 	 .L_main_loop_run_8_${rndsuffix}
    vextracti32x4 	 \$0x0,%zmm9,%xmm0
    vextracti32x4 	 \$0x1,%zmm9,%xmm15
    jmp 	 .L_do_n_blocks_${rndsuffix}

    .L_steal_cipher_with_tweak_${rndsuffix}:
    # %xmm0 holds tweak, %xmm15 holds tweak'
    vmovdqa	shufb_15_7(%rip),%xmm11
    vpshufb 	 %xmm11,%xmm0,%xmm12
    vpsllq	\$0x1,%xmm0,%xmm13
    vpsrlq \$0x7,%xmm12,%xmm14
    vpclmulqdq 	 \$0x0,%xmm25,%xmm14,%xmm15 # just the first lane of ZPOLY
    vpxord 	 %xmm13,%xmm15,%xmm15

    .L_steal_cipher_${rndsuffix}:
    # 1. Decrypt the final complete block with tweak', result is held in xmm8.
    vmovdqu	($input), %xmm8
    vpxor	%xmm15,%xmm8,%xmm8
    vpxor	($key1),%xmm8,%xmm8
    vaesdec	0x10($key1),%xmm8,%xmm8
    vaesdec	0x20($key1),%xmm8,%xmm8
    vaesdec	0x30($key1),%xmm8,%xmm8
    vaesdec	0x40($key1),%xmm8,%xmm8
    vaesdec	0x50($key1),%xmm8,%xmm8
    vaesdec	0x60($key1),%xmm8,%xmm8
    vaesdec	0x70($key1),%xmm8,%xmm8
    vaesdec	0x80($key1),%xmm8,%xmm8
    vaesdec	0x90($key1),%xmm8,%xmm8
    vaesdec	0xa0($key1),%xmm8,%xmm8
    vaesdec	0xb0($key1),%xmm8,%xmm8
    vaesdec	0xc0($key1),%xmm8,%xmm8
    vaesdec	0xd0($key1),%xmm8,%xmm8
    vaesdeclast	0xe0($key1),%xmm8,%xmm8
    vpxor %xmm15,%xmm8,%xmm8

    # 2. Take the n (s.t. n < 16) leftover bytes from the cipher text and
    # replace the front n bytes of the decrypted block from step 1, held in
    # xmm9.
    mov	\$1,%r11
    mov	$key1,$tmp1
    mov	$length,$key1 # shl's shift op has to be in %cl.
    shlq	%cl,%r11
    sub	\$1,%r11
    kmovq	%r11,%k1
	vmovdqu8	0x10($input),%xmm9{%k1}{z}
	vmovdqu8	%xmm8,%xmm10{%k1}{z} # save front n bytes to append later
    vpblendmb	%xmm9,%xmm8,%xmm9{%k1}

    # 3. Run decrypt on that block again, with tweak.
    mov	$tmp1,$key1 # put the pointer to the keys back into %rcx
    vpxor	%xmm0,%xmm9,%xmm9
    vpxor	($key1),%xmm9,%xmm9
    vaesdec	0x10($key1),%xmm9,%xmm9
    vaesdec	0x20($key1),%xmm9,%xmm9
    vaesdec	0x30($key1),%xmm9,%xmm9
    vaesdec	0x40($key1),%xmm9,%xmm9
    vaesdec	0x50($key1),%xmm9,%xmm9
    vaesdec	0x60($key1),%xmm9,%xmm9
    vaesdec	0x70($key1),%xmm9,%xmm9
    vaesdec	0x80($key1),%xmm9,%xmm9
    vaesdec	0x90($key1),%xmm9,%xmm9
    vaesdec	0xa0($key1),%xmm9,%xmm9
    vaesdec	0xb0($key1),%xmm9,%xmm9
    vaesdec	0xc0($key1),%xmm9,%xmm9
    vaesdec	0xd0($key1),%xmm9,%xmm9
    vaesdeclast	0xe0($key1),%xmm9,%xmm9
    vpxor %xmm0,%xmm9,%xmm9

    # 4. Final output is that block, + the original front n bytes from the last
    # complete block.
	vmovdqu	%xmm9,($output)
	vmovdqu8	%xmm10,0x10($output){%k1}
    jmp	.L_ret_${rndsuffix}

    .L_final_block_is_only_block_${rndsuffix}:
    vmovdqa	($TW),%xmm0
    and	\$0xf,$length
    jne	.L_steal_cipher_with_tweak_${rndsuffix}

    .L_final_block_${rndsuffix}:
    vmovdqa	($input), %xmm8
    vpxor	%xmm0,%xmm8,%xmm8
    vpxor	($key1),%xmm8,%xmm8
    vaesdec	0x10($key1),%xmm8,%xmm8
    vaesdec	0x20($key1),%xmm8,%xmm8
    vaesdec	0x30($key1),%xmm8,%xmm8
    vaesdec	0x40($key1),%xmm8,%xmm8
    vaesdec	0x50($key1),%xmm8,%xmm8
    vaesdec	0x60($key1),%xmm8,%xmm8
    vaesdec	0x70($key1),%xmm8,%xmm8
    vaesdec	0x80($key1),%xmm8,%xmm8
    vaesdec	0x90($key1),%xmm8,%xmm8
    vaesdec	0xa0($key1),%xmm8,%xmm8
    vaesdec	0xb0($key1),%xmm8,%xmm8
    vaesdec	0xc0($key1),%xmm8,%xmm8
    vaesdec	0xd0($key1),%xmm8,%xmm8
    vaesdeclast	0xe0($key1),%xmm8,%xmm8
    vpxor %xmm0,%xmm8,%xmm8
	vmovdqa %xmm8,($output)

    .L_ret_${rndsuffix}:
    mov 	 $GP_STORAGE($TW),%rbx
    xor    $tmp1,$tmp1
    mov    $tmp1,$GP_STORAGE($TW)
    vpxorq %zmm0,%zmm0,%zmm0
___
    }

    if ($win64) {
      $code .= <<___;
      mov $GP_STORAGE + 8*1($TW),%rdi
      mov $tmp1,$GP_STORAGE + 8*1($TW)
      mov $GP_STORAGE + 8*2($TW),%rsi
      mov $tmp1,$GP_STORAGE + 8*2($TW)

      vmovdqa $XMM_STORAGE + 16 * 0($TW), %xmm6
      vmovdqa $XMM_STORAGE + 16 * 1($TW), %xmm7
      vmovdqa $XMM_STORAGE + 16 * 2($TW), %xmm8
      vmovdqa $XMM_STORAGE + 16 * 3($TW), %xmm9

      # Zero the 64 bytes we just restored to the xmm registers.
      vmovdqa64 %zmm0,$XMM_STORAGE($TW)

      vmovdqa $XMM_STORAGE + 16 * 4($TW), %xmm10
      vmovdqa $XMM_STORAGE + 16 * 5($TW), %xmm11
      vmovdqa $XMM_STORAGE + 16 * 6($TW), %xmm12
      vmovdqa $XMM_STORAGE + 16 * 7($TW), %xmm13

      # And again.
      vmovdqa64 %zmm0,$XMM_STORAGE + 16 * 4($TW)

      vmovdqa $XMM_STORAGE + 16 * 8($TW), %xmm14
      vmovdqa $XMM_STORAGE + 16 * 9($TW), %xmm15

      # Last round is only 32 bytes (256-bits), so we use `%ymm` as the
      # source operand.
      vmovdqa %ymm0,$XMM_STORAGE + 16 * 8($TW)
___
    }

    {
    $code .= <<___;
    mov %rbp,$TW
    pop %rbp
    vzeroupper
    ret

    .L_less_than_128_bytes_${rndsuffix}:
    vpbroadcastq	$gf_poly_8b, $ZPOLY
    cmp 	 \$0x10,$decLength
    jb 	 .L_ret_${rndsuffix}
    vbroadcasti32x4	($TW), %zmm0
    vbroadcasti32x4	shufb_15_7(%rip), %zmm8
    movl    \$0xaa, %r8d
    kmovq	%r8, %k2
    mov	$decLength,$tmp1
    and	\$0x70,$tmp1
    cmp	\$0x60,$tmp1
    je	.L_num_blocks_is_6_${rndsuffix}
    cmp	\$0x50,$tmp1
    je	.L_num_blocks_is_5_${rndsuffix}
    cmp	\$0x40,$tmp1
    je	.L_num_blocks_is_4_${rndsuffix}
    cmp	\$0x30,$tmp1
    je	.L_num_blocks_is_3_${rndsuffix}
    cmp	\$0x20,$tmp1
    je	.L_num_blocks_is_2_${rndsuffix}
    cmp	\$0x10,$tmp1
    je	.L_num_blocks_is_1_${rndsuffix}

    .L_num_blocks_is_7_${rndsuffix}:
    vpshufb	%zmm8, %zmm0, %zmm1
    vpsllvq	const_dq3210(%rip), %zmm0, %zmm4
    vpsrlvq	const_dq5678(%rip), %zmm1, %zmm2
    vpclmulqdq	\$0x00, $ZPOLY, %zmm2, %zmm3
    vpxorq	%zmm2, %zmm4, %zmm4{%k2}
    vpxord	%zmm4, %zmm3, %zmm9
    vpsllvq	const_dq7654(%rip), %zmm0, %zmm5
    vpsrlvq	const_dq1234(%rip), %zmm1, %zmm6
    vpclmulqdq	\$0x00, $ZPOLY, %zmm6, %zmm7
    vpxorq	%zmm6, %zmm5, %zmm5{%k2}
    vpxord	%zmm5, %zmm7, %zmm10
    mov	\$0x0000ffffffffffff, $tmp1
    kmovq	$tmp1, %k1
    vmovdqu8	16*0($input), %zmm1
    vmovdqu8	16*4($input), %zmm2{%k1}

    add	\$0x70,$input
___
    }

    decrypt_by_eight("%zmm1", "%zmm2", "%zmm9", "%zmm10", "%zmm0", 1);

    {
    $code .= <<___;
    vmovdqu8	%zmm1, 16*0($output)
    vmovdqu8	%zmm2, 16*4($output){%k1}
    add	\$0x70,$output

    vextracti32x4	\$0x3, %zmm10, %xmm0

    and	\$0xf,$length
    je	.L_final_block_${rndsuffix}

    vpsrldq 	 \$0xf,%zmm9,%zmm13
    vpclmulqdq 	 \$0x0,$ZPOLY,%zmm13,%zmm14
    vpslldq 	 \$0x1,%zmm9,%zmm11
    vpxord 	 %zmm14,%zmm11,%zmm11
    vextracti32x4	\$0x0, %zmm11, %xmm15
    jmp	.L_steal_cipher_${rndsuffix}
___
    }

    {
    $code .= <<___;
    .L_num_blocks_is_6_${rndsuffix}:
    vpshufb	%zmm8, %zmm0, %zmm1
    vpsllvq	const_dq3210(%rip), %zmm0, %zmm4
    vpsrlvq	const_dq5678(%rip), %zmm1, %zmm2
    vpclmulqdq	\$0x00, $ZPOLY, %zmm2, %zmm3
    vpxorq	%zmm2, %zmm4, %zmm4{%k2}
    vpxord	%zmm4, %zmm3, %zmm9
    vpsllvq	const_dq7654(%rip), %zmm0, %zmm5
    vpsrlvq	const_dq1234(%rip), %zmm1, %zmm6
    vpclmulqdq	\$0x00, $ZPOLY, %zmm6, %zmm7
    vpxorq	%zmm6, %zmm5, %zmm5{%k2}
    vpxord	%zmm5, %zmm7, %zmm10
    vmovdqu8	16*0($input), %zmm1
    vmovdqu8	16*4($input), %ymm2
    add	\$96, $input
___
    }

    decrypt_by_eight("%zmm1", "%zmm2", "%zmm9", "%zmm10", "%zmm0", 1);

    {
    $code .= <<___;
    vmovdqu8	%zmm1, 16*0($output)
    vmovdqu8	%ymm2, 16*4($output)
    add	\$96, $output

    vextracti32x4	\$0x2, %zmm10, %xmm0
    vextracti32x4	\$0x3, %zmm10, %xmm15
    and	\$0xf,$length
    je	.L_final_block_${rndsuffix}
    jmp	.L_steal_cipher_${rndsuffix}
___
    }

    {
    $code .= <<___;
    .L_num_blocks_is_5_${rndsuffix}:
    vpshufb	%zmm8, %zmm0, %zmm1
    vpsllvq	const_dq3210(%rip), %zmm0, %zmm4
    vpsrlvq	const_dq5678(%rip), %zmm1, %zmm2
    vpclmulqdq	\$0x00, $ZPOLY, %zmm2, %zmm3
    vpxorq	%zmm2, %zmm4, %zmm4{%k2}
    vpxord	%zmm4, %zmm3, %zmm9
    vpsllvq	const_dq7654(%rip), %zmm0, %zmm5
    vpsrlvq	const_dq1234(%rip), %zmm1, %zmm6
    vpclmulqdq	\$0x00, $ZPOLY, %zmm6, %zmm7
    vpxorq	%zmm6, %zmm5, %zmm5{%k2}
    vpxord	%zmm5, %zmm7, %zmm10
    vmovdqu8	16*0($input), %zmm1
    vmovdqu8	16*4($input), %xmm2
    add	\$80, $input
___
    }

    decrypt_by_eight("%zmm1", "%zmm2", "%zmm9", "%zmm10", "%zmm0", 1);

    {
    $code .= <<___;
    vmovdqu8	%zmm1, 16*0($output)
    vmovdqu8	%xmm2, 16*4($output)
    add	\$80, $output

    vmovdqa	%xmm2, %xmm8
    vextracti32x4	\$0x1, %zmm10, %xmm0
    vextracti32x4	\$0x2, %zmm10, %xmm15
    and	\$0xf,$length
    je	.L_final_block_${rndsuffix}
    jmp	.L_steal_cipher_${rndsuffix}
___
    }

    {
    $code .= <<___;
    .L_num_blocks_is_4_${rndsuffix}:
    vpshufb	%zmm8, %zmm0, %zmm1
    vpsllvq	const_dq3210(%rip), %zmm0, %zmm4
    vpsrlvq	const_dq5678(%rip), %zmm1, %zmm2
    vpclmulqdq	\$0x00, $ZPOLY, %zmm2, %zmm3
    vpxorq	%zmm2, %zmm4, %zmm4{%k2}
    vpxord	%zmm4, %zmm3, %zmm9
    vpsllvq	const_dq7654(%rip), %zmm0, %zmm5
    vpsrlvq	const_dq1234(%rip), %zmm1, %zmm6
    vpclmulqdq	\$0x00, $ZPOLY, %zmm6, %zmm7
    vpxorq	%zmm6, %zmm5, %zmm5{%k2}
    vpxord	%zmm5, %zmm7, %zmm10
    vmovdqu8	16*0($input), %zmm1
    add	\$64, $input
___
    }

    decrypt_by_four("%zmm1", "%zmm9", "%zmm0");

    {
    $code .= <<___;
    vmovdqu8	%zmm1, 16*0($output)
    add	\$64, $output
    vmovdqa	%xmm10, %xmm0
    vextracti32x4	\$0x1, %zmm10, %xmm15
    and	\$0xf,$length
    je	.L_final_block_${rndsuffix}
    jmp	.L_steal_cipher_${rndsuffix}
___
    }

    {
    $code .= <<___;
    .L_num_blocks_is_3_${rndsuffix}:
    vpshufb	%zmm8, %zmm0, %zmm1
    vpsllvq	const_dq3210(%rip), %zmm0, %zmm4
    vpsrlvq	const_dq5678(%rip), %zmm1, %zmm2
    vpclmulqdq	\$0x00, $ZPOLY, %zmm2, %zmm3
    vpxorq	%zmm2, %zmm4, %zmm4{%k2}
    vpxord	%zmm4, %zmm3, %zmm9
    vpsllvq	const_dq7654(%rip), %zmm0, %zmm5
    vpsrlvq	const_dq1234(%rip), %zmm1, %zmm6
    vpclmulqdq	\$0x00, $ZPOLY, %zmm6, %zmm7
    vpxorq	%zmm6, %zmm5, %zmm5{%k2}
    vpxord	%zmm5, %zmm7, %zmm10
    mov	\$0x0000ffffffffffff, $tmp1
    kmovq	$tmp1, %k1
    vmovdqu8	16*0($input), %zmm1{%k1}
    add	\$48, $input
___
    }

    decrypt_by_four("%zmm1", "%zmm9", "%zmm0");

    {
    $code .= <<___;
    vmovdqu8	%zmm1, 16*0($output){%k1}
    add	\$48, $output
    vextracti32x4	\$3, %zmm9, %xmm0
    vextracti32x4	\$0, %zmm10, %xmm15
    and	\$0xf,$length
    je	.L_final_block_${rndsuffix}
    jmp	.L_steal_cipher_${rndsuffix}
___
    }

    {
    $code .= <<___;
    .L_num_blocks_is_2_${rndsuffix}:
    vpshufb	%zmm8, %zmm0, %zmm1
    vpsllvq	const_dq3210(%rip), %zmm0, %zmm4
    vpsrlvq	const_dq5678(%rip), %zmm1, %zmm2
    vpclmulqdq	\$0x00, $ZPOLY, %zmm2, %zmm3
    vpxorq	%zmm2, %zmm4, %zmm4{%k2}
    vpxord	%zmm4, %zmm3, %zmm9

    vmovdqu8	16*0($input), %ymm1
    add	\$32, $input
___
    }

    decrypt_by_four("%ymm1", "%ymm9", "%ymm0");

    {
    $code .= <<___;
    vmovdqu8	%ymm1, 16*0($output)
    add	\$32, $output

    vextracti32x4	\$2, %zmm9, %xmm0
    vextracti32x4	\$3, %zmm9, %xmm15
    and	\$0xf,$length
    je	.L_final_block_${rndsuffix}
    jmp	.L_steal_cipher_${rndsuffix}
___
    }

    {
    $code .= <<___;
    .L_num_blocks_is_1_${rndsuffix}:
    vpshufb	%zmm8, %zmm0, %zmm1
    vpsllvq	const_dq3210(%rip), %zmm0, %zmm4
    vpsrlvq	const_dq5678(%rip), %zmm1, %zmm2
    vpclmulqdq	\$0x00, $ZPOLY, %zmm2, %zmm3
    vpxorq	%zmm2, %zmm4, %zmm4{%k2}
    vpxord	%zmm4, %zmm3, %zmm9

    vmovdqu8	16*0($input), %xmm1
    add	\$16, $input
___
    }

    decrypt_by_four("%ymm1", "%ymm9", "%ymm0");

    {
    $code .= <<___;
    vmovdqu8	%xmm1, 16*0($output)
    add	\$16, $output

    vmovdqa	%xmm1, %xmm8
    vextracti32x4	\$1, %zmm9, %xmm0
    vextracti32x4	\$2, %zmm9, %xmm15
    and	\$0xf,$length
    je	.L_final_block_${rndsuffix}
    jmp	.L_steal_cipher_${rndsuffix}
    .cfi_endproc
___
    }
  }

  enc();
  dec();

  $code .= <<___;
  .section .rodata
  .align 16

  vpshufb_shf_table:
    .quad 0x8786858483828100, 0x8f8e8d8c8b8a8988
    .quad 0x0706050403020100, 0x000e0d0c0b0a0908

  mask1:
    .quad 0x8080808080808080, 0x8080808080808080

  const_dq3210:
    .quad 0, 0, 1, 1, 2, 2, 3, 3
  const_dq5678:
    .quad 8, 8, 7, 7, 6, 6, 5, 5
  const_dq7654:
    .quad 4, 4, 5, 5, 6, 6, 7, 7
  const_dq1234:
    .quad 4, 4, 3, 3, 2, 2, 1, 1

  shufb_15_7:
    .byte  15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 7, 0xff, 0xff
    .byte  0xff, 0xff, 0xff, 0xff, 0xff

.text
___

} else {
    $code .= <<___;
    .text
    .globl  aes_hw_xts_encrypt_avx512
    .globl  aes_hw_xts_decrypt_avx512

    aes_hw_xts_encrypt_avx512:
    aes_hw_xts_decrypt_avx512:
    .byte   0x0f,0x0b    # ud2
    ret
___
}

# Bits 7 & 4 contain the src1 register's MSB in inverted form
# Bits 6 & 5 contian the dst register's MSB in inverted form
# Bits 1 & 0 is fixed to 10 for vaesenc* instrcutions and 11
# for vpclmulqdq instruction
sub evex_byte1 {
  my ($mm, $src1, $dst) = @_;
  # set default to zero
  $src1 = 0 if (!defined($src1));
  $dst = 0 if (!defined($dst));

  my $byte = 0xf0 | $mm;

  if (($src1 & 0x8) > 0) {
      $byte = $byte & 0x7f;
  }
  if (($src1 & 0x10) > 0) {
      $byte = $byte & 0xef;
  }

  if (($dst & 0x8) > 0) {
      $byte = $byte & 0xdf;
  }
  if (($dst & 0x10) > 0) {
      $byte = $byte & 0xbf;
  }
  return $byte;
}

# Bits 6->3 contians the lower 4 bits of src2 register in inverted form
# Bits 0->2 is fixed to 101
sub evex_byte2 {
  my $src2 = shift;
  $src2 = ($src2 & 0x0f) ^ 0x0f;
  return (($src2 << 3) | 0x05);
}

# Bits 6 & 5 tells about the operand register types and bit 3 contains
# the src2 register's MSB in inverted form
sub evex_byte3 {
  my ($type, $src2) = @_;
  my $byte = 0x0; # default for xmm registers
  if ($type eq 'y') {
	$byte = 0x01;
  } elsif ($type eq 'z') {
	$byte = 0x02;
  }

  $byte = $byte << 5;

  if (!($src2 & 0x10)) {
      $byte = $byte | 0x08;
  }
  return $byte;
}

sub vpclmulqdq {
  my $line = shift;
  my @opcode = (0x62);
  my $inst_type = 0x03; #vpclmulqdq
  my %opcodelet = (
     "vpclmulqdq" => 0x44,
  );
  if ($line=~/(vpclmul[a-z]+)\s+\$0x([0-9]+),\s*%([xyz])mm([0-9]+),\s*%[xyz]mm([0-9]+),\s*%[xyz]mm([0-9]+)/) {
        return undef if (!defined($opcodelet{$1}));
        my $byte1 = evex_byte1($inst_type, $6, $4);
        my $byte2 = evex_byte2($5);
        my $byte3 = evex_byte3($3, $5);
        my $modrm = 0xc0 | (($4 & 7) | (($6 & 7) << 3));
	push @opcode,$byte1,$byte2,$byte3;
	push @opcode,($opcodelet{$1});
	push @opcode,$modrm;
	push @opcode,hex($2);
        return ".byte\t".join(',',@opcode);
  }
  return $line;
}

sub vaesni {
  my $line = shift;
  my @opcode = (0x62);
  my $inst_type = 0x02; # vaesenc
  my $byte1, $byte2, $byte3;
  my %opcodelet = (
     "vaesenc" => 0xdc, "vaesdec" => 0xde,
     "vaesenclast" => 0xdd, "vaesdeclast" => 0xdf,
  );
  if ($line=~/(vaes[a-z]+)\s+%([xyz])mm([0-9]+),\s*%[xyz]mm([0-9]+),\s*%[xyz]mm([0-9]*)/) {
        return undef if (!defined($opcodelet{$1}));
        $byte1 = evex_byte1($inst_type, $5, $3);
        $byte2 = evex_byte2($4);
        $byte3 = evex_byte3($2, $4);
        my $modrm = 0xc0 | ((($5 & 7) << 3) | ($3 & 7));
	push @opcode,$byte1,$byte2,$byte3;
	push @opcode,($opcodelet{$1});
	push @opcode,$modrm;
        return ".byte\t".join(',',@opcode);
  } elsif ($line=~/(vaes[a-z]+)\s+0x([a-f,0-9]+)\(%rsp\),\s*%([xyz])mm([0-9]+),\s*%[xyz]mm([0-9]+)/) {
        return undef if (!defined($opcodelet{$1}));
        $byte1 = evex_byte1($inst_type,$5);
        $byte2 = evex_byte2($5);
        $byte3 = evex_byte3($3, $5);
        push @opcode,$byte1,$byte2,$byte3;
        push @opcode,($opcodelet{$1});
        my $rsp = 0x04;
        my $modrm = 0x80 | ((($5 & 7) << 3) | $rsp);
        push @opcode,$modrm;
        push @opcode,0x24;
        push @opcode, (hex($2) & 0xFF), ((hex($2) >> 8) & 0xFF);
        push @opcode, ((hex($2) >> 16) & 0xFF), ((hex($2) >> 24) & 0xFF);
        return ".byte\t".join(',',@opcode);
  }
  return $line;
}

$code =~ s/\`([^\`]*)\`/eval($1)/gem;
$code =~ s/\b(vpclmul.*).*$/vpclmulqdq($1)/gem;
$code =~ s/\b(vaesenc.*).*$/vaesni($1)/gem;
$code =~ s/\b(vaesdec.*).*$/vaesni($1)/gem;

print $code;

close STDOUT or die "error closing STDOUT: $!";
