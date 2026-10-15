#! /usr/bin/env perl
# Copyright (C) 2025 Intel Corporation

if ($#ARGV < 1) { die "Not enough arguments provided.
  Two arguments are necessary: the flavour and the output file path."; }

$flavour = shift;
$output  = shift;

$win64=0; $win64=1 if ($flavour =~ /[nm]asm|mingw64/ || $output =~ /\.asm$/);

$avx512md5 = 1;
for (@ARGV) { $avx512md5 = 0 if (/-DMY_ASSEMBLER_IS_TOO_OLD_FOR_512AVX/); }

$0 =~ m/(.*[\/\\])[^\/\\]+$/; $dir=$1;
( $xlate="${dir}x86_64-xlate.pl" and -f $xlate ) or
( $xlate="${dir}../../../perlasm/x86_64-xlate.pl" and -f $xlate) or
die "can't locate x86_64-xlate.pl";

open OUT,"| \"$^X\" \"$xlate\" $flavour \"$output\"";
*STDOUT=*OUT;

#======================================================================

if ($avx512md5) {

  my $XMM_STORAGE = 16 * 5;

  my $state = "%rdi";
  my $data = "%rsi";
  my $num = "%rdx";

  my $a = "%xmm1";
  my $b = "%xmm2";
  my $c = "%xmm3";
  my $d = "%xmm4";

  my $pa = "%xmm5";
  my $pb = "%xmm6";
  my $pc = "%xmm7";
  my $pd = "%xmm8";

  sub md5_step {
    my ($src, $a, $b, $c, $d, $off, $rot, $t, $imm8) = @_;

    # TODO(pittma): At the cost of another register, we can add t and k
    # together, and then combine results which may get us better ILP.
    $code .= <<___;
    vmovd	.L_T+4*$t(%rip), %xmm10
    vpaddd	$off*4($src), %xmm10, %xmm10  # T[i] + k[i]
    vpaddd	$a, %xmm10, %xmm10            # T[i] + k[i] + a
    vmovdqa	$b, %xmm9                     # preserve b
    vpternlogd	$imm8, $d, $c, %xmm9      # f(b, c, d)
    vpaddd	%xmm9, %xmm10, %xmm9          # (T[i] + k[i]) + (f(b, c, d) + a)
    vprold	\$$rot, %xmm9, %xmm9          # tmp <<< s
    vpaddd	$b, %xmm9, $a                 # b + (tmp <<< s)
___
  }

  sub round1_op {
    my ($src, $a, $b, $c, $d, $off, $rot, $t) = @_;

    md5_step($src, $a, $b, $c, $d, $off, $rot, $t, "\$0xca");
  }

  sub round2_op {
    my ($src, $a, $b, $c, $d, $off, $rot, $t) = @_;

    md5_step($src, $a, $b, $c, $d, $off, $rot, $t, "\$0xe4");
  }

  sub round3_op {
    my ($src, $a, $b, $c, $d, $off, $rot, $t) = @_;

    md5_step($src, $a, $b, $c, $d, $off, $rot, $t, "\$0x96");
  }

  sub round4_op {
    my ($src, $a, $b, $c, $d, $off, $rot, $t) = @_;

    md5_step($src, $a, $b, $c, $d, $off, $rot, $t, "\$0x39");
  }

  sub one_round {
   my ($src) = @_;

    $code .= <<___;
    vmovdqa	$a, $pa
    vmovdqa	$b, $pb
    vmovdqa	$c, $pc
    vmovdqa	$d, $pd
___

    # Round 1
    # [ABCD  0  7  1]  [DABC  1 12  2]  [CDAB  2 17  3]  [BCDA  3 22  4]
    round1_op($src, $a, $b, $c, $d, 0, 7,  0);
    round1_op($src, $d, $a, $b, $c, 1, 12, 1);
    round1_op($src, $c, $d, $a, $b, 2, 17, 2);
    round1_op($src, $b, $c, $d, $a, 3, 22, 3);

    # [ABCD  4  7  5]  [DABC  5 12  6]  [CDAB  6 17  7]  [BCDA  7 22  8]
    round1_op($src, $a, $b, $c, $d, 4, 7, 4);
    round1_op($src, $d, $a, $b, $c, 5, 12, 5);
    round1_op($src, $c, $d, $a, $b, 6, 17, 6);
    round1_op($src, $b, $c, $d, $a, 7, 22, 7);

    # [ABCD  8  7  9]  [DABC  9 12 10]  [CDAB 10 17 11]  [BCDA 11 22 12]
    round1_op($src, $a, $b, $c, $d, 8, 7, 8);
    round1_op($src, $d, $a, $b, $c, 9, 12, 9);
    round1_op($src, $c, $d, $a, $b, 10, 17, 10);
    round1_op($src, $b, $c, $d, $a, 11, 22, 11);

    # [ABCD 12  7 13]  [DABC 13 12 14]  [CDAB 14 17 15]  [BCDA 15 22 16]
    round1_op($src, $a, $b, $c, $d, 12, 7, 12);
    round1_op($src, $d, $a, $b, $c, 13, 12, 13);
    round1_op($src, $c, $d, $a, $b, 14, 17, 14);
    round1_op($src, $b, $c, $d, $a, 15, 22, 15);

    # Round 2
    # [ABCD  1  5 17]  [DABC  6  9 18]  [CDAB 11 14 19]  [BCDA  0 20 20]
    round2_op($src, $a, $b, $c, $d, 1, 5, 16);
    round2_op($src, $d, $a, $b, $c, 6, 9, 17);
    round2_op($src, $c, $d, $a, $b, 11, 14, 18);
    round2_op($src, $b, $c, $d, $a, 0, 20, 19);

    # [ABCD  5  5 21]  [DABC 10  9 22]  [CDAB 15 14 23]  [BCDA  4 20 24]
    round2_op($src, $a, $b, $c, $d, 5, 5, 20);
    round2_op($src, $d, $a, $b, $c, 10, 9, 21);
    round2_op($src, $c, $d, $a, $b, 15, 14, 22);
    round2_op($src, $b, $c, $d, $a, 4, 20, 23);

    # [ABCD  9  5 25]  [DABC 14  9 26]  [CDAB  3 14 27]  [BCDA  8 20 28]
    round2_op($src, $a, $b, $c, $d, 9, 5, 24);
    round2_op($src, $d, $a, $b, $c, 14, 9, 25);
    round2_op($src, $c, $d, $a, $b, 3, 14, 26);
    round2_op($src, $b, $c, $d, $a, 8, 20, 27);

    # [ABCD 13  5 29]  [DABC  2  9 30]  [CDAB  7 14 31]  [BCDA 12 20 32]
    round2_op($src, $a, $b, $c, $d, 13, 5, 28);
    round2_op($src, $d, $a, $b, $c, 2, 9, 29);
    round2_op($src, $c, $d, $a, $b, 7, 14, 30);
    round2_op($src, $b, $c, $d, $a, 12, 20, 31);

    # Round 3
    # [ABCD  5  4 33]  [DABC  8 11 34]  [CDAB 11 16 35]  [BCDA 14 23 36]
    round3_op($src, $a, $b, $c, $d, 5, 4, 32);
    round3_op($src, $d, $a, $b, $c, 8, 11, 33);
    round3_op($src, $c, $d, $a, $b, 11, 16, 34);
    round3_op($src, $b, $c, $d, $a, 14, 23, 35);

    # [ABCD  1  4 37]  [DABC  4 11 38]  [CDAB  7 16 39]  [BCDA 10 23 40]
    round3_op($src, $a, $b, $c, $d, 1, 4, 36);
    round3_op($src, $d, $a, $b, $c, 4, 11, 37);
    round3_op($src, $c, $d, $a, $b, 7, 16, 38);
    round3_op($src, $b, $c, $d, $a, 10, 23, 39);

    # [ABCD 13  4 41]  [DABC  0 11 42]  [CDAB  3 16 43]  [BCDA  6 23 44]
    round3_op($src, $a, $b, $c, $d, 13, 4, 40);
    round3_op($src, $d, $a, $b, $c, 0, 11, 41);
    round3_op($src, $c, $d, $a, $b, 3, 16, 42);
    round3_op($src, $b, $c, $d, $a, 6, 23, 43);

    # [ABCD  9  4 45]  [DABC 12 11 46]  [CDAB 15 16 47]  [BCDA  2 23 48]
    round3_op($src, $a, $b, $c, $d, 9, 4, 44);
    round3_op($src, $d, $a, $b, $c, 12, 11, 45);
    round3_op($src, $c, $d, $a, $b, 15, 16, 46);
    round3_op($src, $b, $c, $d, $a, 2, 23, 47);

    # Round 4
    # [ABCD  0  6 49]  [DABC  7 10 50]  [CDAB 14 15 51]  [BCDA  5 21 52]
    round4_op($src, $a, $b, $c, $d, 0, 6, 48);
    round4_op($src, $d, $a, $b, $c, 7, 10, 49);
    round4_op($src, $c, $d, $a, $b, 14, 15, 50);
    round4_op($src, $b, $c, $d, $a, 5, 21, 51);

    # [ABCD 12  6 53]  [DABC  3 10 54]  [CDAB 10 15 55]  [BCDA  1 21 56]
    round4_op($src, $a, $b, $c, $d, 12, 6, 52);
    round4_op($src, $d, $a, $b, $c, 3, 10, 53);
    round4_op($src, $c, $d, $a, $b, 10, 15, 54);
    round4_op($src, $b, $c, $d, $a, 1, 21, 55);

    # [ABCD  8  6 57]  [DABC 15 10 58]  [CDAB  6 15 59]  [BCDA 13 21 60]
    round4_op($src, $a, $b, $c, $d, 8, 6, 56);
    round4_op($src, $d, $a, $b, $c, 15, 10, 57);
    round4_op($src, $c, $d, $a, $b, 6, 15, 58);
    round4_op($src, $b, $c, $d, $a, 13, 21, 59);

    # [ABCD  4  6 61]  [DABC 11 10 62]  [CDAB  2 15 63]  [BCDA  9 21 64]
    round4_op($src, $a, $b, $c, $d, 4, 6, 60);
    round4_op($src, $d, $a, $b, $c, 11, 10, 61);
    round4_op($src, $c, $d, $a, $b, 2, 15, 62);
    round4_op($src, $b, $c, $d, $a, 9, 21, 63);

    $code .= <<___;
    vpaddd	$pa, $a, $a
    vpaddd	$pb, $b, $b
    vpaddd	$pc, $c, $c
    vpaddd	$pd, $d, $d
___
  }

  # int md5_x86_64_avx512(const uint8_t *data,
  #                       size_t len,
  #                       uint8_t out[MD5_DIGEST_LENGTH]);
  $code .= <<___;
#ifndef MY_ASSEMBLER_IS_TOO_OLD_FOR_512AVX
  .text

  .globl	md5_x86_64_avx512
  .type	md5_x86_64_avx512,\@function,3
  .align	32
  md5_x86_64_avx512:
  .cfi_startproc
  endbranch
___
  if ($win64) {
    $code .= <<___;
    push  %rbp
    mov %rsp,%rbp
    sub $XMM_STORAGE, %rsp
    and	\$0xfffffffffffffff0,%rsp
    vmovdqa  %xmm6, 16*0(%rsp)
    vmovdqa  %xmm7, 16*1(%rsp)
    vmovdqa  %xmm8, 16*2(%rsp)
    vmovdqa  %xmm9, 16*3(%rsp)
    vmovdqa  %xmm10, 16*4(%rsp)
___
  }
  $code .= <<___;
  vmovd	4*0($state), $a
  vmovd	4*1($state), $b
  vmovd	4*2($state), $c
  vmovd	4*3($state), $d

  .align 32
  .L_main_loop:
___

  one_round($data);

  $code .= <<___;
  add	\$64, $data
  dec	$num
  jnz	.L_main_loop

  .L_done:
___
  if ($win64) {
    $code .= <<___;
    vmovdqa  16*0(%rsp), %xmm6
    vmovdqa  16*1(%rsp), %xmm7
    vmovdqa  16*2(%rsp), %xmm8
    vmovdqa  16*3(%rsp), %xmm9
    vmovdqa  16*4(%rsp), %xmm10
    mov %rbp,%rsp
    pop  %rbp
___
  }

  $code .= <<___;
  vmovd	$a, 4*0($state)
  vmovd	$b, 4*1($state)
  vmovd	$c, 4*2($state)
  vmovd	$d, 4*3($state)
  ret
  .cfi_endproc
  .size md5_x86_64_avx512, .-md5_x86_64_avx512

  .section .rodata
  .align 32
  .L_T:
      .long 0xd76aa478, 0xe8c7b756, 0x242070db, 0xc1bdceee
      .long 0xf57c0faf, 0x4787c62a, 0xa8304613, 0xfd469501
      .long 0x698098d8, 0x8b44f7af, 0xffff5bb1, 0x895cd7be
      .long 0x6b901122, 0xfd987193, 0xa679438e, 0x49b40821
      .long 0xf61e2562, 0xc040b340, 0x265e5a51, 0xe9b6c7aa
      .long 0xd62f105d, 0x02441453, 0xd8a1e681, 0xe7d3fbc8
      .long 0x21e1cde6, 0xc33707d6, 0xf4d50d87, 0x455a14ed
      .long 0xa9e3e905, 0xfcefa3f8, 0x676f02d9, 0x8d2a4c8a
      .long 0xfffa3942, 0x8771f681, 0x6d9d6122, 0xfde5380c
      .long 0xa4beea44, 0x4bdecfa9, 0xf6bb4b60, 0xbebfbc70
      .long 0x289b7ec6, 0xeaa127fa, 0xd4ef3085, 0x04881d05
      .long 0xd9d4d039, 0xe6db99e5, 0x1fa27cf8, 0xc4ac5665
      .long 0xf4292244, 0x432aff97, 0xab9423a7, 0xfc93a039
      .long 0x655b59c3, 0x8f0ccc92, 0xffeff47d, 0x85845dd1
      .long 0x6fa87e4f, 0xfe2ce6e0, 0xa3014314, 0x4e0811a1
      .long 0xf7537e82, 0xbd3af235, 0x2ad7d2bb, 0xeb86d391
#endif
___

} else {
  $code = <<___;
  .text
  .globl	md5_x86_64_avx512
  md5_x86_64_avx512:
    .byte   0x0f,0x0b    # ud2
    ret
  .size md5_x86_64_avx512, .-md5_x86_64_avx512
___
}

print $code;

close STDOUT or die "error closing STDOUT: $!";
