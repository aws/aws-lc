#! /usr/bin/env perl
# Copyright (C) 2025 Intel Corporation
#
# Licensed under the OpenSSL license (the "License").  You may not use
# this file except in compliance with the License.  You can obtain a copy
# in the file LICENSE in the source distribution or at
# https://www.openssl.org/source/license.html

# This implementation is identical to the liboqs version
# (https://github.com/open-quantum-safe/liboqs/blob/main/src/common/sha3/avx512vl_low/KeccakP-1600-AVX512VL.S)
# and adapted (simplified) to fit to the existing absorb and squeeze API's in C.
#
######################################################################
# The main building block of this code is keccak_1600_permute function.
# It is implemented using AVX512VL instruction set, AVX512F and AVX512DQ extensions in particular.
#
# This function, as is, can work on 1 to 4 independent states at the same time.
#
# YMM registers 0 to 24 are used as Keccak state registers.
#

# The first two arguments should always be the flavour and output file path.
if ($#ARGV < 1) {
    die "Not enough arguments provided. " .
        "Two arguments are necessary: the flavour and the output file path.";
}

$flavour = shift;
$output  = shift;

$win64=0;
$win64=1 if ($flavour =~ /[nm]asm|mingw64/ || $output =~ /\.asm$/);

$0 =~ m/(.*[\/\\])[^\/\\]+$/;
$dir=$1;

( $xlate="${dir}x86_64-xlate.pl" and -f $xlate ) or
    ( $xlate="${dir}../../../perlasm/x86_64-xlate.pl" and -f $xlate) or
    die "can't locate x86_64-xlate.pl";

$avx512vl = 1;
for (@ARGV) {
    $avx512vl = 0 if (/-DMY_ASSEMBLER_IS_TOO_OLD_FOR_512AVX/);
}

open OUT,"| \"$^X\" \"$xlate\" $flavour \"$output\"";
*STDOUT=*OUT;

#======================================================================


# Loads one 64-bit register from four state structures into single ymm
# ymmN = state[0][N] | state[1][N] | state[2][N] | state[3][N]
sub load_reg_x4
{
    my ($base,$reg_index) = @_;
    my $offset = $reg_index * 8;
    my $lane = 25 * 8;

    $code.=<<___ ;
    vmovq       $offset+$lane*0($base), %xmm$reg_index
    vpinsrq     \$1, $offset+$lane*1($base), %xmm$reg_index, %xmm$reg_index
    vmovq       $offset+$lane*2($base), %xmm25
    vpinsrq     \$1, $offset+$lane*3($base), %xmm25, %xmm25
    vinserti32x4 \$1, %xmm25, %ymm$reg_index, %ymm$reg_index
___
}

# Loads four 64-bit registers from four state structures into four ymm registers
# Same as load_reg_x4 but more efficient transposition.
sub load_4regs_x4
{
    my ($base,$reg_index) = @_;
    my $offset = $reg_index * 8;
    my $r0 = $reg_index;
    my $r1 = $reg_index + 1;
    my $r2 = $reg_index + 2;
    my $r3 = $reg_index + 3;
    my $lane = 25 * 8;

    $code.=<<___ ;
    vmovdqu64   $offset+$lane*0($base), %ymm25
    vmovdqu64   $offset+$lane*1($base), %ymm26
    vmovdqu64   $offset+$lane*2($base), %ymm27
    vmovdqu64   $offset+$lane*3($base), %ymm28
    vpunpcklqdq %ymm26, %ymm25, %ymm29          # A0 B0 A2 B2
    vpunpckhqdq %ymm26, %ymm25, %ymm30          # A1 B1 A3 B3
    vpunpcklqdq %ymm28, %ymm27, %ymm25          # C0 D0 C2 D2
    vpunpckhqdq %ymm28, %ymm27, %ymm26          # C1 D1 C3 D3
    vshufi64x2  \$0, %ymm25, %ymm29, %ymm$r0    # A0 B0 C0 D0
    vshufi64x2  \$0, %ymm26, %ymm30, %ymm$r1    # A1 B1 C1 D1
    vshufi64x2  \$3, %ymm25, %ymm29, %ymm$r2    # A2 B2 C2 D2
    vshufi64x2  \$3, %ymm26, %ymm30, %ymm$r3    # A3 B3 C3 D3
___
}

# Stores one 64-bit register into four state structures from a single ymm
# state[0][N] = ymmN & (2^64-1)
# state[1][N] = (ymmN >> 64) & (2^64-1)
# state[2][N] = (ymmN >> 128) & (2^64-1)
# state[3][N] = (ymmN >> 192) & (2^64-1)
sub save_reg_x4
{
    my ($base,$reg_index) = @_;
    my $offset = $reg_index * 8;
    my $lane = 25 * 8;

    $code.=<<___ ;
    vextracti32x4 \$1, %ymm$reg_index, %xmm25
    vmovq       %xmm$reg_index, $offset+$lane*0($base)
    vpextrq     \$1,  %xmm$reg_index, $offset+$lane*1($base)
    vmovq       %xmm25, $offset+$lane*2($base)
    vpextrq     \$1,  %xmm25, $offset+$lane*3($base)
___
}

# Stores four 64-bit registers into four state structures from four ymm registers
# Same as store_reg_x4 but more efficient transposition.
sub save_4regs_x4
{
    my ($base,$reg_index) = @_;
    my $offset = $reg_index * 8;
    my $r0 = $reg_index;
    my $r1 = $reg_index + 1;
    my $r2 = $reg_index + 2;
    my $r3 = $reg_index + 3;
    my $lane = 25 * 8;

    $code.=<<___ ;
    vpunpcklqdq %ymm$r1, %ymm$r0, %ymm25        # A0 A1 C0 C1
    vpunpckhqdq %ymm$r1, %ymm$r0, %ymm26        # B0 B1 D0 D1
    vpunpcklqdq %ymm$r3, %ymm$r2, %ymm27        # A2 A3 C2 C3
    vpunpckhqdq %ymm$r3, %ymm$r2, %ymm28        # B2 B3 D2 D3
    vshufi64x2  \$0, %ymm27, %ymm25, %ymm$r0    # A0 A1 A2 A3
    vshufi64x2  \$0, %ymm28, %ymm26, %ymm$r1    # B0 B1 B2 B3
    vshufi64x2  \$3, %ymm27, %ymm25, %ymm$r2    # C0 C1 C2 C3
    vshufi64x2  \$3, %ymm28, %ymm26, %ymm$r3    # D0 D1 D2 D3
    vmovdqu64   %ymm$r0, $offset+$lane*0($base)
    vmovdqu64   %ymm$r1, $offset+$lane*1($base)
    vmovdqu64   %ymm$r2, $offset+$lane*2($base)
    vmovdqu64   %ymm$r3, $offset+$lane*3($base)
___
}

# Stores XMM6-XMM15 on the stack frame on Windows
sub save_xmm6_xmm15
{
    if ($win64) {
        $code .= "sub \$10*16, %rsp\n";
        for (my $j = 0; $j < 10; $j++) {
            my $r = 6 + $j;
            $code .= "vmovdqu  %xmm$r, $j*16(%rsp)\n";
        }
    }
}

# Restores XMM6-XMM15 from the stack on Windows
sub restore_xmm6_xmm15
{
    if ($win64) {
        for (my $j = 0; $j < 10; $j++) {
            my $r = 6 + $j;
            $code .= "vmovdqu  $j*16(%rsp), %xmm$r\n";
        }
        $code .= "add \$10*16, %rsp\n";
    }
}

if ($avx512vl) {

    $arg1="%rdi";	# 1st arg
    $roundn="%r10d";
    $tblptr="%r11";

$code.=<<___ ;
#ifndef MY_ASSEMBLER_IS_TOO_OLD_FOR_512AVX

.text

# Perform Keccak permutation
#
# YMM registers 0 to 24 are used as Keccak state registers.
# This function, as is, can work on 1 to 4 independent states at the same time.
#
# There is no clear boundary between Theta, Rho, Pi, Chi and Iota steps.
# Instructions corresponding to these steps overlap for better efficiency.
#
# ymm0-ymm24    [in/out]    Keccak state registers (one SIMD per one state register)
# ymm25-ymm31   [clobbered] temporary SIMD registers
# $roundn       [clobbered] used for round tracking
# $tblptr       [clobbered] used for access to SHA3 constant table

.align  32
keccak_1600_permute:
.cfi_startproc
    endbranch
    movl    \$24, $roundn                          # 24 rounds
    leaq    iotas_avx512(%rip), $tblptr            # Load the address of the SHA3 round constants

.align  32
.Lkeccak_rnd_loop:
    # Theta step

    # Compute column parities
    # C[5] = [0, 0, 0, 0, 0]
    # for x in 0 to 4:
    #     C[x] = state[x][0] XOR state[x][1] XOR state[x][2] XOR state[x][3] XOR state[x][4]

    vmovdqa64   %ymm0, %ymm25
    vpternlogq  \$0x96, %ymm5, %ymm10, %ymm25
    vmovdqa64   %ymm1, %ymm26
    vpternlogq  \$0x96, %ymm11, %ymm6, %ymm26
    vmovdqa64   %ymm2, %ymm27
    vpternlogq  \$0x96, %ymm12, %ymm7, %ymm27

    vmovdqa64   %ymm3, %ymm28
    vpternlogq  \$0x96, %ymm13, %ymm8, %ymm28
    vmovdqa64   %ymm4, %ymm29
    vpternlogq  \$0x96, %ymm14, %ymm9, %ymm29
    vpternlogq  \$0x96, %ymm20, %ymm15, %ymm25

    vpternlogq  \$0x96, %ymm21, %ymm16, %ymm26
    vpternlogq  \$0x96, %ymm22, %ymm17, %ymm27
    vpternlogq  \$0x96, %ymm23, %ymm18, %ymm28

    # Start computing D values and keep computing column parity
    # D[5] = [0, 0, 0, 0, 0]
    # for x in 0 to 4:
    #     D[x] = C[(x+4) mod 5] XOR ROTATE_LEFT(C[(x+1) mod 5], 1)

    vprolq      \$1, %ymm26, %ymm30
    vprolq      \$1, %ymm27, %ymm31
    vpternlogq  \$0x96, %ymm24, %ymm19, %ymm29

    # Continue computing D values and apply Theta
    # for x in 0 to 4:
    #     for y in 0 to 4:
    #         state[x][y] = state[x][y] XOR D[x]

    vpternlogq  \$0x96, %ymm30, %ymm29, %ymm0
    vpternlogq  \$0x96, %ymm30, %ymm29, %ymm10
    vpternlogq  \$0x96, %ymm30, %ymm29, %ymm20

    vpternlogq  \$0x96, %ymm30, %ymm29, %ymm5
    vpternlogq  \$0x96, %ymm30, %ymm29, %ymm15
    vprolq      \$1, %ymm28, %ymm30

    vpternlogq  \$0x96, %ymm31, %ymm25, %ymm6
    vpternlogq  \$0x96, %ymm31, %ymm25, %ymm16
    vpternlogq  \$0x96, %ymm31, %ymm25, %ymm1

    vpternlogq  \$0x96, %ymm31, %ymm25, %ymm11
    vpternlogq  \$0x96, %ymm31, %ymm25, %ymm21
    vprolq      \$1, %ymm29, %ymm31

    vpbroadcastq    ($tblptr), %ymm29           # Load the round constant into ymm29 (Iota)
    addq        \$8, $tblptr                    # Increment the pointer to the next round constant

    vpternlogq  \$0x96, %ymm30, %ymm26, %ymm12
    vpternlogq  \$0x96, %ymm30, %ymm26, %ymm7
    vpternlogq  \$0x96, %ymm30, %ymm26, %ymm22

    vpternlogq  \$0x96, %ymm30, %ymm26, %ymm17
    vpternlogq  \$0x96, %ymm30, %ymm26, %ymm2
    vprolq      \$1, %ymm25, %ymm30

    # Rho step
    # Keep applying Theta and start Rho step
    #
    # ROTATION_OFFSETS[5][5] = [
    #     [0, 1, 62, 28, 27],
    #     [36, 44, 6, 55, 20],
    #     [3, 10, 43, 25, 39],
    #     [41, 45, 15, 21, 8],
    #     [18, 2, 61, 56, 14] ]
    #
    # for x in 0 to 4:
    #     for y in 0 to 4:
    #         state[x][y] = ROTATE_LEFT(state[x][y], ROTATION_OFFSETS[x][y])

    vpternlogq  \$0x96, %ymm31, %ymm27, %ymm3
    vpternlogq  \$0x96, %ymm31, %ymm27, %ymm13
    vpternlogq  \$0x96, %ymm31, %ymm27, %ymm23

    vprolq      \$44, %ymm6, %ymm6
    vpternlogq  \$0x96, %ymm31, %ymm27, %ymm18
    vpternlogq  \$0x96, %ymm31, %ymm27, %ymm8

    vprolq      \$43, %ymm12, %ymm12
    vprolq      \$21, %ymm18, %ymm18
    vpternlogq  \$0x96, %ymm30, %ymm28, %ymm24

    vprolq      \$14, %ymm24, %ymm24
    vprolq      \$28, %ymm3, %ymm3
    vpternlogq  \$0x96, %ymm30, %ymm28, %ymm9

    vprolq      \$20, %ymm9, %ymm9
    vprolq      \$3, %ymm10, %ymm10
    vpternlogq  \$0x96, %ymm30, %ymm28, %ymm19

    vprolq      \$45, %ymm16, %ymm16
    vprolq      \$61, %ymm22, %ymm22
    vpternlogq  \$0x96, %ymm30, %ymm28, %ymm4

    vprolq      \$1, %ymm1, %ymm1
    vprolq      \$6, %ymm7, %ymm7
    vpternlogq  \$0x96, %ymm30, %ymm28, %ymm14

    # Continue with Rho and start Pi and Chi steps at the same time
    # Ternary logic 0xD2 is used for Chi step
    #
    # for x in 0 to 4:
    #     for y in 0 to 4:
    #         state[x][y] = state[x][y] XOR ((NOT state[(x+1) mod 5][y]) AND state[(x+2) mod 5][y])

    vprolq      \$25, %ymm13, %ymm13
    vprolq      \$8, %ymm19, %ymm19
    vmovdqa64   %ymm0, %ymm30
    vpternlogq  \$0xD2, %ymm12, %ymm6, %ymm30

    vprolq      \$18, %ymm20, %ymm20
    vprolq      \$27, %ymm4, %ymm4
    vpxorq      %ymm29, %ymm30, %ymm30          # Iota step

    vprolq      \$36, %ymm5, %ymm5
    vprolq      \$10, %ymm11, %ymm11
    vmovdqa64   %ymm6, %ymm31
    vpternlogq  \$0xD2, %ymm18, %ymm12, %ymm31

    vprolq      \$15, %ymm17, %ymm17
    vprolq      \$56, %ymm23, %ymm23
    vpternlogq  \$0xD2, %ymm24, %ymm18, %ymm12

    vprolq      \$62, %ymm2, %ymm2
    vprolq      \$55, %ymm8, %ymm8
    vpternlogq  \$0xD2, %ymm0, %ymm24, %ymm18

    vprolq      \$39, %ymm14, %ymm14
    vprolq      \$41, %ymm15, %ymm15
    vpternlogq  \$0xD2, %ymm6, %ymm0, %ymm24
    vmovdqa64   %ymm30, %ymm0
    vmovdqa64   %ymm31, %ymm6

    vprolq      \$2, %ymm21, %ymm21
    vmovdqa64   %ymm3, %ymm30
    vpternlogq  \$0xD2, %ymm10, %ymm9, %ymm30
    vmovdqa64   %ymm9, %ymm31
    vpternlogq  \$0xD2, %ymm16, %ymm10, %ymm31

    vpternlogq  \$0xD2, %ymm22, %ymm16, %ymm10
    vpternlogq  \$0xD2, %ymm3, %ymm22, %ymm16
    vpternlogq  \$0xD2, %ymm9, %ymm3, %ymm22
    vmovdqa64   %ymm30, %ymm3
    vmovdqa64   %ymm31, %ymm9

    vmovdqa64   %ymm1, %ymm30
    vpternlogq  \$0xD2, %ymm13, %ymm7, %ymm30
    vmovdqa64   %ymm7, %ymm31
    vpternlogq  \$0xD2, %ymm19, %ymm13, %ymm31
    vpternlogq  \$0xD2, %ymm20, %ymm19, %ymm13

    vpternlogq  \$0xD2, %ymm1, %ymm20, %ymm19
    vpternlogq  \$0xD2, %ymm7, %ymm1, %ymm20
    vmovdqa64   %ymm30, %ymm1
    vmovdqa64   %ymm31, %ymm7
    vmovdqa64   %ymm4, %ymm30
    vpternlogq  \$0xD2, %ymm11, %ymm5, %ymm30

    vmovdqa64   %ymm5, %ymm31
    vpternlogq  \$0xD2, %ymm17, %ymm11, %ymm31
    vpternlogq  \$0xD2, %ymm23, %ymm17, %ymm11
    vpternlogq  \$0xD2, %ymm4, %ymm23, %ymm17

    vpternlogq  \$0xD2, %ymm5, %ymm4, %ymm23
    vmovdqa64   %ymm30, %ymm4
    vmovdqa64   %ymm31, %ymm5
    vmovdqa64   %ymm2, %ymm30
    vpternlogq  \$0xD2, %ymm14, %ymm8, %ymm30
    vmovdqa64   %ymm8, %ymm31
    vpternlogq  \$0xD2, %ymm15, %ymm14, %ymm31

    vpternlogq  \$0xD2, %ymm21, %ymm15, %ymm14
    vpternlogq  \$0xD2, %ymm2, %ymm21, %ymm15
    vpternlogq  \$0xD2, %ymm8, %ymm2, %ymm21
    vmovdqa64   %ymm30, %ymm2
    vmovdqa64   %ymm31, %ymm8

    # Complete the steps and update state registers in ymm0 to ymm24
    vmovdqa64   %ymm3,  %ymm30
    vmovdqa64   %ymm18, %ymm3
    vmovdqa64   %ymm17, %ymm18
    vmovdqa64   %ymm11, %ymm17
    vmovdqa64   %ymm7,  %ymm11
    vmovdqa64   %ymm10, %ymm7
    vmovdqa64   %ymm1,  %ymm10
    vmovdqa64   %ymm6,  %ymm1
    vmovdqa64   %ymm9,  %ymm6
    vmovdqa64   %ymm22, %ymm9
    vmovdqa64   %ymm14, %ymm22
    vmovdqa64   %ymm20, %ymm14
    vmovdqa64   %ymm2,  %ymm20
    vmovdqa64   %ymm12, %ymm2
    vmovdqa64   %ymm13, %ymm12
    vmovdqa64   %ymm19, %ymm13
    vmovdqa64   %ymm23, %ymm19
    vmovdqa64   %ymm15, %ymm23
    vmovdqa64   %ymm4,  %ymm15
    vmovdqa64   %ymm24, %ymm4
    vmovdqa64   %ymm21, %ymm24
    vmovdqa64   %ymm8,  %ymm21
    vmovdqa64   %ymm16, %ymm8
    vmovdqa64   %ymm5,  %ymm16
    vmovdqa64   %ymm30, %ymm5

    decl        $roundn              # Decrement the round counter
    jnz         .Lkeccak_rnd_loop    # Jump to the start of the loop if r13d is not zero
    ret
.cfi_endproc

.globl	KeccakF1600_avx512vl
.type	KeccakF1600_avx512vl,\@function,1
.align  32
KeccakF1600_avx512vl:
.cfi_startproc
    endbranch
___
    # save xmm6-xmm15 if required
    &save_xmm6_xmm15();

    # load the state
    for (my $i = 0; $i < 25; $i++) {
        $code .= "vmovq   8*$i($arg1),  %xmm$i\n";
    }

    # perform permute on the state
    $code.=<<___ ;

    call    keccak_1600_permute

___

    # save updated state
    for (my $i = 0; $i < 25; $i++) {
        $code .= "vmovq   %xmm$i,  8*$i($arg1)\n";
    }

    # restore xmm6-xmm15 if required
    &restore_xmm6_xmm15();

    $code.=<<___ ;
    vzeroupper
    ret
.cfi_endproc

.globl	KeccakF1600_x4_avx512vl
.type	KeccakF1600_x4_avx512vl,\@function,1
.align  32
KeccakF1600_x4_avx512vl:
.cfi_startproc
    endbranch
___
    # save xmm6-xmm15 if required
    &save_xmm6_xmm15();

    # load and transpose four states
    for (my $i = 0; ($i + 4) < 25; $i += 4) {
        &load_4regs_x4($arg1, $i);
    }
    &load_reg_x4($arg1, 24);

    # perform permute on the four states

    $code.=<<___ ;

    call    keccak_1600_permute

___

    # transpose and save four updated states
    for (my $i = 0; ($i + 4) < 25; $i += 4) {
        &save_4regs_x4($arg1, $i);
    }
    &save_reg_x4($arg1, 24);

    # restore xmm6-xmm15 if required
    &restore_xmm6_xmm15();

    $code.=<<___ ;
    vzeroupper
    ret
.cfi_endproc

.section .rodata

.align  64
iotas_avx512:
.quad 0x0000000000000001, 0x0000000000008082
.quad 0x800000000000808a, 0x8000000080008000
.quad 0x000000000000808b, 0x0000000080000001
.quad 0x8000000080008081, 0x8000000000008009
.quad 0x000000000000008a, 0x0000000000000088
.quad 0x0000000080008009, 0x000000008000000a
.quad 0x000000008000808b, 0x800000000000008b
.quad 0x8000000000008089, 0x8000000000008003
.quad 0x8000000000008002, 0x8000000000000080
.quad 0x000000000000800a, 0x800000008000000a
.quad 0x8000000080008081, 0x8000000000008080
.quad 0x0000000080000001, 0x8000000080008008

#endif

.text
___
} else {
$code.=<<___ ;
.text
.globl	KeccakF1600_avx512vl
.type	KeccakF1600_avx512vl,\@function,1
.globl	KeccakF1600_x4_avx512vl
.type	KeccakF1600_x4_avx512vl,\@function,1
KeccakF1600_avx512vl:
KeccakF1600_x4_avx512vl:
.cfi_startproc
    ret
.cfi_endproc
___
}

print $code;

close STDOUT or die "error closing STDOUT: $!";
