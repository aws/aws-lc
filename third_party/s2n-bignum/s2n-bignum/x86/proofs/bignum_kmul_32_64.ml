(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* 32x32 -> 64 multiplication, using Karatsuba reduction.                    *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/fastmul/bignum_kmul_32_64.o";;
 ****)

let bignum_kmul_32_64_mc = define_assert_from_elf "bignum_kmul_32_64_mc" "x86/fastmul/bignum_kmul_32_64.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x53;                    (* PUSH (% rbx) *)
  0x55;                    (* PUSH (% rbp) *)
  0x41; 0x54;              (* PUSH (% r12) *)
  0x41; 0x55;              (* PUSH (% r13) *)
  0x41; 0x56;              (* PUSH (% r14) *)
  0x41; 0x57;              (* PUSH (% r15) *)
  0x51;                    (* PUSH (% rcx) *)
  0x48; 0x89; 0xd1;        (* MOV (% rcx) (% rdx) *)
  0xe8; 0x07; 0x0e; 0x00; 0x00;
                           (* CALL (Imm32 (word 3591)) *)
  0x48; 0x8d; 0xbf; 0xc0; 0x00; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rdi,192)) *)
  0x48; 0x8d; 0x76; 0x40;  (* LEA (% rsi) (%% (rsi,64)) *)
  0x48; 0x8d; 0x89; 0x80; 0x00; 0x00; 0x00;
                           (* LEA (% rcx) (%% (rcx,128)) *)
  0xe8; 0xf0; 0x0d; 0x00; 0x00;
                           (* CALL (Imm32 (word 3568)) *)
  0x4c; 0x8b; 0x04; 0x24;  (* MOV (% r8) (Memop Quadword (%% (rsp,0))) *)
  0x48; 0x81; 0xef; 0x40; 0x01; 0x00; 0x00;
                           (* SUB (% rdi) (Imm32 (word 320)) *)
  0x48; 0x89; 0x3c; 0x24;  (* MOV (Memop Quadword (%% (rsp,0))) (% rdi) *)
  0x48; 0x8b; 0x86; 0x40; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Memop Quadword (%% (rsi,18446744073709551424))) *)
  0x48; 0x2b; 0x46; 0xc0;  (* SUB (% rax) (Memop Quadword (%% (rsi,18446744073709551552))) *)
  0x49; 0x89; 0x00;        (* MOV (Memop Quadword (%% (r8,0))) (% rax) *)
  0x48; 0x8b; 0x86; 0x48; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Memop Quadword (%% (rsi,18446744073709551432))) *)
  0x48; 0x1b; 0x46; 0xc8;  (* SBB (% rax) (Memop Quadword (%% (rsi,18446744073709551560))) *)
  0x49; 0x89; 0x40; 0x08;  (* MOV (Memop Quadword (%% (r8,8))) (% rax) *)
  0x48; 0x8b; 0x86; 0x50; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Memop Quadword (%% (rsi,18446744073709551440))) *)
  0x48; 0x1b; 0x46; 0xd0;  (* SBB (% rax) (Memop Quadword (%% (rsi,18446744073709551568))) *)
  0x49; 0x89; 0x40; 0x10;  (* MOV (Memop Quadword (%% (r8,16))) (% rax) *)
  0x48; 0x8b; 0x86; 0x58; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Memop Quadword (%% (rsi,18446744073709551448))) *)
  0x48; 0x1b; 0x46; 0xd8;  (* SBB (% rax) (Memop Quadword (%% (rsi,18446744073709551576))) *)
  0x49; 0x89; 0x40; 0x18;  (* MOV (Memop Quadword (%% (r8,24))) (% rax) *)
  0x48; 0x8b; 0x86; 0x60; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Memop Quadword (%% (rsi,18446744073709551456))) *)
  0x48; 0x1b; 0x46; 0xe0;  (* SBB (% rax) (Memop Quadword (%% (rsi,18446744073709551584))) *)
  0x49; 0x89; 0x40; 0x20;  (* MOV (Memop Quadword (%% (r8,32))) (% rax) *)
  0x48; 0x8b; 0x86; 0x68; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Memop Quadword (%% (rsi,18446744073709551464))) *)
  0x48; 0x1b; 0x46; 0xe8;  (* SBB (% rax) (Memop Quadword (%% (rsi,18446744073709551592))) *)
  0x49; 0x89; 0x40; 0x28;  (* MOV (Memop Quadword (%% (r8,40))) (% rax) *)
  0x48; 0x8b; 0x86; 0x70; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Memop Quadword (%% (rsi,18446744073709551472))) *)
  0x48; 0x1b; 0x46; 0xf0;  (* SBB (% rax) (Memop Quadword (%% (rsi,18446744073709551600))) *)
  0x49; 0x89; 0x40; 0x30;  (* MOV (Memop Quadword (%% (r8,48))) (% rax) *)
  0x48; 0x8b; 0x86; 0x78; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Memop Quadword (%% (rsi,18446744073709551480))) *)
  0x48; 0x1b; 0x46; 0xf8;  (* SBB (% rax) (Memop Quadword (%% (rsi,18446744073709551608))) *)
  0x49; 0x89; 0x40; 0x38;  (* MOV (Memop Quadword (%% (r8,56))) (% rax) *)
  0x48; 0x8b; 0x46; 0x80;  (* MOV (% rax) (Memop Quadword (%% (rsi,18446744073709551488))) *)
  0x48; 0x1b; 0x06;        (* SBB (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x49; 0x89; 0x40; 0x40;  (* MOV (Memop Quadword (%% (r8,64))) (% rax) *)
  0x48; 0x8b; 0x46; 0x88;  (* MOV (% rax) (Memop Quadword (%% (rsi,18446744073709551496))) *)
  0x48; 0x1b; 0x46; 0x08;  (* SBB (% rax) (Memop Quadword (%% (rsi,8))) *)
  0x49; 0x89; 0x40; 0x48;  (* MOV (Memop Quadword (%% (r8,72))) (% rax) *)
  0x48; 0x8b; 0x46; 0x90;  (* MOV (% rax) (Memop Quadword (%% (rsi,18446744073709551504))) *)
  0x48; 0x1b; 0x46; 0x10;  (* SBB (% rax) (Memop Quadword (%% (rsi,16))) *)
  0x49; 0x89; 0x40; 0x50;  (* MOV (Memop Quadword (%% (r8,80))) (% rax) *)
  0x48; 0x8b; 0x46; 0x98;  (* MOV (% rax) (Memop Quadword (%% (rsi,18446744073709551512))) *)
  0x48; 0x1b; 0x46; 0x18;  (* SBB (% rax) (Memop Quadword (%% (rsi,24))) *)
  0x49; 0x89; 0x40; 0x58;  (* MOV (Memop Quadword (%% (r8,88))) (% rax) *)
  0x48; 0x8b; 0x46; 0xa0;  (* MOV (% rax) (Memop Quadword (%% (rsi,18446744073709551520))) *)
  0x48; 0x1b; 0x46; 0x20;  (* SBB (% rax) (Memop Quadword (%% (rsi,32))) *)
  0x49; 0x89; 0x40; 0x60;  (* MOV (Memop Quadword (%% (r8,96))) (% rax) *)
  0x48; 0x8b; 0x46; 0xa8;  (* MOV (% rax) (Memop Quadword (%% (rsi,18446744073709551528))) *)
  0x48; 0x1b; 0x46; 0x28;  (* SBB (% rax) (Memop Quadword (%% (rsi,40))) *)
  0x49; 0x89; 0x40; 0x68;  (* MOV (Memop Quadword (%% (r8,104))) (% rax) *)
  0x48; 0x8b; 0x46; 0xb0;  (* MOV (% rax) (Memop Quadword (%% (rsi,18446744073709551536))) *)
  0x48; 0x1b; 0x46; 0x30;  (* SBB (% rax) (Memop Quadword (%% (rsi,48))) *)
  0x49; 0x89; 0x40; 0x70;  (* MOV (Memop Quadword (%% (r8,112))) (% rax) *)
  0x48; 0x8b; 0x46; 0xb8;  (* MOV (% rax) (Memop Quadword (%% (rsi,18446744073709551544))) *)
  0x48; 0x1b; 0x46; 0x38;  (* SBB (% rax) (Memop Quadword (%% (rsi,56))) *)
  0x49; 0x89; 0x40; 0x78;  (* MOV (Memop Quadword (%% (r8,120))) (% rax) *)
  0xbb; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% ebx) (Imm32 (word 0)) *)
  0x4d; 0x19; 0xc9;        (* SBB (% r9) (% r9) *)
  0x49; 0x8b; 0x10;        (* MOV (% rdx) (Memop Quadword (%% (r8,0))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADCX (% rdx) (% rbx) *)
  0x49; 0x89; 0x10;        (* MOV (Memop Quadword (%% (r8,0))) (% rdx) *)
  0x49; 0x8b; 0x50; 0x08;  (* MOV (% rdx) (Memop Quadword (%% (r8,8))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADCX (% rdx) (% rbx) *)
  0x49; 0x89; 0x50; 0x08;  (* MOV (Memop Quadword (%% (r8,8))) (% rdx) *)
  0x49; 0x8b; 0x50; 0x10;  (* MOV (% rdx) (Memop Quadword (%% (r8,16))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADCX (% rdx) (% rbx) *)
  0x49; 0x89; 0x50; 0x10;  (* MOV (Memop Quadword (%% (r8,16))) (% rdx) *)
  0x49; 0x8b; 0x50; 0x18;  (* MOV (% rdx) (Memop Quadword (%% (r8,24))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADCX (% rdx) (% rbx) *)
  0x49; 0x89; 0x50; 0x18;  (* MOV (Memop Quadword (%% (r8,24))) (% rdx) *)
  0x49; 0x8b; 0x50; 0x20;  (* MOV (% rdx) (Memop Quadword (%% (r8,32))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADCX (% rdx) (% rbx) *)
  0x49; 0x89; 0x50; 0x20;  (* MOV (Memop Quadword (%% (r8,32))) (% rdx) *)
  0x49; 0x8b; 0x50; 0x28;  (* MOV (% rdx) (Memop Quadword (%% (r8,40))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADCX (% rdx) (% rbx) *)
  0x49; 0x89; 0x50; 0x28;  (* MOV (Memop Quadword (%% (r8,40))) (% rdx) *)
  0x49; 0x8b; 0x50; 0x30;  (* MOV (% rdx) (Memop Quadword (%% (r8,48))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADCX (% rdx) (% rbx) *)
  0x49; 0x89; 0x50; 0x30;  (* MOV (Memop Quadword (%% (r8,48))) (% rdx) *)
  0x49; 0x8b; 0x50; 0x38;  (* MOV (% rdx) (Memop Quadword (%% (r8,56))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADCX (% rdx) (% rbx) *)
  0x49; 0x89; 0x50; 0x38;  (* MOV (Memop Quadword (%% (r8,56))) (% rdx) *)
  0x49; 0x8b; 0x50; 0x40;  (* MOV (% rdx) (Memop Quadword (%% (r8,64))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADCX (% rdx) (% rbx) *)
  0x49; 0x89; 0x50; 0x40;  (* MOV (Memop Quadword (%% (r8,64))) (% rdx) *)
  0x49; 0x8b; 0x50; 0x48;  (* MOV (% rdx) (Memop Quadword (%% (r8,72))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADCX (% rdx) (% rbx) *)
  0x49; 0x89; 0x50; 0x48;  (* MOV (Memop Quadword (%% (r8,72))) (% rdx) *)
  0x49; 0x8b; 0x50; 0x50;  (* MOV (% rdx) (Memop Quadword (%% (r8,80))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADCX (% rdx) (% rbx) *)
  0x49; 0x89; 0x50; 0x50;  (* MOV (Memop Quadword (%% (r8,80))) (% rdx) *)
  0x49; 0x8b; 0x50; 0x58;  (* MOV (% rdx) (Memop Quadword (%% (r8,88))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADCX (% rdx) (% rbx) *)
  0x49; 0x89; 0x50; 0x58;  (* MOV (Memop Quadword (%% (r8,88))) (% rdx) *)
  0x49; 0x8b; 0x50; 0x60;  (* MOV (% rdx) (Memop Quadword (%% (r8,96))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADCX (% rdx) (% rbx) *)
  0x49; 0x89; 0x50; 0x60;  (* MOV (Memop Quadword (%% (r8,96))) (% rdx) *)
  0x49; 0x8b; 0x50; 0x68;  (* MOV (% rdx) (Memop Quadword (%% (r8,104))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADCX (% rdx) (% rbx) *)
  0x49; 0x89; 0x50; 0x68;  (* MOV (Memop Quadword (%% (r8,104))) (% rdx) *)
  0x49; 0x8b; 0x50; 0x70;  (* MOV (% rdx) (Memop Quadword (%% (r8,112))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADCX (% rdx) (% rbx) *)
  0x49; 0x89; 0x50; 0x70;  (* MOV (Memop Quadword (%% (r8,112))) (% rdx) *)
  0x49; 0x8b; 0x50; 0x78;  (* MOV (% rdx) (Memop Quadword (%% (r8,120))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADCX (% rdx) (% rbx) *)
  0x49; 0x89; 0x50; 0x78;  (* MOV (Memop Quadword (%% (r8,120))) (% rdx) *)
  0x48; 0x8b; 0x01;        (* MOV (% rax) (Memop Quadword (%% (rcx,0))) *)
  0x48; 0x2b; 0x41; 0x80;  (* SUB (% rax) (Memop Quadword (%% (rcx,18446744073709551488))) *)
  0x49; 0x89; 0x80; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (r8,128))) (% rax) *)
  0x48; 0x8b; 0x41; 0x08;  (* MOV (% rax) (Memop Quadword (%% (rcx,8))) *)
  0x48; 0x1b; 0x41; 0x88;  (* SBB (% rax) (Memop Quadword (%% (rcx,18446744073709551496))) *)
  0x49; 0x89; 0x80; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (r8,136))) (% rax) *)
  0x48; 0x8b; 0x41; 0x10;  (* MOV (% rax) (Memop Quadword (%% (rcx,16))) *)
  0x48; 0x1b; 0x41; 0x90;  (* SBB (% rax) (Memop Quadword (%% (rcx,18446744073709551504))) *)
  0x49; 0x89; 0x80; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (r8,144))) (% rax) *)
  0x48; 0x8b; 0x41; 0x18;  (* MOV (% rax) (Memop Quadword (%% (rcx,24))) *)
  0x48; 0x1b; 0x41; 0x98;  (* SBB (% rax) (Memop Quadword (%% (rcx,18446744073709551512))) *)
  0x49; 0x89; 0x80; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (r8,152))) (% rax) *)
  0x48; 0x8b; 0x41; 0x20;  (* MOV (% rax) (Memop Quadword (%% (rcx,32))) *)
  0x48; 0x1b; 0x41; 0xa0;  (* SBB (% rax) (Memop Quadword (%% (rcx,18446744073709551520))) *)
  0x49; 0x89; 0x80; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (r8,160))) (% rax) *)
  0x48; 0x8b; 0x41; 0x28;  (* MOV (% rax) (Memop Quadword (%% (rcx,40))) *)
  0x48; 0x1b; 0x41; 0xa8;  (* SBB (% rax) (Memop Quadword (%% (rcx,18446744073709551528))) *)
  0x49; 0x89; 0x80; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (r8,168))) (% rax) *)
  0x48; 0x8b; 0x41; 0x30;  (* MOV (% rax) (Memop Quadword (%% (rcx,48))) *)
  0x48; 0x1b; 0x41; 0xb0;  (* SBB (% rax) (Memop Quadword (%% (rcx,18446744073709551536))) *)
  0x49; 0x89; 0x80; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (r8,176))) (% rax) *)
  0x48; 0x8b; 0x41; 0x38;  (* MOV (% rax) (Memop Quadword (%% (rcx,56))) *)
  0x48; 0x1b; 0x41; 0xb8;  (* SBB (% rax) (Memop Quadword (%% (rcx,18446744073709551544))) *)
  0x49; 0x89; 0x80; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (r8,184))) (% rax) *)
  0x48; 0x8b; 0x41; 0x40;  (* MOV (% rax) (Memop Quadword (%% (rcx,64))) *)
  0x48; 0x1b; 0x41; 0xc0;  (* SBB (% rax) (Memop Quadword (%% (rcx,18446744073709551552))) *)
  0x49; 0x89; 0x80; 0xc0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (r8,192))) (% rax) *)
  0x48; 0x8b; 0x41; 0x48;  (* MOV (% rax) (Memop Quadword (%% (rcx,72))) *)
  0x48; 0x1b; 0x41; 0xc8;  (* SBB (% rax) (Memop Quadword (%% (rcx,18446744073709551560))) *)
  0x49; 0x89; 0x80; 0xc8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (r8,200))) (% rax) *)
  0x48; 0x8b; 0x41; 0x50;  (* MOV (% rax) (Memop Quadword (%% (rcx,80))) *)
  0x48; 0x1b; 0x41; 0xd0;  (* SBB (% rax) (Memop Quadword (%% (rcx,18446744073709551568))) *)
  0x49; 0x89; 0x80; 0xd0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (r8,208))) (% rax) *)
  0x48; 0x8b; 0x41; 0x58;  (* MOV (% rax) (Memop Quadword (%% (rcx,88))) *)
  0x48; 0x1b; 0x41; 0xd8;  (* SBB (% rax) (Memop Quadword (%% (rcx,18446744073709551576))) *)
  0x49; 0x89; 0x80; 0xd8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (r8,216))) (% rax) *)
  0x48; 0x8b; 0x41; 0x60;  (* MOV (% rax) (Memop Quadword (%% (rcx,96))) *)
  0x48; 0x1b; 0x41; 0xe0;  (* SBB (% rax) (Memop Quadword (%% (rcx,18446744073709551584))) *)
  0x49; 0x89; 0x80; 0xe0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (r8,224))) (% rax) *)
  0x48; 0x8b; 0x41; 0x68;  (* MOV (% rax) (Memop Quadword (%% (rcx,104))) *)
  0x48; 0x1b; 0x41; 0xe8;  (* SBB (% rax) (Memop Quadword (%% (rcx,18446744073709551592))) *)
  0x49; 0x89; 0x80; 0xe8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (r8,232))) (% rax) *)
  0x48; 0x8b; 0x41; 0x70;  (* MOV (% rax) (Memop Quadword (%% (rcx,112))) *)
  0x48; 0x1b; 0x41; 0xf0;  (* SBB (% rax) (Memop Quadword (%% (rcx,18446744073709551600))) *)
  0x49; 0x89; 0x80; 0xf0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (r8,240))) (% rax) *)
  0x48; 0x8b; 0x41; 0x78;  (* MOV (% rax) (Memop Quadword (%% (rcx,120))) *)
  0x48; 0x1b; 0x41; 0xf8;  (* SBB (% rax) (Memop Quadword (%% (rcx,18446744073709551608))) *)
  0x49; 0x89; 0x80; 0xf8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (r8,248))) (% rax) *)
  0xbb; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% ebx) (Imm32 (word 0)) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x49; 0x8b; 0x90; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (r8,128))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADCX (% rdx) (% rbx) *)
  0x49; 0x89; 0x90; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (r8,128))) (% rdx) *)
  0x49; 0x8b; 0x90; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (r8,136))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADCX (% rdx) (% rbx) *)
  0x49; 0x89; 0x90; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (r8,136))) (% rdx) *)
  0x49; 0x8b; 0x90; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (r8,144))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADCX (% rdx) (% rbx) *)
  0x49; 0x89; 0x90; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (r8,144))) (% rdx) *)
  0x49; 0x8b; 0x90; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (r8,152))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADCX (% rdx) (% rbx) *)
  0x49; 0x89; 0x90; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (r8,152))) (% rdx) *)
  0x49; 0x8b; 0x90; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (r8,160))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADCX (% rdx) (% rbx) *)
  0x49; 0x89; 0x90; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (r8,160))) (% rdx) *)
  0x49; 0x8b; 0x90; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (r8,168))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADCX (% rdx) (% rbx) *)
  0x49; 0x89; 0x90; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (r8,168))) (% rdx) *)
  0x49; 0x8b; 0x90; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (r8,176))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADCX (% rdx) (% rbx) *)
  0x49; 0x89; 0x90; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (r8,176))) (% rdx) *)
  0x49; 0x8b; 0x90; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (r8,184))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADCX (% rdx) (% rbx) *)
  0x49; 0x89; 0x90; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (r8,184))) (% rdx) *)
  0x49; 0x8b; 0x90; 0xc0; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (r8,192))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADCX (% rdx) (% rbx) *)
  0x49; 0x89; 0x90; 0xc0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (r8,192))) (% rdx) *)
  0x49; 0x8b; 0x90; 0xc8; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (r8,200))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADCX (% rdx) (% rbx) *)
  0x49; 0x89; 0x90; 0xc8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (r8,200))) (% rdx) *)
  0x49; 0x8b; 0x90; 0xd0; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (r8,208))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADCX (% rdx) (% rbx) *)
  0x49; 0x89; 0x90; 0xd0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (r8,208))) (% rdx) *)
  0x49; 0x8b; 0x90; 0xd8; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (r8,216))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADCX (% rdx) (% rbx) *)
  0x49; 0x89; 0x90; 0xd8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (r8,216))) (% rdx) *)
  0x49; 0x8b; 0x90; 0xe0; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (r8,224))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADCX (% rdx) (% rbx) *)
  0x49; 0x89; 0x90; 0xe0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (r8,224))) (% rdx) *)
  0x49; 0x8b; 0x90; 0xe8; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (r8,232))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADCX (% rdx) (% rbx) *)
  0x49; 0x89; 0x90; 0xe8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (r8,232))) (% rdx) *)
  0x49; 0x8b; 0x90; 0xf0; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (r8,240))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADCX (% rdx) (% rbx) *)
  0x49; 0x89; 0x90; 0xf0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (r8,240))) (% rdx) *)
  0x49; 0x8b; 0x90; 0xf8; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (r8,248))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADCX (% rdx) (% rbx) *)
  0x49; 0x89; 0x90; 0xf8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (r8,248))) (% rdx) *)
  0x49; 0x31; 0xe9;        (* XOR (% r9) (% rbp) *)
  0x4d; 0x89; 0x88; 0x00; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (r8,512))) (% r9) *)
  0x4c; 0x89; 0xc1;        (* MOV (% rcx) (% r8) *)
  0x49; 0x8d; 0xb0; 0x80; 0x00; 0x00; 0x00;
                           (* LEA (% rsi) (%% (r8,128)) *)
  0x49; 0x8d; 0xb8; 0x00; 0x01; 0x00; 0x00;
                           (* LEA (% rdi) (%% (r8,256)) *)
  0xe8; 0x8e; 0x08; 0x00; 0x00;
                           (* CALL (Imm32 (word 2190)) *)
  0x48; 0x8b; 0x3c; 0x24;  (* MOV (% rdi) (Memop Quadword (%% (rsp,0))) *)
  0x31; 0xdb;              (* XOR (% ebx) (% ebx) *)
  0x48; 0x8b; 0x87; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rdi,128))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x07;
                           (* ADCX (% rax) (Memop Quadword (%% (rdi,0))) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0x00; 0x01; 0x00; 0x00;
                           (* ADOX (% rax) (Memop Quadword (%% (rdi,256))) *)
  0x48; 0x89; 0x01;        (* MOV (Memop Quadword (%% (rcx,0))) (% rax) *)
  0x48; 0x8b; 0x87; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rdi,136))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x47; 0x08;
                           (* ADCX (% rax) (Memop Quadword (%% (rdi,8))) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0x08; 0x01; 0x00; 0x00;
                           (* ADOX (% rax) (Memop Quadword (%% (rdi,264))) *)
  0x48; 0x89; 0x41; 0x08;  (* MOV (Memop Quadword (%% (rcx,8))) (% rax) *)
  0x48; 0x8b; 0x87; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rdi,144))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x47; 0x10;
                           (* ADCX (% rax) (Memop Quadword (%% (rdi,16))) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0x10; 0x01; 0x00; 0x00;
                           (* ADOX (% rax) (Memop Quadword (%% (rdi,272))) *)
  0x48; 0x89; 0x41; 0x10;  (* MOV (Memop Quadword (%% (rcx,16))) (% rax) *)
  0x48; 0x8b; 0x87; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rdi,152))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x47; 0x18;
                           (* ADCX (% rax) (Memop Quadword (%% (rdi,24))) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0x18; 0x01; 0x00; 0x00;
                           (* ADOX (% rax) (Memop Quadword (%% (rdi,280))) *)
  0x48; 0x89; 0x41; 0x18;  (* MOV (Memop Quadword (%% (rcx,24))) (% rax) *)
  0x48; 0x8b; 0x87; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rdi,160))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x47; 0x20;
                           (* ADCX (% rax) (Memop Quadword (%% (rdi,32))) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0x20; 0x01; 0x00; 0x00;
                           (* ADOX (% rax) (Memop Quadword (%% (rdi,288))) *)
  0x48; 0x89; 0x41; 0x20;  (* MOV (Memop Quadword (%% (rcx,32))) (% rax) *)
  0x48; 0x8b; 0x87; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rdi,168))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x47; 0x28;
                           (* ADCX (% rax) (Memop Quadword (%% (rdi,40))) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0x28; 0x01; 0x00; 0x00;
                           (* ADOX (% rax) (Memop Quadword (%% (rdi,296))) *)
  0x48; 0x89; 0x41; 0x28;  (* MOV (Memop Quadword (%% (rcx,40))) (% rax) *)
  0x48; 0x8b; 0x87; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rdi,176))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x47; 0x30;
                           (* ADCX (% rax) (Memop Quadword (%% (rdi,48))) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0x30; 0x01; 0x00; 0x00;
                           (* ADOX (% rax) (Memop Quadword (%% (rdi,304))) *)
  0x48; 0x89; 0x41; 0x30;  (* MOV (Memop Quadword (%% (rcx,48))) (% rax) *)
  0x48; 0x8b; 0x87; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rdi,184))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x47; 0x38;
                           (* ADCX (% rax) (Memop Quadword (%% (rdi,56))) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0x38; 0x01; 0x00; 0x00;
                           (* ADOX (% rax) (Memop Quadword (%% (rdi,312))) *)
  0x48; 0x89; 0x41; 0x38;  (* MOV (Memop Quadword (%% (rcx,56))) (% rax) *)
  0x48; 0x8b; 0x87; 0xc0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rdi,192))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x47; 0x40;
                           (* ADCX (% rax) (Memop Quadword (%% (rdi,64))) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0x40; 0x01; 0x00; 0x00;
                           (* ADOX (% rax) (Memop Quadword (%% (rdi,320))) *)
  0x48; 0x89; 0x41; 0x40;  (* MOV (Memop Quadword (%% (rcx,64))) (% rax) *)
  0x48; 0x8b; 0x87; 0xc8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rdi,200))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x47; 0x48;
                           (* ADCX (% rax) (Memop Quadword (%% (rdi,72))) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0x48; 0x01; 0x00; 0x00;
                           (* ADOX (% rax) (Memop Quadword (%% (rdi,328))) *)
  0x48; 0x89; 0x41; 0x48;  (* MOV (Memop Quadword (%% (rcx,72))) (% rax) *)
  0x48; 0x8b; 0x87; 0xd0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rdi,208))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x47; 0x50;
                           (* ADCX (% rax) (Memop Quadword (%% (rdi,80))) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0x50; 0x01; 0x00; 0x00;
                           (* ADOX (% rax) (Memop Quadword (%% (rdi,336))) *)
  0x48; 0x89; 0x41; 0x50;  (* MOV (Memop Quadword (%% (rcx,80))) (% rax) *)
  0x48; 0x8b; 0x87; 0xd8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rdi,216))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x47; 0x58;
                           (* ADCX (% rax) (Memop Quadword (%% (rdi,88))) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0x58; 0x01; 0x00; 0x00;
                           (* ADOX (% rax) (Memop Quadword (%% (rdi,344))) *)
  0x48; 0x89; 0x41; 0x58;  (* MOV (Memop Quadword (%% (rcx,88))) (% rax) *)
  0x48; 0x8b; 0x87; 0xe0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rdi,224))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x47; 0x60;
                           (* ADCX (% rax) (Memop Quadword (%% (rdi,96))) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0x60; 0x01; 0x00; 0x00;
                           (* ADOX (% rax) (Memop Quadword (%% (rdi,352))) *)
  0x48; 0x89; 0x41; 0x60;  (* MOV (Memop Quadword (%% (rcx,96))) (% rax) *)
  0x48; 0x8b; 0x87; 0xe8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rdi,232))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x47; 0x68;
                           (* ADCX (% rax) (Memop Quadword (%% (rdi,104))) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0x68; 0x01; 0x00; 0x00;
                           (* ADOX (% rax) (Memop Quadword (%% (rdi,360))) *)
  0x48; 0x89; 0x41; 0x68;  (* MOV (Memop Quadword (%% (rcx,104))) (% rax) *)
  0x48; 0x8b; 0x87; 0xf0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rdi,240))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x47; 0x70;
                           (* ADCX (% rax) (Memop Quadword (%% (rdi,112))) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0x70; 0x01; 0x00; 0x00;
                           (* ADOX (% rax) (Memop Quadword (%% (rdi,368))) *)
  0x48; 0x89; 0x41; 0x70;  (* MOV (Memop Quadword (%% (rcx,112))) (% rax) *)
  0x48; 0x8b; 0x87; 0xf8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rdi,248))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x47; 0x78;
                           (* ADCX (% rax) (Memop Quadword (%% (rdi,120))) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0x78; 0x01; 0x00; 0x00;
                           (* ADOX (% rax) (Memop Quadword (%% (rdi,376))) *)
  0x48; 0x89; 0x41; 0x78;  (* MOV (Memop Quadword (%% (rcx,120))) (% rax) *)
  0x48; 0x8b; 0x87; 0x00; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rdi,256))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0x80; 0x00; 0x00; 0x00;
                           (* ADCX (% rax) (Memop Quadword (%% (rdi,128))) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0x80; 0x01; 0x00; 0x00;
                           (* ADOX (% rax) (Memop Quadword (%% (rdi,384))) *)
  0x48; 0x89; 0x81; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rcx,128))) (% rax) *)
  0x48; 0x8b; 0x87; 0x08; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rdi,264))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0x88; 0x00; 0x00; 0x00;
                           (* ADCX (% rax) (Memop Quadword (%% (rdi,136))) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0x88; 0x01; 0x00; 0x00;
                           (* ADOX (% rax) (Memop Quadword (%% (rdi,392))) *)
  0x48; 0x89; 0x81; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rcx,136))) (% rax) *)
  0x48; 0x8b; 0x87; 0x10; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rdi,272))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0x90; 0x00; 0x00; 0x00;
                           (* ADCX (% rax) (Memop Quadword (%% (rdi,144))) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0x90; 0x01; 0x00; 0x00;
                           (* ADOX (% rax) (Memop Quadword (%% (rdi,400))) *)
  0x48; 0x89; 0x81; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rcx,144))) (% rax) *)
  0x48; 0x8b; 0x87; 0x18; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rdi,280))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0x98; 0x00; 0x00; 0x00;
                           (* ADCX (% rax) (Memop Quadword (%% (rdi,152))) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0x98; 0x01; 0x00; 0x00;
                           (* ADOX (% rax) (Memop Quadword (%% (rdi,408))) *)
  0x48; 0x89; 0x81; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rcx,152))) (% rax) *)
  0x48; 0x8b; 0x87; 0x20; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rdi,288))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0xa0; 0x00; 0x00; 0x00;
                           (* ADCX (% rax) (Memop Quadword (%% (rdi,160))) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0xa0; 0x01; 0x00; 0x00;
                           (* ADOX (% rax) (Memop Quadword (%% (rdi,416))) *)
  0x48; 0x89; 0x81; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rcx,160))) (% rax) *)
  0x48; 0x8b; 0x87; 0x28; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rdi,296))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0xa8; 0x00; 0x00; 0x00;
                           (* ADCX (% rax) (Memop Quadword (%% (rdi,168))) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0xa8; 0x01; 0x00; 0x00;
                           (* ADOX (% rax) (Memop Quadword (%% (rdi,424))) *)
  0x48; 0x89; 0x81; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rcx,168))) (% rax) *)
  0x48; 0x8b; 0x87; 0x30; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rdi,304))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0xb0; 0x00; 0x00; 0x00;
                           (* ADCX (% rax) (Memop Quadword (%% (rdi,176))) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0xb0; 0x01; 0x00; 0x00;
                           (* ADOX (% rax) (Memop Quadword (%% (rdi,432))) *)
  0x48; 0x89; 0x81; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rcx,176))) (% rax) *)
  0x48; 0x8b; 0x87; 0x38; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rdi,312))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0xb8; 0x00; 0x00; 0x00;
                           (* ADCX (% rax) (Memop Quadword (%% (rdi,184))) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0xb8; 0x01; 0x00; 0x00;
                           (* ADOX (% rax) (Memop Quadword (%% (rdi,440))) *)
  0x48; 0x89; 0x81; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rcx,184))) (% rax) *)
  0x48; 0x8b; 0x87; 0x40; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rdi,320))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0xc0; 0x00; 0x00; 0x00;
                           (* ADCX (% rax) (Memop Quadword (%% (rdi,192))) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0xc0; 0x01; 0x00; 0x00;
                           (* ADOX (% rax) (Memop Quadword (%% (rdi,448))) *)
  0x48; 0x89; 0x81; 0xc0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rcx,192))) (% rax) *)
  0x48; 0x8b; 0x87; 0x48; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rdi,328))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0xc8; 0x00; 0x00; 0x00;
                           (* ADCX (% rax) (Memop Quadword (%% (rdi,200))) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0xc8; 0x01; 0x00; 0x00;
                           (* ADOX (% rax) (Memop Quadword (%% (rdi,456))) *)
  0x48; 0x89; 0x81; 0xc8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rcx,200))) (% rax) *)
  0x48; 0x8b; 0x87; 0x50; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rdi,336))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0xd0; 0x00; 0x00; 0x00;
                           (* ADCX (% rax) (Memop Quadword (%% (rdi,208))) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0xd0; 0x01; 0x00; 0x00;
                           (* ADOX (% rax) (Memop Quadword (%% (rdi,464))) *)
  0x48; 0x89; 0x81; 0xd0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rcx,208))) (% rax) *)
  0x48; 0x8b; 0x87; 0x58; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rdi,344))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0xd8; 0x00; 0x00; 0x00;
                           (* ADCX (% rax) (Memop Quadword (%% (rdi,216))) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0xd8; 0x01; 0x00; 0x00;
                           (* ADOX (% rax) (Memop Quadword (%% (rdi,472))) *)
  0x48; 0x89; 0x81; 0xd8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rcx,216))) (% rax) *)
  0x48; 0x8b; 0x87; 0x60; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rdi,352))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0xe0; 0x00; 0x00; 0x00;
                           (* ADCX (% rax) (Memop Quadword (%% (rdi,224))) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0xe0; 0x01; 0x00; 0x00;
                           (* ADOX (% rax) (Memop Quadword (%% (rdi,480))) *)
  0x48; 0x89; 0x81; 0xe0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rcx,224))) (% rax) *)
  0x48; 0x8b; 0x87; 0x68; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rdi,360))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0xe8; 0x00; 0x00; 0x00;
                           (* ADCX (% rax) (Memop Quadword (%% (rdi,232))) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0xe8; 0x01; 0x00; 0x00;
                           (* ADOX (% rax) (Memop Quadword (%% (rdi,488))) *)
  0x48; 0x89; 0x81; 0xe8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rcx,232))) (% rax) *)
  0x48; 0x8b; 0x87; 0x70; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rdi,368))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0xf0; 0x00; 0x00; 0x00;
                           (* ADCX (% rax) (Memop Quadword (%% (rdi,240))) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0xf0; 0x01; 0x00; 0x00;
                           (* ADOX (% rax) (Memop Quadword (%% (rdi,496))) *)
  0x48; 0x89; 0x81; 0xf0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rcx,240))) (% rax) *)
  0x48; 0x8b; 0x87; 0x78; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rdi,376))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0xf8; 0x00; 0x00; 0x00;
                           (* ADCX (% rax) (Memop Quadword (%% (rdi,248))) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0xf8; 0x01; 0x00; 0x00;
                           (* ADOX (% rax) (Memop Quadword (%% (rdi,504))) *)
  0x48; 0x89; 0x81; 0xf8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rcx,248))) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% rbx) (% rbx) *)
  0x48; 0x83; 0xd3; 0x00;  (* ADC (% rbx) (Imm8 (word 0)) *)
  0x4c; 0x8b; 0x89; 0x00; 0x02; 0x00; 0x00;
                           (* MOV (% r9) (Memop Quadword (%% (rcx,512))) *)
  0x49; 0xf7; 0xd9;        (* NEG (% r9) *)
  0x49; 0xf7; 0xd9;        (* NEG (% r9) *)
  0x48; 0x8b; 0x91; 0x00; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rcx,256))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x11;
                           (* ADCX (% rdx) (Memop Quadword (%% (rcx,0))) *)
  0x48; 0x89; 0x97; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,128))) (% rdx) *)
  0x48; 0x8b; 0x91; 0x08; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rcx,264))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x51; 0x08;
                           (* ADCX (% rdx) (Memop Quadword (%% (rcx,8))) *)
  0x48; 0x89; 0x97; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,136))) (% rdx) *)
  0x48; 0x8b; 0x91; 0x10; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rcx,272))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x51; 0x10;
                           (* ADCX (% rdx) (Memop Quadword (%% (rcx,16))) *)
  0x48; 0x89; 0x97; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,144))) (% rdx) *)
  0x48; 0x8b; 0x91; 0x18; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rcx,280))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x51; 0x18;
                           (* ADCX (% rdx) (Memop Quadword (%% (rcx,24))) *)
  0x48; 0x89; 0x97; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,152))) (% rdx) *)
  0x48; 0x8b; 0x91; 0x20; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rcx,288))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x51; 0x20;
                           (* ADCX (% rdx) (Memop Quadword (%% (rcx,32))) *)
  0x48; 0x89; 0x97; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,160))) (% rdx) *)
  0x48; 0x8b; 0x91; 0x28; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rcx,296))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x51; 0x28;
                           (* ADCX (% rdx) (Memop Quadword (%% (rcx,40))) *)
  0x48; 0x89; 0x97; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,168))) (% rdx) *)
  0x48; 0x8b; 0x91; 0x30; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rcx,304))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x51; 0x30;
                           (* ADCX (% rdx) (Memop Quadword (%% (rcx,48))) *)
  0x48; 0x89; 0x97; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,176))) (% rdx) *)
  0x48; 0x8b; 0x91; 0x38; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rcx,312))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x51; 0x38;
                           (* ADCX (% rdx) (Memop Quadword (%% (rcx,56))) *)
  0x48; 0x89; 0x97; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,184))) (% rdx) *)
  0x48; 0x8b; 0x91; 0x40; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rcx,320))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x51; 0x40;
                           (* ADCX (% rdx) (Memop Quadword (%% (rcx,64))) *)
  0x48; 0x89; 0x97; 0xc0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,192))) (% rdx) *)
  0x48; 0x8b; 0x91; 0x48; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rcx,328))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x51; 0x48;
                           (* ADCX (% rdx) (Memop Quadword (%% (rcx,72))) *)
  0x48; 0x89; 0x97; 0xc8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,200))) (% rdx) *)
  0x48; 0x8b; 0x91; 0x50; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rcx,336))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x51; 0x50;
                           (* ADCX (% rdx) (Memop Quadword (%% (rcx,80))) *)
  0x48; 0x89; 0x97; 0xd0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,208))) (% rdx) *)
  0x48; 0x8b; 0x91; 0x58; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rcx,344))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x51; 0x58;
                           (* ADCX (% rdx) (Memop Quadword (%% (rcx,88))) *)
  0x48; 0x89; 0x97; 0xd8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,216))) (% rdx) *)
  0x48; 0x8b; 0x91; 0x60; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rcx,352))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x51; 0x60;
                           (* ADCX (% rdx) (Memop Quadword (%% (rcx,96))) *)
  0x48; 0x89; 0x97; 0xe0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,224))) (% rdx) *)
  0x48; 0x8b; 0x91; 0x68; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rcx,360))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x51; 0x68;
                           (* ADCX (% rdx) (Memop Quadword (%% (rcx,104))) *)
  0x48; 0x89; 0x97; 0xe8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,232))) (% rdx) *)
  0x48; 0x8b; 0x91; 0x70; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rcx,368))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x51; 0x70;
                           (* ADCX (% rdx) (Memop Quadword (%% (rcx,112))) *)
  0x48; 0x89; 0x97; 0xf0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,240))) (% rdx) *)
  0x48; 0x8b; 0x91; 0x78; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rcx,376))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x51; 0x78;
                           (* ADCX (% rdx) (Memop Quadword (%% (rcx,120))) *)
  0x48; 0x89; 0x97; 0xf8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,248))) (% rdx) *)
  0x48; 0x8b; 0x91; 0x80; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rcx,384))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x91; 0x80; 0x00; 0x00; 0x00;
                           (* ADCX (% rdx) (Memop Quadword (%% (rcx,128))) *)
  0x48; 0x89; 0x97; 0x00; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,256))) (% rdx) *)
  0x48; 0x8b; 0x91; 0x88; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rcx,392))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x91; 0x88; 0x00; 0x00; 0x00;
                           (* ADCX (% rdx) (Memop Quadword (%% (rcx,136))) *)
  0x48; 0x89; 0x97; 0x08; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,264))) (% rdx) *)
  0x48; 0x8b; 0x91; 0x90; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rcx,400))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x91; 0x90; 0x00; 0x00; 0x00;
                           (* ADCX (% rdx) (Memop Quadword (%% (rcx,144))) *)
  0x48; 0x89; 0x97; 0x10; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,272))) (% rdx) *)
  0x48; 0x8b; 0x91; 0x98; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rcx,408))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x91; 0x98; 0x00; 0x00; 0x00;
                           (* ADCX (% rdx) (Memop Quadword (%% (rcx,152))) *)
  0x48; 0x89; 0x97; 0x18; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,280))) (% rdx) *)
  0x48; 0x8b; 0x91; 0xa0; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rcx,416))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x91; 0xa0; 0x00; 0x00; 0x00;
                           (* ADCX (% rdx) (Memop Quadword (%% (rcx,160))) *)
  0x48; 0x89; 0x97; 0x20; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,288))) (% rdx) *)
  0x48; 0x8b; 0x91; 0xa8; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rcx,424))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x91; 0xa8; 0x00; 0x00; 0x00;
                           (* ADCX (% rdx) (Memop Quadword (%% (rcx,168))) *)
  0x48; 0x89; 0x97; 0x28; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,296))) (% rdx) *)
  0x48; 0x8b; 0x91; 0xb0; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rcx,432))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x91; 0xb0; 0x00; 0x00; 0x00;
                           (* ADCX (% rdx) (Memop Quadword (%% (rcx,176))) *)
  0x48; 0x89; 0x97; 0x30; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,304))) (% rdx) *)
  0x48; 0x8b; 0x91; 0xb8; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rcx,440))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x91; 0xb8; 0x00; 0x00; 0x00;
                           (* ADCX (% rdx) (Memop Quadword (%% (rcx,184))) *)
  0x48; 0x89; 0x97; 0x38; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,312))) (% rdx) *)
  0x48; 0x8b; 0x91; 0xc0; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rcx,448))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x91; 0xc0; 0x00; 0x00; 0x00;
                           (* ADCX (% rdx) (Memop Quadword (%% (rcx,192))) *)
  0x48; 0x89; 0x97; 0x40; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,320))) (% rdx) *)
  0x48; 0x8b; 0x91; 0xc8; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rcx,456))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x91; 0xc8; 0x00; 0x00; 0x00;
                           (* ADCX (% rdx) (Memop Quadword (%% (rcx,200))) *)
  0x48; 0x89; 0x97; 0x48; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,328))) (% rdx) *)
  0x48; 0x8b; 0x91; 0xd0; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rcx,464))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x91; 0xd0; 0x00; 0x00; 0x00;
                           (* ADCX (% rdx) (Memop Quadword (%% (rcx,208))) *)
  0x48; 0x89; 0x97; 0x50; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,336))) (% rdx) *)
  0x48; 0x8b; 0x91; 0xd8; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rcx,472))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x91; 0xd8; 0x00; 0x00; 0x00;
                           (* ADCX (% rdx) (Memop Quadword (%% (rcx,216))) *)
  0x48; 0x89; 0x97; 0x58; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,344))) (% rdx) *)
  0x48; 0x8b; 0x91; 0xe0; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rcx,480))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x91; 0xe0; 0x00; 0x00; 0x00;
                           (* ADCX (% rdx) (Memop Quadword (%% (rcx,224))) *)
  0x48; 0x89; 0x97; 0x60; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,352))) (% rdx) *)
  0x48; 0x8b; 0x91; 0xe8; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rcx,488))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x91; 0xe8; 0x00; 0x00; 0x00;
                           (* ADCX (% rdx) (Memop Quadword (%% (rcx,232))) *)
  0x48; 0x89; 0x97; 0x68; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,360))) (% rdx) *)
  0x48; 0x8b; 0x91; 0xf0; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rcx,496))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x91; 0xf0; 0x00; 0x00; 0x00;
                           (* ADCX (% rdx) (Memop Quadword (%% (rcx,240))) *)
  0x48; 0x89; 0x97; 0x70; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,368))) (% rdx) *)
  0x48; 0x8b; 0x91; 0xf8; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rcx,504))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x91; 0xf8; 0x00; 0x00; 0x00;
                           (* ADCX (% rdx) (Memop Quadword (%% (rcx,248))) *)
  0x48; 0x89; 0x97; 0x78; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,376))) (% rdx) *)
  0x66; 0x49; 0x0f; 0x38; 0xf6; 0xd9;
                           (* ADCX (% rbx) (% r9) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0x48; 0x01; 0x9f; 0x80; 0x01; 0x00; 0x00;
                           (* ADD (Memop Quadword (%% (rdi,384))) (% rbx) *)
  0x48; 0x11; 0x87; 0x88; 0x01; 0x00; 0x00;
                           (* ADC (Memop Quadword (%% (rdi,392))) (% rax) *)
  0x48; 0x11; 0x87; 0x90; 0x01; 0x00; 0x00;
                           (* ADC (Memop Quadword (%% (rdi,400))) (% rax) *)
  0x48; 0x11; 0x87; 0x98; 0x01; 0x00; 0x00;
                           (* ADC (Memop Quadword (%% (rdi,408))) (% rax) *)
  0x48; 0x11; 0x87; 0xa0; 0x01; 0x00; 0x00;
                           (* ADC (Memop Quadword (%% (rdi,416))) (% rax) *)
  0x48; 0x11; 0x87; 0xa8; 0x01; 0x00; 0x00;
                           (* ADC (Memop Quadword (%% (rdi,424))) (% rax) *)
  0x48; 0x11; 0x87; 0xb0; 0x01; 0x00; 0x00;
                           (* ADC (Memop Quadword (%% (rdi,432))) (% rax) *)
  0x48; 0x11; 0x87; 0xb8; 0x01; 0x00; 0x00;
                           (* ADC (Memop Quadword (%% (rdi,440))) (% rax) *)
  0x48; 0x11; 0x87; 0xc0; 0x01; 0x00; 0x00;
                           (* ADC (Memop Quadword (%% (rdi,448))) (% rax) *)
  0x48; 0x11; 0x87; 0xc8; 0x01; 0x00; 0x00;
                           (* ADC (Memop Quadword (%% (rdi,456))) (% rax) *)
  0x48; 0x11; 0x87; 0xd0; 0x01; 0x00; 0x00;
                           (* ADC (Memop Quadword (%% (rdi,464))) (% rax) *)
  0x48; 0x11; 0x87; 0xd8; 0x01; 0x00; 0x00;
                           (* ADC (Memop Quadword (%% (rdi,472))) (% rax) *)
  0x48; 0x11; 0x87; 0xe0; 0x01; 0x00; 0x00;
                           (* ADC (Memop Quadword (%% (rdi,480))) (% rax) *)
  0x48; 0x11; 0x87; 0xe8; 0x01; 0x00; 0x00;
                           (* ADC (Memop Quadword (%% (rdi,488))) (% rax) *)
  0x48; 0x11; 0x87; 0xf0; 0x01; 0x00; 0x00;
                           (* ADC (Memop Quadword (%% (rdi,496))) (% rax) *)
  0x48; 0x11; 0x87; 0xf8; 0x01; 0x00; 0x00;
                           (* ADC (Memop Quadword (%% (rdi,504))) (% rax) *)
  0x59;                    (* POP (% rcx) *)
  0x41; 0x5f;              (* POP (% r15) *)
  0x41; 0x5e;              (* POP (% r14) *)
  0x41; 0x5d;              (* POP (% r13) *)
  0x41; 0x5c;              (* POP (% r12) *)
  0x5d;                    (* POP (% rbp) *)
  0x5b;                    (* POP (% rbx) *)
  0xc3;                    (* RET *)
  0x48; 0x8b; 0x11;        (* MOV (% rdx) (Memop Quadword (%% (rcx,0))) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x0e;
                           (* MULX4 (% r9,% rax) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x48; 0x89; 0x07;        (* MOV (Memop Quadword (%% (rdi,0))) (% rax) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x56; 0x08;
                           (* MULX4 (% r10,% rax) (% rdx,Memop Quadword (%% (rsi,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x5e; 0x10;
                           (* MULX4 (% r11,% rax) (% rdx,Memop Quadword (%% (rsi,16))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x66; 0x18;
                           (* MULX4 (% r12,% rax) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x6e; 0x20;
                           (* MULX4 (% r13,% rax) (% rdx,Memop Quadword (%% (rsi,32))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x76; 0x28;
                           (* MULX4 (% r14,% rax) (% rdx,Memop Quadword (%% (rsi,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x7e; 0x30;
                           (* MULX4 (% r15,% rax) (% rdx,Memop Quadword (%% (rsi,48))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x46; 0x38;
                           (* MULX4 (% r8,% rax) (% rdx,Memop Quadword (%% (rsi,56))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0x49; 0x11; 0xe8;        (* ADC (% r8) (% rbp) *)
  0x48; 0x8b; 0x51; 0x08;  (* MOV (% rdx) (Memop Quadword (%% (rcx,8))) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1e;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0x4c; 0x89; 0x4f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% r9) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x08;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x10;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,16))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x18;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x20;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,32))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x28;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x30;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,48))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x4e; 0x38;
                           (* MULX4 (% r9,% rax) (% rdx,Memop Quadword (%% (rsi,56))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcd;
                           (* ADOX (% r9) (% rbp) *)
  0x49; 0x11; 0xe9;        (* ADC (% r9) (% rbp) *)
  0x48; 0x8b; 0x51; 0x10;  (* MOV (% rdx) (Memop Quadword (%% (rcx,16))) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1e;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0x4c; 0x89; 0x57; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r10) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x08;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x10;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,16))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x18;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x20;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,32))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x28;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x30;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,48))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x56; 0x38;
                           (* MULX4 (% r10,% rax) (% rdx,Memop Quadword (%% (rsi,56))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd5;
                           (* ADOX (% r10) (% rbp) *)
  0x49; 0x11; 0xea;        (* ADC (% r10) (% rbp) *)
  0x48; 0x8b; 0x51; 0x18;  (* MOV (% rdx) (Memop Quadword (%% (rcx,24))) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1e;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0x4c; 0x89; 0x5f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r11) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x08;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x10;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,16))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x18;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x20;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,32))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x28;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x30;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,48))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x5e; 0x38;
                           (* MULX4 (% r11,% rax) (% rdx,Memop Quadword (%% (rsi,56))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdd;
                           (* ADOX (% r11) (% rbp) *)
  0x49; 0x11; 0xeb;        (* ADC (% r11) (% rbp) *)
  0x48; 0x8b; 0x51; 0x20;  (* MOV (% rdx) (Memop Quadword (%% (rcx,32))) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1e;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0x4c; 0x89; 0x67; 0x20;  (* MOV (Memop Quadword (%% (rdi,32))) (% r12) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x08;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x10;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,16))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x18;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x20;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,32))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x28;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x30;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,48))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x66; 0x38;
                           (* MULX4 (% r12,% rax) (% rdx,Memop Quadword (%% (rsi,56))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe5;
                           (* ADOX (% r12) (% rbp) *)
  0x49; 0x11; 0xec;        (* ADC (% r12) (% rbp) *)
  0x48; 0x8b; 0x51; 0x28;  (* MOV (% rdx) (Memop Quadword (%% (rcx,40))) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1e;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0x4c; 0x89; 0x6f; 0x28;  (* MOV (Memop Quadword (%% (rdi,40))) (% r13) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x08;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x10;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,16))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x18;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x20;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,32))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x28;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x30;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,48))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x6e; 0x38;
                           (* MULX4 (% r13,% rax) (% rdx,Memop Quadword (%% (rsi,56))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xed;
                           (* ADOX (% r13) (% rbp) *)
  0x49; 0x11; 0xed;        (* ADC (% r13) (% rbp) *)
  0x48; 0x8b; 0x51; 0x30;  (* MOV (% rdx) (Memop Quadword (%% (rcx,48))) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1e;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0x4c; 0x89; 0x77; 0x30;  (* MOV (Memop Quadword (%% (rdi,48))) (% r14) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x08;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x10;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,16))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x18;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x20;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,32))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x28;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x30;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,48))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x76; 0x38;
                           (* MULX4 (% r14,% rax) (% rdx,Memop Quadword (%% (rsi,56))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf5;
                           (* ADOX (% r14) (% rbp) *)
  0x49; 0x11; 0xee;        (* ADC (% r14) (% rbp) *)
  0x48; 0x8b; 0x51; 0x38;  (* MOV (% rdx) (Memop Quadword (%% (rcx,56))) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1e;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0x4c; 0x89; 0x7f; 0x38;  (* MOV (Memop Quadword (%% (rdi,56))) (% r15) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x08;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x10;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,16))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x18;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x20;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,32))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x28;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x30;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,48))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x7e; 0x38;
                           (* MULX4 (% r15,% rax) (% rdx,Memop Quadword (%% (rsi,56))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfd;
                           (* ADOX (% r15) (% rbp) *)
  0x49; 0x11; 0xef;        (* ADC (% r15) (% rbp) *)
  0x48; 0x8b; 0x51; 0x40;  (* MOV (% rdx) (Memop Quadword (%% (rcx,64))) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1e;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0x4c; 0x89; 0x47; 0x40;  (* MOV (Memop Quadword (%% (rdi,64))) (% r8) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x08;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x10;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,16))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x18;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x20;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,32))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x28;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x30;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,48))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x46; 0x38;
                           (* MULX4 (% r8,% rax) (% rdx,Memop Quadword (%% (rsi,56))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc5;
                           (* ADOX (% r8) (% rbp) *)
  0x49; 0x11; 0xe8;        (* ADC (% r8) (% rbp) *)
  0x48; 0x8b; 0x51; 0x48;  (* MOV (% rdx) (Memop Quadword (%% (rcx,72))) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1e;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0x4c; 0x89; 0x4f; 0x48;  (* MOV (Memop Quadword (%% (rdi,72))) (% r9) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x08;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x10;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,16))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x18;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x20;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,32))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x28;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x30;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,48))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x4e; 0x38;
                           (* MULX4 (% r9,% rax) (% rdx,Memop Quadword (%% (rsi,56))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcd;
                           (* ADOX (% r9) (% rbp) *)
  0x49; 0x11; 0xe9;        (* ADC (% r9) (% rbp) *)
  0x48; 0x8b; 0x51; 0x50;  (* MOV (% rdx) (Memop Quadword (%% (rcx,80))) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1e;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0x4c; 0x89; 0x57; 0x50;  (* MOV (Memop Quadword (%% (rdi,80))) (% r10) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x08;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x10;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,16))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x18;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x20;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,32))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x28;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x30;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,48))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x56; 0x38;
                           (* MULX4 (% r10,% rax) (% rdx,Memop Quadword (%% (rsi,56))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd5;
                           (* ADOX (% r10) (% rbp) *)
  0x49; 0x11; 0xea;        (* ADC (% r10) (% rbp) *)
  0x48; 0x8b; 0x51; 0x58;  (* MOV (% rdx) (Memop Quadword (%% (rcx,88))) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1e;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0x4c; 0x89; 0x5f; 0x58;  (* MOV (Memop Quadword (%% (rdi,88))) (% r11) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x08;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x10;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,16))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x18;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x20;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,32))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x28;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x30;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,48))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x5e; 0x38;
                           (* MULX4 (% r11,% rax) (% rdx,Memop Quadword (%% (rsi,56))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdd;
                           (* ADOX (% r11) (% rbp) *)
  0x49; 0x11; 0xeb;        (* ADC (% r11) (% rbp) *)
  0x48; 0x8b; 0x51; 0x60;  (* MOV (% rdx) (Memop Quadword (%% (rcx,96))) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1e;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0x4c; 0x89; 0x67; 0x60;  (* MOV (Memop Quadword (%% (rdi,96))) (% r12) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x08;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x10;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,16))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x18;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x20;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,32))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x28;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x30;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,48))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x66; 0x38;
                           (* MULX4 (% r12,% rax) (% rdx,Memop Quadword (%% (rsi,56))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe5;
                           (* ADOX (% r12) (% rbp) *)
  0x49; 0x11; 0xec;        (* ADC (% r12) (% rbp) *)
  0x48; 0x8b; 0x51; 0x68;  (* MOV (% rdx) (Memop Quadword (%% (rcx,104))) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1e;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0x4c; 0x89; 0x6f; 0x68;  (* MOV (Memop Quadword (%% (rdi,104))) (% r13) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x08;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x10;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,16))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x18;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x20;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,32))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x28;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x30;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,48))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x6e; 0x38;
                           (* MULX4 (% r13,% rax) (% rdx,Memop Quadword (%% (rsi,56))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xed;
                           (* ADOX (% r13) (% rbp) *)
  0x49; 0x11; 0xed;        (* ADC (% r13) (% rbp) *)
  0x48; 0x8b; 0x51; 0x70;  (* MOV (% rdx) (Memop Quadword (%% (rcx,112))) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1e;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0x4c; 0x89; 0x77; 0x70;  (* MOV (Memop Quadword (%% (rdi,112))) (% r14) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x08;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x10;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,16))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x18;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x20;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,32))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x28;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x30;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,48))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x76; 0x38;
                           (* MULX4 (% r14,% rax) (% rdx,Memop Quadword (%% (rsi,56))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf5;
                           (* ADOX (% r14) (% rbp) *)
  0x49; 0x11; 0xee;        (* ADC (% r14) (% rbp) *)
  0x48; 0x8b; 0x51; 0x78;  (* MOV (% rdx) (Memop Quadword (%% (rcx,120))) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1e;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0x4c; 0x89; 0x7f; 0x78;  (* MOV (Memop Quadword (%% (rdi,120))) (% r15) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x08;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x10;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,16))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x18;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x20;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,32))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x28;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x30;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,48))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x7e; 0x38;
                           (* MULX4 (% r15,% rax) (% rdx,Memop Quadword (%% (rsi,56))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfd;
                           (* ADOX (% r15) (% rbp) *)
  0x49; 0x11; 0xef;        (* ADC (% r15) (% rbp) *)
  0x4c; 0x89; 0x87; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,128))) (% r8) *)
  0x4c; 0x89; 0x8f; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,136))) (% r9) *)
  0x4c; 0x89; 0x97; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,144))) (% r10) *)
  0x4c; 0x89; 0x9f; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,152))) (% r11) *)
  0x4c; 0x89; 0xa7; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,160))) (% r12) *)
  0x4c; 0x89; 0xaf; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,168))) (% r13) *)
  0x4c; 0x89; 0xb7; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,176))) (% r14) *)
  0x4c; 0x89; 0xbf; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,184))) (% r15) *)
  0x48; 0x83; 0xc7; 0x40;  (* ADD (% rdi) (Imm8 (word 64)) *)
  0x48; 0x83; 0xc6; 0x40;  (* ADD (% rsi) (Imm8 (word 64)) *)
  0x48; 0x8b; 0x11;        (* MOV (% rdx) (Memop Quadword (%% (rcx,0))) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0x4c; 0x8b; 0x07;        (* MOV (% r8) (Memop Quadword (%% (rdi,0))) *)
  0x4c; 0x8b; 0x4f; 0x08;  (* MOV (% r9) (Memop Quadword (%% (rdi,8))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1e;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0x4c; 0x89; 0x07;        (* MOV (Memop Quadword (%% (rdi,0))) (% r8) *)
  0x4c; 0x8b; 0x57; 0x10;  (* MOV (% r10) (Memop Quadword (%% (rdi,16))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x08;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0x4c; 0x8b; 0x5f; 0x18;  (* MOV (% r11) (Memop Quadword (%% (rdi,24))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x10;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,16))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0x4c; 0x8b; 0x67; 0x20;  (* MOV (% r12) (Memop Quadword (%% (rdi,32))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x18;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0x4c; 0x8b; 0x6f; 0x28;  (* MOV (% r13) (Memop Quadword (%% (rdi,40))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x20;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,32))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0x4c; 0x8b; 0x77; 0x30;  (* MOV (% r14) (Memop Quadword (%% (rdi,48))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x28;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0x4c; 0x8b; 0x7f; 0x38;  (* MOV (% r15) (Memop Quadword (%% (rdi,56))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x30;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,48))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x46; 0x38;
                           (* MULX4 (% r8,% rax) (% rdx,Memop Quadword (%% (rsi,56))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc5;
                           (* ADOX (% r8) (% rbp) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc5;
                           (* ADCX (% r8) (% rbp) *)
  0x48; 0x8b; 0x51; 0x08;  (* MOV (% rdx) (Memop Quadword (%% (rcx,8))) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1e;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0x4c; 0x89; 0x4f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% r9) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x08;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x10;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,16))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x18;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x20;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,32))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x28;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x30;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,48))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x4e; 0x38;
                           (* MULX4 (% r9,% rax) (% rdx,Memop Quadword (%% (rsi,56))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcd;
                           (* ADOX (% r9) (% rbp) *)
  0x49; 0x11; 0xe9;        (* ADC (% r9) (% rbp) *)
  0x48; 0x8b; 0x51; 0x10;  (* MOV (% rdx) (Memop Quadword (%% (rcx,16))) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1e;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0x4c; 0x89; 0x57; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r10) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x08;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x10;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,16))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x18;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x20;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,32))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x28;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x30;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,48))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x56; 0x38;
                           (* MULX4 (% r10,% rax) (% rdx,Memop Quadword (%% (rsi,56))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd5;
                           (* ADOX (% r10) (% rbp) *)
  0x49; 0x11; 0xea;        (* ADC (% r10) (% rbp) *)
  0x48; 0x8b; 0x51; 0x18;  (* MOV (% rdx) (Memop Quadword (%% (rcx,24))) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1e;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0x4c; 0x89; 0x5f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r11) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x08;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x10;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,16))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x18;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x20;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,32))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x28;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x30;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,48))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x5e; 0x38;
                           (* MULX4 (% r11,% rax) (% rdx,Memop Quadword (%% (rsi,56))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdd;
                           (* ADOX (% r11) (% rbp) *)
  0x49; 0x11; 0xeb;        (* ADC (% r11) (% rbp) *)
  0x48; 0x8b; 0x51; 0x20;  (* MOV (% rdx) (Memop Quadword (%% (rcx,32))) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1e;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0x4c; 0x89; 0x67; 0x20;  (* MOV (Memop Quadword (%% (rdi,32))) (% r12) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x08;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x10;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,16))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x18;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x20;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,32))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x28;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x30;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,48))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x66; 0x38;
                           (* MULX4 (% r12,% rax) (% rdx,Memop Quadword (%% (rsi,56))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe5;
                           (* ADOX (% r12) (% rbp) *)
  0x49; 0x11; 0xec;        (* ADC (% r12) (% rbp) *)
  0x48; 0x8b; 0x51; 0x28;  (* MOV (% rdx) (Memop Quadword (%% (rcx,40))) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1e;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0x4c; 0x89; 0x6f; 0x28;  (* MOV (Memop Quadword (%% (rdi,40))) (% r13) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x08;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x10;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,16))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x18;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x20;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,32))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x28;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x30;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,48))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x6e; 0x38;
                           (* MULX4 (% r13,% rax) (% rdx,Memop Quadword (%% (rsi,56))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xed;
                           (* ADOX (% r13) (% rbp) *)
  0x49; 0x11; 0xed;        (* ADC (% r13) (% rbp) *)
  0x48; 0x8b; 0x51; 0x30;  (* MOV (% rdx) (Memop Quadword (%% (rcx,48))) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1e;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0x4c; 0x89; 0x77; 0x30;  (* MOV (Memop Quadword (%% (rdi,48))) (% r14) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x08;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x10;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,16))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x18;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x20;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,32))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x28;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x30;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,48))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x76; 0x38;
                           (* MULX4 (% r14,% rax) (% rdx,Memop Quadword (%% (rsi,56))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf5;
                           (* ADOX (% r14) (% rbp) *)
  0x49; 0x11; 0xee;        (* ADC (% r14) (% rbp) *)
  0x48; 0x8b; 0x51; 0x38;  (* MOV (% rdx) (Memop Quadword (%% (rcx,56))) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1e;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0x4c; 0x89; 0x7f; 0x38;  (* MOV (Memop Quadword (%% (rdi,56))) (% r15) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x08;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x10;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,16))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x18;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x20;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,32))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x28;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x30;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,48))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x7e; 0x38;
                           (* MULX4 (% r15,% rax) (% rdx,Memop Quadword (%% (rsi,56))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfd;
                           (* ADOX (% r15) (% rbp) *)
  0x49; 0x11; 0xef;        (* ADC (% r15) (% rbp) *)
  0x48; 0x8b; 0x51; 0x40;  (* MOV (% rdx) (Memop Quadword (%% (rcx,64))) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0x47; 0x40;
                           (* ADOX (% r8) (Memop Quadword (%% (rdi,64))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1e;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0x4c; 0x89; 0x47; 0x40;  (* MOV (Memop Quadword (%% (rdi,64))) (% r8) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x08;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x10;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,16))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x18;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x20;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,32))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x28;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x30;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,48))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x46; 0x38;
                           (* MULX4 (% r8,% rax) (% rdx,Memop Quadword (%% (rsi,56))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc5;
                           (* ADOX (% r8) (% rbp) *)
  0x49; 0x11; 0xe8;        (* ADC (% r8) (% rbp) *)
  0x48; 0x8b; 0x51; 0x48;  (* MOV (% rdx) (Memop Quadword (%% (rcx,72))) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0x4f; 0x48;
                           (* ADOX (% r9) (Memop Quadword (%% (rdi,72))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1e;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0x4c; 0x89; 0x4f; 0x48;  (* MOV (Memop Quadword (%% (rdi,72))) (% r9) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x08;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x10;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,16))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x18;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x20;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,32))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x28;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x30;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,48))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x4e; 0x38;
                           (* MULX4 (% r9,% rax) (% rdx,Memop Quadword (%% (rsi,56))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcd;
                           (* ADOX (% r9) (% rbp) *)
  0x49; 0x11; 0xe9;        (* ADC (% r9) (% rbp) *)
  0x48; 0x8b; 0x51; 0x50;  (* MOV (% rdx) (Memop Quadword (%% (rcx,80))) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0x57; 0x50;
                           (* ADOX (% r10) (Memop Quadword (%% (rdi,80))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1e;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0x4c; 0x89; 0x57; 0x50;  (* MOV (Memop Quadword (%% (rdi,80))) (% r10) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x08;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x10;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,16))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x18;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x20;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,32))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x28;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x30;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,48))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x56; 0x38;
                           (* MULX4 (% r10,% rax) (% rdx,Memop Quadword (%% (rsi,56))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd5;
                           (* ADOX (% r10) (% rbp) *)
  0x49; 0x11; 0xea;        (* ADC (% r10) (% rbp) *)
  0x48; 0x8b; 0x51; 0x58;  (* MOV (% rdx) (Memop Quadword (%% (rcx,88))) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0x5f; 0x58;
                           (* ADOX (% r11) (Memop Quadword (%% (rdi,88))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1e;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0x4c; 0x89; 0x5f; 0x58;  (* MOV (Memop Quadword (%% (rdi,88))) (% r11) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x08;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x10;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,16))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x18;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x20;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,32))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x28;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x30;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,48))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x5e; 0x38;
                           (* MULX4 (% r11,% rax) (% rdx,Memop Quadword (%% (rsi,56))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdd;
                           (* ADOX (% r11) (% rbp) *)
  0x49; 0x11; 0xeb;        (* ADC (% r11) (% rbp) *)
  0x48; 0x8b; 0x51; 0x60;  (* MOV (% rdx) (Memop Quadword (%% (rcx,96))) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0x67; 0x60;
                           (* ADOX (% r12) (Memop Quadword (%% (rdi,96))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1e;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0x4c; 0x89; 0x67; 0x60;  (* MOV (Memop Quadword (%% (rdi,96))) (% r12) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x08;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x10;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,16))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x18;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x20;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,32))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x28;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x30;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,48))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x66; 0x38;
                           (* MULX4 (% r12,% rax) (% rdx,Memop Quadword (%% (rsi,56))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe5;
                           (* ADOX (% r12) (% rbp) *)
  0x49; 0x11; 0xec;        (* ADC (% r12) (% rbp) *)
  0x48; 0x8b; 0x51; 0x68;  (* MOV (% rdx) (Memop Quadword (%% (rcx,104))) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0x6f; 0x68;
                           (* ADOX (% r13) (Memop Quadword (%% (rdi,104))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1e;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0x4c; 0x89; 0x6f; 0x68;  (* MOV (Memop Quadword (%% (rdi,104))) (% r13) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x08;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x10;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,16))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x18;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x20;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,32))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x28;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x30;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,48))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x6e; 0x38;
                           (* MULX4 (% r13,% rax) (% rdx,Memop Quadword (%% (rsi,56))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xed;
                           (* ADOX (% r13) (% rbp) *)
  0x49; 0x11; 0xed;        (* ADC (% r13) (% rbp) *)
  0x48; 0x8b; 0x51; 0x70;  (* MOV (% rdx) (Memop Quadword (%% (rcx,112))) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0x77; 0x70;
                           (* ADOX (% r14) (Memop Quadword (%% (rdi,112))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1e;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0x4c; 0x89; 0x77; 0x70;  (* MOV (Memop Quadword (%% (rdi,112))) (% r14) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x08;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x10;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,16))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x18;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x20;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,32))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x28;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x30;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,48))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x76; 0x38;
                           (* MULX4 (% r14,% rax) (% rdx,Memop Quadword (%% (rsi,56))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf5;
                           (* ADOX (% r14) (% rbp) *)
  0x49; 0x11; 0xee;        (* ADC (% r14) (% rbp) *)
  0x48; 0x8b; 0x51; 0x78;  (* MOV (% rdx) (Memop Quadword (%% (rcx,120))) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0x7f; 0x78;
                           (* ADOX (% r15) (Memop Quadword (%% (rdi,120))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1e;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0x4c; 0x89; 0x7f; 0x78;  (* MOV (Memop Quadword (%% (rdi,120))) (% r15) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x08;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x10;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,16))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x18;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x20;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,32))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x28;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x30;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,48))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x7e; 0x38;
                           (* MULX4 (% r15,% rax) (% rdx,Memop Quadword (%% (rsi,56))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfd;
                           (* ADOX (% r15) (% rbp) *)
  0x49; 0x11; 0xef;        (* ADC (% r15) (% rbp) *)
  0x4c; 0x89; 0x87; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,128))) (% r8) *)
  0x4c; 0x89; 0x8f; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,136))) (% r9) *)
  0x4c; 0x89; 0x97; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,144))) (% r10) *)
  0x4c; 0x89; 0x9f; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,152))) (% r11) *)
  0x4c; 0x89; 0xa7; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,160))) (% r12) *)
  0x4c; 0x89; 0xaf; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,168))) (% r13) *)
  0x4c; 0x89; 0xb7; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,176))) (% r14) *)
  0x4c; 0x89; 0xbf; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,184))) (% r15) *)
  0xc3                     (* RET *)
];;

let bignum_kmul_32_64_tmc = define_trimmed "bignum_kmul_32_64_tmc" bignum_kmul_32_64_mc;;

let BIGNUM_KMUL_32_64_EXEC = X86_MK_EXEC_RULE bignum_kmul_32_64_tmc;;

(* ------------------------------------------------------------------------- *)
(* First of all the correctness lemma for the embedded bignum_kmul_16_32     *)
(* ------------------------------------------------------------------------- *)

let local_kmul_16_32_tmc_def = define
 `local_kmul_16_32_tmc = ITER 0xe1a TL bignum_kmul_32_64_tmc`;;

let local_kmul_16_32_tmc =
  GEN_REWRITE_RULE DEPTH_CONV [TL]
    (REWRITE_RULE[bignum_kmul_32_64_tmc; CONJUNCT1 ITER]
      (CONV_RULE(RAND_CONV(TOP_DEPTH_CONV
         (RATOR_CONV(LAND_CONV num_CONV) THENC GEN_REWRITE_CONV I [ITER])))
         local_kmul_16_32_tmc_def));;

let LOCAL_KMUL_16_32_EXEC = X86_MK_EXEC_RULE local_kmul_16_32_tmc;;

let LOCAL_KMUL_16_32_CORRECT = prove
 (`!z x y a b pc.
      ALL (nonoverlapping (z,8 * 32)) [(word pc,5145); (x,8 * 16); (y,8 * 16)]
      ==> ensures x86
            (\s. bytes_loaded s (word pc) local_kmul_16_32_tmc /\
                 read RIP s = word pc /\
                 read RDI s = z /\
                 read RSI s = x /\
                 read RCX s = y /\
                 bignum_from_memory (x,16) s = a /\
                 bignum_from_memory (y,16) s = b)
            (\s. read RIP s = word(pc + 5144) /\
                 read RDI s = word_add z (word 0x40) /\
                 read RSI s = word_add x (word 0x40) /\
                 read RCX s = y /\
                 bignum_from_memory (z,32) s = a * b)
            (MAYCHANGE [RIP; RDI; RSI; RAX; RBP; RBX; RCX; RDX;
                        R8; R9; R10; R11; R12; R13; R14; R15] ,,
             MAYCHANGE [memory :> bytes(z,8 * 32)] ,,
             MAYCHANGE SOME_FLAGS)`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `y:int64`; `a:num`; `b:num`; `pc:num`] THEN
  REWRITE_TAC[ALLPAIRS; ALL; PAIRWISE] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,16) s0` THEN
  BIGNUM_DIGITIZE_TAC "y_" `bignum_from_memory (y,16) s0` THEN
  X86_XACCSTEPS_TAC LOCAL_KMUL_16_32_EXEC
   [`RDI`; `RSI`] (1--921) (1--921) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXPAND_TAC ["a"; "b"] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Common tactic for the main part with standard and Windows ABIs            *)
(* ------------------------------------------------------------------------- *)

let tac mc execth pcinst =
  let maintac = X86_SUBROUTINE_SIM_TAC
    (mc,execth,dest_small_numeral(rand pcinst),
     local_kmul_16_32_tmc,LOCAL_KMUL_16_32_CORRECT)
    [`read RDI s`; `read RSI s`; `read RCX s`;
     `read (memory :> bytes (read RSI s,8 * 16)) s`;
     `read (memory :> bytes (read RCX s,8 * 16)) s`;
     pcinst]
  and posttac =
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM ADD_ASSOC]) THEN
    RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_ADD_CONV)) in
  let LOCAL_KMUL_16_32_TAC n = maintac n THEN posttac in

  (*** Initialization and splitting of the inputs ***)

  REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
  BIGNUM_TERMRANGE_TAC `32` `a:num` THEN
  BIGNUM_TERMRANGE_TAC `32` `b:num` THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
  MP_TAC(CONJ
   (ISPECL [`x:int64`; `16`; `16`] BIGNUM_FROM_MEMORY_SPLIT)
   (ISPECL [`y:int64`; `16`; `16`] BIGNUM_FROM_MEMORY_SPLIT)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV(NUM_ADD_CONV ORELSEC NUM_MULT_CONV))) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY ABBREV_TAC
   [`ahi = read (memory :> bytes (word_add x (word 128),8 * 16)) s0`;
    `alo = read (memory :> bytes (x,8 * 16)) s0`;
    `bhi = read (memory :> bytes (word_add y (word 128),8 * 16)) s0`;
    `blo = read (memory :> bytes (y,8 * 16)) s0`] THEN

  (*** First nested multiply: low part ***)

  X86_STEPS_TAC execth (1--2) THEN
  LOCAL_KMUL_16_32_TAC 3 THEN

  (*** Second nested multiply: high part ***)

  X86_STEPS_TAC execth (4--8) THEN
  LOCAL_KMUL_16_32_TAC 9 THEN

  (*** Reshuffling of pointers to get t back off the stack ***)

  X86_STEPS_TAC execth (10--13) THEN

  (*** First absolute difference computation, then throw away x data ***)

  BIGNUM_LDIGITIZE_TAC "x_" `bignum_from_memory(x,32) s13` THEN
  X86_ACCSTEPS_TAC execth
   (map (fun n -> 15 + 3 * n) (0--15)) (14--63) THEN
  SUBGOAL_THEN `carry_s60 <=> alo < ahi` (ASSUME_TAC o SYM) THENL
   [MAP_EVERY EXPAND_TAC ["ahi"; "alo"] THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `1024` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VAL_EQ_0; WORD_NEG_EQ_0; WORD_BITVAL_EQ_0]) THEN
  X86_ACCSTEPS_TAC execth
   (map (fun n -> 68 + 6 * n) (0--15)) (64--159) THEN
  SUBGOAL_THEN
   `&(read (memory :> bytes (t,8 * 16)) s159):real = abs(&alo - &ahi)`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`64 * 16`; `&0:real`] THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0; BIGNUM_FROM_MEMORY_BOUND];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_ABS_POS] THEN MATCH_MP_TAC(REAL_ARITH
       `&x < e /\ &y < e ==> abs(&x - &y):real < e`) THEN
      REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
      MAP_EVERY EXPAND_TAC ["ahi"; "alo"] THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_BOUND];
      REWRITE_TAC[INTEGER_CLOSED]] THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LT; REAL_ARITH
     `abs(&x - &y):real = if &x < &y then &y - &x else &x - &y`] THEN
    MAP_EVERY EXPAND_TAC ["ahi"; "alo"] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    ASM_CASES_TAC `carry_s60:bool` THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES; REAL_VAL_WORD_NOT; DIMINDEX_64] THEN
    DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    UNDISCH_TAC
     `read (memory :> bytes64 (word_add stackpointer (word 8))) s159 = z` THEN
    DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes64 x) s = y`] THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `x:int64` o concl))) THEN
    DISCH_TAC] THEN

  (*** Second absolute difference computation, then throw away y data ***)

  BIGNUM_LDIGITIZE_TAC "y_" `bignum_from_memory(y,32) s159` THEN
  X86_ACCSTEPS_TAC execth
   (map (fun n -> 161 + 3 * n) (0--15)) (160--209) THEN
  SUBGOAL_THEN `carry_s206 <=> bhi < blo` (ASSUME_TAC o SYM) THENL
   [MAP_EVERY EXPAND_TAC ["bhi"; "blo"] THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `1024` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VAL_EQ_0; WORD_NEG_EQ_0; WORD_BITVAL_EQ_0]) THEN
  X86_ACCSTEPS_TAC execth
   (map (fun n -> 214 + 6 * n) (0--15)) (210--305) THEN
  SUBGOAL_THEN
   `&(read (memory :> bytes (word_add t (word 128),8 * 16)) s305):real =
    abs(&bhi - &blo)`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`64 * 16`; `&0:real`] THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0; BIGNUM_FROM_MEMORY_BOUND];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_ABS_POS] THEN MATCH_MP_TAC(REAL_ARITH
       `&x < e /\ &y < e ==> abs(&x - &y):real < e`) THEN
      REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
      MAP_EVERY EXPAND_TAC ["bhi"; "blo"] THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_BOUND];
      REWRITE_TAC[INTEGER_CLOSED]] THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LT; REAL_ARITH
     `abs(&x - &y):real = if &x < &y then &y - &x else &x - &y`] THEN
    MAP_EVERY EXPAND_TAC ["bhi"; "blo"] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    ASM_CASES_TAC `carry_s206:bool` THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES; REAL_VAL_WORD_NOT; DIMINDEX_64] THEN
    DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    UNDISCH_TAC
     `read (memory :> bytes64 (word_add stackpointer (word 8))) s305 = z` THEN
    DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes64 x) s = y`] THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `x:int64` o concl))) THEN
    DISCH_TAC] THEN

  (*** Stashing the combined sign ***)

  X86_STEPS_TAC execth [306;307] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_XOR_MASKS]) THEN
  ABBREV_TAC `sgn <=> ~(carry_s60 <=> carry_s206)` THEN

  (*** Third and last nested multiplication, of the absolute differences ***)

  ABBREV_TAC `adiff = read (memory :> bytes (t,8 * 16)) s307` THEN
  ABBREV_TAC
   `bdiff = read (memory :> bytes (word_add t (word 128),8 * 16)) s307` THEN
  X86_STEPS_TAC execth (308--311) THEN
  LOCAL_KMUL_16_32_TAC 312 THEN
  X86_STEPS_TAC execth (313--314) THEN

  (*** Digitize low and high products ***)

  BIGNUM_LDIGITIZE_TAC "l_" `read (memory :> bytes (z,8 * 32)) s314` THEN
  BIGNUM_LDIGITIZE_TAC "h_"
   `read (memory :> bytes (word_add z (word 256),8 * 32)) s314` THEN

  (*** Simulate the interlocking part, just deduce top carry zeroness ***)

  X86_ACCSTEPS_TAC execth
   (sort (<)  (map (fun n -> 317 + 4 * n) (0--31) @
               map (fun n -> 318 + 4 * n) (0--31) @ [445]))
   (315--445) THEN
  UNDISCH_TAC
   `&2 pow 64 * &(bitval carry_s445) + &(val(sum_s445:int64)) =
    &(val(word(bitval carry_s442):int64)) + &(bitval carry_s441)` THEN
  REWRITE_TAC[VAL_WORD_BITVAL] THEN
  DISCH_THEN(MP_TAC o end_itlist CONJ o DECARRY_RULE o CONJUNCTS) THEN
  STRIP_TAC THEN

  (*** Refresh the sign after we pull it out of storage ***)

  X86_STEPS_TAC execth (446--448) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [WORD_NEG_NEG; VAL_EQ_0; WORD_NEG_EQ_0; WORD_BITVAL_EQ_0]) THEN

  (*** Digitize the mid-product and simulate the rest ***)

  BIGNUM_LDIGITIZE_TAC "m_"
   `read (memory :> bytes (word_add t (word 256),8 * 32)) s448` THEN
  X86_ACCSTEPS_TAC execth
   (map (fun n -> 453 + 6 * n) (0--31) @ [641]) (449--641) THEN
  X86_ACCSTEPS_TAC execth (643--658) (642--658) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  (*** The Karatsuba rearrangement ***)

  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`64 * 64`; `&0:real`] THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_BOUND];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0] THEN
    REWRITE_TAC[EXP_ADD; ARITH_RULE `64 * 64 = 64 * 32 + 64 * 32`] THEN
    ASM_SIMP_TAC[LT_MULT2];
    REWRITE_TAC[INTEGER_CLOSED]] THEN
  SUBGOAL_THEN
   `(&a:real) * &b =
    (&1 + &2 pow 1024) * (&(alo * blo) + &2 pow 1024 * &(ahi * bhi)) +
    --(&1) pow bitval sgn * &2 pow 1024 * &(bdiff * adiff)`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
    MAP_EVERY EXPAND_TAC ["sgn"; "carry_s60"; "carry_s206"; "a"; "b"] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN
    REWRITE_TAC[REAL_ARITH
     `abs(x - y:real) = if x < y then y - x else x - y`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES]) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN

  (*** Justify the carry suspension ***)

  UNDISCH_THEN
  `&(val(sum_s445:int64)):real = &(bitval carry_s442) + &(bitval carry_s441)`
  SUBST_ALL_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (vfree_in `carry_s641:bool` o concl)) THEN
  DISCH_THEN(MP_TAC o SPEC `&(bitval sgn):real` o MATCH_MP (REAL_ARITH
   `&2 pow 64 * c + s = x
    ==> !c'. (&2 pow 64 * c + s = x ==> c = c')
             ==> s = x - &2 pow 64 * c'`)) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_EQ; EQ_BITVAL] THEN
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
    BOOL_CASES_TAC `sgn:bool` THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES; REAL_VAL_WORD_NOT; DIMINDEX_64] THEN
    CONV_TAC WORD_REDUCE_CONV THENL
     [STRIP_TAC;
      DISCH_THEN(K ALL_TAC) THEN
      DISCH_THEN(MP_TAC o end_itlist CONJ o DECARRY_RULE o CONJUNCTS) THEN
      SIMP_TAC[BITVAL_EQ_0; REAL_OF_NUM_EQ]] THEN
    GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM] THEN
    DISCH_THEN(SUBST1_TAC o EQF_INTRO) THEN
    REWRITE_TAC[BITVAL_CLAUSES; REAL_MUL_RZERO; REAL_ADD_LID] THEN
    MATCH_MP_TAC(REAL_ARITH
     `s:real <= e /\ &0 < cc + d ==> ~(s = cc + e + d)`) THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH
     `!d:real. &0 <= d /\ d - &2 pow 2048 * c < &0 ==> &0 < c`) THEN
    EXISTS_TAC
     `(&(alo * blo) + &(ahi * bhi)) - &(bdiff * adiff):real` THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_LT; REAL_ARITH
       `abs(x - y:real) = if x < y then y - x else x - y`] THEN
      FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (TAUT
       `~(p <=> q) ==> (q <=> ~p)`)) THEN
      REWRITE_TAC[COND_SWAP] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
      SIMP_TAC[REAL_POS; REAL_LE_ADD; REAL_LE_MUL];
      ALL_TAC] THEN
    REPEAT(FIRST_X_ASSUM(SUBST1_TAC o SYM o
      check(can (term_match [] `bignum_of_wordlist l = a * b`) o concl))) THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC(LAND_CONV REAL_POLY_CONV) THEN BOUNDER_TAC[];
    DISCH_THEN SUBST_ALL_TAC] THEN

  (*** Complete the accumulation proof ***)

  REPEAT(FIRST_X_ASSUM(SUBST1_TAC o SYM o
    check(can (term_match [] `bignum_of_wordlist l = a * b`) o concl))) THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  REWRITE_TAC[WORD_XOR_MASK] THEN POP_ASSUM_LIST(K ALL_TAC) THEN
  BOOL_CASES_TAC `sgn:bool` THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES; REAL_VAL_WORD_NOT; DIMINDEX_64] THEN
  REWRITE_TAC[COND_SWAP; GSYM WORD_BITVAL; VAL_WORD_BITVAL] THEN STRIP_TAC THEN
  ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN REAL_INTEGER_TAC;;

(* ------------------------------------------------------------------------- *)
(* Proof of the standard ABI version.                                        *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_KMUL_32_64_NOIBT_SUBROUTINE_CORRECT = prove
 (`!z x y a b t pc stackpointer returnaddress.
      ALL (nonoverlapping (word_sub stackpointer (word 64),72))
          [(z,8 * 64); (t,8 * 96)] /\
      ALL (nonoverlapping (word_sub stackpointer (word 64),64))
         [(word pc,LENGTH bignum_kmul_32_64_tmc); (x,8 * 32); (y,8 * 32)] /\
      nonoverlapping (z,8 * 64) (t,8 * 96) /\
      ALLPAIRS nonoverlapping
       [(z,8 * 64); (t,8 * 96)]
       [(word pc,LENGTH bignum_kmul_32_64_tmc); (x,8 * 32); (y,8 * 32)]
      ==> ensures x86
            (\s. bytes_loaded s (word pc) bignum_kmul_32_64_tmc /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [z; x; y; t] s /\
                 bignum_from_memory (x,32) s = a /\
                 bignum_from_memory (y,32) s = b)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 bignum_from_memory (z,64) s = a * b)
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(z,8 * 64); memory :> bytes(t,8 * 96);
                        memory :> bytes(word_sub stackpointer (word 64),64)])`,
  REWRITE_TAC[fst BIGNUM_KMUL_32_64_EXEC] THEN
  REWRITE_TAC [MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `y:int64`;
    `a:num`; `b:num`; `t:int64`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 64 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  REWRITE_TAC[ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN STRIP_TAC THEN

  (*** Start and end boilerplate for save and restore of registers ***)

  SUBGOAL_THEN
   `ensures x86
     (\s. bytes_loaded s (word pc) bignum_kmul_32_64_tmc /\
          read RIP s = word(pc + 0xb) /\
          read RSP s = word_add stackpointer (word 8) /\
          C_ARGUMENTS [z; x; y] s /\
          read (memory :> bytes64 (word_add stackpointer (word 8))) s = t /\
          bignum_from_memory (x,32) s = a /\
          bignum_from_memory (y,32) s = b)
     (\s. read RIP s = word(pc + 0xe0e) /\
          bignum_from_memory (z,64) s = a * b)
     (MAYCHANGE [RIP; RSI; RDI; RAX; RCX; RDX; R8; R9; R10; R11;
                 RBX; RBP; R12; R13; R14; R15] ,,
      MAYCHANGE [memory :> bytes(z,8 * 64); memory :> bytes(t,8 * 96);
                 memory :> bytes(stackpointer,16)] ,,
      MAYCHANGE SOME_FLAGS)`
  MP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THENL
   [ENSURES_EXISTING_PRESERVED_TAC `RSP`;
    DISCH_THEN(fun th ->
      ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
      ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
      ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
      ENSURES_PRESERVED_TAC "r13_init" `R13` THEN
      ENSURES_PRESERVED_TAC "r14_init" `R14` THEN
      ENSURES_PRESERVED_TAC "r15_init" `R15` THEN
      ENSURES_INIT_TAC "s0" THEN
      X86_STEPS_TAC BIGNUM_KMUL_32_64_EXEC (1--7) THEN
      MP_TAC th) THEN
    X86_BIGSTEP_TAC BIGNUM_KMUL_32_64_EXEC "s8" THEN
    X86_STEPS_TAC BIGNUM_KMUL_32_64_EXEC (9--16) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]] THEN

  tac bignum_kmul_32_64_tmc BIGNUM_KMUL_32_64_EXEC `pc + 0xe1a`);;

let BIGNUM_KMUL_32_64_SUBROUTINE_CORRECT = prove
 (`!z x y a b t pc stackpointer returnaddress.
      ALL (nonoverlapping (word_sub stackpointer (word 64),72))
          [(z,8 * 64); (t,8 * 96)] /\
      ALL (nonoverlapping (word_sub stackpointer (word 64),64))
         [(word pc,LENGTH bignum_kmul_32_64_mc); (x,8 * 32); (y,8 * 32)] /\
      nonoverlapping (z,8 * 64) (t,8 * 96) /\
      ALLPAIRS nonoverlapping
       [(z,8 * 64); (t,8 * 96)]
       [(word pc,LENGTH bignum_kmul_32_64_mc); (x,8 * 32); (y,8 * 32)]
      ==> ensures x86
            (\s. bytes_loaded s (word pc) bignum_kmul_32_64_mc /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [z; x; y; t] s /\
                 bignum_from_memory (x,32) s = a /\
                 bignum_from_memory (y,32) s = b)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 bignum_from_memory (z,64) s = a * b)
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(z,8 * 64); memory :> bytes(t,8 * 96);
                        memory :> bytes(word_sub stackpointer (word 64),64)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_KMUL_32_64_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_kmul_32_64_windows_mc = define_from_elf
   "bignum_kmul_32_64_windows_mc" "x86/fastmul/bignum_kmul_32_64.obj";;

let bignum_kmul_32_64_windows_tmc = define_trimmed "bignum_kmul_32_64_windows_tmc" bignum_kmul_32_64_windows_mc;;

let WINDOWS_BIGNUM_KMUL_32_64_EXEC =
  X86_MK_EXEC_RULE bignum_kmul_32_64_windows_tmc;;

let BIGNUM_KMUL_32_64_NOIBT_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!z x y a b t pc stackpointer returnaddress.
      ALL (nonoverlapping (word_sub stackpointer (word 80),88))
          [(z,8 * 64); (t,8 * 96)] /\
      ALL (nonoverlapping (word_sub stackpointer (word 80),80))
         [(word pc,LENGTH bignum_kmul_32_64_windows_tmc); (x,8 * 32); (y,8 * 32)] /\
      nonoverlapping (z,8 * 64) (t,8 * 96) /\
      ALLPAIRS nonoverlapping
       [(z,8 * 64); (t,8 * 96)]
       [(word pc,LENGTH bignum_kmul_32_64_windows_tmc); (x,8 * 32); (y,8 * 32)]
      ==> ensures x86
            (\s. bytes_loaded s (word pc) bignum_kmul_32_64_windows_tmc /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 WINDOWS_C_ARGUMENTS [z; x; y; t] s /\
                 bignum_from_memory (x,32) s = a /\
                 bignum_from_memory (y,32) s = b)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 bignum_from_memory (z,64) s = a * b)
            (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(z,8 * 64); memory :> bytes(t,8 * 96);
                        memory :> bytes(word_sub stackpointer (word 80),80)])`,
  REWRITE_TAC[fst WINDOWS_BIGNUM_KMUL_32_64_EXEC] THEN
  REWRITE_TAC[WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `y:int64`;
    `a:num`; `b:num`; `t:int64`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 80 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[WINDOWS_C_ARGUMENTS; WINDOWS_C_RETURN; SOME_FLAGS] THEN
  REWRITE_TAC[ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN STRIP_TAC THEN

  (*** Start and end boilerplate for save and restore of registers ***)

  SUBGOAL_THEN
   `ensures x86
     (\s. bytes_loaded s (word pc) bignum_kmul_32_64_windows_tmc /\
          read RIP s = word(pc + 0x19) /\
          read RSP s = word_add stackpointer (word 8) /\
          C_ARGUMENTS [z; x; y] s /\
          read (memory :> bytes64 (word_add stackpointer (word 8))) s = t /\
          bignum_from_memory (x,32) s = a /\
          bignum_from_memory (y,32) s = b)
     (\s. read RIP s = word(pc + 0xe1c) /\
          bignum_from_memory (z,64) s = a * b)
     (MAYCHANGE [RIP; RSI; RDI; RAX; RCX; RDX; R8; R9; R10; R11;
                 RBX; RBP; R12; R13; R14; R15] ,,
      MAYCHANGE [memory :> bytes(z,8 * 64); memory :> bytes(t,8 * 96);
                 memory :> bytes(stackpointer,16)] ,,
      MAYCHANGE SOME_FLAGS)`
  MP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THENL
   [ENSURES_EXISTING_PRESERVED_TAC `RSP`;
    DISCH_THEN(fun th ->
      ENSURES_PRESERVED_TAC "rdi_init" `RDI` THEN
      ENSURES_PRESERVED_TAC "rsi_init" `RSI` THEN
      ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
      ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
      ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
      ENSURES_PRESERVED_TAC "r13_init" `R13` THEN
      ENSURES_PRESERVED_TAC "r14_init" `R14` THEN
      ENSURES_PRESERVED_TAC "r15_init" `R15` THEN
      ENSURES_INIT_TAC "s0" THEN
      X86_STEPS_TAC WINDOWS_BIGNUM_KMUL_32_64_EXEC (1--13) THEN
      MP_TAC th) THEN
    X86_BIGSTEP_TAC WINDOWS_BIGNUM_KMUL_32_64_EXEC "s14" THEN
    X86_STEPS_TAC WINDOWS_BIGNUM_KMUL_32_64_EXEC (15--24) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]] THEN

  tac bignum_kmul_32_64_windows_tmc WINDOWS_BIGNUM_KMUL_32_64_EXEC
      `pc + 0xe2a`);;

let BIGNUM_KMUL_32_64_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!z x y a b t pc stackpointer returnaddress.
      ALL (nonoverlapping (word_sub stackpointer (word 80),88))
          [(z,8 * 64); (t,8 * 96)] /\
      ALL (nonoverlapping (word_sub stackpointer (word 80),80))
         [(word pc,LENGTH bignum_kmul_32_64_windows_mc); (x,8 * 32); (y,8 * 32)] /\
      nonoverlapping (z,8 * 64) (t,8 * 96) /\
      ALLPAIRS nonoverlapping
       [(z,8 * 64); (t,8 * 96)]
       [(word pc,LENGTH bignum_kmul_32_64_windows_mc); (x,8 * 32); (y,8 * 32)]
      ==> ensures x86
            (\s. bytes_loaded s (word pc) bignum_kmul_32_64_windows_mc /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 WINDOWS_C_ARGUMENTS [z; x; y; t] s /\
                 bignum_from_memory (x,32) s = a /\
                 bignum_from_memory (y,32) s = b)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 bignum_from_memory (z,64) s = a * b)
            (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(z,8 * 64); memory :> bytes(t,8 * 96);
                        memory :> bytes(word_sub stackpointer (word 80),80)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_KMUL_32_64_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

