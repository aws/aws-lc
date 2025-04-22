(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* MULX-based Karatsuba 32x32->64 squaring.                                  *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/fastmul/bignum_ksqr_32_64.o";;
 ****)

let bignum_ksqr_32_64_mc =
  define_assert_from_elf "bignum_ksqr_32_64_mc" "x86/fastmul/bignum_ksqr_32_64.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x55;                    (* PUSH (% rbp) *)
  0x53;                    (* PUSH (% rbx) *)
  0x41; 0x54;              (* PUSH (% r12) *)
  0x41; 0x55;              (* PUSH (% r13) *)
  0x41; 0x56;              (* PUSH (% r14) *)
  0x41; 0x57;              (* PUSH (% r15) *)
  0x48; 0x89; 0xd1;        (* MOV (% rcx) (% rdx) *)
  0xe8; 0xc4; 0x08; 0x00; 0x00;
                           (* CALL (Imm32 (word 2244)) *)
  0x48; 0x8d; 0xb6; 0x80; 0x00; 0x00; 0x00;
                           (* LEA (% rsi) (%% (rsi,128)) *)
  0x48; 0x8d; 0xbf; 0x00; 0x01; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rdi,256)) *)
  0xe8; 0xb1; 0x08; 0x00; 0x00;
                           (* CALL (Imm32 (word 2225)) *)
  0x48; 0x8b; 0x46; 0x80;  (* MOV (% rax) (Memop Quadword (%% (rsi,18446744073709551488))) *)
  0x48; 0x2b; 0x06;        (* SUB (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0x89; 0x01;        (* MOV (Memop Quadword (%% (rcx,0))) (% rax) *)
  0x48; 0x8b; 0x46; 0x88;  (* MOV (% rax) (Memop Quadword (%% (rsi,18446744073709551496))) *)
  0x48; 0x1b; 0x46; 0x08;  (* SBB (% rax) (Memop Quadword (%% (rsi,8))) *)
  0x48; 0x89; 0x41; 0x08;  (* MOV (Memop Quadword (%% (rcx,8))) (% rax) *)
  0x48; 0x8b; 0x46; 0x90;  (* MOV (% rax) (Memop Quadword (%% (rsi,18446744073709551504))) *)
  0x48; 0x1b; 0x46; 0x10;  (* SBB (% rax) (Memop Quadword (%% (rsi,16))) *)
  0x48; 0x89; 0x41; 0x10;  (* MOV (Memop Quadword (%% (rcx,16))) (% rax) *)
  0x48; 0x8b; 0x46; 0x98;  (* MOV (% rax) (Memop Quadword (%% (rsi,18446744073709551512))) *)
  0x48; 0x1b; 0x46; 0x18;  (* SBB (% rax) (Memop Quadword (%% (rsi,24))) *)
  0x48; 0x89; 0x41; 0x18;  (* MOV (Memop Quadword (%% (rcx,24))) (% rax) *)
  0x48; 0x8b; 0x46; 0xa0;  (* MOV (% rax) (Memop Quadword (%% (rsi,18446744073709551520))) *)
  0x48; 0x1b; 0x46; 0x20;  (* SBB (% rax) (Memop Quadword (%% (rsi,32))) *)
  0x48; 0x89; 0x41; 0x20;  (* MOV (Memop Quadword (%% (rcx,32))) (% rax) *)
  0x48; 0x8b; 0x46; 0xa8;  (* MOV (% rax) (Memop Quadword (%% (rsi,18446744073709551528))) *)
  0x48; 0x1b; 0x46; 0x28;  (* SBB (% rax) (Memop Quadword (%% (rsi,40))) *)
  0x48; 0x89; 0x41; 0x28;  (* MOV (Memop Quadword (%% (rcx,40))) (% rax) *)
  0x48; 0x8b; 0x46; 0xb0;  (* MOV (% rax) (Memop Quadword (%% (rsi,18446744073709551536))) *)
  0x48; 0x1b; 0x46; 0x30;  (* SBB (% rax) (Memop Quadword (%% (rsi,48))) *)
  0x48; 0x89; 0x41; 0x30;  (* MOV (Memop Quadword (%% (rcx,48))) (% rax) *)
  0x48; 0x8b; 0x46; 0xb8;  (* MOV (% rax) (Memop Quadword (%% (rsi,18446744073709551544))) *)
  0x48; 0x1b; 0x46; 0x38;  (* SBB (% rax) (Memop Quadword (%% (rsi,56))) *)
  0x48; 0x89; 0x41; 0x38;  (* MOV (Memop Quadword (%% (rcx,56))) (% rax) *)
  0x48; 0x8b; 0x46; 0xc0;  (* MOV (% rax) (Memop Quadword (%% (rsi,18446744073709551552))) *)
  0x48; 0x1b; 0x46; 0x40;  (* SBB (% rax) (Memop Quadword (%% (rsi,64))) *)
  0x48; 0x89; 0x41; 0x40;  (* MOV (Memop Quadword (%% (rcx,64))) (% rax) *)
  0x48; 0x8b; 0x46; 0xc8;  (* MOV (% rax) (Memop Quadword (%% (rsi,18446744073709551560))) *)
  0x48; 0x1b; 0x46; 0x48;  (* SBB (% rax) (Memop Quadword (%% (rsi,72))) *)
  0x48; 0x89; 0x41; 0x48;  (* MOV (Memop Quadword (%% (rcx,72))) (% rax) *)
  0x48; 0x8b; 0x46; 0xd0;  (* MOV (% rax) (Memop Quadword (%% (rsi,18446744073709551568))) *)
  0x48; 0x1b; 0x46; 0x50;  (* SBB (% rax) (Memop Quadword (%% (rsi,80))) *)
  0x48; 0x89; 0x41; 0x50;  (* MOV (Memop Quadword (%% (rcx,80))) (% rax) *)
  0x48; 0x8b; 0x46; 0xd8;  (* MOV (% rax) (Memop Quadword (%% (rsi,18446744073709551576))) *)
  0x48; 0x1b; 0x46; 0x58;  (* SBB (% rax) (Memop Quadword (%% (rsi,88))) *)
  0x48; 0x89; 0x41; 0x58;  (* MOV (Memop Quadword (%% (rcx,88))) (% rax) *)
  0x48; 0x8b; 0x46; 0xe0;  (* MOV (% rax) (Memop Quadword (%% (rsi,18446744073709551584))) *)
  0x48; 0x1b; 0x46; 0x60;  (* SBB (% rax) (Memop Quadword (%% (rsi,96))) *)
  0x48; 0x89; 0x41; 0x60;  (* MOV (Memop Quadword (%% (rcx,96))) (% rax) *)
  0x48; 0x8b; 0x46; 0xe8;  (* MOV (% rax) (Memop Quadword (%% (rsi,18446744073709551592))) *)
  0x48; 0x1b; 0x46; 0x68;  (* SBB (% rax) (Memop Quadword (%% (rsi,104))) *)
  0x48; 0x89; 0x41; 0x68;  (* MOV (Memop Quadword (%% (rcx,104))) (% rax) *)
  0x48; 0x8b; 0x46; 0xf0;  (* MOV (% rax) (Memop Quadword (%% (rsi,18446744073709551600))) *)
  0x48; 0x1b; 0x46; 0x70;  (* SBB (% rax) (Memop Quadword (%% (rsi,112))) *)
  0x48; 0x89; 0x41; 0x70;  (* MOV (Memop Quadword (%% (rcx,112))) (% rax) *)
  0x48; 0x8b; 0x46; 0xf8;  (* MOV (% rax) (Memop Quadword (%% (rsi,18446744073709551608))) *)
  0x48; 0x1b; 0x46; 0x78;  (* SBB (% rax) (Memop Quadword (%% (rsi,120))) *)
  0x48; 0x89; 0x41; 0x78;  (* MOV (Memop Quadword (%% (rcx,120))) (% rax) *)
  0xbb; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% ebx) (Imm32 (word 0)) *)
  0x48; 0x19; 0xc0;        (* SBB (% rax) (% rax) *)
  0x48; 0x8b; 0x11;        (* MOV (% rdx) (Memop Quadword (%% (rcx,0))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADCX (% rdx) (% rbx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x48; 0x89; 0x11;        (* MOV (Memop Quadword (%% (rcx,0))) (% rdx) *)
  0x48; 0x8b; 0x51; 0x08;  (* MOV (% rdx) (Memop Quadword (%% (rcx,8))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADCX (% rdx) (% rbx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x48; 0x89; 0x51; 0x08;  (* MOV (Memop Quadword (%% (rcx,8))) (% rdx) *)
  0x48; 0x8b; 0x51; 0x10;  (* MOV (% rdx) (Memop Quadword (%% (rcx,16))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADCX (% rdx) (% rbx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x48; 0x89; 0x51; 0x10;  (* MOV (Memop Quadword (%% (rcx,16))) (% rdx) *)
  0x48; 0x8b; 0x51; 0x18;  (* MOV (% rdx) (Memop Quadword (%% (rcx,24))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADCX (% rdx) (% rbx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x48; 0x89; 0x51; 0x18;  (* MOV (Memop Quadword (%% (rcx,24))) (% rdx) *)
  0x48; 0x8b; 0x51; 0x20;  (* MOV (% rdx) (Memop Quadword (%% (rcx,32))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADCX (% rdx) (% rbx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x48; 0x89; 0x51; 0x20;  (* MOV (Memop Quadword (%% (rcx,32))) (% rdx) *)
  0x48; 0x8b; 0x51; 0x28;  (* MOV (% rdx) (Memop Quadword (%% (rcx,40))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADCX (% rdx) (% rbx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x48; 0x89; 0x51; 0x28;  (* MOV (Memop Quadword (%% (rcx,40))) (% rdx) *)
  0x48; 0x8b; 0x51; 0x30;  (* MOV (% rdx) (Memop Quadword (%% (rcx,48))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADCX (% rdx) (% rbx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x48; 0x89; 0x51; 0x30;  (* MOV (Memop Quadword (%% (rcx,48))) (% rdx) *)
  0x48; 0x8b; 0x51; 0x38;  (* MOV (% rdx) (Memop Quadword (%% (rcx,56))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADCX (% rdx) (% rbx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x48; 0x89; 0x51; 0x38;  (* MOV (Memop Quadword (%% (rcx,56))) (% rdx) *)
  0x48; 0x8b; 0x51; 0x40;  (* MOV (% rdx) (Memop Quadword (%% (rcx,64))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADCX (% rdx) (% rbx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x48; 0x89; 0x51; 0x40;  (* MOV (Memop Quadword (%% (rcx,64))) (% rdx) *)
  0x48; 0x8b; 0x51; 0x48;  (* MOV (% rdx) (Memop Quadword (%% (rcx,72))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADCX (% rdx) (% rbx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x48; 0x89; 0x51; 0x48;  (* MOV (Memop Quadword (%% (rcx,72))) (% rdx) *)
  0x48; 0x8b; 0x51; 0x50;  (* MOV (% rdx) (Memop Quadword (%% (rcx,80))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADCX (% rdx) (% rbx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x48; 0x89; 0x51; 0x50;  (* MOV (Memop Quadword (%% (rcx,80))) (% rdx) *)
  0x48; 0x8b; 0x51; 0x58;  (* MOV (% rdx) (Memop Quadword (%% (rcx,88))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADCX (% rdx) (% rbx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x48; 0x89; 0x51; 0x58;  (* MOV (Memop Quadword (%% (rcx,88))) (% rdx) *)
  0x48; 0x8b; 0x51; 0x60;  (* MOV (% rdx) (Memop Quadword (%% (rcx,96))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADCX (% rdx) (% rbx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x48; 0x89; 0x51; 0x60;  (* MOV (Memop Quadword (%% (rcx,96))) (% rdx) *)
  0x48; 0x8b; 0x51; 0x68;  (* MOV (% rdx) (Memop Quadword (%% (rcx,104))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADCX (% rdx) (% rbx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x48; 0x89; 0x51; 0x68;  (* MOV (Memop Quadword (%% (rcx,104))) (% rdx) *)
  0x48; 0x8b; 0x51; 0x70;  (* MOV (% rdx) (Memop Quadword (%% (rcx,112))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADCX (% rdx) (% rbx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x48; 0x89; 0x51; 0x70;  (* MOV (Memop Quadword (%% (rcx,112))) (% rdx) *)
  0x48; 0x8b; 0x51; 0x78;  (* MOV (% rdx) (Memop Quadword (%% (rcx,120))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADCX (% rdx) (% rbx) *)
  0x48; 0x0f; 0x44; 0xd0;  (* CMOVE (% rdx) (% rax) *)
  0x48; 0x89; 0x51; 0x78;  (* MOV (Memop Quadword (%% (rcx,120))) (% rdx) *)
  0x31; 0xd2;              (* XOR (% edx) (% edx) *)
  0x48; 0x8b; 0x47; 0x80;  (* MOV (% rax) (Memop Quadword (%% (rdi,18446744073709551488))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0x00; 0xff; 0xff; 0xff;
                           (* ADCX (% rax) (Memop Quadword (%% (rdi,18446744073709551360))) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0x07;
                           (* ADOX (% rax) (Memop Quadword (%% (rdi,0))) *)
  0x48; 0x89; 0x81; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rcx,128))) (% rax) *)
  0x48; 0x8b; 0x47; 0x88;  (* MOV (% rax) (Memop Quadword (%% (rdi,18446744073709551496))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0x08; 0xff; 0xff; 0xff;
                           (* ADCX (% rax) (Memop Quadword (%% (rdi,18446744073709551368))) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0x47; 0x08;
                           (* ADOX (% rax) (Memop Quadword (%% (rdi,8))) *)
  0x48; 0x89; 0x81; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rcx,136))) (% rax) *)
  0x48; 0x8b; 0x47; 0x90;  (* MOV (% rax) (Memop Quadword (%% (rdi,18446744073709551504))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0x10; 0xff; 0xff; 0xff;
                           (* ADCX (% rax) (Memop Quadword (%% (rdi,18446744073709551376))) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0x47; 0x10;
                           (* ADOX (% rax) (Memop Quadword (%% (rdi,16))) *)
  0x48; 0x89; 0x81; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rcx,144))) (% rax) *)
  0x48; 0x8b; 0x47; 0x98;  (* MOV (% rax) (Memop Quadword (%% (rdi,18446744073709551512))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0x18; 0xff; 0xff; 0xff;
                           (* ADCX (% rax) (Memop Quadword (%% (rdi,18446744073709551384))) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0x47; 0x18;
                           (* ADOX (% rax) (Memop Quadword (%% (rdi,24))) *)
  0x48; 0x89; 0x81; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rcx,152))) (% rax) *)
  0x48; 0x8b; 0x47; 0xa0;  (* MOV (% rax) (Memop Quadword (%% (rdi,18446744073709551520))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0x20; 0xff; 0xff; 0xff;
                           (* ADCX (% rax) (Memop Quadword (%% (rdi,18446744073709551392))) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0x47; 0x20;
                           (* ADOX (% rax) (Memop Quadword (%% (rdi,32))) *)
  0x48; 0x89; 0x81; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rcx,160))) (% rax) *)
  0x48; 0x8b; 0x47; 0xa8;  (* MOV (% rax) (Memop Quadword (%% (rdi,18446744073709551528))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0x28; 0xff; 0xff; 0xff;
                           (* ADCX (% rax) (Memop Quadword (%% (rdi,18446744073709551400))) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0x47; 0x28;
                           (* ADOX (% rax) (Memop Quadword (%% (rdi,40))) *)
  0x48; 0x89; 0x81; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rcx,168))) (% rax) *)
  0x48; 0x8b; 0x47; 0xb0;  (* MOV (% rax) (Memop Quadword (%% (rdi,18446744073709551536))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0x30; 0xff; 0xff; 0xff;
                           (* ADCX (% rax) (Memop Quadword (%% (rdi,18446744073709551408))) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0x47; 0x30;
                           (* ADOX (% rax) (Memop Quadword (%% (rdi,48))) *)
  0x48; 0x89; 0x81; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rcx,176))) (% rax) *)
  0x48; 0x8b; 0x47; 0xb8;  (* MOV (% rax) (Memop Quadword (%% (rdi,18446744073709551544))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0x38; 0xff; 0xff; 0xff;
                           (* ADCX (% rax) (Memop Quadword (%% (rdi,18446744073709551416))) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0x47; 0x38;
                           (* ADOX (% rax) (Memop Quadword (%% (rdi,56))) *)
  0x48; 0x89; 0x81; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rcx,184))) (% rax) *)
  0x48; 0x8b; 0x47; 0xc0;  (* MOV (% rax) (Memop Quadword (%% (rdi,18446744073709551552))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0x40; 0xff; 0xff; 0xff;
                           (* ADCX (% rax) (Memop Quadword (%% (rdi,18446744073709551424))) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0x47; 0x40;
                           (* ADOX (% rax) (Memop Quadword (%% (rdi,64))) *)
  0x48; 0x89; 0x81; 0xc0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rcx,192))) (% rax) *)
  0x48; 0x8b; 0x47; 0xc8;  (* MOV (% rax) (Memop Quadword (%% (rdi,18446744073709551560))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0x48; 0xff; 0xff; 0xff;
                           (* ADCX (% rax) (Memop Quadword (%% (rdi,18446744073709551432))) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0x47; 0x48;
                           (* ADOX (% rax) (Memop Quadword (%% (rdi,72))) *)
  0x48; 0x89; 0x81; 0xc8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rcx,200))) (% rax) *)
  0x48; 0x8b; 0x47; 0xd0;  (* MOV (% rax) (Memop Quadword (%% (rdi,18446744073709551568))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0x50; 0xff; 0xff; 0xff;
                           (* ADCX (% rax) (Memop Quadword (%% (rdi,18446744073709551440))) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0x47; 0x50;
                           (* ADOX (% rax) (Memop Quadword (%% (rdi,80))) *)
  0x48; 0x89; 0x81; 0xd0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rcx,208))) (% rax) *)
  0x48; 0x8b; 0x47; 0xd8;  (* MOV (% rax) (Memop Quadword (%% (rdi,18446744073709551576))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0x58; 0xff; 0xff; 0xff;
                           (* ADCX (% rax) (Memop Quadword (%% (rdi,18446744073709551448))) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0x47; 0x58;
                           (* ADOX (% rax) (Memop Quadword (%% (rdi,88))) *)
  0x48; 0x89; 0x81; 0xd8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rcx,216))) (% rax) *)
  0x48; 0x8b; 0x47; 0xe0;  (* MOV (% rax) (Memop Quadword (%% (rdi,18446744073709551584))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0x60; 0xff; 0xff; 0xff;
                           (* ADCX (% rax) (Memop Quadword (%% (rdi,18446744073709551456))) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0x47; 0x60;
                           (* ADOX (% rax) (Memop Quadword (%% (rdi,96))) *)
  0x48; 0x89; 0x81; 0xe0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rcx,224))) (% rax) *)
  0x48; 0x8b; 0x47; 0xe8;  (* MOV (% rax) (Memop Quadword (%% (rdi,18446744073709551592))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0x68; 0xff; 0xff; 0xff;
                           (* ADCX (% rax) (Memop Quadword (%% (rdi,18446744073709551464))) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0x47; 0x68;
                           (* ADOX (% rax) (Memop Quadword (%% (rdi,104))) *)
  0x48; 0x89; 0x81; 0xe8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rcx,232))) (% rax) *)
  0x48; 0x8b; 0x47; 0xf0;  (* MOV (% rax) (Memop Quadword (%% (rdi,18446744073709551600))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0x70; 0xff; 0xff; 0xff;
                           (* ADCX (% rax) (Memop Quadword (%% (rdi,18446744073709551472))) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0x47; 0x70;
                           (* ADOX (% rax) (Memop Quadword (%% (rdi,112))) *)
  0x48; 0x89; 0x81; 0xf0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rcx,240))) (% rax) *)
  0x48; 0x8b; 0x47; 0xf8;  (* MOV (% rax) (Memop Quadword (%% (rdi,18446744073709551608))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0x78; 0xff; 0xff; 0xff;
                           (* ADCX (% rax) (Memop Quadword (%% (rdi,18446744073709551480))) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0x47; 0x78;
                           (* ADOX (% rax) (Memop Quadword (%% (rdi,120))) *)
  0x48; 0x89; 0x81; 0xf8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rcx,248))) (% rax) *)
  0x48; 0x8b; 0x07;        (* MOV (% rax) (Memop Quadword (%% (rdi,0))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x47; 0x80;
                           (* ADCX (% rax) (Memop Quadword (%% (rdi,18446744073709551488))) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0x80; 0x00; 0x00; 0x00;
                           (* ADOX (% rax) (Memop Quadword (%% (rdi,128))) *)
  0x48; 0x89; 0x07;        (* MOV (Memop Quadword (%% (rdi,0))) (% rax) *)
  0x48; 0x8b; 0x47; 0x08;  (* MOV (% rax) (Memop Quadword (%% (rdi,8))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x47; 0x88;
                           (* ADCX (% rax) (Memop Quadword (%% (rdi,18446744073709551496))) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0x88; 0x00; 0x00; 0x00;
                           (* ADOX (% rax) (Memop Quadword (%% (rdi,136))) *)
  0x48; 0x89; 0x47; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% rax) *)
  0x48; 0x8b; 0x47; 0x10;  (* MOV (% rax) (Memop Quadword (%% (rdi,16))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x47; 0x90;
                           (* ADCX (% rax) (Memop Quadword (%% (rdi,18446744073709551504))) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0x90; 0x00; 0x00; 0x00;
                           (* ADOX (% rax) (Memop Quadword (%% (rdi,144))) *)
  0x48; 0x89; 0x47; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% rax) *)
  0x48; 0x8b; 0x47; 0x18;  (* MOV (% rax) (Memop Quadword (%% (rdi,24))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x47; 0x98;
                           (* ADCX (% rax) (Memop Quadword (%% (rdi,18446744073709551512))) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0x98; 0x00; 0x00; 0x00;
                           (* ADOX (% rax) (Memop Quadword (%% (rdi,152))) *)
  0x48; 0x89; 0x47; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% rax) *)
  0x48; 0x8b; 0x47; 0x20;  (* MOV (% rax) (Memop Quadword (%% (rdi,32))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x47; 0xa0;
                           (* ADCX (% rax) (Memop Quadword (%% (rdi,18446744073709551520))) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0xa0; 0x00; 0x00; 0x00;
                           (* ADOX (% rax) (Memop Quadword (%% (rdi,160))) *)
  0x48; 0x89; 0x47; 0x20;  (* MOV (Memop Quadword (%% (rdi,32))) (% rax) *)
  0x48; 0x8b; 0x47; 0x28;  (* MOV (% rax) (Memop Quadword (%% (rdi,40))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x47; 0xa8;
                           (* ADCX (% rax) (Memop Quadword (%% (rdi,18446744073709551528))) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0xa8; 0x00; 0x00; 0x00;
                           (* ADOX (% rax) (Memop Quadword (%% (rdi,168))) *)
  0x48; 0x89; 0x47; 0x28;  (* MOV (Memop Quadword (%% (rdi,40))) (% rax) *)
  0x48; 0x8b; 0x47; 0x30;  (* MOV (% rax) (Memop Quadword (%% (rdi,48))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x47; 0xb0;
                           (* ADCX (% rax) (Memop Quadword (%% (rdi,18446744073709551536))) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0xb0; 0x00; 0x00; 0x00;
                           (* ADOX (% rax) (Memop Quadword (%% (rdi,176))) *)
  0x48; 0x89; 0x47; 0x30;  (* MOV (Memop Quadword (%% (rdi,48))) (% rax) *)
  0x48; 0x8b; 0x47; 0x38;  (* MOV (% rax) (Memop Quadword (%% (rdi,56))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x47; 0xb8;
                           (* ADCX (% rax) (Memop Quadword (%% (rdi,18446744073709551544))) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0xb8; 0x00; 0x00; 0x00;
                           (* ADOX (% rax) (Memop Quadword (%% (rdi,184))) *)
  0x48; 0x89; 0x47; 0x38;  (* MOV (Memop Quadword (%% (rdi,56))) (% rax) *)
  0x48; 0x8b; 0x47; 0x40;  (* MOV (% rax) (Memop Quadword (%% (rdi,64))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x47; 0xc0;
                           (* ADCX (% rax) (Memop Quadword (%% (rdi,18446744073709551552))) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0xc0; 0x00; 0x00; 0x00;
                           (* ADOX (% rax) (Memop Quadword (%% (rdi,192))) *)
  0x48; 0x89; 0x47; 0x40;  (* MOV (Memop Quadword (%% (rdi,64))) (% rax) *)
  0x48; 0x8b; 0x47; 0x48;  (* MOV (% rax) (Memop Quadword (%% (rdi,72))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x47; 0xc8;
                           (* ADCX (% rax) (Memop Quadword (%% (rdi,18446744073709551560))) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0xc8; 0x00; 0x00; 0x00;
                           (* ADOX (% rax) (Memop Quadword (%% (rdi,200))) *)
  0x48; 0x89; 0x47; 0x48;  (* MOV (Memop Quadword (%% (rdi,72))) (% rax) *)
  0x48; 0x8b; 0x47; 0x50;  (* MOV (% rax) (Memop Quadword (%% (rdi,80))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x47; 0xd0;
                           (* ADCX (% rax) (Memop Quadword (%% (rdi,18446744073709551568))) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0xd0; 0x00; 0x00; 0x00;
                           (* ADOX (% rax) (Memop Quadword (%% (rdi,208))) *)
  0x48; 0x89; 0x47; 0x50;  (* MOV (Memop Quadword (%% (rdi,80))) (% rax) *)
  0x48; 0x8b; 0x47; 0x58;  (* MOV (% rax) (Memop Quadword (%% (rdi,88))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x47; 0xd8;
                           (* ADCX (% rax) (Memop Quadword (%% (rdi,18446744073709551576))) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0xd8; 0x00; 0x00; 0x00;
                           (* ADOX (% rax) (Memop Quadword (%% (rdi,216))) *)
  0x48; 0x89; 0x47; 0x58;  (* MOV (Memop Quadword (%% (rdi,88))) (% rax) *)
  0x48; 0x8b; 0x47; 0x60;  (* MOV (% rax) (Memop Quadword (%% (rdi,96))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x47; 0xe0;
                           (* ADCX (% rax) (Memop Quadword (%% (rdi,18446744073709551584))) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0xe0; 0x00; 0x00; 0x00;
                           (* ADOX (% rax) (Memop Quadword (%% (rdi,224))) *)
  0x48; 0x89; 0x47; 0x60;  (* MOV (Memop Quadword (%% (rdi,96))) (% rax) *)
  0x48; 0x8b; 0x47; 0x68;  (* MOV (% rax) (Memop Quadword (%% (rdi,104))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x47; 0xe8;
                           (* ADCX (% rax) (Memop Quadword (%% (rdi,18446744073709551592))) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0xe8; 0x00; 0x00; 0x00;
                           (* ADOX (% rax) (Memop Quadword (%% (rdi,232))) *)
  0x48; 0x89; 0x47; 0x68;  (* MOV (Memop Quadword (%% (rdi,104))) (% rax) *)
  0x48; 0x8b; 0x47; 0x70;  (* MOV (% rax) (Memop Quadword (%% (rdi,112))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x47; 0xf0;
                           (* ADCX (% rax) (Memop Quadword (%% (rdi,18446744073709551600))) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0xf0; 0x00; 0x00; 0x00;
                           (* ADOX (% rax) (Memop Quadword (%% (rdi,240))) *)
  0x48; 0x89; 0x47; 0x70;  (* MOV (Memop Quadword (%% (rdi,112))) (% rax) *)
  0x48; 0x8b; 0x47; 0x78;  (* MOV (% rax) (Memop Quadword (%% (rdi,120))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x47; 0xf8;
                           (* ADCX (% rax) (Memop Quadword (%% (rdi,18446744073709551608))) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0x87; 0xf8; 0x00; 0x00; 0x00;
                           (* ADOX (% rax) (Memop Quadword (%% (rdi,248))) *)
  0x48; 0x89; 0x47; 0x78;  (* MOV (Memop Quadword (%% (rdi,120))) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xd2;
                           (* ADOX (% rdx) (% rdx) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x48; 0x89; 0x91; 0x00; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rcx,512))) (% rdx) *)
  0x48; 0x89; 0xce;        (* MOV (% rsi) (% rcx) *)
  0x48; 0x8d; 0x8f; 0x00; 0xff; 0xff; 0xff;
                           (* LEA (% rcx) (%% (rdi,18446744073709551360)) *)
  0x48; 0x8d; 0xbe; 0x00; 0x01; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rsi,256)) *)
  0xe8; 0xf7; 0x02; 0x00; 0x00;
                           (* CALL (Imm32 (word 759)) *)
  0x48; 0x8b; 0x86; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsi,128))) *)
  0x48; 0x2b; 0x07;        (* SUB (% rax) (Memop Quadword (%% (rdi,0))) *)
  0x48; 0x89; 0x81; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rcx,128))) (% rax) *)
  0x48; 0x8b; 0x86; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsi,136))) *)
  0x48; 0x1b; 0x47; 0x08;  (* SBB (% rax) (Memop Quadword (%% (rdi,8))) *)
  0x48; 0x89; 0x81; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rcx,136))) (% rax) *)
  0x48; 0x8b; 0x86; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsi,144))) *)
  0x48; 0x1b; 0x47; 0x10;  (* SBB (% rax) (Memop Quadword (%% (rdi,16))) *)
  0x48; 0x89; 0x81; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rcx,144))) (% rax) *)
  0x48; 0x8b; 0x86; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsi,152))) *)
  0x48; 0x1b; 0x47; 0x18;  (* SBB (% rax) (Memop Quadword (%% (rdi,24))) *)
  0x48; 0x89; 0x81; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rcx,152))) (% rax) *)
  0x48; 0x8b; 0x86; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsi,160))) *)
  0x48; 0x1b; 0x47; 0x20;  (* SBB (% rax) (Memop Quadword (%% (rdi,32))) *)
  0x48; 0x89; 0x81; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rcx,160))) (% rax) *)
  0x48; 0x8b; 0x86; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsi,168))) *)
  0x48; 0x1b; 0x47; 0x28;  (* SBB (% rax) (Memop Quadword (%% (rdi,40))) *)
  0x48; 0x89; 0x81; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rcx,168))) (% rax) *)
  0x48; 0x8b; 0x86; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsi,176))) *)
  0x48; 0x1b; 0x47; 0x30;  (* SBB (% rax) (Memop Quadword (%% (rdi,48))) *)
  0x48; 0x89; 0x81; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rcx,176))) (% rax) *)
  0x48; 0x8b; 0x86; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsi,184))) *)
  0x48; 0x1b; 0x47; 0x38;  (* SBB (% rax) (Memop Quadword (%% (rdi,56))) *)
  0x48; 0x89; 0x81; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rcx,184))) (% rax) *)
  0x48; 0x8b; 0x86; 0xc0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsi,192))) *)
  0x48; 0x1b; 0x47; 0x40;  (* SBB (% rax) (Memop Quadword (%% (rdi,64))) *)
  0x48; 0x89; 0x81; 0xc0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rcx,192))) (% rax) *)
  0x48; 0x8b; 0x86; 0xc8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsi,200))) *)
  0x48; 0x1b; 0x47; 0x48;  (* SBB (% rax) (Memop Quadword (%% (rdi,72))) *)
  0x48; 0x89; 0x81; 0xc8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rcx,200))) (% rax) *)
  0x48; 0x8b; 0x86; 0xd0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsi,208))) *)
  0x48; 0x1b; 0x47; 0x50;  (* SBB (% rax) (Memop Quadword (%% (rdi,80))) *)
  0x48; 0x89; 0x81; 0xd0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rcx,208))) (% rax) *)
  0x48; 0x8b; 0x86; 0xd8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsi,216))) *)
  0x48; 0x1b; 0x47; 0x58;  (* SBB (% rax) (Memop Quadword (%% (rdi,88))) *)
  0x48; 0x89; 0x81; 0xd8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rcx,216))) (% rax) *)
  0x48; 0x8b; 0x86; 0xe0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsi,224))) *)
  0x48; 0x1b; 0x47; 0x60;  (* SBB (% rax) (Memop Quadword (%% (rdi,96))) *)
  0x48; 0x89; 0x81; 0xe0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rcx,224))) (% rax) *)
  0x48; 0x8b; 0x86; 0xe8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsi,232))) *)
  0x48; 0x1b; 0x47; 0x68;  (* SBB (% rax) (Memop Quadword (%% (rdi,104))) *)
  0x48; 0x89; 0x81; 0xe8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rcx,232))) (% rax) *)
  0x48; 0x8b; 0x86; 0xf0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsi,240))) *)
  0x48; 0x1b; 0x47; 0x70;  (* SBB (% rax) (Memop Quadword (%% (rdi,112))) *)
  0x48; 0x89; 0x81; 0xf0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rcx,240))) (% rax) *)
  0x48; 0x8b; 0x86; 0xf8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsi,248))) *)
  0x48; 0x1b; 0x47; 0x78;  (* SBB (% rax) (Memop Quadword (%% (rdi,120))) *)
  0x48; 0x89; 0x81; 0xf8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rcx,248))) (% rax) *)
  0x48; 0x8b; 0x81; 0x00; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rcx,256))) *)
  0x48; 0x1b; 0x87; 0x80; 0x00; 0x00; 0x00;
                           (* SBB (% rax) (Memop Quadword (%% (rdi,128))) *)
  0x48; 0x89; 0x81; 0x00; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rcx,256))) (% rax) *)
  0x48; 0x8b; 0x81; 0x08; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rcx,264))) *)
  0x48; 0x1b; 0x87; 0x88; 0x00; 0x00; 0x00;
                           (* SBB (% rax) (Memop Quadword (%% (rdi,136))) *)
  0x48; 0x89; 0x81; 0x08; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rcx,264))) (% rax) *)
  0x48; 0x8b; 0x81; 0x10; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rcx,272))) *)
  0x48; 0x1b; 0x87; 0x90; 0x00; 0x00; 0x00;
                           (* SBB (% rax) (Memop Quadword (%% (rdi,144))) *)
  0x48; 0x89; 0x81; 0x10; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rcx,272))) (% rax) *)
  0x48; 0x8b; 0x81; 0x18; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rcx,280))) *)
  0x48; 0x1b; 0x87; 0x98; 0x00; 0x00; 0x00;
                           (* SBB (% rax) (Memop Quadword (%% (rdi,152))) *)
  0x48; 0x89; 0x81; 0x18; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rcx,280))) (% rax) *)
  0x48; 0x8b; 0x81; 0x20; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rcx,288))) *)
  0x48; 0x1b; 0x87; 0xa0; 0x00; 0x00; 0x00;
                           (* SBB (% rax) (Memop Quadword (%% (rdi,160))) *)
  0x48; 0x89; 0x81; 0x20; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rcx,288))) (% rax) *)
  0x48; 0x8b; 0x81; 0x28; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rcx,296))) *)
  0x48; 0x1b; 0x87; 0xa8; 0x00; 0x00; 0x00;
                           (* SBB (% rax) (Memop Quadword (%% (rdi,168))) *)
  0x48; 0x89; 0x81; 0x28; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rcx,296))) (% rax) *)
  0x48; 0x8b; 0x81; 0x30; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rcx,304))) *)
  0x48; 0x1b; 0x87; 0xb0; 0x00; 0x00; 0x00;
                           (* SBB (% rax) (Memop Quadword (%% (rdi,176))) *)
  0x48; 0x89; 0x81; 0x30; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rcx,304))) (% rax) *)
  0x48; 0x8b; 0x81; 0x38; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rcx,312))) *)
  0x48; 0x1b; 0x87; 0xb8; 0x00; 0x00; 0x00;
                           (* SBB (% rax) (Memop Quadword (%% (rdi,184))) *)
  0x48; 0x89; 0x81; 0x38; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rcx,312))) (% rax) *)
  0x48; 0x8b; 0x81; 0x40; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rcx,320))) *)
  0x48; 0x1b; 0x87; 0xc0; 0x00; 0x00; 0x00;
                           (* SBB (% rax) (Memop Quadword (%% (rdi,192))) *)
  0x48; 0x89; 0x81; 0x40; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rcx,320))) (% rax) *)
  0x48; 0x8b; 0x81; 0x48; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rcx,328))) *)
  0x48; 0x1b; 0x87; 0xc8; 0x00; 0x00; 0x00;
                           (* SBB (% rax) (Memop Quadword (%% (rdi,200))) *)
  0x48; 0x89; 0x81; 0x48; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rcx,328))) (% rax) *)
  0x48; 0x8b; 0x81; 0x50; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rcx,336))) *)
  0x48; 0x1b; 0x87; 0xd0; 0x00; 0x00; 0x00;
                           (* SBB (% rax) (Memop Quadword (%% (rdi,208))) *)
  0x48; 0x89; 0x81; 0x50; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rcx,336))) (% rax) *)
  0x48; 0x8b; 0x81; 0x58; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rcx,344))) *)
  0x48; 0x1b; 0x87; 0xd8; 0x00; 0x00; 0x00;
                           (* SBB (% rax) (Memop Quadword (%% (rdi,216))) *)
  0x48; 0x89; 0x81; 0x58; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rcx,344))) (% rax) *)
  0x48; 0x8b; 0x81; 0x60; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rcx,352))) *)
  0x48; 0x1b; 0x87; 0xe0; 0x00; 0x00; 0x00;
                           (* SBB (% rax) (Memop Quadword (%% (rdi,224))) *)
  0x48; 0x89; 0x81; 0x60; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rcx,352))) (% rax) *)
  0x48; 0x8b; 0x81; 0x68; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rcx,360))) *)
  0x48; 0x1b; 0x87; 0xe8; 0x00; 0x00; 0x00;
                           (* SBB (% rax) (Memop Quadword (%% (rdi,232))) *)
  0x48; 0x89; 0x81; 0x68; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rcx,360))) (% rax) *)
  0x48; 0x8b; 0x81; 0x70; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rcx,368))) *)
  0x48; 0x1b; 0x87; 0xf0; 0x00; 0x00; 0x00;
                           (* SBB (% rax) (Memop Quadword (%% (rdi,240))) *)
  0x48; 0x89; 0x81; 0x70; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rcx,368))) (% rax) *)
  0x48; 0x8b; 0x81; 0x78; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rcx,376))) *)
  0x48; 0x1b; 0x87; 0xf8; 0x00; 0x00; 0x00;
                           (* SBB (% rax) (Memop Quadword (%% (rdi,248))) *)
  0x48; 0x89; 0x81; 0x78; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rcx,376))) (% rax) *)
  0x48; 0x8b; 0x96; 0x00; 0x02; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsi,512))) *)
  0x48; 0x83; 0xda; 0x00;  (* SBB (% rdx) (Imm8 (word 0)) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0x48; 0x01; 0x91; 0x80; 0x01; 0x00; 0x00;
                           (* ADD (Memop Quadword (%% (rcx,384))) (% rdx) *)
  0x48; 0x11; 0x81; 0x88; 0x01; 0x00; 0x00;
                           (* ADC (Memop Quadword (%% (rcx,392))) (% rax) *)
  0x48; 0x11; 0x81; 0x90; 0x01; 0x00; 0x00;
                           (* ADC (Memop Quadword (%% (rcx,400))) (% rax) *)
  0x48; 0x11; 0x81; 0x98; 0x01; 0x00; 0x00;
                           (* ADC (Memop Quadword (%% (rcx,408))) (% rax) *)
  0x48; 0x11; 0x81; 0xa0; 0x01; 0x00; 0x00;
                           (* ADC (Memop Quadword (%% (rcx,416))) (% rax) *)
  0x48; 0x11; 0x81; 0xa8; 0x01; 0x00; 0x00;
                           (* ADC (Memop Quadword (%% (rcx,424))) (% rax) *)
  0x48; 0x11; 0x81; 0xb0; 0x01; 0x00; 0x00;
                           (* ADC (Memop Quadword (%% (rcx,432))) (% rax) *)
  0x48; 0x11; 0x81; 0xb8; 0x01; 0x00; 0x00;
                           (* ADC (Memop Quadword (%% (rcx,440))) (% rax) *)
  0x48; 0x11; 0x81; 0xc0; 0x01; 0x00; 0x00;
                           (* ADC (Memop Quadword (%% (rcx,448))) (% rax) *)
  0x48; 0x11; 0x81; 0xc8; 0x01; 0x00; 0x00;
                           (* ADC (Memop Quadword (%% (rcx,456))) (% rax) *)
  0x48; 0x11; 0x81; 0xd0; 0x01; 0x00; 0x00;
                           (* ADC (Memop Quadword (%% (rcx,464))) (% rax) *)
  0x48; 0x11; 0x81; 0xd8; 0x01; 0x00; 0x00;
                           (* ADC (Memop Quadword (%% (rcx,472))) (% rax) *)
  0x48; 0x11; 0x81; 0xe0; 0x01; 0x00; 0x00;
                           (* ADC (Memop Quadword (%% (rcx,480))) (% rax) *)
  0x48; 0x11; 0x81; 0xe8; 0x01; 0x00; 0x00;
                           (* ADC (Memop Quadword (%% (rcx,488))) (% rax) *)
  0x48; 0x11; 0x81; 0xf0; 0x01; 0x00; 0x00;
                           (* ADC (Memop Quadword (%% (rcx,496))) (% rax) *)
  0x48; 0x11; 0x81; 0xf8; 0x01; 0x00; 0x00;
                           (* ADC (Memop Quadword (%% (rcx,504))) (% rax) *)
  0x41; 0x5f;              (* POP (% r15) *)
  0x41; 0x5e;              (* POP (% r14) *)
  0x41; 0x5d;              (* POP (% r13) *)
  0x41; 0x5c;              (* POP (% r12) *)
  0x5b;                    (* POP (% rbx) *)
  0x5d;                    (* POP (% rbp) *)
  0xc3;                    (* RET *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0x48; 0x8b; 0x16;        (* MOV (% rdx) (Memop Quadword (%% (rsi,0))) *)
  0xc4; 0xe2; 0xb3; 0xf6; 0x46; 0x08;
                           (* MULX4 (% rax,% r9) (% rdx,Memop Quadword (%% (rsi,8))) *)
  0x4c; 0x89; 0x4f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% r9) *)
  0xc4; 0xe2; 0xab; 0xf6; 0x5e; 0x10;
                           (* MULX4 (% rbx,% r10) (% rdx,Memop Quadword (%% (rsi,16))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0x4c; 0x89; 0x57; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r10) *)
  0xc4; 0xe2; 0xa3; 0xf6; 0x46; 0x18;
                           (* MULX4 (% rax,% r11) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADCX (% r11) (% rbx) *)
  0xc4; 0xe2; 0x9b; 0xf6; 0x5e; 0x20;
                           (* MULX4 (% rbx,% r12) (% rdx,Memop Quadword (%% (rsi,32))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xc4; 0xe2; 0x93; 0xf6; 0x46; 0x28;
                           (* MULX4 (% rax,% r13) (% rdx,Memop Quadword (%% (rsi,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADCX (% r13) (% rbx) *)
  0xc4; 0xe2; 0x8b; 0xf6; 0x5e; 0x30;
                           (* MULX4 (% rbx,% r14) (% rdx,Memop Quadword (%% (rsi,48))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xc4; 0x62; 0x83; 0xf6; 0x46; 0x38;
                           (* MULX4 (% r8,% r15) (% rdx,Memop Quadword (%% (rsi,56))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADCX (% r15) (% rbx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc5;
                           (* ADCX (% r8) (% rbp) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0x48; 0x8b; 0x56; 0x08;  (* MOV (% rdx) (Memop Quadword (%% (rsi,8))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x10;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,16))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0x4c; 0x89; 0x5f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r11) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x18;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0x4c; 0x89; 0x67; 0x20;  (* MOV (Memop Quadword (%% (rdi,32))) (% r12) *)
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
  0x48; 0x8b; 0x56; 0x20;  (* MOV (% rdx) (Memop Quadword (%% (rsi,32))) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x56; 0x28;
                           (* MULX4 (% r10,% rax) (% rdx,Memop Quadword (%% (rsi,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd5;
                           (* ADOX (% r10) (% rbp) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd5;
                           (* ADCX (% r10) (% rbp) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0x48; 0x8b; 0x56; 0x10;  (* MOV (% rdx) (Memop Quadword (%% (rsi,16))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x18;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0x4c; 0x89; 0x6f; 0x28;  (* MOV (Memop Quadword (%% (rdi,40))) (% r13) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x20;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,32))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0x4c; 0x89; 0x77; 0x30;  (* MOV (Memop Quadword (%% (rdi,48))) (% r14) *)
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
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x38;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,56))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0x48; 0x8b; 0x56; 0x30;  (* MOV (% rdx) (Memop Quadword (%% (rsi,48))) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x5e; 0x20;
                           (* MULX4 (% r11,% rax) (% rdx,Memop Quadword (%% (rsi,32))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdd;
                           (* ADOX (% r11) (% rbp) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x66; 0x28;
                           (* MULX4 (% r12,% rax) (% rdx,Memop Quadword (%% (rsi,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe5;
                           (* ADOX (% r12) (% rbp) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe5;
                           (* ADCX (% r12) (% rbp) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0x48; 0x8b; 0x56; 0x18;  (* MOV (% rdx) (Memop Quadword (%% (rsi,24))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x20;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,32))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0x4c; 0x89; 0x7f; 0x38;  (* MOV (Memop Quadword (%% (rdi,56))) (% r15) *)
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
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x38;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,56))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0x48; 0x8b; 0x56; 0x38;  (* MOV (% rdx) (Memop Quadword (%% (rsi,56))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x20;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,32))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x6e; 0x28;
                           (* MULX4 (% r13,% rax) (% rdx,Memop Quadword (%% (rsi,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xed;
                           (* ADOX (% r13) (% rbp) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x76; 0x30;
                           (* MULX4 (% r14,% rax) (% rdx,Memop Quadword (%% (rsi,48))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf5;
                           (* ADOX (% r14) (% rbp) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf5;
                           (* ADCX (% r14) (% rbp) *)
  0x48; 0x8b; 0x56; 0x40;  (* MOV (% rdx) (Memop Quadword (%% (rsi,64))) *)
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
  0xc4; 0x62; 0xfb; 0xf6; 0x7e; 0x30;
                           (* MULX4 (% r15,% rax) (% rdx,Memop Quadword (%% (rsi,48))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfd;
                           (* ADOX (% r15) (% rbp) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x46; 0x38;
                           (* MULX4 (% r8,% rax) (% rdx,Memop Quadword (%% (rsi,56))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc5;
                           (* ADOX (% r8) (% rbp) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc5;
                           (* ADCX (% r8) (% rbp) *)
  0x48; 0x8b; 0x56; 0x48;  (* MOV (% rdx) (Memop Quadword (%% (rsi,72))) *)
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
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xcd;
                           (* ADCX (% r9) (% rbp) *)
  0x48; 0x8b; 0x56; 0x50;  (* MOV (% rdx) (Memop Quadword (%% (rsi,80))) *)
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
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd5;
                           (* ADCX (% r10) (% rbp) *)
  0x48; 0x8b; 0x56; 0x58;  (* MOV (% rdx) (Memop Quadword (%% (rsi,88))) *)
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
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xdd;
                           (* ADCX (% r11) (% rbp) *)
  0x48; 0x8b; 0x56; 0x60;  (* MOV (% rdx) (Memop Quadword (%% (rsi,96))) *)
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
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe5;
                           (* ADCX (% r12) (% rbp) *)
  0x48; 0x8b; 0x56; 0x68;  (* MOV (% rdx) (Memop Quadword (%% (rsi,104))) *)
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
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xed;
                           (* ADCX (% r13) (% rbp) *)
  0x48; 0x8b; 0x56; 0x70;  (* MOV (% rdx) (Memop Quadword (%% (rsi,112))) *)
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
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf5;
                           (* ADCX (% r14) (% rbp) *)
  0x48; 0x8b; 0x56; 0x78;  (* MOV (% rdx) (Memop Quadword (%% (rsi,120))) *)
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
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xfd;
                           (* ADCX (% r15) (% rbp) *)
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
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0x4c; 0x8b; 0x8f; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (% r9) (Memop Quadword (%% (rdi,136))) *)
  0x4c; 0x8b; 0x97; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (% r10) (Memop Quadword (%% (rdi,144))) *)
  0x4c; 0x8b; 0x9f; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (% r11) (Memop Quadword (%% (rdi,152))) *)
  0x4c; 0x8b; 0xa7; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (% r12) (Memop Quadword (%% (rdi,160))) *)
  0x4c; 0x8b; 0xaf; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (% r13) (Memop Quadword (%% (rdi,168))) *)
  0x4c; 0x8b; 0xb7; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (% r14) (Memop Quadword (%% (rdi,176))) *)
  0x4c; 0x8b; 0xbf; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (% r15) (Memop Quadword (%% (rdi,184))) *)
  0x48; 0x8b; 0x56; 0x40;  (* MOV (% rdx) (Memop Quadword (%% (rsi,64))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x48;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,72))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0x4c; 0x89; 0x8f; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,136))) (% r9) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x50;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,80))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0x4c; 0x89; 0x97; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,144))) (% r10) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x58;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,88))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x60;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,96))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x68;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,104))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x70;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,112))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x46; 0x78;
                           (* MULX4 (% r8,% rax) (% rdx,Memop Quadword (%% (rsi,120))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc5;
                           (* ADOX (% r8) (% rbp) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc5;
                           (* ADCX (% r8) (% rbp) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0x48; 0x8b; 0x56; 0x48;  (* MOV (% rdx) (Memop Quadword (%% (rsi,72))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x50;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,80))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0x4c; 0x89; 0x9f; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,152))) (% r11) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x58;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,88))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0x4c; 0x89; 0xa7; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,160))) (% r12) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x60;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,96))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x68;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,104))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x70;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,112))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x4e; 0x78;
                           (* MULX4 (% r9,% rax) (% rdx,Memop Quadword (%% (rsi,120))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcd;
                           (* ADOX (% r9) (% rbp) *)
  0x48; 0x8b; 0x56; 0x60;  (* MOV (% rdx) (Memop Quadword (%% (rsi,96))) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x56; 0x68;
                           (* MULX4 (% r10,% rax) (% rdx,Memop Quadword (%% (rsi,104))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd5;
                           (* ADOX (% r10) (% rbp) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd5;
                           (* ADCX (% r10) (% rbp) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0x48; 0x8b; 0x56; 0x50;  (* MOV (% rdx) (Memop Quadword (%% (rsi,80))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x58;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,88))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0x4c; 0x89; 0xaf; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,168))) (% r13) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x60;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,96))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0x4c; 0x89; 0xb7; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,176))) (% r14) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x68;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,104))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x70;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,112))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x78;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,120))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0x48; 0x8b; 0x56; 0x70;  (* MOV (% rdx) (Memop Quadword (%% (rsi,112))) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x5e; 0x60;
                           (* MULX4 (% r11,% rax) (% rdx,Memop Quadword (%% (rsi,96))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdd;
                           (* ADOX (% r11) (% rbp) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x66; 0x68;
                           (* MULX4 (% r12,% rax) (% rdx,Memop Quadword (%% (rsi,104))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe5;
                           (* ADOX (% r12) (% rbp) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe5;
                           (* ADCX (% r12) (% rbp) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0x48; 0x8b; 0x56; 0x58;  (* MOV (% rdx) (Memop Quadword (%% (rsi,88))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x60;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,96))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0x4c; 0x89; 0xbf; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,184))) (% r15) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x68;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,104))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x70;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,112))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x78;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,120))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0x48; 0x8b; 0x56; 0x78;  (* MOV (% rdx) (Memop Quadword (%% (rsi,120))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x60;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,96))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x6e; 0x68;
                           (* MULX4 (% r13,% rax) (% rdx,Memop Quadword (%% (rsi,104))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xed;
                           (* ADOX (% r13) (% rbp) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x76; 0x70;
                           (* MULX4 (% r14,% rax) (% rdx,Memop Quadword (%% (rsi,112))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf5;
                           (* ADOX (% r14) (% rbp) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf5;
                           (* ADCX (% r14) (% rbp) *)
  0x4c; 0x89; 0x87; 0xc0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,192))) (% r8) *)
  0x4c; 0x89; 0x8f; 0xc8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,200))) (% r9) *)
  0x4c; 0x89; 0x97; 0xd0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,208))) (% r10) *)
  0x4c; 0x89; 0x9f; 0xd8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,216))) (% r11) *)
  0x4c; 0x89; 0xa7; 0xe0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,224))) (% r12) *)
  0x4c; 0x89; 0xaf; 0xe8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,232))) (% r13) *)
  0x4c; 0x89; 0xb7; 0xf0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,240))) (% r14) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0x48; 0x8b; 0x16;        (* MOV (% rdx) (Memop Quadword (%% (rsi,0))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rax) (% rdx,% rdx) *)
  0x48; 0x89; 0x07;        (* MOV (Memop Quadword (%% (rdi,0))) (% rax) *)
  0x48; 0x8b; 0x57; 0x08;  (* MOV (% rdx) (Memop Quadword (%% (rdi,8))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd2;
                           (* ADCX (% rdx) (% rdx) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% rdx) (% rbx) *)
  0x48; 0x89; 0x57; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% rdx) *)
  0x48; 0x8b; 0x56; 0x08;  (* MOV (% rdx) (Memop Quadword (%% (rsi,8))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rax) (% rdx,% rdx) *)
  0x48; 0x8b; 0x57; 0x10;  (* MOV (% rdx) (Memop Quadword (%% (rdi,16))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd2;
                           (* ADCX (% rdx) (% rdx) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADOX (% rdx) (% rax) *)
  0x48; 0x89; 0x57; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% rdx) *)
  0x48; 0x8b; 0x57; 0x18;  (* MOV (% rdx) (Memop Quadword (%% (rdi,24))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd2;
                           (* ADCX (% rdx) (% rdx) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% rdx) (% rbx) *)
  0x48; 0x89; 0x57; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% rdx) *)
  0x48; 0x8b; 0x56; 0x10;  (* MOV (% rdx) (Memop Quadword (%% (rsi,16))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rax) (% rdx,% rdx) *)
  0x48; 0x8b; 0x57; 0x20;  (* MOV (% rdx) (Memop Quadword (%% (rdi,32))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd2;
                           (* ADCX (% rdx) (% rdx) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADOX (% rdx) (% rax) *)
  0x48; 0x89; 0x57; 0x20;  (* MOV (Memop Quadword (%% (rdi,32))) (% rdx) *)
  0x48; 0x8b; 0x57; 0x28;  (* MOV (% rdx) (Memop Quadword (%% (rdi,40))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd2;
                           (* ADCX (% rdx) (% rdx) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% rdx) (% rbx) *)
  0x48; 0x89; 0x57; 0x28;  (* MOV (Memop Quadword (%% (rdi,40))) (% rdx) *)
  0x48; 0x8b; 0x56; 0x18;  (* MOV (% rdx) (Memop Quadword (%% (rsi,24))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rax) (% rdx,% rdx) *)
  0x48; 0x8b; 0x57; 0x30;  (* MOV (% rdx) (Memop Quadword (%% (rdi,48))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd2;
                           (* ADCX (% rdx) (% rdx) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADOX (% rdx) (% rax) *)
  0x48; 0x89; 0x57; 0x30;  (* MOV (Memop Quadword (%% (rdi,48))) (% rdx) *)
  0x48; 0x8b; 0x57; 0x38;  (* MOV (% rdx) (Memop Quadword (%% (rdi,56))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd2;
                           (* ADCX (% rdx) (% rdx) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% rdx) (% rbx) *)
  0x48; 0x89; 0x57; 0x38;  (* MOV (Memop Quadword (%% (rdi,56))) (% rdx) *)
  0x48; 0x8b; 0x56; 0x20;  (* MOV (% rdx) (Memop Quadword (%% (rsi,32))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rax) (% rdx,% rdx) *)
  0x48; 0x8b; 0x57; 0x40;  (* MOV (% rdx) (Memop Quadword (%% (rdi,64))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd2;
                           (* ADCX (% rdx) (% rdx) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADOX (% rdx) (% rax) *)
  0x48; 0x89; 0x57; 0x40;  (* MOV (Memop Quadword (%% (rdi,64))) (% rdx) *)
  0x48; 0x8b; 0x57; 0x48;  (* MOV (% rdx) (Memop Quadword (%% (rdi,72))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd2;
                           (* ADCX (% rdx) (% rdx) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% rdx) (% rbx) *)
  0x48; 0x89; 0x57; 0x48;  (* MOV (Memop Quadword (%% (rdi,72))) (% rdx) *)
  0x48; 0x8b; 0x56; 0x28;  (* MOV (% rdx) (Memop Quadword (%% (rsi,40))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rax) (% rdx,% rdx) *)
  0x48; 0x8b; 0x57; 0x50;  (* MOV (% rdx) (Memop Quadword (%% (rdi,80))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd2;
                           (* ADCX (% rdx) (% rdx) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADOX (% rdx) (% rax) *)
  0x48; 0x89; 0x57; 0x50;  (* MOV (Memop Quadword (%% (rdi,80))) (% rdx) *)
  0x48; 0x8b; 0x57; 0x58;  (* MOV (% rdx) (Memop Quadword (%% (rdi,88))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd2;
                           (* ADCX (% rdx) (% rdx) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% rdx) (% rbx) *)
  0x48; 0x89; 0x57; 0x58;  (* MOV (Memop Quadword (%% (rdi,88))) (% rdx) *)
  0x48; 0x8b; 0x56; 0x30;  (* MOV (% rdx) (Memop Quadword (%% (rsi,48))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rax) (% rdx,% rdx) *)
  0x48; 0x8b; 0x57; 0x60;  (* MOV (% rdx) (Memop Quadword (%% (rdi,96))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd2;
                           (* ADCX (% rdx) (% rdx) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADOX (% rdx) (% rax) *)
  0x48; 0x89; 0x57; 0x60;  (* MOV (Memop Quadword (%% (rdi,96))) (% rdx) *)
  0x48; 0x8b; 0x57; 0x68;  (* MOV (% rdx) (Memop Quadword (%% (rdi,104))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd2;
                           (* ADCX (% rdx) (% rdx) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% rdx) (% rbx) *)
  0x48; 0x89; 0x57; 0x68;  (* MOV (Memop Quadword (%% (rdi,104))) (% rdx) *)
  0x48; 0x8b; 0x56; 0x38;  (* MOV (% rdx) (Memop Quadword (%% (rsi,56))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rax) (% rdx,% rdx) *)
  0x48; 0x8b; 0x57; 0x70;  (* MOV (% rdx) (Memop Quadword (%% (rdi,112))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd2;
                           (* ADCX (% rdx) (% rdx) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADOX (% rdx) (% rax) *)
  0x48; 0x89; 0x57; 0x70;  (* MOV (Memop Quadword (%% (rdi,112))) (% rdx) *)
  0x48; 0x8b; 0x57; 0x78;  (* MOV (% rdx) (Memop Quadword (%% (rdi,120))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd2;
                           (* ADCX (% rdx) (% rdx) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% rdx) (% rbx) *)
  0x48; 0x89; 0x57; 0x78;  (* MOV (Memop Quadword (%% (rdi,120))) (% rdx) *)
  0x48; 0x8b; 0x56; 0x40;  (* MOV (% rdx) (Memop Quadword (%% (rsi,64))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rax) (% rdx,% rdx) *)
  0x48; 0x8b; 0x97; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rdi,128))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd2;
                           (* ADCX (% rdx) (% rdx) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADOX (% rdx) (% rax) *)
  0x48; 0x89; 0x97; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,128))) (% rdx) *)
  0x48; 0x8b; 0x97; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rdi,136))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd2;
                           (* ADCX (% rdx) (% rdx) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% rdx) (% rbx) *)
  0x48; 0x89; 0x97; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,136))) (% rdx) *)
  0x48; 0x8b; 0x56; 0x48;  (* MOV (% rdx) (Memop Quadword (%% (rsi,72))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rax) (% rdx,% rdx) *)
  0x48; 0x8b; 0x97; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rdi,144))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd2;
                           (* ADCX (% rdx) (% rdx) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADOX (% rdx) (% rax) *)
  0x48; 0x89; 0x97; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,144))) (% rdx) *)
  0x48; 0x8b; 0x97; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rdi,152))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd2;
                           (* ADCX (% rdx) (% rdx) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% rdx) (% rbx) *)
  0x48; 0x89; 0x97; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,152))) (% rdx) *)
  0x48; 0x8b; 0x56; 0x50;  (* MOV (% rdx) (Memop Quadword (%% (rsi,80))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rax) (% rdx,% rdx) *)
  0x48; 0x8b; 0x97; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rdi,160))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd2;
                           (* ADCX (% rdx) (% rdx) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADOX (% rdx) (% rax) *)
  0x48; 0x89; 0x97; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,160))) (% rdx) *)
  0x48; 0x8b; 0x97; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rdi,168))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd2;
                           (* ADCX (% rdx) (% rdx) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% rdx) (% rbx) *)
  0x48; 0x89; 0x97; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,168))) (% rdx) *)
  0x48; 0x8b; 0x56; 0x58;  (* MOV (% rdx) (Memop Quadword (%% (rsi,88))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rax) (% rdx,% rdx) *)
  0x48; 0x8b; 0x97; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rdi,176))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd2;
                           (* ADCX (% rdx) (% rdx) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADOX (% rdx) (% rax) *)
  0x48; 0x89; 0x97; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,176))) (% rdx) *)
  0x48; 0x8b; 0x97; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rdi,184))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd2;
                           (* ADCX (% rdx) (% rdx) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% rdx) (% rbx) *)
  0x48; 0x89; 0x97; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,184))) (% rdx) *)
  0x48; 0x8b; 0x56; 0x60;  (* MOV (% rdx) (Memop Quadword (%% (rsi,96))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rax) (% rdx,% rdx) *)
  0x48; 0x8b; 0x97; 0xc0; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rdi,192))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd2;
                           (* ADCX (% rdx) (% rdx) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADOX (% rdx) (% rax) *)
  0x48; 0x89; 0x97; 0xc0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,192))) (% rdx) *)
  0x48; 0x8b; 0x97; 0xc8; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rdi,200))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd2;
                           (* ADCX (% rdx) (% rdx) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% rdx) (% rbx) *)
  0x48; 0x89; 0x97; 0xc8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,200))) (% rdx) *)
  0x48; 0x8b; 0x56; 0x68;  (* MOV (% rdx) (Memop Quadword (%% (rsi,104))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rax) (% rdx,% rdx) *)
  0x48; 0x8b; 0x97; 0xd0; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rdi,208))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd2;
                           (* ADCX (% rdx) (% rdx) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADOX (% rdx) (% rax) *)
  0x48; 0x89; 0x97; 0xd0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,208))) (% rdx) *)
  0x48; 0x8b; 0x97; 0xd8; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rdi,216))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd2;
                           (* ADCX (% rdx) (% rdx) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% rdx) (% rbx) *)
  0x48; 0x89; 0x97; 0xd8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,216))) (% rdx) *)
  0x48; 0x8b; 0x56; 0x70;  (* MOV (% rdx) (Memop Quadword (%% (rsi,112))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rax) (% rdx,% rdx) *)
  0x48; 0x8b; 0x97; 0xe0; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rdi,224))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd2;
                           (* ADCX (% rdx) (% rdx) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADOX (% rdx) (% rax) *)
  0x48; 0x89; 0x97; 0xe0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,224))) (% rdx) *)
  0x48; 0x8b; 0x97; 0xe8; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rdi,232))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd2;
                           (* ADCX (% rdx) (% rdx) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% rdx) (% rbx) *)
  0x48; 0x89; 0x97; 0xe8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,232))) (% rdx) *)
  0x48; 0x8b; 0x56; 0x78;  (* MOV (% rdx) (Memop Quadword (%% (rsi,120))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rax) (% rdx,% rdx) *)
  0x48; 0x8b; 0x97; 0xf0; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rdi,240))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd2;
                           (* ADCX (% rdx) (% rdx) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADOX (% rdx) (% rax) *)
  0x48; 0x89; 0x97; 0xf0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,240))) (% rdx) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xdd;
                           (* ADCX (% rbx) (% rbp) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xdd;
                           (* ADOX (% rbx) (% rbp) *)
  0x48; 0x89; 0x9f; 0xf8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,248))) (% rbx) *)
  0xc3                     (* RET *)
];;

let bignum_ksqr_32_64_tmc = define_trimmed "bignum_ksqr_32_64_tmc" bignum_ksqr_32_64_mc;;

let BIGNUM_KSQR_32_64_EXEC = X86_MK_EXEC_RULE bignum_ksqr_32_64_tmc;;

(* ------------------------------------------------------------------------- *)
(* The lemma for the embedded subroutine (close to bignum_sqr_16_32).        *)
(* ------------------------------------------------------------------------- *)

let local_ksqr_16_32_tmc_def = define
 `local_ksqr_16_32_tmc = ITER 0x8d6 TL bignum_ksqr_32_64_tmc`;;

let local_ksqr_16_32_tmc =
  GEN_REWRITE_RULE DEPTH_CONV [TL]
    (REWRITE_RULE[bignum_ksqr_32_64_tmc; CONJUNCT1 ITER]
      (CONV_RULE(RAND_CONV(TOP_DEPTH_CONV
         (RATOR_CONV(LAND_CONV num_CONV) THENC GEN_REWRITE_CONV I [ITER])))
         local_ksqr_16_32_tmc_def));;

let LOCAL_KSQR_16_32_EXEC = X86_MK_EXEC_RULE local_ksqr_16_32_tmc;;

let LOCAL_KSQR_16_32_CORRECT = prove
 (`!z x a pc.
     nonoverlapping (word pc,3440) (z,8 * 32) /\
     nonoverlapping (x,8 * 16) (z,8 * 32)
     ==> ensures x86
          (\s. bytes_loaded s (word pc) local_ksqr_16_32_tmc /\
               read RIP s = word pc /\
               C_ARGUMENTS [z; x] s /\
               bignum_from_memory (x,16) s = a)
          (\s. read RIP s = word (pc + 3439) /\
               bignum_from_memory (z,32) s = a EXP 2)
          (MAYCHANGE [RIP; RAX; RBP; RBX; RDX;
                      R8; R9; R10; R11; R12; R13; R14; R15] ,,
           MAYCHANGE [memory :> bytes(z,8 * 32)] ,,
           MAYCHANGE SOME_FLAGS)`,
  REWRITE_TAC[ADD_CLAUSES] THEN
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `a:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,16) s0` THEN
  X86_ACCSTEPS_TAC LOCAL_KSQR_16_32_EXEC (1--607) (1--607) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  EXPAND_TAC "a" THEN REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Common tactic for the main part with standard and Windows ABIs            *)
(* ------------------------------------------------------------------------- *)

let tac mc execth pcinst =
  let maintac = X86_SUBROUTINE_SIM_TAC
   (mc,execth,dest_small_numeral(rand pcinst),
    local_ksqr_16_32_tmc,LOCAL_KSQR_16_32_CORRECT)
    [`read RDI s`; `read RSI s`;
     `read (memory :> bytes (read RSI s,8 * 16)) s`;
     pcinst]
  and posttac =
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM ADD_ASSOC]) THEN
    RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_ADD_CONV)) in
  let LOCAL_KSQR_16_32_TAC n = maintac n THEN posttac in

  REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
  BIGNUM_TERMRANGE_TAC `32` `a:num` THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
  MP_TAC(ISPECL [`x:int64`; `16`; `16`] BIGNUM_FROM_MEMORY_SPLIT) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV(NUM_ADD_CONV ORELSEC NUM_MULT_CONV))) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY ABBREV_TAC
   [`ahi = read (memory :> bytes (word_add x (word 128),8 * 16)) s0`;
    `alo = read (memory :> bytes (x,8 * 16)) s0`] THEN

  (*** First nested squaring: low part ***)

  X86_STEPS_TAC execth (1--2) THEN
  LOCAL_KSQR_16_32_TAC 3 THEN
  X86_STEPS_TAC execth [4] THEN

  (*** Second nested squaring: high part ***)

  X86_STEPS_TAC execth (5--7) THEN
  LOCAL_KSQR_16_32_TAC 8 THEN
  X86_STEPS_TAC execth [9] THEN

  (*** Absolute difference computation ***)

  BIGNUM_LDIGITIZE_TAC "x_" `bignum_from_memory(x,32) s9` THEN
  X86_ACCSTEPS_TAC execth
   (map (fun n -> 11 + 3 * n) (0--15)) (10--59) THEN
  SUBGOAL_THEN `carry_s56 <=> alo < ahi` (ASSUME_TAC o SYM) THENL
   [MAP_EVERY EXPAND_TAC ["ahi"; "alo"] THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `1024` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VAL_EQ_0; WORD_NEG_EQ_0; WORD_BITVAL_EQ_0]) THEN
  X86_ACCSTEPS_TAC execth
   (map (fun n -> 63 + 6 * n) (0--15)) (60--155) THEN
  SUBGOAL_THEN
   `&(read (memory :> bytes (t,8 * 16)) s155):real = abs(&alo - &ahi)`
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
    ASM_CASES_TAC `carry_s56:bool` THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
    DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Discard elementwise assignments and things to do with x ***)

  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes64 x) s = y`] THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `x:int64` o concl))) THEN

  (*** Digitize low and high products ***)

  BIGNUM_LDIGITIZE_TAC "l_" `read (memory :> bytes (z,8 * 32)) s155` THEN
  BIGNUM_LDIGITIZE_TAC "h_"
   `read (memory :> bytes (word_add z (word 256),8 * 32)) s155` THEN

  (*** Simulate the interlocking part, just deduce top carry zeroness ***)

  X86_ACCSTEPS_TAC execth
   (sort (<)  (map (fun n -> 158 + 4 * n) (0--31) @
               map (fun n -> 159 + 4 * n) (0--31) @ [286]))
   (156--287) THEN
  UNDISCH_TAC
   `&2 pow 64 * &(bitval carry_s286) + &(val(sum_s286:int64)) =
    &(val(word(bitval carry_s283):int64)) + &(bitval carry_s282)` THEN
  REWRITE_TAC[VAL_WORD_BITVAL] THEN
  DISCH_THEN(MP_TAC o end_itlist CONJ o DECARRY_RULE o CONJUNCTS) THEN
  STRIP_TAC THEN

  (*** Third nested squaring: absolute difference ***)

  ABBREV_TAC `adiff = read (memory :> bytes (t,8 * 16)) s287` THEN
  X86_STEPS_TAC execth (288--291) THEN
  LOCAL_KSQR_16_32_TAC 292 THEN
  X86_STEPS_TAC execth [293] THEN

  (*** Digitize the mid-product and simulate main bit of its subtraction ***)

  BIGNUM_LDIGITIZE_TAC "m_"
   `read (memory :> bytes (word_add t (word 256),8 * 32)) s293` THEN

  X86_ACCSTEPS_TAC execth
   (map (fun n -> 295 + 3 * n) (0--32)) (294--391) THEN

  (*** Deduce that we don't wrap the suspended carry negative ***)

  SUBGOAL_THEN
   `(&0):real <= --(&2 pow 64) * &(bitval carry_s391) + &(val(sum_s391:int64))`
  MP_TAC THENL
   [ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN
    MATCH_MP_TAC REAL_LE_REVERSE_INTEGERS THEN
    REPEAT(CONJ_TAC THENL [REAL_INTEGER_TAC; ALL_TAC]) THEN
    MATCH_MP_TAC(REAL_ARITH
     `!m:real. &0 <= m /\ m - &2 pow 2048 * cc < &2 pow 2048
      ==> ~(cc + &1 <= &0)`) THEN
    EXISTS_TAC `(&alo:real) pow 2 + &ahi pow 2 - (&alo - &ahi) pow 2` THEN
    CONJ_TAC THENL
     [CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
      REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0];
      ALL_TAC] THEN
    ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
    UNDISCH_THEN `&adiff:real = abs(&alo - &ahi)` (SUBST1_TAC o SYM) THEN
    REWRITE_TAC[REAL_ABS_NUM; REAL_OF_NUM_POW] THEN
    REPEAT(FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (ARITH_RULE
     `a = b EXP 2 ==> b EXP 2 = a`))) THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC(LAND_CONV REAL_POLY_CONV) THEN BOUNDER_TAC[];
    DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
     `&0 <= --e * c + s
      ==> s < e /\ (e * c < e * &1 ==> e * c = &0) ==> e * c = &0`)) THEN
    SIMP_TAC[REAL_LT_LMUL_EQ; REAL_LT_POW2; REAL_ENTIRE] THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES; VAL_BOUND_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE
     [REAL_MUL_RZERO; REAL_ADD_LID; REAL_SUB_RZERO])] THEN

  (*** Finish the carry propagation, and then the finale ***)

  X86_ACCSTEPS_TAC execth
   (393--408) (392--408) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_THEN
   `&(val(sum_s391:int64)) = &(val(sum_s286:int64)) - &(bitval carry_s388)`
  SUBST_ALL_TAC THEN
  UNDISCH_THEN
   `&(val(sum_s286:int64)) = &(bitval carry_s283) + &(bitval carry_s282)`
  SUBST_ALL_TAC THEN
  SUBST1_TAC(ARITH_RULE `512 = 8 * 64`) THEN
  REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; GSYM REAL_OF_NUM_CLAUSES] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`64 * 64`; `&0:real`] THEN
  REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0; BIGNUM_FROM_MEMORY_BOUND] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[EXP_ADD; ARITH_RULE `64 * 64 = 64 * 32 + 64 * 32`] THEN
    ASM_SIMP_TAC[EXP_2; LT_MULT2];
    REWRITE_TAC[INTEGER_CLOSED]] THEN
  EXPAND_TAC "a" THEN REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  ONCE_REWRITE_TAC[REAL_ARITH
   `(e * h + l:real) pow 2 =
    l pow 2 + e pow 2 * h pow 2 +
    e * (h pow 2 + l pow 2 - (l - h) pow 2)`] THEN
  ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
  UNDISCH_THEN `&adiff:real = abs(&alo - &ahi)` (SUBST1_TAC o SYM) THEN
  REWRITE_TAC[REAL_ABS_NUM; REAL_OF_NUM_POW] THEN
  REPEAT(FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (ARITH_RULE
   `a = b EXP 2 ==> b EXP 2 = a`))) THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_EXPAND_CONV) THEN
  ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;;

(* ------------------------------------------------------------------------- *)
(* Proof of the standard ABI version.                                        *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_KSQR_32_64_NOIBT_SUBROUTINE_CORRECT = time prove
 (`!z x t a pc stackpointer returnaddress.
     ALL (nonoverlapping (word_sub stackpointer (word 56),64))
         [(z,8 * 64); (t,8 * 72)] /\
     ALL (nonoverlapping (word_sub stackpointer (word 56),56))
         [(word pc,LENGTH bignum_ksqr_32_64_tmc); (x,8 * 32)] /\
     nonoverlapping (z,8 * 64) (t,8 * 72) /\
     ALLPAIRS nonoverlapping
         [(z,8 * 64); (t,8 * 72)] [(word pc,LENGTH bignum_ksqr_32_64_tmc); (x,8 * 32)]
     ==> ensures x86
          (\s. bytes_loaded s (word pc) bignum_ksqr_32_64_tmc /\
               read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               C_ARGUMENTS [z; x; t] s /\
               bignum_from_memory (x,32) s = a)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               bignum_from_memory (z,64) s = a EXP 2)
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(z,8 * 64); memory :> bytes(t,8 * 72);
                      memory :> bytes(word_sub stackpointer (word 56),56)])`,
  REWRITE_TAC[fst BIGNUM_KSQR_32_64_EXEC] THEN
  REWRITE_TAC [MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `t:int64`; `a:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 56 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  REWRITE_TAC[ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN STRIP_TAC THEN

  (*** Start and end boilerplate for save and restore of registers ***)

  SUBGOAL_THEN
   `ensures x86
     (\s. bytes_loaded s (word pc) bignum_ksqr_32_64_tmc /\
          read RIP s = word(pc + 0xa) /\
          read RSP s = word_add stackpointer (word 8) /\
          C_ARGUMENTS [z; x; t] s /\
          bignum_from_memory (x,32) s = a)
     (\s. read RIP s = word(pc + 0x8cb) /\
          bignum_from_memory (z,64) s = a EXP 2)
     (MAYCHANGE [RIP; RSI; RDI; RAX; RCX; RDX; R8; R9; R10; R11;
                 RBX; RBP; R12; R13; R14; R15] ,,
      MAYCHANGE [memory :> bytes(z,8 * 64); memory :> bytes(t,8 * 72);
                 memory :> bytes(stackpointer,8)] ,,
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
      X86_STEPS_TAC BIGNUM_KSQR_32_64_EXEC (1--6) THEN
      MP_TAC th) THEN
    X86_BIGSTEP_TAC BIGNUM_KSQR_32_64_EXEC "s7" THEN
    X86_STEPS_TAC BIGNUM_KSQR_32_64_EXEC (8--14) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]] THEN

  tac bignum_ksqr_32_64_tmc BIGNUM_KSQR_32_64_EXEC `pc + 0x8d6`);;

let BIGNUM_KSQR_32_64_SUBROUTINE_CORRECT = time prove
 (`!z x t a pc stackpointer returnaddress.
     ALL (nonoverlapping (word_sub stackpointer (word 56),64))
         [(z,8 * 64); (t,8 * 72)] /\
     ALL (nonoverlapping (word_sub stackpointer (word 56),56))
         [(word pc,LENGTH bignum_ksqr_32_64_mc); (x,8 * 32)] /\
     nonoverlapping (z,8 * 64) (t,8 * 72) /\
     ALLPAIRS nonoverlapping
         [(z,8 * 64); (t,8 * 72)] [(word pc,LENGTH bignum_ksqr_32_64_mc); (x,8 * 32)]
     ==> ensures x86
          (\s. bytes_loaded s (word pc) bignum_ksqr_32_64_mc /\
               read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               C_ARGUMENTS [z; x; t] s /\
               bignum_from_memory (x,32) s = a)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               bignum_from_memory (z,64) s = a EXP 2)
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(z,8 * 64); memory :> bytes(t,8 * 72);
                      memory :> bytes(word_sub stackpointer (word 56),56)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_KSQR_32_64_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_ksqr_32_64_windows_mc = define_from_elf
   "bignum_ksqr_32_64_windows_mc" "x86/fastmul/bignum_ksqr_32_64.obj";;

let bignum_ksqr_32_64_windows_tmc = define_trimmed "bignum_ksqr_32_64_windows_tmc" bignum_ksqr_32_64_windows_mc;;

let WINDOWS_BIGNUM_KSQR_32_64_EXEC =
  X86_MK_EXEC_RULE bignum_ksqr_32_64_windows_tmc;;

let BIGNUM_KSQR_32_64_NOIBT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x t a pc stackpointer returnaddress.
     ALL (nonoverlapping (word_sub stackpointer (word 72),80))
         [(z,8 * 64); (t,8 * 72)] /\
     ALL (nonoverlapping (word_sub stackpointer (word 72),72))
         [(word pc,LENGTH bignum_ksqr_32_64_windows_tmc); (x,8 * 32)] /\
     nonoverlapping (z,8 * 64) (t,8 * 72) /\
     ALLPAIRS nonoverlapping
         [(z,8 * 64); (t,8 * 72)] [(word pc,LENGTH bignum_ksqr_32_64_windows_tmc); (x,8 * 32)]
     ==> ensures x86
          (\s. bytes_loaded s (word pc) bignum_ksqr_32_64_windows_tmc /\
               read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               WINDOWS_C_ARGUMENTS [z; x; t] s /\
               bignum_from_memory (x,32) s = a)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               bignum_from_memory (z,64) s = a EXP 2)
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(z,8 * 64); memory :> bytes(t,8 * 72);
                      memory :> bytes(word_sub stackpointer (word 72),72)])`,
  REWRITE_TAC[fst WINDOWS_BIGNUM_KSQR_32_64_EXEC] THEN
  REWRITE_TAC [WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `t:int64`; `a:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 72 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[WINDOWS_C_ARGUMENTS; WINDOWS_C_RETURN; SOME_FLAGS] THEN
  REWRITE_TAC[ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN STRIP_TAC THEN

  (*** Start and end boilerplate for save and restore of registers ***)

  SUBGOAL_THEN
   `ensures x86
     (\s. bytes_loaded s (word pc) bignum_ksqr_32_64_windows_tmc /\
          read RIP s = word(pc + 0x15) /\
          read RSP s = word_add stackpointer (word 8) /\
          C_ARGUMENTS [z; x; t] s /\
          bignum_from_memory (x,32) s = a)
     (\s. read RIP s = word(pc + 0x8d6) /\
          bignum_from_memory (z,64) s = a EXP 2)
     (MAYCHANGE [RIP; RSI; RDI; RAX; RCX; RDX; R8; R9; R10; R11;
                 RBX; RBP; R12; R13; R14; R15] ,,
      MAYCHANGE [memory :> bytes(z,8 * 64); memory :> bytes(t,8 * 72);
                 memory :> bytes(stackpointer,8)] ,,
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
      X86_STEPS_TAC WINDOWS_BIGNUM_KSQR_32_64_EXEC (1--11) THEN
      MP_TAC th) THEN
    X86_BIGSTEP_TAC WINDOWS_BIGNUM_KSQR_32_64_EXEC "s12" THEN
    X86_STEPS_TAC WINDOWS_BIGNUM_KSQR_32_64_EXEC (13--21) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]] THEN

  tac bignum_ksqr_32_64_windows_tmc WINDOWS_BIGNUM_KSQR_32_64_EXEC
   `pc + 0x8e3`);;

let BIGNUM_KSQR_32_64_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x t a pc stackpointer returnaddress.
     ALL (nonoverlapping (word_sub stackpointer (word 72),80))
         [(z,8 * 64); (t,8 * 72)] /\
     ALL (nonoverlapping (word_sub stackpointer (word 72),72))
         [(word pc,LENGTH bignum_ksqr_32_64_windows_mc); (x,8 * 32)] /\
     nonoverlapping (z,8 * 64) (t,8 * 72) /\
     ALLPAIRS nonoverlapping
         [(z,8 * 64); (t,8 * 72)] [(word pc,LENGTH bignum_ksqr_32_64_windows_mc); (x,8 * 32)]
     ==> ensures x86
          (\s. bytes_loaded s (word pc) bignum_ksqr_32_64_windows_mc /\
               read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               WINDOWS_C_ARGUMENTS [z; x; t] s /\
               bignum_from_memory (x,32) s = a)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               bignum_from_memory (z,64) s = a EXP 2)
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(z,8 * 64); memory :> bytes(t,8 * 72);
                      memory :> bytes(word_sub stackpointer (word 72),72)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_KSQR_32_64_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

