(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Scalar multiplication for NIST P-521.                                     *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "common/ecencoding.ml";;
needs "EC/jacobian.ml";;
needs "EC/nistp521.ml";;

prioritize_int();;
prioritize_real();;
prioritize_num();;

needs "x86/proofs/bignum_mod_n521_9_alt.ml";;
needs "x86/proofs/bignum_mod_p521_9.ml";;

(* ------------------------------------------------------------------------- *)
(* Code.                                                                     *)
(* ------------------------------------------------------------------------- *)

(**** print_literal_from_elf "x86/p521/p521_jscalarmul_alt.o";;
 ****)

let p521_jscalarmul_alt_mc = define_assert_from_elf
  "p521_jscalarmul_alt_mc" "x86/p521/p521_jscalarmul_alt.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x41; 0x57;              (* PUSH (% r15) *)
  0x41; 0x56;              (* PUSH (% r14) *)
  0x41; 0x55;              (* PUSH (% r13) *)
  0x41; 0x54;              (* PUSH (% r12) *)
  0x55;                    (* PUSH (% rbp) *)
  0x53;                    (* PUSH (% rbx) *)
  0x48; 0x81; 0xec; 0xc0; 0x0f; 0x00; 0x00;
                           (* SUB (% rsp) (Imm32 (word 4032)) *)
  0x48; 0x89; 0xbc; 0x24; 0x78; 0x0f; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,3960))) (% rdi) *)
  0x48; 0x89; 0xd3;        (* MOV (% rbx) (% rdx) *)
  0x48; 0x8d; 0x3c; 0x24;  (* LEA (% rdi) (%% (rsp,0)) *)
  0xe8; 0x9e; 0x1a; 0x00; 0x00;
                           (* CALL (Imm32 (word 6814)) *)
  0x48; 0x8d; 0xbc; 0x24; 0xf8; 0x01; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rsp,504)) *)
  0x48; 0x89; 0xde;        (* MOV (% rsi) (% rbx) *)
  0xe8; 0xe6; 0x19; 0x00; 0x00;
                           (* CALL (Imm32 (word 6630)) *)
  0x48; 0x8d; 0xbc; 0x24; 0x40; 0x02; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rsp,576)) *)
  0x48; 0x8d; 0x73; 0x48;  (* LEA (% rsi) (%% (rbx,72)) *)
  0xe8; 0xd5; 0x19; 0x00; 0x00;
                           (* CALL (Imm32 (word 6613)) *)
  0x48; 0x8d; 0xbc; 0x24; 0x88; 0x02; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rsp,648)) *)
  0x48; 0x8d; 0xb3; 0x90; 0x00; 0x00; 0x00;
                           (* LEA (% rsi) (%% (rbx,144)) *)
  0xe8; 0xc1; 0x19; 0x00; 0x00;
                           (* CALL (Imm32 (word 6593)) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0x48; 0xf7; 0xd0;        (* NOT (% rax) *)
  0x49; 0xb8; 0x09; 0x64; 0x38; 0x91; 0x1e; 0xb7; 0x6f; 0xbb;
                           (* MOV (% r8) (Imm64 (word 13506215149420700681)) *)
  0x4c; 0x2b; 0x04; 0x24;  (* SUB (% r8) (Memop Quadword (%% (rsp,0))) *)
  0x49; 0xb9; 0xae; 0x47; 0x9c; 0x89; 0xb8; 0xc9; 0xb5; 0x3b;
                           (* MOV (% r9) (Imm64 (word 4302566813442262958)) *)
  0x4c; 0x1b; 0x4c; 0x24; 0x08;
                           (* SBB (% r9) (Memop Quadword (%% (rsp,8))) *)
  0x49; 0xba; 0xd0; 0xa5; 0x09; 0xf7; 0x48; 0x01; 0xcc; 0x7f;
                           (* MOV (% r10) (Imm64 (word 9208736750959699408)) *)
  0x4c; 0x1b; 0x54; 0x24; 0x10;
                           (* SBB (% r10) (Memop Quadword (%% (rsp,16))) *)
  0x49; 0xbb; 0x6b; 0x96; 0x2f; 0xbf; 0x83; 0x87; 0x86; 0x51;
                           (* MOV (% r11) (Imm64 (word 5874531763869423211)) *)
  0x4c; 0x1b; 0x5c; 0x24; 0x18;
                           (* SBB (% r11) (Memop Quadword (%% (rsp,24))) *)
  0x4c; 0x8d; 0x60; 0xfb;  (* LEA (% r12) (%% (rax,18446744073709551611)) *)
  0x4c; 0x1b; 0x64; 0x24; 0x20;
                           (* SBB (% r12) (Memop Quadword (%% (rsp,32))) *)
  0x49; 0x89; 0xc5;        (* MOV (% r13) (% rax) *)
  0x4c; 0x1b; 0x6c; 0x24; 0x28;
                           (* SBB (% r13) (Memop Quadword (%% (rsp,40))) *)
  0x49; 0x89; 0xc6;        (* MOV (% r14) (% rax) *)
  0x4c; 0x1b; 0x74; 0x24; 0x30;
                           (* SBB (% r14) (Memop Quadword (%% (rsp,48))) *)
  0x49; 0x89; 0xc7;        (* MOV (% r15) (% rax) *)
  0x4c; 0x1b; 0x7c; 0x24; 0x38;
                           (* SBB (% r15) (Memop Quadword (%% (rsp,56))) *)
  0x48; 0xc7; 0xc0; 0xff; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Imm32 (word 511)) *)
  0x48; 0x8b; 0x4c; 0x24; 0x40;
                           (* MOV (% rcx) (Memop Quadword (%% (rsp,64))) *)
  0x48; 0x19; 0xc8;        (* SBB (% rax) (% rcx) *)
  0x48; 0x0f; 0xba; 0xe1; 0x08;
                           (* BT (% rcx) (Imm8 (word 8)) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x0f; 0x43; 0x04; 0x24;
                           (* CMOVAE (% r8) (Memop Quadword (%% (rsp,0))) *)
  0x4c; 0x0f; 0x43; 0x4c; 0x24; 0x08;
                           (* CMOVAE (% r9) (Memop Quadword (%% (rsp,8))) *)
  0x4c; 0x0f; 0x43; 0x54; 0x24; 0x10;
                           (* CMOVAE (% r10) (Memop Quadword (%% (rsp,16))) *)
  0x4c; 0x0f; 0x43; 0x5c; 0x24; 0x18;
                           (* CMOVAE (% r11) (Memop Quadword (%% (rsp,24))) *)
  0x4c; 0x0f; 0x43; 0x64; 0x24; 0x20;
                           (* CMOVAE (% r12) (Memop Quadword (%% (rsp,32))) *)
  0x4c; 0x0f; 0x43; 0x6c; 0x24; 0x28;
                           (* CMOVAE (% r13) (Memop Quadword (%% (rsp,40))) *)
  0x4c; 0x0f; 0x43; 0x74; 0x24; 0x30;
                           (* CMOVAE (% r14) (Memop Quadword (%% (rsp,48))) *)
  0x4c; 0x0f; 0x43; 0x7c; 0x24; 0x38;
                           (* CMOVAE (% r15) (Memop Quadword (%% (rsp,56))) *)
  0x48; 0x0f; 0x43; 0x44; 0x24; 0x40;
                           (* CMOVAE (% rax) (Memop Quadword (%% (rsp,64))) *)
  0x4c; 0x89; 0x04; 0x24;  (* MOV (Memop Quadword (%% (rsp,0))) (% r8) *)
  0x4c; 0x89; 0x4c; 0x24; 0x08;
                           (* MOV (Memop Quadword (%% (rsp,8))) (% r9) *)
  0x4c; 0x89; 0x54; 0x24; 0x10;
                           (* MOV (Memop Quadword (%% (rsp,16))) (% r10) *)
  0x4c; 0x89; 0x5c; 0x24; 0x18;
                           (* MOV (Memop Quadword (%% (rsp,24))) (% r11) *)
  0x4c; 0x89; 0x64; 0x24; 0x20;
                           (* MOV (Memop Quadword (%% (rsp,32))) (% r12) *)
  0x4c; 0x89; 0x6c; 0x24; 0x28;
                           (* MOV (Memop Quadword (%% (rsp,40))) (% r13) *)
  0x4c; 0x89; 0x74; 0x24; 0x30;
                           (* MOV (Memop Quadword (%% (rsp,48))) (% r14) *)
  0x4c; 0x89; 0x7c; 0x24; 0x38;
                           (* MOV (Memop Quadword (%% (rsp,56))) (% r15) *)
  0x48; 0x89; 0x44; 0x24; 0x40;
                           (* MOV (Memop Quadword (%% (rsp,64))) (% rax) *)
  0x4c; 0x8b; 0x84; 0x24; 0x40; 0x02; 0x00; 0x00;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,576))) *)
  0x4c; 0x8b; 0x8c; 0x24; 0x48; 0x02; 0x00; 0x00;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,584))) *)
  0x4c; 0x8b; 0x94; 0x24; 0x50; 0x02; 0x00; 0x00;
                           (* MOV (% r10) (Memop Quadword (%% (rsp,592))) *)
  0x4c; 0x8b; 0x9c; 0x24; 0x58; 0x02; 0x00; 0x00;
                           (* MOV (% r11) (Memop Quadword (%% (rsp,600))) *)
  0x4c; 0x8b; 0xa4; 0x24; 0x60; 0x02; 0x00; 0x00;
                           (* MOV (% r12) (Memop Quadword (%% (rsp,608))) *)
  0x4c; 0x8b; 0xac; 0x24; 0x68; 0x02; 0x00; 0x00;
                           (* MOV (% r13) (Memop Quadword (%% (rsp,616))) *)
  0x4c; 0x8b; 0xb4; 0x24; 0x70; 0x02; 0x00; 0x00;
                           (* MOV (% r14) (Memop Quadword (%% (rsp,624))) *)
  0x4c; 0x8b; 0xbc; 0x24; 0x78; 0x02; 0x00; 0x00;
                           (* MOV (% r15) (Memop Quadword (%% (rsp,632))) *)
  0x48; 0x8b; 0x84; 0x24; 0x80; 0x02; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,640))) *)
  0x4c; 0x89; 0xc3;        (* MOV (% rbx) (% r8) *)
  0x4c; 0x89; 0xe5;        (* MOV (% rbp) (% r12) *)
  0x4c; 0x09; 0xcb;        (* OR (% rbx) (% r9) *)
  0x4c; 0x09; 0xed;        (* OR (% rbp) (% r13) *)
  0x4c; 0x09; 0xd3;        (* OR (% rbx) (% r10) *)
  0x4c; 0x09; 0xf5;        (* OR (% rbp) (% r14) *)
  0x4c; 0x09; 0xdb;        (* OR (% rbx) (% r11) *)
  0x4c; 0x09; 0xfd;        (* OR (% rbp) (% r15) *)
  0x48; 0x09; 0xeb;        (* OR (% rbx) (% rbp) *)
  0x48; 0x09; 0xc3;        (* OR (% rbx) (% rax) *)
  0x48; 0x0f; 0x44; 0xcb;  (* CMOVE (% rcx) (% rbx) *)
  0x49; 0x31; 0xc8;        (* XOR (% r8) (% rcx) *)
  0x49; 0x31; 0xc9;        (* XOR (% r9) (% rcx) *)
  0x49; 0x31; 0xca;        (* XOR (% r10) (% rcx) *)
  0x49; 0x31; 0xcb;        (* XOR (% r11) (% rcx) *)
  0x49; 0x31; 0xcc;        (* XOR (% r12) (% rcx) *)
  0x49; 0x31; 0xcd;        (* XOR (% r13) (% rcx) *)
  0x49; 0x31; 0xce;        (* XOR (% r14) (% rcx) *)
  0x49; 0x31; 0xcf;        (* XOR (% r15) (% rcx) *)
  0x48; 0x81; 0xe1; 0xff; 0x01; 0x00; 0x00;
                           (* AND (% rcx) (Imm32 (word 511)) *)
  0x48; 0x31; 0xc8;        (* XOR (% rax) (% rcx) *)
  0x4c; 0x89; 0x84; 0x24; 0x40; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,576))) (% r8) *)
  0x4c; 0x89; 0x8c; 0x24; 0x48; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,584))) (% r9) *)
  0x4c; 0x89; 0x94; 0x24; 0x50; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,592))) (% r10) *)
  0x4c; 0x89; 0x9c; 0x24; 0x58; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,600))) (% r11) *)
  0x4c; 0x89; 0xa4; 0x24; 0x60; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,608))) (% r12) *)
  0x4c; 0x89; 0xac; 0x24; 0x68; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,616))) (% r13) *)
  0x4c; 0x89; 0xb4; 0x24; 0x70; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,624))) (% r14) *)
  0x4c; 0x89; 0xbc; 0x24; 0x78; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,632))) (% r15) *)
  0x48; 0x89; 0x84; 0x24; 0x80; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,640))) (% rax) *)
  0x48; 0x8d; 0xbc; 0x24; 0xd0; 0x02; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rsp,720)) *)
  0x48; 0x8d; 0xb4; 0x24; 0xf8; 0x01; 0x00; 0x00;
                           (* LEA (% rsi) (%% (rsp,504)) *)
  0xe8; 0xc0; 0x26; 0x00; 0x00;
                           (* CALL (Imm32 (word 9920)) *)
  0x48; 0x8d; 0xbc; 0x24; 0xa8; 0x03; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rsp,936)) *)
  0x48; 0x8d; 0xb4; 0x24; 0xd0; 0x02; 0x00; 0x00;
                           (* LEA (% rsi) (%% (rsp,720)) *)
  0x48; 0x8d; 0x94; 0x24; 0xf8; 0x01; 0x00; 0x00;
                           (* LEA (% rdx) (%% (rsp,504)) *)
  0xe8; 0xb5; 0x19; 0x00; 0x00;
                           (* CALL (Imm32 (word 6581)) *)
  0x48; 0x8d; 0xbc; 0x24; 0x80; 0x04; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rsp,1152)) *)
  0x48; 0x8d; 0xb4; 0x24; 0xd0; 0x02; 0x00; 0x00;
                           (* LEA (% rsi) (%% (rsp,720)) *)
  0xe8; 0x8e; 0x26; 0x00; 0x00;
                           (* CALL (Imm32 (word 9870)) *)
  0x48; 0x8d; 0xbc; 0x24; 0x58; 0x05; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rsp,1368)) *)
  0x48; 0x8d; 0xb4; 0x24; 0x80; 0x04; 0x00; 0x00;
                           (* LEA (% rsi) (%% (rsp,1152)) *)
  0x48; 0x8d; 0x94; 0x24; 0xf8; 0x01; 0x00; 0x00;
                           (* LEA (% rdx) (%% (rsp,504)) *)
  0xe8; 0x83; 0x19; 0x00; 0x00;
                           (* CALL (Imm32 (word 6531)) *)
  0x48; 0x8d; 0xbc; 0x24; 0x30; 0x06; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rsp,1584)) *)
  0x48; 0x8d; 0xb4; 0x24; 0xa8; 0x03; 0x00; 0x00;
                           (* LEA (% rsi) (%% (rsp,936)) *)
  0xe8; 0x5c; 0x26; 0x00; 0x00;
                           (* CALL (Imm32 (word 9820)) *)
  0x48; 0x8d; 0xbc; 0x24; 0x08; 0x07; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rsp,1800)) *)
  0x48; 0x8d; 0xb4; 0x24; 0x30; 0x06; 0x00; 0x00;
                           (* LEA (% rsi) (%% (rsp,1584)) *)
  0x48; 0x8d; 0x94; 0x24; 0xf8; 0x01; 0x00; 0x00;
                           (* LEA (% rdx) (%% (rsp,504)) *)
  0xe8; 0x51; 0x19; 0x00; 0x00;
                           (* CALL (Imm32 (word 6481)) *)
  0x48; 0x8d; 0xbc; 0x24; 0xe0; 0x07; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rsp,2016)) *)
  0x48; 0x8d; 0xb4; 0x24; 0x80; 0x04; 0x00; 0x00;
                           (* LEA (% rsi) (%% (rsp,1152)) *)
  0xe8; 0x2a; 0x26; 0x00; 0x00;
                           (* CALL (Imm32 (word 9770)) *)
  0x48; 0x8d; 0xbc; 0x24; 0xb8; 0x08; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rsp,2232)) *)
  0x48; 0x8d; 0xb4; 0x24; 0xe0; 0x07; 0x00; 0x00;
                           (* LEA (% rsi) (%% (rsp,2016)) *)
  0x48; 0x8d; 0x94; 0x24; 0xf8; 0x01; 0x00; 0x00;
                           (* LEA (% rdx) (%% (rsp,504)) *)
  0xe8; 0x1f; 0x19; 0x00; 0x00;
                           (* CALL (Imm32 (word 6431)) *)
  0x48; 0x8d; 0xbc; 0x24; 0x90; 0x09; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rsp,2448)) *)
  0x48; 0x8d; 0xb4; 0x24; 0x58; 0x05; 0x00; 0x00;
                           (* LEA (% rsi) (%% (rsp,1368)) *)
  0xe8; 0xf8; 0x25; 0x00; 0x00;
                           (* CALL (Imm32 (word 9720)) *)
  0x48; 0x8d; 0xbc; 0x24; 0x68; 0x0a; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rsp,2664)) *)
  0x48; 0x8d; 0xb4; 0x24; 0x90; 0x09; 0x00; 0x00;
                           (* LEA (% rsi) (%% (rsp,2448)) *)
  0x48; 0x8d; 0x94; 0x24; 0xf8; 0x01; 0x00; 0x00;
                           (* LEA (% rdx) (%% (rsp,504)) *)
  0xe8; 0xed; 0x18; 0x00; 0x00;
                           (* CALL (Imm32 (word 6381)) *)
  0x48; 0x8d; 0xbc; 0x24; 0x40; 0x0b; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rsp,2880)) *)
  0x48; 0x8d; 0xb4; 0x24; 0x30; 0x06; 0x00; 0x00;
                           (* LEA (% rsi) (%% (rsp,1584)) *)
  0xe8; 0xc6; 0x25; 0x00; 0x00;
                           (* CALL (Imm32 (word 9670)) *)
  0x48; 0x8d; 0xbc; 0x24; 0x18; 0x0c; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rsp,3096)) *)
  0x48; 0x8d; 0xb4; 0x24; 0x40; 0x0b; 0x00; 0x00;
                           (* LEA (% rsi) (%% (rsp,2880)) *)
  0x48; 0x8d; 0x94; 0x24; 0xf8; 0x01; 0x00; 0x00;
                           (* LEA (% rdx) (%% (rsp,504)) *)
  0xe8; 0xbb; 0x18; 0x00; 0x00;
                           (* CALL (Imm32 (word 6331)) *)
  0x48; 0x8d; 0xbc; 0x24; 0xf0; 0x0c; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rsp,3312)) *)
  0x48; 0x8d; 0xb4; 0x24; 0x08; 0x07; 0x00; 0x00;
                           (* LEA (% rsi) (%% (rsp,1800)) *)
  0xe8; 0x94; 0x25; 0x00; 0x00;
                           (* CALL (Imm32 (word 9620)) *)
  0x48; 0x8d; 0xbc; 0x24; 0xc8; 0x0d; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rsp,3528)) *)
  0x48; 0x8d; 0xb4; 0x24; 0xf0; 0x0c; 0x00; 0x00;
                           (* LEA (% rsi) (%% (rsp,3312)) *)
  0x48; 0x8d; 0x94; 0x24; 0xf8; 0x01; 0x00; 0x00;
                           (* LEA (% rdx) (%% (rsp,504)) *)
  0xe8; 0x89; 0x18; 0x00; 0x00;
                           (* CALL (Imm32 (word 6281)) *)
  0x48; 0x8d; 0xbc; 0x24; 0xa0; 0x0e; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rsp,3744)) *)
  0x48; 0x8d; 0xb4; 0x24; 0xe0; 0x07; 0x00; 0x00;
                           (* LEA (% rsi) (%% (rsp,2016)) *)
  0xe8; 0x62; 0x25; 0x00; 0x00;
                           (* CALL (Imm32 (word 9570)) *)
  0x48; 0xb8; 0x21; 0x84; 0x10; 0x42; 0x08; 0x21; 0x84; 0x10;
                           (* MOV (% rax) (Imm64 (word 1190112520884487201)) *)
  0x48; 0x89; 0xc3;        (* MOV (% rbx) (% rax) *)
  0x48; 0xd1; 0xe8;        (* SHR (% rax) (Imm8 (word 1)) *)
  0x4c; 0x8b; 0x04; 0x24;  (* MOV (% r8) (Memop Quadword (%% (rsp,0))) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x4c; 0x8b; 0x4c; 0x24; 0x08;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,8))) *)
  0x49; 0x11; 0xd9;        (* ADC (% r9) (% rbx) *)
  0x48; 0x8d; 0x0c; 0x1b;  (* LEA (% rcx) (%%% (rbx,0,rbx)) *)
  0x4c; 0x8b; 0x54; 0x24; 0x10;
                           (* MOV (% r10) (Memop Quadword (%% (rsp,16))) *)
  0x49; 0x11; 0xca;        (* ADC (% r10) (% rcx) *)
  0x48; 0x8d; 0x0c; 0x09;  (* LEA (% rcx) (%%% (rcx,0,rcx)) *)
  0x4c; 0x8b; 0x5c; 0x24; 0x18;
                           (* MOV (% r11) (Memop Quadword (%% (rsp,24))) *)
  0x49; 0x11; 0xcb;        (* ADC (% r11) (% rcx) *)
  0x48; 0x8d; 0x0c; 0x09;  (* LEA (% rcx) (%%% (rcx,0,rcx)) *)
  0x4c; 0x8b; 0x64; 0x24; 0x20;
                           (* MOV (% r12) (Memop Quadword (%% (rsp,32))) *)
  0x49; 0x11; 0xcc;        (* ADC (% r12) (% rcx) *)
  0x4c; 0x8b; 0x6c; 0x24; 0x28;
                           (* MOV (% r13) (Memop Quadword (%% (rsp,40))) *)
  0x49; 0x11; 0xc5;        (* ADC (% r13) (% rax) *)
  0x4c; 0x8b; 0x74; 0x24; 0x30;
                           (* MOV (% r14) (Memop Quadword (%% (rsp,48))) *)
  0x49; 0x11; 0xde;        (* ADC (% r14) (% rbx) *)
  0x4c; 0x8b; 0x7c; 0x24; 0x38;
                           (* MOV (% r15) (Memop Quadword (%% (rsp,56))) *)
  0x48; 0x8d; 0x0c; 0x1b;  (* LEA (% rcx) (%%% (rbx,0,rbx)) *)
  0x49; 0x11; 0xcf;        (* ADC (% r15) (% rcx) *)
  0x48; 0x8b; 0x44; 0x24; 0x40;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,64))) *)
  0x48; 0x15; 0x84; 0x00; 0x00; 0x00;
                           (* ADC (% rax) (Imm32 (word 132)) *)
  0x48; 0x89; 0xc7;        (* MOV (% rdi) (% rax) *)
  0x48; 0xc1; 0xef; 0x08;  (* SHR (% rdi) (Imm8 (word 8)) *)
  0x4c; 0x0f; 0xa4; 0xf8; 0x38;
                           (* SHLD (% rax) (% r15) (Imm8 (word 56)) *)
  0x4d; 0x0f; 0xa4; 0xf7; 0x38;
                           (* SHLD (% r15) (% r14) (Imm8 (word 56)) *)
  0x4d; 0x0f; 0xa4; 0xee; 0x38;
                           (* SHLD (% r14) (% r13) (Imm8 (word 56)) *)
  0x4d; 0x0f; 0xa4; 0xe5; 0x38;
                           (* SHLD (% r13) (% r12) (Imm8 (word 56)) *)
  0x4d; 0x0f; 0xa4; 0xdc; 0x38;
                           (* SHLD (% r12) (% r11) (Imm8 (word 56)) *)
  0x4d; 0x0f; 0xa4; 0xd3; 0x38;
                           (* SHLD (% r11) (% r10) (Imm8 (word 56)) *)
  0x4d; 0x0f; 0xa4; 0xca; 0x38;
                           (* SHLD (% r10) (% r9) (Imm8 (word 56)) *)
  0x4d; 0x0f; 0xa4; 0xc1; 0x38;
                           (* SHLD (% r9) (% r8) (Imm8 (word 56)) *)
  0x49; 0xc1; 0xe0; 0x38;  (* SHL (% r8) (Imm8 (word 56)) *)
  0x4c; 0x89; 0x04; 0x24;  (* MOV (Memop Quadword (%% (rsp,0))) (% r8) *)
  0x4c; 0x89; 0x4c; 0x24; 0x08;
                           (* MOV (Memop Quadword (%% (rsp,8))) (% r9) *)
  0x4c; 0x89; 0x54; 0x24; 0x10;
                           (* MOV (Memop Quadword (%% (rsp,16))) (% r10) *)
  0x4c; 0x89; 0x5c; 0x24; 0x18;
                           (* MOV (Memop Quadword (%% (rsp,24))) (% r11) *)
  0x4c; 0x89; 0x64; 0x24; 0x20;
                           (* MOV (Memop Quadword (%% (rsp,32))) (% r12) *)
  0x4c; 0x89; 0x6c; 0x24; 0x28;
                           (* MOV (Memop Quadword (%% (rsp,40))) (% r13) *)
  0x4c; 0x89; 0x74; 0x24; 0x30;
                           (* MOV (Memop Quadword (%% (rsp,48))) (% r14) *)
  0x4c; 0x89; 0x7c; 0x24; 0x38;
                           (* MOV (Memop Quadword (%% (rsp,56))) (% r15) *)
  0x48; 0x89; 0x44; 0x24; 0x40;
                           (* MOV (Memop Quadword (%% (rsp,64))) (% rax) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x85; 0xff;        (* TEST (% rdi) (% rdi) *)
  0x48; 0x8b; 0x84; 0x24; 0xf8; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,504))) *)
  0x48; 0x0f; 0x44; 0xc1;  (* CMOVE (% rax) (% rcx) *)
  0x48; 0x89; 0x44; 0x24; 0x48;
                           (* MOV (Memop Quadword (%% (rsp,72))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x00; 0x02; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,512))) *)
  0x48; 0x0f; 0x44; 0xc1;  (* CMOVE (% rax) (% rcx) *)
  0x48; 0x89; 0x44; 0x24; 0x50;
                           (* MOV (Memop Quadword (%% (rsp,80))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x08; 0x02; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,520))) *)
  0x48; 0x0f; 0x44; 0xc1;  (* CMOVE (% rax) (% rcx) *)
  0x48; 0x89; 0x44; 0x24; 0x58;
                           (* MOV (Memop Quadword (%% (rsp,88))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x10; 0x02; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,528))) *)
  0x48; 0x0f; 0x44; 0xc1;  (* CMOVE (% rax) (% rcx) *)
  0x48; 0x89; 0x44; 0x24; 0x60;
                           (* MOV (Memop Quadword (%% (rsp,96))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x18; 0x02; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,536))) *)
  0x48; 0x0f; 0x44; 0xc1;  (* CMOVE (% rax) (% rcx) *)
  0x48; 0x89; 0x44; 0x24; 0x68;
                           (* MOV (Memop Quadword (%% (rsp,104))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x20; 0x02; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,544))) *)
  0x48; 0x0f; 0x44; 0xc1;  (* CMOVE (% rax) (% rcx) *)
  0x48; 0x89; 0x44; 0x24; 0x70;
                           (* MOV (Memop Quadword (%% (rsp,112))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x28; 0x02; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,552))) *)
  0x48; 0x0f; 0x44; 0xc1;  (* CMOVE (% rax) (% rcx) *)
  0x48; 0x89; 0x44; 0x24; 0x78;
                           (* MOV (Memop Quadword (%% (rsp,120))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x30; 0x02; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,560))) *)
  0x48; 0x0f; 0x44; 0xc1;  (* CMOVE (% rax) (% rcx) *)
  0x48; 0x89; 0x84; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,128))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x38; 0x02; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,568))) *)
  0x48; 0x0f; 0x44; 0xc1;  (* CMOVE (% rax) (% rcx) *)
  0x48; 0x89; 0x84; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,136))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x40; 0x02; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,576))) *)
  0x48; 0x0f; 0x44; 0xc1;  (* CMOVE (% rax) (% rcx) *)
  0x48; 0x89; 0x84; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,144))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x48; 0x02; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,584))) *)
  0x48; 0x0f; 0x44; 0xc1;  (* CMOVE (% rax) (% rcx) *)
  0x48; 0x89; 0x84; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,152))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x50; 0x02; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,592))) *)
  0x48; 0x0f; 0x44; 0xc1;  (* CMOVE (% rax) (% rcx) *)
  0x48; 0x89; 0x84; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,160))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x58; 0x02; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,600))) *)
  0x48; 0x0f; 0x44; 0xc1;  (* CMOVE (% rax) (% rcx) *)
  0x48; 0x89; 0x84; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,168))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x60; 0x02; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,608))) *)
  0x48; 0x0f; 0x44; 0xc1;  (* CMOVE (% rax) (% rcx) *)
  0x48; 0x89; 0x84; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,176))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x68; 0x02; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,616))) *)
  0x48; 0x0f; 0x44; 0xc1;  (* CMOVE (% rax) (% rcx) *)
  0x48; 0x89; 0x84; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,184))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x70; 0x02; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,624))) *)
  0x48; 0x0f; 0x44; 0xc1;  (* CMOVE (% rax) (% rcx) *)
  0x48; 0x89; 0x84; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,192))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x78; 0x02; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,632))) *)
  0x48; 0x0f; 0x44; 0xc1;  (* CMOVE (% rax) (% rcx) *)
  0x48; 0x89; 0x84; 0x24; 0xc8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,200))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x80; 0x02; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,640))) *)
  0x48; 0x0f; 0x44; 0xc1;  (* CMOVE (% rax) (% rcx) *)
  0x48; 0x89; 0x84; 0x24; 0xd0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,208))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x88; 0x02; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,648))) *)
  0x48; 0x0f; 0x44; 0xc1;  (* CMOVE (% rax) (% rcx) *)
  0x48; 0x89; 0x84; 0x24; 0xd8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,216))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x90; 0x02; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,656))) *)
  0x48; 0x0f; 0x44; 0xc1;  (* CMOVE (% rax) (% rcx) *)
  0x48; 0x89; 0x84; 0x24; 0xe0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,224))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x98; 0x02; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,664))) *)
  0x48; 0x0f; 0x44; 0xc1;  (* CMOVE (% rax) (% rcx) *)
  0x48; 0x89; 0x84; 0x24; 0xe8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,232))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0xa0; 0x02; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,672))) *)
  0x48; 0x0f; 0x44; 0xc1;  (* CMOVE (% rax) (% rcx) *)
  0x48; 0x89; 0x84; 0x24; 0xf0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,240))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0xa8; 0x02; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,680))) *)
  0x48; 0x0f; 0x44; 0xc1;  (* CMOVE (% rax) (% rcx) *)
  0x48; 0x89; 0x84; 0x24; 0xf8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,248))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0xb0; 0x02; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,688))) *)
  0x48; 0x0f; 0x44; 0xc1;  (* CMOVE (% rax) (% rcx) *)
  0x48; 0x89; 0x84; 0x24; 0x00; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,256))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0xb8; 0x02; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,696))) *)
  0x48; 0x0f; 0x44; 0xc1;  (* CMOVE (% rax) (% rcx) *)
  0x48; 0x89; 0x84; 0x24; 0x08; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,264))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0xc0; 0x02; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,704))) *)
  0x48; 0x0f; 0x44; 0xc1;  (* CMOVE (% rax) (% rcx) *)
  0x48; 0x89; 0x84; 0x24; 0x10; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,272))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0xc8; 0x02; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,712))) *)
  0x48; 0x0f; 0x44; 0xc1;  (* CMOVE (% rax) (% rcx) *)
  0x48; 0x89; 0x84; 0x24; 0x18; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,280))) (% rax) *)
  0xbd; 0x08; 0x02; 0x00; 0x00;
                           (* MOV (% ebp) (Imm32 (word 520)) *)
  0x48; 0x83; 0xed; 0x05;  (* SUB (% rbp) (Imm8 (word 5)) *)
  0x48; 0x8d; 0x74; 0x24; 0x48;
                           (* LEA (% rsi) (%% (rsp,72)) *)
  0x48; 0x8d; 0x7c; 0x24; 0x48;
                           (* LEA (% rdi) (%% (rsp,72)) *)
  0xe8; 0x75; 0x22; 0x00; 0x00;
                           (* CALL (Imm32 (word 8821)) *)
  0x48; 0x8d; 0x74; 0x24; 0x48;
                           (* LEA (% rsi) (%% (rsp,72)) *)
  0x48; 0x8d; 0x7c; 0x24; 0x48;
                           (* LEA (% rdi) (%% (rsp,72)) *)
  0xe8; 0x66; 0x22; 0x00; 0x00;
                           (* CALL (Imm32 (word 8806)) *)
  0x48; 0x8d; 0x74; 0x24; 0x48;
                           (* LEA (% rsi) (%% (rsp,72)) *)
  0x48; 0x8d; 0x7c; 0x24; 0x48;
                           (* LEA (% rdi) (%% (rsp,72)) *)
  0xe8; 0x57; 0x22; 0x00; 0x00;
                           (* CALL (Imm32 (word 8791)) *)
  0x48; 0x8d; 0x74; 0x24; 0x48;
                           (* LEA (% rsi) (%% (rsp,72)) *)
  0x48; 0x8d; 0x7c; 0x24; 0x48;
                           (* LEA (% rdi) (%% (rsp,72)) *)
  0xe8; 0x48; 0x22; 0x00; 0x00;
                           (* CALL (Imm32 (word 8776)) *)
  0x48; 0x8d; 0x74; 0x24; 0x48;
                           (* LEA (% rsi) (%% (rsp,72)) *)
  0x48; 0x8d; 0x7c; 0x24; 0x48;
                           (* LEA (% rdi) (%% (rsp,72)) *)
  0xe8; 0x39; 0x22; 0x00; 0x00;
                           (* CALL (Imm32 (word 8761)) *)
  0x4c; 0x8b; 0x04; 0x24;  (* MOV (% r8) (Memop Quadword (%% (rsp,0))) *)
  0x4c; 0x8b; 0x4c; 0x24; 0x08;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,8))) *)
  0x4c; 0x8b; 0x54; 0x24; 0x10;
                           (* MOV (% r10) (Memop Quadword (%% (rsp,16))) *)
  0x4c; 0x8b; 0x5c; 0x24; 0x18;
                           (* MOV (% r11) (Memop Quadword (%% (rsp,24))) *)
  0x4c; 0x8b; 0x64; 0x24; 0x20;
                           (* MOV (% r12) (Memop Quadword (%% (rsp,32))) *)
  0x4c; 0x8b; 0x6c; 0x24; 0x28;
                           (* MOV (% r13) (Memop Quadword (%% (rsp,40))) *)
  0x4c; 0x8b; 0x74; 0x24; 0x30;
                           (* MOV (% r14) (Memop Quadword (%% (rsp,48))) *)
  0x4c; 0x8b; 0x7c; 0x24; 0x38;
                           (* MOV (% r15) (Memop Quadword (%% (rsp,56))) *)
  0x48; 0x8b; 0x44; 0x24; 0x40;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,64))) *)
  0x48; 0x89; 0xc7;        (* MOV (% rdi) (% rax) *)
  0x48; 0xc1; 0xef; 0x3b;  (* SHR (% rdi) (Imm8 (word 59)) *)
  0x4c; 0x0f; 0xa4; 0xf8; 0x05;
                           (* SHLD (% rax) (% r15) (Imm8 (word 5)) *)
  0x4d; 0x0f; 0xa4; 0xf7; 0x05;
                           (* SHLD (% r15) (% r14) (Imm8 (word 5)) *)
  0x4d; 0x0f; 0xa4; 0xee; 0x05;
                           (* SHLD (% r14) (% r13) (Imm8 (word 5)) *)
  0x4d; 0x0f; 0xa4; 0xe5; 0x05;
                           (* SHLD (% r13) (% r12) (Imm8 (word 5)) *)
  0x4d; 0x0f; 0xa4; 0xdc; 0x05;
                           (* SHLD (% r12) (% r11) (Imm8 (word 5)) *)
  0x4d; 0x0f; 0xa4; 0xd3; 0x05;
                           (* SHLD (% r11) (% r10) (Imm8 (word 5)) *)
  0x4d; 0x0f; 0xa4; 0xca; 0x05;
                           (* SHLD (% r10) (% r9) (Imm8 (word 5)) *)
  0x4d; 0x0f; 0xa4; 0xc1; 0x05;
                           (* SHLD (% r9) (% r8) (Imm8 (word 5)) *)
  0x49; 0xc1; 0xe0; 0x05;  (* SHL (% r8) (Imm8 (word 5)) *)
  0x4c; 0x89; 0x04; 0x24;  (* MOV (Memop Quadword (%% (rsp,0))) (% r8) *)
  0x4c; 0x89; 0x4c; 0x24; 0x08;
                           (* MOV (Memop Quadword (%% (rsp,8))) (% r9) *)
  0x4c; 0x89; 0x54; 0x24; 0x10;
                           (* MOV (Memop Quadword (%% (rsp,16))) (% r10) *)
  0x4c; 0x89; 0x5c; 0x24; 0x18;
                           (* MOV (Memop Quadword (%% (rsp,24))) (% r11) *)
  0x4c; 0x89; 0x64; 0x24; 0x20;
                           (* MOV (Memop Quadword (%% (rsp,32))) (% r12) *)
  0x4c; 0x89; 0x6c; 0x24; 0x28;
                           (* MOV (Memop Quadword (%% (rsp,40))) (% r13) *)
  0x4c; 0x89; 0x74; 0x24; 0x30;
                           (* MOV (Memop Quadword (%% (rsp,48))) (% r14) *)
  0x4c; 0x89; 0x7c; 0x24; 0x38;
                           (* MOV (Memop Quadword (%% (rsp,56))) (% r15) *)
  0x48; 0x89; 0x44; 0x24; 0x40;
                           (* MOV (Memop Quadword (%% (rsp,64))) (% rax) *)
  0x48; 0x83; 0xef; 0x10;  (* SUB (% rdi) (Imm8 (word 16)) *)
  0x48; 0x19; 0xf6;        (* SBB (% rsi) (% rsi) *)
  0x48; 0x31; 0xf7;        (* XOR (% rdi) (% rsi) *)
  0x48; 0x29; 0xf7;        (* SUB (% rdi) (% rsi) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0x31; 0xdb;              (* XOR (% ebx) (% ebx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x31; 0xd2;              (* XOR (% edx) (% edx) *)
  0x45; 0x31; 0xc0;        (* XOR (% r8d) (% r8d) *)
  0x45; 0x31; 0xc9;        (* XOR (% r9d) (% r9d) *)
  0x45; 0x31; 0xd2;        (* XOR (% r10d) (% r10d) *)
  0x45; 0x31; 0xdb;        (* XOR (% r11d) (% r11d) *)
  0x45; 0x31; 0xe4;        (* XOR (% r12d) (% r12d) *)
  0x48; 0x83; 0xff; 0x01;  (* CMP (% rdi) (Imm8 (word 1)) *)
  0x48; 0x0f; 0x44; 0x84; 0x24; 0xf8; 0x01; 0x00; 0x00;
                           (* CMOVE (% rax) (Memop Quadword (%% (rsp,504))) *)
  0x48; 0x0f; 0x44; 0x9c; 0x24; 0x00; 0x02; 0x00; 0x00;
                           (* CMOVE (% rbx) (Memop Quadword (%% (rsp,512))) *)
  0x48; 0x0f; 0x44; 0x8c; 0x24; 0x08; 0x02; 0x00; 0x00;
                           (* CMOVE (% rcx) (Memop Quadword (%% (rsp,520))) *)
  0x48; 0x0f; 0x44; 0x94; 0x24; 0x10; 0x02; 0x00; 0x00;
                           (* CMOVE (% rdx) (Memop Quadword (%% (rsp,528))) *)
  0x4c; 0x0f; 0x44; 0x84; 0x24; 0x18; 0x02; 0x00; 0x00;
                           (* CMOVE (% r8) (Memop Quadword (%% (rsp,536))) *)
  0x4c; 0x0f; 0x44; 0x8c; 0x24; 0x20; 0x02; 0x00; 0x00;
                           (* CMOVE (% r9) (Memop Quadword (%% (rsp,544))) *)
  0x4c; 0x0f; 0x44; 0x94; 0x24; 0x28; 0x02; 0x00; 0x00;
                           (* CMOVE (% r10) (Memop Quadword (%% (rsp,552))) *)
  0x4c; 0x0f; 0x44; 0x9c; 0x24; 0x30; 0x02; 0x00; 0x00;
                           (* CMOVE (% r11) (Memop Quadword (%% (rsp,560))) *)
  0x4c; 0x0f; 0x44; 0xa4; 0x24; 0x38; 0x02; 0x00; 0x00;
                           (* CMOVE (% r12) (Memop Quadword (%% (rsp,568))) *)
  0x48; 0x83; 0xff; 0x02;  (* CMP (% rdi) (Imm8 (word 2)) *)
  0x48; 0x0f; 0x44; 0x84; 0x24; 0xd0; 0x02; 0x00; 0x00;
                           (* CMOVE (% rax) (Memop Quadword (%% (rsp,720))) *)
  0x48; 0x0f; 0x44; 0x9c; 0x24; 0xd8; 0x02; 0x00; 0x00;
                           (* CMOVE (% rbx) (Memop Quadword (%% (rsp,728))) *)
  0x48; 0x0f; 0x44; 0x8c; 0x24; 0xe0; 0x02; 0x00; 0x00;
                           (* CMOVE (% rcx) (Memop Quadword (%% (rsp,736))) *)
  0x48; 0x0f; 0x44; 0x94; 0x24; 0xe8; 0x02; 0x00; 0x00;
                           (* CMOVE (% rdx) (Memop Quadword (%% (rsp,744))) *)
  0x4c; 0x0f; 0x44; 0x84; 0x24; 0xf0; 0x02; 0x00; 0x00;
                           (* CMOVE (% r8) (Memop Quadword (%% (rsp,752))) *)
  0x4c; 0x0f; 0x44; 0x8c; 0x24; 0xf8; 0x02; 0x00; 0x00;
                           (* CMOVE (% r9) (Memop Quadword (%% (rsp,760))) *)
  0x4c; 0x0f; 0x44; 0x94; 0x24; 0x00; 0x03; 0x00; 0x00;
                           (* CMOVE (% r10) (Memop Quadword (%% (rsp,768))) *)
  0x4c; 0x0f; 0x44; 0x9c; 0x24; 0x08; 0x03; 0x00; 0x00;
                           (* CMOVE (% r11) (Memop Quadword (%% (rsp,776))) *)
  0x4c; 0x0f; 0x44; 0xa4; 0x24; 0x10; 0x03; 0x00; 0x00;
                           (* CMOVE (% r12) (Memop Quadword (%% (rsp,784))) *)
  0x48; 0x83; 0xff; 0x03;  (* CMP (% rdi) (Imm8 (word 3)) *)
  0x48; 0x0f; 0x44; 0x84; 0x24; 0xa8; 0x03; 0x00; 0x00;
                           (* CMOVE (% rax) (Memop Quadword (%% (rsp,936))) *)
  0x48; 0x0f; 0x44; 0x9c; 0x24; 0xb0; 0x03; 0x00; 0x00;
                           (* CMOVE (% rbx) (Memop Quadword (%% (rsp,944))) *)
  0x48; 0x0f; 0x44; 0x8c; 0x24; 0xb8; 0x03; 0x00; 0x00;
                           (* CMOVE (% rcx) (Memop Quadword (%% (rsp,952))) *)
  0x48; 0x0f; 0x44; 0x94; 0x24; 0xc0; 0x03; 0x00; 0x00;
                           (* CMOVE (% rdx) (Memop Quadword (%% (rsp,960))) *)
  0x4c; 0x0f; 0x44; 0x84; 0x24; 0xc8; 0x03; 0x00; 0x00;
                           (* CMOVE (% r8) (Memop Quadword (%% (rsp,968))) *)
  0x4c; 0x0f; 0x44; 0x8c; 0x24; 0xd0; 0x03; 0x00; 0x00;
                           (* CMOVE (% r9) (Memop Quadword (%% (rsp,976))) *)
  0x4c; 0x0f; 0x44; 0x94; 0x24; 0xd8; 0x03; 0x00; 0x00;
                           (* CMOVE (% r10) (Memop Quadword (%% (rsp,984))) *)
  0x4c; 0x0f; 0x44; 0x9c; 0x24; 0xe0; 0x03; 0x00; 0x00;
                           (* CMOVE (% r11) (Memop Quadword (%% (rsp,992))) *)
  0x4c; 0x0f; 0x44; 0xa4; 0x24; 0xe8; 0x03; 0x00; 0x00;
                           (* CMOVE (% r12) (Memop Quadword (%% (rsp,1000))) *)
  0x48; 0x83; 0xff; 0x04;  (* CMP (% rdi) (Imm8 (word 4)) *)
  0x48; 0x0f; 0x44; 0x84; 0x24; 0x80; 0x04; 0x00; 0x00;
                           (* CMOVE (% rax) (Memop Quadword (%% (rsp,1152))) *)
  0x48; 0x0f; 0x44; 0x9c; 0x24; 0x88; 0x04; 0x00; 0x00;
                           (* CMOVE (% rbx) (Memop Quadword (%% (rsp,1160))) *)
  0x48; 0x0f; 0x44; 0x8c; 0x24; 0x90; 0x04; 0x00; 0x00;
                           (* CMOVE (% rcx) (Memop Quadword (%% (rsp,1168))) *)
  0x48; 0x0f; 0x44; 0x94; 0x24; 0x98; 0x04; 0x00; 0x00;
                           (* CMOVE (% rdx) (Memop Quadword (%% (rsp,1176))) *)
  0x4c; 0x0f; 0x44; 0x84; 0x24; 0xa0; 0x04; 0x00; 0x00;
                           (* CMOVE (% r8) (Memop Quadword (%% (rsp,1184))) *)
  0x4c; 0x0f; 0x44; 0x8c; 0x24; 0xa8; 0x04; 0x00; 0x00;
                           (* CMOVE (% r9) (Memop Quadword (%% (rsp,1192))) *)
  0x4c; 0x0f; 0x44; 0x94; 0x24; 0xb0; 0x04; 0x00; 0x00;
                           (* CMOVE (% r10) (Memop Quadword (%% (rsp,1200))) *)
  0x4c; 0x0f; 0x44; 0x9c; 0x24; 0xb8; 0x04; 0x00; 0x00;
                           (* CMOVE (% r11) (Memop Quadword (%% (rsp,1208))) *)
  0x4c; 0x0f; 0x44; 0xa4; 0x24; 0xc0; 0x04; 0x00; 0x00;
                           (* CMOVE (% r12) (Memop Quadword (%% (rsp,1216))) *)
  0x48; 0x83; 0xff; 0x05;  (* CMP (% rdi) (Imm8 (word 5)) *)
  0x48; 0x0f; 0x44; 0x84; 0x24; 0x58; 0x05; 0x00; 0x00;
                           (* CMOVE (% rax) (Memop Quadword (%% (rsp,1368))) *)
  0x48; 0x0f; 0x44; 0x9c; 0x24; 0x60; 0x05; 0x00; 0x00;
                           (* CMOVE (% rbx) (Memop Quadword (%% (rsp,1376))) *)
  0x48; 0x0f; 0x44; 0x8c; 0x24; 0x68; 0x05; 0x00; 0x00;
                           (* CMOVE (% rcx) (Memop Quadword (%% (rsp,1384))) *)
  0x48; 0x0f; 0x44; 0x94; 0x24; 0x70; 0x05; 0x00; 0x00;
                           (* CMOVE (% rdx) (Memop Quadword (%% (rsp,1392))) *)
  0x4c; 0x0f; 0x44; 0x84; 0x24; 0x78; 0x05; 0x00; 0x00;
                           (* CMOVE (% r8) (Memop Quadword (%% (rsp,1400))) *)
  0x4c; 0x0f; 0x44; 0x8c; 0x24; 0x80; 0x05; 0x00; 0x00;
                           (* CMOVE (% r9) (Memop Quadword (%% (rsp,1408))) *)
  0x4c; 0x0f; 0x44; 0x94; 0x24; 0x88; 0x05; 0x00; 0x00;
                           (* CMOVE (% r10) (Memop Quadword (%% (rsp,1416))) *)
  0x4c; 0x0f; 0x44; 0x9c; 0x24; 0x90; 0x05; 0x00; 0x00;
                           (* CMOVE (% r11) (Memop Quadword (%% (rsp,1424))) *)
  0x4c; 0x0f; 0x44; 0xa4; 0x24; 0x98; 0x05; 0x00; 0x00;
                           (* CMOVE (% r12) (Memop Quadword (%% (rsp,1432))) *)
  0x48; 0x83; 0xff; 0x06;  (* CMP (% rdi) (Imm8 (word 6)) *)
  0x48; 0x0f; 0x44; 0x84; 0x24; 0x30; 0x06; 0x00; 0x00;
                           (* CMOVE (% rax) (Memop Quadword (%% (rsp,1584))) *)
  0x48; 0x0f; 0x44; 0x9c; 0x24; 0x38; 0x06; 0x00; 0x00;
                           (* CMOVE (% rbx) (Memop Quadword (%% (rsp,1592))) *)
  0x48; 0x0f; 0x44; 0x8c; 0x24; 0x40; 0x06; 0x00; 0x00;
                           (* CMOVE (% rcx) (Memop Quadword (%% (rsp,1600))) *)
  0x48; 0x0f; 0x44; 0x94; 0x24; 0x48; 0x06; 0x00; 0x00;
                           (* CMOVE (% rdx) (Memop Quadword (%% (rsp,1608))) *)
  0x4c; 0x0f; 0x44; 0x84; 0x24; 0x50; 0x06; 0x00; 0x00;
                           (* CMOVE (% r8) (Memop Quadword (%% (rsp,1616))) *)
  0x4c; 0x0f; 0x44; 0x8c; 0x24; 0x58; 0x06; 0x00; 0x00;
                           (* CMOVE (% r9) (Memop Quadword (%% (rsp,1624))) *)
  0x4c; 0x0f; 0x44; 0x94; 0x24; 0x60; 0x06; 0x00; 0x00;
                           (* CMOVE (% r10) (Memop Quadword (%% (rsp,1632))) *)
  0x4c; 0x0f; 0x44; 0x9c; 0x24; 0x68; 0x06; 0x00; 0x00;
                           (* CMOVE (% r11) (Memop Quadword (%% (rsp,1640))) *)
  0x4c; 0x0f; 0x44; 0xa4; 0x24; 0x70; 0x06; 0x00; 0x00;
                           (* CMOVE (% r12) (Memop Quadword (%% (rsp,1648))) *)
  0x48; 0x83; 0xff; 0x07;  (* CMP (% rdi) (Imm8 (word 7)) *)
  0x48; 0x0f; 0x44; 0x84; 0x24; 0x08; 0x07; 0x00; 0x00;
                           (* CMOVE (% rax) (Memop Quadword (%% (rsp,1800))) *)
  0x48; 0x0f; 0x44; 0x9c; 0x24; 0x10; 0x07; 0x00; 0x00;
                           (* CMOVE (% rbx) (Memop Quadword (%% (rsp,1808))) *)
  0x48; 0x0f; 0x44; 0x8c; 0x24; 0x18; 0x07; 0x00; 0x00;
                           (* CMOVE (% rcx) (Memop Quadword (%% (rsp,1816))) *)
  0x48; 0x0f; 0x44; 0x94; 0x24; 0x20; 0x07; 0x00; 0x00;
                           (* CMOVE (% rdx) (Memop Quadword (%% (rsp,1824))) *)
  0x4c; 0x0f; 0x44; 0x84; 0x24; 0x28; 0x07; 0x00; 0x00;
                           (* CMOVE (% r8) (Memop Quadword (%% (rsp,1832))) *)
  0x4c; 0x0f; 0x44; 0x8c; 0x24; 0x30; 0x07; 0x00; 0x00;
                           (* CMOVE (% r9) (Memop Quadword (%% (rsp,1840))) *)
  0x4c; 0x0f; 0x44; 0x94; 0x24; 0x38; 0x07; 0x00; 0x00;
                           (* CMOVE (% r10) (Memop Quadword (%% (rsp,1848))) *)
  0x4c; 0x0f; 0x44; 0x9c; 0x24; 0x40; 0x07; 0x00; 0x00;
                           (* CMOVE (% r11) (Memop Quadword (%% (rsp,1856))) *)
  0x4c; 0x0f; 0x44; 0xa4; 0x24; 0x48; 0x07; 0x00; 0x00;
                           (* CMOVE (% r12) (Memop Quadword (%% (rsp,1864))) *)
  0x48; 0x83; 0xff; 0x08;  (* CMP (% rdi) (Imm8 (word 8)) *)
  0x48; 0x0f; 0x44; 0x84; 0x24; 0xe0; 0x07; 0x00; 0x00;
                           (* CMOVE (% rax) (Memop Quadword (%% (rsp,2016))) *)
  0x48; 0x0f; 0x44; 0x9c; 0x24; 0xe8; 0x07; 0x00; 0x00;
                           (* CMOVE (% rbx) (Memop Quadword (%% (rsp,2024))) *)
  0x48; 0x0f; 0x44; 0x8c; 0x24; 0xf0; 0x07; 0x00; 0x00;
                           (* CMOVE (% rcx) (Memop Quadword (%% (rsp,2032))) *)
  0x48; 0x0f; 0x44; 0x94; 0x24; 0xf8; 0x07; 0x00; 0x00;
                           (* CMOVE (% rdx) (Memop Quadword (%% (rsp,2040))) *)
  0x4c; 0x0f; 0x44; 0x84; 0x24; 0x00; 0x08; 0x00; 0x00;
                           (* CMOVE (% r8) (Memop Quadword (%% (rsp,2048))) *)
  0x4c; 0x0f; 0x44; 0x8c; 0x24; 0x08; 0x08; 0x00; 0x00;
                           (* CMOVE (% r9) (Memop Quadword (%% (rsp,2056))) *)
  0x4c; 0x0f; 0x44; 0x94; 0x24; 0x10; 0x08; 0x00; 0x00;
                           (* CMOVE (% r10) (Memop Quadword (%% (rsp,2064))) *)
  0x4c; 0x0f; 0x44; 0x9c; 0x24; 0x18; 0x08; 0x00; 0x00;
                           (* CMOVE (% r11) (Memop Quadword (%% (rsp,2072))) *)
  0x4c; 0x0f; 0x44; 0xa4; 0x24; 0x20; 0x08; 0x00; 0x00;
                           (* CMOVE (% r12) (Memop Quadword (%% (rsp,2080))) *)
  0x48; 0x83; 0xff; 0x09;  (* CMP (% rdi) (Imm8 (word 9)) *)
  0x48; 0x0f; 0x44; 0x84; 0x24; 0xb8; 0x08; 0x00; 0x00;
                           (* CMOVE (% rax) (Memop Quadword (%% (rsp,2232))) *)
  0x48; 0x0f; 0x44; 0x9c; 0x24; 0xc0; 0x08; 0x00; 0x00;
                           (* CMOVE (% rbx) (Memop Quadword (%% (rsp,2240))) *)
  0x48; 0x0f; 0x44; 0x8c; 0x24; 0xc8; 0x08; 0x00; 0x00;
                           (* CMOVE (% rcx) (Memop Quadword (%% (rsp,2248))) *)
  0x48; 0x0f; 0x44; 0x94; 0x24; 0xd0; 0x08; 0x00; 0x00;
                           (* CMOVE (% rdx) (Memop Quadword (%% (rsp,2256))) *)
  0x4c; 0x0f; 0x44; 0x84; 0x24; 0xd8; 0x08; 0x00; 0x00;
                           (* CMOVE (% r8) (Memop Quadword (%% (rsp,2264))) *)
  0x4c; 0x0f; 0x44; 0x8c; 0x24; 0xe0; 0x08; 0x00; 0x00;
                           (* CMOVE (% r9) (Memop Quadword (%% (rsp,2272))) *)
  0x4c; 0x0f; 0x44; 0x94; 0x24; 0xe8; 0x08; 0x00; 0x00;
                           (* CMOVE (% r10) (Memop Quadword (%% (rsp,2280))) *)
  0x4c; 0x0f; 0x44; 0x9c; 0x24; 0xf0; 0x08; 0x00; 0x00;
                           (* CMOVE (% r11) (Memop Quadword (%% (rsp,2288))) *)
  0x4c; 0x0f; 0x44; 0xa4; 0x24; 0xf8; 0x08; 0x00; 0x00;
                           (* CMOVE (% r12) (Memop Quadword (%% (rsp,2296))) *)
  0x48; 0x83; 0xff; 0x0a;  (* CMP (% rdi) (Imm8 (word 10)) *)
  0x48; 0x0f; 0x44; 0x84; 0x24; 0x90; 0x09; 0x00; 0x00;
                           (* CMOVE (% rax) (Memop Quadword (%% (rsp,2448))) *)
  0x48; 0x0f; 0x44; 0x9c; 0x24; 0x98; 0x09; 0x00; 0x00;
                           (* CMOVE (% rbx) (Memop Quadword (%% (rsp,2456))) *)
  0x48; 0x0f; 0x44; 0x8c; 0x24; 0xa0; 0x09; 0x00; 0x00;
                           (* CMOVE (% rcx) (Memop Quadword (%% (rsp,2464))) *)
  0x48; 0x0f; 0x44; 0x94; 0x24; 0xa8; 0x09; 0x00; 0x00;
                           (* CMOVE (% rdx) (Memop Quadword (%% (rsp,2472))) *)
  0x4c; 0x0f; 0x44; 0x84; 0x24; 0xb0; 0x09; 0x00; 0x00;
                           (* CMOVE (% r8) (Memop Quadword (%% (rsp,2480))) *)
  0x4c; 0x0f; 0x44; 0x8c; 0x24; 0xb8; 0x09; 0x00; 0x00;
                           (* CMOVE (% r9) (Memop Quadword (%% (rsp,2488))) *)
  0x4c; 0x0f; 0x44; 0x94; 0x24; 0xc0; 0x09; 0x00; 0x00;
                           (* CMOVE (% r10) (Memop Quadword (%% (rsp,2496))) *)
  0x4c; 0x0f; 0x44; 0x9c; 0x24; 0xc8; 0x09; 0x00; 0x00;
                           (* CMOVE (% r11) (Memop Quadword (%% (rsp,2504))) *)
  0x4c; 0x0f; 0x44; 0xa4; 0x24; 0xd0; 0x09; 0x00; 0x00;
                           (* CMOVE (% r12) (Memop Quadword (%% (rsp,2512))) *)
  0x48; 0x83; 0xff; 0x0b;  (* CMP (% rdi) (Imm8 (word 11)) *)
  0x48; 0x0f; 0x44; 0x84; 0x24; 0x68; 0x0a; 0x00; 0x00;
                           (* CMOVE (% rax) (Memop Quadword (%% (rsp,2664))) *)
  0x48; 0x0f; 0x44; 0x9c; 0x24; 0x70; 0x0a; 0x00; 0x00;
                           (* CMOVE (% rbx) (Memop Quadword (%% (rsp,2672))) *)
  0x48; 0x0f; 0x44; 0x8c; 0x24; 0x78; 0x0a; 0x00; 0x00;
                           (* CMOVE (% rcx) (Memop Quadword (%% (rsp,2680))) *)
  0x48; 0x0f; 0x44; 0x94; 0x24; 0x80; 0x0a; 0x00; 0x00;
                           (* CMOVE (% rdx) (Memop Quadword (%% (rsp,2688))) *)
  0x4c; 0x0f; 0x44; 0x84; 0x24; 0x88; 0x0a; 0x00; 0x00;
                           (* CMOVE (% r8) (Memop Quadword (%% (rsp,2696))) *)
  0x4c; 0x0f; 0x44; 0x8c; 0x24; 0x90; 0x0a; 0x00; 0x00;
                           (* CMOVE (% r9) (Memop Quadword (%% (rsp,2704))) *)
  0x4c; 0x0f; 0x44; 0x94; 0x24; 0x98; 0x0a; 0x00; 0x00;
                           (* CMOVE (% r10) (Memop Quadword (%% (rsp,2712))) *)
  0x4c; 0x0f; 0x44; 0x9c; 0x24; 0xa0; 0x0a; 0x00; 0x00;
                           (* CMOVE (% r11) (Memop Quadword (%% (rsp,2720))) *)
  0x4c; 0x0f; 0x44; 0xa4; 0x24; 0xa8; 0x0a; 0x00; 0x00;
                           (* CMOVE (% r12) (Memop Quadword (%% (rsp,2728))) *)
  0x48; 0x83; 0xff; 0x0c;  (* CMP (% rdi) (Imm8 (word 12)) *)
  0x48; 0x0f; 0x44; 0x84; 0x24; 0x40; 0x0b; 0x00; 0x00;
                           (* CMOVE (% rax) (Memop Quadword (%% (rsp,2880))) *)
  0x48; 0x0f; 0x44; 0x9c; 0x24; 0x48; 0x0b; 0x00; 0x00;
                           (* CMOVE (% rbx) (Memop Quadword (%% (rsp,2888))) *)
  0x48; 0x0f; 0x44; 0x8c; 0x24; 0x50; 0x0b; 0x00; 0x00;
                           (* CMOVE (% rcx) (Memop Quadword (%% (rsp,2896))) *)
  0x48; 0x0f; 0x44; 0x94; 0x24; 0x58; 0x0b; 0x00; 0x00;
                           (* CMOVE (% rdx) (Memop Quadword (%% (rsp,2904))) *)
  0x4c; 0x0f; 0x44; 0x84; 0x24; 0x60; 0x0b; 0x00; 0x00;
                           (* CMOVE (% r8) (Memop Quadword (%% (rsp,2912))) *)
  0x4c; 0x0f; 0x44; 0x8c; 0x24; 0x68; 0x0b; 0x00; 0x00;
                           (* CMOVE (% r9) (Memop Quadword (%% (rsp,2920))) *)
  0x4c; 0x0f; 0x44; 0x94; 0x24; 0x70; 0x0b; 0x00; 0x00;
                           (* CMOVE (% r10) (Memop Quadword (%% (rsp,2928))) *)
  0x4c; 0x0f; 0x44; 0x9c; 0x24; 0x78; 0x0b; 0x00; 0x00;
                           (* CMOVE (% r11) (Memop Quadword (%% (rsp,2936))) *)
  0x4c; 0x0f; 0x44; 0xa4; 0x24; 0x80; 0x0b; 0x00; 0x00;
                           (* CMOVE (% r12) (Memop Quadword (%% (rsp,2944))) *)
  0x48; 0x83; 0xff; 0x0d;  (* CMP (% rdi) (Imm8 (word 13)) *)
  0x48; 0x0f; 0x44; 0x84; 0x24; 0x18; 0x0c; 0x00; 0x00;
                           (* CMOVE (% rax) (Memop Quadword (%% (rsp,3096))) *)
  0x48; 0x0f; 0x44; 0x9c; 0x24; 0x20; 0x0c; 0x00; 0x00;
                           (* CMOVE (% rbx) (Memop Quadword (%% (rsp,3104))) *)
  0x48; 0x0f; 0x44; 0x8c; 0x24; 0x28; 0x0c; 0x00; 0x00;
                           (* CMOVE (% rcx) (Memop Quadword (%% (rsp,3112))) *)
  0x48; 0x0f; 0x44; 0x94; 0x24; 0x30; 0x0c; 0x00; 0x00;
                           (* CMOVE (% rdx) (Memop Quadword (%% (rsp,3120))) *)
  0x4c; 0x0f; 0x44; 0x84; 0x24; 0x38; 0x0c; 0x00; 0x00;
                           (* CMOVE (% r8) (Memop Quadword (%% (rsp,3128))) *)
  0x4c; 0x0f; 0x44; 0x8c; 0x24; 0x40; 0x0c; 0x00; 0x00;
                           (* CMOVE (% r9) (Memop Quadword (%% (rsp,3136))) *)
  0x4c; 0x0f; 0x44; 0x94; 0x24; 0x48; 0x0c; 0x00; 0x00;
                           (* CMOVE (% r10) (Memop Quadword (%% (rsp,3144))) *)
  0x4c; 0x0f; 0x44; 0x9c; 0x24; 0x50; 0x0c; 0x00; 0x00;
                           (* CMOVE (% r11) (Memop Quadword (%% (rsp,3152))) *)
  0x4c; 0x0f; 0x44; 0xa4; 0x24; 0x58; 0x0c; 0x00; 0x00;
                           (* CMOVE (% r12) (Memop Quadword (%% (rsp,3160))) *)
  0x48; 0x83; 0xff; 0x0e;  (* CMP (% rdi) (Imm8 (word 14)) *)
  0x48; 0x0f; 0x44; 0x84; 0x24; 0xf0; 0x0c; 0x00; 0x00;
                           (* CMOVE (% rax) (Memop Quadword (%% (rsp,3312))) *)
  0x48; 0x0f; 0x44; 0x9c; 0x24; 0xf8; 0x0c; 0x00; 0x00;
                           (* CMOVE (% rbx) (Memop Quadword (%% (rsp,3320))) *)
  0x48; 0x0f; 0x44; 0x8c; 0x24; 0x00; 0x0d; 0x00; 0x00;
                           (* CMOVE (% rcx) (Memop Quadword (%% (rsp,3328))) *)
  0x48; 0x0f; 0x44; 0x94; 0x24; 0x08; 0x0d; 0x00; 0x00;
                           (* CMOVE (% rdx) (Memop Quadword (%% (rsp,3336))) *)
  0x4c; 0x0f; 0x44; 0x84; 0x24; 0x10; 0x0d; 0x00; 0x00;
                           (* CMOVE (% r8) (Memop Quadword (%% (rsp,3344))) *)
  0x4c; 0x0f; 0x44; 0x8c; 0x24; 0x18; 0x0d; 0x00; 0x00;
                           (* CMOVE (% r9) (Memop Quadword (%% (rsp,3352))) *)
  0x4c; 0x0f; 0x44; 0x94; 0x24; 0x20; 0x0d; 0x00; 0x00;
                           (* CMOVE (% r10) (Memop Quadword (%% (rsp,3360))) *)
  0x4c; 0x0f; 0x44; 0x9c; 0x24; 0x28; 0x0d; 0x00; 0x00;
                           (* CMOVE (% r11) (Memop Quadword (%% (rsp,3368))) *)
  0x4c; 0x0f; 0x44; 0xa4; 0x24; 0x30; 0x0d; 0x00; 0x00;
                           (* CMOVE (% r12) (Memop Quadword (%% (rsp,3376))) *)
  0x48; 0x83; 0xff; 0x0f;  (* CMP (% rdi) (Imm8 (word 15)) *)
  0x48; 0x0f; 0x44; 0x84; 0x24; 0xc8; 0x0d; 0x00; 0x00;
                           (* CMOVE (% rax) (Memop Quadword (%% (rsp,3528))) *)
  0x48; 0x0f; 0x44; 0x9c; 0x24; 0xd0; 0x0d; 0x00; 0x00;
                           (* CMOVE (% rbx) (Memop Quadword (%% (rsp,3536))) *)
  0x48; 0x0f; 0x44; 0x8c; 0x24; 0xd8; 0x0d; 0x00; 0x00;
                           (* CMOVE (% rcx) (Memop Quadword (%% (rsp,3544))) *)
  0x48; 0x0f; 0x44; 0x94; 0x24; 0xe0; 0x0d; 0x00; 0x00;
                           (* CMOVE (% rdx) (Memop Quadword (%% (rsp,3552))) *)
  0x4c; 0x0f; 0x44; 0x84; 0x24; 0xe8; 0x0d; 0x00; 0x00;
                           (* CMOVE (% r8) (Memop Quadword (%% (rsp,3560))) *)
  0x4c; 0x0f; 0x44; 0x8c; 0x24; 0xf0; 0x0d; 0x00; 0x00;
                           (* CMOVE (% r9) (Memop Quadword (%% (rsp,3568))) *)
  0x4c; 0x0f; 0x44; 0x94; 0x24; 0xf8; 0x0d; 0x00; 0x00;
                           (* CMOVE (% r10) (Memop Quadword (%% (rsp,3576))) *)
  0x4c; 0x0f; 0x44; 0x9c; 0x24; 0x00; 0x0e; 0x00; 0x00;
                           (* CMOVE (% r11) (Memop Quadword (%% (rsp,3584))) *)
  0x4c; 0x0f; 0x44; 0xa4; 0x24; 0x08; 0x0e; 0x00; 0x00;
                           (* CMOVE (% r12) (Memop Quadword (%% (rsp,3592))) *)
  0x48; 0x83; 0xff; 0x10;  (* CMP (% rdi) (Imm8 (word 16)) *)
  0x48; 0x0f; 0x44; 0x84; 0x24; 0xa0; 0x0e; 0x00; 0x00;
                           (* CMOVE (% rax) (Memop Quadword (%% (rsp,3744))) *)
  0x48; 0x0f; 0x44; 0x9c; 0x24; 0xa8; 0x0e; 0x00; 0x00;
                           (* CMOVE (% rbx) (Memop Quadword (%% (rsp,3752))) *)
  0x48; 0x0f; 0x44; 0x8c; 0x24; 0xb0; 0x0e; 0x00; 0x00;
                           (* CMOVE (% rcx) (Memop Quadword (%% (rsp,3760))) *)
  0x48; 0x0f; 0x44; 0x94; 0x24; 0xb8; 0x0e; 0x00; 0x00;
                           (* CMOVE (% rdx) (Memop Quadword (%% (rsp,3768))) *)
  0x4c; 0x0f; 0x44; 0x84; 0x24; 0xc0; 0x0e; 0x00; 0x00;
                           (* CMOVE (% r8) (Memop Quadword (%% (rsp,3776))) *)
  0x4c; 0x0f; 0x44; 0x8c; 0x24; 0xc8; 0x0e; 0x00; 0x00;
                           (* CMOVE (% r9) (Memop Quadword (%% (rsp,3784))) *)
  0x4c; 0x0f; 0x44; 0x94; 0x24; 0xd0; 0x0e; 0x00; 0x00;
                           (* CMOVE (% r10) (Memop Quadword (%% (rsp,3792))) *)
  0x4c; 0x0f; 0x44; 0x9c; 0x24; 0xd8; 0x0e; 0x00; 0x00;
                           (* CMOVE (% r11) (Memop Quadword (%% (rsp,3800))) *)
  0x4c; 0x0f; 0x44; 0xa4; 0x24; 0xe0; 0x0e; 0x00; 0x00;
                           (* CMOVE (% r12) (Memop Quadword (%% (rsp,3808))) *)
  0x48; 0x89; 0x84; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,288))) (% rax) *)
  0x48; 0x89; 0x9c; 0x24; 0x28; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,296))) (% rbx) *)
  0x48; 0x89; 0x8c; 0x24; 0x30; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,304))) (% rcx) *)
  0x48; 0x89; 0x94; 0x24; 0x38; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,312))) (% rdx) *)
  0x4c; 0x89; 0x84; 0x24; 0x40; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,320))) (% r8) *)
  0x4c; 0x89; 0x8c; 0x24; 0x48; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,328))) (% r9) *)
  0x4c; 0x89; 0x94; 0x24; 0x50; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,336))) (% r10) *)
  0x4c; 0x89; 0x9c; 0x24; 0x58; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,344))) (% r11) *)
  0x4c; 0x89; 0xa4; 0x24; 0x60; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,352))) (% r12) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0x31; 0xdb;              (* XOR (% ebx) (% ebx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x31; 0xd2;              (* XOR (% edx) (% edx) *)
  0x45; 0x31; 0xc0;        (* XOR (% r8d) (% r8d) *)
  0x45; 0x31; 0xc9;        (* XOR (% r9d) (% r9d) *)
  0x45; 0x31; 0xd2;        (* XOR (% r10d) (% r10d) *)
  0x45; 0x31; 0xdb;        (* XOR (% r11d) (% r11d) *)
  0x45; 0x31; 0xe4;        (* XOR (% r12d) (% r12d) *)
  0x48; 0x83; 0xff; 0x01;  (* CMP (% rdi) (Imm8 (word 1)) *)
  0x48; 0x0f; 0x44; 0x84; 0x24; 0x88; 0x02; 0x00; 0x00;
                           (* CMOVE (% rax) (Memop Quadword (%% (rsp,648))) *)
  0x48; 0x0f; 0x44; 0x9c; 0x24; 0x90; 0x02; 0x00; 0x00;
                           (* CMOVE (% rbx) (Memop Quadword (%% (rsp,656))) *)
  0x48; 0x0f; 0x44; 0x8c; 0x24; 0x98; 0x02; 0x00; 0x00;
                           (* CMOVE (% rcx) (Memop Quadword (%% (rsp,664))) *)
  0x48; 0x0f; 0x44; 0x94; 0x24; 0xa0; 0x02; 0x00; 0x00;
                           (* CMOVE (% rdx) (Memop Quadword (%% (rsp,672))) *)
  0x4c; 0x0f; 0x44; 0x84; 0x24; 0xa8; 0x02; 0x00; 0x00;
                           (* CMOVE (% r8) (Memop Quadword (%% (rsp,680))) *)
  0x4c; 0x0f; 0x44; 0x8c; 0x24; 0xb0; 0x02; 0x00; 0x00;
                           (* CMOVE (% r9) (Memop Quadword (%% (rsp,688))) *)
  0x4c; 0x0f; 0x44; 0x94; 0x24; 0xb8; 0x02; 0x00; 0x00;
                           (* CMOVE (% r10) (Memop Quadword (%% (rsp,696))) *)
  0x4c; 0x0f; 0x44; 0x9c; 0x24; 0xc0; 0x02; 0x00; 0x00;
                           (* CMOVE (% r11) (Memop Quadword (%% (rsp,704))) *)
  0x4c; 0x0f; 0x44; 0xa4; 0x24; 0xc8; 0x02; 0x00; 0x00;
                           (* CMOVE (% r12) (Memop Quadword (%% (rsp,712))) *)
  0x48; 0x83; 0xff; 0x02;  (* CMP (% rdi) (Imm8 (word 2)) *)
  0x48; 0x0f; 0x44; 0x84; 0x24; 0x60; 0x03; 0x00; 0x00;
                           (* CMOVE (% rax) (Memop Quadword (%% (rsp,864))) *)
  0x48; 0x0f; 0x44; 0x9c; 0x24; 0x68; 0x03; 0x00; 0x00;
                           (* CMOVE (% rbx) (Memop Quadword (%% (rsp,872))) *)
  0x48; 0x0f; 0x44; 0x8c; 0x24; 0x70; 0x03; 0x00; 0x00;
                           (* CMOVE (% rcx) (Memop Quadword (%% (rsp,880))) *)
  0x48; 0x0f; 0x44; 0x94; 0x24; 0x78; 0x03; 0x00; 0x00;
                           (* CMOVE (% rdx) (Memop Quadword (%% (rsp,888))) *)
  0x4c; 0x0f; 0x44; 0x84; 0x24; 0x80; 0x03; 0x00; 0x00;
                           (* CMOVE (% r8) (Memop Quadword (%% (rsp,896))) *)
  0x4c; 0x0f; 0x44; 0x8c; 0x24; 0x88; 0x03; 0x00; 0x00;
                           (* CMOVE (% r9) (Memop Quadword (%% (rsp,904))) *)
  0x4c; 0x0f; 0x44; 0x94; 0x24; 0x90; 0x03; 0x00; 0x00;
                           (* CMOVE (% r10) (Memop Quadword (%% (rsp,912))) *)
  0x4c; 0x0f; 0x44; 0x9c; 0x24; 0x98; 0x03; 0x00; 0x00;
                           (* CMOVE (% r11) (Memop Quadword (%% (rsp,920))) *)
  0x4c; 0x0f; 0x44; 0xa4; 0x24; 0xa0; 0x03; 0x00; 0x00;
                           (* CMOVE (% r12) (Memop Quadword (%% (rsp,928))) *)
  0x48; 0x83; 0xff; 0x03;  (* CMP (% rdi) (Imm8 (word 3)) *)
  0x48; 0x0f; 0x44; 0x84; 0x24; 0x38; 0x04; 0x00; 0x00;
                           (* CMOVE (% rax) (Memop Quadword (%% (rsp,1080))) *)
  0x48; 0x0f; 0x44; 0x9c; 0x24; 0x40; 0x04; 0x00; 0x00;
                           (* CMOVE (% rbx) (Memop Quadword (%% (rsp,1088))) *)
  0x48; 0x0f; 0x44; 0x8c; 0x24; 0x48; 0x04; 0x00; 0x00;
                           (* CMOVE (% rcx) (Memop Quadword (%% (rsp,1096))) *)
  0x48; 0x0f; 0x44; 0x94; 0x24; 0x50; 0x04; 0x00; 0x00;
                           (* CMOVE (% rdx) (Memop Quadword (%% (rsp,1104))) *)
  0x4c; 0x0f; 0x44; 0x84; 0x24; 0x58; 0x04; 0x00; 0x00;
                           (* CMOVE (% r8) (Memop Quadword (%% (rsp,1112))) *)
  0x4c; 0x0f; 0x44; 0x8c; 0x24; 0x60; 0x04; 0x00; 0x00;
                           (* CMOVE (% r9) (Memop Quadword (%% (rsp,1120))) *)
  0x4c; 0x0f; 0x44; 0x94; 0x24; 0x68; 0x04; 0x00; 0x00;
                           (* CMOVE (% r10) (Memop Quadword (%% (rsp,1128))) *)
  0x4c; 0x0f; 0x44; 0x9c; 0x24; 0x70; 0x04; 0x00; 0x00;
                           (* CMOVE (% r11) (Memop Quadword (%% (rsp,1136))) *)
  0x4c; 0x0f; 0x44; 0xa4; 0x24; 0x78; 0x04; 0x00; 0x00;
                           (* CMOVE (% r12) (Memop Quadword (%% (rsp,1144))) *)
  0x48; 0x83; 0xff; 0x04;  (* CMP (% rdi) (Imm8 (word 4)) *)
  0x48; 0x0f; 0x44; 0x84; 0x24; 0x10; 0x05; 0x00; 0x00;
                           (* CMOVE (% rax) (Memop Quadword (%% (rsp,1296))) *)
  0x48; 0x0f; 0x44; 0x9c; 0x24; 0x18; 0x05; 0x00; 0x00;
                           (* CMOVE (% rbx) (Memop Quadword (%% (rsp,1304))) *)
  0x48; 0x0f; 0x44; 0x8c; 0x24; 0x20; 0x05; 0x00; 0x00;
                           (* CMOVE (% rcx) (Memop Quadword (%% (rsp,1312))) *)
  0x48; 0x0f; 0x44; 0x94; 0x24; 0x28; 0x05; 0x00; 0x00;
                           (* CMOVE (% rdx) (Memop Quadword (%% (rsp,1320))) *)
  0x4c; 0x0f; 0x44; 0x84; 0x24; 0x30; 0x05; 0x00; 0x00;
                           (* CMOVE (% r8) (Memop Quadword (%% (rsp,1328))) *)
  0x4c; 0x0f; 0x44; 0x8c; 0x24; 0x38; 0x05; 0x00; 0x00;
                           (* CMOVE (% r9) (Memop Quadword (%% (rsp,1336))) *)
  0x4c; 0x0f; 0x44; 0x94; 0x24; 0x40; 0x05; 0x00; 0x00;
                           (* CMOVE (% r10) (Memop Quadword (%% (rsp,1344))) *)
  0x4c; 0x0f; 0x44; 0x9c; 0x24; 0x48; 0x05; 0x00; 0x00;
                           (* CMOVE (% r11) (Memop Quadword (%% (rsp,1352))) *)
  0x4c; 0x0f; 0x44; 0xa4; 0x24; 0x50; 0x05; 0x00; 0x00;
                           (* CMOVE (% r12) (Memop Quadword (%% (rsp,1360))) *)
  0x48; 0x83; 0xff; 0x05;  (* CMP (% rdi) (Imm8 (word 5)) *)
  0x48; 0x0f; 0x44; 0x84; 0x24; 0xe8; 0x05; 0x00; 0x00;
                           (* CMOVE (% rax) (Memop Quadword (%% (rsp,1512))) *)
  0x48; 0x0f; 0x44; 0x9c; 0x24; 0xf0; 0x05; 0x00; 0x00;
                           (* CMOVE (% rbx) (Memop Quadword (%% (rsp,1520))) *)
  0x48; 0x0f; 0x44; 0x8c; 0x24; 0xf8; 0x05; 0x00; 0x00;
                           (* CMOVE (% rcx) (Memop Quadword (%% (rsp,1528))) *)
  0x48; 0x0f; 0x44; 0x94; 0x24; 0x00; 0x06; 0x00; 0x00;
                           (* CMOVE (% rdx) (Memop Quadword (%% (rsp,1536))) *)
  0x4c; 0x0f; 0x44; 0x84; 0x24; 0x08; 0x06; 0x00; 0x00;
                           (* CMOVE (% r8) (Memop Quadword (%% (rsp,1544))) *)
  0x4c; 0x0f; 0x44; 0x8c; 0x24; 0x10; 0x06; 0x00; 0x00;
                           (* CMOVE (% r9) (Memop Quadword (%% (rsp,1552))) *)
  0x4c; 0x0f; 0x44; 0x94; 0x24; 0x18; 0x06; 0x00; 0x00;
                           (* CMOVE (% r10) (Memop Quadword (%% (rsp,1560))) *)
  0x4c; 0x0f; 0x44; 0x9c; 0x24; 0x20; 0x06; 0x00; 0x00;
                           (* CMOVE (% r11) (Memop Quadword (%% (rsp,1568))) *)
  0x4c; 0x0f; 0x44; 0xa4; 0x24; 0x28; 0x06; 0x00; 0x00;
                           (* CMOVE (% r12) (Memop Quadword (%% (rsp,1576))) *)
  0x48; 0x83; 0xff; 0x06;  (* CMP (% rdi) (Imm8 (word 6)) *)
  0x48; 0x0f; 0x44; 0x84; 0x24; 0xc0; 0x06; 0x00; 0x00;
                           (* CMOVE (% rax) (Memop Quadword (%% (rsp,1728))) *)
  0x48; 0x0f; 0x44; 0x9c; 0x24; 0xc8; 0x06; 0x00; 0x00;
                           (* CMOVE (% rbx) (Memop Quadword (%% (rsp,1736))) *)
  0x48; 0x0f; 0x44; 0x8c; 0x24; 0xd0; 0x06; 0x00; 0x00;
                           (* CMOVE (% rcx) (Memop Quadword (%% (rsp,1744))) *)
  0x48; 0x0f; 0x44; 0x94; 0x24; 0xd8; 0x06; 0x00; 0x00;
                           (* CMOVE (% rdx) (Memop Quadword (%% (rsp,1752))) *)
  0x4c; 0x0f; 0x44; 0x84; 0x24; 0xe0; 0x06; 0x00; 0x00;
                           (* CMOVE (% r8) (Memop Quadword (%% (rsp,1760))) *)
  0x4c; 0x0f; 0x44; 0x8c; 0x24; 0xe8; 0x06; 0x00; 0x00;
                           (* CMOVE (% r9) (Memop Quadword (%% (rsp,1768))) *)
  0x4c; 0x0f; 0x44; 0x94; 0x24; 0xf0; 0x06; 0x00; 0x00;
                           (* CMOVE (% r10) (Memop Quadword (%% (rsp,1776))) *)
  0x4c; 0x0f; 0x44; 0x9c; 0x24; 0xf8; 0x06; 0x00; 0x00;
                           (* CMOVE (% r11) (Memop Quadword (%% (rsp,1784))) *)
  0x4c; 0x0f; 0x44; 0xa4; 0x24; 0x00; 0x07; 0x00; 0x00;
                           (* CMOVE (% r12) (Memop Quadword (%% (rsp,1792))) *)
  0x48; 0x83; 0xff; 0x07;  (* CMP (% rdi) (Imm8 (word 7)) *)
  0x48; 0x0f; 0x44; 0x84; 0x24; 0x98; 0x07; 0x00; 0x00;
                           (* CMOVE (% rax) (Memop Quadword (%% (rsp,1944))) *)
  0x48; 0x0f; 0x44; 0x9c; 0x24; 0xa0; 0x07; 0x00; 0x00;
                           (* CMOVE (% rbx) (Memop Quadword (%% (rsp,1952))) *)
  0x48; 0x0f; 0x44; 0x8c; 0x24; 0xa8; 0x07; 0x00; 0x00;
                           (* CMOVE (% rcx) (Memop Quadword (%% (rsp,1960))) *)
  0x48; 0x0f; 0x44; 0x94; 0x24; 0xb0; 0x07; 0x00; 0x00;
                           (* CMOVE (% rdx) (Memop Quadword (%% (rsp,1968))) *)
  0x4c; 0x0f; 0x44; 0x84; 0x24; 0xb8; 0x07; 0x00; 0x00;
                           (* CMOVE (% r8) (Memop Quadword (%% (rsp,1976))) *)
  0x4c; 0x0f; 0x44; 0x8c; 0x24; 0xc0; 0x07; 0x00; 0x00;
                           (* CMOVE (% r9) (Memop Quadword (%% (rsp,1984))) *)
  0x4c; 0x0f; 0x44; 0x94; 0x24; 0xc8; 0x07; 0x00; 0x00;
                           (* CMOVE (% r10) (Memop Quadword (%% (rsp,1992))) *)
  0x4c; 0x0f; 0x44; 0x9c; 0x24; 0xd0; 0x07; 0x00; 0x00;
                           (* CMOVE (% r11) (Memop Quadword (%% (rsp,2000))) *)
  0x4c; 0x0f; 0x44; 0xa4; 0x24; 0xd8; 0x07; 0x00; 0x00;
                           (* CMOVE (% r12) (Memop Quadword (%% (rsp,2008))) *)
  0x48; 0x83; 0xff; 0x08;  (* CMP (% rdi) (Imm8 (word 8)) *)
  0x48; 0x0f; 0x44; 0x84; 0x24; 0x70; 0x08; 0x00; 0x00;
                           (* CMOVE (% rax) (Memop Quadword (%% (rsp,2160))) *)
  0x48; 0x0f; 0x44; 0x9c; 0x24; 0x78; 0x08; 0x00; 0x00;
                           (* CMOVE (% rbx) (Memop Quadword (%% (rsp,2168))) *)
  0x48; 0x0f; 0x44; 0x8c; 0x24; 0x80; 0x08; 0x00; 0x00;
                           (* CMOVE (% rcx) (Memop Quadword (%% (rsp,2176))) *)
  0x48; 0x0f; 0x44; 0x94; 0x24; 0x88; 0x08; 0x00; 0x00;
                           (* CMOVE (% rdx) (Memop Quadword (%% (rsp,2184))) *)
  0x4c; 0x0f; 0x44; 0x84; 0x24; 0x90; 0x08; 0x00; 0x00;
                           (* CMOVE (% r8) (Memop Quadword (%% (rsp,2192))) *)
  0x4c; 0x0f; 0x44; 0x8c; 0x24; 0x98; 0x08; 0x00; 0x00;
                           (* CMOVE (% r9) (Memop Quadword (%% (rsp,2200))) *)
  0x4c; 0x0f; 0x44; 0x94; 0x24; 0xa0; 0x08; 0x00; 0x00;
                           (* CMOVE (% r10) (Memop Quadword (%% (rsp,2208))) *)
  0x4c; 0x0f; 0x44; 0x9c; 0x24; 0xa8; 0x08; 0x00; 0x00;
                           (* CMOVE (% r11) (Memop Quadword (%% (rsp,2216))) *)
  0x4c; 0x0f; 0x44; 0xa4; 0x24; 0xb0; 0x08; 0x00; 0x00;
                           (* CMOVE (% r12) (Memop Quadword (%% (rsp,2224))) *)
  0x48; 0x83; 0xff; 0x09;  (* CMP (% rdi) (Imm8 (word 9)) *)
  0x48; 0x0f; 0x44; 0x84; 0x24; 0x48; 0x09; 0x00; 0x00;
                           (* CMOVE (% rax) (Memop Quadword (%% (rsp,2376))) *)
  0x48; 0x0f; 0x44; 0x9c; 0x24; 0x50; 0x09; 0x00; 0x00;
                           (* CMOVE (% rbx) (Memop Quadword (%% (rsp,2384))) *)
  0x48; 0x0f; 0x44; 0x8c; 0x24; 0x58; 0x09; 0x00; 0x00;
                           (* CMOVE (% rcx) (Memop Quadword (%% (rsp,2392))) *)
  0x48; 0x0f; 0x44; 0x94; 0x24; 0x60; 0x09; 0x00; 0x00;
                           (* CMOVE (% rdx) (Memop Quadword (%% (rsp,2400))) *)
  0x4c; 0x0f; 0x44; 0x84; 0x24; 0x68; 0x09; 0x00; 0x00;
                           (* CMOVE (% r8) (Memop Quadword (%% (rsp,2408))) *)
  0x4c; 0x0f; 0x44; 0x8c; 0x24; 0x70; 0x09; 0x00; 0x00;
                           (* CMOVE (% r9) (Memop Quadword (%% (rsp,2416))) *)
  0x4c; 0x0f; 0x44; 0x94; 0x24; 0x78; 0x09; 0x00; 0x00;
                           (* CMOVE (% r10) (Memop Quadword (%% (rsp,2424))) *)
  0x4c; 0x0f; 0x44; 0x9c; 0x24; 0x80; 0x09; 0x00; 0x00;
                           (* CMOVE (% r11) (Memop Quadword (%% (rsp,2432))) *)
  0x4c; 0x0f; 0x44; 0xa4; 0x24; 0x88; 0x09; 0x00; 0x00;
                           (* CMOVE (% r12) (Memop Quadword (%% (rsp,2440))) *)
  0x48; 0x83; 0xff; 0x0a;  (* CMP (% rdi) (Imm8 (word 10)) *)
  0x48; 0x0f; 0x44; 0x84; 0x24; 0x20; 0x0a; 0x00; 0x00;
                           (* CMOVE (% rax) (Memop Quadword (%% (rsp,2592))) *)
  0x48; 0x0f; 0x44; 0x9c; 0x24; 0x28; 0x0a; 0x00; 0x00;
                           (* CMOVE (% rbx) (Memop Quadword (%% (rsp,2600))) *)
  0x48; 0x0f; 0x44; 0x8c; 0x24; 0x30; 0x0a; 0x00; 0x00;
                           (* CMOVE (% rcx) (Memop Quadword (%% (rsp,2608))) *)
  0x48; 0x0f; 0x44; 0x94; 0x24; 0x38; 0x0a; 0x00; 0x00;
                           (* CMOVE (% rdx) (Memop Quadword (%% (rsp,2616))) *)
  0x4c; 0x0f; 0x44; 0x84; 0x24; 0x40; 0x0a; 0x00; 0x00;
                           (* CMOVE (% r8) (Memop Quadword (%% (rsp,2624))) *)
  0x4c; 0x0f; 0x44; 0x8c; 0x24; 0x48; 0x0a; 0x00; 0x00;
                           (* CMOVE (% r9) (Memop Quadword (%% (rsp,2632))) *)
  0x4c; 0x0f; 0x44; 0x94; 0x24; 0x50; 0x0a; 0x00; 0x00;
                           (* CMOVE (% r10) (Memop Quadword (%% (rsp,2640))) *)
  0x4c; 0x0f; 0x44; 0x9c; 0x24; 0x58; 0x0a; 0x00; 0x00;
                           (* CMOVE (% r11) (Memop Quadword (%% (rsp,2648))) *)
  0x4c; 0x0f; 0x44; 0xa4; 0x24; 0x60; 0x0a; 0x00; 0x00;
                           (* CMOVE (% r12) (Memop Quadword (%% (rsp,2656))) *)
  0x48; 0x83; 0xff; 0x0b;  (* CMP (% rdi) (Imm8 (word 11)) *)
  0x48; 0x0f; 0x44; 0x84; 0x24; 0xf8; 0x0a; 0x00; 0x00;
                           (* CMOVE (% rax) (Memop Quadword (%% (rsp,2808))) *)
  0x48; 0x0f; 0x44; 0x9c; 0x24; 0x00; 0x0b; 0x00; 0x00;
                           (* CMOVE (% rbx) (Memop Quadword (%% (rsp,2816))) *)
  0x48; 0x0f; 0x44; 0x8c; 0x24; 0x08; 0x0b; 0x00; 0x00;
                           (* CMOVE (% rcx) (Memop Quadword (%% (rsp,2824))) *)
  0x48; 0x0f; 0x44; 0x94; 0x24; 0x10; 0x0b; 0x00; 0x00;
                           (* CMOVE (% rdx) (Memop Quadword (%% (rsp,2832))) *)
  0x4c; 0x0f; 0x44; 0x84; 0x24; 0x18; 0x0b; 0x00; 0x00;
                           (* CMOVE (% r8) (Memop Quadword (%% (rsp,2840))) *)
  0x4c; 0x0f; 0x44; 0x8c; 0x24; 0x20; 0x0b; 0x00; 0x00;
                           (* CMOVE (% r9) (Memop Quadword (%% (rsp,2848))) *)
  0x4c; 0x0f; 0x44; 0x94; 0x24; 0x28; 0x0b; 0x00; 0x00;
                           (* CMOVE (% r10) (Memop Quadword (%% (rsp,2856))) *)
  0x4c; 0x0f; 0x44; 0x9c; 0x24; 0x30; 0x0b; 0x00; 0x00;
                           (* CMOVE (% r11) (Memop Quadword (%% (rsp,2864))) *)
  0x4c; 0x0f; 0x44; 0xa4; 0x24; 0x38; 0x0b; 0x00; 0x00;
                           (* CMOVE (% r12) (Memop Quadword (%% (rsp,2872))) *)
  0x48; 0x83; 0xff; 0x0c;  (* CMP (% rdi) (Imm8 (word 12)) *)
  0x48; 0x0f; 0x44; 0x84; 0x24; 0xd0; 0x0b; 0x00; 0x00;
                           (* CMOVE (% rax) (Memop Quadword (%% (rsp,3024))) *)
  0x48; 0x0f; 0x44; 0x9c; 0x24; 0xd8; 0x0b; 0x00; 0x00;
                           (* CMOVE (% rbx) (Memop Quadword (%% (rsp,3032))) *)
  0x48; 0x0f; 0x44; 0x8c; 0x24; 0xe0; 0x0b; 0x00; 0x00;
                           (* CMOVE (% rcx) (Memop Quadword (%% (rsp,3040))) *)
  0x48; 0x0f; 0x44; 0x94; 0x24; 0xe8; 0x0b; 0x00; 0x00;
                           (* CMOVE (% rdx) (Memop Quadword (%% (rsp,3048))) *)
  0x4c; 0x0f; 0x44; 0x84; 0x24; 0xf0; 0x0b; 0x00; 0x00;
                           (* CMOVE (% r8) (Memop Quadword (%% (rsp,3056))) *)
  0x4c; 0x0f; 0x44; 0x8c; 0x24; 0xf8; 0x0b; 0x00; 0x00;
                           (* CMOVE (% r9) (Memop Quadword (%% (rsp,3064))) *)
  0x4c; 0x0f; 0x44; 0x94; 0x24; 0x00; 0x0c; 0x00; 0x00;
                           (* CMOVE (% r10) (Memop Quadword (%% (rsp,3072))) *)
  0x4c; 0x0f; 0x44; 0x9c; 0x24; 0x08; 0x0c; 0x00; 0x00;
                           (* CMOVE (% r11) (Memop Quadword (%% (rsp,3080))) *)
  0x4c; 0x0f; 0x44; 0xa4; 0x24; 0x10; 0x0c; 0x00; 0x00;
                           (* CMOVE (% r12) (Memop Quadword (%% (rsp,3088))) *)
  0x48; 0x83; 0xff; 0x0d;  (* CMP (% rdi) (Imm8 (word 13)) *)
  0x48; 0x0f; 0x44; 0x84; 0x24; 0xa8; 0x0c; 0x00; 0x00;
                           (* CMOVE (% rax) (Memop Quadword (%% (rsp,3240))) *)
  0x48; 0x0f; 0x44; 0x9c; 0x24; 0xb0; 0x0c; 0x00; 0x00;
                           (* CMOVE (% rbx) (Memop Quadword (%% (rsp,3248))) *)
  0x48; 0x0f; 0x44; 0x8c; 0x24; 0xb8; 0x0c; 0x00; 0x00;
                           (* CMOVE (% rcx) (Memop Quadword (%% (rsp,3256))) *)
  0x48; 0x0f; 0x44; 0x94; 0x24; 0xc0; 0x0c; 0x00; 0x00;
                           (* CMOVE (% rdx) (Memop Quadword (%% (rsp,3264))) *)
  0x4c; 0x0f; 0x44; 0x84; 0x24; 0xc8; 0x0c; 0x00; 0x00;
                           (* CMOVE (% r8) (Memop Quadword (%% (rsp,3272))) *)
  0x4c; 0x0f; 0x44; 0x8c; 0x24; 0xd0; 0x0c; 0x00; 0x00;
                           (* CMOVE (% r9) (Memop Quadword (%% (rsp,3280))) *)
  0x4c; 0x0f; 0x44; 0x94; 0x24; 0xd8; 0x0c; 0x00; 0x00;
                           (* CMOVE (% r10) (Memop Quadword (%% (rsp,3288))) *)
  0x4c; 0x0f; 0x44; 0x9c; 0x24; 0xe0; 0x0c; 0x00; 0x00;
                           (* CMOVE (% r11) (Memop Quadword (%% (rsp,3296))) *)
  0x4c; 0x0f; 0x44; 0xa4; 0x24; 0xe8; 0x0c; 0x00; 0x00;
                           (* CMOVE (% r12) (Memop Quadword (%% (rsp,3304))) *)
  0x48; 0x83; 0xff; 0x0e;  (* CMP (% rdi) (Imm8 (word 14)) *)
  0x48; 0x0f; 0x44; 0x84; 0x24; 0x80; 0x0d; 0x00; 0x00;
                           (* CMOVE (% rax) (Memop Quadword (%% (rsp,3456))) *)
  0x48; 0x0f; 0x44; 0x9c; 0x24; 0x88; 0x0d; 0x00; 0x00;
                           (* CMOVE (% rbx) (Memop Quadword (%% (rsp,3464))) *)
  0x48; 0x0f; 0x44; 0x8c; 0x24; 0x90; 0x0d; 0x00; 0x00;
                           (* CMOVE (% rcx) (Memop Quadword (%% (rsp,3472))) *)
  0x48; 0x0f; 0x44; 0x94; 0x24; 0x98; 0x0d; 0x00; 0x00;
                           (* CMOVE (% rdx) (Memop Quadword (%% (rsp,3480))) *)
  0x4c; 0x0f; 0x44; 0x84; 0x24; 0xa0; 0x0d; 0x00; 0x00;
                           (* CMOVE (% r8) (Memop Quadword (%% (rsp,3488))) *)
  0x4c; 0x0f; 0x44; 0x8c; 0x24; 0xa8; 0x0d; 0x00; 0x00;
                           (* CMOVE (% r9) (Memop Quadword (%% (rsp,3496))) *)
  0x4c; 0x0f; 0x44; 0x94; 0x24; 0xb0; 0x0d; 0x00; 0x00;
                           (* CMOVE (% r10) (Memop Quadword (%% (rsp,3504))) *)
  0x4c; 0x0f; 0x44; 0x9c; 0x24; 0xb8; 0x0d; 0x00; 0x00;
                           (* CMOVE (% r11) (Memop Quadword (%% (rsp,3512))) *)
  0x4c; 0x0f; 0x44; 0xa4; 0x24; 0xc0; 0x0d; 0x00; 0x00;
                           (* CMOVE (% r12) (Memop Quadword (%% (rsp,3520))) *)
  0x48; 0x83; 0xff; 0x0f;  (* CMP (% rdi) (Imm8 (word 15)) *)
  0x48; 0x0f; 0x44; 0x84; 0x24; 0x58; 0x0e; 0x00; 0x00;
                           (* CMOVE (% rax) (Memop Quadword (%% (rsp,3672))) *)
  0x48; 0x0f; 0x44; 0x9c; 0x24; 0x60; 0x0e; 0x00; 0x00;
                           (* CMOVE (% rbx) (Memop Quadword (%% (rsp,3680))) *)
  0x48; 0x0f; 0x44; 0x8c; 0x24; 0x68; 0x0e; 0x00; 0x00;
                           (* CMOVE (% rcx) (Memop Quadword (%% (rsp,3688))) *)
  0x48; 0x0f; 0x44; 0x94; 0x24; 0x70; 0x0e; 0x00; 0x00;
                           (* CMOVE (% rdx) (Memop Quadword (%% (rsp,3696))) *)
  0x4c; 0x0f; 0x44; 0x84; 0x24; 0x78; 0x0e; 0x00; 0x00;
                           (* CMOVE (% r8) (Memop Quadword (%% (rsp,3704))) *)
  0x4c; 0x0f; 0x44; 0x8c; 0x24; 0x80; 0x0e; 0x00; 0x00;
                           (* CMOVE (% r9) (Memop Quadword (%% (rsp,3712))) *)
  0x4c; 0x0f; 0x44; 0x94; 0x24; 0x88; 0x0e; 0x00; 0x00;
                           (* CMOVE (% r10) (Memop Quadword (%% (rsp,3720))) *)
  0x4c; 0x0f; 0x44; 0x9c; 0x24; 0x90; 0x0e; 0x00; 0x00;
                           (* CMOVE (% r11) (Memop Quadword (%% (rsp,3728))) *)
  0x4c; 0x0f; 0x44; 0xa4; 0x24; 0x98; 0x0e; 0x00; 0x00;
                           (* CMOVE (% r12) (Memop Quadword (%% (rsp,3736))) *)
  0x48; 0x83; 0xff; 0x10;  (* CMP (% rdi) (Imm8 (word 16)) *)
  0x48; 0x0f; 0x44; 0x84; 0x24; 0x30; 0x0f; 0x00; 0x00;
                           (* CMOVE (% rax) (Memop Quadword (%% (rsp,3888))) *)
  0x48; 0x0f; 0x44; 0x9c; 0x24; 0x38; 0x0f; 0x00; 0x00;
                           (* CMOVE (% rbx) (Memop Quadword (%% (rsp,3896))) *)
  0x48; 0x0f; 0x44; 0x8c; 0x24; 0x40; 0x0f; 0x00; 0x00;
                           (* CMOVE (% rcx) (Memop Quadword (%% (rsp,3904))) *)
  0x48; 0x0f; 0x44; 0x94; 0x24; 0x48; 0x0f; 0x00; 0x00;
                           (* CMOVE (% rdx) (Memop Quadword (%% (rsp,3912))) *)
  0x4c; 0x0f; 0x44; 0x84; 0x24; 0x50; 0x0f; 0x00; 0x00;
                           (* CMOVE (% r8) (Memop Quadword (%% (rsp,3920))) *)
  0x4c; 0x0f; 0x44; 0x8c; 0x24; 0x58; 0x0f; 0x00; 0x00;
                           (* CMOVE (% r9) (Memop Quadword (%% (rsp,3928))) *)
  0x4c; 0x0f; 0x44; 0x94; 0x24; 0x60; 0x0f; 0x00; 0x00;
                           (* CMOVE (% r10) (Memop Quadword (%% (rsp,3936))) *)
  0x4c; 0x0f; 0x44; 0x9c; 0x24; 0x68; 0x0f; 0x00; 0x00;
                           (* CMOVE (% r11) (Memop Quadword (%% (rsp,3944))) *)
  0x4c; 0x0f; 0x44; 0xa4; 0x24; 0x70; 0x0f; 0x00; 0x00;
                           (* CMOVE (% r12) (Memop Quadword (%% (rsp,3952))) *)
  0x48; 0x89; 0x84; 0x24; 0xb0; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,432))) (% rax) *)
  0x48; 0x89; 0x9c; 0x24; 0xb8; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,440))) (% rbx) *)
  0x48; 0x89; 0x8c; 0x24; 0xc0; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,448))) (% rcx) *)
  0x48; 0x89; 0x94; 0x24; 0xc8; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,456))) (% rdx) *)
  0x4c; 0x89; 0x84; 0x24; 0xd0; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,464))) (% r8) *)
  0x4c; 0x89; 0x8c; 0x24; 0xd8; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,472))) (% r9) *)
  0x4c; 0x89; 0x94; 0x24; 0xe0; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,480))) (% r10) *)
  0x4c; 0x89; 0x9c; 0x24; 0xe8; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,488))) (% r11) *)
  0x4c; 0x89; 0xa4; 0x24; 0xf0; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,496))) (% r12) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0x31; 0xdb;              (* XOR (% ebx) (% ebx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x31; 0xd2;              (* XOR (% edx) (% edx) *)
  0x45; 0x31; 0xc0;        (* XOR (% r8d) (% r8d) *)
  0x45; 0x31; 0xc9;        (* XOR (% r9d) (% r9d) *)
  0x45; 0x31; 0xd2;        (* XOR (% r10d) (% r10d) *)
  0x45; 0x31; 0xdb;        (* XOR (% r11d) (% r11d) *)
  0x45; 0x31; 0xe4;        (* XOR (% r12d) (% r12d) *)
  0x48; 0x83; 0xff; 0x01;  (* CMP (% rdi) (Imm8 (word 1)) *)
  0x48; 0x0f; 0x44; 0x84; 0x24; 0x40; 0x02; 0x00; 0x00;
                           (* CMOVE (% rax) (Memop Quadword (%% (rsp,576))) *)
  0x48; 0x0f; 0x44; 0x9c; 0x24; 0x48; 0x02; 0x00; 0x00;
                           (* CMOVE (% rbx) (Memop Quadword (%% (rsp,584))) *)
  0x48; 0x0f; 0x44; 0x8c; 0x24; 0x50; 0x02; 0x00; 0x00;
                           (* CMOVE (% rcx) (Memop Quadword (%% (rsp,592))) *)
  0x48; 0x0f; 0x44; 0x94; 0x24; 0x58; 0x02; 0x00; 0x00;
                           (* CMOVE (% rdx) (Memop Quadword (%% (rsp,600))) *)
  0x4c; 0x0f; 0x44; 0x84; 0x24; 0x60; 0x02; 0x00; 0x00;
                           (* CMOVE (% r8) (Memop Quadword (%% (rsp,608))) *)
  0x4c; 0x0f; 0x44; 0x8c; 0x24; 0x68; 0x02; 0x00; 0x00;
                           (* CMOVE (% r9) (Memop Quadword (%% (rsp,616))) *)
  0x4c; 0x0f; 0x44; 0x94; 0x24; 0x70; 0x02; 0x00; 0x00;
                           (* CMOVE (% r10) (Memop Quadword (%% (rsp,624))) *)
  0x4c; 0x0f; 0x44; 0x9c; 0x24; 0x78; 0x02; 0x00; 0x00;
                           (* CMOVE (% r11) (Memop Quadword (%% (rsp,632))) *)
  0x4c; 0x0f; 0x44; 0xa4; 0x24; 0x80; 0x02; 0x00; 0x00;
                           (* CMOVE (% r12) (Memop Quadword (%% (rsp,640))) *)
  0x48; 0x83; 0xff; 0x02;  (* CMP (% rdi) (Imm8 (word 2)) *)
  0x48; 0x0f; 0x44; 0x84; 0x24; 0x18; 0x03; 0x00; 0x00;
                           (* CMOVE (% rax) (Memop Quadword (%% (rsp,792))) *)
  0x48; 0x0f; 0x44; 0x9c; 0x24; 0x20; 0x03; 0x00; 0x00;
                           (* CMOVE (% rbx) (Memop Quadword (%% (rsp,800))) *)
  0x48; 0x0f; 0x44; 0x8c; 0x24; 0x28; 0x03; 0x00; 0x00;
                           (* CMOVE (% rcx) (Memop Quadword (%% (rsp,808))) *)
  0x48; 0x0f; 0x44; 0x94; 0x24; 0x30; 0x03; 0x00; 0x00;
                           (* CMOVE (% rdx) (Memop Quadword (%% (rsp,816))) *)
  0x4c; 0x0f; 0x44; 0x84; 0x24; 0x38; 0x03; 0x00; 0x00;
                           (* CMOVE (% r8) (Memop Quadword (%% (rsp,824))) *)
  0x4c; 0x0f; 0x44; 0x8c; 0x24; 0x40; 0x03; 0x00; 0x00;
                           (* CMOVE (% r9) (Memop Quadword (%% (rsp,832))) *)
  0x4c; 0x0f; 0x44; 0x94; 0x24; 0x48; 0x03; 0x00; 0x00;
                           (* CMOVE (% r10) (Memop Quadword (%% (rsp,840))) *)
  0x4c; 0x0f; 0x44; 0x9c; 0x24; 0x50; 0x03; 0x00; 0x00;
                           (* CMOVE (% r11) (Memop Quadword (%% (rsp,848))) *)
  0x4c; 0x0f; 0x44; 0xa4; 0x24; 0x58; 0x03; 0x00; 0x00;
                           (* CMOVE (% r12) (Memop Quadword (%% (rsp,856))) *)
  0x48; 0x83; 0xff; 0x03;  (* CMP (% rdi) (Imm8 (word 3)) *)
  0x48; 0x0f; 0x44; 0x84; 0x24; 0xf0; 0x03; 0x00; 0x00;
                           (* CMOVE (% rax) (Memop Quadword (%% (rsp,1008))) *)
  0x48; 0x0f; 0x44; 0x9c; 0x24; 0xf8; 0x03; 0x00; 0x00;
                           (* CMOVE (% rbx) (Memop Quadword (%% (rsp,1016))) *)
  0x48; 0x0f; 0x44; 0x8c; 0x24; 0x00; 0x04; 0x00; 0x00;
                           (* CMOVE (% rcx) (Memop Quadword (%% (rsp,1024))) *)
  0x48; 0x0f; 0x44; 0x94; 0x24; 0x08; 0x04; 0x00; 0x00;
                           (* CMOVE (% rdx) (Memop Quadword (%% (rsp,1032))) *)
  0x4c; 0x0f; 0x44; 0x84; 0x24; 0x10; 0x04; 0x00; 0x00;
                           (* CMOVE (% r8) (Memop Quadword (%% (rsp,1040))) *)
  0x4c; 0x0f; 0x44; 0x8c; 0x24; 0x18; 0x04; 0x00; 0x00;
                           (* CMOVE (% r9) (Memop Quadword (%% (rsp,1048))) *)
  0x4c; 0x0f; 0x44; 0x94; 0x24; 0x20; 0x04; 0x00; 0x00;
                           (* CMOVE (% r10) (Memop Quadword (%% (rsp,1056))) *)
  0x4c; 0x0f; 0x44; 0x9c; 0x24; 0x28; 0x04; 0x00; 0x00;
                           (* CMOVE (% r11) (Memop Quadword (%% (rsp,1064))) *)
  0x4c; 0x0f; 0x44; 0xa4; 0x24; 0x30; 0x04; 0x00; 0x00;
                           (* CMOVE (% r12) (Memop Quadword (%% (rsp,1072))) *)
  0x48; 0x83; 0xff; 0x04;  (* CMP (% rdi) (Imm8 (word 4)) *)
  0x48; 0x0f; 0x44; 0x84; 0x24; 0xc8; 0x04; 0x00; 0x00;
                           (* CMOVE (% rax) (Memop Quadword (%% (rsp,1224))) *)
  0x48; 0x0f; 0x44; 0x9c; 0x24; 0xd0; 0x04; 0x00; 0x00;
                           (* CMOVE (% rbx) (Memop Quadword (%% (rsp,1232))) *)
  0x48; 0x0f; 0x44; 0x8c; 0x24; 0xd8; 0x04; 0x00; 0x00;
                           (* CMOVE (% rcx) (Memop Quadword (%% (rsp,1240))) *)
  0x48; 0x0f; 0x44; 0x94; 0x24; 0xe0; 0x04; 0x00; 0x00;
                           (* CMOVE (% rdx) (Memop Quadword (%% (rsp,1248))) *)
  0x4c; 0x0f; 0x44; 0x84; 0x24; 0xe8; 0x04; 0x00; 0x00;
                           (* CMOVE (% r8) (Memop Quadword (%% (rsp,1256))) *)
  0x4c; 0x0f; 0x44; 0x8c; 0x24; 0xf0; 0x04; 0x00; 0x00;
                           (* CMOVE (% r9) (Memop Quadword (%% (rsp,1264))) *)
  0x4c; 0x0f; 0x44; 0x94; 0x24; 0xf8; 0x04; 0x00; 0x00;
                           (* CMOVE (% r10) (Memop Quadword (%% (rsp,1272))) *)
  0x4c; 0x0f; 0x44; 0x9c; 0x24; 0x00; 0x05; 0x00; 0x00;
                           (* CMOVE (% r11) (Memop Quadword (%% (rsp,1280))) *)
  0x4c; 0x0f; 0x44; 0xa4; 0x24; 0x08; 0x05; 0x00; 0x00;
                           (* CMOVE (% r12) (Memop Quadword (%% (rsp,1288))) *)
  0x48; 0x83; 0xff; 0x05;  (* CMP (% rdi) (Imm8 (word 5)) *)
  0x48; 0x0f; 0x44; 0x84; 0x24; 0xa0; 0x05; 0x00; 0x00;
                           (* CMOVE (% rax) (Memop Quadword (%% (rsp,1440))) *)
  0x48; 0x0f; 0x44; 0x9c; 0x24; 0xa8; 0x05; 0x00; 0x00;
                           (* CMOVE (% rbx) (Memop Quadword (%% (rsp,1448))) *)
  0x48; 0x0f; 0x44; 0x8c; 0x24; 0xb0; 0x05; 0x00; 0x00;
                           (* CMOVE (% rcx) (Memop Quadword (%% (rsp,1456))) *)
  0x48; 0x0f; 0x44; 0x94; 0x24; 0xb8; 0x05; 0x00; 0x00;
                           (* CMOVE (% rdx) (Memop Quadword (%% (rsp,1464))) *)
  0x4c; 0x0f; 0x44; 0x84; 0x24; 0xc0; 0x05; 0x00; 0x00;
                           (* CMOVE (% r8) (Memop Quadword (%% (rsp,1472))) *)
  0x4c; 0x0f; 0x44; 0x8c; 0x24; 0xc8; 0x05; 0x00; 0x00;
                           (* CMOVE (% r9) (Memop Quadword (%% (rsp,1480))) *)
  0x4c; 0x0f; 0x44; 0x94; 0x24; 0xd0; 0x05; 0x00; 0x00;
                           (* CMOVE (% r10) (Memop Quadword (%% (rsp,1488))) *)
  0x4c; 0x0f; 0x44; 0x9c; 0x24; 0xd8; 0x05; 0x00; 0x00;
                           (* CMOVE (% r11) (Memop Quadword (%% (rsp,1496))) *)
  0x4c; 0x0f; 0x44; 0xa4; 0x24; 0xe0; 0x05; 0x00; 0x00;
                           (* CMOVE (% r12) (Memop Quadword (%% (rsp,1504))) *)
  0x48; 0x83; 0xff; 0x06;  (* CMP (% rdi) (Imm8 (word 6)) *)
  0x48; 0x0f; 0x44; 0x84; 0x24; 0x78; 0x06; 0x00; 0x00;
                           (* CMOVE (% rax) (Memop Quadword (%% (rsp,1656))) *)
  0x48; 0x0f; 0x44; 0x9c; 0x24; 0x80; 0x06; 0x00; 0x00;
                           (* CMOVE (% rbx) (Memop Quadword (%% (rsp,1664))) *)
  0x48; 0x0f; 0x44; 0x8c; 0x24; 0x88; 0x06; 0x00; 0x00;
                           (* CMOVE (% rcx) (Memop Quadword (%% (rsp,1672))) *)
  0x48; 0x0f; 0x44; 0x94; 0x24; 0x90; 0x06; 0x00; 0x00;
                           (* CMOVE (% rdx) (Memop Quadword (%% (rsp,1680))) *)
  0x4c; 0x0f; 0x44; 0x84; 0x24; 0x98; 0x06; 0x00; 0x00;
                           (* CMOVE (% r8) (Memop Quadword (%% (rsp,1688))) *)
  0x4c; 0x0f; 0x44; 0x8c; 0x24; 0xa0; 0x06; 0x00; 0x00;
                           (* CMOVE (% r9) (Memop Quadword (%% (rsp,1696))) *)
  0x4c; 0x0f; 0x44; 0x94; 0x24; 0xa8; 0x06; 0x00; 0x00;
                           (* CMOVE (% r10) (Memop Quadword (%% (rsp,1704))) *)
  0x4c; 0x0f; 0x44; 0x9c; 0x24; 0xb0; 0x06; 0x00; 0x00;
                           (* CMOVE (% r11) (Memop Quadword (%% (rsp,1712))) *)
  0x4c; 0x0f; 0x44; 0xa4; 0x24; 0xb8; 0x06; 0x00; 0x00;
                           (* CMOVE (% r12) (Memop Quadword (%% (rsp,1720))) *)
  0x48; 0x83; 0xff; 0x07;  (* CMP (% rdi) (Imm8 (word 7)) *)
  0x48; 0x0f; 0x44; 0x84; 0x24; 0x50; 0x07; 0x00; 0x00;
                           (* CMOVE (% rax) (Memop Quadword (%% (rsp,1872))) *)
  0x48; 0x0f; 0x44; 0x9c; 0x24; 0x58; 0x07; 0x00; 0x00;
                           (* CMOVE (% rbx) (Memop Quadword (%% (rsp,1880))) *)
  0x48; 0x0f; 0x44; 0x8c; 0x24; 0x60; 0x07; 0x00; 0x00;
                           (* CMOVE (% rcx) (Memop Quadword (%% (rsp,1888))) *)
  0x48; 0x0f; 0x44; 0x94; 0x24; 0x68; 0x07; 0x00; 0x00;
                           (* CMOVE (% rdx) (Memop Quadword (%% (rsp,1896))) *)
  0x4c; 0x0f; 0x44; 0x84; 0x24; 0x70; 0x07; 0x00; 0x00;
                           (* CMOVE (% r8) (Memop Quadword (%% (rsp,1904))) *)
  0x4c; 0x0f; 0x44; 0x8c; 0x24; 0x78; 0x07; 0x00; 0x00;
                           (* CMOVE (% r9) (Memop Quadword (%% (rsp,1912))) *)
  0x4c; 0x0f; 0x44; 0x94; 0x24; 0x80; 0x07; 0x00; 0x00;
                           (* CMOVE (% r10) (Memop Quadword (%% (rsp,1920))) *)
  0x4c; 0x0f; 0x44; 0x9c; 0x24; 0x88; 0x07; 0x00; 0x00;
                           (* CMOVE (% r11) (Memop Quadword (%% (rsp,1928))) *)
  0x4c; 0x0f; 0x44; 0xa4; 0x24; 0x90; 0x07; 0x00; 0x00;
                           (* CMOVE (% r12) (Memop Quadword (%% (rsp,1936))) *)
  0x48; 0x83; 0xff; 0x08;  (* CMP (% rdi) (Imm8 (word 8)) *)
  0x48; 0x0f; 0x44; 0x84; 0x24; 0x28; 0x08; 0x00; 0x00;
                           (* CMOVE (% rax) (Memop Quadword (%% (rsp,2088))) *)
  0x48; 0x0f; 0x44; 0x9c; 0x24; 0x30; 0x08; 0x00; 0x00;
                           (* CMOVE (% rbx) (Memop Quadword (%% (rsp,2096))) *)
  0x48; 0x0f; 0x44; 0x8c; 0x24; 0x38; 0x08; 0x00; 0x00;
                           (* CMOVE (% rcx) (Memop Quadword (%% (rsp,2104))) *)
  0x48; 0x0f; 0x44; 0x94; 0x24; 0x40; 0x08; 0x00; 0x00;
                           (* CMOVE (% rdx) (Memop Quadword (%% (rsp,2112))) *)
  0x4c; 0x0f; 0x44; 0x84; 0x24; 0x48; 0x08; 0x00; 0x00;
                           (* CMOVE (% r8) (Memop Quadword (%% (rsp,2120))) *)
  0x4c; 0x0f; 0x44; 0x8c; 0x24; 0x50; 0x08; 0x00; 0x00;
                           (* CMOVE (% r9) (Memop Quadword (%% (rsp,2128))) *)
  0x4c; 0x0f; 0x44; 0x94; 0x24; 0x58; 0x08; 0x00; 0x00;
                           (* CMOVE (% r10) (Memop Quadword (%% (rsp,2136))) *)
  0x4c; 0x0f; 0x44; 0x9c; 0x24; 0x60; 0x08; 0x00; 0x00;
                           (* CMOVE (% r11) (Memop Quadword (%% (rsp,2144))) *)
  0x4c; 0x0f; 0x44; 0xa4; 0x24; 0x68; 0x08; 0x00; 0x00;
                           (* CMOVE (% r12) (Memop Quadword (%% (rsp,2152))) *)
  0x48; 0x83; 0xff; 0x09;  (* CMP (% rdi) (Imm8 (word 9)) *)
  0x48; 0x0f; 0x44; 0x84; 0x24; 0x00; 0x09; 0x00; 0x00;
                           (* CMOVE (% rax) (Memop Quadword (%% (rsp,2304))) *)
  0x48; 0x0f; 0x44; 0x9c; 0x24; 0x08; 0x09; 0x00; 0x00;
                           (* CMOVE (% rbx) (Memop Quadword (%% (rsp,2312))) *)
  0x48; 0x0f; 0x44; 0x8c; 0x24; 0x10; 0x09; 0x00; 0x00;
                           (* CMOVE (% rcx) (Memop Quadword (%% (rsp,2320))) *)
  0x48; 0x0f; 0x44; 0x94; 0x24; 0x18; 0x09; 0x00; 0x00;
                           (* CMOVE (% rdx) (Memop Quadword (%% (rsp,2328))) *)
  0x4c; 0x0f; 0x44; 0x84; 0x24; 0x20; 0x09; 0x00; 0x00;
                           (* CMOVE (% r8) (Memop Quadword (%% (rsp,2336))) *)
  0x4c; 0x0f; 0x44; 0x8c; 0x24; 0x28; 0x09; 0x00; 0x00;
                           (* CMOVE (% r9) (Memop Quadword (%% (rsp,2344))) *)
  0x4c; 0x0f; 0x44; 0x94; 0x24; 0x30; 0x09; 0x00; 0x00;
                           (* CMOVE (% r10) (Memop Quadword (%% (rsp,2352))) *)
  0x4c; 0x0f; 0x44; 0x9c; 0x24; 0x38; 0x09; 0x00; 0x00;
                           (* CMOVE (% r11) (Memop Quadword (%% (rsp,2360))) *)
  0x4c; 0x0f; 0x44; 0xa4; 0x24; 0x40; 0x09; 0x00; 0x00;
                           (* CMOVE (% r12) (Memop Quadword (%% (rsp,2368))) *)
  0x48; 0x83; 0xff; 0x0a;  (* CMP (% rdi) (Imm8 (word 10)) *)
  0x48; 0x0f; 0x44; 0x84; 0x24; 0xd8; 0x09; 0x00; 0x00;
                           (* CMOVE (% rax) (Memop Quadword (%% (rsp,2520))) *)
  0x48; 0x0f; 0x44; 0x9c; 0x24; 0xe0; 0x09; 0x00; 0x00;
                           (* CMOVE (% rbx) (Memop Quadword (%% (rsp,2528))) *)
  0x48; 0x0f; 0x44; 0x8c; 0x24; 0xe8; 0x09; 0x00; 0x00;
                           (* CMOVE (% rcx) (Memop Quadword (%% (rsp,2536))) *)
  0x48; 0x0f; 0x44; 0x94; 0x24; 0xf0; 0x09; 0x00; 0x00;
                           (* CMOVE (% rdx) (Memop Quadword (%% (rsp,2544))) *)
  0x4c; 0x0f; 0x44; 0x84; 0x24; 0xf8; 0x09; 0x00; 0x00;
                           (* CMOVE (% r8) (Memop Quadword (%% (rsp,2552))) *)
  0x4c; 0x0f; 0x44; 0x8c; 0x24; 0x00; 0x0a; 0x00; 0x00;
                           (* CMOVE (% r9) (Memop Quadword (%% (rsp,2560))) *)
  0x4c; 0x0f; 0x44; 0x94; 0x24; 0x08; 0x0a; 0x00; 0x00;
                           (* CMOVE (% r10) (Memop Quadword (%% (rsp,2568))) *)
  0x4c; 0x0f; 0x44; 0x9c; 0x24; 0x10; 0x0a; 0x00; 0x00;
                           (* CMOVE (% r11) (Memop Quadword (%% (rsp,2576))) *)
  0x4c; 0x0f; 0x44; 0xa4; 0x24; 0x18; 0x0a; 0x00; 0x00;
                           (* CMOVE (% r12) (Memop Quadword (%% (rsp,2584))) *)
  0x48; 0x83; 0xff; 0x0b;  (* CMP (% rdi) (Imm8 (word 11)) *)
  0x48; 0x0f; 0x44; 0x84; 0x24; 0xb0; 0x0a; 0x00; 0x00;
                           (* CMOVE (% rax) (Memop Quadword (%% (rsp,2736))) *)
  0x48; 0x0f; 0x44; 0x9c; 0x24; 0xb8; 0x0a; 0x00; 0x00;
                           (* CMOVE (% rbx) (Memop Quadword (%% (rsp,2744))) *)
  0x48; 0x0f; 0x44; 0x8c; 0x24; 0xc0; 0x0a; 0x00; 0x00;
                           (* CMOVE (% rcx) (Memop Quadword (%% (rsp,2752))) *)
  0x48; 0x0f; 0x44; 0x94; 0x24; 0xc8; 0x0a; 0x00; 0x00;
                           (* CMOVE (% rdx) (Memop Quadword (%% (rsp,2760))) *)
  0x4c; 0x0f; 0x44; 0x84; 0x24; 0xd0; 0x0a; 0x00; 0x00;
                           (* CMOVE (% r8) (Memop Quadword (%% (rsp,2768))) *)
  0x4c; 0x0f; 0x44; 0x8c; 0x24; 0xd8; 0x0a; 0x00; 0x00;
                           (* CMOVE (% r9) (Memop Quadword (%% (rsp,2776))) *)
  0x4c; 0x0f; 0x44; 0x94; 0x24; 0xe0; 0x0a; 0x00; 0x00;
                           (* CMOVE (% r10) (Memop Quadword (%% (rsp,2784))) *)
  0x4c; 0x0f; 0x44; 0x9c; 0x24; 0xe8; 0x0a; 0x00; 0x00;
                           (* CMOVE (% r11) (Memop Quadword (%% (rsp,2792))) *)
  0x4c; 0x0f; 0x44; 0xa4; 0x24; 0xf0; 0x0a; 0x00; 0x00;
                           (* CMOVE (% r12) (Memop Quadword (%% (rsp,2800))) *)
  0x48; 0x83; 0xff; 0x0c;  (* CMP (% rdi) (Imm8 (word 12)) *)
  0x48; 0x0f; 0x44; 0x84; 0x24; 0x88; 0x0b; 0x00; 0x00;
                           (* CMOVE (% rax) (Memop Quadword (%% (rsp,2952))) *)
  0x48; 0x0f; 0x44; 0x9c; 0x24; 0x90; 0x0b; 0x00; 0x00;
                           (* CMOVE (% rbx) (Memop Quadword (%% (rsp,2960))) *)
  0x48; 0x0f; 0x44; 0x8c; 0x24; 0x98; 0x0b; 0x00; 0x00;
                           (* CMOVE (% rcx) (Memop Quadword (%% (rsp,2968))) *)
  0x48; 0x0f; 0x44; 0x94; 0x24; 0xa0; 0x0b; 0x00; 0x00;
                           (* CMOVE (% rdx) (Memop Quadword (%% (rsp,2976))) *)
  0x4c; 0x0f; 0x44; 0x84; 0x24; 0xa8; 0x0b; 0x00; 0x00;
                           (* CMOVE (% r8) (Memop Quadword (%% (rsp,2984))) *)
  0x4c; 0x0f; 0x44; 0x8c; 0x24; 0xb0; 0x0b; 0x00; 0x00;
                           (* CMOVE (% r9) (Memop Quadword (%% (rsp,2992))) *)
  0x4c; 0x0f; 0x44; 0x94; 0x24; 0xb8; 0x0b; 0x00; 0x00;
                           (* CMOVE (% r10) (Memop Quadword (%% (rsp,3000))) *)
  0x4c; 0x0f; 0x44; 0x9c; 0x24; 0xc0; 0x0b; 0x00; 0x00;
                           (* CMOVE (% r11) (Memop Quadword (%% (rsp,3008))) *)
  0x4c; 0x0f; 0x44; 0xa4; 0x24; 0xc8; 0x0b; 0x00; 0x00;
                           (* CMOVE (% r12) (Memop Quadword (%% (rsp,3016))) *)
  0x48; 0x83; 0xff; 0x0d;  (* CMP (% rdi) (Imm8 (word 13)) *)
  0x48; 0x0f; 0x44; 0x84; 0x24; 0x60; 0x0c; 0x00; 0x00;
                           (* CMOVE (% rax) (Memop Quadword (%% (rsp,3168))) *)
  0x48; 0x0f; 0x44; 0x9c; 0x24; 0x68; 0x0c; 0x00; 0x00;
                           (* CMOVE (% rbx) (Memop Quadword (%% (rsp,3176))) *)
  0x48; 0x0f; 0x44; 0x8c; 0x24; 0x70; 0x0c; 0x00; 0x00;
                           (* CMOVE (% rcx) (Memop Quadword (%% (rsp,3184))) *)
  0x48; 0x0f; 0x44; 0x94; 0x24; 0x78; 0x0c; 0x00; 0x00;
                           (* CMOVE (% rdx) (Memop Quadword (%% (rsp,3192))) *)
  0x4c; 0x0f; 0x44; 0x84; 0x24; 0x80; 0x0c; 0x00; 0x00;
                           (* CMOVE (% r8) (Memop Quadword (%% (rsp,3200))) *)
  0x4c; 0x0f; 0x44; 0x8c; 0x24; 0x88; 0x0c; 0x00; 0x00;
                           (* CMOVE (% r9) (Memop Quadword (%% (rsp,3208))) *)
  0x4c; 0x0f; 0x44; 0x94; 0x24; 0x90; 0x0c; 0x00; 0x00;
                           (* CMOVE (% r10) (Memop Quadword (%% (rsp,3216))) *)
  0x4c; 0x0f; 0x44; 0x9c; 0x24; 0x98; 0x0c; 0x00; 0x00;
                           (* CMOVE (% r11) (Memop Quadword (%% (rsp,3224))) *)
  0x4c; 0x0f; 0x44; 0xa4; 0x24; 0xa0; 0x0c; 0x00; 0x00;
                           (* CMOVE (% r12) (Memop Quadword (%% (rsp,3232))) *)
  0x48; 0x83; 0xff; 0x0e;  (* CMP (% rdi) (Imm8 (word 14)) *)
  0x48; 0x0f; 0x44; 0x84; 0x24; 0x38; 0x0d; 0x00; 0x00;
                           (* CMOVE (% rax) (Memop Quadword (%% (rsp,3384))) *)
  0x48; 0x0f; 0x44; 0x9c; 0x24; 0x40; 0x0d; 0x00; 0x00;
                           (* CMOVE (% rbx) (Memop Quadword (%% (rsp,3392))) *)
  0x48; 0x0f; 0x44; 0x8c; 0x24; 0x48; 0x0d; 0x00; 0x00;
                           (* CMOVE (% rcx) (Memop Quadword (%% (rsp,3400))) *)
  0x48; 0x0f; 0x44; 0x94; 0x24; 0x50; 0x0d; 0x00; 0x00;
                           (* CMOVE (% rdx) (Memop Quadword (%% (rsp,3408))) *)
  0x4c; 0x0f; 0x44; 0x84; 0x24; 0x58; 0x0d; 0x00; 0x00;
                           (* CMOVE (% r8) (Memop Quadword (%% (rsp,3416))) *)
  0x4c; 0x0f; 0x44; 0x8c; 0x24; 0x60; 0x0d; 0x00; 0x00;
                           (* CMOVE (% r9) (Memop Quadword (%% (rsp,3424))) *)
  0x4c; 0x0f; 0x44; 0x94; 0x24; 0x68; 0x0d; 0x00; 0x00;
                           (* CMOVE (% r10) (Memop Quadword (%% (rsp,3432))) *)
  0x4c; 0x0f; 0x44; 0x9c; 0x24; 0x70; 0x0d; 0x00; 0x00;
                           (* CMOVE (% r11) (Memop Quadword (%% (rsp,3440))) *)
  0x4c; 0x0f; 0x44; 0xa4; 0x24; 0x78; 0x0d; 0x00; 0x00;
                           (* CMOVE (% r12) (Memop Quadword (%% (rsp,3448))) *)
  0x48; 0x83; 0xff; 0x0f;  (* CMP (% rdi) (Imm8 (word 15)) *)
  0x48; 0x0f; 0x44; 0x84; 0x24; 0x10; 0x0e; 0x00; 0x00;
                           (* CMOVE (% rax) (Memop Quadword (%% (rsp,3600))) *)
  0x48; 0x0f; 0x44; 0x9c; 0x24; 0x18; 0x0e; 0x00; 0x00;
                           (* CMOVE (% rbx) (Memop Quadword (%% (rsp,3608))) *)
  0x48; 0x0f; 0x44; 0x8c; 0x24; 0x20; 0x0e; 0x00; 0x00;
                           (* CMOVE (% rcx) (Memop Quadword (%% (rsp,3616))) *)
  0x48; 0x0f; 0x44; 0x94; 0x24; 0x28; 0x0e; 0x00; 0x00;
                           (* CMOVE (% rdx) (Memop Quadword (%% (rsp,3624))) *)
  0x4c; 0x0f; 0x44; 0x84; 0x24; 0x30; 0x0e; 0x00; 0x00;
                           (* CMOVE (% r8) (Memop Quadword (%% (rsp,3632))) *)
  0x4c; 0x0f; 0x44; 0x8c; 0x24; 0x38; 0x0e; 0x00; 0x00;
                           (* CMOVE (% r9) (Memop Quadword (%% (rsp,3640))) *)
  0x4c; 0x0f; 0x44; 0x94; 0x24; 0x40; 0x0e; 0x00; 0x00;
                           (* CMOVE (% r10) (Memop Quadword (%% (rsp,3648))) *)
  0x4c; 0x0f; 0x44; 0x9c; 0x24; 0x48; 0x0e; 0x00; 0x00;
                           (* CMOVE (% r11) (Memop Quadword (%% (rsp,3656))) *)
  0x4c; 0x0f; 0x44; 0xa4; 0x24; 0x50; 0x0e; 0x00; 0x00;
                           (* CMOVE (% r12) (Memop Quadword (%% (rsp,3664))) *)
  0x48; 0x83; 0xff; 0x10;  (* CMP (% rdi) (Imm8 (word 16)) *)
  0x48; 0x0f; 0x44; 0x84; 0x24; 0xe8; 0x0e; 0x00; 0x00;
                           (* CMOVE (% rax) (Memop Quadword (%% (rsp,3816))) *)
  0x48; 0x0f; 0x44; 0x9c; 0x24; 0xf0; 0x0e; 0x00; 0x00;
                           (* CMOVE (% rbx) (Memop Quadword (%% (rsp,3824))) *)
  0x48; 0x0f; 0x44; 0x8c; 0x24; 0xf8; 0x0e; 0x00; 0x00;
                           (* CMOVE (% rcx) (Memop Quadword (%% (rsp,3832))) *)
  0x48; 0x0f; 0x44; 0x94; 0x24; 0x00; 0x0f; 0x00; 0x00;
                           (* CMOVE (% rdx) (Memop Quadword (%% (rsp,3840))) *)
  0x4c; 0x0f; 0x44; 0x84; 0x24; 0x08; 0x0f; 0x00; 0x00;
                           (* CMOVE (% r8) (Memop Quadword (%% (rsp,3848))) *)
  0x4c; 0x0f; 0x44; 0x8c; 0x24; 0x10; 0x0f; 0x00; 0x00;
                           (* CMOVE (% r9) (Memop Quadword (%% (rsp,3856))) *)
  0x4c; 0x0f; 0x44; 0x94; 0x24; 0x18; 0x0f; 0x00; 0x00;
                           (* CMOVE (% r10) (Memop Quadword (%% (rsp,3864))) *)
  0x4c; 0x0f; 0x44; 0x9c; 0x24; 0x20; 0x0f; 0x00; 0x00;
                           (* CMOVE (% r11) (Memop Quadword (%% (rsp,3872))) *)
  0x4c; 0x0f; 0x44; 0xa4; 0x24; 0x28; 0x0f; 0x00; 0x00;
                           (* CMOVE (% r12) (Memop Quadword (%% (rsp,3880))) *)
  0x49; 0x89; 0xc5;        (* MOV (% r13) (% rax) *)
  0x49; 0x09; 0xdd;        (* OR (% r13) (% rbx) *)
  0x49; 0x89; 0xce;        (* MOV (% r14) (% rcx) *)
  0x49; 0x09; 0xd6;        (* OR (% r14) (% rdx) *)
  0x4d; 0x89; 0xc7;        (* MOV (% r15) (% r8) *)
  0x4d; 0x09; 0xcf;        (* OR (% r15) (% r9) *)
  0x4c; 0x89; 0xd7;        (* MOV (% rdi) (% r10) *)
  0x4c; 0x09; 0xdf;        (* OR (% rdi) (% r11) *)
  0x4d; 0x09; 0xf5;        (* OR (% r13) (% r14) *)
  0x49; 0x09; 0xff;        (* OR (% r15) (% rdi) *)
  0x4d; 0x09; 0xe7;        (* OR (% r15) (% r12) *)
  0x4d; 0x09; 0xfd;        (* OR (% r13) (% r15) *)
  0x49; 0x0f; 0x44; 0xf5;  (* CMOVE (% rsi) (% r13) *)
  0x48; 0x31; 0xf0;        (* XOR (% rax) (% rsi) *)
  0x48; 0x31; 0xf3;        (* XOR (% rbx) (% rsi) *)
  0x48; 0x31; 0xf1;        (* XOR (% rcx) (% rsi) *)
  0x48; 0x31; 0xf2;        (* XOR (% rdx) (% rsi) *)
  0x49; 0x31; 0xf0;        (* XOR (% r8) (% rsi) *)
  0x49; 0x31; 0xf1;        (* XOR (% r9) (% rsi) *)
  0x49; 0x31; 0xf2;        (* XOR (% r10) (% rsi) *)
  0x49; 0x31; 0xf3;        (* XOR (% r11) (% rsi) *)
  0x48; 0x81; 0xe6; 0xff; 0x01; 0x00; 0x00;
                           (* AND (% rsi) (Imm32 (word 511)) *)
  0x49; 0x31; 0xf4;        (* XOR (% r12) (% rsi) *)
  0x48; 0x89; 0x84; 0x24; 0x68; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,360))) (% rax) *)
  0x48; 0x89; 0x9c; 0x24; 0x70; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,368))) (% rbx) *)
  0x48; 0x89; 0x8c; 0x24; 0x78; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,376))) (% rcx) *)
  0x48; 0x89; 0x94; 0x24; 0x80; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,384))) (% rdx) *)
  0x4c; 0x89; 0x84; 0x24; 0x88; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,392))) (% r8) *)
  0x4c; 0x89; 0x8c; 0x24; 0x90; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,400))) (% r9) *)
  0x4c; 0x89; 0x94; 0x24; 0x98; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,408))) (% r10) *)
  0x4c; 0x89; 0x9c; 0x24; 0xa0; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,416))) (% r11) *)
  0x4c; 0x89; 0xa4; 0x24; 0xa8; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,424))) (% r12) *)
  0x48; 0x8d; 0x94; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* LEA (% rdx) (%% (rsp,288)) *)
  0x48; 0x8d; 0x74; 0x24; 0x48;
                           (* LEA (% rsi) (%% (rsp,72)) *)
  0x48; 0x8d; 0x7c; 0x24; 0x48;
                           (* LEA (% rdi) (%% (rsp,72)) *)
  0xe8; 0x45; 0x03; 0x00; 0x00;
                           (* CALL (Imm32 (word 837)) *)
  0x48; 0x85; 0xed;        (* TEST (% rbp) (% rbp) *)
  0x0f; 0x85; 0xa2; 0xed; 0xff; 0xff;
                           (* JNE (Imm32 (word 4294962594)) *)
  0x48; 0x8b; 0xbc; 0x24; 0x78; 0x0f; 0x00; 0x00;
                           (* MOV (% rdi) (Memop Quadword (%% (rsp,3960))) *)
  0x48; 0x8b; 0x44; 0x24; 0x48;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,72))) *)
  0x48; 0x89; 0x07;        (* MOV (Memop Quadword (%% (rdi,0))) (% rax) *)
  0x48; 0x8b; 0x44; 0x24; 0x50;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,80))) *)
  0x48; 0x89; 0x47; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% rax) *)
  0x48; 0x8b; 0x44; 0x24; 0x58;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,88))) *)
  0x48; 0x89; 0x47; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% rax) *)
  0x48; 0x8b; 0x44; 0x24; 0x60;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,96))) *)
  0x48; 0x89; 0x47; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% rax) *)
  0x48; 0x8b; 0x44; 0x24; 0x68;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,104))) *)
  0x48; 0x89; 0x47; 0x20;  (* MOV (Memop Quadword (%% (rdi,32))) (% rax) *)
  0x48; 0x8b; 0x44; 0x24; 0x70;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,112))) *)
  0x48; 0x89; 0x47; 0x28;  (* MOV (Memop Quadword (%% (rdi,40))) (% rax) *)
  0x48; 0x8b; 0x44; 0x24; 0x78;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,120))) *)
  0x48; 0x89; 0x47; 0x30;  (* MOV (Memop Quadword (%% (rdi,48))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,128))) *)
  0x48; 0x89; 0x47; 0x38;  (* MOV (Memop Quadword (%% (rdi,56))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,136))) *)
  0x48; 0x89; 0x47; 0x40;  (* MOV (Memop Quadword (%% (rdi,64))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,144))) *)
  0x48; 0x89; 0x47; 0x48;  (* MOV (Memop Quadword (%% (rdi,72))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,152))) *)
  0x48; 0x89; 0x47; 0x50;  (* MOV (Memop Quadword (%% (rdi,80))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,160))) *)
  0x48; 0x89; 0x47; 0x58;  (* MOV (Memop Quadword (%% (rdi,88))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,168))) *)
  0x48; 0x89; 0x47; 0x60;  (* MOV (Memop Quadword (%% (rdi,96))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,176))) *)
  0x48; 0x89; 0x47; 0x68;  (* MOV (Memop Quadword (%% (rdi,104))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,184))) *)
  0x48; 0x89; 0x47; 0x70;  (* MOV (Memop Quadword (%% (rdi,112))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,192))) *)
  0x48; 0x89; 0x47; 0x78;  (* MOV (Memop Quadword (%% (rdi,120))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0xc8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,200))) *)
  0x48; 0x89; 0x87; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,128))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0xd0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,208))) *)
  0x48; 0x89; 0x87; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,136))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0xd8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,216))) *)
  0x48; 0x89; 0x87; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,144))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0xe0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,224))) *)
  0x48; 0x89; 0x87; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,152))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0xe8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,232))) *)
  0x48; 0x89; 0x87; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,160))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0xf0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,240))) *)
  0x48; 0x89; 0x87; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,168))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0xf8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,248))) *)
  0x48; 0x89; 0x87; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,176))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x00; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,256))) *)
  0x48; 0x89; 0x87; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,184))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x08; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,264))) *)
  0x48; 0x89; 0x87; 0xc0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,192))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x10; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,272))) *)
  0x48; 0x89; 0x87; 0xc8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,200))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x18; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,280))) *)
  0x48; 0x89; 0x87; 0xd0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,208))) (% rax) *)
  0x48; 0x81; 0xc4; 0xc0; 0x0f; 0x00; 0x00;
                           (* ADD (% rsp) (Imm32 (word 4032)) *)
  0x5b;                    (* POP (% rbx) *)
  0x5d;                    (* POP (% rbp) *)
  0x41; 0x5c;              (* POP (% r12) *)
  0x41; 0x5d;              (* POP (% r13) *)
  0x41; 0x5e;              (* POP (% r14) *)
  0x41; 0x5f;              (* POP (% r15) *)
  0xc3;                    (* RET *)
  0x53;                    (* PUSH (% rbx) *)
  0x48; 0x8b; 0x46; 0x40;  (* MOV (% rax) (Memop Quadword (%% (rsi,64))) *)
  0xba; 0xff; 0x01; 0x00; 0x00;
                           (* MOV (% edx) (Imm32 (word 511)) *)
  0x48; 0x21; 0xc2;        (* AND (% rdx) (% rax) *)
  0x48; 0xc1; 0xe8; 0x09;  (* SHR (% rax) (Imm8 (word 9)) *)
  0xf9;                    (* STCF *)
  0x48; 0x13; 0x06;        (* ADC (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0x8b; 0x4e; 0x08;  (* MOV (% rcx) (Memop Quadword (%% (rsi,8))) *)
  0x48; 0x83; 0xd1; 0x00;  (* ADC (% rcx) (Imm8 (word 0)) *)
  0x4c; 0x8b; 0x46; 0x10;  (* MOV (% r8) (Memop Quadword (%% (rsi,16))) *)
  0x49; 0x83; 0xd0; 0x00;  (* ADC (% r8) (Imm8 (word 0)) *)
  0x4c; 0x8b; 0x4e; 0x18;  (* MOV (% r9) (Memop Quadword (%% (rsi,24))) *)
  0x49; 0x83; 0xd1; 0x00;  (* ADC (% r9) (Imm8 (word 0)) *)
  0x4c; 0x8b; 0x56; 0x20;  (* MOV (% r10) (Memop Quadword (%% (rsi,32))) *)
  0x49; 0x83; 0xd2; 0x00;  (* ADC (% r10) (Imm8 (word 0)) *)
  0x4c; 0x8b; 0x5e; 0x28;  (* MOV (% r11) (Memop Quadword (%% (rsi,40))) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x5e; 0x30;  (* MOV (% rbx) (Memop Quadword (%% (rsi,48))) *)
  0x48; 0x83; 0xd3; 0x00;  (* ADC (% rbx) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x76; 0x38;  (* MOV (% rsi) (Memop Quadword (%% (rsi,56))) *)
  0x48; 0x83; 0xd6; 0x00;  (* ADC (% rsi) (Imm8 (word 0)) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x48; 0x81; 0xfa; 0x00; 0x02; 0x00; 0x00;
                           (* CMP (% rdx) (Imm32 (word 512)) *)
  0x48; 0x83; 0xd8; 0x00;  (* SBB (% rax) (Imm8 (word 0)) *)
  0x48; 0x89; 0x07;        (* MOV (Memop Quadword (%% (rdi,0))) (% rax) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x48; 0x89; 0x4f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% rcx) *)
  0x49; 0x83; 0xd8; 0x00;  (* SBB (% r8) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x47; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r8) *)
  0x49; 0x83; 0xd9; 0x00;  (* SBB (% r9) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x4f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r9) *)
  0x49; 0x83; 0xda; 0x00;  (* SBB (% r10) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x57; 0x20;  (* MOV (Memop Quadword (%% (rdi,32))) (% r10) *)
  0x49; 0x83; 0xdb; 0x00;  (* SBB (% r11) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x5f; 0x28;  (* MOV (Memop Quadword (%% (rdi,40))) (% r11) *)
  0x48; 0x83; 0xdb; 0x00;  (* SBB (% rbx) (Imm8 (word 0)) *)
  0x48; 0x89; 0x5f; 0x30;  (* MOV (Memop Quadword (%% (rdi,48))) (% rbx) *)
  0x48; 0x83; 0xde; 0x00;  (* SBB (% rsi) (Imm8 (word 0)) *)
  0x48; 0x89; 0x77; 0x38;  (* MOV (Memop Quadword (%% (rdi,56))) (% rsi) *)
  0x48; 0x83; 0xda; 0x00;  (* SBB (% rdx) (Imm8 (word 0)) *)
  0x48; 0x81; 0xe2; 0xff; 0x01; 0x00; 0x00;
                           (* AND (% rdx) (Imm32 (word 511)) *)
  0x48; 0x89; 0x57; 0x40;  (* MOV (Memop Quadword (%% (rdi,64))) (% rdx) *)
  0x5b;                    (* POP (% rbx) *)
  0xc3;                    (* RET *)
  0x48; 0x8b; 0x4e; 0x40;  (* MOV (% rcx) (Memop Quadword (%% (rsi,64))) *)
  0x48; 0xc7; 0xc0; 0x00; 0xfe; 0xff; 0xff;
                           (* MOV (% rax) (Imm32 (word 4294966784)) *)
  0x48; 0x09; 0xc8;        (* OR (% rax) (% rcx) *)
  0x48; 0x89; 0x47; 0x40;  (* MOV (Memop Quadword (%% (rdi,64))) (% rax) *)
  0x48; 0xc1; 0xe9; 0x09;  (* SHR (% rcx) (Imm8 (word 9)) *)
  0x48; 0x83; 0xc1; 0x01;  (* ADD (% rcx) (Imm8 (word 1)) *)
  0x48; 0xb8; 0xf7; 0x9b; 0xc7; 0x6e; 0xe1; 0x48; 0x90; 0x44;
                           (* MOV (% rax) (Imm64 (word 4940528924288850935)) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x48; 0xb8; 0x51; 0xb8; 0x63; 0x76; 0x47; 0x36; 0x4a; 0xc4;
                           (* MOV (% rax) (Imm64 (word 14144177260267288657)) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0xb8; 0x2f; 0x5a; 0xf6; 0x08; 0xb7; 0xfe; 0x33; 0x80;
                           (* MOV (% rax) (Imm64 (word 9238007322749852207)) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0xb8; 0x94; 0x69; 0xd0; 0x40; 0x7c; 0x78; 0x79; 0xae;
                           (* MOV (% rax) (Imm64 (word 12572212309840128404)) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x48; 0x6b; 0xc9; 0x05;  (* IMUL3 (% rcx) (% rcx,Imm8 (word 5)) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x48; 0x11; 0xd1;        (* ADC (% rcx) (% rdx) *)
  0x48; 0x19; 0xd2;        (* SBB (% rdx) (% rdx) *)
  0x48; 0xf7; 0xda;        (* NEG (% rdx) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0x4c; 0x03; 0x06;        (* ADD (% r8) (Memop Quadword (%% (rsi,0))) *)
  0x4c; 0x89; 0x07;        (* MOV (Memop Quadword (%% (rdi,0))) (% r8) *)
  0x4c; 0x13; 0x4e; 0x08;  (* ADC (% r9) (Memop Quadword (%% (rsi,8))) *)
  0x4c; 0x89; 0x4f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% r9) *)
  0x4c; 0x13; 0x56; 0x10;  (* ADC (% r10) (Memop Quadword (%% (rsi,16))) *)
  0x4c; 0x89; 0x57; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r10) *)
  0x4c; 0x13; 0x5e; 0x18;  (* ADC (% r11) (Memop Quadword (%% (rsi,24))) *)
  0x4c; 0x89; 0x5f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r11) *)
  0x48; 0x13; 0x4e; 0x20;  (* ADC (% rcx) (Memop Quadword (%% (rsi,32))) *)
  0x48; 0x89; 0x4f; 0x20;  (* MOV (Memop Quadword (%% (rdi,32))) (% rcx) *)
  0x48; 0x13; 0x56; 0x28;  (* ADC (% rdx) (Memop Quadword (%% (rsi,40))) *)
  0x48; 0x89; 0x57; 0x28;  (* MOV (Memop Quadword (%% (rdi,40))) (% rdx) *)
  0x48; 0x8b; 0x56; 0x30;  (* MOV (% rdx) (Memop Quadword (%% (rsi,48))) *)
  0x48; 0x11; 0xc2;        (* ADC (% rdx) (% rax) *)
  0x48; 0x89; 0x57; 0x30;  (* MOV (Memop Quadword (%% (rdi,48))) (% rdx) *)
  0x48; 0x8b; 0x56; 0x38;  (* MOV (% rdx) (Memop Quadword (%% (rsi,56))) *)
  0x48; 0x11; 0xc2;        (* ADC (% rdx) (% rax) *)
  0x48; 0x89; 0x57; 0x38;  (* MOV (Memop Quadword (%% (rdi,56))) (% rdx) *)
  0x48; 0x8b; 0x4f; 0x40;  (* MOV (% rcx) (Memop Quadword (%% (rdi,64))) *)
  0x48; 0x11; 0xc1;        (* ADC (% rcx) (% rax) *)
  0xf5;                    (* CMC *)
  0x48; 0x19; 0xd2;        (* SBB (% rdx) (% rdx) *)
  0x49; 0xb8; 0xf7; 0x9b; 0xc7; 0x6e; 0xe1; 0x48; 0x90; 0x44;
                           (* MOV (% r8) (Imm64 (word 4940528924288850935)) *)
  0x49; 0x21; 0xd0;        (* AND (% r8) (% rdx) *)
  0x49; 0xb9; 0x51; 0xb8; 0x63; 0x76; 0x47; 0x36; 0x4a; 0xc4;
                           (* MOV (% r9) (Imm64 (word 14144177260267288657)) *)
  0x49; 0x21; 0xd1;        (* AND (% r9) (% rdx) *)
  0x49; 0xba; 0x2f; 0x5a; 0xf6; 0x08; 0xb7; 0xfe; 0x33; 0x80;
                           (* MOV (% r10) (Imm64 (word 9238007322749852207)) *)
  0x49; 0x21; 0xd2;        (* AND (% r10) (% rdx) *)
  0x49; 0xbb; 0x94; 0x69; 0xd0; 0x40; 0x7c; 0x78; 0x79; 0xae;
                           (* MOV (% r11) (Imm64 (word 12572212309840128404)) *)
  0x49; 0x21; 0xd3;        (* AND (% r11) (% rdx) *)
  0x48; 0x83; 0xe2; 0x05;  (* AND (% rdx) (Imm8 (word 5)) *)
  0x4c; 0x29; 0x07;        (* SUB (Memop Quadword (%% (rdi,0))) (% r8) *)
  0x4c; 0x19; 0x4f; 0x08;  (* SBB (Memop Quadword (%% (rdi,8))) (% r9) *)
  0x4c; 0x19; 0x57; 0x10;  (* SBB (Memop Quadword (%% (rdi,16))) (% r10) *)
  0x4c; 0x19; 0x5f; 0x18;  (* SBB (Memop Quadword (%% (rdi,24))) (% r11) *)
  0x48; 0x19; 0x57; 0x20;  (* SBB (Memop Quadword (%% (rdi,32))) (% rdx) *)
  0x48; 0x19; 0x47; 0x28;  (* SBB (Memop Quadword (%% (rdi,40))) (% rax) *)
  0x48; 0x19; 0x47; 0x30;  (* SBB (Memop Quadword (%% (rdi,48))) (% rax) *)
  0x48; 0x19; 0x47; 0x38;  (* SBB (Memop Quadword (%% (rdi,56))) (% rax) *)
  0x19; 0xc1;              (* SBB (% ecx) (% eax) *)
  0x81; 0xe1; 0xff; 0x01; 0x00; 0x00;
                           (* AND (% ecx) (Imm32 (word 511)) *)
  0x48; 0x89; 0x4f; 0x40;  (* MOV (Memop Quadword (%% (rdi,64))) (% rcx) *)
  0xc3;                    (* RET *)
  0x53;                    (* PUSH (% rbx) *)
  0x55;                    (* PUSH (% rbp) *)
  0x41; 0x54;              (* PUSH (% r12) *)
  0x41; 0x55;              (* PUSH (% r13) *)
  0x41; 0x56;              (* PUSH (% r14) *)
  0x41; 0x57;              (* PUSH (% r15) *)
  0x48; 0x81; 0xec; 0x10; 0x02; 0x00; 0x00;
                           (* SUB (% rsp) (Imm32 (word 528)) *)
  0x48; 0x89; 0xbc; 0x24; 0xf8; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,504))) (% rdi) *)
  0x48; 0x89; 0xb4; 0x24; 0x00; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,512))) (% rsi) *)
  0x48; 0x89; 0x94; 0x24; 0x08; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,520))) (% rdx) *)
  0x48; 0x8b; 0xb4; 0x24; 0x00; 0x02; 0x00; 0x00;
                           (* MOV (% rsi) (Memop Quadword (%% (rsp,512))) *)
  0x48; 0x8d; 0xb6; 0x90; 0x00; 0x00; 0x00;
                           (* LEA (% rsi) (%% (rsi,144)) *)
  0x48; 0x8d; 0x3c; 0x24;  (* LEA (% rdi) (%% (rsp,0)) *)
  0xe8; 0x35; 0x1e; 0x00; 0x00;
                           (* CALL (Imm32 (word 7733)) *)
  0x48; 0x8b; 0xbc; 0x24; 0x08; 0x02; 0x00; 0x00;
                           (* MOV (% rdi) (Memop Quadword (%% (rsp,520))) *)
  0x48; 0x8d; 0xb7; 0x90; 0x00; 0x00; 0x00;
                           (* LEA (% rsi) (%% (rdi,144)) *)
  0x48; 0x8d; 0xbc; 0x24; 0x68; 0x01; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rsp,360)) *)
  0xe8; 0x19; 0x1e; 0x00; 0x00;
                           (* CALL (Imm32 (word 7705)) *)
  0x48; 0x8b; 0xb4; 0x24; 0x00; 0x02; 0x00; 0x00;
                           (* MOV (% rsi) (Memop Quadword (%% (rsp,512))) *)
  0x48; 0x8b; 0xbc; 0x24; 0x08; 0x02; 0x00; 0x00;
                           (* MOV (% rdi) (Memop Quadword (%% (rsp,520))) *)
  0x48; 0x8d; 0x56; 0x48;  (* LEA (% rdx) (%% (rsi,72)) *)
  0x48; 0x8d; 0xb7; 0x90; 0x00; 0x00; 0x00;
                           (* LEA (% rsi) (%% (rdi,144)) *)
  0x48; 0x8d; 0xbc; 0x24; 0xb0; 0x01; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rsp,432)) *)
  0xe8; 0x57; 0x17; 0x00; 0x00;
                           (* CALL (Imm32 (word 5975)) *)
  0x48; 0x8b; 0xb4; 0x24; 0x00; 0x02; 0x00; 0x00;
                           (* MOV (% rsi) (Memop Quadword (%% (rsp,512))) *)
  0x48; 0x8b; 0xbc; 0x24; 0x08; 0x02; 0x00; 0x00;
                           (* MOV (% rdi) (Memop Quadword (%% (rsp,520))) *)
  0x48; 0x8d; 0x57; 0x48;  (* LEA (% rdx) (%% (rdi,72)) *)
  0x48; 0x8d; 0xb6; 0x90; 0x00; 0x00; 0x00;
                           (* LEA (% rsi) (%% (rsi,144)) *)
  0x48; 0x8d; 0x7c; 0x24; 0x48;
                           (* LEA (% rdi) (%% (rsp,72)) *)
  0xe8; 0x32; 0x17; 0x00; 0x00;
                           (* CALL (Imm32 (word 5938)) *)
  0x48; 0x8b; 0xbc; 0x24; 0x08; 0x02; 0x00; 0x00;
                           (* MOV (% rdi) (Memop Quadword (%% (rsp,520))) *)
  0x48; 0x8d; 0x17;        (* LEA (% rdx) (%% (rdi,0)) *)
  0x48; 0x8d; 0x34; 0x24;  (* LEA (% rsi) (%% (rsp,0)) *)
  0x48; 0x8d; 0xbc; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rsp,144)) *)
  0xe8; 0x16; 0x17; 0x00; 0x00;
                           (* CALL (Imm32 (word 5910)) *)
  0x48; 0x8b; 0xb4; 0x24; 0x00; 0x02; 0x00; 0x00;
                           (* MOV (% rsi) (Memop Quadword (%% (rsp,512))) *)
  0x48; 0x8d; 0x16;        (* LEA (% rdx) (%% (rsi,0)) *)
  0x48; 0x8d; 0xb4; 0x24; 0x68; 0x01; 0x00; 0x00;
                           (* LEA (% rsi) (%% (rsp,360)) *)
  0x48; 0x8d; 0xbc; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rsp,288)) *)
  0xe8; 0xf6; 0x16; 0x00; 0x00;
                           (* CALL (Imm32 (word 5878)) *)
  0x48; 0x8d; 0x54; 0x24; 0x48;
                           (* LEA (% rdx) (%% (rsp,72)) *)
  0x48; 0x8d; 0x34; 0x24;  (* LEA (% rsi) (%% (rsp,0)) *)
  0x48; 0x8d; 0x7c; 0x24; 0x48;
                           (* LEA (% rdi) (%% (rsp,72)) *)
  0xe8; 0xe3; 0x16; 0x00; 0x00;
                           (* CALL (Imm32 (word 5859)) *)
  0x48; 0x8d; 0x94; 0x24; 0xb0; 0x01; 0x00; 0x00;
                           (* LEA (% rdx) (%% (rsp,432)) *)
  0x48; 0x8d; 0xb4; 0x24; 0x68; 0x01; 0x00; 0x00;
                           (* LEA (% rsi) (%% (rsp,360)) *)
  0x48; 0x8d; 0xbc; 0x24; 0xb0; 0x01; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rsp,432)) *)
  0xe8; 0xc6; 0x16; 0x00; 0x00;
                           (* CALL (Imm32 (word 5830)) *)
  0x48; 0x8b; 0x84; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,144))) *)
  0x48; 0x2b; 0x84; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* SUB (% rax) (Memop Quadword (%% (rsp,288))) *)
  0x48; 0x8b; 0x94; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,152))) *)
  0x48; 0x1b; 0x94; 0x24; 0x28; 0x01; 0x00; 0x00;
                           (* SBB (% rdx) (Memop Quadword (%% (rsp,296))) *)
  0x4c; 0x8b; 0x84; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,160))) *)
  0x4c; 0x1b; 0x84; 0x24; 0x30; 0x01; 0x00; 0x00;
                           (* SBB (% r8) (Memop Quadword (%% (rsp,304))) *)
  0x4c; 0x8b; 0x8c; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,168))) *)
  0x4c; 0x1b; 0x8c; 0x24; 0x38; 0x01; 0x00; 0x00;
                           (* SBB (% r9) (Memop Quadword (%% (rsp,312))) *)
  0x4c; 0x8b; 0x94; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (% r10) (Memop Quadword (%% (rsp,176))) *)
  0x4c; 0x1b; 0x94; 0x24; 0x40; 0x01; 0x00; 0x00;
                           (* SBB (% r10) (Memop Quadword (%% (rsp,320))) *)
  0x4c; 0x8b; 0x9c; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (% r11) (Memop Quadword (%% (rsp,184))) *)
  0x4c; 0x1b; 0x9c; 0x24; 0x48; 0x01; 0x00; 0x00;
                           (* SBB (% r11) (Memop Quadword (%% (rsp,328))) *)
  0x4c; 0x8b; 0xa4; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* MOV (% r12) (Memop Quadword (%% (rsp,192))) *)
  0x4c; 0x1b; 0xa4; 0x24; 0x50; 0x01; 0x00; 0x00;
                           (* SBB (% r12) (Memop Quadword (%% (rsp,336))) *)
  0x4c; 0x8b; 0xac; 0x24; 0xc8; 0x00; 0x00; 0x00;
                           (* MOV (% r13) (Memop Quadword (%% (rsp,200))) *)
  0x4c; 0x1b; 0xac; 0x24; 0x58; 0x01; 0x00; 0x00;
                           (* SBB (% r13) (Memop Quadword (%% (rsp,344))) *)
  0x4c; 0x8b; 0xb4; 0x24; 0xd0; 0x00; 0x00; 0x00;
                           (* MOV (% r14) (Memop Quadword (%% (rsp,208))) *)
  0x4c; 0x1b; 0xb4; 0x24; 0x60; 0x01; 0x00; 0x00;
                           (* SBB (% r14) (Memop Quadword (%% (rsp,352))) *)
  0x48; 0x83; 0xd8; 0x00;  (* SBB (% rax) (Imm8 (word 0)) *)
  0x48; 0x89; 0x84; 0x24; 0x68; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,360))) (% rax) *)
  0x48; 0x83; 0xda; 0x00;  (* SBB (% rdx) (Imm8 (word 0)) *)
  0x48; 0x89; 0x94; 0x24; 0x70; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,368))) (% rdx) *)
  0x49; 0x83; 0xd8; 0x00;  (* SBB (% r8) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x84; 0x24; 0x78; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,376))) (% r8) *)
  0x49; 0x83; 0xd9; 0x00;  (* SBB (% r9) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x8c; 0x24; 0x80; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,384))) (% r9) *)
  0x49; 0x83; 0xda; 0x00;  (* SBB (% r10) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x94; 0x24; 0x88; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,392))) (% r10) *)
  0x49; 0x83; 0xdb; 0x00;  (* SBB (% r11) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x9c; 0x24; 0x90; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,400))) (% r11) *)
  0x49; 0x83; 0xdc; 0x00;  (* SBB (% r12) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xa4; 0x24; 0x98; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,408))) (% r12) *)
  0x49; 0x83; 0xdd; 0x00;  (* SBB (% r13) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xac; 0x24; 0xa0; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,416))) (% r13) *)
  0x49; 0x83; 0xde; 0x00;  (* SBB (% r14) (Imm8 (word 0)) *)
  0x49; 0x81; 0xe6; 0xff; 0x01; 0x00; 0x00;
                           (* AND (% r14) (Imm32 (word 511)) *)
  0x4c; 0x89; 0xb4; 0x24; 0xa8; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,424))) (% r14) *)
  0x48; 0x8b; 0x44; 0x24; 0x48;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,72))) *)
  0x48; 0x2b; 0x84; 0x24; 0xb0; 0x01; 0x00; 0x00;
                           (* SUB (% rax) (Memop Quadword (%% (rsp,432))) *)
  0x48; 0x8b; 0x54; 0x24; 0x50;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,80))) *)
  0x48; 0x1b; 0x94; 0x24; 0xb8; 0x01; 0x00; 0x00;
                           (* SBB (% rdx) (Memop Quadword (%% (rsp,440))) *)
  0x4c; 0x8b; 0x44; 0x24; 0x58;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,88))) *)
  0x4c; 0x1b; 0x84; 0x24; 0xc0; 0x01; 0x00; 0x00;
                           (* SBB (% r8) (Memop Quadword (%% (rsp,448))) *)
  0x4c; 0x8b; 0x4c; 0x24; 0x60;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,96))) *)
  0x4c; 0x1b; 0x8c; 0x24; 0xc8; 0x01; 0x00; 0x00;
                           (* SBB (% r9) (Memop Quadword (%% (rsp,456))) *)
  0x4c; 0x8b; 0x54; 0x24; 0x68;
                           (* MOV (% r10) (Memop Quadword (%% (rsp,104))) *)
  0x4c; 0x1b; 0x94; 0x24; 0xd0; 0x01; 0x00; 0x00;
                           (* SBB (% r10) (Memop Quadword (%% (rsp,464))) *)
  0x4c; 0x8b; 0x5c; 0x24; 0x70;
                           (* MOV (% r11) (Memop Quadword (%% (rsp,112))) *)
  0x4c; 0x1b; 0x9c; 0x24; 0xd8; 0x01; 0x00; 0x00;
                           (* SBB (% r11) (Memop Quadword (%% (rsp,472))) *)
  0x4c; 0x8b; 0x64; 0x24; 0x78;
                           (* MOV (% r12) (Memop Quadword (%% (rsp,120))) *)
  0x4c; 0x1b; 0xa4; 0x24; 0xe0; 0x01; 0x00; 0x00;
                           (* SBB (% r12) (Memop Quadword (%% (rsp,480))) *)
  0x4c; 0x8b; 0xac; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (% r13) (Memop Quadword (%% (rsp,128))) *)
  0x4c; 0x1b; 0xac; 0x24; 0xe8; 0x01; 0x00; 0x00;
                           (* SBB (% r13) (Memop Quadword (%% (rsp,488))) *)
  0x4c; 0x8b; 0xb4; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (% r14) (Memop Quadword (%% (rsp,136))) *)
  0x4c; 0x1b; 0xb4; 0x24; 0xf0; 0x01; 0x00; 0x00;
                           (* SBB (% r14) (Memop Quadword (%% (rsp,496))) *)
  0x48; 0x83; 0xd8; 0x00;  (* SBB (% rax) (Imm8 (word 0)) *)
  0x48; 0x89; 0x44; 0x24; 0x48;
                           (* MOV (Memop Quadword (%% (rsp,72))) (% rax) *)
  0x48; 0x83; 0xda; 0x00;  (* SBB (% rdx) (Imm8 (word 0)) *)
  0x48; 0x89; 0x54; 0x24; 0x50;
                           (* MOV (Memop Quadword (%% (rsp,80))) (% rdx) *)
  0x49; 0x83; 0xd8; 0x00;  (* SBB (% r8) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x44; 0x24; 0x58;
                           (* MOV (Memop Quadword (%% (rsp,88))) (% r8) *)
  0x49; 0x83; 0xd9; 0x00;  (* SBB (% r9) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x4c; 0x24; 0x60;
                           (* MOV (Memop Quadword (%% (rsp,96))) (% r9) *)
  0x49; 0x83; 0xda; 0x00;  (* SBB (% r10) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x54; 0x24; 0x68;
                           (* MOV (Memop Quadword (%% (rsp,104))) (% r10) *)
  0x49; 0x83; 0xdb; 0x00;  (* SBB (% r11) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x5c; 0x24; 0x70;
                           (* MOV (Memop Quadword (%% (rsp,112))) (% r11) *)
  0x49; 0x83; 0xdc; 0x00;  (* SBB (% r12) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x64; 0x24; 0x78;
                           (* MOV (Memop Quadword (%% (rsp,120))) (% r12) *)
  0x49; 0x83; 0xdd; 0x00;  (* SBB (% r13) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xac; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,128))) (% r13) *)
  0x49; 0x83; 0xde; 0x00;  (* SBB (% r14) (Imm8 (word 0)) *)
  0x49; 0x81; 0xe6; 0xff; 0x01; 0x00; 0x00;
                           (* AND (% r14) (Imm32 (word 511)) *)
  0x4c; 0x89; 0xb4; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,136))) (% r14) *)
  0x48; 0x8d; 0xb4; 0x24; 0x68; 0x01; 0x00; 0x00;
                           (* LEA (% rsi) (%% (rsp,360)) *)
  0x48; 0x8d; 0xbc; 0x24; 0xd8; 0x00; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rsp,216)) *)
  0xe8; 0x6f; 0x1b; 0x00; 0x00;
                           (* CALL (Imm32 (word 7023)) *)
  0x48; 0x8d; 0x74; 0x24; 0x48;
                           (* LEA (% rsi) (%% (rsp,72)) *)
  0x48; 0x8d; 0x3c; 0x24;  (* LEA (% rdi) (%% (rsp,0)) *)
  0xe8; 0x61; 0x1b; 0x00; 0x00;
                           (* CALL (Imm32 (word 7009)) *)
  0x48; 0x8d; 0x94; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* LEA (% rdx) (%% (rsp,288)) *)
  0x48; 0x8d; 0xb4; 0x24; 0xd8; 0x00; 0x00; 0x00;
                           (* LEA (% rsi) (%% (rsp,216)) *)
  0x48; 0x8d; 0xbc; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rsp,288)) *)
  0xe8; 0xaa; 0x14; 0x00; 0x00;
                           (* CALL (Imm32 (word 5290)) *)
  0x48; 0x8d; 0x94; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* LEA (% rdx) (%% (rsp,144)) *)
  0x48; 0x8d; 0xb4; 0x24; 0xd8; 0x00; 0x00; 0x00;
                           (* LEA (% rsi) (%% (rsp,216)) *)
  0x48; 0x8d; 0xbc; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rsp,144)) *)
  0xe8; 0x8d; 0x14; 0x00; 0x00;
                           (* CALL (Imm32 (word 5261)) *)
  0x48; 0x8b; 0x04; 0x24;  (* MOV (% rax) (Memop Quadword (%% (rsp,0))) *)
  0x48; 0x2b; 0x84; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* SUB (% rax) (Memop Quadword (%% (rsp,288))) *)
  0x48; 0x8b; 0x54; 0x24; 0x08;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,8))) *)
  0x48; 0x1b; 0x94; 0x24; 0x28; 0x01; 0x00; 0x00;
                           (* SBB (% rdx) (Memop Quadword (%% (rsp,296))) *)
  0x4c; 0x8b; 0x44; 0x24; 0x10;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,16))) *)
  0x4c; 0x1b; 0x84; 0x24; 0x30; 0x01; 0x00; 0x00;
                           (* SBB (% r8) (Memop Quadword (%% (rsp,304))) *)
  0x4c; 0x8b; 0x4c; 0x24; 0x18;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,24))) *)
  0x4c; 0x1b; 0x8c; 0x24; 0x38; 0x01; 0x00; 0x00;
                           (* SBB (% r9) (Memop Quadword (%% (rsp,312))) *)
  0x4c; 0x8b; 0x54; 0x24; 0x20;
                           (* MOV (% r10) (Memop Quadword (%% (rsp,32))) *)
  0x4c; 0x1b; 0x94; 0x24; 0x40; 0x01; 0x00; 0x00;
                           (* SBB (% r10) (Memop Quadword (%% (rsp,320))) *)
  0x4c; 0x8b; 0x5c; 0x24; 0x28;
                           (* MOV (% r11) (Memop Quadword (%% (rsp,40))) *)
  0x4c; 0x1b; 0x9c; 0x24; 0x48; 0x01; 0x00; 0x00;
                           (* SBB (% r11) (Memop Quadword (%% (rsp,328))) *)
  0x4c; 0x8b; 0x64; 0x24; 0x30;
                           (* MOV (% r12) (Memop Quadword (%% (rsp,48))) *)
  0x4c; 0x1b; 0xa4; 0x24; 0x50; 0x01; 0x00; 0x00;
                           (* SBB (% r12) (Memop Quadword (%% (rsp,336))) *)
  0x4c; 0x8b; 0x6c; 0x24; 0x38;
                           (* MOV (% r13) (Memop Quadword (%% (rsp,56))) *)
  0x4c; 0x1b; 0xac; 0x24; 0x58; 0x01; 0x00; 0x00;
                           (* SBB (% r13) (Memop Quadword (%% (rsp,344))) *)
  0x4c; 0x8b; 0x74; 0x24; 0x40;
                           (* MOV (% r14) (Memop Quadword (%% (rsp,64))) *)
  0x4c; 0x1b; 0xb4; 0x24; 0x60; 0x01; 0x00; 0x00;
                           (* SBB (% r14) (Memop Quadword (%% (rsp,352))) *)
  0x48; 0x83; 0xd8; 0x00;  (* SBB (% rax) (Imm8 (word 0)) *)
  0x48; 0x89; 0x04; 0x24;  (* MOV (Memop Quadword (%% (rsp,0))) (% rax) *)
  0x48; 0x83; 0xda; 0x00;  (* SBB (% rdx) (Imm8 (word 0)) *)
  0x48; 0x89; 0x54; 0x24; 0x08;
                           (* MOV (Memop Quadword (%% (rsp,8))) (% rdx) *)
  0x49; 0x83; 0xd8; 0x00;  (* SBB (% r8) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x44; 0x24; 0x10;
                           (* MOV (Memop Quadword (%% (rsp,16))) (% r8) *)
  0x49; 0x83; 0xd9; 0x00;  (* SBB (% r9) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x4c; 0x24; 0x18;
                           (* MOV (Memop Quadword (%% (rsp,24))) (% r9) *)
  0x49; 0x83; 0xda; 0x00;  (* SBB (% r10) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x54; 0x24; 0x20;
                           (* MOV (Memop Quadword (%% (rsp,32))) (% r10) *)
  0x49; 0x83; 0xdb; 0x00;  (* SBB (% r11) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x5c; 0x24; 0x28;
                           (* MOV (Memop Quadword (%% (rsp,40))) (% r11) *)
  0x49; 0x83; 0xdc; 0x00;  (* SBB (% r12) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x64; 0x24; 0x30;
                           (* MOV (Memop Quadword (%% (rsp,48))) (% r12) *)
  0x49; 0x83; 0xdd; 0x00;  (* SBB (% r13) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x6c; 0x24; 0x38;
                           (* MOV (Memop Quadword (%% (rsp,56))) (% r13) *)
  0x49; 0x83; 0xde; 0x00;  (* SBB (% r14) (Imm8 (word 0)) *)
  0x49; 0x81; 0xe6; 0xff; 0x01; 0x00; 0x00;
                           (* AND (% r14) (Imm32 (word 511)) *)
  0x4c; 0x89; 0x74; 0x24; 0x40;
                           (* MOV (Memop Quadword (%% (rsp,64))) (% r14) *)
  0x48; 0x8b; 0x84; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,144))) *)
  0x48; 0x2b; 0x84; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* SUB (% rax) (Memop Quadword (%% (rsp,288))) *)
  0x48; 0x8b; 0x94; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,152))) *)
  0x48; 0x1b; 0x94; 0x24; 0x28; 0x01; 0x00; 0x00;
                           (* SBB (% rdx) (Memop Quadword (%% (rsp,296))) *)
  0x4c; 0x8b; 0x84; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,160))) *)
  0x4c; 0x1b; 0x84; 0x24; 0x30; 0x01; 0x00; 0x00;
                           (* SBB (% r8) (Memop Quadword (%% (rsp,304))) *)
  0x4c; 0x8b; 0x8c; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,168))) *)
  0x4c; 0x1b; 0x8c; 0x24; 0x38; 0x01; 0x00; 0x00;
                           (* SBB (% r9) (Memop Quadword (%% (rsp,312))) *)
  0x4c; 0x8b; 0x94; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (% r10) (Memop Quadword (%% (rsp,176))) *)
  0x4c; 0x1b; 0x94; 0x24; 0x40; 0x01; 0x00; 0x00;
                           (* SBB (% r10) (Memop Quadword (%% (rsp,320))) *)
  0x4c; 0x8b; 0x9c; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (% r11) (Memop Quadword (%% (rsp,184))) *)
  0x4c; 0x1b; 0x9c; 0x24; 0x48; 0x01; 0x00; 0x00;
                           (* SBB (% r11) (Memop Quadword (%% (rsp,328))) *)
  0x4c; 0x8b; 0xa4; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* MOV (% r12) (Memop Quadword (%% (rsp,192))) *)
  0x4c; 0x1b; 0xa4; 0x24; 0x50; 0x01; 0x00; 0x00;
                           (* SBB (% r12) (Memop Quadword (%% (rsp,336))) *)
  0x4c; 0x8b; 0xac; 0x24; 0xc8; 0x00; 0x00; 0x00;
                           (* MOV (% r13) (Memop Quadword (%% (rsp,200))) *)
  0x4c; 0x1b; 0xac; 0x24; 0x58; 0x01; 0x00; 0x00;
                           (* SBB (% r13) (Memop Quadword (%% (rsp,344))) *)
  0x4c; 0x8b; 0xb4; 0x24; 0xd0; 0x00; 0x00; 0x00;
                           (* MOV (% r14) (Memop Quadword (%% (rsp,208))) *)
  0x4c; 0x1b; 0xb4; 0x24; 0x60; 0x01; 0x00; 0x00;
                           (* SBB (% r14) (Memop Quadword (%% (rsp,352))) *)
  0x48; 0x83; 0xd8; 0x00;  (* SBB (% rax) (Imm8 (word 0)) *)
  0x48; 0x89; 0x84; 0x24; 0xd8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,216))) (% rax) *)
  0x48; 0x83; 0xda; 0x00;  (* SBB (% rdx) (Imm8 (word 0)) *)
  0x48; 0x89; 0x94; 0x24; 0xe0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,224))) (% rdx) *)
  0x49; 0x83; 0xd8; 0x00;  (* SBB (% r8) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x84; 0x24; 0xe8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,232))) (% r8) *)
  0x49; 0x83; 0xd9; 0x00;  (* SBB (% r9) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x8c; 0x24; 0xf0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,240))) (% r9) *)
  0x49; 0x83; 0xda; 0x00;  (* SBB (% r10) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x94; 0x24; 0xf8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,248))) (% r10) *)
  0x49; 0x83; 0xdb; 0x00;  (* SBB (% r11) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x9c; 0x24; 0x00; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,256))) (% r11) *)
  0x49; 0x83; 0xdc; 0x00;  (* SBB (% r12) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xa4; 0x24; 0x08; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,264))) (% r12) *)
  0x49; 0x83; 0xdd; 0x00;  (* SBB (% r13) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xac; 0x24; 0x10; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,272))) (% r13) *)
  0x49; 0x83; 0xde; 0x00;  (* SBB (% r14) (Imm8 (word 0)) *)
  0x49; 0x81; 0xe6; 0xff; 0x01; 0x00; 0x00;
                           (* AND (% r14) (Imm32 (word 511)) *)
  0x4c; 0x89; 0xb4; 0x24; 0x18; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,280))) (% r14) *)
  0x48; 0x8b; 0xb4; 0x24; 0x00; 0x02; 0x00; 0x00;
                           (* MOV (% rsi) (Memop Quadword (%% (rsp,512))) *)
  0x48; 0x8d; 0x96; 0x90; 0x00; 0x00; 0x00;
                           (* LEA (% rdx) (%% (rsi,144)) *)
  0x48; 0x8d; 0xb4; 0x24; 0x68; 0x01; 0x00; 0x00;
                           (* LEA (% rsi) (%% (rsp,360)) *)
  0x48; 0x8d; 0xbc; 0x24; 0x68; 0x01; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rsp,360)) *)
  0xe8; 0x9b; 0x12; 0x00; 0x00;
                           (* CALL (Imm32 (word 4763)) *)
  0x48; 0x8b; 0x04; 0x24;  (* MOV (% rax) (Memop Quadword (%% (rsp,0))) *)
  0x48; 0x2b; 0x84; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* SUB (% rax) (Memop Quadword (%% (rsp,144))) *)
  0x48; 0x8b; 0x54; 0x24; 0x08;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,8))) *)
  0x48; 0x1b; 0x94; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* SBB (% rdx) (Memop Quadword (%% (rsp,152))) *)
  0x4c; 0x8b; 0x44; 0x24; 0x10;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,16))) *)
  0x4c; 0x1b; 0x84; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* SBB (% r8) (Memop Quadword (%% (rsp,160))) *)
  0x4c; 0x8b; 0x4c; 0x24; 0x18;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,24))) *)
  0x4c; 0x1b; 0x8c; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* SBB (% r9) (Memop Quadword (%% (rsp,168))) *)
  0x4c; 0x8b; 0x54; 0x24; 0x20;
                           (* MOV (% r10) (Memop Quadword (%% (rsp,32))) *)
  0x4c; 0x1b; 0x94; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* SBB (% r10) (Memop Quadword (%% (rsp,176))) *)
  0x4c; 0x8b; 0x5c; 0x24; 0x28;
                           (* MOV (% r11) (Memop Quadword (%% (rsp,40))) *)
  0x4c; 0x1b; 0x9c; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* SBB (% r11) (Memop Quadword (%% (rsp,184))) *)
  0x4c; 0x8b; 0x64; 0x24; 0x30;
                           (* MOV (% r12) (Memop Quadword (%% (rsp,48))) *)
  0x4c; 0x1b; 0xa4; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* SBB (% r12) (Memop Quadword (%% (rsp,192))) *)
  0x4c; 0x8b; 0x6c; 0x24; 0x38;
                           (* MOV (% r13) (Memop Quadword (%% (rsp,56))) *)
  0x4c; 0x1b; 0xac; 0x24; 0xc8; 0x00; 0x00; 0x00;
                           (* SBB (% r13) (Memop Quadword (%% (rsp,200))) *)
  0x4c; 0x8b; 0x74; 0x24; 0x40;
                           (* MOV (% r14) (Memop Quadword (%% (rsp,64))) *)
  0x4c; 0x1b; 0xb4; 0x24; 0xd0; 0x00; 0x00; 0x00;
                           (* SBB (% r14) (Memop Quadword (%% (rsp,208))) *)
  0x48; 0x83; 0xd8; 0x00;  (* SBB (% rax) (Imm8 (word 0)) *)
  0x48; 0x89; 0x04; 0x24;  (* MOV (Memop Quadword (%% (rsp,0))) (% rax) *)
  0x48; 0x83; 0xda; 0x00;  (* SBB (% rdx) (Imm8 (word 0)) *)
  0x48; 0x89; 0x54; 0x24; 0x08;
                           (* MOV (Memop Quadword (%% (rsp,8))) (% rdx) *)
  0x49; 0x83; 0xd8; 0x00;  (* SBB (% r8) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x44; 0x24; 0x10;
                           (* MOV (Memop Quadword (%% (rsp,16))) (% r8) *)
  0x49; 0x83; 0xd9; 0x00;  (* SBB (% r9) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x4c; 0x24; 0x18;
                           (* MOV (Memop Quadword (%% (rsp,24))) (% r9) *)
  0x49; 0x83; 0xda; 0x00;  (* SBB (% r10) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x54; 0x24; 0x20;
                           (* MOV (Memop Quadword (%% (rsp,32))) (% r10) *)
  0x49; 0x83; 0xdb; 0x00;  (* SBB (% r11) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x5c; 0x24; 0x28;
                           (* MOV (Memop Quadword (%% (rsp,40))) (% r11) *)
  0x49; 0x83; 0xdc; 0x00;  (* SBB (% r12) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x64; 0x24; 0x30;
                           (* MOV (Memop Quadword (%% (rsp,48))) (% r12) *)
  0x49; 0x83; 0xdd; 0x00;  (* SBB (% r13) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x6c; 0x24; 0x38;
                           (* MOV (Memop Quadword (%% (rsp,56))) (% r13) *)
  0x49; 0x83; 0xde; 0x00;  (* SBB (% r14) (Imm8 (word 0)) *)
  0x49; 0x81; 0xe6; 0xff; 0x01; 0x00; 0x00;
                           (* AND (% r14) (Imm32 (word 511)) *)
  0x4c; 0x89; 0x74; 0x24; 0x40;
                           (* MOV (Memop Quadword (%% (rsp,64))) (% r14) *)
  0x48; 0x8b; 0x84; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,288))) *)
  0x48; 0x2b; 0x04; 0x24;  (* SUB (% rax) (Memop Quadword (%% (rsp,0))) *)
  0x48; 0x8b; 0x94; 0x24; 0x28; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,296))) *)
  0x48; 0x1b; 0x54; 0x24; 0x08;
                           (* SBB (% rdx) (Memop Quadword (%% (rsp,8))) *)
  0x4c; 0x8b; 0x84; 0x24; 0x30; 0x01; 0x00; 0x00;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,304))) *)
  0x4c; 0x1b; 0x44; 0x24; 0x10;
                           (* SBB (% r8) (Memop Quadword (%% (rsp,16))) *)
  0x4c; 0x8b; 0x8c; 0x24; 0x38; 0x01; 0x00; 0x00;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,312))) *)
  0x4c; 0x1b; 0x4c; 0x24; 0x18;
                           (* SBB (% r9) (Memop Quadword (%% (rsp,24))) *)
  0x4c; 0x8b; 0x94; 0x24; 0x40; 0x01; 0x00; 0x00;
                           (* MOV (% r10) (Memop Quadword (%% (rsp,320))) *)
  0x4c; 0x1b; 0x54; 0x24; 0x20;
                           (* SBB (% r10) (Memop Quadword (%% (rsp,32))) *)
  0x4c; 0x8b; 0x9c; 0x24; 0x48; 0x01; 0x00; 0x00;
                           (* MOV (% r11) (Memop Quadword (%% (rsp,328))) *)
  0x4c; 0x1b; 0x5c; 0x24; 0x28;
                           (* SBB (% r11) (Memop Quadword (%% (rsp,40))) *)
  0x4c; 0x8b; 0xa4; 0x24; 0x50; 0x01; 0x00; 0x00;
                           (* MOV (% r12) (Memop Quadword (%% (rsp,336))) *)
  0x4c; 0x1b; 0x64; 0x24; 0x30;
                           (* SBB (% r12) (Memop Quadword (%% (rsp,48))) *)
  0x4c; 0x8b; 0xac; 0x24; 0x58; 0x01; 0x00; 0x00;
                           (* MOV (% r13) (Memop Quadword (%% (rsp,344))) *)
  0x4c; 0x1b; 0x6c; 0x24; 0x38;
                           (* SBB (% r13) (Memop Quadword (%% (rsp,56))) *)
  0x4c; 0x8b; 0xb4; 0x24; 0x60; 0x01; 0x00; 0x00;
                           (* MOV (% r14) (Memop Quadword (%% (rsp,352))) *)
  0x4c; 0x1b; 0x74; 0x24; 0x40;
                           (* SBB (% r14) (Memop Quadword (%% (rsp,64))) *)
  0x48; 0x83; 0xd8; 0x00;  (* SBB (% rax) (Imm8 (word 0)) *)
  0x48; 0x89; 0x84; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,288))) (% rax) *)
  0x48; 0x83; 0xda; 0x00;  (* SBB (% rdx) (Imm8 (word 0)) *)
  0x48; 0x89; 0x94; 0x24; 0x28; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,296))) (% rdx) *)
  0x49; 0x83; 0xd8; 0x00;  (* SBB (% r8) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x84; 0x24; 0x30; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,304))) (% r8) *)
  0x49; 0x83; 0xd9; 0x00;  (* SBB (% r9) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x8c; 0x24; 0x38; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,312))) (% r9) *)
  0x49; 0x83; 0xda; 0x00;  (* SBB (% r10) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x94; 0x24; 0x40; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,320))) (% r10) *)
  0x49; 0x83; 0xdb; 0x00;  (* SBB (% r11) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x9c; 0x24; 0x48; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,328))) (% r11) *)
  0x49; 0x83; 0xdc; 0x00;  (* SBB (% r12) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xa4; 0x24; 0x50; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,336))) (% r12) *)
  0x49; 0x83; 0xdd; 0x00;  (* SBB (% r13) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xac; 0x24; 0x58; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,344))) (% r13) *)
  0x49; 0x83; 0xde; 0x00;  (* SBB (% r14) (Imm8 (word 0)) *)
  0x49; 0x81; 0xe6; 0xff; 0x01; 0x00; 0x00;
                           (* AND (% r14) (Imm32 (word 511)) *)
  0x4c; 0x89; 0xb4; 0x24; 0x60; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,352))) (% r14) *)
  0x48; 0x8d; 0x94; 0x24; 0xb0; 0x01; 0x00; 0x00;
                           (* LEA (% rdx) (%% (rsp,432)) *)
  0x48; 0x8d; 0xb4; 0x24; 0xd8; 0x00; 0x00; 0x00;
                           (* LEA (% rsi) (%% (rsp,216)) *)
  0x48; 0x8d; 0xbc; 0x24; 0xd8; 0x00; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rsp,216)) *)
  0xe8; 0xcc; 0x10; 0x00; 0x00;
                           (* CALL (Imm32 (word 4300)) *)
  0x48; 0x8b; 0xbc; 0x24; 0x08; 0x02; 0x00; 0x00;
                           (* MOV (% rdi) (Memop Quadword (%% (rsp,520))) *)
  0x48; 0x8d; 0x97; 0x90; 0x00; 0x00; 0x00;
                           (* LEA (% rdx) (%% (rdi,144)) *)
  0x48; 0x8d; 0xb4; 0x24; 0x68; 0x01; 0x00; 0x00;
                           (* LEA (% rsi) (%% (rsp,360)) *)
  0x48; 0x8d; 0xbc; 0x24; 0x68; 0x01; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rsp,360)) *)
  0xe8; 0xa8; 0x10; 0x00; 0x00;
                           (* CALL (Imm32 (word 4264)) *)
  0x48; 0x8d; 0x94; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* LEA (% rdx) (%% (rsp,288)) *)
  0x48; 0x8d; 0x74; 0x24; 0x48;
                           (* LEA (% rsi) (%% (rsp,72)) *)
  0x48; 0x8d; 0xbc; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rsp,288)) *)
  0xe8; 0x8e; 0x10; 0x00; 0x00;
                           (* CALL (Imm32 (word 4238)) *)
  0x48; 0x8b; 0x84; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,288))) *)
  0x48; 0x2b; 0x84; 0x24; 0xd8; 0x00; 0x00; 0x00;
                           (* SUB (% rax) (Memop Quadword (%% (rsp,216))) *)
  0x48; 0x8b; 0x94; 0x24; 0x28; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,296))) *)
  0x48; 0x1b; 0x94; 0x24; 0xe0; 0x00; 0x00; 0x00;
                           (* SBB (% rdx) (Memop Quadword (%% (rsp,224))) *)
  0x4c; 0x8b; 0x84; 0x24; 0x30; 0x01; 0x00; 0x00;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,304))) *)
  0x4c; 0x1b; 0x84; 0x24; 0xe8; 0x00; 0x00; 0x00;
                           (* SBB (% r8) (Memop Quadword (%% (rsp,232))) *)
  0x4c; 0x8b; 0x8c; 0x24; 0x38; 0x01; 0x00; 0x00;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,312))) *)
  0x4c; 0x1b; 0x8c; 0x24; 0xf0; 0x00; 0x00; 0x00;
                           (* SBB (% r9) (Memop Quadword (%% (rsp,240))) *)
  0x4c; 0x8b; 0x94; 0x24; 0x40; 0x01; 0x00; 0x00;
                           (* MOV (% r10) (Memop Quadword (%% (rsp,320))) *)
  0x4c; 0x1b; 0x94; 0x24; 0xf8; 0x00; 0x00; 0x00;
                           (* SBB (% r10) (Memop Quadword (%% (rsp,248))) *)
  0x4c; 0x8b; 0x9c; 0x24; 0x48; 0x01; 0x00; 0x00;
                           (* MOV (% r11) (Memop Quadword (%% (rsp,328))) *)
  0x4c; 0x1b; 0x9c; 0x24; 0x00; 0x01; 0x00; 0x00;
                           (* SBB (% r11) (Memop Quadword (%% (rsp,256))) *)
  0x4c; 0x8b; 0xa4; 0x24; 0x50; 0x01; 0x00; 0x00;
                           (* MOV (% r12) (Memop Quadword (%% (rsp,336))) *)
  0x4c; 0x1b; 0xa4; 0x24; 0x08; 0x01; 0x00; 0x00;
                           (* SBB (% r12) (Memop Quadword (%% (rsp,264))) *)
  0x4c; 0x8b; 0xac; 0x24; 0x58; 0x01; 0x00; 0x00;
                           (* MOV (% r13) (Memop Quadword (%% (rsp,344))) *)
  0x4c; 0x1b; 0xac; 0x24; 0x10; 0x01; 0x00; 0x00;
                           (* SBB (% r13) (Memop Quadword (%% (rsp,272))) *)
  0x4c; 0x8b; 0xb4; 0x24; 0x60; 0x01; 0x00; 0x00;
                           (* MOV (% r14) (Memop Quadword (%% (rsp,352))) *)
  0x4c; 0x1b; 0xb4; 0x24; 0x18; 0x01; 0x00; 0x00;
                           (* SBB (% r14) (Memop Quadword (%% (rsp,280))) *)
  0x48; 0x83; 0xd8; 0x00;  (* SBB (% rax) (Imm8 (word 0)) *)
  0x48; 0x89; 0x84; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,288))) (% rax) *)
  0x48; 0x83; 0xda; 0x00;  (* SBB (% rdx) (Imm8 (word 0)) *)
  0x48; 0x89; 0x94; 0x24; 0x28; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,296))) (% rdx) *)
  0x49; 0x83; 0xd8; 0x00;  (* SBB (% r8) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x84; 0x24; 0x30; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,304))) (% r8) *)
  0x49; 0x83; 0xd9; 0x00;  (* SBB (% r9) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x8c; 0x24; 0x38; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,312))) (% r9) *)
  0x49; 0x83; 0xda; 0x00;  (* SBB (% r10) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x94; 0x24; 0x40; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,320))) (% r10) *)
  0x49; 0x83; 0xdb; 0x00;  (* SBB (% r11) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x9c; 0x24; 0x48; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,328))) (% r11) *)
  0x49; 0x83; 0xdc; 0x00;  (* SBB (% r12) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xa4; 0x24; 0x50; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,336))) (% r12) *)
  0x49; 0x83; 0xdd; 0x00;  (* SBB (% r13) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xac; 0x24; 0x58; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,344))) (% r13) *)
  0x49; 0x83; 0xde; 0x00;  (* SBB (% r14) (Imm8 (word 0)) *)
  0x49; 0x81; 0xe6; 0xff; 0x01; 0x00; 0x00;
                           (* AND (% r14) (Imm32 (word 511)) *)
  0x4c; 0x89; 0xb4; 0x24; 0x60; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,352))) (% r14) *)
  0x48; 0x8b; 0xb4; 0x24; 0x00; 0x02; 0x00; 0x00;
                           (* MOV (% rsi) (Memop Quadword (%% (rsp,512))) *)
  0x4c; 0x8b; 0x86; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (% r8) (Memop Quadword (%% (rsi,144))) *)
  0x4c; 0x8b; 0x8e; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (% r9) (Memop Quadword (%% (rsi,152))) *)
  0x4c; 0x8b; 0x96; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (% r10) (Memop Quadword (%% (rsi,160))) *)
  0x4c; 0x8b; 0x9e; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (% r11) (Memop Quadword (%% (rsi,168))) *)
  0x4c; 0x8b; 0xa6; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (% r12) (Memop Quadword (%% (rsi,176))) *)
  0x4c; 0x8b; 0xae; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (% r13) (Memop Quadword (%% (rsi,184))) *)
  0x4c; 0x8b; 0xb6; 0xc0; 0x00; 0x00; 0x00;
                           (* MOV (% r14) (Memop Quadword (%% (rsi,192))) *)
  0x4c; 0x8b; 0xbe; 0xc8; 0x00; 0x00; 0x00;
                           (* MOV (% r15) (Memop Quadword (%% (rsi,200))) *)
  0x48; 0x8b; 0xae; 0xd0; 0x00; 0x00; 0x00;
                           (* MOV (% rbp) (Memop Quadword (%% (rsi,208))) *)
  0x4d; 0x09; 0xc8;        (* OR (% r8) (% r9) *)
  0x4d; 0x09; 0xda;        (* OR (% r10) (% r11) *)
  0x4d; 0x09; 0xec;        (* OR (% r12) (% r13) *)
  0x4d; 0x09; 0xfe;        (* OR (% r14) (% r15) *)
  0x4d; 0x09; 0xd0;        (* OR (% r8) (% r10) *)
  0x4d; 0x09; 0xf4;        (* OR (% r12) (% r14) *)
  0x49; 0x09; 0xe8;        (* OR (% r8) (% rbp) *)
  0x4d; 0x09; 0xe0;        (* OR (% r8) (% r12) *)
  0x49; 0xf7; 0xd8;        (* NEG (% r8) *)
  0x48; 0x19; 0xc0;        (* SBB (% rax) (% rax) *)
  0x48; 0x8b; 0xbc; 0x24; 0x08; 0x02; 0x00; 0x00;
                           (* MOV (% rdi) (Memop Quadword (%% (rsp,520))) *)
  0x4c; 0x8b; 0x87; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (% r8) (Memop Quadword (%% (rdi,144))) *)
  0x4c; 0x8b; 0x8f; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (% r9) (Memop Quadword (%% (rdi,152))) *)
  0x4c; 0x8b; 0x97; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (% r10) (Memop Quadword (%% (rdi,160))) *)
  0x4c; 0x8b; 0x9f; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (% r11) (Memop Quadword (%% (rdi,168))) *)
  0x4c; 0x8b; 0xa7; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (% r12) (Memop Quadword (%% (rdi,176))) *)
  0x4c; 0x8b; 0xaf; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (% r13) (Memop Quadword (%% (rdi,184))) *)
  0x4c; 0x8b; 0xb7; 0xc0; 0x00; 0x00; 0x00;
                           (* MOV (% r14) (Memop Quadword (%% (rdi,192))) *)
  0x4c; 0x8b; 0xbf; 0xc8; 0x00; 0x00; 0x00;
                           (* MOV (% r15) (Memop Quadword (%% (rdi,200))) *)
  0x48; 0x8b; 0xaf; 0xd0; 0x00; 0x00; 0x00;
                           (* MOV (% rbp) (Memop Quadword (%% (rdi,208))) *)
  0x4d; 0x09; 0xc8;        (* OR (% r8) (% r9) *)
  0x4d; 0x09; 0xda;        (* OR (% r10) (% r11) *)
  0x4d; 0x09; 0xec;        (* OR (% r12) (% r13) *)
  0x4d; 0x09; 0xfe;        (* OR (% r14) (% r15) *)
  0x4d; 0x09; 0xd0;        (* OR (% r8) (% r10) *)
  0x4d; 0x09; 0xf4;        (* OR (% r12) (% r14) *)
  0x49; 0x09; 0xe8;        (* OR (% r8) (% rbp) *)
  0x4d; 0x09; 0xe0;        (* OR (% r8) (% r12) *)
  0x49; 0xf7; 0xd8;        (* NEG (% r8) *)
  0x48; 0x19; 0xd2;        (* SBB (% rdx) (% rdx) *)
  0x48; 0x39; 0xc2;        (* CMP (% rdx) (% rax) *)
  0x4c; 0x8b; 0x84; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,288))) *)
  0x4c; 0x0f; 0x42; 0x46; 0x48;
                           (* CMOVB (% r8) (Memop Quadword (%% (rsi,72))) *)
  0x4c; 0x0f; 0x47; 0x47; 0x48;
                           (* CMOVA (% r8) (Memop Quadword (%% (rdi,72))) *)
  0x4c; 0x8b; 0x8c; 0x24; 0x28; 0x01; 0x00; 0x00;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,296))) *)
  0x4c; 0x0f; 0x42; 0x4e; 0x50;
                           (* CMOVB (% r9) (Memop Quadword (%% (rsi,80))) *)
  0x4c; 0x0f; 0x47; 0x4f; 0x50;
                           (* CMOVA (% r9) (Memop Quadword (%% (rdi,80))) *)
  0x4c; 0x8b; 0x94; 0x24; 0x30; 0x01; 0x00; 0x00;
                           (* MOV (% r10) (Memop Quadword (%% (rsp,304))) *)
  0x4c; 0x0f; 0x42; 0x56; 0x58;
                           (* CMOVB (% r10) (Memop Quadword (%% (rsi,88))) *)
  0x4c; 0x0f; 0x47; 0x57; 0x58;
                           (* CMOVA (% r10) (Memop Quadword (%% (rdi,88))) *)
  0x4c; 0x8b; 0x9c; 0x24; 0x38; 0x01; 0x00; 0x00;
                           (* MOV (% r11) (Memop Quadword (%% (rsp,312))) *)
  0x4c; 0x0f; 0x42; 0x5e; 0x60;
                           (* CMOVB (% r11) (Memop Quadword (%% (rsi,96))) *)
  0x4c; 0x0f; 0x47; 0x5f; 0x60;
                           (* CMOVA (% r11) (Memop Quadword (%% (rdi,96))) *)
  0x4c; 0x8b; 0xa4; 0x24; 0x40; 0x01; 0x00; 0x00;
                           (* MOV (% r12) (Memop Quadword (%% (rsp,320))) *)
  0x4c; 0x0f; 0x42; 0x66; 0x68;
                           (* CMOVB (% r12) (Memop Quadword (%% (rsi,104))) *)
  0x4c; 0x0f; 0x47; 0x67; 0x68;
                           (* CMOVA (% r12) (Memop Quadword (%% (rdi,104))) *)
  0x4c; 0x8b; 0xac; 0x24; 0x48; 0x01; 0x00; 0x00;
                           (* MOV (% r13) (Memop Quadword (%% (rsp,328))) *)
  0x4c; 0x0f; 0x42; 0x6e; 0x70;
                           (* CMOVB (% r13) (Memop Quadword (%% (rsi,112))) *)
  0x4c; 0x0f; 0x47; 0x6f; 0x70;
                           (* CMOVA (% r13) (Memop Quadword (%% (rdi,112))) *)
  0x4c; 0x8b; 0xb4; 0x24; 0x50; 0x01; 0x00; 0x00;
                           (* MOV (% r14) (Memop Quadword (%% (rsp,336))) *)
  0x4c; 0x0f; 0x42; 0x76; 0x78;
                           (* CMOVB (% r14) (Memop Quadword (%% (rsi,120))) *)
  0x4c; 0x0f; 0x47; 0x77; 0x78;
                           (* CMOVA (% r14) (Memop Quadword (%% (rdi,120))) *)
  0x4c; 0x8b; 0xbc; 0x24; 0x58; 0x01; 0x00; 0x00;
                           (* MOV (% r15) (Memop Quadword (%% (rsp,344))) *)
  0x4c; 0x0f; 0x42; 0xbe; 0x80; 0x00; 0x00; 0x00;
                           (* CMOVB (% r15) (Memop Quadword (%% (rsi,128))) *)
  0x4c; 0x0f; 0x47; 0xbf; 0x80; 0x00; 0x00; 0x00;
                           (* CMOVA (% r15) (Memop Quadword (%% (rdi,128))) *)
  0x48; 0x8b; 0xac; 0x24; 0x60; 0x01; 0x00; 0x00;
                           (* MOV (% rbp) (Memop Quadword (%% (rsp,352))) *)
  0x48; 0x0f; 0x42; 0xae; 0x88; 0x00; 0x00; 0x00;
                           (* CMOVB (% rbp) (Memop Quadword (%% (rsi,136))) *)
  0x48; 0x0f; 0x47; 0xaf; 0x88; 0x00; 0x00; 0x00;
                           (* CMOVA (% rbp) (Memop Quadword (%% (rdi,136))) *)
  0x4c; 0x89; 0x84; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,288))) (% r8) *)
  0x4c; 0x89; 0x8c; 0x24; 0x28; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,296))) (% r9) *)
  0x4c; 0x89; 0x94; 0x24; 0x30; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,304))) (% r10) *)
  0x4c; 0x89; 0x9c; 0x24; 0x38; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,312))) (% r11) *)
  0x4c; 0x89; 0xa4; 0x24; 0x40; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,320))) (% r12) *)
  0x4c; 0x89; 0xac; 0x24; 0x48; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,328))) (% r13) *)
  0x4c; 0x89; 0xb4; 0x24; 0x50; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,336))) (% r14) *)
  0x4c; 0x89; 0xbc; 0x24; 0x58; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,344))) (% r15) *)
  0x48; 0x89; 0xac; 0x24; 0x60; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,352))) (% rbp) *)
  0x4c; 0x8b; 0x84; 0x24; 0x68; 0x01; 0x00; 0x00;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,360))) *)
  0x4c; 0x0f; 0x42; 0x86; 0x90; 0x00; 0x00; 0x00;
                           (* CMOVB (% r8) (Memop Quadword (%% (rsi,144))) *)
  0x4c; 0x0f; 0x47; 0x87; 0x90; 0x00; 0x00; 0x00;
                           (* CMOVA (% r8) (Memop Quadword (%% (rdi,144))) *)
  0x4c; 0x8b; 0x8c; 0x24; 0x70; 0x01; 0x00; 0x00;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,368))) *)
  0x4c; 0x0f; 0x42; 0x8e; 0x98; 0x00; 0x00; 0x00;
                           (* CMOVB (% r9) (Memop Quadword (%% (rsi,152))) *)
  0x4c; 0x0f; 0x47; 0x8f; 0x98; 0x00; 0x00; 0x00;
                           (* CMOVA (% r9) (Memop Quadword (%% (rdi,152))) *)
  0x4c; 0x8b; 0x94; 0x24; 0x78; 0x01; 0x00; 0x00;
                           (* MOV (% r10) (Memop Quadword (%% (rsp,376))) *)
  0x4c; 0x0f; 0x42; 0x96; 0xa0; 0x00; 0x00; 0x00;
                           (* CMOVB (% r10) (Memop Quadword (%% (rsi,160))) *)
  0x4c; 0x0f; 0x47; 0x97; 0xa0; 0x00; 0x00; 0x00;
                           (* CMOVA (% r10) (Memop Quadword (%% (rdi,160))) *)
  0x4c; 0x8b; 0x9c; 0x24; 0x80; 0x01; 0x00; 0x00;
                           (* MOV (% r11) (Memop Quadword (%% (rsp,384))) *)
  0x4c; 0x0f; 0x42; 0x9e; 0xa8; 0x00; 0x00; 0x00;
                           (* CMOVB (% r11) (Memop Quadword (%% (rsi,168))) *)
  0x4c; 0x0f; 0x47; 0x9f; 0xa8; 0x00; 0x00; 0x00;
                           (* CMOVA (% r11) (Memop Quadword (%% (rdi,168))) *)
  0x4c; 0x8b; 0xa4; 0x24; 0x88; 0x01; 0x00; 0x00;
                           (* MOV (% r12) (Memop Quadword (%% (rsp,392))) *)
  0x4c; 0x0f; 0x42; 0xa6; 0xb0; 0x00; 0x00; 0x00;
                           (* CMOVB (% r12) (Memop Quadword (%% (rsi,176))) *)
  0x4c; 0x0f; 0x47; 0xa7; 0xb0; 0x00; 0x00; 0x00;
                           (* CMOVA (% r12) (Memop Quadword (%% (rdi,176))) *)
  0x4c; 0x8b; 0xac; 0x24; 0x90; 0x01; 0x00; 0x00;
                           (* MOV (% r13) (Memop Quadword (%% (rsp,400))) *)
  0x4c; 0x0f; 0x42; 0xae; 0xb8; 0x00; 0x00; 0x00;
                           (* CMOVB (% r13) (Memop Quadword (%% (rsi,184))) *)
  0x4c; 0x0f; 0x47; 0xaf; 0xb8; 0x00; 0x00; 0x00;
                           (* CMOVA (% r13) (Memop Quadword (%% (rdi,184))) *)
  0x4c; 0x8b; 0xb4; 0x24; 0x98; 0x01; 0x00; 0x00;
                           (* MOV (% r14) (Memop Quadword (%% (rsp,408))) *)
  0x4c; 0x0f; 0x42; 0xb6; 0xc0; 0x00; 0x00; 0x00;
                           (* CMOVB (% r14) (Memop Quadword (%% (rsi,192))) *)
  0x4c; 0x0f; 0x47; 0xb7; 0xc0; 0x00; 0x00; 0x00;
                           (* CMOVA (% r14) (Memop Quadword (%% (rdi,192))) *)
  0x4c; 0x8b; 0xbc; 0x24; 0xa0; 0x01; 0x00; 0x00;
                           (* MOV (% r15) (Memop Quadword (%% (rsp,416))) *)
  0x4c; 0x0f; 0x42; 0xbe; 0xc8; 0x00; 0x00; 0x00;
                           (* CMOVB (% r15) (Memop Quadword (%% (rsi,200))) *)
  0x4c; 0x0f; 0x47; 0xbf; 0xc8; 0x00; 0x00; 0x00;
                           (* CMOVA (% r15) (Memop Quadword (%% (rdi,200))) *)
  0x48; 0x8b; 0xac; 0x24; 0xa8; 0x01; 0x00; 0x00;
                           (* MOV (% rbp) (Memop Quadword (%% (rsp,424))) *)
  0x48; 0x0f; 0x42; 0xae; 0xd0; 0x00; 0x00; 0x00;
                           (* CMOVB (% rbp) (Memop Quadword (%% (rsi,208))) *)
  0x48; 0x0f; 0x47; 0xaf; 0xd0; 0x00; 0x00; 0x00;
                           (* CMOVA (% rbp) (Memop Quadword (%% (rdi,208))) *)
  0x4c; 0x89; 0x84; 0x24; 0x68; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,360))) (% r8) *)
  0x4c; 0x89; 0x8c; 0x24; 0x70; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,368))) (% r9) *)
  0x4c; 0x89; 0x94; 0x24; 0x78; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,376))) (% r10) *)
  0x4c; 0x89; 0x9c; 0x24; 0x80; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,384))) (% r11) *)
  0x4c; 0x89; 0xa4; 0x24; 0x88; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,392))) (% r12) *)
  0x4c; 0x89; 0xac; 0x24; 0x90; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,400))) (% r13) *)
  0x4c; 0x89; 0xb4; 0x24; 0x98; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,408))) (% r14) *)
  0x4c; 0x89; 0xbc; 0x24; 0xa0; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,416))) (% r15) *)
  0x48; 0x89; 0xac; 0x24; 0xa8; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,424))) (% rbp) *)
  0x4c; 0x8b; 0x04; 0x24;  (* MOV (% r8) (Memop Quadword (%% (rsp,0))) *)
  0x4c; 0x0f; 0x42; 0x06;  (* CMOVB (% r8) (Memop Quadword (%% (rsi,0))) *)
  0x4c; 0x0f; 0x47; 0x07;  (* CMOVA (% r8) (Memop Quadword (%% (rdi,0))) *)
  0x4c; 0x8b; 0x4c; 0x24; 0x08;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,8))) *)
  0x4c; 0x0f; 0x42; 0x4e; 0x08;
                           (* CMOVB (% r9) (Memop Quadword (%% (rsi,8))) *)
  0x4c; 0x0f; 0x47; 0x4f; 0x08;
                           (* CMOVA (% r9) (Memop Quadword (%% (rdi,8))) *)
  0x4c; 0x8b; 0x54; 0x24; 0x10;
                           (* MOV (% r10) (Memop Quadword (%% (rsp,16))) *)
  0x4c; 0x0f; 0x42; 0x56; 0x10;
                           (* CMOVB (% r10) (Memop Quadword (%% (rsi,16))) *)
  0x4c; 0x0f; 0x47; 0x57; 0x10;
                           (* CMOVA (% r10) (Memop Quadword (%% (rdi,16))) *)
  0x4c; 0x8b; 0x5c; 0x24; 0x18;
                           (* MOV (% r11) (Memop Quadword (%% (rsp,24))) *)
  0x4c; 0x0f; 0x42; 0x5e; 0x18;
                           (* CMOVB (% r11) (Memop Quadword (%% (rsi,24))) *)
  0x4c; 0x0f; 0x47; 0x5f; 0x18;
                           (* CMOVA (% r11) (Memop Quadword (%% (rdi,24))) *)
  0x4c; 0x8b; 0x64; 0x24; 0x20;
                           (* MOV (% r12) (Memop Quadword (%% (rsp,32))) *)
  0x4c; 0x0f; 0x42; 0x66; 0x20;
                           (* CMOVB (% r12) (Memop Quadword (%% (rsi,32))) *)
  0x4c; 0x0f; 0x47; 0x67; 0x20;
                           (* CMOVA (% r12) (Memop Quadword (%% (rdi,32))) *)
  0x4c; 0x8b; 0x6c; 0x24; 0x28;
                           (* MOV (% r13) (Memop Quadword (%% (rsp,40))) *)
  0x4c; 0x0f; 0x42; 0x6e; 0x28;
                           (* CMOVB (% r13) (Memop Quadword (%% (rsi,40))) *)
  0x4c; 0x0f; 0x47; 0x6f; 0x28;
                           (* CMOVA (% r13) (Memop Quadword (%% (rdi,40))) *)
  0x4c; 0x8b; 0x74; 0x24; 0x30;
                           (* MOV (% r14) (Memop Quadword (%% (rsp,48))) *)
  0x4c; 0x0f; 0x42; 0x76; 0x30;
                           (* CMOVB (% r14) (Memop Quadword (%% (rsi,48))) *)
  0x4c; 0x0f; 0x47; 0x77; 0x30;
                           (* CMOVA (% r14) (Memop Quadword (%% (rdi,48))) *)
  0x4c; 0x8b; 0x7c; 0x24; 0x38;
                           (* MOV (% r15) (Memop Quadword (%% (rsp,56))) *)
  0x4c; 0x0f; 0x42; 0x7e; 0x38;
                           (* CMOVB (% r15) (Memop Quadword (%% (rsi,56))) *)
  0x4c; 0x0f; 0x47; 0x7f; 0x38;
                           (* CMOVA (% r15) (Memop Quadword (%% (rdi,56))) *)
  0x48; 0x8b; 0x6c; 0x24; 0x40;
                           (* MOV (% rbp) (Memop Quadword (%% (rsp,64))) *)
  0x48; 0x0f; 0x42; 0x6e; 0x40;
                           (* CMOVB (% rbp) (Memop Quadword (%% (rsi,64))) *)
  0x48; 0x0f; 0x47; 0x6f; 0x40;
                           (* CMOVA (% rbp) (Memop Quadword (%% (rdi,64))) *)
  0x48; 0x8b; 0xbc; 0x24; 0xf8; 0x01; 0x00; 0x00;
                           (* MOV (% rdi) (Memop Quadword (%% (rsp,504))) *)
  0x4c; 0x89; 0x07;        (* MOV (Memop Quadword (%% (rdi,0))) (% r8) *)
  0x4c; 0x89; 0x4f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% r9) *)
  0x4c; 0x89; 0x57; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r10) *)
  0x4c; 0x89; 0x5f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r11) *)
  0x4c; 0x89; 0x67; 0x20;  (* MOV (Memop Quadword (%% (rdi,32))) (% r12) *)
  0x4c; 0x89; 0x6f; 0x28;  (* MOV (Memop Quadword (%% (rdi,40))) (% r13) *)
  0x4c; 0x89; 0x77; 0x30;  (* MOV (Memop Quadword (%% (rdi,48))) (% r14) *)
  0x4c; 0x89; 0x7f; 0x38;  (* MOV (Memop Quadword (%% (rdi,56))) (% r15) *)
  0x48; 0x89; 0x6f; 0x40;  (* MOV (Memop Quadword (%% (rdi,64))) (% rbp) *)
  0x48; 0x8b; 0x84; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,288))) *)
  0x48; 0x89; 0x47; 0x48;  (* MOV (Memop Quadword (%% (rdi,72))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x28; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,296))) *)
  0x48; 0x89; 0x47; 0x50;  (* MOV (Memop Quadword (%% (rdi,80))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x30; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,304))) *)
  0x48; 0x89; 0x47; 0x58;  (* MOV (Memop Quadword (%% (rdi,88))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x38; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,312))) *)
  0x48; 0x89; 0x47; 0x60;  (* MOV (Memop Quadword (%% (rdi,96))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x40; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,320))) *)
  0x48; 0x89; 0x47; 0x68;  (* MOV (Memop Quadword (%% (rdi,104))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x48; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,328))) *)
  0x48; 0x89; 0x47; 0x70;  (* MOV (Memop Quadword (%% (rdi,112))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x50; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,336))) *)
  0x48; 0x89; 0x47; 0x78;  (* MOV (Memop Quadword (%% (rdi,120))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x58; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,344))) *)
  0x48; 0x89; 0x87; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,128))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x60; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,352))) *)
  0x48; 0x89; 0x87; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,136))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x68; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,360))) *)
  0x48; 0x89; 0x87; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,144))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x70; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,368))) *)
  0x48; 0x89; 0x87; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,152))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x78; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,376))) *)
  0x48; 0x89; 0x87; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,160))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x80; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,384))) *)
  0x48; 0x89; 0x87; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,168))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x88; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,392))) *)
  0x48; 0x89; 0x87; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,176))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x90; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,400))) *)
  0x48; 0x89; 0x87; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,184))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x98; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,408))) *)
  0x48; 0x89; 0x87; 0xc0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,192))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0xa0; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,416))) *)
  0x48; 0x89; 0x87; 0xc8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,200))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0xa8; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,424))) *)
  0x48; 0x89; 0x87; 0xd0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,208))) (% rax) *)
  0x48; 0x81; 0xc4; 0x10; 0x02; 0x00; 0x00;
                           (* ADD (% rsp) (Imm32 (word 528)) *)
  0x41; 0x5f;              (* POP (% r15) *)
  0x41; 0x5e;              (* POP (% r14) *)
  0x41; 0x5d;              (* POP (% r13) *)
  0x41; 0x5c;              (* POP (% r12) *)
  0x5d;                    (* POP (% rbp) *)
  0x5b;                    (* POP (% rbx) *)
  0xc3;                    (* RET *)
  0x53;                    (* PUSH (% rbx) *)
  0x55;                    (* PUSH (% rbp) *)
  0x41; 0x54;              (* PUSH (% r12) *)
  0x41; 0x55;              (* PUSH (% r13) *)
  0x41; 0x56;              (* PUSH (% r14) *)
  0x41; 0x57;              (* PUSH (% r15) *)
  0x48; 0x81; 0xec; 0x08; 0x02; 0x00; 0x00;
                           (* SUB (% rsp) (Imm32 (word 520)) *)
  0x48; 0x89; 0xbc; 0x24; 0xf8; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,504))) (% rdi) *)
  0x48; 0x89; 0xb4; 0x24; 0x00; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,512))) (% rsi) *)
  0x48; 0x8b; 0xbc; 0x24; 0x00; 0x02; 0x00; 0x00;
                           (* MOV (% rdi) (Memop Quadword (%% (rsp,512))) *)
  0x48; 0x8d; 0xb7; 0x90; 0x00; 0x00; 0x00;
                           (* LEA (% rsi) (%% (rdi,144)) *)
  0x48; 0x8d; 0x3c; 0x24;  (* LEA (% rdi) (%% (rsp,0)) *)
  0xe8; 0x4f; 0x11; 0x00; 0x00;
                           (* CALL (Imm32 (word 4431)) *)
  0x48; 0x8b; 0xbc; 0x24; 0x00; 0x02; 0x00; 0x00;
                           (* MOV (% rdi) (Memop Quadword (%% (rsp,512))) *)
  0x48; 0x8d; 0x77; 0x48;  (* LEA (% rsi) (%% (rdi,72)) *)
  0x48; 0x8d; 0x7c; 0x24; 0x48;
                           (* LEA (% rdi) (%% (rsp,72)) *)
  0xe8; 0x39; 0x11; 0x00; 0x00;
                           (* CALL (Imm32 (word 4409)) *)
  0x48; 0x8b; 0xbc; 0x24; 0x00; 0x02; 0x00; 0x00;
                           (* MOV (% rdi) (Memop Quadword (%% (rsp,512))) *)
  0xf9;                    (* STCF *)
  0x48; 0x8b; 0x07;        (* MOV (% rax) (Memop Quadword (%% (rdi,0))) *)
  0x48; 0x13; 0x04; 0x24;  (* ADC (% rax) (Memop Quadword (%% (rsp,0))) *)
  0x48; 0x8b; 0x5f; 0x08;  (* MOV (% rbx) (Memop Quadword (%% (rdi,8))) *)
  0x48; 0x13; 0x5c; 0x24; 0x08;
                           (* ADC (% rbx) (Memop Quadword (%% (rsp,8))) *)
  0x4c; 0x8b; 0x47; 0x10;  (* MOV (% r8) (Memop Quadword (%% (rdi,16))) *)
  0x4c; 0x13; 0x44; 0x24; 0x10;
                           (* ADC (% r8) (Memop Quadword (%% (rsp,16))) *)
  0x4c; 0x8b; 0x4f; 0x18;  (* MOV (% r9) (Memop Quadword (%% (rdi,24))) *)
  0x4c; 0x13; 0x4c; 0x24; 0x18;
                           (* ADC (% r9) (Memop Quadword (%% (rsp,24))) *)
  0x4c; 0x8b; 0x57; 0x20;  (* MOV (% r10) (Memop Quadword (%% (rdi,32))) *)
  0x4c; 0x13; 0x54; 0x24; 0x20;
                           (* ADC (% r10) (Memop Quadword (%% (rsp,32))) *)
  0x4c; 0x8b; 0x5f; 0x28;  (* MOV (% r11) (Memop Quadword (%% (rdi,40))) *)
  0x4c; 0x13; 0x5c; 0x24; 0x28;
                           (* ADC (% r11) (Memop Quadword (%% (rsp,40))) *)
  0x4c; 0x8b; 0x67; 0x30;  (* MOV (% r12) (Memop Quadword (%% (rdi,48))) *)
  0x4c; 0x13; 0x64; 0x24; 0x30;
                           (* ADC (% r12) (Memop Quadword (%% (rsp,48))) *)
  0x4c; 0x8b; 0x6f; 0x38;  (* MOV (% r13) (Memop Quadword (%% (rdi,56))) *)
  0x4c; 0x13; 0x6c; 0x24; 0x38;
                           (* ADC (% r13) (Memop Quadword (%% (rsp,56))) *)
  0x4c; 0x8b; 0x77; 0x40;  (* MOV (% r14) (Memop Quadword (%% (rdi,64))) *)
  0x4c; 0x13; 0x74; 0x24; 0x40;
                           (* ADC (% r14) (Memop Quadword (%% (rsp,64))) *)
  0x48; 0xc7; 0xc2; 0x00; 0x02; 0x00; 0x00;
                           (* MOV (% rdx) (Imm32 (word 512)) *)
  0x4c; 0x21; 0xf2;        (* AND (% rdx) (% r14) *)
  0x48; 0x81; 0xfa; 0x00; 0x02; 0x00; 0x00;
                           (* CMP (% rdx) (Imm32 (word 512)) *)
  0x48; 0x83; 0xd8; 0x00;  (* SBB (% rax) (Imm8 (word 0)) *)
  0x48; 0x89; 0x84; 0x24; 0x68; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,360))) (% rax) *)
  0x48; 0x83; 0xdb; 0x00;  (* SBB (% rbx) (Imm8 (word 0)) *)
  0x48; 0x89; 0x9c; 0x24; 0x70; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,368))) (% rbx) *)
  0x49; 0x83; 0xd8; 0x00;  (* SBB (% r8) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x84; 0x24; 0x78; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,376))) (% r8) *)
  0x49; 0x83; 0xd9; 0x00;  (* SBB (% r9) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x8c; 0x24; 0x80; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,384))) (% r9) *)
  0x49; 0x83; 0xda; 0x00;  (* SBB (% r10) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x94; 0x24; 0x88; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,392))) (% r10) *)
  0x49; 0x83; 0xdb; 0x00;  (* SBB (% r11) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x9c; 0x24; 0x90; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,400))) (% r11) *)
  0x49; 0x83; 0xdc; 0x00;  (* SBB (% r12) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xa4; 0x24; 0x98; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,408))) (% r12) *)
  0x49; 0x83; 0xdd; 0x00;  (* SBB (% r13) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xac; 0x24; 0xa0; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,416))) (% r13) *)
  0x49; 0x19; 0xd6;        (* SBB (% r14) (% rdx) *)
  0x4c; 0x89; 0xb4; 0x24; 0xa8; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,424))) (% r14) *)
  0x48; 0x8b; 0xbc; 0x24; 0x00; 0x02; 0x00; 0x00;
                           (* MOV (% rdi) (Memop Quadword (%% (rsp,512))) *)
  0x48; 0x8b; 0x07;        (* MOV (% rax) (Memop Quadword (%% (rdi,0))) *)
  0x48; 0x2b; 0x04; 0x24;  (* SUB (% rax) (Memop Quadword (%% (rsp,0))) *)
  0x48; 0x8b; 0x57; 0x08;  (* MOV (% rdx) (Memop Quadword (%% (rdi,8))) *)
  0x48; 0x1b; 0x54; 0x24; 0x08;
                           (* SBB (% rdx) (Memop Quadword (%% (rsp,8))) *)
  0x4c; 0x8b; 0x47; 0x10;  (* MOV (% r8) (Memop Quadword (%% (rdi,16))) *)
  0x4c; 0x1b; 0x44; 0x24; 0x10;
                           (* SBB (% r8) (Memop Quadword (%% (rsp,16))) *)
  0x4c; 0x8b; 0x4f; 0x18;  (* MOV (% r9) (Memop Quadword (%% (rdi,24))) *)
  0x4c; 0x1b; 0x4c; 0x24; 0x18;
                           (* SBB (% r9) (Memop Quadword (%% (rsp,24))) *)
  0x4c; 0x8b; 0x57; 0x20;  (* MOV (% r10) (Memop Quadword (%% (rdi,32))) *)
  0x4c; 0x1b; 0x54; 0x24; 0x20;
                           (* SBB (% r10) (Memop Quadword (%% (rsp,32))) *)
  0x4c; 0x8b; 0x5f; 0x28;  (* MOV (% r11) (Memop Quadword (%% (rdi,40))) *)
  0x4c; 0x1b; 0x5c; 0x24; 0x28;
                           (* SBB (% r11) (Memop Quadword (%% (rsp,40))) *)
  0x4c; 0x8b; 0x67; 0x30;  (* MOV (% r12) (Memop Quadword (%% (rdi,48))) *)
  0x4c; 0x1b; 0x64; 0x24; 0x30;
                           (* SBB (% r12) (Memop Quadword (%% (rsp,48))) *)
  0x4c; 0x8b; 0x6f; 0x38;  (* MOV (% r13) (Memop Quadword (%% (rdi,56))) *)
  0x4c; 0x1b; 0x6c; 0x24; 0x38;
                           (* SBB (% r13) (Memop Quadword (%% (rsp,56))) *)
  0x4c; 0x8b; 0x77; 0x40;  (* MOV (% r14) (Memop Quadword (%% (rdi,64))) *)
  0x4c; 0x1b; 0x74; 0x24; 0x40;
                           (* SBB (% r14) (Memop Quadword (%% (rsp,64))) *)
  0x48; 0x83; 0xd8; 0x00;  (* SBB (% rax) (Imm8 (word 0)) *)
  0x48; 0x89; 0x84; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,288))) (% rax) *)
  0x48; 0x83; 0xda; 0x00;  (* SBB (% rdx) (Imm8 (word 0)) *)
  0x48; 0x89; 0x94; 0x24; 0x28; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,296))) (% rdx) *)
  0x49; 0x83; 0xd8; 0x00;  (* SBB (% r8) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x84; 0x24; 0x30; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,304))) (% r8) *)
  0x49; 0x83; 0xd9; 0x00;  (* SBB (% r9) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x8c; 0x24; 0x38; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,312))) (% r9) *)
  0x49; 0x83; 0xda; 0x00;  (* SBB (% r10) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x94; 0x24; 0x40; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,320))) (% r10) *)
  0x49; 0x83; 0xdb; 0x00;  (* SBB (% r11) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x9c; 0x24; 0x48; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,328))) (% r11) *)
  0x49; 0x83; 0xdc; 0x00;  (* SBB (% r12) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xa4; 0x24; 0x50; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,336))) (% r12) *)
  0x49; 0x83; 0xdd; 0x00;  (* SBB (% r13) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xac; 0x24; 0x58; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,344))) (% r13) *)
  0x49; 0x83; 0xde; 0x00;  (* SBB (% r14) (Imm8 (word 0)) *)
  0x49; 0x81; 0xe6; 0xff; 0x01; 0x00; 0x00;
                           (* AND (% r14) (Imm32 (word 511)) *)
  0x4c; 0x89; 0xb4; 0x24; 0x60; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,352))) (% r14) *)
  0x48; 0x8d; 0x94; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* LEA (% rdx) (%% (rsp,288)) *)
  0x48; 0x8d; 0xb4; 0x24; 0x68; 0x01; 0x00; 0x00;
                           (* LEA (% rsi) (%% (rsp,360)) *)
  0x48; 0x8d; 0xbc; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rsp,144)) *)
  0xe8; 0xe4; 0x08; 0x00; 0x00;
                           (* CALL (Imm32 (word 2276)) *)
  0x48; 0x8b; 0xbc; 0x24; 0x00; 0x02; 0x00; 0x00;
                           (* MOV (% rdi) (Memop Quadword (%% (rsp,512))) *)
  0xf9;                    (* STCF *)
  0x48; 0x8b; 0x47; 0x48;  (* MOV (% rax) (Memop Quadword (%% (rdi,72))) *)
  0x48; 0x13; 0x87; 0x90; 0x00; 0x00; 0x00;
                           (* ADC (% rax) (Memop Quadword (%% (rdi,144))) *)
  0x48; 0x8b; 0x5f; 0x50;  (* MOV (% rbx) (Memop Quadword (%% (rdi,80))) *)
  0x48; 0x13; 0x9f; 0x98; 0x00; 0x00; 0x00;
                           (* ADC (% rbx) (Memop Quadword (%% (rdi,152))) *)
  0x4c; 0x8b; 0x47; 0x58;  (* MOV (% r8) (Memop Quadword (%% (rdi,88))) *)
  0x4c; 0x13; 0x87; 0xa0; 0x00; 0x00; 0x00;
                           (* ADC (% r8) (Memop Quadword (%% (rdi,160))) *)
  0x4c; 0x8b; 0x4f; 0x60;  (* MOV (% r9) (Memop Quadword (%% (rdi,96))) *)
  0x4c; 0x13; 0x8f; 0xa8; 0x00; 0x00; 0x00;
                           (* ADC (% r9) (Memop Quadword (%% (rdi,168))) *)
  0x4c; 0x8b; 0x57; 0x68;  (* MOV (% r10) (Memop Quadword (%% (rdi,104))) *)
  0x4c; 0x13; 0x97; 0xb0; 0x00; 0x00; 0x00;
                           (* ADC (% r10) (Memop Quadword (%% (rdi,176))) *)
  0x4c; 0x8b; 0x5f; 0x70;  (* MOV (% r11) (Memop Quadword (%% (rdi,112))) *)
  0x4c; 0x13; 0x9f; 0xb8; 0x00; 0x00; 0x00;
                           (* ADC (% r11) (Memop Quadword (%% (rdi,184))) *)
  0x4c; 0x8b; 0x67; 0x78;  (* MOV (% r12) (Memop Quadword (%% (rdi,120))) *)
  0x4c; 0x13; 0xa7; 0xc0; 0x00; 0x00; 0x00;
                           (* ADC (% r12) (Memop Quadword (%% (rdi,192))) *)
  0x4c; 0x8b; 0xaf; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (% r13) (Memop Quadword (%% (rdi,128))) *)
  0x4c; 0x13; 0xaf; 0xc8; 0x00; 0x00; 0x00;
                           (* ADC (% r13) (Memop Quadword (%% (rdi,200))) *)
  0x4c; 0x8b; 0xb7; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (% r14) (Memop Quadword (%% (rdi,136))) *)
  0x4c; 0x13; 0xb7; 0xd0; 0x00; 0x00; 0x00;
                           (* ADC (% r14) (Memop Quadword (%% (rdi,208))) *)
  0x48; 0xc7; 0xc2; 0x00; 0x02; 0x00; 0x00;
                           (* MOV (% rdx) (Imm32 (word 512)) *)
  0x4c; 0x21; 0xf2;        (* AND (% rdx) (% r14) *)
  0x48; 0x81; 0xfa; 0x00; 0x02; 0x00; 0x00;
                           (* CMP (% rdx) (Imm32 (word 512)) *)
  0x48; 0x83; 0xd8; 0x00;  (* SBB (% rax) (Imm8 (word 0)) *)
  0x48; 0x89; 0x84; 0x24; 0x68; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,360))) (% rax) *)
  0x48; 0x83; 0xdb; 0x00;  (* SBB (% rbx) (Imm8 (word 0)) *)
  0x48; 0x89; 0x9c; 0x24; 0x70; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,368))) (% rbx) *)
  0x49; 0x83; 0xd8; 0x00;  (* SBB (% r8) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x84; 0x24; 0x78; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,376))) (% r8) *)
  0x49; 0x83; 0xd9; 0x00;  (* SBB (% r9) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x8c; 0x24; 0x80; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,384))) (% r9) *)
  0x49; 0x83; 0xda; 0x00;  (* SBB (% r10) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x94; 0x24; 0x88; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,392))) (% r10) *)
  0x49; 0x83; 0xdb; 0x00;  (* SBB (% r11) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x9c; 0x24; 0x90; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,400))) (% r11) *)
  0x49; 0x83; 0xdc; 0x00;  (* SBB (% r12) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xa4; 0x24; 0x98; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,408))) (% r12) *)
  0x49; 0x83; 0xdd; 0x00;  (* SBB (% r13) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xac; 0x24; 0xa0; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,416))) (% r13) *)
  0x49; 0x19; 0xd6;        (* SBB (% r14) (% rdx) *)
  0x4c; 0x89; 0xb4; 0x24; 0xa8; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,424))) (% r14) *)
  0x48; 0x8d; 0xb4; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* LEA (% rsi) (%% (rsp,144)) *)
  0x48; 0x8d; 0xbc; 0x24; 0xb0; 0x01; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rsp,432)) *)
  0xe8; 0x7b; 0x0e; 0x00; 0x00;
                           (* CALL (Imm32 (word 3707)) *)
  0x48; 0x8b; 0xbc; 0x24; 0x00; 0x02; 0x00; 0x00;
                           (* MOV (% rdi) (Memop Quadword (%% (rsp,512))) *)
  0x48; 0x8d; 0x54; 0x24; 0x48;
                           (* LEA (% rdx) (%% (rsp,72)) *)
  0x48; 0x8d; 0x37;        (* LEA (% rsi) (%% (rdi,0)) *)
  0x48; 0x8d; 0xbc; 0x24; 0xd8; 0x00; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rsp,216)) *)
  0xe8; 0xc4; 0x07; 0x00; 0x00;
                           (* CALL (Imm32 (word 1988)) *)
  0x48; 0x8d; 0xb4; 0x24; 0x68; 0x01; 0x00; 0x00;
                           (* LEA (% rsi) (%% (rsp,360)) *)
  0x48; 0x8d; 0xbc; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rsp,288)) *)
  0xe8; 0x49; 0x0e; 0x00; 0x00;
                           (* CALL (Imm32 (word 3657)) *)
  0x48; 0xc7; 0xc1; 0x09; 0x00; 0x00; 0x00;
                           (* MOV (% rcx) (Imm32 (word 9)) *)
  0x48; 0x8b; 0x84; 0x24; 0xb0; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,432))) *)
  0x48; 0xf7; 0xd0;        (* NOT (% rax) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x48; 0x8b; 0x84; 0x24; 0xb8; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,440))) *)
  0x48; 0xf7; 0xd0;        (* NOT (% rax) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x45; 0x31; 0xd2;        (* XOR (% r10d) (% r10d) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x8b; 0x84; 0x24; 0xc0; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,448))) *)
  0x48; 0xf7; 0xd0;        (* NOT (% rax) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x45; 0x31; 0xdb;        (* XOR (% r11d) (% r11d) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x8b; 0x84; 0x24; 0xc8; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,456))) *)
  0x48; 0xf7; 0xd0;        (* NOT (% rax) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x45; 0x31; 0xe4;        (* XOR (% r12d) (% r12d) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x48; 0x8b; 0x84; 0x24; 0xd0; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,464))) *)
  0x48; 0xf7; 0xd0;        (* NOT (% rax) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x45; 0x31; 0xed;        (* XOR (% r13d) (% r13d) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x48; 0x8b; 0x84; 0x24; 0xd8; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,472))) *)
  0x48; 0xf7; 0xd0;        (* NOT (% rax) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x45; 0x31; 0xf6;        (* XOR (% r14d) (% r14d) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x48; 0x8b; 0x84; 0x24; 0xe0; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,480))) *)
  0x48; 0xf7; 0xd0;        (* NOT (% rax) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x45; 0x31; 0xff;        (* XOR (% r15d) (% r15d) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0x48; 0x8b; 0x84; 0x24; 0xe8; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,488))) *)
  0x48; 0xf7; 0xd0;        (* NOT (% rax) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x31; 0xdb;              (* XOR (% ebx) (% ebx) *)
  0x49; 0x01; 0xc7;        (* ADD (% r15) (% rax) *)
  0x48; 0x11; 0xd3;        (* ADC (% rbx) (% rdx) *)
  0x48; 0x8b; 0x84; 0x24; 0xf0; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,496))) *)
  0x48; 0x35; 0xff; 0x01; 0x00; 0x00;
                           (* XOR (% rax) (Imm32 (word 511)) *)
  0x48; 0x0f; 0xaf; 0xc1;  (* IMUL (% rax) (% rcx) *)
  0x48; 0x01; 0xc3;        (* ADD (% rbx) (% rax) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0xb9; 0x0c; 0x00; 0x00; 0x00;
                           (* MOV (% ecx) (Imm32 (word 12)) *)
  0x48; 0x8b; 0x84; 0x24; 0xd8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,216))) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0x8b; 0x84; 0x24; 0xe0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,224))) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x48; 0x29; 0xea;        (* SUB (% rdx) (% rbp) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0x8b; 0x84; 0x24; 0xe8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,232))) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x48; 0x29; 0xea;        (* SUB (% rdx) (% rbp) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0x8b; 0x84; 0x24; 0xf0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,240))) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x48; 0x29; 0xea;        (* SUB (% rdx) (% rbp) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0x8b; 0x84; 0x24; 0xf8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,248))) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x48; 0x29; 0xea;        (* SUB (% rdx) (% rbp) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0x8b; 0x84; 0x24; 0x00; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,256))) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x48; 0x29; 0xea;        (* SUB (% rdx) (% rbp) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0x8b; 0x84; 0x24; 0x08; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,264))) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x48; 0x29; 0xea;        (* SUB (% rdx) (% rbp) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0x8b; 0x84; 0x24; 0x10; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,272))) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x48; 0x29; 0xea;        (* SUB (% rdx) (% rbp) *)
  0x49; 0x01; 0xc7;        (* ADD (% r15) (% rax) *)
  0x48; 0x11; 0xd3;        (* ADC (% rbx) (% rdx) *)
  0x48; 0x8b; 0x84; 0x24; 0x18; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,280))) *)
  0x48; 0x0f; 0xaf; 0xc1;  (* IMUL (% rax) (% rcx) *)
  0x48; 0x01; 0xc3;        (* ADD (% rbx) (% rax) *)
  0x4c; 0x89; 0xc8;        (* MOV (% rax) (% r9) *)
  0x4c; 0x21; 0xd0;        (* AND (% rax) (% r10) *)
  0x4c; 0x21; 0xd8;        (* AND (% rax) (% r11) *)
  0x4c; 0x21; 0xe0;        (* AND (% rax) (% r12) *)
  0x4c; 0x21; 0xe8;        (* AND (% rax) (% r13) *)
  0x4c; 0x21; 0xf0;        (* AND (% rax) (% r14) *)
  0x4c; 0x21; 0xf8;        (* AND (% rax) (% r15) *)
  0x48; 0x89; 0xda;        (* MOV (% rdx) (% rbx) *)
  0x48; 0xc1; 0xea; 0x09;  (* SHR (% rdx) (Imm8 (word 9)) *)
  0x48; 0x81; 0xcb; 0x00; 0xfe; 0xff; 0xff;
                           (* OR (% rbx) (Imm32 (word 4294966784)) *)
  0x48; 0x8d; 0x4a; 0x01;  (* LEA (% rcx) (%% (rdx,1)) *)
  0x4c; 0x01; 0xc1;        (* ADD (% rcx) (% r8) *)
  0xb9; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% ecx) (Imm32 (word 0)) *)
  0x48; 0x11; 0xc8;        (* ADC (% rax) (% rcx) *)
  0x48; 0x89; 0xd8;        (* MOV (% rax) (% rbx) *)
  0x48; 0x11; 0xc8;        (* ADC (% rax) (% rcx) *)
  0x49; 0x11; 0xd0;        (* ADC (% r8) (% rdx) *)
  0x4c; 0x89; 0x84; 0x24; 0xb0; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,432))) (% r8) *)
  0x49; 0x11; 0xc9;        (* ADC (% r9) (% rcx) *)
  0x4c; 0x89; 0x8c; 0x24; 0xb8; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,440))) (% r9) *)
  0x49; 0x11; 0xca;        (* ADC (% r10) (% rcx) *)
  0x4c; 0x89; 0x94; 0x24; 0xc0; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,448))) (% r10) *)
  0x49; 0x11; 0xcb;        (* ADC (% r11) (% rcx) *)
  0x4c; 0x89; 0x9c; 0x24; 0xc8; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,456))) (% r11) *)
  0x49; 0x11; 0xcc;        (* ADC (% r12) (% rcx) *)
  0x4c; 0x89; 0xa4; 0x24; 0xd0; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,464))) (% r12) *)
  0x49; 0x11; 0xcd;        (* ADC (% r13) (% rcx) *)
  0x4c; 0x89; 0xac; 0x24; 0xd8; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,472))) (% r13) *)
  0x49; 0x11; 0xce;        (* ADC (% r14) (% rcx) *)
  0x4c; 0x89; 0xb4; 0x24; 0xe0; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,480))) (% r14) *)
  0x49; 0x11; 0xcf;        (* ADC (% r15) (% rcx) *)
  0x4c; 0x89; 0xbc; 0x24; 0xe8; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,488))) (% r15) *)
  0x48; 0x11; 0xcb;        (* ADC (% rbx) (% rcx) *)
  0x48; 0x81; 0xe3; 0xff; 0x01; 0x00; 0x00;
                           (* AND (% rbx) (Imm32 (word 511)) *)
  0x48; 0x89; 0x9c; 0x24; 0xf0; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,496))) (% rbx) *)
  0x48; 0x8b; 0x84; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,288))) *)
  0x48; 0x2b; 0x04; 0x24;  (* SUB (% rax) (Memop Quadword (%% (rsp,0))) *)
  0x48; 0x8b; 0x94; 0x24; 0x28; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,296))) *)
  0x48; 0x1b; 0x54; 0x24; 0x08;
                           (* SBB (% rdx) (Memop Quadword (%% (rsp,8))) *)
  0x4c; 0x8b; 0x84; 0x24; 0x30; 0x01; 0x00; 0x00;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,304))) *)
  0x4c; 0x1b; 0x44; 0x24; 0x10;
                           (* SBB (% r8) (Memop Quadword (%% (rsp,16))) *)
  0x4c; 0x8b; 0x8c; 0x24; 0x38; 0x01; 0x00; 0x00;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,312))) *)
  0x4c; 0x1b; 0x4c; 0x24; 0x18;
                           (* SBB (% r9) (Memop Quadword (%% (rsp,24))) *)
  0x4c; 0x8b; 0x94; 0x24; 0x40; 0x01; 0x00; 0x00;
                           (* MOV (% r10) (Memop Quadword (%% (rsp,320))) *)
  0x4c; 0x1b; 0x54; 0x24; 0x20;
                           (* SBB (% r10) (Memop Quadword (%% (rsp,32))) *)
  0x4c; 0x8b; 0x9c; 0x24; 0x48; 0x01; 0x00; 0x00;
                           (* MOV (% r11) (Memop Quadword (%% (rsp,328))) *)
  0x4c; 0x1b; 0x5c; 0x24; 0x28;
                           (* SBB (% r11) (Memop Quadword (%% (rsp,40))) *)
  0x4c; 0x8b; 0xa4; 0x24; 0x50; 0x01; 0x00; 0x00;
                           (* MOV (% r12) (Memop Quadword (%% (rsp,336))) *)
  0x4c; 0x1b; 0x64; 0x24; 0x30;
                           (* SBB (% r12) (Memop Quadword (%% (rsp,48))) *)
  0x4c; 0x8b; 0xac; 0x24; 0x58; 0x01; 0x00; 0x00;
                           (* MOV (% r13) (Memop Quadword (%% (rsp,344))) *)
  0x4c; 0x1b; 0x6c; 0x24; 0x38;
                           (* SBB (% r13) (Memop Quadword (%% (rsp,56))) *)
  0x4c; 0x8b; 0xb4; 0x24; 0x60; 0x01; 0x00; 0x00;
                           (* MOV (% r14) (Memop Quadword (%% (rsp,352))) *)
  0x4c; 0x1b; 0x74; 0x24; 0x40;
                           (* SBB (% r14) (Memop Quadword (%% (rsp,64))) *)
  0x48; 0x83; 0xd8; 0x00;  (* SBB (% rax) (Imm8 (word 0)) *)
  0x48; 0x89; 0x84; 0x24; 0x68; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,360))) (% rax) *)
  0x48; 0x83; 0xda; 0x00;  (* SBB (% rdx) (Imm8 (word 0)) *)
  0x48; 0x89; 0x94; 0x24; 0x70; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,368))) (% rdx) *)
  0x49; 0x83; 0xd8; 0x00;  (* SBB (% r8) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x84; 0x24; 0x78; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,376))) (% r8) *)
  0x49; 0x83; 0xd9; 0x00;  (* SBB (% r9) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x8c; 0x24; 0x80; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,384))) (% r9) *)
  0x49; 0x83; 0xda; 0x00;  (* SBB (% r10) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x94; 0x24; 0x88; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,392))) (% r10) *)
  0x49; 0x83; 0xdb; 0x00;  (* SBB (% r11) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x9c; 0x24; 0x90; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,400))) (% r11) *)
  0x49; 0x83; 0xdc; 0x00;  (* SBB (% r12) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xa4; 0x24; 0x98; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,408))) (% r12) *)
  0x49; 0x83; 0xdd; 0x00;  (* SBB (% r13) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xac; 0x24; 0xa0; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,416))) (% r13) *)
  0x49; 0x83; 0xde; 0x00;  (* SBB (% r14) (Imm8 (word 0)) *)
  0x49; 0x81; 0xe6; 0xff; 0x01; 0x00; 0x00;
                           (* AND (% r14) (Imm32 (word 511)) *)
  0x4c; 0x89; 0xb4; 0x24; 0xa8; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,424))) (% r14) *)
  0x48; 0x8d; 0x74; 0x24; 0x48;
                           (* LEA (% rsi) (%% (rsp,72)) *)
  0x48; 0x8d; 0xbc; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rsp,288)) *)
  0xe8; 0x16; 0x0b; 0x00; 0x00;
                           (* CALL (Imm32 (word 2838)) *)
  0x48; 0x8b; 0xbc; 0x24; 0xf8; 0x01; 0x00; 0x00;
                           (* MOV (% rdi) (Memop Quadword (%% (rsp,504))) *)
  0x48; 0x8b; 0x84; 0x24; 0x68; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,360))) *)
  0x48; 0x2b; 0x44; 0x24; 0x48;
                           (* SUB (% rax) (Memop Quadword (%% (rsp,72))) *)
  0x48; 0x8b; 0x94; 0x24; 0x70; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,368))) *)
  0x48; 0x1b; 0x54; 0x24; 0x50;
                           (* SBB (% rdx) (Memop Quadword (%% (rsp,80))) *)
  0x4c; 0x8b; 0x84; 0x24; 0x78; 0x01; 0x00; 0x00;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,376))) *)
  0x4c; 0x1b; 0x44; 0x24; 0x58;
                           (* SBB (% r8) (Memop Quadword (%% (rsp,88))) *)
  0x4c; 0x8b; 0x8c; 0x24; 0x80; 0x01; 0x00; 0x00;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,384))) *)
  0x4c; 0x1b; 0x4c; 0x24; 0x60;
                           (* SBB (% r9) (Memop Quadword (%% (rsp,96))) *)
  0x4c; 0x8b; 0x94; 0x24; 0x88; 0x01; 0x00; 0x00;
                           (* MOV (% r10) (Memop Quadword (%% (rsp,392))) *)
  0x4c; 0x1b; 0x54; 0x24; 0x68;
                           (* SBB (% r10) (Memop Quadword (%% (rsp,104))) *)
  0x4c; 0x8b; 0x9c; 0x24; 0x90; 0x01; 0x00; 0x00;
                           (* MOV (% r11) (Memop Quadword (%% (rsp,400))) *)
  0x4c; 0x1b; 0x5c; 0x24; 0x70;
                           (* SBB (% r11) (Memop Quadword (%% (rsp,112))) *)
  0x4c; 0x8b; 0xa4; 0x24; 0x98; 0x01; 0x00; 0x00;
                           (* MOV (% r12) (Memop Quadword (%% (rsp,408))) *)
  0x4c; 0x1b; 0x64; 0x24; 0x78;
                           (* SBB (% r12) (Memop Quadword (%% (rsp,120))) *)
  0x4c; 0x8b; 0xac; 0x24; 0xa0; 0x01; 0x00; 0x00;
                           (* MOV (% r13) (Memop Quadword (%% (rsp,416))) *)
  0x4c; 0x1b; 0xac; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* SBB (% r13) (Memop Quadword (%% (rsp,128))) *)
  0x4c; 0x8b; 0xb4; 0x24; 0xa8; 0x01; 0x00; 0x00;
                           (* MOV (% r14) (Memop Quadword (%% (rsp,424))) *)
  0x4c; 0x1b; 0xb4; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* SBB (% r14) (Memop Quadword (%% (rsp,136))) *)
  0x48; 0x83; 0xd8; 0x00;  (* SBB (% rax) (Imm8 (word 0)) *)
  0x48; 0x89; 0x87; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,144))) (% rax) *)
  0x48; 0x83; 0xda; 0x00;  (* SBB (% rdx) (Imm8 (word 0)) *)
  0x48; 0x89; 0x97; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,152))) (% rdx) *)
  0x49; 0x83; 0xd8; 0x00;  (* SBB (% r8) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x87; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,160))) (% r8) *)
  0x49; 0x83; 0xd9; 0x00;  (* SBB (% r9) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x8f; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,168))) (% r9) *)
  0x49; 0x83; 0xda; 0x00;  (* SBB (% r10) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x97; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,176))) (% r10) *)
  0x49; 0x83; 0xdb; 0x00;  (* SBB (% r11) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x9f; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,184))) (% r11) *)
  0x49; 0x83; 0xdc; 0x00;  (* SBB (% r12) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xa7; 0xc0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,192))) (% r12) *)
  0x49; 0x83; 0xdd; 0x00;  (* SBB (% r13) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xaf; 0xc8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,200))) (% r13) *)
  0x49; 0x83; 0xde; 0x00;  (* SBB (% r14) (Imm8 (word 0)) *)
  0x49; 0x81; 0xe6; 0xff; 0x01; 0x00; 0x00;
                           (* AND (% r14) (Imm32 (word 511)) *)
  0x4c; 0x89; 0xb7; 0xd0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,208))) (% r14) *)
  0x48; 0x8d; 0x94; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* LEA (% rdx) (%% (rsp,144)) *)
  0x48; 0x8d; 0xb4; 0x24; 0xb0; 0x01; 0x00; 0x00;
                           (* LEA (% rsi) (%% (rsp,432)) *)
  0x48; 0x8d; 0xbc; 0x24; 0x68; 0x01; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rsp,360)) *)
  0xe8; 0x72; 0x03; 0x00; 0x00;
                           (* CALL (Imm32 (word 882)) *)
  0x48; 0x8b; 0xbc; 0x24; 0xf8; 0x01; 0x00; 0x00;
                           (* MOV (% rdi) (Memop Quadword (%% (rsp,504))) *)
  0x48; 0x8b; 0x9c; 0x24; 0x18; 0x01; 0x00; 0x00;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,280))) *)
  0x4c; 0x8b; 0xbc; 0x24; 0x10; 0x01; 0x00; 0x00;
                           (* MOV (% r15) (Memop Quadword (%% (rsp,272))) *)
  0x4c; 0x0f; 0xa4; 0xfb; 0x02;
                           (* SHLD (% rbx) (% r15) (Imm8 (word 2)) *)
  0x4c; 0x8b; 0xb4; 0x24; 0x08; 0x01; 0x00; 0x00;
                           (* MOV (% r14) (Memop Quadword (%% (rsp,264))) *)
  0x4d; 0x0f; 0xa4; 0xf7; 0x02;
                           (* SHLD (% r15) (% r14) (Imm8 (word 2)) *)
  0x4c; 0x8b; 0xac; 0x24; 0x00; 0x01; 0x00; 0x00;
                           (* MOV (% r13) (Memop Quadword (%% (rsp,256))) *)
  0x4d; 0x0f; 0xa4; 0xee; 0x02;
                           (* SHLD (% r14) (% r13) (Imm8 (word 2)) *)
  0x4c; 0x8b; 0xa4; 0x24; 0xf8; 0x00; 0x00; 0x00;
                           (* MOV (% r12) (Memop Quadword (%% (rsp,248))) *)
  0x4d; 0x0f; 0xa4; 0xe5; 0x02;
                           (* SHLD (% r13) (% r12) (Imm8 (word 2)) *)
  0x4c; 0x8b; 0x9c; 0x24; 0xf0; 0x00; 0x00; 0x00;
                           (* MOV (% r11) (Memop Quadword (%% (rsp,240))) *)
  0x4d; 0x0f; 0xa4; 0xdc; 0x02;
                           (* SHLD (% r12) (% r11) (Imm8 (word 2)) *)
  0x4c; 0x8b; 0x94; 0x24; 0xe8; 0x00; 0x00; 0x00;
                           (* MOV (% r10) (Memop Quadword (%% (rsp,232))) *)
  0x4d; 0x0f; 0xa4; 0xd3; 0x02;
                           (* SHLD (% r11) (% r10) (Imm8 (word 2)) *)
  0x4c; 0x8b; 0x8c; 0x24; 0xe0; 0x00; 0x00; 0x00;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,224))) *)
  0x4d; 0x0f; 0xa4; 0xca; 0x02;
                           (* SHLD (% r10) (% r9) (Imm8 (word 2)) *)
  0x4c; 0x8b; 0x84; 0x24; 0xd8; 0x00; 0x00; 0x00;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,216))) *)
  0x4d; 0x0f; 0xa4; 0xc1; 0x02;
                           (* SHLD (% r9) (% r8) (Imm8 (word 2)) *)
  0x49; 0xc1; 0xe0; 0x02;  (* SHL (% r8) (Imm8 (word 2)) *)
  0x48; 0x8b; 0x8c; 0x24; 0xf0; 0x01; 0x00; 0x00;
                           (* MOV (% rcx) (Memop Quadword (%% (rsp,496))) *)
  0x48; 0x81; 0xf1; 0xff; 0x01; 0x00; 0x00;
                           (* XOR (% rcx) (Imm32 (word 511)) *)
  0x48; 0x8b; 0x84; 0x24; 0xb0; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,432))) *)
  0x48; 0xf7; 0xd0;        (* NOT (% rax) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0xb8; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,440))) *)
  0x48; 0xf7; 0xd0;        (* NOT (% rax) *)
  0x49; 0x11; 0xc1;        (* ADC (% r9) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0xc0; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,448))) *)
  0x48; 0xf7; 0xd0;        (* NOT (% rax) *)
  0x49; 0x11; 0xc2;        (* ADC (% r10) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0xc8; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,456))) *)
  0x48; 0xf7; 0xd0;        (* NOT (% rax) *)
  0x49; 0x11; 0xc3;        (* ADC (% r11) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0xd0; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,464))) *)
  0x48; 0xf7; 0xd0;        (* NOT (% rax) *)
  0x49; 0x11; 0xc4;        (* ADC (% r12) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0xd8; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,472))) *)
  0x48; 0xf7; 0xd0;        (* NOT (% rax) *)
  0x49; 0x11; 0xc5;        (* ADC (% r13) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0xe0; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,480))) *)
  0x48; 0xf7; 0xd0;        (* NOT (% rax) *)
  0x49; 0x11; 0xc6;        (* ADC (% r14) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0xe8; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,488))) *)
  0x48; 0xf7; 0xd0;        (* NOT (% rax) *)
  0x49; 0x11; 0xc7;        (* ADC (% r15) (% rax) *)
  0x48; 0x11; 0xcb;        (* ADC (% rbx) (% rcx) *)
  0x4c; 0x89; 0xc8;        (* MOV (% rax) (% r9) *)
  0x4c; 0x21; 0xd0;        (* AND (% rax) (% r10) *)
  0x4c; 0x21; 0xd8;        (* AND (% rax) (% r11) *)
  0x4c; 0x21; 0xe0;        (* AND (% rax) (% r12) *)
  0x4c; 0x21; 0xe8;        (* AND (% rax) (% r13) *)
  0x4c; 0x21; 0xf0;        (* AND (% rax) (% r14) *)
  0x4c; 0x21; 0xf8;        (* AND (% rax) (% r15) *)
  0x48; 0x89; 0xda;        (* MOV (% rdx) (% rbx) *)
  0x48; 0xc1; 0xea; 0x09;  (* SHR (% rdx) (Imm8 (word 9)) *)
  0x48; 0x81; 0xcb; 0x00; 0xfe; 0xff; 0xff;
                           (* OR (% rbx) (Imm32 (word 4294966784)) *)
  0x48; 0x8d; 0x4a; 0x01;  (* LEA (% rcx) (%% (rdx,1)) *)
  0x4c; 0x01; 0xc1;        (* ADD (% rcx) (% r8) *)
  0xb9; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% ecx) (Imm32 (word 0)) *)
  0x48; 0x11; 0xc8;        (* ADC (% rax) (% rcx) *)
  0x48; 0x89; 0xd8;        (* MOV (% rax) (% rbx) *)
  0x48; 0x11; 0xc8;        (* ADC (% rax) (% rcx) *)
  0x49; 0x11; 0xd0;        (* ADC (% r8) (% rdx) *)
  0x4c; 0x89; 0x07;        (* MOV (Memop Quadword (%% (rdi,0))) (% r8) *)
  0x49; 0x11; 0xc9;        (* ADC (% r9) (% rcx) *)
  0x4c; 0x89; 0x4f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% r9) *)
  0x49; 0x11; 0xca;        (* ADC (% r10) (% rcx) *)
  0x4c; 0x89; 0x57; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r10) *)
  0x49; 0x11; 0xcb;        (* ADC (% r11) (% rcx) *)
  0x4c; 0x89; 0x5f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r11) *)
  0x49; 0x11; 0xcc;        (* ADC (% r12) (% rcx) *)
  0x4c; 0x89; 0x67; 0x20;  (* MOV (Memop Quadword (%% (rdi,32))) (% r12) *)
  0x49; 0x11; 0xcd;        (* ADC (% r13) (% rcx) *)
  0x4c; 0x89; 0x6f; 0x28;  (* MOV (Memop Quadword (%% (rdi,40))) (% r13) *)
  0x49; 0x11; 0xce;        (* ADC (% r14) (% rcx) *)
  0x4c; 0x89; 0x77; 0x30;  (* MOV (Memop Quadword (%% (rdi,48))) (% r14) *)
  0x49; 0x11; 0xcf;        (* ADC (% r15) (% rcx) *)
  0x4c; 0x89; 0x7f; 0x38;  (* MOV (Memop Quadword (%% (rdi,56))) (% r15) *)
  0x48; 0x11; 0xcb;        (* ADC (% rbx) (% rcx) *)
  0x48; 0x81; 0xe3; 0xff; 0x01; 0x00; 0x00;
                           (* AND (% rbx) (Imm32 (word 511)) *)
  0x48; 0x89; 0x5f; 0x40;  (* MOV (Memop Quadword (%% (rdi,64))) (% rbx) *)
  0x48; 0x8b; 0xbc; 0x24; 0xf8; 0x01; 0x00; 0x00;
                           (* MOV (% rdi) (Memop Quadword (%% (rsp,504))) *)
  0x48; 0x8b; 0x9c; 0x24; 0x60; 0x01; 0x00; 0x00;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,352))) *)
  0x48; 0x81; 0xf3; 0xff; 0x01; 0x00; 0x00;
                           (* XOR (% rbx) (Imm32 (word 511)) *)
  0x4c; 0x8b; 0xbc; 0x24; 0x58; 0x01; 0x00; 0x00;
                           (* MOV (% r15) (Memop Quadword (%% (rsp,344))) *)
  0x49; 0xf7; 0xd7;        (* NOT (% r15) *)
  0x4c; 0x0f; 0xa4; 0xfb; 0x03;
                           (* SHLD (% rbx) (% r15) (Imm8 (word 3)) *)
  0x4c; 0x8b; 0xb4; 0x24; 0x50; 0x01; 0x00; 0x00;
                           (* MOV (% r14) (Memop Quadword (%% (rsp,336))) *)
  0x49; 0xf7; 0xd6;        (* NOT (% r14) *)
  0x4d; 0x0f; 0xa4; 0xf7; 0x03;
                           (* SHLD (% r15) (% r14) (Imm8 (word 3)) *)
  0x4c; 0x8b; 0xac; 0x24; 0x48; 0x01; 0x00; 0x00;
                           (* MOV (% r13) (Memop Quadword (%% (rsp,328))) *)
  0x49; 0xf7; 0xd5;        (* NOT (% r13) *)
  0x4d; 0x0f; 0xa4; 0xee; 0x03;
                           (* SHLD (% r14) (% r13) (Imm8 (word 3)) *)
  0x4c; 0x8b; 0xa4; 0x24; 0x40; 0x01; 0x00; 0x00;
                           (* MOV (% r12) (Memop Quadword (%% (rsp,320))) *)
  0x49; 0xf7; 0xd4;        (* NOT (% r12) *)
  0x4d; 0x0f; 0xa4; 0xe5; 0x03;
                           (* SHLD (% r13) (% r12) (Imm8 (word 3)) *)
  0x4c; 0x8b; 0x9c; 0x24; 0x38; 0x01; 0x00; 0x00;
                           (* MOV (% r11) (Memop Quadword (%% (rsp,312))) *)
  0x49; 0xf7; 0xd3;        (* NOT (% r11) *)
  0x4d; 0x0f; 0xa4; 0xdc; 0x03;
                           (* SHLD (% r12) (% r11) (Imm8 (word 3)) *)
  0x4c; 0x8b; 0x94; 0x24; 0x30; 0x01; 0x00; 0x00;
                           (* MOV (% r10) (Memop Quadword (%% (rsp,304))) *)
  0x49; 0xf7; 0xd2;        (* NOT (% r10) *)
  0x4d; 0x0f; 0xa4; 0xd3; 0x03;
                           (* SHLD (% r11) (% r10) (Imm8 (word 3)) *)
  0x4c; 0x8b; 0x8c; 0x24; 0x28; 0x01; 0x00; 0x00;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,296))) *)
  0x49; 0xf7; 0xd1;        (* NOT (% r9) *)
  0x4d; 0x0f; 0xa4; 0xca; 0x03;
                           (* SHLD (% r10) (% r9) (Imm8 (word 3)) *)
  0x4c; 0x8b; 0x84; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,288))) *)
  0x49; 0xf7; 0xd0;        (* NOT (% r8) *)
  0x4d; 0x0f; 0xa4; 0xc1; 0x03;
                           (* SHLD (% r9) (% r8) (Imm8 (word 3)) *)
  0x49; 0xc1; 0xe0; 0x03;  (* SHL (% r8) (Imm8 (word 3)) *)
  0xb9; 0x03; 0x00; 0x00; 0x00;
                           (* MOV (% ecx) (Imm32 (word 3)) *)
  0x48; 0x8b; 0x84; 0x24; 0x68; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,360))) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0x8b; 0x84; 0x24; 0x70; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,368))) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x48; 0x29; 0xea;        (* SUB (% rdx) (% rbp) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0x8b; 0x84; 0x24; 0x78; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,376))) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x48; 0x29; 0xea;        (* SUB (% rdx) (% rbp) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0x8b; 0x84; 0x24; 0x80; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,384))) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x48; 0x29; 0xea;        (* SUB (% rdx) (% rbp) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0x8b; 0x84; 0x24; 0x88; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,392))) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x48; 0x29; 0xea;        (* SUB (% rdx) (% rbp) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0x8b; 0x84; 0x24; 0x90; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,400))) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x48; 0x29; 0xea;        (* SUB (% rdx) (% rbp) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0x8b; 0x84; 0x24; 0x98; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,408))) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x48; 0x29; 0xea;        (* SUB (% rdx) (% rbp) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0x8b; 0x84; 0x24; 0xa0; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,416))) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x48; 0x29; 0xea;        (* SUB (% rdx) (% rbp) *)
  0x49; 0x01; 0xc7;        (* ADD (% r15) (% rax) *)
  0x48; 0x11; 0xd3;        (* ADC (% rbx) (% rdx) *)
  0x48; 0x8b; 0x84; 0x24; 0xa8; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,424))) *)
  0x48; 0x0f; 0xaf; 0xc1;  (* IMUL (% rax) (% rcx) *)
  0x48; 0x01; 0xc3;        (* ADD (% rbx) (% rax) *)
  0x4c; 0x89; 0xc8;        (* MOV (% rax) (% r9) *)
  0x4c; 0x21; 0xd0;        (* AND (% rax) (% r10) *)
  0x4c; 0x21; 0xd8;        (* AND (% rax) (% r11) *)
  0x4c; 0x21; 0xe0;        (* AND (% rax) (% r12) *)
  0x4c; 0x21; 0xe8;        (* AND (% rax) (% r13) *)
  0x4c; 0x21; 0xf0;        (* AND (% rax) (% r14) *)
  0x4c; 0x21; 0xf8;        (* AND (% rax) (% r15) *)
  0x48; 0x89; 0xda;        (* MOV (% rdx) (% rbx) *)
  0x48; 0xc1; 0xea; 0x09;  (* SHR (% rdx) (Imm8 (word 9)) *)
  0x48; 0x81; 0xcb; 0x00; 0xfe; 0xff; 0xff;
                           (* OR (% rbx) (Imm32 (word 4294966784)) *)
  0x48; 0x8d; 0x4a; 0x01;  (* LEA (% rcx) (%% (rdx,1)) *)
  0x4c; 0x01; 0xc1;        (* ADD (% rcx) (% r8) *)
  0xb9; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% ecx) (Imm32 (word 0)) *)
  0x48; 0x11; 0xc8;        (* ADC (% rax) (% rcx) *)
  0x48; 0x89; 0xd8;        (* MOV (% rax) (% rbx) *)
  0x48; 0x11; 0xc8;        (* ADC (% rax) (% rcx) *)
  0x49; 0x11; 0xd0;        (* ADC (% r8) (% rdx) *)
  0x4c; 0x89; 0x47; 0x48;  (* MOV (Memop Quadword (%% (rdi,72))) (% r8) *)
  0x49; 0x11; 0xc9;        (* ADC (% r9) (% rcx) *)
  0x4c; 0x89; 0x4f; 0x50;  (* MOV (Memop Quadword (%% (rdi,80))) (% r9) *)
  0x49; 0x11; 0xca;        (* ADC (% r10) (% rcx) *)
  0x4c; 0x89; 0x57; 0x58;  (* MOV (Memop Quadword (%% (rdi,88))) (% r10) *)
  0x49; 0x11; 0xcb;        (* ADC (% r11) (% rcx) *)
  0x4c; 0x89; 0x5f; 0x60;  (* MOV (Memop Quadword (%% (rdi,96))) (% r11) *)
  0x49; 0x11; 0xcc;        (* ADC (% r12) (% rcx) *)
  0x4c; 0x89; 0x67; 0x68;  (* MOV (Memop Quadword (%% (rdi,104))) (% r12) *)
  0x49; 0x11; 0xcd;        (* ADC (% r13) (% rcx) *)
  0x4c; 0x89; 0x6f; 0x70;  (* MOV (Memop Quadword (%% (rdi,112))) (% r13) *)
  0x49; 0x11; 0xce;        (* ADC (% r14) (% rcx) *)
  0x4c; 0x89; 0x77; 0x78;  (* MOV (Memop Quadword (%% (rdi,120))) (% r14) *)
  0x49; 0x11; 0xcf;        (* ADC (% r15) (% rcx) *)
  0x4c; 0x89; 0xbf; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,128))) (% r15) *)
  0x48; 0x11; 0xcb;        (* ADC (% rbx) (% rcx) *)
  0x48; 0x81; 0xe3; 0xff; 0x01; 0x00; 0x00;
                           (* AND (% rbx) (Imm32 (word 511)) *)
  0x48; 0x89; 0x9f; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,136))) (% rbx) *)
  0x48; 0x81; 0xc4; 0x08; 0x02; 0x00; 0x00;
                           (* ADD (% rsp) (Imm32 (word 520)) *)
  0x41; 0x5f;              (* POP (% r15) *)
  0x41; 0x5e;              (* POP (% r14) *)
  0x41; 0x5d;              (* POP (% r13) *)
  0x41; 0x5c;              (* POP (% r12) *)
  0x5d;                    (* POP (% rbp) *)
  0x5b;                    (* POP (% rbx) *)
  0xc3;                    (* RET *)
  0x48; 0x83; 0xec; 0x48;  (* SUB (% rsp) (Imm8 (word 72)) *)
  0x48; 0x89; 0xd1;        (* MOV (% rcx) (% rdx) *)
  0x48; 0x8b; 0x06;        (* MOV (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0xf7; 0x21;        (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,0))) *)
  0x48; 0x89; 0x04; 0x24;  (* MOV (Memop Quadword (%% (rsp,0))) (% rax) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x48; 0x8b; 0x06;        (* MOV (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0xf7; 0x61; 0x08;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,8))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x8b; 0x46; 0x08;  (* MOV (% rax) (Memop Quadword (%% (rsi,8))) *)
  0x48; 0xf7; 0x21;        (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,0))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x4d; 0x11; 0xdb;        (* ADC (% r11) (% r11) *)
  0x4c; 0x89; 0x4c; 0x24; 0x08;
                           (* MOV (Memop Quadword (%% (rsp,8))) (% r9) *)
  0x4d; 0x31; 0xe4;        (* XOR (% r12) (% r12) *)
  0x48; 0x8b; 0x06;        (* MOV (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0xf7; 0x61; 0x10;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,16))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x4d; 0x11; 0xe4;        (* ADC (% r12) (% r12) *)
  0x48; 0x8b; 0x46; 0x08;  (* MOV (% rax) (Memop Quadword (%% (rsi,8))) *)
  0x48; 0xf7; 0x61; 0x08;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,8))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x10;  (* MOV (% rax) (Memop Quadword (%% (rsi,16))) *)
  0x48; 0xf7; 0x21;        (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,0))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x54; 0x24; 0x10;
                           (* MOV (Memop Quadword (%% (rsp,16))) (% r10) *)
  0x4d; 0x31; 0xed;        (* XOR (% r13) (% r13) *)
  0x48; 0x8b; 0x06;        (* MOV (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0xf7; 0x61; 0x18;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,24))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x4d; 0x11; 0xed;        (* ADC (% r13) (% r13) *)
  0x48; 0x8b; 0x46; 0x08;  (* MOV (% rax) (Memop Quadword (%% (rsi,8))) *)
  0x48; 0xf7; 0x61; 0x10;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,16))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x10;  (* MOV (% rax) (Memop Quadword (%% (rsi,16))) *)
  0x48; 0xf7; 0x61; 0x08;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,8))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x18;  (* MOV (% rax) (Memop Quadword (%% (rsi,24))) *)
  0x48; 0xf7; 0x21;        (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,0))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x5c; 0x24; 0x18;
                           (* MOV (Memop Quadword (%% (rsp,24))) (% r11) *)
  0x4d; 0x31; 0xf6;        (* XOR (% r14) (% r14) *)
  0x48; 0x8b; 0x06;        (* MOV (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0xf7; 0x61; 0x20;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,32))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x4d; 0x11; 0xf6;        (* ADC (% r14) (% r14) *)
  0x48; 0x8b; 0x46; 0x08;  (* MOV (% rax) (Memop Quadword (%% (rsi,8))) *)
  0x48; 0xf7; 0x61; 0x18;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,24))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x10;  (* MOV (% rax) (Memop Quadword (%% (rsi,16))) *)
  0x48; 0xf7; 0x61; 0x10;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,16))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x18;  (* MOV (% rax) (Memop Quadword (%% (rsi,24))) *)
  0x48; 0xf7; 0x61; 0x08;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,8))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x20;  (* MOV (% rax) (Memop Quadword (%% (rsi,32))) *)
  0x48; 0xf7; 0x21;        (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,0))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x64; 0x24; 0x20;
                           (* MOV (Memop Quadword (%% (rsp,32))) (% r12) *)
  0x4d; 0x31; 0xff;        (* XOR (% r15) (% r15) *)
  0x48; 0x8b; 0x06;        (* MOV (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0xf7; 0x61; 0x28;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,40))) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x4d; 0x11; 0xff;        (* ADC (% r15) (% r15) *)
  0x48; 0x8b; 0x46; 0x08;  (* MOV (% rax) (Memop Quadword (%% (rsi,8))) *)
  0x48; 0xf7; 0x61; 0x20;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,32))) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x10;  (* MOV (% rax) (Memop Quadword (%% (rsi,16))) *)
  0x48; 0xf7; 0x61; 0x18;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,24))) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x18;  (* MOV (% rax) (Memop Quadword (%% (rsi,24))) *)
  0x48; 0xf7; 0x61; 0x10;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,16))) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x20;  (* MOV (% rax) (Memop Quadword (%% (rsi,32))) *)
  0x48; 0xf7; 0x61; 0x08;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,8))) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x28;  (* MOV (% rax) (Memop Quadword (%% (rsi,40))) *)
  0x48; 0xf7; 0x21;        (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,0))) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x6c; 0x24; 0x28;
                           (* MOV (Memop Quadword (%% (rsp,40))) (% r13) *)
  0x4d; 0x31; 0xc0;        (* XOR (% r8) (% r8) *)
  0x48; 0x8b; 0x06;        (* MOV (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0xf7; 0x61; 0x30;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,48))) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0x4d; 0x11; 0xc0;        (* ADC (% r8) (% r8) *)
  0x48; 0x8b; 0x46; 0x08;  (* MOV (% rax) (Memop Quadword (%% (rsi,8))) *)
  0x48; 0xf7; 0x61; 0x28;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,40))) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0x49; 0x83; 0xd0; 0x00;  (* ADC (% r8) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x10;  (* MOV (% rax) (Memop Quadword (%% (rsi,16))) *)
  0x48; 0xf7; 0x61; 0x20;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,32))) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0x49; 0x83; 0xd0; 0x00;  (* ADC (% r8) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x18;  (* MOV (% rax) (Memop Quadword (%% (rsi,24))) *)
  0x48; 0xf7; 0x61; 0x18;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,24))) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0x49; 0x83; 0xd0; 0x00;  (* ADC (% r8) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x20;  (* MOV (% rax) (Memop Quadword (%% (rsi,32))) *)
  0x48; 0xf7; 0x61; 0x10;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,16))) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0x49; 0x83; 0xd0; 0x00;  (* ADC (% r8) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x28;  (* MOV (% rax) (Memop Quadword (%% (rsi,40))) *)
  0x48; 0xf7; 0x61; 0x08;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,8))) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0x49; 0x83; 0xd0; 0x00;  (* ADC (% r8) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x30;  (* MOV (% rax) (Memop Quadword (%% (rsi,48))) *)
  0x48; 0xf7; 0x21;        (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,0))) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0x49; 0x83; 0xd0; 0x00;  (* ADC (% r8) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x74; 0x24; 0x30;
                           (* MOV (Memop Quadword (%% (rsp,48))) (% r14) *)
  0x4d; 0x31; 0xc9;        (* XOR (% r9) (% r9) *)
  0x48; 0x8b; 0x06;        (* MOV (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0xf7; 0x61; 0x38;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,56))) *)
  0x49; 0x01; 0xc7;        (* ADD (% r15) (% rax) *)
  0x49; 0x11; 0xd0;        (* ADC (% r8) (% rdx) *)
  0x4d; 0x11; 0xc9;        (* ADC (% r9) (% r9) *)
  0x48; 0x8b; 0x46; 0x08;  (* MOV (% rax) (Memop Quadword (%% (rsi,8))) *)
  0x48; 0xf7; 0x61; 0x30;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,48))) *)
  0x49; 0x01; 0xc7;        (* ADD (% r15) (% rax) *)
  0x49; 0x11; 0xd0;        (* ADC (% r8) (% rdx) *)
  0x49; 0x83; 0xd1; 0x00;  (* ADC (% r9) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x10;  (* MOV (% rax) (Memop Quadword (%% (rsi,16))) *)
  0x48; 0xf7; 0x61; 0x28;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,40))) *)
  0x49; 0x01; 0xc7;        (* ADD (% r15) (% rax) *)
  0x49; 0x11; 0xd0;        (* ADC (% r8) (% rdx) *)
  0x49; 0x83; 0xd1; 0x00;  (* ADC (% r9) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x18;  (* MOV (% rax) (Memop Quadword (%% (rsi,24))) *)
  0x48; 0xf7; 0x61; 0x20;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,32))) *)
  0x49; 0x01; 0xc7;        (* ADD (% r15) (% rax) *)
  0x49; 0x11; 0xd0;        (* ADC (% r8) (% rdx) *)
  0x49; 0x83; 0xd1; 0x00;  (* ADC (% r9) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x20;  (* MOV (% rax) (Memop Quadword (%% (rsi,32))) *)
  0x48; 0xf7; 0x61; 0x18;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,24))) *)
  0x49; 0x01; 0xc7;        (* ADD (% r15) (% rax) *)
  0x49; 0x11; 0xd0;        (* ADC (% r8) (% rdx) *)
  0x49; 0x83; 0xd1; 0x00;  (* ADC (% r9) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x28;  (* MOV (% rax) (Memop Quadword (%% (rsi,40))) *)
  0x48; 0xf7; 0x61; 0x10;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,16))) *)
  0x49; 0x01; 0xc7;        (* ADD (% r15) (% rax) *)
  0x49; 0x11; 0xd0;        (* ADC (% r8) (% rdx) *)
  0x49; 0x83; 0xd1; 0x00;  (* ADC (% r9) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x30;  (* MOV (% rax) (Memop Quadword (%% (rsi,48))) *)
  0x48; 0xf7; 0x61; 0x08;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,8))) *)
  0x49; 0x01; 0xc7;        (* ADD (% r15) (% rax) *)
  0x49; 0x11; 0xd0;        (* ADC (% r8) (% rdx) *)
  0x49; 0x83; 0xd1; 0x00;  (* ADC (% r9) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x38;  (* MOV (% rax) (Memop Quadword (%% (rsi,56))) *)
  0x48; 0xf7; 0x21;        (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,0))) *)
  0x49; 0x01; 0xc7;        (* ADD (% r15) (% rax) *)
  0x49; 0x11; 0xd0;        (* ADC (% r8) (% rdx) *)
  0x49; 0x83; 0xd1; 0x00;  (* ADC (% r9) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x7c; 0x24; 0x38;
                           (* MOV (Memop Quadword (%% (rsp,56))) (% r15) *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x48; 0x8b; 0x06;        (* MOV (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0xf7; 0x61; 0x40;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,64))) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x4d; 0x11; 0xd2;        (* ADC (% r10) (% r10) *)
  0x48; 0x8b; 0x46; 0x08;  (* MOV (% rax) (Memop Quadword (%% (rsi,8))) *)
  0x48; 0xf7; 0x61; 0x38;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,56))) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x49; 0x83; 0xd2; 0x00;  (* ADC (% r10) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x10;  (* MOV (% rax) (Memop Quadword (%% (rsi,16))) *)
  0x48; 0xf7; 0x61; 0x30;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,48))) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x49; 0x83; 0xd2; 0x00;  (* ADC (% r10) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x18;  (* MOV (% rax) (Memop Quadword (%% (rsi,24))) *)
  0x48; 0xf7; 0x61; 0x28;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,40))) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x49; 0x83; 0xd2; 0x00;  (* ADC (% r10) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x20;  (* MOV (% rax) (Memop Quadword (%% (rsi,32))) *)
  0x48; 0xf7; 0x61; 0x20;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,32))) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x49; 0x83; 0xd2; 0x00;  (* ADC (% r10) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x28;  (* MOV (% rax) (Memop Quadword (%% (rsi,40))) *)
  0x48; 0xf7; 0x61; 0x18;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,24))) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x49; 0x83; 0xd2; 0x00;  (* ADC (% r10) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x30;  (* MOV (% rax) (Memop Quadword (%% (rsi,48))) *)
  0x48; 0xf7; 0x61; 0x10;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,16))) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x49; 0x83; 0xd2; 0x00;  (* ADC (% r10) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x38;  (* MOV (% rax) (Memop Quadword (%% (rsi,56))) *)
  0x48; 0xf7; 0x61; 0x08;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,8))) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x49; 0x83; 0xd2; 0x00;  (* ADC (% r10) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x40;  (* MOV (% rax) (Memop Quadword (%% (rsi,64))) *)
  0x48; 0xf7; 0x21;        (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,0))) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x49; 0x83; 0xd2; 0x00;  (* ADC (% r10) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x44; 0x24; 0x40;
                           (* MOV (Memop Quadword (%% (rsp,64))) (% r8) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x48; 0x8b; 0x46; 0x08;  (* MOV (% rax) (Memop Quadword (%% (rsi,8))) *)
  0x48; 0xf7; 0x61; 0x40;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,64))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x4d; 0x11; 0xdb;        (* ADC (% r11) (% r11) *)
  0x48; 0x8b; 0x46; 0x10;  (* MOV (% rax) (Memop Quadword (%% (rsi,16))) *)
  0x48; 0xf7; 0x61; 0x38;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,56))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x18;  (* MOV (% rax) (Memop Quadword (%% (rsi,24))) *)
  0x48; 0xf7; 0x61; 0x30;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,48))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x20;  (* MOV (% rax) (Memop Quadword (%% (rsi,32))) *)
  0x48; 0xf7; 0x61; 0x28;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,40))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x28;  (* MOV (% rax) (Memop Quadword (%% (rsi,40))) *)
  0x48; 0xf7; 0x61; 0x20;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,32))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x30;  (* MOV (% rax) (Memop Quadword (%% (rsi,48))) *)
  0x48; 0xf7; 0x61; 0x18;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,24))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x38;  (* MOV (% rax) (Memop Quadword (%% (rsi,56))) *)
  0x48; 0xf7; 0x61; 0x10;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,16))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x40;  (* MOV (% rax) (Memop Quadword (%% (rsi,64))) *)
  0x48; 0xf7; 0x61; 0x08;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,8))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xe4;        (* XOR (% r12) (% r12) *)
  0x48; 0x8b; 0x46; 0x10;  (* MOV (% rax) (Memop Quadword (%% (rsi,16))) *)
  0x48; 0xf7; 0x61; 0x40;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,64))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x4d; 0x11; 0xe4;        (* ADC (% r12) (% r12) *)
  0x48; 0x8b; 0x46; 0x18;  (* MOV (% rax) (Memop Quadword (%% (rsi,24))) *)
  0x48; 0xf7; 0x61; 0x38;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,56))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x20;  (* MOV (% rax) (Memop Quadword (%% (rsi,32))) *)
  0x48; 0xf7; 0x61; 0x30;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,48))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x28;  (* MOV (% rax) (Memop Quadword (%% (rsi,40))) *)
  0x48; 0xf7; 0x61; 0x28;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,40))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x30;  (* MOV (% rax) (Memop Quadword (%% (rsi,48))) *)
  0x48; 0xf7; 0x61; 0x20;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,32))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x38;  (* MOV (% rax) (Memop Quadword (%% (rsi,56))) *)
  0x48; 0xf7; 0x61; 0x18;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,24))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x40;  (* MOV (% rax) (Memop Quadword (%% (rsi,64))) *)
  0x48; 0xf7; 0x61; 0x10;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,16))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xed;        (* XOR (% r13) (% r13) *)
  0x48; 0x8b; 0x46; 0x18;  (* MOV (% rax) (Memop Quadword (%% (rsi,24))) *)
  0x48; 0xf7; 0x61; 0x40;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,64))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x4d; 0x11; 0xed;        (* ADC (% r13) (% r13) *)
  0x48; 0x8b; 0x46; 0x20;  (* MOV (% rax) (Memop Quadword (%% (rsi,32))) *)
  0x48; 0xf7; 0x61; 0x38;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,56))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x28;  (* MOV (% rax) (Memop Quadword (%% (rsi,40))) *)
  0x48; 0xf7; 0x61; 0x30;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,48))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x30;  (* MOV (% rax) (Memop Quadword (%% (rsi,48))) *)
  0x48; 0xf7; 0x61; 0x28;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,40))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x38;  (* MOV (% rax) (Memop Quadword (%% (rsi,56))) *)
  0x48; 0xf7; 0x61; 0x20;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,32))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x40;  (* MOV (% rax) (Memop Quadword (%% (rsi,64))) *)
  0x48; 0xf7; 0x61; 0x18;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,24))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xf6;        (* XOR (% r14) (% r14) *)
  0x48; 0x8b; 0x46; 0x20;  (* MOV (% rax) (Memop Quadword (%% (rsi,32))) *)
  0x48; 0xf7; 0x61; 0x40;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,64))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x4d; 0x11; 0xf6;        (* ADC (% r14) (% r14) *)
  0x48; 0x8b; 0x46; 0x28;  (* MOV (% rax) (Memop Quadword (%% (rsi,40))) *)
  0x48; 0xf7; 0x61; 0x38;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,56))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x30;  (* MOV (% rax) (Memop Quadword (%% (rsi,48))) *)
  0x48; 0xf7; 0x61; 0x30;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,48))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x38;  (* MOV (% rax) (Memop Quadword (%% (rsi,56))) *)
  0x48; 0xf7; 0x61; 0x28;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,40))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x40;  (* MOV (% rax) (Memop Quadword (%% (rsi,64))) *)
  0x48; 0xf7; 0x61; 0x20;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,32))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xff;        (* XOR (% r15) (% r15) *)
  0x48; 0x8b; 0x46; 0x28;  (* MOV (% rax) (Memop Quadword (%% (rsi,40))) *)
  0x48; 0xf7; 0x61; 0x40;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,64))) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x4d; 0x11; 0xff;        (* ADC (% r15) (% r15) *)
  0x48; 0x8b; 0x46; 0x30;  (* MOV (% rax) (Memop Quadword (%% (rsi,48))) *)
  0x48; 0xf7; 0x61; 0x38;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,56))) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x38;  (* MOV (% rax) (Memop Quadword (%% (rsi,56))) *)
  0x48; 0xf7; 0x61; 0x30;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,48))) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x40;  (* MOV (% rax) (Memop Quadword (%% (rsi,64))) *)
  0x48; 0xf7; 0x61; 0x28;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,40))) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xc0;        (* XOR (% r8) (% r8) *)
  0x48; 0x8b; 0x46; 0x30;  (* MOV (% rax) (Memop Quadword (%% (rsi,48))) *)
  0x48; 0xf7; 0x61; 0x40;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,64))) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0x4d; 0x11; 0xc0;        (* ADC (% r8) (% r8) *)
  0x48; 0x8b; 0x46; 0x38;  (* MOV (% rax) (Memop Quadword (%% (rsi,56))) *)
  0x48; 0xf7; 0x61; 0x38;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,56))) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0x49; 0x83; 0xd0; 0x00;  (* ADC (% r8) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x40;  (* MOV (% rax) (Memop Quadword (%% (rsi,64))) *)
  0x48; 0xf7; 0x61; 0x30;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,48))) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0x49; 0x83; 0xd0; 0x00;  (* ADC (% r8) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x38;  (* MOV (% rax) (Memop Quadword (%% (rsi,56))) *)
  0x48; 0xf7; 0x61; 0x40;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,64))) *)
  0x49; 0x01; 0xc7;        (* ADD (% r15) (% rax) *)
  0x49; 0x11; 0xd0;        (* ADC (% r8) (% rdx) *)
  0x48; 0x8b; 0x46; 0x40;  (* MOV (% rax) (Memop Quadword (%% (rsi,64))) *)
  0x48; 0xf7; 0x61; 0x38;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,56))) *)
  0x49; 0x01; 0xc7;        (* ADD (% r15) (% rax) *)
  0x49; 0x11; 0xd0;        (* ADC (% r8) (% rdx) *)
  0x48; 0x8b; 0x46; 0x40;  (* MOV (% rax) (Memop Quadword (%% (rsi,64))) *)
  0x48; 0x0f; 0xaf; 0x41; 0x40;
                           (* IMUL (% rax) (Memop Quadword (%% (rcx,64))) *)
  0x4c; 0x01; 0xc0;        (* ADD (% rax) (% r8) *)
  0x4c; 0x8b; 0x44; 0x24; 0x40;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,64))) *)
  0x4c; 0x89; 0xc2;        (* MOV (% rdx) (% r8) *)
  0x48; 0x81; 0xe2; 0xff; 0x01; 0x00; 0x00;
                           (* AND (% rdx) (Imm32 (word 511)) *)
  0x4d; 0x0f; 0xac; 0xc8; 0x09;
                           (* SHRD (% r8) (% r9) (Imm8 (word 9)) *)
  0x4d; 0x0f; 0xac; 0xd1; 0x09;
                           (* SHRD (% r9) (% r10) (Imm8 (word 9)) *)
  0x4d; 0x0f; 0xac; 0xda; 0x09;
                           (* SHRD (% r10) (% r11) (Imm8 (word 9)) *)
  0x4d; 0x0f; 0xac; 0xe3; 0x09;
                           (* SHRD (% r11) (% r12) (Imm8 (word 9)) *)
  0x4d; 0x0f; 0xac; 0xec; 0x09;
                           (* SHRD (% r12) (% r13) (Imm8 (word 9)) *)
  0x4d; 0x0f; 0xac; 0xf5; 0x09;
                           (* SHRD (% r13) (% r14) (Imm8 (word 9)) *)
  0x4d; 0x0f; 0xac; 0xfe; 0x09;
                           (* SHRD (% r14) (% r15) (Imm8 (word 9)) *)
  0x49; 0x0f; 0xac; 0xc7; 0x09;
                           (* SHRD (% r15) (% rax) (Imm8 (word 9)) *)
  0x48; 0xc1; 0xe8; 0x09;  (* SHR (% rax) (Imm8 (word 9)) *)
  0x48; 0x01; 0xc2;        (* ADD (% rdx) (% rax) *)
  0xf9;                    (* STCF *)
  0x4c; 0x13; 0x04; 0x24;  (* ADC (% r8) (Memop Quadword (%% (rsp,0))) *)
  0x4c; 0x13; 0x4c; 0x24; 0x08;
                           (* ADC (% r9) (Memop Quadword (%% (rsp,8))) *)
  0x4c; 0x13; 0x54; 0x24; 0x10;
                           (* ADC (% r10) (Memop Quadword (%% (rsp,16))) *)
  0x4c; 0x13; 0x5c; 0x24; 0x18;
                           (* ADC (% r11) (Memop Quadword (%% (rsp,24))) *)
  0x4c; 0x13; 0x64; 0x24; 0x20;
                           (* ADC (% r12) (Memop Quadword (%% (rsp,32))) *)
  0x4c; 0x13; 0x6c; 0x24; 0x28;
                           (* ADC (% r13) (Memop Quadword (%% (rsp,40))) *)
  0x4c; 0x13; 0x74; 0x24; 0x30;
                           (* ADC (% r14) (Memop Quadword (%% (rsp,48))) *)
  0x4c; 0x13; 0x7c; 0x24; 0x38;
                           (* ADC (% r15) (Memop Quadword (%% (rsp,56))) *)
  0x48; 0x81; 0xd2; 0x00; 0xfe; 0xff; 0xff;
                           (* ADC (% rdx) (Imm32 (word 4294966784)) *)
  0xf5;                    (* CMC *)
  0x49; 0x83; 0xd8; 0x00;  (* SBB (% r8) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x07;        (* MOV (Memop Quadword (%% (rdi,0))) (% r8) *)
  0x49; 0x83; 0xd9; 0x00;  (* SBB (% r9) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x4f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% r9) *)
  0x49; 0x83; 0xda; 0x00;  (* SBB (% r10) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x57; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r10) *)
  0x49; 0x83; 0xdb; 0x00;  (* SBB (% r11) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x5f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r11) *)
  0x49; 0x83; 0xdc; 0x00;  (* SBB (% r12) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x67; 0x20;  (* MOV (Memop Quadword (%% (rdi,32))) (% r12) *)
  0x49; 0x83; 0xdd; 0x00;  (* SBB (% r13) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x6f; 0x28;  (* MOV (Memop Quadword (%% (rdi,40))) (% r13) *)
  0x49; 0x83; 0xde; 0x00;  (* SBB (% r14) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x77; 0x30;  (* MOV (Memop Quadword (%% (rdi,48))) (% r14) *)
  0x49; 0x83; 0xdf; 0x00;  (* SBB (% r15) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x7f; 0x38;  (* MOV (Memop Quadword (%% (rdi,56))) (% r15) *)
  0x48; 0x83; 0xda; 0x00;  (* SBB (% rdx) (Imm8 (word 0)) *)
  0x48; 0x81; 0xe2; 0xff; 0x01; 0x00; 0x00;
                           (* AND (% rdx) (Imm32 (word 511)) *)
  0x48; 0x89; 0x57; 0x40;  (* MOV (Memop Quadword (%% (rdi,64))) (% rdx) *)
  0x48; 0x83; 0xc4; 0x48;  (* ADD (% rsp) (Imm8 (word 72)) *)
  0xc3;                    (* RET *)
  0x48; 0x83; 0xec; 0x48;  (* SUB (% rsp) (Imm8 (word 72)) *)
  0x48; 0x8b; 0x06;        (* MOV (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x48; 0x89; 0x04; 0x24;  (* MOV (Memop Quadword (%% (rsp,0))) (% rax) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x48; 0x8b; 0x06;        (* MOV (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0xf7; 0x66; 0x08;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,8))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x4c; 0x24; 0x08;
                           (* MOV (Memop Quadword (%% (rsp,8))) (% r9) *)
  0x4d; 0x31; 0xe4;        (* XOR (% r12) (% r12) *)
  0x48; 0x8b; 0x46; 0x08;  (* MOV (% rax) (Memop Quadword (%% (rsi,8))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x06;        (* MOV (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0xf7; 0x66; 0x10;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,16))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x54; 0x24; 0x10;
                           (* MOV (Memop Quadword (%% (rsp,16))) (% r10) *)
  0x48; 0x8b; 0x06;        (* MOV (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0xf7; 0x66; 0x18;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,24))) *)
  0x4d; 0x31; 0xed;        (* XOR (% r13) (% r13) *)
  0x48; 0x89; 0xc3;        (* MOV (% rbx) (% rax) *)
  0x48; 0x89; 0xd1;        (* MOV (% rcx) (% rdx) *)
  0x48; 0x8b; 0x46; 0x08;  (* MOV (% rax) (Memop Quadword (%% (rsi,8))) *)
  0x48; 0xf7; 0x66; 0x10;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,16))) *)
  0x48; 0x01; 0xc3;        (* ADD (% rbx) (% rax) *)
  0x48; 0x11; 0xd1;        (* ADC (% rcx) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x01; 0xdb;        (* ADD (% rbx) (% rbx) *)
  0x48; 0x11; 0xc9;        (* ADC (% rcx) (% rcx) *)
  0x4d; 0x11; 0xed;        (* ADC (% r13) (% r13) *)
  0x49; 0x01; 0xdb;        (* ADD (% r11) (% rbx) *)
  0x49; 0x11; 0xcc;        (* ADC (% r12) (% rcx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x5c; 0x24; 0x18;
                           (* MOV (Memop Quadword (%% (rsp,24))) (% r11) *)
  0x48; 0x8b; 0x06;        (* MOV (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0xf7; 0x66; 0x20;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,32))) *)
  0x4d; 0x31; 0xf6;        (* XOR (% r14) (% r14) *)
  0x48; 0x89; 0xc3;        (* MOV (% rbx) (% rax) *)
  0x48; 0x89; 0xd1;        (* MOV (% rcx) (% rdx) *)
  0x48; 0x8b; 0x46; 0x08;  (* MOV (% rax) (Memop Quadword (%% (rsi,8))) *)
  0x48; 0xf7; 0x66; 0x18;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,24))) *)
  0x48; 0x01; 0xc3;        (* ADD (% rbx) (% rax) *)
  0x48; 0x11; 0xd1;        (* ADC (% rcx) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x48; 0x01; 0xdb;        (* ADD (% rbx) (% rbx) *)
  0x48; 0x11; 0xc9;        (* ADC (% rcx) (% rcx) *)
  0x4d; 0x11; 0xf6;        (* ADC (% r14) (% r14) *)
  0x49; 0x01; 0xdc;        (* ADD (% r12) (% rbx) *)
  0x49; 0x11; 0xcd;        (* ADC (% r13) (% rcx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x10;  (* MOV (% rax) (Memop Quadword (%% (rsi,16))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x64; 0x24; 0x20;
                           (* MOV (Memop Quadword (%% (rsp,32))) (% r12) *)
  0x48; 0x8b; 0x06;        (* MOV (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0xf7; 0x66; 0x28;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,40))) *)
  0x4d; 0x31; 0xff;        (* XOR (% r15) (% r15) *)
  0x48; 0x89; 0xc3;        (* MOV (% rbx) (% rax) *)
  0x48; 0x89; 0xd1;        (* MOV (% rcx) (% rdx) *)
  0x48; 0x8b; 0x46; 0x08;  (* MOV (% rax) (Memop Quadword (%% (rsi,8))) *)
  0x48; 0xf7; 0x66; 0x20;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,32))) *)
  0x48; 0x01; 0xc3;        (* ADD (% rbx) (% rax) *)
  0x48; 0x11; 0xd1;        (* ADC (% rcx) (% rdx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x10;  (* MOV (% rax) (Memop Quadword (%% (rsi,16))) *)
  0x48; 0xf7; 0x66; 0x18;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,24))) *)
  0x48; 0x01; 0xc3;        (* ADD (% rbx) (% rax) *)
  0x48; 0x11; 0xd1;        (* ADC (% rcx) (% rdx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x48; 0x01; 0xdb;        (* ADD (% rbx) (% rbx) *)
  0x48; 0x11; 0xc9;        (* ADC (% rcx) (% rcx) *)
  0x4d; 0x11; 0xff;        (* ADC (% r15) (% r15) *)
  0x49; 0x01; 0xdd;        (* ADD (% r13) (% rbx) *)
  0x49; 0x11; 0xce;        (* ADC (% r14) (% rcx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x6c; 0x24; 0x28;
                           (* MOV (Memop Quadword (%% (rsp,40))) (% r13) *)
  0x48; 0x8b; 0x06;        (* MOV (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0xf7; 0x66; 0x30;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,48))) *)
  0x4d; 0x31; 0xc0;        (* XOR (% r8) (% r8) *)
  0x48; 0x89; 0xc3;        (* MOV (% rbx) (% rax) *)
  0x48; 0x89; 0xd1;        (* MOV (% rcx) (% rdx) *)
  0x48; 0x8b; 0x46; 0x08;  (* MOV (% rax) (Memop Quadword (%% (rsi,8))) *)
  0x48; 0xf7; 0x66; 0x28;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,40))) *)
  0x48; 0x01; 0xc3;        (* ADD (% rbx) (% rax) *)
  0x48; 0x11; 0xd1;        (* ADC (% rcx) (% rdx) *)
  0x49; 0x83; 0xd0; 0x00;  (* ADC (% r8) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x10;  (* MOV (% rax) (Memop Quadword (%% (rsi,16))) *)
  0x48; 0xf7; 0x66; 0x20;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,32))) *)
  0x48; 0x01; 0xc3;        (* ADD (% rbx) (% rax) *)
  0x48; 0x11; 0xd1;        (* ADC (% rcx) (% rdx) *)
  0x49; 0x83; 0xd0; 0x00;  (* ADC (% r8) (Imm8 (word 0)) *)
  0x48; 0x01; 0xdb;        (* ADD (% rbx) (% rbx) *)
  0x48; 0x11; 0xc9;        (* ADC (% rcx) (% rcx) *)
  0x4d; 0x11; 0xc0;        (* ADC (% r8) (% r8) *)
  0x49; 0x01; 0xde;        (* ADD (% r14) (% rbx) *)
  0x49; 0x11; 0xcf;        (* ADC (% r15) (% rcx) *)
  0x49; 0x83; 0xd0; 0x00;  (* ADC (% r8) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x18;  (* MOV (% rax) (Memop Quadword (%% (rsi,24))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0x49; 0x83; 0xd0; 0x00;  (* ADC (% r8) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x74; 0x24; 0x30;
                           (* MOV (Memop Quadword (%% (rsp,48))) (% r14) *)
  0x48; 0x8b; 0x06;        (* MOV (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0xf7; 0x66; 0x38;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,56))) *)
  0x4d; 0x31; 0xc9;        (* XOR (% r9) (% r9) *)
  0x48; 0x89; 0xc3;        (* MOV (% rbx) (% rax) *)
  0x48; 0x89; 0xd1;        (* MOV (% rcx) (% rdx) *)
  0x48; 0x8b; 0x46; 0x08;  (* MOV (% rax) (Memop Quadword (%% (rsi,8))) *)
  0x48; 0xf7; 0x66; 0x30;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,48))) *)
  0x48; 0x01; 0xc3;        (* ADD (% rbx) (% rax) *)
  0x48; 0x11; 0xd1;        (* ADC (% rcx) (% rdx) *)
  0x49; 0x83; 0xd1; 0x00;  (* ADC (% r9) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x10;  (* MOV (% rax) (Memop Quadword (%% (rsi,16))) *)
  0x48; 0xf7; 0x66; 0x28;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,40))) *)
  0x48; 0x01; 0xc3;        (* ADD (% rbx) (% rax) *)
  0x48; 0x11; 0xd1;        (* ADC (% rcx) (% rdx) *)
  0x49; 0x83; 0xd1; 0x00;  (* ADC (% r9) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x18;  (* MOV (% rax) (Memop Quadword (%% (rsi,24))) *)
  0x48; 0xf7; 0x66; 0x20;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,32))) *)
  0x48; 0x01; 0xc3;        (* ADD (% rbx) (% rax) *)
  0x48; 0x11; 0xd1;        (* ADC (% rcx) (% rdx) *)
  0x49; 0x83; 0xd1; 0x00;  (* ADC (% r9) (Imm8 (word 0)) *)
  0x48; 0x01; 0xdb;        (* ADD (% rbx) (% rbx) *)
  0x48; 0x11; 0xc9;        (* ADC (% rcx) (% rcx) *)
  0x4d; 0x11; 0xc9;        (* ADC (% r9) (% r9) *)
  0x49; 0x01; 0xdf;        (* ADD (% r15) (% rbx) *)
  0x49; 0x11; 0xc8;        (* ADC (% r8) (% rcx) *)
  0x49; 0x83; 0xd1; 0x00;  (* ADC (% r9) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x7c; 0x24; 0x38;
                           (* MOV (Memop Quadword (%% (rsp,56))) (% r15) *)
  0x48; 0x8b; 0x06;        (* MOV (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0xf7; 0x66; 0x40;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,64))) *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x48; 0x89; 0xc3;        (* MOV (% rbx) (% rax) *)
  0x48; 0x89; 0xd1;        (* MOV (% rcx) (% rdx) *)
  0x48; 0x8b; 0x46; 0x08;  (* MOV (% rax) (Memop Quadword (%% (rsi,8))) *)
  0x48; 0xf7; 0x66; 0x38;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,56))) *)
  0x48; 0x01; 0xc3;        (* ADD (% rbx) (% rax) *)
  0x48; 0x11; 0xd1;        (* ADC (% rcx) (% rdx) *)
  0x49; 0x83; 0xd2; 0x00;  (* ADC (% r10) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x10;  (* MOV (% rax) (Memop Quadword (%% (rsi,16))) *)
  0x48; 0xf7; 0x66; 0x30;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,48))) *)
  0x48; 0x01; 0xc3;        (* ADD (% rbx) (% rax) *)
  0x48; 0x11; 0xd1;        (* ADC (% rcx) (% rdx) *)
  0x49; 0x83; 0xd2; 0x00;  (* ADC (% r10) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x18;  (* MOV (% rax) (Memop Quadword (%% (rsi,24))) *)
  0x48; 0xf7; 0x66; 0x28;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,40))) *)
  0x48; 0x01; 0xc3;        (* ADD (% rbx) (% rax) *)
  0x48; 0x11; 0xd1;        (* ADC (% rcx) (% rdx) *)
  0x49; 0x83; 0xd2; 0x00;  (* ADC (% r10) (Imm8 (word 0)) *)
  0x48; 0x01; 0xdb;        (* ADD (% rbx) (% rbx) *)
  0x48; 0x11; 0xc9;        (* ADC (% rcx) (% rcx) *)
  0x4d; 0x11; 0xd2;        (* ADC (% r10) (% r10) *)
  0x49; 0x01; 0xd8;        (* ADD (% r8) (% rbx) *)
  0x49; 0x11; 0xc9;        (* ADC (% r9) (% rcx) *)
  0x49; 0x83; 0xd2; 0x00;  (* ADC (% r10) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x20;  (* MOV (% rax) (Memop Quadword (%% (rsi,32))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x49; 0x83; 0xd2; 0x00;  (* ADC (% r10) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x44; 0x24; 0x40;
                           (* MOV (Memop Quadword (%% (rsp,64))) (% r8) *)
  0x48; 0x8b; 0x46; 0x08;  (* MOV (% rax) (Memop Quadword (%% (rsi,8))) *)
  0x48; 0xf7; 0x66; 0x40;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,64))) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x48; 0x89; 0xc3;        (* MOV (% rbx) (% rax) *)
  0x48; 0x89; 0xd1;        (* MOV (% rcx) (% rdx) *)
  0x48; 0x8b; 0x46; 0x10;  (* MOV (% rax) (Memop Quadword (%% (rsi,16))) *)
  0x48; 0xf7; 0x66; 0x38;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,56))) *)
  0x48; 0x01; 0xc3;        (* ADD (% rbx) (% rax) *)
  0x48; 0x11; 0xd1;        (* ADC (% rcx) (% rdx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x18;  (* MOV (% rax) (Memop Quadword (%% (rsi,24))) *)
  0x48; 0xf7; 0x66; 0x30;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,48))) *)
  0x48; 0x01; 0xc3;        (* ADD (% rbx) (% rax) *)
  0x48; 0x11; 0xd1;        (* ADC (% rcx) (% rdx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x20;  (* MOV (% rax) (Memop Quadword (%% (rsi,32))) *)
  0x48; 0xf7; 0x66; 0x28;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,40))) *)
  0x48; 0x01; 0xc3;        (* ADD (% rbx) (% rax) *)
  0x48; 0x11; 0xd1;        (* ADC (% rcx) (% rdx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x48; 0x01; 0xdb;        (* ADD (% rbx) (% rbx) *)
  0x48; 0x11; 0xc9;        (* ADC (% rcx) (% rcx) *)
  0x4d; 0x11; 0xdb;        (* ADC (% r11) (% r11) *)
  0x49; 0x01; 0xd9;        (* ADD (% r9) (% rbx) *)
  0x49; 0x11; 0xca;        (* ADC (% r10) (% rcx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x10;  (* MOV (% rax) (Memop Quadword (%% (rsi,16))) *)
  0x48; 0xf7; 0x66; 0x40;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,64))) *)
  0x4d; 0x31; 0xe4;        (* XOR (% r12) (% r12) *)
  0x48; 0x89; 0xc3;        (* MOV (% rbx) (% rax) *)
  0x48; 0x89; 0xd1;        (* MOV (% rcx) (% rdx) *)
  0x48; 0x8b; 0x46; 0x18;  (* MOV (% rax) (Memop Quadword (%% (rsi,24))) *)
  0x48; 0xf7; 0x66; 0x38;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,56))) *)
  0x48; 0x01; 0xc3;        (* ADD (% rbx) (% rax) *)
  0x48; 0x11; 0xd1;        (* ADC (% rcx) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x20;  (* MOV (% rax) (Memop Quadword (%% (rsi,32))) *)
  0x48; 0xf7; 0x66; 0x30;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,48))) *)
  0x48; 0x01; 0xc3;        (* ADD (% rbx) (% rax) *)
  0x48; 0x11; 0xd1;        (* ADC (% rcx) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x48; 0x01; 0xdb;        (* ADD (% rbx) (% rbx) *)
  0x48; 0x11; 0xc9;        (* ADC (% rcx) (% rcx) *)
  0x4d; 0x11; 0xe4;        (* ADC (% r12) (% r12) *)
  0x49; 0x01; 0xda;        (* ADD (% r10) (% rbx) *)
  0x49; 0x11; 0xcb;        (* ADC (% r11) (% rcx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x28;  (* MOV (% rax) (Memop Quadword (%% (rsi,40))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x18;  (* MOV (% rax) (Memop Quadword (%% (rsi,24))) *)
  0x48; 0xf7; 0x66; 0x40;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,64))) *)
  0x4d; 0x31; 0xed;        (* XOR (% r13) (% r13) *)
  0x48; 0x89; 0xc3;        (* MOV (% rbx) (% rax) *)
  0x48; 0x89; 0xd1;        (* MOV (% rcx) (% rdx) *)
  0x48; 0x8b; 0x46; 0x20;  (* MOV (% rax) (Memop Quadword (%% (rsi,32))) *)
  0x48; 0xf7; 0x66; 0x38;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,56))) *)
  0x48; 0x01; 0xc3;        (* ADD (% rbx) (% rax) *)
  0x48; 0x11; 0xd1;        (* ADC (% rcx) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x28;  (* MOV (% rax) (Memop Quadword (%% (rsi,40))) *)
  0x48; 0xf7; 0x66; 0x30;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,48))) *)
  0x48; 0x01; 0xc3;        (* ADD (% rbx) (% rax) *)
  0x48; 0x11; 0xd1;        (* ADC (% rcx) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x01; 0xdb;        (* ADD (% rbx) (% rbx) *)
  0x48; 0x11; 0xc9;        (* ADC (% rcx) (% rcx) *)
  0x4d; 0x11; 0xed;        (* ADC (% r13) (% r13) *)
  0x49; 0x01; 0xdb;        (* ADD (% r11) (% rbx) *)
  0x49; 0x11; 0xcc;        (* ADC (% r12) (% rcx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x20;  (* MOV (% rax) (Memop Quadword (%% (rsi,32))) *)
  0x48; 0xf7; 0x66; 0x40;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,64))) *)
  0x4d; 0x31; 0xf6;        (* XOR (% r14) (% r14) *)
  0x48; 0x89; 0xc3;        (* MOV (% rbx) (% rax) *)
  0x48; 0x89; 0xd1;        (* MOV (% rcx) (% rdx) *)
  0x48; 0x8b; 0x46; 0x28;  (* MOV (% rax) (Memop Quadword (%% (rsi,40))) *)
  0x48; 0xf7; 0x66; 0x38;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,56))) *)
  0x48; 0x01; 0xc3;        (* ADD (% rbx) (% rax) *)
  0x48; 0x11; 0xd1;        (* ADC (% rcx) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x48; 0x01; 0xdb;        (* ADD (% rbx) (% rbx) *)
  0x48; 0x11; 0xc9;        (* ADC (% rcx) (% rcx) *)
  0x4d; 0x11; 0xf6;        (* ADC (% r14) (% r14) *)
  0x49; 0x01; 0xdc;        (* ADD (% r12) (% rbx) *)
  0x49; 0x11; 0xcd;        (* ADC (% r13) (% rcx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x30;  (* MOV (% rax) (Memop Quadword (%% (rsi,48))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x28;  (* MOV (% rax) (Memop Quadword (%% (rsi,40))) *)
  0x48; 0xf7; 0x66; 0x40;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,64))) *)
  0x4d; 0x31; 0xff;        (* XOR (% r15) (% r15) *)
  0x48; 0x89; 0xc3;        (* MOV (% rbx) (% rax) *)
  0x48; 0x89; 0xd1;        (* MOV (% rcx) (% rdx) *)
  0x48; 0x8b; 0x46; 0x30;  (* MOV (% rax) (Memop Quadword (%% (rsi,48))) *)
  0x48; 0xf7; 0x66; 0x38;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,56))) *)
  0x48; 0x01; 0xc3;        (* ADD (% rbx) (% rax) *)
  0x48; 0x11; 0xd1;        (* ADC (% rcx) (% rdx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x48; 0x01; 0xdb;        (* ADD (% rbx) (% rbx) *)
  0x48; 0x11; 0xc9;        (* ADC (% rcx) (% rcx) *)
  0x4d; 0x11; 0xff;        (* ADC (% r15) (% r15) *)
  0x49; 0x01; 0xdd;        (* ADD (% r13) (% rbx) *)
  0x49; 0x11; 0xce;        (* ADC (% r14) (% rcx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xc0;        (* XOR (% r8) (% r8) *)
  0x48; 0x8b; 0x46; 0x38;  (* MOV (% rax) (Memop Quadword (%% (rsi,56))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0x49; 0x83; 0xd0; 0x00;  (* ADC (% r8) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x30;  (* MOV (% rax) (Memop Quadword (%% (rsi,48))) *)
  0x48; 0xf7; 0x66; 0x40;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,64))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd0; 0x00;  (* ADC (% r8) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0x49; 0x83; 0xd0; 0x00;  (* ADC (% r8) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x38;  (* MOV (% rax) (Memop Quadword (%% (rsi,56))) *)
  0x48; 0xf7; 0x66; 0x40;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsi,64))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x01; 0xc7;        (* ADD (% r15) (% rax) *)
  0x49; 0x11; 0xd0;        (* ADC (% r8) (% rdx) *)
  0x48; 0x8b; 0x46; 0x40;  (* MOV (% rax) (Memop Quadword (%% (rsi,64))) *)
  0x48; 0x0f; 0xaf; 0xc0;  (* IMUL (% rax) (% rax) *)
  0x4c; 0x01; 0xc0;        (* ADD (% rax) (% r8) *)
  0x4c; 0x8b; 0x44; 0x24; 0x40;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,64))) *)
  0x4c; 0x89; 0xc2;        (* MOV (% rdx) (% r8) *)
  0x48; 0x81; 0xe2; 0xff; 0x01; 0x00; 0x00;
                           (* AND (% rdx) (Imm32 (word 511)) *)
  0x4d; 0x0f; 0xac; 0xc8; 0x09;
                           (* SHRD (% r8) (% r9) (Imm8 (word 9)) *)
  0x4d; 0x0f; 0xac; 0xd1; 0x09;
                           (* SHRD (% r9) (% r10) (Imm8 (word 9)) *)
  0x4d; 0x0f; 0xac; 0xda; 0x09;
                           (* SHRD (% r10) (% r11) (Imm8 (word 9)) *)
  0x4d; 0x0f; 0xac; 0xe3; 0x09;
                           (* SHRD (% r11) (% r12) (Imm8 (word 9)) *)
  0x4d; 0x0f; 0xac; 0xec; 0x09;
                           (* SHRD (% r12) (% r13) (Imm8 (word 9)) *)
  0x4d; 0x0f; 0xac; 0xf5; 0x09;
                           (* SHRD (% r13) (% r14) (Imm8 (word 9)) *)
  0x4d; 0x0f; 0xac; 0xfe; 0x09;
                           (* SHRD (% r14) (% r15) (Imm8 (word 9)) *)
  0x49; 0x0f; 0xac; 0xc7; 0x09;
                           (* SHRD (% r15) (% rax) (Imm8 (word 9)) *)
  0x48; 0xc1; 0xe8; 0x09;  (* SHR (% rax) (Imm8 (word 9)) *)
  0x48; 0x01; 0xc2;        (* ADD (% rdx) (% rax) *)
  0xf9;                    (* STCF *)
  0x4c; 0x13; 0x04; 0x24;  (* ADC (% r8) (Memop Quadword (%% (rsp,0))) *)
  0x4c; 0x13; 0x4c; 0x24; 0x08;
                           (* ADC (% r9) (Memop Quadword (%% (rsp,8))) *)
  0x4c; 0x13; 0x54; 0x24; 0x10;
                           (* ADC (% r10) (Memop Quadword (%% (rsp,16))) *)
  0x4c; 0x13; 0x5c; 0x24; 0x18;
                           (* ADC (% r11) (Memop Quadword (%% (rsp,24))) *)
  0x4c; 0x13; 0x64; 0x24; 0x20;
                           (* ADC (% r12) (Memop Quadword (%% (rsp,32))) *)
  0x4c; 0x13; 0x6c; 0x24; 0x28;
                           (* ADC (% r13) (Memop Quadword (%% (rsp,40))) *)
  0x4c; 0x13; 0x74; 0x24; 0x30;
                           (* ADC (% r14) (Memop Quadword (%% (rsp,48))) *)
  0x4c; 0x13; 0x7c; 0x24; 0x38;
                           (* ADC (% r15) (Memop Quadword (%% (rsp,56))) *)
  0x48; 0x81; 0xd2; 0x00; 0xfe; 0xff; 0xff;
                           (* ADC (% rdx) (Imm32 (word 4294966784)) *)
  0xf5;                    (* CMC *)
  0x49; 0x83; 0xd8; 0x00;  (* SBB (% r8) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x07;        (* MOV (Memop Quadword (%% (rdi,0))) (% r8) *)
  0x49; 0x83; 0xd9; 0x00;  (* SBB (% r9) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x4f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% r9) *)
  0x49; 0x83; 0xda; 0x00;  (* SBB (% r10) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x57; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r10) *)
  0x49; 0x83; 0xdb; 0x00;  (* SBB (% r11) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x5f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r11) *)
  0x49; 0x83; 0xdc; 0x00;  (* SBB (% r12) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x67; 0x20;  (* MOV (Memop Quadword (%% (rdi,32))) (% r12) *)
  0x49; 0x83; 0xdd; 0x00;  (* SBB (% r13) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x6f; 0x28;  (* MOV (Memop Quadword (%% (rdi,40))) (% r13) *)
  0x49; 0x83; 0xde; 0x00;  (* SBB (% r14) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x77; 0x30;  (* MOV (Memop Quadword (%% (rdi,48))) (% r14) *)
  0x49; 0x83; 0xdf; 0x00;  (* SBB (% r15) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x7f; 0x38;  (* MOV (Memop Quadword (%% (rdi,56))) (% r15) *)
  0x48; 0x83; 0xda; 0x00;  (* SBB (% rdx) (Imm8 (word 0)) *)
  0x48; 0x81; 0xe2; 0xff; 0x01; 0x00; 0x00;
                           (* AND (% rdx) (Imm32 (word 511)) *)
  0x48; 0x89; 0x57; 0x40;  (* MOV (Memop Quadword (%% (rdi,64))) (% rdx) *)
  0x48; 0x83; 0xc4; 0x48;  (* ADD (% rsp) (Imm8 (word 72)) *)
  0xc3                     (* RET *)
];;

let p521_jscalarmul_alt_tmc = define_trimmed "p521_jscalarmul_alt_tmc" p521_jscalarmul_alt_mc;;

let P521_JSCALARMUL_ALT_EXEC = X86_MK_EXEC_RULE p521_jscalarmul_alt_tmc;;

let DESUM_RULE' = cache DESUM_RULE and DECARRY_RULE' = cache DECARRY_RULE;;

(* ------------------------------------------------------------------------- *)
(* Level 1: the embedded field squaring and multiplication                   *)
(* ------------------------------------------------------------------------- *)

let LOCAL_SQR_P521_CORRECT = time prove
 (`!z x n pc stackpointer.
        ALL (nonoverlapping (stackpointer,72))
            [(word pc,0x3f52); (z,8 * 9); (x,8 * 9)] /\
        nonoverlapping (z,8 * 9) (word pc,0x3f52)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) p521_jscalarmul_alt_tmc /\
                  read RIP s = word(pc + 0x3a68) /\
                  read RSP s = stackpointer /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,9) s = n)
             (\s. read RIP s = word (pc + 0x3f4d) /\
                  (n < p_521
                   ==> bignum_from_memory (z,9) s = (n EXP 2) MOD p_521))
          (MAYCHANGE [RIP; RAX; RBX; RCX; RDX;
                      R8; R9; R10; R11; R12; R13; R14; R15] ,,
           MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [memory :> bignum(z,9);
                      memory :> bytes(stackpointer,72)])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `n:num`; `pc:num`; `stackpointer:int64`] THEN
  REWRITE_TAC[ALL; C_ARGUMENTS; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the n < p_521 assumption for simplicity's sake ***)

  ASM_CASES_TAC `n < p_521` THENL
   [ASM_REWRITE_TAC[]; X86_SIM_TAC P521_JSCALARMUL_ALT_EXEC (1--353)] THEN

  (*** Digitize, deduce the bound on the top word specifically ***)

  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_LDIGITIZE_TAC "n_" `read (memory :> bytes (x,8 * 9)) s0` THEN
  SUBGOAL_THEN `n DIV 2 EXP 512 < 2 EXP 9` MP_TAC THENL
   [UNDISCH_TAC `n < p_521` THEN REWRITE_TAC[p_521] THEN ARITH_TAC;
    FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (funpow 3 LAND_CONV) [SYM th]) THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV)) THEN
    DISCH_TAC] THEN

  (*** Simulate the initial squaring ***)
  (*** Manual hack at state 309 for the rogue IMUL ***)

  X86_ACCSTEPS_TAC P521_JSCALARMUL_ALT_EXEC (1--308) (1--308) THEN
  X86_STEPS_TAC P521_JSCALARMUL_ALT_EXEC [309] THEN
  FIRST_X_ASSUM(ASSUME_TAC o GEN_REWRITE_RULE RAND_CONV
    [WORD_RULE `word_mul x y = word(0 + val x * val y)`]) THEN
  ACCUMULATE_ARITH_TAC "s309" THEN
  X86_ACCSTEPS_TAC P521_JSCALARMUL_ALT_EXEC [310] [310] THEN

  (*** Introduce more systematic names for the high part digits ***)

  MAP_EVERY (fun s -> REABBREV_TAC s THEN POP_ASSUM SUBST_ALL_TAC)
   [`h0 = read (memory :> bytes64 (word_add stackpointer (word 64))) s310`;
    `h1 = read R9 s310`;
    `h2 = read R10 s310`;
    `h3 = read R11 s310`;
    `h4 = read R12 s310`;
    `h5 = read R13 s310`;
    `h6 = read R14 s310`;
    `h7 = read R15 s310`;
    `h8 = read RAX s310`] THEN

  (*** Show that the core squaring operation is correct ***)

  SUBGOAL_THEN
   `2 EXP 512 * bignum_of_wordlist[h0;h1;h2;h3;h4;h5;h6;h7;h8] +
    bignum_from_memory(stackpointer,8) s310 =
    n EXP 2`
  ASSUME_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
    ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`1088`; `&0:real`] THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0] THEN
      REWRITE_TAC[ARITH_RULE `2 EXP 1088 = 2 EXP 544 EXP 2`] THEN
      REWRITE_TAC[EXP_MONO_LT] THEN UNDISCH_TAC `n < p_521` THEN
      REWRITE_TAC[p_521] THEN ARITH_TAC;
      REWRITE_TAC[INTEGER_CLOSED]] THEN
    EXPAND_TAC "n" THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o
      filter (is_ratconst o rand o concl) o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES])] THEN

  (*** Now simulate the rotation part ***)

  X86_STEPS_TAC P521_JSCALARMUL_ALT_EXEC (311--323) THEN

  (*** Break up into high and low parts ***)

  ABBREV_TAC `h = (n EXP 2) DIV 2 EXP 521` THEN
  ABBREV_TAC `l = (n EXP 2) MOD 2 EXP 521` THEN
  SUBGOAL_THEN `h < p_521 /\ l <= p_521` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"] THEN REWRITE_TAC[p_521] THEN
    CONJ_TAC THENL [ALL_TAC; ARITH_TAC] THEN
    SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN
    TRANS_TAC LET_TRANS `(p_521 - 1) EXP 2` THEN
    CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[p_521] THEN ARITH_TAC] THEN
    REWRITE_TAC[EXP_2] THEN MATCH_MP_TAC LE_MULT2 THEN CONJ_TAC THEN
    MATCH_MP_TAC(ARITH_RULE `x < n ==> x <= n - 1`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(n EXP 2) MOD p_521 = (h + l) MOD p_521` SUBST1_TAC THENL
   [SUBST1_TAC(SYM(SPECL
     [`n EXP 2:num`; `2 EXP 521`] (CONJUNCT2 DIVISION_SIMP))) THEN
    ASM_REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC(NUMBER_RULE
     `(e == 1) (mod p) ==> (e * h + l == h + l) (mod p)`) THEN
    REWRITE_TAC[CONG; p_521] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(n EXP 2) DIV 2 EXP 521 =
    bignum_of_wordlist
     [word_subword (word_join (h1:int64) h0:int128) (9,64);
      word_subword (word_join (h2:int64) h1:int128) (9,64);
      word_subword (word_join (h3:int64) h2:int128) (9,64);
      word_subword (word_join (h4:int64) h3:int128) (9,64);
      word_subword (word_join (h5:int64) h4:int128) (9,64);
      word_subword (word_join (h6:int64) h5:int128) (9,64);
      word_subword (word_join (h7:int64) h6:int128) (9,64);
      word_subword (word_join (h8:int64) h7:int128) (9,64);
      word_ushr h8 9] /\
    (n EXP 2) MOD 2 EXP 521 =
    2 EXP 512 * val(word_and h0 (word 511):int64) +
    bignum_of_wordlist
     [mullo_s2; sum_s12; sum_s27; sum_s44;
      sum_s66; sum_s88; sum_s115; sum_s142]`
  (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
   [MATCH_MP_TAC DIVMOD_UNIQ THEN
    REWRITE_TAC[VAL_WORD_AND_MASK_WORD; ARITH_RULE `511 = 2 EXP 9 - 1`] THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) THEN
      CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
      ASM_REWRITE_TAC[ADD_ASSOC; EQ_ADD_RCANCEL] THEN
      REWRITE_TAC[bignum_of_wordlist; VAL_WORD_USHR] THEN
      SIMP_TAC[VAL_WORD_SUBWORD_JOIN_64; DIMINDEX_64; ARITH_LE; ARITH_LT] THEN
      ARITH_TAC;
      MATCH_MP_TAC(ARITH_RULE
       `x < 2 EXP (64 * 8) ==> 2 EXP 512 * h MOD 2 EXP 9 + x < 2 EXP 521`) THEN
      MATCH_MP_TAC BIGNUM_OF_WORDLIST_BOUND THEN REWRITE_TAC[LENGTH; ARITH]];
    ALL_TAC] THEN

  (*** The net comparison h + l >= p_521 ***)

  X86_ACCSTEPS_TAC P521_JSCALARMUL_ALT_EXEC (324--333) (324--333) THEN
  SUBGOAL_THEN
   `&(val(word_add (word_and h0 (word 511):int64) (word_ushr h8 9))):real =
    &(val(word_and h0 (word 511):int64)) + &(val(word_ushr h8 9:int64))`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_CLAUSES; VAL_WORD_ADD; DIMINDEX_64] THEN
    MATCH_MP_TAC MOD_LT THEN
    REWRITE_TAC[VAL_WORD_AND_MASK_WORD; ARITH_RULE `511 = 2 EXP 9 - 1`] THEN
    REWRITE_TAC[VAL_WORD_USHR] THEN
    MP_TAC(SPEC `h8:int64` VAL_BOUND_64) THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `carry_s333 <=> p_521 <= h + l` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `576` THEN
    MAP_EVERY EXPAND_TAC ["h"; "l"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_521] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN

  (*** The final correction ***)

  X86_ACCSTEPS_TAC P521_JSCALARMUL_ALT_EXEC (334--353) (334--353) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN CONV_TAC(RAND_CONV BIGNUM_LEXPAND_CONV) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  MAP_EVERY EXISTS_TAC
   [`521`;
    `if h + l < p_521 then &h + &l:real else (&h + &l) - &p_521`] THEN
  REPEAT CONJ_TAC THENL
   [BOUNDER_TAC[];
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    REWRITE_TAC[GSYM NOT_LT] THEN ABBREV_TAC `bb <=> h + l < p_521` THEN
    MAP_EVERY EXPAND_TAC ["h"; "l"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_521] THEN
    REWRITE_TAC[VAL_WORD_AND_MASK_WORD; ARITH_RULE `511 = 2 EXP 9 - 1`] THEN
    REWRITE_TAC[REAL_OF_NUM_MOD] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ASM_SIMP_TAC[MOD_CASES; ARITH_RULE
     `h < p /\ l <= p ==> h + l < 2 * p`] THEN
    SIMP_TAC[REAL_OF_NUM_CLAUSES; REAL_OF_NUM_SUB; COND_SWAP; GSYM NOT_LE] THEN
    MESON_TAC[]]);;

let LOCAL_SQR_P521_SUBR_CORRECT = prove
 (`!z x n pc stackpointer returnaddress.
        ALL (nonoverlapping (z,8 * 9))
            [(word pc,0x3f52); (word_sub stackpointer (word 72),80)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 72),72))
            [(word pc,0x3f52); (x,8 * 9)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) p521_jscalarmul_alt_tmc /\
                  read RIP s = word(pc + 0x3a64) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,9) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (n < p_521
                   ==> bignum_from_memory (z,9) s = n EXP 2 MOD p_521))
             (MAYCHANGE [RIP; RSP; RAX; RBX; RCX; RDX; R8; R9;
                         R10; R11; R12; R13; R14; R15] ,,
              MAYCHANGE SOME_FLAGS ,,
              MAYCHANGE [memory :> bytes(z,8 * 9);
                     memory :> bytes(word_sub stackpointer (word 72),72)])`,
  X86_ADD_RETURN_STACK_TAC  P521_JSCALARMUL_ALT_EXEC
   LOCAL_SQR_P521_CORRECT `[]:((x86state,(64)word)component)list` 72);;

let LOCAL_MUL_P521_CORRECT = prove
 (`!z x y a b pc stackpointer.
        ALL (nonoverlapping (stackpointer,72))
            [(word pc,0x3f52); (z,8 * 9); (x,8 * 9); (y,8 * 9)] /\
        nonoverlapping (z,8 * 9) (word pc,0x3f52)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) p521_jscalarmul_alt_tmc /\
                  read RIP s = word(pc + 0x33ce) /\
                  read RSP s = stackpointer /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,9) s = a /\
                  bignum_from_memory (y,9) s = b)
             (\s. read RIP s = word (pc + 0x3a5f) /\
                  (a < p_521 /\ b < p_521
                   ==> bignum_from_memory (z,9) s = (a * b) MOD p_521))
             (MAYCHANGE [RIP; RAX; RBP; RBX; RCX; RDX;
                         R8; R9; R10; R11; R12; R13; R14; R15] ,,
              MAYCHANGE [memory :> bytes(z,8 * 9);
                         memory :> bytes(stackpointer,72)] ,,
              MAYCHANGE SOME_FLAGS)`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `y:int64`; `a:num`; `b:num`;
     `pc:num`; `stackpointer:int64`] THEN
  REWRITE_TAC[ALL; C_ARGUMENTS; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the a < p_521 /\ b < p_521 assumption for simplicity ***)

  ASM_CASES_TAC `a < p_521 /\ b < p_521` THENL
   [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC);
    X86_SIM_TAC P521_JSCALARMUL_ALT_EXEC (1--466)] THEN

  (*** Digitize, deduce the bound on the top words ***)

  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_LDIGITIZE_TAC "x_" `bignum_from_memory (x,9) s0` THEN
  BIGNUM_LDIGITIZE_TAC "y_" `bignum_from_memory (y,9) s0` THEN
  SUBGOAL_THEN
   `a DIV 2 EXP 512 < 2 EXP 9 /\ b DIV 2 EXP 512 < 2 EXP 9`
  MP_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`a < p_521`; `b < p_521`] THEN
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    MAP_EVERY EXPAND_TAC ["a"; "b"] THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN

  (*** Simulate the initial multiplication ***)
  (*** Manual hack at state 422 for the rogue IMUL ***)

  X86_ACCSTEPS_TAC P521_JSCALARMUL_ALT_EXEC (1--421) (1--421) THEN
  X86_STEPS_TAC P521_JSCALARMUL_ALT_EXEC [422] THEN
  FIRST_X_ASSUM(ASSUME_TAC o GEN_REWRITE_RULE RAND_CONV
    [WORD_RULE `word_mul x y = word(0 + val x * val y)`]) THEN
  ACCUMULATE_ARITH_TAC "s422" THEN
  X86_ACCSTEPS_TAC P521_JSCALARMUL_ALT_EXEC [423] [423] THEN

  (*** Introduce more systematic names for the high part digits ***)

  MAP_EVERY (fun s -> REABBREV_TAC s THEN POP_ASSUM SUBST_ALL_TAC)
   [`h0 = read (memory :> bytes64 (word_add stackpointer (word 64))) s423`;
    `h1 = read R9 s423`;
    `h2 = read R10 s423`;
    `h3 = read R11 s423`;
    `h4 = read R12 s423`;
    `h5 = read R13 s423`;
    `h6 = read R14 s423`;
    `h7 = read R15 s423`;
    `h8 = read RAX s423`] THEN

  (*** Show that the core multiplication operation is correct ***)

  SUBGOAL_THEN
   `2 EXP 512 * bignum_of_wordlist[h0;h1;h2;h3;h4;h5;h6;h7;h8] +
    bignum_from_memory(stackpointer,8) s423 =
    a * b`
  ASSUME_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
    ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`1088`; `&0:real`] THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0] THEN
      REWRITE_TAC[EXP_2; ARITH_RULE `2 EXP 1088 = 2 EXP 544 EXP 2`] THEN
      MATCH_MP_TAC LT_MULT2 THEN
      MAP_EVERY UNDISCH_TAC [`a < p_521`; `b < p_521`] THEN
      REWRITE_TAC[p_521] THEN ARITH_TAC;
      REWRITE_TAC[INTEGER_CLOSED]] THEN
    MAP_EVERY EXPAND_TAC ["a"; "b"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o
      filter (is_ratconst o rand o concl) o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES])] THEN

  (*** Now simulate the rotation part ***)

  X86_STEPS_TAC P521_JSCALARMUL_ALT_EXEC (424--436) THEN

  (*** Break up into high and low parts ***)

  ABBREV_TAC `h = (a * b) DIV 2 EXP 521` THEN
  ABBREV_TAC `l = (a * b) MOD 2 EXP 521` THEN
  SUBGOAL_THEN `h < p_521 /\ l <= p_521` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"] THEN REWRITE_TAC[p_521] THEN
    CONJ_TAC THENL [ALL_TAC; ARITH_TAC] THEN
    SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN
    TRANS_TAC LET_TRANS `(p_521 - 1) EXP 2` THEN
    CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[p_521] THEN ARITH_TAC] THEN
    REWRITE_TAC[EXP_2] THEN MATCH_MP_TAC LE_MULT2 THEN CONJ_TAC THEN
    MATCH_MP_TAC(ARITH_RULE `x < n ==> x <= n - 1`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(a * b) MOD p_521 = (h + l) MOD p_521` SUBST1_TAC THENL
   [SUBST1_TAC(SYM(SPECL
     [`a * b:num`; `2 EXP 521`] (CONJUNCT2 DIVISION_SIMP))) THEN
    ASM_REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC(NUMBER_RULE
     `(e == 1) (mod p) ==> (e * h + l == h + l) (mod p)`) THEN
    REWRITE_TAC[CONG; p_521] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(a * b) DIV 2 EXP 521 =
    bignum_of_wordlist
     [word_subword (word_join (h1:int64) h0:int128) (9,64);
      word_subword (word_join (h2:int64) h1:int128) (9,64);
      word_subword (word_join (h3:int64) h2:int128) (9,64);
      word_subword (word_join (h4:int64) h3:int128) (9,64);
      word_subword (word_join (h5:int64) h4:int128) (9,64);
      word_subword (word_join (h6:int64) h5:int128) (9,64);
      word_subword (word_join (h7:int64) h6:int128) (9,64);
      word_subword (word_join (h8:int64) h7:int128) (9,64);
      word_ushr h8 9] /\
    (a * b) MOD 2 EXP 521 =
    2 EXP 512 * val(word_and h0 (word 511):int64) +
    bignum_of_wordlist
     [mullo_s3; sum_s14; sum_s31; sum_s53;
      sum_s80; sum_s112; sum_s149; sum_s191]`
  (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
   [MATCH_MP_TAC DIVMOD_UNIQ THEN
    REWRITE_TAC[VAL_WORD_AND_MASK_WORD; ARITH_RULE `511 = 2 EXP 9 - 1`] THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) THEN
      CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
      ASM_REWRITE_TAC[ADD_ASSOC; EQ_ADD_RCANCEL] THEN
      REWRITE_TAC[bignum_of_wordlist; VAL_WORD_USHR] THEN
      SIMP_TAC[VAL_WORD_SUBWORD_JOIN_64; DIMINDEX_64; ARITH_LE; ARITH_LT] THEN
      ARITH_TAC;
      MATCH_MP_TAC(ARITH_RULE
       `x < 2 EXP (64 * 8) ==> 2 EXP 512 * h MOD 2 EXP 9 + x < 2 EXP 521`) THEN
      MATCH_MP_TAC BIGNUM_OF_WORDLIST_BOUND THEN REWRITE_TAC[LENGTH; ARITH]];
    ALL_TAC] THEN

  (*** The net comparison h + l >= p_521 ***)

  X86_ACCSTEPS_TAC P521_JSCALARMUL_ALT_EXEC (437--446) (437--446) THEN
  SUBGOAL_THEN
   `&(val(word_add (word_and h0 (word 511):int64) (word_ushr h8 9))):real =
    &(val(word_and h0 (word 511):int64)) + &(val(word_ushr h8 9:int64))`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_CLAUSES; VAL_WORD_ADD; DIMINDEX_64] THEN
    MATCH_MP_TAC MOD_LT THEN
    REWRITE_TAC[VAL_WORD_AND_MASK_WORD; ARITH_RULE `511 = 2 EXP 9 - 1`] THEN
    REWRITE_TAC[VAL_WORD_USHR] THEN
    MP_TAC(SPEC `h8:int64` VAL_BOUND_64) THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `carry_s446 <=> p_521 <= h + l` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `576` THEN
    MAP_EVERY EXPAND_TAC ["h"; "l"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_521] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN

  (*** The final correction ***)

  X86_ACCSTEPS_TAC P521_JSCALARMUL_ALT_EXEC (447--466) (447--466) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN CONV_TAC(RAND_CONV BIGNUM_LEXPAND_CONV) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  MAP_EVERY EXISTS_TAC
   [`521`;
    `if h + l < p_521 then &h + &l:real else (&h + &l) - &p_521`] THEN
  REPEAT CONJ_TAC THENL
   [BOUNDER_TAC[];
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    REWRITE_TAC[GSYM NOT_LT] THEN ABBREV_TAC `bb <=> h + l < p_521` THEN
    MAP_EVERY EXPAND_TAC ["h"; "l"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_521] THEN
    REWRITE_TAC[VAL_WORD_AND_MASK_WORD; ARITH_RULE `511 = 2 EXP 9 - 1`] THEN
    REWRITE_TAC[REAL_OF_NUM_MOD] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ASM_SIMP_TAC[MOD_CASES; ARITH_RULE
     `h < p /\ l <= p ==> h + l < 2 * p`] THEN
    SIMP_TAC[REAL_OF_NUM_CLAUSES; REAL_OF_NUM_SUB; COND_SWAP; GSYM NOT_LE] THEN
    MESON_TAC[]]);;

let LOCAL_MUL_P521_SUBR_CORRECT = prove
 (`!z x y a b pc stackpointer returnaddress.
        ALL (nonoverlapping (z,8 * 9))
            [(word pc,0x3f52); (word_sub stackpointer (word 72),80)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 72),72))
            [(word pc,0x3f52); (x,8 * 9); (y,8 * 9)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) p521_jscalarmul_alt_tmc /\
                  read RIP s = word(pc + 0x33ca) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,9) s = a /\
                  bignum_from_memory (y,9) s = b)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (a < p_521 /\ b < p_521
                   ==> bignum_from_memory (z,9) s = (a * b) MOD p_521))
             (MAYCHANGE [RIP; RSP; RAX; RBP; RBX; RCX; RDX; R8; R9;
                         R10; R11; R12; R13; R14; R15] ,,
              MAYCHANGE SOME_FLAGS ,,
              MAYCHANGE [memory :> bytes(z,8 * 9);
                       memory :> bytes(word_sub stackpointer (word 72),72)])`,
  X86_ADD_RETURN_STACK_TAC P521_JSCALARMUL_ALT_EXEC
    LOCAL_MUL_P521_CORRECT `[]:((x86state,(64)word)component)list` 72);;

(* ------------------------------------------------------------------------- *)
(* Level 2: the embedded point operations.                                   *)
(* ------------------------------------------------------------------------- *)

let lvs =
 ["x_1",[`RDI`;`0`];
  "y_1",[`RDI`;`72`];
  "z_1",[`RDI`;`144`];
  "x_3",[`RDI`;`0`];
  "y_3",[`RDI`;`72`];
  "z_3",[`RDI`;`144`];
  "z2",[`RSP`;`0`];
  "y2",[`RSP`;`72`];
  "x2p",[`RSP`;`144`];
  "xy2",[`RSP`;`216`];
  "y4",[`RSP`;`288`];
  "t2",[`RSP`;`288`];
  "dx2",[`RSP`;`360`];
  "t1",[`RSP`;`360`];
  "d",[`RSP`;`432`];
  "x4p",[`RSP`;`432`]];;

let PROLOGUE_SUBROUTINE_SIM_TAC corth inargs outarg m inouts =
  let main_tac =
     X86_SUBROUTINE_SIM_ABBREV_TAC
      (p521_jscalarmul_alt_tmc,P521_JSCALARMUL_ALT_EXEC,0,p521_jscalarmul_alt_tmc,corth)
      inargs outarg
  and k = length inouts + 1 in
  W(fun (asl,w) ->
    let dvar = mk_var(hd inouts,`:num`) in
    let dvar' =
      variant (rev_itlist (union o frees o concl o snd) asl []) dvar in
    let pcs = tryfind
      (find_term (can (term_match [] `read PC s`)) o concl o snd) asl in
    let sname = name_of(rand pcs) in
    let n = int_of_string (String.sub sname 1 (String.length sname - 1)) in
    X86_STEPS_TAC P521_JSCALARMUL_ALT_EXEC ((n+1)--(n+m+k)) THEN
    main_tac (name_of dvar') (n+m+k+1));;

let LOCAL_MUL_P521_TAC =
  PROLOGUE_SUBROUTINE_SIM_TAC LOCAL_MUL_P521_SUBR_CORRECT
   [`read RDI s`; `read RSI s`; `read RDX s`;
    `read (memory :> bytes(read RSI s,8 * 9)) s`;
    `read (memory :> bytes(read RDX s,8 * 9)) s`;
    `pc:num`; `read RSP s`; `read (memory :> bytes64(read RSP s)) s`]
   `read (memory :> bytes(read RDI s,8 * 9)) s'`;;

let LOCAL_SQR_P521_TAC =
  PROLOGUE_SUBROUTINE_SIM_TAC LOCAL_SQR_P521_SUBR_CORRECT
   [`read RDI s`; `read RSI s`;
    `read (memory :> bytes(read RSI s,8 * 9)) s`;
    `pc:num`; `read RSP s`; `read (memory :> bytes64(read RSP s)) s`]
   `read (memory :> bytes(read RDI s,8 * 9)) s'`;;

let LOCAL_ADD_P521_TAC =
  X86_MACRO_SIM_ABBREV_TAC p521_jscalarmul_alt_tmc 40 lvs
  `!(t:x86state) pcin pcout p3 n3 p1 n1 p2 n2.
    !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 9)) t = m
    ==>
    !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 9)) t = n
    ==>
    nonoverlapping (word pc,0x3f52) (word_add (read p3 t) (word n3),72)
    ==> ensures x86
         (\s. bytes_loaded s (word pc) p521_jscalarmul_alt_tmc /\
              read RIP s = pcin /\
              read RSP s = read RSP t /\
              read RDI s = read RDI t /\
              read RSI s = read RSI t /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 9)) s =
              m /\
              read(memory :> bytes(word_add (read p2 t) (word n2),8 * 9)) s =
              n)
         (\s. read RIP s = pcout /\
              (m < p_521 /\ n < p_521
               ==> read(memory :> bytes(word_add (read p3 t) (word n3),
                          8 * 9)) s = (m + n) MOD p_521))
         (MAYCHANGE [RIP; RAX; RDX; R8; R9; R10; R11; RBX; R12; R13; R14] ,,
          MAYCHANGE
           [memory :> bytes(word_add (read p3 t) (word n3),8 * 9)] ,,
          MAYCHANGE SOME_FLAGS)`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the m < p_521 /\ n < p_521 assumption ***)

  ASM_CASES_TAC `m < p_521 /\ n < p_521` THENL
   [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC);
    X86_SIM_TAC P521_JSCALARMUL_ALT_EXEC (1--40)] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "m_" o lhand o concl) THEN

  (*** Initial non-overflowing addition s = x + y + 1 ***)

  X86_ACCSTEPS_TAC P521_JSCALARMUL_ALT_EXEC [3;5;7;9;11;13;15;17;19] (1--19) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist
     [sum_s3;sum_s5;sum_s7;sum_s9;sum_s11;sum_s13;sum_s15;sum_s17;sum_s19] =
    m + n + 1`
  ASSUME_TAC THENL
   [REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`576`; `&0:real`] THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`m < p_521`; `n < p_521`] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_LT; GSYM REAL_OF_NUM_ADD] THEN
      REWRITE_TAC[p_521] THEN REAL_ARITH_TAC;
      REWRITE_TAC[INTEGER_CLOSED]] THEN
    MAP_EVERY EXPAND_TAC ["m"; "n"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** The net comparison s >= 2^521 <=> x + y >= p_521 ***)

  X86_STEPS_TAC P521_JSCALARMUL_ALT_EXEC (20--21) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [SYM(NUM_REDUCE_CONV `2 EXP 9`); GSYM WORD_OF_BITS_SING_AS_WORD;
    WORD_OF_BITS_SING_AND_WORD]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [WORD_OF_BITS_SING_AS_WORD; NUM_REDUCE_CONV `2 EXP 9`]) THEN
  SUBGOAL_THEN `bit 9 (sum_s19:int64) <=> p_521 <= m + n` SUBST_ALL_TAC THENL
   [REWRITE_TAC[BIT_VAL_MOD] THEN
    SUBGOAL_THEN `val(sum_s19:int64) = (m + n + 1) DIV 2 EXP 512`
    SUBST1_TAC THENL
     [FIRST_X_ASSUM(fun th ->
        GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [SYM th]) THEN
      CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
      REWRITE_TAC[];
      MATCH_MP_TAC(MESON[MOD_LT]
       `y < n /\ (x <= y <=> q) ==> (x <= y MOD n <=> q)`) THEN
      MAP_EVERY UNDISCH_TAC [`m < p_521`; `n < p_521`] THEN
      REWRITE_TAC[p_521] THEN ARITH_TAC];
    ALL_TAC] THEN
  X86_STEPS_TAC P521_JSCALARMUL_ALT_EXEC [22] THEN
  SUBGOAL_THEN
   `val(if p_521 <= m + n then word 512 else word 0:int64) < 512 <=>
    ~(p_521 <= m + n)`
  SUBST_ALL_TAC THENL
   [COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN

  (*** The final optional subtraction of either 1 or 2^521 ***)

  X86_ACCSTEPS_TAC P521_JSCALARMUL_ALT_EXEC
   [23;25;27;29;31;33;35;37;39] (23--40) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN CONV_TAC(RAND_CONV BIGNUM_LEXPAND_CONV) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  MAP_EVERY EXISTS_TAC
   [`64 * 9`;
    `if p_521 <= m + n then &(m + n + 1) - &2 pow 521
     else &(m + n + 1) - &1:real`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC BIGNUM_OF_WORDLIST_BOUND THEN
    REWRITE_TAC[LENGTH] THEN ARITH_TAC;
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    ALL_TAC;
    ASM_SIMP_TAC[MOD_ADD_CASES; GSYM NOT_LE; COND_SWAP] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_521] THEN REAL_ARITH_TAC] THEN
  ABBREV_TAC `s = m + n + 1` THEN POP_ASSUM(K ALL_TAC) THEN EXPAND_TAC "s" THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
  REWRITE_TAC[WORD_AND_MASK; GSYM NOT_LE] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let GENERAL_SUB_P521_TAC localvars =
  X86_MACRO_SIM_ABBREV_TAC p521_jscalarmul_alt_tmc 37 localvars
  `!(t:x86state) pcin pcout p3 n3 p1 n1 p2 n2.
    !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 9)) t = m
    ==>
    !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 9)) t = n
    ==>
    nonoverlapping (word pc,0x3f52) (word_add (read p3 t) (word n3),72)
    ==> ensures x86
         (\s. bytes_loaded s (word pc) p521_jscalarmul_alt_tmc /\
              read RIP s = pcin /\
              read RSP s = read RSP t /\
              read RDI s = read RDI t /\
              read RSI s = read RSI t /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 9)) s =
              m /\
              read(memory :> bytes(word_add (read p2 t) (word n2),8 * 9)) s =
              n)
         (\s. read RIP s = pcout /\
              (m < p_521 /\ n < p_521
               ==> &(read(memory :> bytes(word_add (read p3 t) (word n3),
                          8 * 9)) s) = (&m - &n) rem &p_521))
         (MAYCHANGE [RIP; RAX; RDX; R8; R9; R10; R11; RBX; R12; R13; R14] ,,
          MAYCHANGE
           [memory :> bytes(word_add (read p3 t) (word n3),8 * 9)] ,,
          MAYCHANGE SOME_FLAGS)`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "m_" o lhand o concl) THEN

  (*** Initial subtraction x - y, comparison result ***)

  X86_ACCSTEPS_TAC P521_JSCALARMUL_ALT_EXEC [2;4;6;8;10;12;14;16;18] (1--18) THEN

  SUBGOAL_THEN `carry_s18 <=> m < n` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `576` THEN
    MAP_EVERY EXPAND_TAC ["m"; "n"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN

  (*** Further optional subtraction mod 2^521 ***)

  X86_ACCSTEPS_TAC P521_JSCALARMUL_ALT_EXEC
   [19;21;23;25;27;29;31;33;35] (19--37) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN

  (*** Map things into the reals, doing case analysis over comparison ***)

  TRANS_TAC EQ_TRANS `if m < n then &m - &n + &p_521:int else &m - &n` THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[int_eq] THEN ONCE_REWRITE_TAC[COND_RAND] THEN
   REWRITE_TAC[int_of_num_th; int_sub_th; int_add_th];
   CONV_TAC SYM_CONV THEN MATCH_MP_TAC INT_REM_UNIQ THEN
   EXISTS_TAC `if m:num < n then --(&1):int else &0` THEN
   MAP_EVERY UNDISCH_TAC [`m < p_521`; `n < p_521`] THEN
   REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; p_521] THEN INT_ARITH_TAC] THEN

  (*** Hence show that we get the right result in 521 bits ***)

  CONV_TAC SYM_CONV THEN
  CONV_TAC(RAND_CONV(RAND_CONV BIGNUM_LEXPAND_CONV)) THEN
  ASM_REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 9 - 1`)] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`521`; `&0:real`] THEN CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`m < p_521`; `n < p_521`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_521] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0] THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(8,1)] THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_SING; VAL_WORD_AND_MASK_WORD] THEN
    MATCH_MP_TAC(ARITH_RULE
     `x < 2 EXP (64 * 8) ==> x + 2 EXP 512 * n MOD 2 EXP 9 < 2 EXP 521`) THEN
    MATCH_MP_TAC BIGNUM_OF_WORDLIST_BOUND THEN
    REWRITE_TAC[LENGTH] THEN ARITH_TAC;
    REWRITE_TAC[INTEGER_CLOSED]] THEN
  ABBREV_TAC `bb <=> m:num < n` THEN MAP_EVERY EXPAND_TAC ["m"; "n"] THEN
  REWRITE_TAC[bignum_of_wordlist; VAL_WORD_AND_MASK_WORD] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_MOD; p_521] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let LOCAL_SUB_P521_TAC = GENERAL_SUB_P521_TAC lvs;;

let LOCAL_CMSUBC9_P521_TAC =
  X86_MACRO_SIM_ABBREV_TAC p521_jscalarmul_alt_tmc 138 lvs
  `!(t:x86state) pcin pcout p3 n3 p1 n1 p2 n2.
    !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 9)) t = m
    ==>
    !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 9)) t = n
    ==> nonoverlapping (word pc,0x3f52) (word_add (read p3 t) (word n3),72)
    ==> ensures x86
         (\s. bytes_loaded s (word pc) p521_jscalarmul_alt_tmc /\
              read RIP s = pcin /\
              read RSP s = read RSP t /\
              read RDI s = read RDI t /\
              read RSI s = read RSI t /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 9)) s =
              m /\
              read(memory :> bytes(word_add (read p2 t) (word n2),8 * 9)) s =
              n)
         (\s. read RIP s = pcout /\
              (m < 2 * p_521 /\ n <= p_521
               ==> &(read(memory :> bytes(word_add (read p3 t) (word n3),
                     8 * 9)) s) = (&12 * &m - &9 * &n) rem &p_521))
            (MAYCHANGE [RIP; RAX; RBX; RBP; RCX; RDX; R8; R9;
                        R10; R11; R12; R13; R14; R15] ,,
             MAYCHANGE
               [memory :> bytes(word_add (read p3 t) (word n3),8 * 9)] ,,
              MAYCHANGE SOME_FLAGS)`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the bound assumption for simplicity ***)

  ASM_CASES_TAC `m < 2 * p_521 /\ n <= p_521` THENL
   [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC);
    X86_SIM_TAC P521_JSCALARMUL_ALT_EXEC (1--138)] THEN

  (*** Digitize and introduce the sign-flipped version of n ***)

  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "m_" o lhand o concl) THEN
  ABBREV_TAC
   `n' = bignum_of_wordlist
    [word_not n_0; word_not n_1; word_not n_2; word_not n_3; word_not n_4;
     word_not n_5; word_not n_6; word_not n_7; word_xor n_8 (word 0x1FF)]` THEN

  SUBGOAL_THEN `p_521 - n = n'` ASSUME_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `n + m:num = p ==> p - n = m`) THEN
    MAP_EVERY EXPAND_TAC ["n"; "n'"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    SUBGOAL_THEN
     `&(val(word_xor (n_8:int64) (word 511))):real = &2 pow 9 - &1 - &(val n_8)`
    SUBST1_TAC THENL
     [REWRITE_TAC[REAL_VAL_WORD_XOR];
      REWRITE_TAC[REAL_VAL_WORD_NOT; DIMINDEX_64; p_521] THEN
      REAL_ARITH_TAC] THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC(REAL_ARITH
     `n':real = n ==> (n + c) - &2 * n' = c - n`) THEN
    REWRITE_TAC[VAL_WORD_AND_MASK_WORD; ARITH_RULE `511 = 2 EXP 9 - 1`] THEN
    REWRITE_TAC[REAL_OF_NUM_EQ] THEN MATCH_MP_TAC MOD_LT THEN
    UNDISCH_TAC `n <= p_521` THEN
    DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
     `n <= p ==> n DIV 2 EXP 512 <= p DIV 2 EXP 512`)) THEN
    EXPAND_TAC "n" THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    ALL_TAC] THEN

  SUBGOAL_THEN
   `(&12 * &m - &9 * &n) rem &p_521 =
    (&12 * &m + &9 * (&p_521 - &n)) rem &p_521`
  SUBST1_TAC THENL
   [REWRITE_TAC[INT_REM_EQ] THEN CONV_TAC INTEGER_RULE;
    ASM_SIMP_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_SUB; INT_OF_NUM_REM]] THEN

  (*** The basic multiply-add block = ca, then forget the components ***)

  ABBREV_TAC `ca = 12 * m + 9 * n'` THEN
  SUBGOAL_THEN `ca < 2 EXP 527` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["ca"; "n'"] THEN UNDISCH_TAC `m < 2 * p_521` THEN
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    ALL_TAC] THEN

  X86_GEN_ACCSTEPS_TAC
   (fun _ -> RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
                `word_sub x (word_neg y):int64 = word_add x y`]) THEN
              RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
               `word_mul x (word n) = word(0 + val x * n)`]))
    P521_JSCALARMUL_ALT_EXEC
     [4;9;11;12;15;17;18;21;23;24;27;29;30;33;35;36;39;41;
      42;45;47;48;51;52;56;57;58;61;62;63;64;67;68;69;70;
      73;74;75;76;79;80;81;82;85;86;87;88;91;92;93;94;97;
      98;99;100;102;103;115;117;119;120;122;124;126;128;130;132;134;136]
     (1--103) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist
     [sum_s57; sum_s63; sum_s69; sum_s75;
      sum_s81; sum_s87; sum_s93; sum_s99; sum_s103] = ca`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`576`; `&0:real`] THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "ca" THEN CONJ_TAC THENL
     [UNDISCH_TAC `m < 2 * p_521` THEN EXPAND_TAC "n'" THEN
      REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0; p_521] THEN ARITH_TAC;
      REWRITE_TAC[INTEGER_CLOSED]] THEN
    UNDISCH_THEN `p_521 - n = n'` (K ALL_TAC) THEN
    MAP_EVERY EXPAND_TAC ["m"; "n'"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
    REWRITE_TAC[REAL_VAL_WORD_NOT; DIMINDEX_64] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o
      filter (is_ratconst o rand o concl) o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `m:num` o concl))) THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `n:num` o concl))) THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `n':num` o concl)))] THEN

  (*** Breaking the problem down to (h + l) MOD p_521 ***)

  SUBGOAL_THEN `ca MOD p_521 = (ca DIV 2 EXP 521 + ca MOD 2 EXP 521) MOD p_521`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)
     [ARITH_RULE `ca = 2 EXP 521 * ca DIV 2 EXP 521 + ca MOD 2 EXP 521`] THEN
    REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC(NUMBER_RULE
     `(e == 1) (mod p) ==> (e * h + l == h + l) (mod p)`) THEN
    REWRITE_TAC[p_521; CONG] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `ca DIV 2 EXP 521 < 2 EXP 64 /\ ca MOD 2 EXP 521 < 2 EXP 521`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MOD_LT_EQ] THEN UNDISCH_TAC `ca < 2 EXP 527` THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** Splitting up and stuffing 1 bits into the low part ***)

  X86_STEPS_TAC P521_JSCALARMUL_ALT_EXEC (104--113) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_AND_ASSOC; DIMINDEX_64]) THEN
  MAP_EVERY ABBREV_TAC
   [`h:int64 = word_ushr sum_s103 9`;
    `d:int64 = word_or sum_s103 (word 18446744073709551104)`;
    `dd:int64 = word_and sum_s63 (word_and sum_s69 (word_and sum_s75
      (word_and sum_s81 (word_and sum_s87 (word_and sum_s93 sum_s99)))))`] THEN

  (*** The comparison in its direct condensed form ***)

  X86_ACCSTEPS_TAC P521_JSCALARMUL_ALT_EXEC [115;117;119] (114--119) THEN

  SUBGOAL_THEN
   `&(val (word_add h (word 1):int64)):real = &(val h) + &1`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_CLAUSES; VAL_WORD_ADD_CASES] THEN
    REWRITE_TAC[DIMINDEX_64; VAL_WORD_1] THEN
    MATCH_MP_TAC(MESON[] `p ==> (if p then x else y) = x`) THEN
    SUBST1_TAC(SYM(ASSUME `word_ushr sum_s103 9 = (h:int64)`)) THEN
    CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `carry_s119 <=>
    2 EXP 192 <=
      2 EXP 128 * val(d:int64) + 2 EXP 64 * val(dd:int64) +
      val(h:int64) + val(sum_s57:int64) + 1`
  (ASSUME_TAC o SYM) THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `192` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Finish the simulation before completing the mathematics ***)

  X86_ACCSTEPS_TAC P521_JSCALARMUL_ALT_EXEC
   [120;122;124;126;128;130;132;134;136] (120--138) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  DISCARD_STATE_TAC "s138" THEN

  (*** Evaluate d and un-condense the inequality ***)

  SUBGOAL_THEN
   `val(d:int64) = 2 EXP 9 * (2 EXP 55 - 1) + val(sum_s103:int64) MOD 2 EXP 9`
  SUBST_ALL_TAC THENL
   [EXPAND_TAC "d" THEN ONCE_REWRITE_TAC[WORD_BITWISE_RULE
     `word_or a b = word_or b (word_and a (word_not b))`] THEN
    SIMP_TAC[VAL_WORD_OR_DISJOINT; WORD_BITWISE_RULE
     `word_and x (word_and y (word_not x)) = word 0`] THEN
    REWRITE_TAC[GSYM VAL_WORD_AND_MASK_WORD] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV;
    ALL_TAC] THEN

  SUBGOAL_THEN
   `2 EXP 512 * val(sum_s103:int64) MOD 2 EXP 9 +
    bignum_of_wordlist
     [sum_s57; sum_s63; sum_s69; sum_s75; sum_s81; sum_s87; sum_s93; sum_s99] =
    ca MOD 2 EXP 521`
  (LABEL_TAC "*") THENL
   [CONV_TAC SYM_CONV THEN EXPAND_TAC "ca" THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(8,1)] THEN
    REWRITE_TAC[ARITH_RULE `2 EXP 521 = 2 EXP 512 * 2 EXP 9`] THEN
    REWRITE_TAC[SYM(NUM_REDUCE_CONV `64 * 8`)] THEN
    SIMP_TAC[LENGTH; ARITH_LT; ARITH_LE; MOD_MULT_MOD; ADD_CLAUSES;
             ARITH_SUC; BIGNUM_OF_WORDLIST_BOUND; MOD_LT; DIV_LT;
             MOD_MULT_ADD; DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_SING] THEN ARITH_TAC;
    ALL_TAC] THEN

  SUBGOAL_THEN
   `2 EXP 521 <= ca MOD 2 EXP 521 + val(h:int64) + 1 <=> carry_s119`
   MP_TAC THENL
   [REMOVE_THEN "*" (SUBST1_TAC o SYM) THEN EXPAND_TAC "carry_s119" THEN
    ONCE_REWRITE_TAC[bignum_of_wordlist] THEN
    MATCH_MP_TAC(TAUT
     `!p q. ((p ==> ~r) /\ (q ==> ~s)) /\ (p <=> q) /\ (~p /\ ~q ==> (r <=> s))
            ==> (r <=> s)`) THEN
    MAP_EVERY EXISTS_TAC
     [`bignum_of_wordlist
        [sum_s63; sum_s69; sum_s75; sum_s81; sum_s87; sum_s93; sum_s99] <
       2 EXP (64 * 7) - 1`;
      `val(dd:int64) < 2 EXP 64 - 1`] THEN
    CONJ_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC(ARITH_RULE
      `2 EXP 64 * b + d < 2 EXP 64 * (a + 1) + c ==> a < b ==> ~(c <= d)`) THEN
      MP_TAC(SPEC `h:int64` VAL_BOUND_64) THEN
      MP_TAC(SPEC `sum_s57:int64` VAL_BOUND_64) THEN ARITH_TAC;
      SIMP_TAC[BIGNUM_OF_WORDLIST_LT_MAX; LENGTH; ARITH_EQ; ARITH_SUC]] THEN
    REWRITE_TAC[GSYM NOT_ALL] THEN MP_TAC(ISPEC `dd:int64` VAL_EQ_MAX) THEN
    SIMP_TAC[VAL_BOUND_64; DIMINDEX_64; ARITH_RULE
      `a < n ==> (a < n - 1 <=> ~(a = n - 1))`] THEN
    DISCH_THEN SUBST1_TAC THEN EXPAND_TAC "dd" THEN
    REWRITE_TAC[WORD_NOT_AND; ALL; WORD_OR_EQ_0] THEN
    REWRITE_TAC[WORD_RULE `word_not d = e <=> d = word_not e`] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC) THEN
    REWRITE_TAC[bignum_of_wordlist] THEN CONV_TAC WORD_REDUCE_CONV THEN
    MP_TAC(ARITH_RULE `val(sum_s103:int64) MOD 2 EXP 9 = 511 \/
                       val(sum_s103:int64) MOD 2 EXP 9 < 511`) THEN
    MP_TAC(SPEC `h:int64` VAL_BOUND_64) THEN
    MP_TAC(SPEC `sum_s57:int64` VAL_BOUND_64) THEN ARITH_TAC;
    FIRST_X_ASSUM(K ALL_TAC o check (is_iff o concl))] THEN

  (*** Also evaluate h ***)

  SUBGOAL_THEN `val(h:int64) = ca DIV 2 EXP 521` SUBST_ALL_TAC THENL
   [EXPAND_TAC "h" THEN REWRITE_TAC[VAL_WORD_USHR] THEN
    EXPAND_TAC "ca" THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN

  (*** Now complete the mathematics ***)

  SUBGOAL_THEN
   `2 EXP 521 <= ca MOD 2 EXP 521 + ca DIV 2 EXP 521 + 1 <=>
    p_521 <= ca DIV 2 EXP 521 + ca MOD 2 EXP 521`
  SUBST1_TAC THENL [REWRITE_TAC[p_521] THEN ARITH_TAC; DISCH_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  MAP_EVERY EXISTS_TAC
   [`521`;
    `if ca DIV 2 EXP 521 + ca MOD 2 EXP 521 < p_521
     then &(ca DIV 2 EXP 521 + ca MOD 2 EXP 521)
     else &(ca DIV 2 EXP 521 + ca MOD 2 EXP 521) - &p_521`] THEN
  REPEAT CONJ_TAC THENL
   [BOUNDER_TAC[];
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    ALL_TAC;
    W(MP_TAC o PART_MATCH (lhand o rand) MOD_CASES o rand o lhand o snd) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `ca < 2 EXP 527` THEN REWRITE_TAC[p_521] THEN ARITH_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN
    SIMP_TAC[GSYM NOT_LE; COND_SWAP; GSYM REAL_OF_NUM_SUB; COND_ID]] THEN
  ASM_REWRITE_TAC[GSYM NOT_LE; COND_SWAP] THEN
  REMOVE_THEN "*" (SUBST1_TAC o SYM) THEN
  REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 9 - 1`)] THEN
  REWRITE_TAC[VAL_WORD_AND_MASK_WORD; bignum_of_wordlist] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_MOD; p_521] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let LOCAL_CMSUB41_P521_TAC =
  X86_MACRO_SIM_ABBREV_TAC p521_jscalarmul_alt_tmc 80 lvs
  `!(t:x86state) pcin pcout p3 n3 p1 n1 p2 n2.
    !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 9)) t = m
    ==>
    !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 9)) t = n
    ==> nonoverlapping (word pc,0x3f52) (word_add (read p3 t) (word n3),72)
    ==> ensures x86
         (\s. bytes_loaded s (word pc) p521_jscalarmul_alt_tmc /\
              read RIP s = pcin /\
              read RSP s = read RSP t /\
              read RDI s = read RDI t /\
              read RSI s = read RSI t /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 9)) s =
              m /\
              read(memory :> bytes(word_add (read p2 t) (word n2),8 * 9)) s =
              n)
         (\s. read RIP s = pcout /\
              (m < 2 * p_521 /\ n <= p_521
               ==> &(read(memory :> bytes(word_add (read p3 t) (word n3),
                     8 * 9)) s) = (&4 * &m - &n) rem &p_521))
            (MAYCHANGE [RIP; RAX; RBX; RCX; RDX; R8; R9;
                        R10; R11; R12; R13; R14; R15] ,,
             MAYCHANGE
               [memory :> bytes(word_add (read p3 t) (word n3),8 * 9)] ,,
              MAYCHANGE SOME_FLAGS)`

 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the bound assumption for simplicity ***)

  ASM_CASES_TAC `m < 2 * p_521 /\ n <= p_521` THENL
   [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC);
    X86_SIM_TAC P521_JSCALARMUL_ALT_EXEC (1--80)] THEN

  (*** Digitize and introduce the sign-flipped version of n ***)

  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "m_" o lhand o concl) THEN
  ABBREV_TAC
   `n' = bignum_of_wordlist
    [word_not n_0; word_not n_1; word_not n_2; word_not n_3; word_not n_4;
     word_not n_5; word_not n_6; word_not n_7; word_xor n_8 (word 0x1FF)]` THEN

  SUBGOAL_THEN `p_521 - n = n'` ASSUME_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `n + m:num = p ==> p - n = m`) THEN
    MAP_EVERY EXPAND_TAC ["n"; "n'"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    SUBGOAL_THEN
     `&(val(word_xor (n_8:int64) (word 511))):real = &2 pow 9 - &1 - &(val n_8)`
    SUBST1_TAC THENL
     [REWRITE_TAC[REAL_VAL_WORD_XOR];
      REWRITE_TAC[REAL_VAL_WORD_NOT; DIMINDEX_64; p_521] THEN
      REAL_ARITH_TAC] THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC(REAL_ARITH
     `n':real = n ==> (n + c) - &2 * n' = c - n`) THEN
    REWRITE_TAC[VAL_WORD_AND_MASK_WORD; ARITH_RULE `511 = 2 EXP 9 - 1`] THEN
    REWRITE_TAC[REAL_OF_NUM_EQ] THEN MATCH_MP_TAC MOD_LT THEN
    UNDISCH_TAC `n <= p_521` THEN
    DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
     `n <= p ==> n DIV 2 EXP 512 <= p DIV 2 EXP 512`)) THEN
    EXPAND_TAC "n" THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** Now introduce the shifted version of m ***)

  ABBREV_TAC
   `m' = bignum_of_wordlist
     [word_shl m_0 2;
      word_subword ((word_join:int64->int64->int128) m_1 m_0) (62,64);
      word_subword ((word_join:int64->int64->int128) m_2 m_1) (62,64);
      word_subword ((word_join:int64->int64->int128) m_3 m_2) (62,64);
      word_subword ((word_join:int64->int64->int128) m_4 m_3) (62,64);
      word_subword ((word_join:int64->int64->int128) m_5 m_4) (62,64);
      word_subword ((word_join:int64->int64->int128) m_6 m_5) (62,64);
      word_subword ((word_join:int64->int64->int128) m_7 m_6) (62,64);
      word_subword ((word_join:int64->int64->int128) m_8 m_7) (62,64)]` THEN
  SUBGOAL_THEN `4 * m = m'` ASSUME_TAC THENL
   [SUBGOAL_THEN `m DIV 2 EXP 512 < 2 EXP 62` MP_TAC THENL
     [UNDISCH_TAC `m < 2 * p_521` THEN REWRITE_TAC[p_521] THEN ARITH_TAC;
      EXPAND_TAC "m" THEN
      CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
      REWRITE_TAC[GSYM UPPER_BITS_ZERO]] THEN
    EXPAND_TAC "m'" THEN POP_ASSUM_LIST(K ALL_TAC) THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `62` th) THEN MP_TAC(SPEC `63` th)) THEN
    CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN DISCH_TAC THEN
    REWRITE_TAC[bignum_of_wordlist; REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[val_def; DIMINDEX_64; bignum_of_wordlist] THEN
    REWRITE_TAC[ARITH_RULE `i < 64 <=> 0 <= i /\ i <= 63`] THEN
    REWRITE_TAC[GSYM IN_NUMSEG; IN_GSPEC] THEN
    REWRITE_TAC[BIT_WORD_SUBWORD; BIT_WORD_JOIN; BIT_WORD_USHR;
                BIT_WORD_SHL; DIMINDEX_64; DIMINDEX_128] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC(ONCE_DEPTH_CONV EXPAND_NSUM_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
    CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[BITVAL_CLAUSES] THEN
    CONV_TAC NUM_RING;
    ALL_TAC] THEN

  SUBGOAL_THEN
   `(&4 * &m - &n) rem &p_521 =
    (&4 * &m + (&p_521 - &n)) rem &p_521`
  SUBST1_TAC THENL
   [REWRITE_TAC[INT_REM_EQ] THEN CONV_TAC INTEGER_RULE;
    ASM_SIMP_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_SUB; INT_OF_NUM_REM]] THEN

  (*** The basic multiply-add block = ca, then forget the components ***)

  ABBREV_TAC `ca:num = m' + n'` THEN
  SUBGOAL_THEN `ca < 2 EXP 527` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["ca"; "m'"; "n'"] THEN
    UNDISCH_TAC `m < 2 * p_521` THEN
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    ALL_TAC] THEN

  X86_ACCSTEPS_TAC P521_JSCALARMUL_ALT_EXEC
   [23;26;29;32;35;38;41;44;45] (1--45) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist
     [sum_s23; sum_s26; sum_s29; sum_s32;
      sum_s35; sum_s38; sum_s41; sum_s44; sum_s45] = ca`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`576`; `&0:real`] THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
     [UNDISCH_TAC `ca < 2 EXP 527` THEN REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
      ARITH_TAC;
      REWRITE_TAC[INTEGER_CLOSED] THEN EXPAND_TAC "ca"] THEN
    UNDISCH_THEN `p_521 - n = n'` (K ALL_TAC) THEN
    UNDISCH_THEN `4 * m = m'` (K ALL_TAC) THEN
    MAP_EVERY EXPAND_TAC ["m'"; "n'"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
    REWRITE_TAC[REAL_VAL_WORD_NOT; DIMINDEX_64] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `m:num` o concl))) THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `n:num` o concl))) THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `n':num` o concl)))] THEN

  (*** Breaking the problem down to (h + l) MOD p_521 ***)

  SUBGOAL_THEN `ca MOD p_521 = (ca DIV 2 EXP 521 + ca MOD 2 EXP 521) MOD p_521`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)
     [ARITH_RULE `ca = 2 EXP 521 * ca DIV 2 EXP 521 + ca MOD 2 EXP 521`] THEN
    REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC(NUMBER_RULE
     `(e == 1) (mod p) ==> (e * h + l == h + l) (mod p)`) THEN
    REWRITE_TAC[p_521; CONG] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `ca DIV 2 EXP 521 < 2 EXP 64 /\ ca MOD 2 EXP 521 < 2 EXP 521`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MOD_LT_EQ] THEN UNDISCH_TAC `ca < 2 EXP 527` THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** Splitting up and stuffing 1 bits into the low part ***)

  X86_STEPS_TAC P521_JSCALARMUL_ALT_EXEC (46--55) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_AND_ASSOC; DIMINDEX_64]) THEN
  MAP_EVERY ABBREV_TAC
   [`h:int64 = word_ushr sum_s45 9`;
    `d:int64 = word_or sum_s45 (word 18446744073709551104)`;
    `dd:int64 = word_and sum_s26 (word_and sum_s29 (word_and sum_s32
      (word_and sum_s35 (word_and sum_s38 (word_and sum_s41 sum_s44)))))`] THEN

  (*** The comparison in its direct condensed form ***)

  X86_ACCSTEPS_TAC P521_JSCALARMUL_ALT_EXEC [57;59;61] (56--61) THEN

  SUBGOAL_THEN
   `&(val (word_add h (word 1):int64)):real = &(val h) + &1`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_CLAUSES; VAL_WORD_ADD_CASES] THEN
    REWRITE_TAC[DIMINDEX_64; VAL_WORD_1] THEN
    MATCH_MP_TAC(MESON[] `p ==> (if p then x else y) = x`) THEN
    SUBST1_TAC(SYM(ASSUME `word_ushr sum_s45 9 = (h:int64)`)) THEN
    CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `carry_s61 <=>
    2 EXP 192 <=
      2 EXP 128 * val(d:int64) + 2 EXP 64 * val(dd:int64) +
      val(h:int64) + val(sum_s23:int64) + 1`
  (ASSUME_TAC o SYM) THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `192` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Finish the simulation before completing the mathematics ***)

  X86_ACCSTEPS_TAC P521_JSCALARMUL_ALT_EXEC
   [62;64;66;68;70;72;74;76;78] (62--80) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  DISCARD_STATE_TAC "s80" THEN

  (*** Evaluate d and un-condense the inequality ***)

  SUBGOAL_THEN
   `val(d:int64) = 2 EXP 9 * (2 EXP 55 - 1) + val(sum_s45:int64) MOD 2 EXP 9`
  SUBST_ALL_TAC THENL
   [EXPAND_TAC "d" THEN ONCE_REWRITE_TAC[WORD_BITWISE_RULE
     `word_or a b = word_or b (word_and a (word_not b))`] THEN
    SIMP_TAC[VAL_WORD_OR_DISJOINT; WORD_BITWISE_RULE
     `word_and x (word_and y (word_not x)) = word 0`] THEN
    REWRITE_TAC[GSYM VAL_WORD_AND_MASK_WORD] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV;
    ALL_TAC] THEN

  SUBGOAL_THEN
   `2 EXP 512 * val(sum_s45:int64) MOD 2 EXP 9 +
    bignum_of_wordlist
     [sum_s23; sum_s26; sum_s29; sum_s32; sum_s35; sum_s38; sum_s41; sum_s44] =
    ca MOD 2 EXP 521`
  (LABEL_TAC "*") THENL
   [CONV_TAC SYM_CONV THEN EXPAND_TAC "ca" THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(8,1)] THEN
    REWRITE_TAC[ARITH_RULE `2 EXP 521 = 2 EXP 512 * 2 EXP 9`] THEN
    REWRITE_TAC[SYM(NUM_REDUCE_CONV `64 * 8`)] THEN
    SIMP_TAC[LENGTH; ARITH_LT; ARITH_LE; MOD_MULT_MOD; ADD_CLAUSES;
             ARITH_SUC; BIGNUM_OF_WORDLIST_BOUND; MOD_LT; DIV_LT;
             MOD_MULT_ADD; DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_SING] THEN ARITH_TAC;
    ALL_TAC] THEN

  SUBGOAL_THEN
   `2 EXP 521 <= ca MOD 2 EXP 521 + val(h:int64) + 1 <=> carry_s61`
  MP_TAC THENL
   [REMOVE_THEN "*" (SUBST1_TAC o SYM) THEN EXPAND_TAC "carry_s61" THEN
    ONCE_REWRITE_TAC[bignum_of_wordlist] THEN
    MATCH_MP_TAC(TAUT
     `!p q. ((p ==> ~r) /\ (q ==> ~s)) /\ (p <=> q) /\ (~p /\ ~q ==> (r <=> s))
            ==> (r <=> s)`) THEN
    MAP_EVERY EXISTS_TAC
     [`bignum_of_wordlist
        [sum_s26; sum_s29; sum_s32; sum_s35; sum_s38; sum_s41; sum_s44] <
       2 EXP (64 * 7) - 1`;
      `val(dd:int64) < 2 EXP 64 - 1`] THEN
    CONJ_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC(ARITH_RULE
      `2 EXP 64 * b + d < 2 EXP 64 * (a + 1) + c ==> a < b ==> ~(c <= d)`) THEN
      MP_TAC(SPEC `h:int64` VAL_BOUND_64) THEN
      MP_TAC(SPEC `sum_s23:int64` VAL_BOUND_64) THEN ARITH_TAC;
      SIMP_TAC[BIGNUM_OF_WORDLIST_LT_MAX; LENGTH; ARITH_EQ; ARITH_SUC]] THEN
    REWRITE_TAC[GSYM NOT_ALL] THEN MP_TAC(ISPEC `dd:int64` VAL_EQ_MAX) THEN
    SIMP_TAC[VAL_BOUND_64; DIMINDEX_64; ARITH_RULE
      `a < n ==> (a < n - 1 <=> ~(a = n - 1))`] THEN
    DISCH_THEN SUBST1_TAC THEN EXPAND_TAC "dd" THEN
    REWRITE_TAC[WORD_NOT_AND; ALL; WORD_OR_EQ_0] THEN
    REWRITE_TAC[WORD_RULE `word_not d = e <=> d = word_not e`] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC) THEN
    REWRITE_TAC[bignum_of_wordlist] THEN CONV_TAC WORD_REDUCE_CONV THEN
    MP_TAC(ARITH_RULE `val(sum_s45:int64) MOD 2 EXP 9 = 511 \/
                       val(sum_s45:int64) MOD 2 EXP 9 < 511`) THEN
    MP_TAC(SPEC `h:int64` VAL_BOUND_64) THEN
    MP_TAC(SPEC `sum_s23:int64` VAL_BOUND_64) THEN ARITH_TAC;
    FIRST_X_ASSUM(K ALL_TAC o check (is_iff o concl))] THEN

  (*** Also evaluate h ***)

  SUBGOAL_THEN `val(h:int64) = ca DIV 2 EXP 521` SUBST_ALL_TAC THENL
   [EXPAND_TAC "h" THEN REWRITE_TAC[VAL_WORD_USHR] THEN
    EXPAND_TAC "ca" THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN

  (*** Now complete the mathematics ***)

  SUBGOAL_THEN
   `2 EXP 521 <= ca MOD 2 EXP 521 + ca DIV 2 EXP 521 + 1 <=>
    p_521 <= ca DIV 2 EXP 521 + ca MOD 2 EXP 521`
  SUBST1_TAC THENL [REWRITE_TAC[p_521] THEN ARITH_TAC; DISCH_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  MAP_EVERY EXISTS_TAC
   [`521`;
    `if ca DIV 2 EXP 521 + ca MOD 2 EXP 521 < p_521
     then &(ca DIV 2 EXP 521 + ca MOD 2 EXP 521)
     else &(ca DIV 2 EXP 521 + ca MOD 2 EXP 521) - &p_521`] THEN
  REPEAT CONJ_TAC THENL
   [BOUNDER_TAC[];
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    ALL_TAC;
    W(MP_TAC o PART_MATCH (lhand o rand) MOD_CASES o rand o lhand o snd) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `ca < 2 EXP 527` THEN REWRITE_TAC[p_521] THEN ARITH_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN
    SIMP_TAC[GSYM NOT_LE; COND_SWAP; GSYM REAL_OF_NUM_SUB; COND_ID]] THEN
  ASM_REWRITE_TAC[GSYM NOT_LE; COND_SWAP] THEN
  REMOVE_THEN "*" (SUBST1_TAC o SYM) THEN
  REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 9 - 1`)] THEN
  REWRITE_TAC[VAL_WORD_AND_MASK_WORD; bignum_of_wordlist] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_MOD; p_521] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let LOCAL_CMSUB38_P521_TAC =
  X86_MACRO_SIM_ABBREV_TAC p521_jscalarmul_alt_tmc 112 lvs
  `!(t:x86state) pcin pcout p3 n3 p1 n1 p2 n2.
    !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 9)) t = m
    ==>
    !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 9)) t = n
    ==> nonoverlapping (word pc,0x3f52) (word_add (read p3 t) (word n3),72)
    ==> ensures x86
         (\s. bytes_loaded s (word pc) p521_jscalarmul_alt_tmc /\
              read RIP s = pcin /\
              read RSP s = read RSP t /\
              read RDI s = read RDI t /\
              read RSI s = read RSI t /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 9)) s =
              m /\
              read(memory :> bytes(word_add (read p2 t) (word n2),8 * 9)) s =
              n)
         (\s. read RIP s = pcout /\
              (m < 2 * p_521 /\ n <= p_521
               ==> &(read(memory :> bytes(word_add (read p3 t) (word n3),
                     8 * 9)) s) = (&3 * &m - &8 * &n) rem &p_521))
            (MAYCHANGE [RIP; RAX; RBX; RBP; RCX; RDX; R8; R9;
                        R10; R11; R12; R13; R14; R15] ,,
             MAYCHANGE
               [memory :> bytes(word_add (read p3 t) (word n3),8 * 9)] ,,
              MAYCHANGE SOME_FLAGS)`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the bound assumption for simplicity ***)

  ASM_CASES_TAC `m < 2 * p_521 /\ n <= p_521` THENL
   [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC);
    X86_SIM_TAC P521_JSCALARMUL_ALT_EXEC (1--112)] THEN

  (*** Digitize and introduce the shifted and flipped version of n ***)

  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "m_" o lhand o concl) THEN
  ABBREV_TAC
   `n' = bignum_of_wordlist
     [word_shl (word_not n_0) 3;
      word_subword ((word_join:int64->int64->int128)
                    (word_not n_1) (word_not n_0)) (61,64);
      word_subword ((word_join:int64->int64->int128)
                    (word_not n_2) (word_not n_1)) (61,64);
      word_subword ((word_join:int64->int64->int128)
                    (word_not n_3) (word_not n_2)) (61,64);
      word_subword ((word_join:int64->int64->int128)
                    (word_not n_4) (word_not n_3)) (61,64);
      word_subword ((word_join:int64->int64->int128)
                    (word_not n_5) (word_not n_4)) (61,64);
      word_subword ((word_join:int64->int64->int128)
                    (word_not n_6) (word_not n_5)) (61,64);
      word_subword ((word_join:int64->int64->int128)
                    (word_not n_7) (word_not n_6)) (61,64);
      word_subword ((word_join:int64->int64->int128)
                    (word_xor n_8 (word 0x1FF)) (word_not n_7)) (61,64)]` THEN
  SUBGOAL_THEN `8 * (p_521 - n) = n'` ASSUME_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `8 * n + m = 8 * p ==> 8 * (p - n) = m`) THEN
    SUBGOAL_THEN `n DIV 2 EXP 512 < 2 EXP 9` MP_TAC THENL
     [UNDISCH_TAC `n <= p_521` THEN REWRITE_TAC[p_521] THEN ARITH_TAC;
      EXPAND_TAC "n" THEN
      CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
      REWRITE_TAC[GSYM UPPER_BITS_ZERO]] THEN
    EXPAND_TAC "n'" THEN POP_ASSUM_LIST(K ALL_TAC) THEN
    DISCH_THEN(MP_TAC o MATCH_MP (MESON[]
     `(!i. P i) ==> (!i. i < 64 ==> P i)`)) THEN
    CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
    REWRITE_TAC[bignum_of_wordlist; REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[val_def; DIMINDEX_64; bignum_of_wordlist] THEN
    REWRITE_TAC[ARITH_RULE `i < 64 <=> 0 <= i /\ i <= 63`] THEN
    REWRITE_TAC[GSYM IN_NUMSEG; IN_GSPEC] THEN
    REWRITE_TAC[BIT_WORD_SUBWORD; BIT_WORD_JOIN; BIT_WORD_SHL;
                BIT_WORD_NOT; BIT_WORD_XOR; DIMINDEX_64; DIMINDEX_128] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC(ONCE_DEPTH_CONV EXPAND_NSUM_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
    CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[BITVAL_CLAUSES] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_BITVAL_NOT] THEN
    REWRITE_TAC[p_521] THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN

  SUBGOAL_THEN
   `(&3 * &m - &8 * &n) rem &p_521 =
    (&3 * &m + &8 * (&p_521 - &n)) rem &p_521`
  SUBST1_TAC THENL
   [REWRITE_TAC[INT_REM_EQ] THEN CONV_TAC INTEGER_RULE;
    ASM_SIMP_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_SUB; INT_OF_NUM_REM]] THEN

  (*** The basic multiply-add block = ca, then forget the components ***)

  ABBREV_TAC `ca = 3 * m + n'` THEN
  SUBGOAL_THEN `ca < 2 EXP 527` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["ca"; "n'"] THEN UNDISCH_TAC `m < 2 * p_521` THEN
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    ALL_TAC] THEN

  X86_GEN_ACCSTEPS_TAC
    (fun _ -> RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
                `word_sub x (word_neg y):int64 = word_add x y`]) THEN
              RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
               `word_mul x (word n) = word(0 + val x * n)`]))
    P521_JSCALARMUL_ALT_EXEC
    [30;31;32; 35;36;37;38; 41;42;43;44; 47;48;49;50; 53;54;55;56;
     59;60;61;62; 65;66;67;68; 71;72;73;74; 76;77] (1--77) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist
     [sum_s31; sum_s37; sum_s43; sum_s49;
      sum_s55; sum_s61; sum_s67; sum_s73; sum_s77] = ca`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`576`; `&0:real`] THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
     [UNDISCH_TAC `ca < 2 EXP 527` THEN REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
      ARITH_TAC;
      REWRITE_TAC[INTEGER_CLOSED] THEN EXPAND_TAC "ca"] THEN
    UNDISCH_THEN `8 * (p_521 - n) = n'` (K ALL_TAC) THEN
    MAP_EVERY EXPAND_TAC ["m"; "n'"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
    REWRITE_TAC[REAL_VAL_WORD_NOT; DIMINDEX_64] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o
      filter (is_ratconst o rand o concl) o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `m:num` o concl))) THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `n:num` o concl))) THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `n':num` o concl)))] THEN

  (*** Breaking the problem down to (h + l) MOD p_521 ***)

  SUBGOAL_THEN `ca MOD p_521 = (ca DIV 2 EXP 521 + ca MOD 2 EXP 521) MOD p_521`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)
     [ARITH_RULE `ca = 2 EXP 521 * ca DIV 2 EXP 521 + ca MOD 2 EXP 521`] THEN
    REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC(NUMBER_RULE
     `(e == 1) (mod p) ==> (e * h + l == h + l) (mod p)`) THEN
    REWRITE_TAC[p_521; CONG] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `ca DIV 2 EXP 521 < 2 EXP 64 /\ ca MOD 2 EXP 521 < 2 EXP 521`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MOD_LT_EQ] THEN UNDISCH_TAC `ca < 2 EXP 527` THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** Splitting up and stuffing 1 bits into the low part ***)

  X86_STEPS_TAC P521_JSCALARMUL_ALT_EXEC (78--87) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_AND_ASSOC; DIMINDEX_64]) THEN
  MAP_EVERY ABBREV_TAC
   [`h:int64 = word_ushr sum_s77 9`;
    `d:int64 = word_or sum_s77 (word 18446744073709551104)`;
    `dd:int64 = word_and sum_s37 (word_and sum_s43 (word_and sum_s49
      (word_and sum_s55 (word_and sum_s61 (word_and sum_s67 sum_s73)))))`] THEN

  (*** The comparison in its direct condensed form ***)

  X86_ACCSTEPS_TAC P521_JSCALARMUL_ALT_EXEC [89;91;93] (88--93) THEN

  SUBGOAL_THEN
   `&(val (word_add h (word 1):int64)):real = &(val h) + &1`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_CLAUSES; VAL_WORD_ADD_CASES] THEN
    REWRITE_TAC[DIMINDEX_64; VAL_WORD_1] THEN
    MATCH_MP_TAC(MESON[] `p ==> (if p then x else y) = x`) THEN
    SUBST1_TAC(SYM(ASSUME `word_ushr sum_s77 9 = (h:int64)`)) THEN
    CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `carry_s93 <=>
    2 EXP 192 <=
      2 EXP 128 * val(d:int64) + 2 EXP 64 * val(dd:int64) +
      val(h:int64) + val(sum_s31:int64) + 1`
  (ASSUME_TAC o SYM) THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `192` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Finish the simulation before completing the mathematics ***)

  X86_ACCSTEPS_TAC P521_JSCALARMUL_ALT_EXEC
   [94;96;98;100;102;104;106;108;110] (94--112) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  DISCARD_STATE_TAC "s112" THEN

  (*** Evaluate d and un-condense the inequality ***)

  SUBGOAL_THEN
   `val(d:int64) = 2 EXP 9 * (2 EXP 55 - 1) + val(sum_s77:int64) MOD 2 EXP 9`
  SUBST_ALL_TAC THENL
   [EXPAND_TAC "d" THEN ONCE_REWRITE_TAC[WORD_BITWISE_RULE
     `word_or a b = word_or b (word_and a (word_not b))`] THEN
    SIMP_TAC[VAL_WORD_OR_DISJOINT; WORD_BITWISE_RULE
     `word_and x (word_and y (word_not x)) = word 0`] THEN
    REWRITE_TAC[GSYM VAL_WORD_AND_MASK_WORD] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV;
    ALL_TAC] THEN

  SUBGOAL_THEN
   `2 EXP 512 * val(sum_s77:int64) MOD 2 EXP 9 +
    bignum_of_wordlist
     [sum_s31; sum_s37; sum_s43; sum_s49; sum_s55; sum_s61; sum_s67; sum_s73] =
    ca MOD 2 EXP 521`
  (LABEL_TAC "*") THENL
   [CONV_TAC SYM_CONV THEN EXPAND_TAC "ca" THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(8,1)] THEN
    REWRITE_TAC[ARITH_RULE `2 EXP 521 = 2 EXP 512 * 2 EXP 9`] THEN
    REWRITE_TAC[SYM(NUM_REDUCE_CONV `64 * 8`)] THEN
    SIMP_TAC[LENGTH; ARITH_LT; ARITH_LE; MOD_MULT_MOD; ADD_CLAUSES;
             ARITH_SUC; BIGNUM_OF_WORDLIST_BOUND; MOD_LT; DIV_LT;
             MOD_MULT_ADD; DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_SING] THEN ARITH_TAC;
    ALL_TAC] THEN

  SUBGOAL_THEN
   `2 EXP 521 <= ca MOD 2 EXP 521 + val(h:int64) + 1 <=> carry_s93`
  MP_TAC THENL
   [REMOVE_THEN "*" (SUBST1_TAC o SYM) THEN EXPAND_TAC "carry_s93" THEN
    ONCE_REWRITE_TAC[bignum_of_wordlist] THEN
    MATCH_MP_TAC(TAUT
     `!p q. ((p ==> ~r) /\ (q ==> ~s)) /\ (p <=> q) /\ (~p /\ ~q ==> (r <=> s))
            ==> (r <=> s)`) THEN
    MAP_EVERY EXISTS_TAC
     [`bignum_of_wordlist
        [sum_s37; sum_s43; sum_s49; sum_s55; sum_s61; sum_s67; sum_s73] <
       2 EXP (64 * 7) - 1`;
      `val(dd:int64) < 2 EXP 64 - 1`] THEN
    CONJ_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC(ARITH_RULE
      `2 EXP 64 * b + d < 2 EXP 64 * (a + 1) + c ==> a < b ==> ~(c <= d)`) THEN
      MP_TAC(SPEC `h:int64` VAL_BOUND_64) THEN
      MP_TAC(SPEC `sum_s31:int64` VAL_BOUND_64) THEN ARITH_TAC;
      SIMP_TAC[BIGNUM_OF_WORDLIST_LT_MAX; LENGTH; ARITH_EQ; ARITH_SUC]] THEN
    REWRITE_TAC[GSYM NOT_ALL] THEN MP_TAC(ISPEC `dd:int64` VAL_EQ_MAX) THEN
    SIMP_TAC[VAL_BOUND_64; DIMINDEX_64; ARITH_RULE
      `a < n ==> (a < n - 1 <=> ~(a = n - 1))`] THEN
    DISCH_THEN SUBST1_TAC THEN EXPAND_TAC "dd" THEN
    REWRITE_TAC[WORD_NOT_AND; ALL; WORD_OR_EQ_0] THEN
    REWRITE_TAC[WORD_RULE `word_not d = e <=> d = word_not e`] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC) THEN
    REWRITE_TAC[bignum_of_wordlist] THEN CONV_TAC WORD_REDUCE_CONV THEN
    MP_TAC(ARITH_RULE `val(sum_s77:int64) MOD 2 EXP 9 = 511 \/
                       val(sum_s77:int64) MOD 2 EXP 9 < 511`) THEN
    MP_TAC(SPEC `h:int64` VAL_BOUND_64) THEN
    MP_TAC(SPEC `sum_s31:int64` VAL_BOUND_64) THEN ARITH_TAC;
    FIRST_X_ASSUM(K ALL_TAC o check (is_iff o concl))] THEN

  (*** Also evaluate h ***)

  SUBGOAL_THEN `val(h:int64) = ca DIV 2 EXP 521` SUBST_ALL_TAC THENL
   [EXPAND_TAC "h" THEN REWRITE_TAC[VAL_WORD_USHR] THEN
    EXPAND_TAC "ca" THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN

  (*** Now complete the mathematics ***)

  SUBGOAL_THEN
   `2 EXP 521 <= ca MOD 2 EXP 521 + ca DIV 2 EXP 521 + 1 <=>
    p_521 <= ca DIV 2 EXP 521 + ca MOD 2 EXP 521`
  SUBST1_TAC THENL [REWRITE_TAC[p_521] THEN ARITH_TAC; DISCH_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  MAP_EVERY EXISTS_TAC
   [`521`;
    `if ca DIV 2 EXP 521 + ca MOD 2 EXP 521 < p_521
     then &(ca DIV 2 EXP 521 + ca MOD 2 EXP 521)
     else &(ca DIV 2 EXP 521 + ca MOD 2 EXP 521) - &p_521`] THEN
  REPEAT CONJ_TAC THENL
   [BOUNDER_TAC[];
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    ALL_TAC;
    W(MP_TAC o PART_MATCH (lhand o rand) MOD_CASES o rand o lhand o snd) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `ca < 2 EXP 527` THEN REWRITE_TAC[p_521] THEN ARITH_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN
    SIMP_TAC[GSYM NOT_LE; COND_SWAP; GSYM REAL_OF_NUM_SUB; COND_ID]] THEN
  ASM_REWRITE_TAC[GSYM NOT_LE; COND_SWAP] THEN
  REMOVE_THEN "*" (SUBST1_TAC o SYM) THEN
  REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 9 - 1`)] THEN
  REWRITE_TAC[VAL_WORD_AND_MASK_WORD; bignum_of_wordlist] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_MOD; p_521] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let unilemma0 = prove
 (`x = a MOD p_521 ==> x < p_521 /\ &x = &a rem &p_521`,
  REWRITE_TAC[INT_OF_NUM_REM; p_521] THEN ARITH_TAC);;

let unilemma1 = prove
 (`&x = a rem &p_521 ==> x < p_521 /\ &x = a rem &p_521`,
  SIMP_TAC[GSYM INT_OF_NUM_LT; INT_LT_REM_EQ; p_521] THEN INT_ARITH_TAC);;

let weierstrass_of_jacobian_p521_double = prove
 (`!P1 P2 x1 y1 z1 x3 y3 z3.
        jacobian_double_unexceptional nistp521
         (x1 rem &p_521,y1 rem &p_521,z1 rem &p_521) =
        (x3 rem &p_521,y3 rem &p_521,z3 rem &p_521)
       ==> weierstrass_of_jacobian (integer_mod_ring p_521)
                (x1 rem &p_521,y1 rem &p_521,z1 rem &p_521) = P1
            ==> weierstrass_of_jacobian (integer_mod_ring p_521)
                  (x3 rem &p_521,y3 rem &p_521,z3 rem &p_521) =
                group_mul p521_group P1 P1`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[nistp521; P521_GROUP] THEN
  MATCH_MP_TAC WEIERSTRASS_OF_JACOBIAN_DOUBLE_UNEXCEPTIONAL THEN
  ASM_REWRITE_TAC[FIELD_INTEGER_MOD_RING; PRIME_P521] THEN
  ASM_REWRITE_TAC[jacobian_point; INTEGER_MOD_RING_CHAR;
                  INTEGER_MOD_RING_CLAUSES; IN_INTEGER_MOD_RING_CARRIER] THEN
  REWRITE_TAC[INT_REM_POS_EQ; INT_LT_REM_EQ; GSYM INT_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[p_521; b_521] THEN CONV_TAC INT_REDUCE_CONV);;

let weierstrass_of_jacobian_p521_add = prove
 (`!P1 P2 x1 y1 z1 x2 y2 z2 x3 y3 z3.
        ~(weierstrass_of_jacobian (integer_mod_ring p_521)
           (x1 rem &p_521,y1 rem &p_521,z1 rem &p_521) =
          weierstrass_of_jacobian (integer_mod_ring p_521)
           (x2 rem &p_521,y2 rem &p_521,z2 rem &p_521)) /\
        jacobian_add_unexceptional nistp521
         (x1 rem &p_521,y1 rem &p_521,z1 rem &p_521)
         (x2 rem &p_521,y2 rem &p_521,z2 rem &p_521) =
        (x3 rem &p_521,y3 rem &p_521,z3 rem &p_521)
        ==> weierstrass_of_jacobian (integer_mod_ring p_521)
                (x1 rem &p_521,y1 rem &p_521,z1 rem &p_521) = P1 /\
            weierstrass_of_jacobian (integer_mod_ring p_521)
                (x2 rem &p_521,y2 rem &p_521,z2 rem &p_521) = P2
            ==> weierstrass_of_jacobian (integer_mod_ring p_521)
                  (x3 rem &p_521,y3 rem &p_521,z3 rem &p_521) =
                group_mul p521_group P1 P2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
  DISCH_THEN(CONJUNCTS_THEN(SUBST1_TAC o SYM)) THEN
  REWRITE_TAC[nistp521; P521_GROUP] THEN
  MATCH_MP_TAC WEIERSTRASS_OF_JACOBIAN_ADD_UNEXCEPTIONAL THEN
  REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
   [ALL_TAC;
    W(MP_TAC o PART_MATCH (rand o rand) WEIERSTRASS_OF_JACOBIAN_EQ o
      rand o snd) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC] THEN
  ASM_REWRITE_TAC[FIELD_INTEGER_MOD_RING; PRIME_P521] THEN
  ASM_REWRITE_TAC[jacobian_point; INTEGER_MOD_RING_CHAR;
                  INTEGER_MOD_RING_CLAUSES; IN_INTEGER_MOD_RING_CARRIER] THEN
  REWRITE_TAC[INT_REM_POS_EQ; INT_LT_REM_EQ; GSYM INT_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[p_521; b_521] THEN CONV_TAC INT_REDUCE_CONV);;

let represents_p521 = new_definition
 `represents_p521 P (x,y,z) <=>
        x < p_521 /\ y < p_521 /\ z < p_521 /\
        weierstrass_of_jacobian (integer_mod_ring p_521)
         (tripled (modular_decode (576,p_521)) (x,y,z)) = P`;;

let LOCAL_JDOUBLE_CORRECT = time prove
 (`!p3 p1 t1 pc stackpointer.
        ALL (nonoverlapping (stackpointer,600))
            [(word pc,0x3f52); (p1,216); (p3,216)] /\
        nonoverlapping (p3,216) (word pc,0x3f52)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) p521_jscalarmul_alt_tmc /\
                  read RIP s = word(pc + 0x28ed) /\
                  read RSP s = word_add stackpointer (word 80) /\
                  C_ARGUMENTS [p3; p1] s /\
                  bignum_triple_from_memory (p1,9) s = t1)
             (\s. read RIP s = word (pc + 0x33b8) /\
                  !P. represents_p521 P t1
                      ==> represents_p521 (group_mul p521_group P P)
                            (bignum_triple_from_memory(p3,9) s))
          (MAYCHANGE [RIP; RDI; RSI; RAX; RBX; RBP; RCX; RDX; R8; R9;
                      R10; R11; R12; R13; R14; R15] ,,
           MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [memory :> bytes(p3,216);
                      memory :> bytes(stackpointer,600)])`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`p3:int64`; `p1:int64`; `x:num`; `y:num`; `z:num`;
    `pc:num`; `stackpointer:int64`] THEN
  REWRITE_TAC[ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS; PAIR_EQ; bignum_triple_from_memory] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
  ENSURES_EXISTING_PRESERVED_TAC `RSP` THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN

  LOCAL_SQR_P521_TAC 3 ["z2";"z_1"] THEN
  LOCAL_SQR_P521_TAC 1 ["y2";"y_1"] THEN
  LOCAL_ADD_P521_TAC 1 ["t1";"x_1";"z2"] THEN
  LOCAL_SUB_P521_TAC 1 ["t2";"x_1";"z2"] THEN
  LOCAL_MUL_P521_TAC 0 ["x2p";"t1";"t2"] THEN
  LOCAL_ADD_P521_TAC 1 ["t1";"y_1";"z_1"] THEN
  LOCAL_SQR_P521_TAC 0 ["x4p";"x2p"] THEN
  LOCAL_MUL_P521_TAC 1 ["xy2";"x_1";"y2"] THEN
  LOCAL_SQR_P521_TAC 0 ["t2";"t1"] THEN
  LOCAL_CMSUBC9_P521_TAC 0 ["d";"xy2";"x4p"] THEN
  LOCAL_SUB_P521_TAC 0 ["t1";"t2";"z2"] THEN
  LOCAL_SQR_P521_TAC 0 ["y4";"y2"] THEN
  LOCAL_SUB_P521_TAC 1 ["z_3";"t1";"y2"] THEN
  LOCAL_MUL_P521_TAC 0 ["dx2";"d";"x2p"] THEN
  LOCAL_CMSUB41_P521_TAC 1 ["x_3";"xy2";"d"] THEN
  LOCAL_CMSUB38_P521_TAC 1 ["y_3";"dx2";"y4"] THEN

  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCARD_STATE_TAC "s54" THEN
  DISCARD_MATCHING_ASSUMPTIONS [`nonoverlapping_modulo a b c`] THEN

  X_GEN_TAC `P:(int#int)option` THEN
  REWRITE_TAC[represents_p521; tripled] THEN
  REWRITE_TAC[modular_decode; INT_OF_NUM_CLAUSES; INT_OF_NUM_REM] THEN
  STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_imp o concl))) THEN
  REPEAT(ANTS_TAC THENL
   [REWRITE_TAC[p_521] THEN RULE_ASSUM_TAC(REWRITE_RULE[p_521]) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM BOUNDER_TAC[];
    (DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP unilemma0) ORELSE
     DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP unilemma1) ORELSE
     STRIP_TAC)]) THEN
  REPEAT(CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC]) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o GEN_REWRITE_RULE I [GSYM NOT_LE])) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [num_congruent; GSYM INT_OF_NUM_CLAUSES; GSYM INT_OF_NUM_REM]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM INT_REM_EQ]) THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE[GSYM INT_SUB_REM; GSYM INT_ADD_REM]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INT_POW_2]) THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE[GSYM INT_MUL_REM]) THEN
  REWRITE_TAC[GSYM INT_OF_NUM_REM; INT_REM_REM; GSYM INT_OF_NUM_CLAUSES] THEN
  FIRST_X_ASSUM(MP_TAC o
    check(can (term_match [] `weierstrass_of_jacobian f j = p`) o concl)) THEN
  MATCH_MP_TAC weierstrass_of_jacobian_p521_double THEN ASM_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[jacobian_double_unexceptional; nistp521;
                  INTEGER_MOD_RING_CLAUSES] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[PAIR_EQ] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN
  REPEAT CONJ_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN INT_ARITH_TAC);;

let LOCAL_JDOUBLE_SUBR_CORRECT = time prove
 (`!p3 p1 t1 pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 648),648))
            [(word pc,0x3f52); (p1,216)] /\
        ALL (nonoverlapping (p3,216))
            [(word pc,0x3f52); (word_sub stackpointer (word 648),656)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) p521_jscalarmul_alt_tmc /\
                  read RIP s = word(pc + 0x28dc) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [p3; p1] s /\
                  bignum_triple_from_memory (p1,9) s = t1)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !P. represents_p521 P t1
                      ==> represents_p521 (group_mul p521_group P P)
                            (bignum_triple_from_memory(p3,9) s))
          (MAYCHANGE [RSP] ,,
           MAYCHANGE [RIP] ,,
           MAYCHANGE [RAX; RCX; RDX; RSI; RDI; R8; R9; R10; R11] ,,
           MAYCHANGE [CF; PF; AF; ZF; SF; OF] ,,
           MAYCHANGE [memory :> bytes(p3,216);
                      memory :> bytes(word_sub stackpointer (word 648),648)])`,
  X86_ADD_RETURN_STACK_TAC P521_JSCALARMUL_ALT_EXEC LOCAL_JDOUBLE_CORRECT
    `[RBX; RBP; R12; R13; R14; R15]` 648);;

let lvs =
 ["x_1",[`RSI`;`0`];
  "y_1",[`RSI`;`72`];
  "z_1",[`RSI`;`144`];
  "x_2",[`RDI`;`0`];
  "y_2",[`RDI`;`72`];
  "z_2",[`RDI`;`144`];
  "x_3",[`RDI`;`0`];
  "y_3",[`RDI`;`72`];
  "z_3",[`RDI`;`144`];
  "z1sq",[`RSP`;`0`];
  "ww",[`RSP`;`0`];
  "resx",[`RSP`;`0`];
  "yd",[`RSP`;`72`];
  "y2a",[`RSP`;`72`];
  "x2a",[`RSP`;`144`];
  "zzx2",[`RSP`;`144`];
  "zz",[`RSP`;`216`];
  "t1",[`RSP`;`216`];
  "t2",[`RSP`;`288`];
  "x1a",[`RSP`;`288`];
  "zzx1",[`RSP`;`288`];
  "resy",[`RSP`;`288`];
  "xd",[`RSP`;`360`];
  "z2sq",[`RSP`;`360`];
  "resz",[`RSP`;`360`];
  "y1a",[`RSP`;`432`]];;

let LOCAL_SUB_P521_TAC = GENERAL_SUB_P521_TAC lvs;;

let LOCAL_JADD_CORRECT = time prove
 (`!p3 p1 t1 p2 t2 pc stackpointer.
        ALL (nonoverlapping (stackpointer,608))
            [(word pc,0x3f52); (p1,216); (p2,216); (p3,216)] /\
        nonoverlapping (p3,216) (word pc,0x3f52)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) p521_jscalarmul_alt_tmc /\
                  read RIP s = word(pc + 0x1bff) /\
                  read RSP s = word_add stackpointer (word 80) /\
                  C_ARGUMENTS [p3; p1; p2] s /\
                  bignum_triple_from_memory (p1,9) s = t1 /\
                  bignum_triple_from_memory (p2,9) s = t2)
             (\s. read RIP s = word (pc + 0x28ca) /\
                  !P1 P2. represents_p521 P1 t1 /\
                          represents_p521 P2 t2 /\
                          (P1 = P2 ==> P2 = NONE)
                          ==> represents_p521(group_mul p521_group P1 P2)
                               (bignum_triple_from_memory(p3,9) s))
          (MAYCHANGE [RIP; RDI; RSI; RAX; RBP; RBX; RCX; RDX; RBP; R8; R9;
                      R10; R11; R12; R13; R14; R15] ,,
           MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [memory :> bytes(p3,216);
                      memory :> bytes(stackpointer,608)])`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`p3:int64`; `p1:int64`; `x1:num`; `y1:num`; `z1:num`; `p2:int64`;
    `x2:num`; `y2:num`; `z2:num`; `pc:num`; `stackpointer:int64`] THEN
  REWRITE_TAC[ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS; PAIR_EQ; bignum_triple_from_memory] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
  ENSURES_EXISTING_PRESERVED_TAC `RSP` THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN

  LOCAL_SQR_P521_TAC 4 ["z1sq";"z_1"] THEN
  LOCAL_SQR_P521_TAC 1 ["z2sq";"z_2"] THEN
  LOCAL_MUL_P521_TAC 2 ["y1a";"z_2";"y_1"] THEN
  LOCAL_MUL_P521_TAC 2 ["y2a";"z_1";"y_2"] THEN
  LOCAL_MUL_P521_TAC 1 ["x2a";"z1sq";"x_2"] THEN
  LOCAL_MUL_P521_TAC 1 ["x1a";"z2sq";"x_1"] THEN
  LOCAL_MUL_P521_TAC 0 ["y2a";"z1sq";"y2a"] THEN
  LOCAL_MUL_P521_TAC 0 ["y1a";"z2sq";"y1a"] THEN
  LOCAL_SUB_P521_TAC 0 ["xd";"x2a";"x1a"] THEN
  LOCAL_SUB_P521_TAC 0 ["yd";"y2a";"y1a"] THEN
  LOCAL_SQR_P521_TAC 0 ["zz";"xd"] THEN
  LOCAL_SQR_P521_TAC 0 ["ww";"yd"] THEN
  LOCAL_MUL_P521_TAC 0 ["zzx1";"zz";"x1a"] THEN
  LOCAL_MUL_P521_TAC 0 ["zzx2";"zz";"x2a"] THEN
  LOCAL_SUB_P521_TAC 0 ["resx";"ww";"zzx1"] THEN
  LOCAL_SUB_P521_TAC 0 ["t1";"zzx2";"zzx1"] THEN
  LOCAL_MUL_P521_TAC 1 ["xd";"xd";"z_1"] THEN
  LOCAL_SUB_P521_TAC 0 ["resx";"resx";"zzx2"] THEN
  LOCAL_SUB_P521_TAC 0 ["t2";"zzx1";"resx"] THEN
  LOCAL_MUL_P521_TAC 0 ["t1";"t1";"y1a"] THEN
  LOCAL_MUL_P521_TAC 1 ["resz";"xd";"z_2"] THEN
  LOCAL_MUL_P521_TAC 0 ["t2";"yd";"t2"] THEN
  LOCAL_SUB_P521_TAC 0 ["resy";"t2";"t1"] THEN

  BIGNUM_LDIGITIZE_TAC "x1_"
   `read (memory :> bytes (p1,8 * 9)) s96` THEN
  BIGNUM_LDIGITIZE_TAC "y1_"
   `read (memory :> bytes (word_add p1 (word 72),8 * 9)) s96` THEN
  BIGNUM_LDIGITIZE_TAC "z1_"
   `read (memory :> bytes (word_add p1 (word 144),8 * 9)) s96` THEN
  BIGNUM_LDIGITIZE_TAC "x2_"
   `read (memory :> bytes (p2,8 * 9)) s96` THEN
  BIGNUM_LDIGITIZE_TAC "y2_"
   `read (memory :> bytes (word_add p2 (word 72),8 * 9)) s96` THEN
  BIGNUM_LDIGITIZE_TAC "z2_"
   `read (memory :> bytes (word_add p2 (word 144),8 * 9)) s96` THEN
  BIGNUM_LDIGITIZE_TAC "resx_"
   `read (memory :> bytes (word_add stackpointer (word 80),8 * 9)) s96` THEN
  BIGNUM_LDIGITIZE_TAC "resy_"
   `read (memory :> bytes (word_add stackpointer (word 368),8 * 9)) s96` THEN
  BIGNUM_LDIGITIZE_TAC "resz_"
   `read (memory :> bytes (word_add stackpointer (word 440),8 * 9)) s96` THEN
  X86_STEPS_TAC P521_JSCALARMUL_ALT_EXEC (97--282) THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCARD_STATE_TAC "s282" THEN
  DISCARD_MATCHING_ASSUMPTIONS [`nonoverlapping_modulo a b c`] THEN
  REWRITE_TAC[WORD_BITWISE_RULE
   `word_or (word_or (word_or (word_or x0 x1) (word_or x2 x3)) x8)
            (word_or (word_or x4 x5) (word_or x6 x7)) =
    word_or x0 (word_or x1 (word_or x2 (word_or x3
       (word_or x4 (word_or x5 (word_or x6 (word_or x7 x8)))))))`] THEN

  MAP_EVERY X_GEN_TAC [`P1:(int#int)option`; `P2:(int#int)option`] THEN
  REWRITE_TAC[represents_p521; tripled; paired] THEN
  REWRITE_TAC[modular_decode; INT_OF_NUM_CLAUSES; INT_OF_NUM_REM] THEN
  STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_imp o concl))) THEN
  REPEAT(ANTS_TAC THENL
   [REWRITE_TAC[p_521] THEN RULE_ASSUM_TAC(REWRITE_RULE[p_521]) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM BOUNDER_TAC[];
    (DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP unilemma0) ORELSE
     DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP unilemma1) ORELSE
     STRIP_TAC)]) THEN

  REWRITE_TAC[WORD_SUB_0; VAL_EQ_0; INT_OF_NUM_EQ; WORD_OR_EQ_0] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN
  MP_TAC(GEN_ALL(SPEC `[x0:int64;x1;x2;x3;x4;x5;x6;x7;x8]`
    BIGNUM_OF_WORDLIST_EQ_0)) THEN
  ASM_REWRITE_TAC[ALL; GSYM INT_OF_NUM_EQ] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY ASM_CASES_TAC [`&z1:int = &0`; `&z2:int = &0`] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  REWRITE_TAC[GSYM(NUM_REDUCE_CONV `2 EXP 256`)] THENL
   [ASM_REWRITE_TAC[] THEN MAP_EVERY EXPAND_TAC ["P1"; "P2"] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_CLAUSES] THEN
    ASM_REWRITE_TAC[INT_MUL_LZERO; INT_MUL_RZERO; INT_REM_ZERO;
                    GSYM INT_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[weierstrass_of_jacobian; INTEGER_MOD_RING_CLAUSES] THEN
    REWRITE_TAC[P521_GROUP; weierstrass_add] THEN
    REWRITE_TAC[p_521] THEN CONV_TAC INT_REDUCE_CONV;
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "P1" THEN
    REWRITE_TAC[GSYM INT_OF_NUM_REM] THEN
    ASM_REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[INT_MUL_RZERO; INT_REM_ZERO] THEN
    REWRITE_TAC[weierstrass_of_jacobian; INTEGER_MOD_RING_CLAUSES] THEN
    REWRITE_TAC[P521_GROUP; weierstrass_add];
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "P2" THEN
    REWRITE_TAC[GSYM INT_OF_NUM_REM] THEN
    ASM_REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[INT_MUL_RZERO; INT_REM_ZERO] THEN
    REWRITE_TAC[weierstrass_of_jacobian; INTEGER_MOD_RING_CLAUSES] THEN
    REWRITE_TAC[P521_GROUP; weierstrass_add];
    ALL_TAC] THEN

  SUBGOAL_THEN `~(&z1 rem &p_521 = &0) /\ ~(&z2 rem &p_521 = &0)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[INT_OF_NUM_REM; MOD_LT]; ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM CONTRAPOS_THM] THEN ANTS_TAC THENL
   [EXPAND_TAC "P2" THEN REWRITE_TAC[weierstrass_of_jacobian] THEN
    ASM_REWRITE_TAC[INTEGER_MOD_RING_CLAUSES; OPTION_DISTINCT;
                    GSYM INT_OF_NUM_REM];
    DISCH_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(CONJ_TAC THENL [REWRITE_TAC[p_521] THEN ARITH_TAC; ALL_TAC]) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o GEN_REWRITE_RULE I [GSYM NOT_LE])) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [num_congruent; GSYM INT_OF_NUM_CLAUSES; GSYM INT_OF_NUM_REM]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM INT_REM_EQ]) THEN
  RULE_ASSUM_TAC(CONV_RULE INT_REM_DOWN_CONV) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INT_POW_2]) THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE[GSYM INT_ADD_REM; GSYM INT_SUB_REM]) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o
    check(can (term_match [] `weierstrass_of_jacobian f j = p`) o concl))) THEN
  REWRITE_TAC[IMP_IMP] THEN
  ASM_REWRITE_TAC[GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_CLAUSES] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN MP_TAC th) THEN
  MATCH_MP_TAC weierstrass_of_jacobian_p521_add THEN ASM_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[jacobian_add_unexceptional; nistp521;
                  INTEGER_MOD_RING_CLAUSES] THEN
  REWRITE_TAC[p_521] THEN CONV_TAC INT_REDUCE_CONV THEN
  REWRITE_TAC[GSYM p_521] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[PAIR_EQ] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN
  REPEAT CONJ_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN INT_ARITH_TAC);;

let LOCAL_JADD_SUBR_CORRECT = time prove
 (`!p3 p1 t1 p2 t2 pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 656),656))
            [(word pc,0x3f52); (p1,216); (p2,216)] /\
        ALL (nonoverlapping (p3,216))
            [(word pc,0x3f52); (word_sub stackpointer (word 656),664)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) p521_jscalarmul_alt_tmc /\
                  read RIP s = word(pc + 0x1bee) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [p3; p1; p2] s /\
                  bignum_triple_from_memory (p1,9) s = t1 /\
                  bignum_triple_from_memory (p2,9) s = t2)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !P1 P2. represents_p521 P1 t1 /\
                          represents_p521 P2 t2 /\
                          (P1 = P2 ==> P2 = NONE)
                          ==> represents_p521(group_mul p521_group P1 P2)
                               (bignum_triple_from_memory(p3,9) s))
          (MAYCHANGE [RSP] ,,
           MAYCHANGE [RIP] ,,
           MAYCHANGE [RAX; RCX; RDX; RSI; RDI; R8; R9; R10; R11] ,,
           MAYCHANGE [CF; PF; AF; ZF; SF; OF] ,,
           MAYCHANGE [memory :> bytes(p3,216);
                      memory :> bytes(word_sub stackpointer (word 656),656)])`,
  X86_ADD_RETURN_STACK_TAC P521_JSCALARMUL_ALT_EXEC LOCAL_JADD_CORRECT
    `[RBX; RBP; R12; R13; R14; R15]` 656);;

(* ------------------------------------------------------------------------- *)
(* Level 3: the top-level proof.                                             *)
(* ------------------------------------------------------------------------- *)

let LOCAL_MOD_N521_TAC =
  let baseth = X86_SIMD_SHARPEN_RULE BIGNUM_MOD_N521_9_ALT_NOIBT_SUBROUTINE_CORRECT
   (X86_PROMOTE_RETURN_NOSTACK_TAC
    bignum_mod_n521_9_alt_tmc BIGNUM_MOD_N521_9_ALT_CORRECT) in
  X86_SUBROUTINE_SIM_TAC
   (p521_jscalarmul_alt_tmc,P521_JSCALARMUL_ALT_EXEC,
    0x1ac3,bignum_mod_n521_9_alt_tmc,baseth)
  [`read RDI s`; `read RSI s`;
   `read(memory :> bytes(read RSI s,8 * 9)) s`;
   `pc + 0x1ac3`; `read RSP s`; `read (memory :> bytes64(read RSP s)) s`];;

let LOCAL_MOD_P521_TAC =
  let baseth = X86_SIMD_SHARPEN_RULE BIGNUM_MOD_P521_9_NOIBT_SUBROUTINE_CORRECT
   (X86_PROMOTE_RETURN_STACK_TAC bignum_mod_p521_9_tmc BIGNUM_MOD_P521_9_CORRECT
   `[RBX]` 8) in
  X86_SUBROUTINE_SIM_TAC
   (p521_jscalarmul_alt_tmc,P521_JSCALARMUL_ALT_EXEC,
    0x1a1b,bignum_mod_p521_9_tmc,baseth)
  [`read RDI s`; `read RSI s`;
   `read(memory :> bytes(read RSI s,8 * 9)) s`;
   `pc + 0x1a1b`; `read RSP s`; `read (memory :> bytes64(read RSP s)) s`];;

let LOCAL_JADD_TAC =
  let th =
    CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
      (REWRITE_RULE[bignum_triple_from_memory; bignum_pair_from_memory]
       LOCAL_JADD_SUBR_CORRECT) in
  X86_SUBROUTINE_SIM_TAC
   (p521_jscalarmul_alt_tmc,P521_JSCALARMUL_ALT_EXEC,
    0x0,p521_jscalarmul_alt_tmc,th)
  [`read RDI s`; `read RSI s`;
   `read(memory :> bytes(read RSI s,8 * 9)) s,
    read(memory :> bytes(word_add (read RSI s) (word 72),8 * 9)) s,
    read(memory :> bytes(word_add (read RSI s) (word 144),8 * 9)) s`;
   `read RDX s`;
   `read(memory :> bytes(read RDX s,8 * 9)) s,
    read(memory :> bytes(word_add (read RDX s) (word 72),8 * 9)) s,
    read(memory :> bytes(word_add (read RDX s) (word 144),8 * 9)) s`;
   `pc:num`; `read RSP s`; `read (memory :> bytes64(read RSP s)) s`];;

let LOCAL_JDOUBLE_TAC =
  let th =
    CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
      (REWRITE_RULE[bignum_triple_from_memory; bignum_pair_from_memory]
       LOCAL_JDOUBLE_SUBR_CORRECT) in
  X86_SUBROUTINE_SIM_TAC
   (p521_jscalarmul_alt_tmc,P521_JSCALARMUL_ALT_EXEC,
    0x0,p521_jscalarmul_alt_tmc,th)
  [`read RDI s`; `read RSI s`;
   `read(memory :> bytes(read RSI s,8 * 9)) s,
    read(memory :> bytes(word_add (read RSI s) (word 72),8 * 9)) s,
    read(memory :> bytes(word_add (read RSI s) (word 144),8 * 9)) s`;
   `pc:num`; `read RSP s`; `read (memory :> bytes64(read RSP s)) s`];;

let REPRESENTS_P521_REDUCTION = prove
 (`!P x y z.
        represents_p521 P (x,y,z)
        ==> represents_p521 P (x MOD p_521,y MOD p_521,z MOD p_521)`,
  REWRITE_TAC[represents_p521; modular_decode; tripled; MOD_LT_EQ] THEN
  SIMP_TAC[INT_OF_NUM_REM; MOD_MOD_REFL] THEN REWRITE_TAC[p_521; ARITH_EQ]);;

let REPRESENTS_P521_NEGATION_ALT = prove
 (`!P x y z.
        represents_p521 P (x,y,z)
        ==> P IN group_carrier p521_group
            ==> represents_p521 (group_inv p521_group P)
                   (x,(if y = 0 then 0 else p_521 - y),z)`,
  REWRITE_TAC[represents_p521] THEN REPEAT GEN_TAC THEN
  STRIP_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`integer_mod_ring p_521`; `ring_neg (integer_mod_ring p_521) (&3)`;
    `&b_521:int`;
    `tripled (modular_decode (576,p_521)) (x,y,z)`]
   WEIERSTRASS_OF_JACOBIAN_NEG) THEN
  ASM_REWRITE_TAC[jacobian_point; GSYM nistp521; P521_GROUP; tripled] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FIELD_INTEGER_MOD_RING; PRIME_P521] THEN
    REWRITE_TAC[b_521; IN_INTEGER_MOD_RING_CARRIER; p_521;
                INTEGER_MOD_RING_CLAUSES] THEN
    CONV_TAC INT_REDUCE_CONV THEN REWRITE_TAC[GSYM p_521] THEN
    CONJ_TAC THENL [ALL_TAC; CONJ_TAC] THEN
    MATCH_MP_TAC MODULAR_DECODE THEN
    REWRITE_TAC[p_521] THEN CONV_TAC NUM_REDUCE_CONV;
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[jacobian_neg; INTEGER_MOD_RING_CLAUSES; nistp521] THEN
    REWRITE_TAC[PAIR_EQ] THEN REWRITE_TAC[modular_decode] THEN
    CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[INT_REM_LNEG] THEN
    ASM_SIMP_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_REM; MOD_LT] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[INT_ABS_NUM; MOD_0] THEN
    ASM_SIMP_TAC[INT_OF_NUM_SUB; LT_IMP_LE; INT_OF_NUM_EQ] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC]);;

let P521_JSCALARMUL_ALT_CORRECT = time prove
 (`!res scalar point n xyz pc stackpointer.
        ALL (nonoverlapping (stackpointer,4696))
            [(word pc,0x3f52); (res,216); (scalar,72); (point,216)] /\
        nonoverlapping (res,216) (word pc,0x3f52)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) p521_jscalarmul_alt_tmc /\
                  read RIP s = word(pc + 0x11) /\
                  read RSP s = word_add stackpointer (word 664) /\
                  C_ARGUMENTS [res;scalar;point] s /\
                  bignum_from_memory (scalar,9) s = n /\
                  bignum_triple_from_memory (point,9) s = xyz)
             (\s. read RIP s = word (pc + 0x1a09) /\
                  !P. P IN group_carrier p521_group /\
                      represents_p521 P xyz
                      ==> represents_p521
                            (group_pow p521_group P n)
                            (bignum_triple_from_memory(res,9) s))
          (MAYCHANGE [RIP] ,,
           MAYCHANGE [RAX; RCX; RDX; RSI; RDI; R8; R9; R10; R11] ,,
           MAYCHANGE [CF; PF; AF; ZF; SF; OF] ,,
           MAYCHANGE [RBX; RBP; R12; R13; R14; R15] ,,
           MAYCHANGE [memory :> bytes(res,216);
                      memory :> bytes(stackpointer,4696)])`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  REWRITE_TAC[GSYM SEQ_ASSOC; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  MAP_EVERY X_GEN_TAC
   [`res:int64`; `scalar:int64`; `point:int64`;
    `n_input:num`; `x_input:num`; `y_input:num`; `z_input:num`;
    `pc:num`; `stackpointer:int64`] THEN
  REWRITE_TAC[ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS; PAIR_EQ; bignum_triple_from_memory] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
  ENSURES_EXISTING_PRESERVED_TAC `RSP` THEN

  (*** Modified input arguments, mathematically first ***)

  MAP_EVERY ABBREV_TAC
   [`x = x_input MOD p_521`;
    `y = y_input MOD p_521`;
    `z = z_input MOD p_521`] THEN
  SUBGOAL_THEN `x < p_521 /\ y < p_521 /\ z < p_521` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["x"; "y"; "z"] THEN
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    ALL_TAC] THEN

  ABBREV_TAC `n_red = n_input MOD n_521` THEN
  SUBGOAL_THEN `n_red < n_521` ASSUME_TAC THENL
   [EXPAND_TAC "n_red" THEN REWRITE_TAC[n_521] THEN ARITH_TAC; ALL_TAC] THEN

  ABBREV_TAC `sgn <=> 2 EXP 520 <= n_red` THEN
  ABBREV_TAC `n_neg = if sgn then n_521 - n_red else n_red` THEN
  SUBGOAL_THEN `n_neg < 2 EXP 520` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["n_neg"; "sgn"] THEN
    UNDISCH_TAC `n_red < n_521` THEN REWRITE_TAC[n_521] THEN ARITH_TAC;
    ALL_TAC] THEN

  ABBREV_TAC `recoder = nsum(0..103) (\i. 2 EXP (5 * i) * 16)` THEN
  FIRST_X_ASSUM(MP_TAC o CONV_RULE(LAND_CONV EXPAND_NSUM_CONV)) THEN
  CONV_TAC(LAND_CONV(LAND_CONV NUM_REDUCE_CONV)) THEN DISCH_TAC THEN
  ABBREV_TAC `n = n_neg + recoder` THEN
  SUBGOAL_THEN `n < 2 EXP 521` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["n"; "recoder"] THEN
    UNDISCH_TAC `n_neg < 2 EXP 520` THEN ARITH_TAC;
    ALL_TAC] THEN

  ABBREV_TAC `y' = if sgn /\ ~(y = 0) then p_521 - y else y` THEN

  (*** Main loop invariant setup. ***)

  ENSURES_WHILE_DOWN_TAC `104` `pc + 0x654` `pc + 0x18a9`
   `\i s.
      read RSP s = word_add stackpointer (word 664) /\
      read (memory :> bytes64(word_add stackpointer (word 4624))) s = res /\
      read RBP s = word (5 * i) /\
      bignum_from_memory(word_add stackpointer (word 664),9) s =
      2 EXP (576 - 5 * i) * n MOD (2 EXP (5 * i)) /\
      !P. P IN group_carrier p521_group /\ represents_p521 P (x,y',z)
          ==> represents_p521
                (group_zpow p521_group P
                    (&(n DIV 2 EXP (5 * i)) - &(recoder DIV 2 EXP (5 * i))))
                (bignum_triple_from_memory
                     (word_add stackpointer (word 736),9) s) /\
              !i. i < 16
                  ==> represents_p521 (group_pow p521_group P (i + 1))
                       (bignum_triple_from_memory
                       (word_add stackpointer (word(216 * i + 1168)),9) s)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initial holding of invariant ***)
    (*** First, the input reduced modulo the group order ***)

    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC P521_JSCALARMUL_ALT_EXEC (1--4) THEN
    LOCAL_MOD_N521_TAC 5 THEN

    (*** Reduction of input point coordinates, actually supererogatory ***)

    X86_STEPS_TAC P521_JSCALARMUL_ALT_EXEC (6--8) THEN
    LOCAL_MOD_P521_TAC 9 THEN
    X86_STEPS_TAC P521_JSCALARMUL_ALT_EXEC (10--12) THEN
    LOCAL_MOD_P521_TAC 13 THEN
    X86_STEPS_TAC P521_JSCALARMUL_ALT_EXEC (14--16) THEN
    LOCAL_MOD_P521_TAC 17 THEN

    (*** Conditional negation of scalar ***)

    BIGNUM_LDIGITIZE_TAC "nn_"
     `read (memory :> bytes (word_add stackpointer (word 664),8 * 9)) s17` THEN
    X86_ACCSTEPS_TAC P521_JSCALARMUL_ALT_EXEC
     [21;23;25;27;29;31;33;35;38] (18--58) THEN

    RULE_ASSUM_TAC(REWRITE_RULE[VAL_EQ_0]) THEN
    SUBGOAL_THEN `bit 8 (nn_8:int64) <=> sgn` SUBST_ALL_TAC THENL
     [EXPAND_TAC "sgn" THEN REWRITE_TAC[GSYM NOT_LT] THEN
      SUBGOAL_THEN `n_red < 2 EXP 520 <=>
                    (n_red DIV 2 EXP 512) MOD 2 EXP 9 < 2 EXP 8`
      SUBST1_TAC THENL
       [ASM_SIMP_TAC[DIV_MOD; ARITH_ADD; ARITH_SUC; GSYM EXP_ADD] THEN
        REWRITE_TAC[ARITH_RULE
         `n DIV 2 EXP 512 < 2 EXP 8 <=> n < 2 EXP 520`] THEN
        AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
        MATCH_MP_TAC MOD_LT THEN UNDISCH_TAC `n_red < n_521` THEN
        REWRITE_TAC[n_521] THEN ARITH_TAC;
        EXPAND_TAC "n_red" THEN
        CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV)] THEN
      CONV_TAC(ONCE_DEPTH_CONV VAL_EXPAND_CONV) THEN
      ASM_CASES_TAC `bit 8 (nn_8:int64)` THEN
      ASM_REWRITE_TAC[BITVAL_CLAUSES; NOT_LE; NOT_LT] THEN BOUNDER_TAC[];
      RULE_ASSUM_TAC(REWRITE_RULE[COND_SWAP])] THEN

    SUBGOAL_THEN
     `read (memory :> bytes (word_add stackpointer (word 664),8 * 9)) s58 =
      n_neg`
    ASSUME_TAC THENL
     [CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "n_neg" THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
      MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
      MAP_EVERY EXISTS_TAC [`576`; `&0:real`] THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
       [UNDISCH_TAC `n_red < n_521` THEN
        REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0; n_521] THEN ARITH_TAC;
        ALL_TAC] THEN
      CONJ_TAC THENL [REAL_INTEGER_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; LT_IMP_LE] THEN
      EXPAND_TAC "n_red" THEN
      REWRITE_TAC[bignum_of_wordlist; n_521; GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
      REWRITE_TAC[REAL_BITVAL_NOT; n_521] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN REAL_INTEGER_TAC;
      ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

    (*** Corresponding negation of the point (y coordinate) ***)

    BIGNUM_LDIGITIZE_TAC "y_"
    `read (memory :> bytes (word_add stackpointer (word 1240),8 * 9)) s58` THEN
    X86_STEPS_TAC P521_JSCALARMUL_ALT_EXEC (59--97) THEN

    SUBGOAL_THEN
     `read (memory :> bytes (word_add stackpointer (word 1240),8 * 9)) s97 =
      y'`
    ASSUME_TAC THENL
     [CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
      SIMP_TAC[WORD_SUB_0; VAL_EQ_0; COND_SWAP; WORD_BITVAL_EQ_0] THEN
      REWRITE_TAC[WORD_OR_EQ_0; GSYM CONJ_ASSOC] THEN
      MP_TAC(SPEC `[y_0;y_1;y_2;y_3;y_4;y_5;y_6;y_7;y_8]:int64 list`
        BIGNUM_OF_WORDLIST_EQ_0) THEN
      ASM_REWRITE_TAC[ALL; CONJ_ACI] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      EXPAND_TAC "y'" THEN COND_CASES_TAC THEN
      REWRITE_TAC[WORD_AND_0; WORD_XOR_0] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[WORD_XOR_MASK; WORD_AND_MASK] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[WORD_XOR_0] THEN
      MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 521` THEN CONJ_TAC THENL
       [SUBGOAL_THEN
         `word_xor y_8 (word 511):int64 =
          word_and (word 511) (word_xor y_8 (word 511))`
         (fun th -> SUBST1_TAC th THEN BOUNDER_TAC[]) THEN
        SUBGOAL_THEN `y < 2 EXP 521` MP_TAC THENL
         [UNDISCH_TAC `y < p_521` THEN REWRITE_TAC[p_521] THEN ARITH_TAC;
          EXPAND_TAC "y"] THEN
        REWRITE_TAC[ARITH_RULE
         `n < 2 EXP 521 <=> n DIV 2 EXP 512 < 2 EXP 9`] THEN
        CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
        CONV_TAC WORD_BLAST;
        ALL_TAC] THEN
      CONJ_TAC THENL [REWRITE_TAC[p_521] THEN ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[num_congruent; GSYM INT_OF_NUM_SUB; LT_IMP_LE] THEN
      REWRITE_TAC[REAL_INT_CONGRUENCE] THEN
      REWRITE_TAC[GSYM REAL_OF_INT_CLAUSES] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_POW_EQ_0] THEN
      REWRITE_TAC[REAL_OF_NUM_EQ; ARITH_EQ] THEN EXPAND_TAC "y" THEN
      REWRITE_TAC[bignum_of_wordlist; p_521; GSYM REAL_OF_NUM_CLAUSES] THEN
      CONV_TAC(ONCE_DEPTH_CONV VAL_EXPAND_CONV) THEN
      CONV_TAC(TOP_DEPTH_CONV BIT_WORD_CONV) THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_BITVAL_NOT] THEN
      REAL_INTEGER_TAC;
      ALL_TAC] THEN

    (*** Computation of 2 * P ***)

    X86_STEPS_TAC P521_JSCALARMUL_ALT_EXEC (98--100) THEN
    LOCAL_JDOUBLE_TAC 101 THEN
    MAP_EVERY ABBREV_TAC
     [`x2 = read(memory :> bytes(word_add stackpointer (word 1384),8 * 9)) s101`;
      `y2 = read(memory :> bytes(word_add stackpointer (word 1456),8 * 9)) s101`;
      `z2 = read(memory :> bytes(word_add stackpointer (word 1528),8 * 9)) s101`
     ] THEN

    (*** Computation of 3 * P ***)

    X86_STEPS_TAC P521_JSCALARMUL_ALT_EXEC (102--105) THEN
    LOCAL_JADD_TAC 106 THEN
    MAP_EVERY ABBREV_TAC
     [`x3 = read(memory :> bytes(word_add stackpointer (word 1600),8 * 9)) s106`;
      `y3 = read(memory :> bytes(word_add stackpointer (word 1672),8 * 9)) s106`;
      `z3 = read(memory :> bytes(word_add stackpointer (word 1744),8 * 9)) s106`
     ] THEN

    (*** Computation of 4 * P ***)

    X86_STEPS_TAC P521_JSCALARMUL_ALT_EXEC (107--109) THEN
    LOCAL_JDOUBLE_TAC 110 THEN
    MAP_EVERY ABBREV_TAC
     [`x4 = read(memory :> bytes(word_add stackpointer (word 1816),8 * 9)) s110`;
      `y4 = read(memory :> bytes(word_add stackpointer (word 1888),8 * 9)) s110`;
      `z4 = read(memory :> bytes(word_add stackpointer (word 1960),8 * 9)) s110`
     ] THEN

    (*** Computation of 5 * P ***)

    X86_STEPS_TAC P521_JSCALARMUL_ALT_EXEC (111--114) THEN
    LOCAL_JADD_TAC 115 THEN
    MAP_EVERY ABBREV_TAC
     [`x5 = read(memory :> bytes(word_add stackpointer (word 2032),8 * 9)) s115`;
      `y5 = read(memory :> bytes(word_add stackpointer (word 2104),8 * 9)) s115`;
      `z5 = read(memory :> bytes(word_add stackpointer (word 2176),8 * 9)) s115`
     ] THEN

    (*** Computation of 6 * P ***)

    X86_STEPS_TAC P521_JSCALARMUL_ALT_EXEC (116--118) THEN
    LOCAL_JDOUBLE_TAC 119 THEN
    MAP_EVERY ABBREV_TAC
     [`x6 = read(memory :> bytes(word_add stackpointer (word 2248),8 * 9)) s119`;
      `y6 = read(memory :> bytes(word_add stackpointer (word 2320),8 * 9)) s119`;
      `z6 = read(memory :> bytes(word_add stackpointer (word 2392),8 * 9)) s119`
     ] THEN

    (*** Computation of 7 * P ***)

    X86_STEPS_TAC P521_JSCALARMUL_ALT_EXEC (120--123) THEN
    LOCAL_JADD_TAC 124 THEN
    MAP_EVERY ABBREV_TAC
     [`x7 = read(memory :> bytes(word_add stackpointer (word 2464),8 * 9)) s124`;
      `y7 = read(memory :> bytes(word_add stackpointer (word 2536),8 * 9)) s124`;
      `z7 = read(memory :> bytes(word_add stackpointer (word 2608),8 * 9)) s124`
     ] THEN

    (*** Computation of 8 * P ***)

    X86_STEPS_TAC P521_JSCALARMUL_ALT_EXEC (125--127) THEN
    LOCAL_JDOUBLE_TAC 128 THEN
    MAP_EVERY ABBREV_TAC
     [`x8 = read(memory :> bytes(word_add stackpointer (word 2680),8 * 9)) s128`;
      `y8 = read(memory :> bytes(word_add stackpointer (word 2752),8 * 9)) s128`;
      `z8 = read(memory :> bytes(word_add stackpointer (word 2824),8 * 9)) s128`
     ] THEN

    (*** Computation of 9 * P ***)

    X86_STEPS_TAC P521_JSCALARMUL_ALT_EXEC (129--132) THEN
    LOCAL_JADD_TAC 133 THEN
    MAP_EVERY ABBREV_TAC
     [`x9 = read(memory :> bytes(word_add stackpointer (word 2896),8 * 9)) s133`;
      `y9 = read(memory :> bytes(word_add stackpointer (word 2968),8 * 9)) s133`;
      `z9 = read(memory :> bytes(word_add stackpointer (word 3040),8 * 9)) s133`
     ] THEN

    (*** Computation of 10 * P ***)

    X86_STEPS_TAC P521_JSCALARMUL_ALT_EXEC (134--136) THEN
    LOCAL_JDOUBLE_TAC 137 THEN
    MAP_EVERY ABBREV_TAC
     [`xa = read(memory :> bytes(word_add stackpointer (word 3112),8 * 9)) s137`;
      `ya = read(memory :> bytes(word_add stackpointer (word 3184),8 * 9)) s137`;
      `za = read(memory :> bytes(word_add stackpointer (word 3256),8 * 9)) s137`
     ] THEN

    (*** Computation of 11 * P ***)

    X86_STEPS_TAC P521_JSCALARMUL_ALT_EXEC (138--141) THEN
    LOCAL_JADD_TAC 142 THEN
    MAP_EVERY ABBREV_TAC
     [`xb = read(memory :> bytes(word_add stackpointer (word 3328),8 * 9)) s142`;
      `yb = read(memory :> bytes(word_add stackpointer (word 3400),8 * 9)) s142`;
      `zb = read(memory :> bytes(word_add stackpointer (word 3472),8 * 9)) s142`
     ] THEN

    (*** Computation of 12 * P ***)

    X86_STEPS_TAC P521_JSCALARMUL_ALT_EXEC (143--145) THEN
    LOCAL_JDOUBLE_TAC 146 THEN
    MAP_EVERY ABBREV_TAC
     [`xc = read(memory :> bytes(word_add stackpointer (word 3544),8 * 9)) s146`;
      `yc = read(memory :> bytes(word_add stackpointer (word 3616),8 * 9)) s146`;
      `zc = read(memory :> bytes(word_add stackpointer (word 3688),8 * 9)) s146`
     ] THEN

    (*** Computation of 13 * P ***)

    X86_STEPS_TAC P521_JSCALARMUL_ALT_EXEC (147--150) THEN
    LOCAL_JADD_TAC 151 THEN
    MAP_EVERY ABBREV_TAC
     [`xd = read(memory :> bytes(word_add stackpointer (word 3760),8 * 9)) s151`;
      `yd = read(memory :> bytes(word_add stackpointer (word 3832),8 * 9)) s151`;
      `zd = read(memory :> bytes(word_add stackpointer (word 3904),8 * 9)) s151`
     ] THEN

    (*** Computation of 14 * P ***)

    X86_STEPS_TAC P521_JSCALARMUL_ALT_EXEC (152--154) THEN
    LOCAL_JDOUBLE_TAC 155 THEN
    MAP_EVERY ABBREV_TAC
     [`xe = read(memory :> bytes(word_add stackpointer (word 3976),8 * 9)) s155`;
      `ye = read(memory :> bytes(word_add stackpointer (word 4048),8 * 9)) s155`;
      `ze = read(memory :> bytes(word_add stackpointer (word 4120),8 * 9)) s155`
     ] THEN

    (*** Computation of 15 * P ***)

    X86_STEPS_TAC P521_JSCALARMUL_ALT_EXEC (156--159) THEN
    LOCAL_JADD_TAC 160 THEN
    MAP_EVERY ABBREV_TAC
     [`xf = read(memory :> bytes(word_add stackpointer (word 4192),8 * 9)) s160`;
      `yf = read(memory :> bytes(word_add stackpointer (word 4264),8 * 9)) s160`;
      `zf = read(memory :> bytes(word_add stackpointer (word 4336),8 * 9)) s160`
     ] THEN

    (*** Computation of 16 * P ***)

    X86_STEPS_TAC P521_JSCALARMUL_ALT_EXEC (161--163) THEN
    LOCAL_JDOUBLE_TAC 164 THEN
    MAP_EVERY ABBREV_TAC
     [`xg = read(memory :> bytes(word_add stackpointer (word 4408),8 * 9)) s164`;
      `yg = read(memory :> bytes(word_add stackpointer (word 4480),8 * 9)) s164`;
      `zg = read(memory :> bytes(word_add stackpointer (word 4552),8 * 9)) s164`
     ] THEN

    (*** Add the recoding constant ***)

    DISCARD_MATCHING_ASSUMPTIONS [`read c s = if p then x else y`] THEN
    BIGNUM_LDIGITIZE_TAC "nr_"
     `read(memory :> bytes (word_add stackpointer (word 664),8 * 9)) s164` THEN
    X86_ACCSTEPS_TAC P521_JSCALARMUL_ALT_EXEC
      [169;171;174;177;180;182;184;187;189] (165--209) THEN
    SUBGOAL_THEN
     `bignum_of_wordlist
      [sum_s169; sum_s171; sum_s174; sum_s177; sum_s180;
       sum_s182; sum_s184; sum_s187; sum_s189] = n`
    ASSUME_TAC THENL
     [MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 576` THEN
      CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[REAL_CONGRUENCE; EXP_EQ_0; ARITH_EQ] THEN
      MAP_EVERY EXPAND_TAC ["n"; "recoder"; "n_neg"] THEN
      REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      REWRITE_TAC[VAL_WORD_BITVAL] THEN
      ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
      ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[COND_SWAP; GSYM WORD_BITVAL])] THEN

    (*** Selection of the top window by conditional selection ***)

    DISCARD_MATCHING_ASSUMPTIONS [`read c s = word_xor a b`] THEN
    BIGNUM_LDIGITIZE_TAC "xx_"
     `read(memory :> bytes (word_add stackpointer (word 1168),8 * 9)) s209` THEN
    BIGNUM_LDIGITIZE_TAC "yy_"
     `read(memory :> bytes (word_add stackpointer (word 1240),8 * 9)) s209` THEN
    BIGNUM_LDIGITIZE_TAC "zz_"
     `read(memory :> bytes (word_add stackpointer (word 1312),8 * 9)) s209` THEN
    X86_STEPS_TAC P521_JSCALARMUL_ALT_EXEC (210--293) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    CONV_TAC(DEPTH_CONV(NUM_ADD_CONV ORELSEC NUM_MULT_CONV)) THEN
    REWRITE_TAC[bignum_triple_from_memory] THEN
    CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
    CONV_TAC(DEPTH_CONV(NUM_ADD_CONV ORELSEC NUM_MULT_CONV)) THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXPAND_TAC "n" THEN REWRITE_TAC[ARITH_RULE
       `x = 2 EXP (576 - 520) * y MOD 2 EXP 520 <=>
        2 EXP 576 * y DIV 2 EXP 520 + x = 2 EXP 56 * y`] THEN
      CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
      REWRITE_TAC[bignum_of_wordlist] THEN CONV_TAC WORD_BLAST;
      REWRITE_TAC[WORD_SUB_0]] THEN
    X_GEN_TAC `P:(int#int)option` THEN STRIP_TAC THEN
    SUBGOAL_THEN `val(word_ushr sum_s189 8:int64) = n DIV 2 EXP 520`
    SUBST1_TAC THENL
     [EXPAND_TAC "n" THEN CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
      REWRITE_TAC[bignum_of_wordlist] THEN CONV_TAC WORD_BLAST;
      ALL_TAC] THEN
    SUBGOAL_THEN `n DIV 2 EXP 520 < 2` MP_TAC THENL
     [UNDISCH_TAC `n < 2 EXP 521` THEN ARITH_TAC;
      SPEC_TAC(`n DIV 2 EXP 520`,`b:num`)] THEN
    REWRITE_TAC[MESON[ARITH_RULE `0 < 2`]
      `(!b. b < 2 ==> P b /\ Q) <=> (Q ==> !b. b < 2 ==> P b) /\ Q`] THEN
    CONJ_TAC THENL
     [EXPAND_TAC "recoder" THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[INT_SUB_RZERO; GROUP_NPOW] THEN
      CONV_TAC(RAND_CONV EXPAND_CASES_CONV) THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
      ASM_REWRITE_TAC[WORD_SUB_0; VAL_WORD_BITVAL; BITVAL_EQ_0] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[group_pow; P521_GROUP; represents_p521; tripled;
                  weierstrass_of_jacobian; modular_decode; p_521;
                  bignum_of_wordlist; INTEGER_MOD_RING_CLAUSES] THEN
      CONV_TAC(DEPTH_CONV(WORD_NUM_RED_CONV ORELSEC INVERSE_MOD_CONV));
      ALL_TAC] THEN

    REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_forall o concl))) THEN
    DISCH_THEN(MP_TAC o SPEC `P:(int#int)option`) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC] THEN
    ASM_SIMP_TAC[GROUP_RULE `group_mul G x x = group_pow G x 2`] THEN
    GEN_REWRITE_TAC I [IMP_CONJ] THEN DISCH_TAC THEN
    GEN_REWRITE_TAC I [IMP_CONJ] THEN DISCH_THEN(MP_TAC o SPECL
     [`group_pow p521_group P 2`; `P:(int#int)option`]) THEN
    ASM_SIMP_TAC[GROUP_RULE `group_pow G x 2 = x <=> x = group_id G`] THEN
    ASM_SIMP_TAC[GROUP_RULE
     `group_mul G (group_pow G x 2) x = group_pow G x 3`] THEN
    ANTS_TAC THENL [REWRITE_TAC[P521_GROUP]; DISCH_TAC] THEN
    GEN_REWRITE_TAC I [IMP_CONJ] THEN DISCH_THEN(MP_TAC o SPEC
     `group_pow p521_group P 2`) THEN
    ASM_SIMP_TAC[GSYM GROUP_POW_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN
    DISCH_TAC THEN GEN_REWRITE_TAC I [IMP_CONJ] THEN DISCH_THEN(MP_TAC o SPECL
     [`group_pow p521_group P 4`; `P:(int#int)option`]) THEN
    ASM_SIMP_TAC[GROUP_RULE
     `group_mul G (group_pow G x 4) x = group_pow G x 5`] THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[GROUP_POW_EQ_ID; P521_GROUP_ELEMENT_ORDER; GROUP_RULE
        `group_pow G x 4 = x <=> group_pow G x 3 = group_id G`] THEN
      REWRITE_TAC[P521_GROUP] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
      REWRITE_TAC[n_521] THEN CONV_TAC(RAND_CONV DIVIDES_CONV) THEN
      REWRITE_TAC[];
      DISCH_TAC] THEN
    GEN_REWRITE_TAC I [IMP_CONJ] THEN DISCH_THEN(MP_TAC o SPEC
     `group_pow p521_group P 3`) THEN
    ASM_SIMP_TAC[GSYM GROUP_POW_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN
    DISCH_TAC THEN GEN_REWRITE_TAC I [IMP_CONJ] THEN DISCH_THEN(MP_TAC o SPECL
     [`group_pow p521_group P 6`; `P:(int#int)option`]) THEN
    ASM_SIMP_TAC[GROUP_RULE
     `group_mul G (group_pow G x 6) x = group_pow G x 7`] THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[GROUP_POW_EQ_ID; P521_GROUP_ELEMENT_ORDER; GROUP_RULE
        `group_pow G x 6 = x <=> group_pow G x 5 = group_id G`] THEN
      REWRITE_TAC[P521_GROUP] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
      REWRITE_TAC[n_521] THEN CONV_TAC(RAND_CONV DIVIDES_CONV) THEN
      REWRITE_TAC[];
      DISCH_TAC] THEN
    GEN_REWRITE_TAC I [IMP_CONJ] THEN DISCH_THEN(MP_TAC o SPEC
     `group_pow p521_group P 4`) THEN
    ASM_SIMP_TAC[GSYM GROUP_POW_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN
    DISCH_TAC THEN GEN_REWRITE_TAC I [IMP_CONJ] THEN DISCH_THEN(MP_TAC o SPECL
     [`group_pow p521_group P 8`; `P:(int#int)option`]) THEN
    ASM_SIMP_TAC[GROUP_RULE
     `group_mul G (group_pow G x 8) x = group_pow G x 9`] THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[GROUP_POW_EQ_ID; P521_GROUP_ELEMENT_ORDER; GROUP_RULE
        `group_pow G x 8 = x <=> group_pow G x 7 = group_id G`] THEN
      REWRITE_TAC[P521_GROUP] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
      REWRITE_TAC[n_521] THEN CONV_TAC(RAND_CONV DIVIDES_CONV) THEN
      REWRITE_TAC[];
      DISCH_TAC] THEN
    GEN_REWRITE_TAC I [IMP_CONJ] THEN DISCH_THEN(MP_TAC o SPEC
     `group_pow p521_group P 5`) THEN
    ASM_SIMP_TAC[GSYM GROUP_POW_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN
    DISCH_TAC THEN GEN_REWRITE_TAC I [IMP_CONJ] THEN DISCH_THEN(MP_TAC o SPECL
     [`group_pow p521_group P 10`; `P:(int#int)option`]) THEN
    ASM_SIMP_TAC[GROUP_RULE
     `group_mul G (group_pow G x 10) x = group_pow G x 11`] THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[GROUP_POW_EQ_ID; P521_GROUP_ELEMENT_ORDER; GROUP_RULE
        `group_pow G x 10 = x <=> group_pow G x 9 = group_id G`] THEN
      REWRITE_TAC[P521_GROUP] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
      REWRITE_TAC[n_521] THEN CONV_TAC(RAND_CONV DIVIDES_CONV) THEN
      REWRITE_TAC[];
      DISCH_TAC] THEN
    GEN_REWRITE_TAC I [IMP_CONJ] THEN DISCH_THEN(MP_TAC o SPEC
     `group_pow p521_group P 6`) THEN
    ASM_SIMP_TAC[GSYM GROUP_POW_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN
    DISCH_TAC THEN GEN_REWRITE_TAC I [IMP_CONJ] THEN DISCH_THEN(MP_TAC o SPECL
     [`group_pow p521_group P 12`; `P:(int#int)option`]) THEN
    ASM_SIMP_TAC[GROUP_RULE
     `group_mul G (group_pow G x 12) x = group_pow G x 13`] THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[GROUP_POW_EQ_ID; P521_GROUP_ELEMENT_ORDER; GROUP_RULE
        `group_pow G x 12 = x <=> group_pow G x 11 = group_id G`] THEN
      REWRITE_TAC[P521_GROUP] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
      REWRITE_TAC[n_521] THEN CONV_TAC(RAND_CONV DIVIDES_CONV) THEN
      REWRITE_TAC[];
      DISCH_TAC] THEN
    GEN_REWRITE_TAC I [IMP_CONJ] THEN DISCH_THEN(MP_TAC o SPEC
     `group_pow p521_group P 7`) THEN
    ASM_SIMP_TAC[GSYM GROUP_POW_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN
    DISCH_TAC THEN GEN_REWRITE_TAC I [IMP_CONJ] THEN DISCH_THEN(MP_TAC o SPECL
     [`group_pow p521_group P 14`; `P:(int#int)option`]) THEN
    ASM_SIMP_TAC[GROUP_RULE
     `group_mul G (group_pow G x 14) x = group_pow G x 15`] THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[GROUP_POW_EQ_ID; P521_GROUP_ELEMENT_ORDER; GROUP_RULE
        `group_pow G x 14 = x <=> group_pow G x 13 = group_id G`] THEN
      REWRITE_TAC[P521_GROUP] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
      REWRITE_TAC[n_521] THEN CONV_TAC(RAND_CONV DIVIDES_CONV) THEN
      REWRITE_TAC[];
      DISCH_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `group_pow p521_group P 8`) THEN
    ASM_SIMP_TAC[GSYM GROUP_POW_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN
    DISCH_TAC THEN ASM_SIMP_TAC[GROUP_POW_1];

    (*** Defer the main invariant preservation proof till below ***)

    ALL_TAC;

    (*** Trivial loop-back goal ***)

    REPEAT STRIP_TAC THEN CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    X86_SIM_TAC P521_JSCALARMUL_ALT_EXEC (1--2) THEN
    VAL_INT64_TAC `5 * i` THEN
    ASM_REWRITE_TAC[ARITH_RULE `5 * i = 0 <=> ~(0 < i)`];

    (*** Final copying to the output and specializing invariant ***)

    GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
     [bignum_triple_from_memory] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[DIV_1] THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    BIGNUM_LDIGITIZE_TAC "x_"
     `read (memory :> bytes(word_add stackpointer (word 736),8 * 9)) s0` THEN
    BIGNUM_LDIGITIZE_TAC "y_"
     `read (memory :> bytes(word_add stackpointer (word 808),8 * 9)) s0` THEN
    BIGNUM_LDIGITIZE_TAC "z_"
     `read (memory :> bytes(word_add stackpointer (word 880),8 * 9)) s0` THEN
    FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP (MESON[]
      `(!x. P x ==> Q x /\ R x) ==> (!x. P x ==> Q x)`)) THEN
    X86_STEPS_TAC P521_JSCALARMUL_ALT_EXEC (1--57) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
    DISCARD_STATE_TAC "s57" THEN X_GEN_TAC `P:(int#int)option` THEN
    STRIP_TAC THEN
    ABBREV_TAC `Q = if sgn then group_inv p521_group P else P` THEN
    SUBGOAL_THEN `Q IN group_carrier p521_group` ASSUME_TAC THENL
     [EXPAND_TAC "Q" THEN COND_CASES_TAC THEN ASM_SIMP_TAC[GROUP_INV];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `Q:(int#int)option`) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `group_zpow p521_group Q (&n - &recoder) = group_pow p521_group P n_input`
    SUBST1_TAC THENL
     [MAP_EVERY EXPAND_TAC ["Q"; "n"; "n_neg"; "n_red"] THEN
      REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
      REWRITE_TAC[INT_ARITH `(x + y) - y:int = x`] THEN
      COND_CASES_TAC THEN REWRITE_TAC[GSYM INT_OF_NUM_REM; GSYM GROUP_NPOW] THEN
      ASM_SIMP_TAC[GSYM GROUP_INV_ZPOW; GSYM GROUP_ZPOW_NEG; GROUP_ZPOW_EQ] THEN
      ASM_SIMP_TAC[P521_GROUP_ELEMENT_ORDER; INT_CONG_LREM; INT_CONG_REFL] THEN
      EXPAND_TAC "n_red" THEN COND_CASES_TAC THEN
      REWRITE_TAC[INT_CONG_MOD_1] THEN
      (SUBGOAL_THEN `n_input MOD n_521 <= n_521`
       (fun th -> SIMP_TAC[GSYM INT_OF_NUM_SUB; th])
       THENL [REWRITE_TAC[n_521] THEN ARITH_TAC; ALL_TAC]) THEN
      REWRITE_TAC[INTEGER_RULE
      `(--(n - x):int == y) (mod n) <=> (x == y) (mod n)`] THEN
      REWRITE_TAC[INT_CONG_LREM; INT_CONG_REFL; GSYM INT_OF_NUM_REM];
      DISCH_THEN MATCH_MP_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP REPRESENTS_P521_REDUCTION) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MAP_EVERY EXPAND_TAC ["y'"; "Q"] THEN
    BOOL_CASES_TAC `sgn:bool` THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP REPRESENTS_P521_NEGATION_ALT) THEN
    ASM_SIMP_TAC[COND_SWAP]] THEN

  (**** Now the preservation of the loop invariant ***)

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  CONV_TAC(RATOR_CONV(LAND_CONV(ONCE_DEPTH_CONV EXPAND_CASES_CONV))) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
   [bignum_triple_from_memory] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN

  GHOST_INTRO_TAC `Xa:num`
   `bignum_from_memory (word_add stackpointer (word 736),9)` THEN
  GHOST_INTRO_TAC `Ya:num`
   `bignum_from_memory (word_add stackpointer (word 808),9)` THEN
  GHOST_INTRO_TAC `Za:num`
   `bignum_from_memory (word_add stackpointer (word 880),9)` THEN

  (*** Computation of 2 * (Xa,Ya,Za) ***)

  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC P521_JSCALARMUL_ALT_EXEC (1--4) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
   `word_sub (word (5 * (i + 1))) (word 5) = word(5 * i)`]) THEN
  LOCAL_JDOUBLE_TAC 5 THEN
  MAP_EVERY ABBREV_TAC
   [`X2a = read (memory :> bytes(word_add stackpointer (word 736),8 * 9)) s5`;
    `Y2a = read (memory :> bytes(word_add stackpointer (word 808),8 * 9)) s5`;
    `Z2a = read (memory :> bytes(word_add stackpointer (word 880),8 * 9)) s5`
   ] THEN

  (*** Computation of 4 * (Xa,Ya,Za) ***)

  X86_STEPS_TAC P521_JSCALARMUL_ALT_EXEC (6--8) THEN
  LOCAL_JDOUBLE_TAC 9 THEN
  MAP_EVERY ABBREV_TAC
   [`X4a = read (memory :> bytes(word_add stackpointer (word 736),8 * 9)) s9`;
    `Y4a = read (memory :> bytes(word_add stackpointer (word 808),8 * 9)) s9`;
    `Z4a = read (memory :> bytes(word_add stackpointer (word 880),8 * 9)) s9`
   ] THEN

  (*** Computation of 8 * (Xa,Ya,Za) ***)

  X86_STEPS_TAC P521_JSCALARMUL_ALT_EXEC (10--12) THEN
  LOCAL_JDOUBLE_TAC 13 THEN
  MAP_EVERY ABBREV_TAC
   [`X8a = read (memory :> bytes(word_add stackpointer (word 736),8 * 9)) s13`;
    `Y8a = read (memory :> bytes(word_add stackpointer (word 808),8 * 9)) s13`;
    `Z8a = read (memory :> bytes(word_add stackpointer (word 880),8 * 9)) s13`
   ] THEN

  (*** Computation of 16 * (Xa,Ya,Za) ***)

  X86_STEPS_TAC P521_JSCALARMUL_ALT_EXEC (14--16) THEN
  LOCAL_JDOUBLE_TAC 17 THEN
  MAP_EVERY ABBREV_TAC
   [`Xha = read (memory :> bytes(word_add stackpointer (word 736),8 * 9)) s17`;
    `Yha = read (memory :> bytes(word_add stackpointer (word 808),8 * 9)) s17`;
    `Zha = read (memory :> bytes(word_add stackpointer (word 880),8 * 9)) s17`
   ] THEN

  (*** Computation of 32 * (Xa,Ya,Za) ***)

  X86_STEPS_TAC P521_JSCALARMUL_ALT_EXEC (18--20) THEN
  LOCAL_JDOUBLE_TAC 21 THEN
  MAP_EVERY ABBREV_TAC
   [`Xta = read (memory :> bytes(word_add stackpointer (word 736),8 * 9)) s21`;
    `Yta = read (memory :> bytes(word_add stackpointer (word 808),8 * 9)) s21`;
    `Zta = read (memory :> bytes(word_add stackpointer (word 880),8 * 9)) s21`
   ] THEN

  (*** Selection of bitfield ***)

  BIGNUM_LDIGITIZE_TAC "n_"
    `read (memory :> bytes (word_add stackpointer (word 664),8 * 9)) s21` THEN
  X86_STEPS_TAC P521_JSCALARMUL_ALT_EXEC (22--54) THEN
  ABBREV_TAC `bf = (n DIV (2 EXP (5 * i))) MOD 32` THEN
  SUBGOAL_THEN
   `word_ushr (n_8:int64) 59 = word bf /\
    read (memory :> bytes (word_add stackpointer (word 664),8 * 9)) s54 =
    2 EXP (576 - 5 * i) * n MOD 2 EXP (5 * i)`
  MP_TAC THENL
   [EXPAND_TAC "bf" THEN
    SUBGOAL_THEN
     `(n DIV 2 EXP (5 * i)) MOD 32 =
      (2 EXP 5 *
       bignum_of_wordlist [n_0; n_1; n_2; n_3; n_4; n_5; n_6; n_7; n_8]) DIV
      2 EXP 576 /\
      2 EXP (576 - 5 * i) * n MOD 2 EXP (5 * i) =
      (2 EXP 5 *
       bignum_of_wordlist[n_0; n_1; n_2; n_3; n_4; n_5; n_6; n_7; n_8]) MOD
      2 EXP 576`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [CONV_TAC(BINOP_CONV SYM_CONV) THEN MATCH_MP_TAC DIVMOD_UNIQ THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [EXPAND_TAC "bf" THEN REWRITE_TAC[GSYM(NUM_REDUCE_CONV `2 EXP 5`)] THEN
        REWRITE_TAC[EXP_ADD; MOD_MULT_MOD; ARITH_RULE
         `5 * (i + 1) = 5 * i + 5`] THEN
        ASM_REWRITE_TAC[MULT_ASSOC; GSYM EXP_ADD] THEN
        ASM_SIMP_TAC[ARITH_RULE
         `i < 104 ==> 5 + 576 - (5 * i + 5) = 576 - 5 * i`] THEN
        REWRITE_TAC[ARITH_RULE`e * (a + b):num = x + e * b <=> e * a = x`] THEN
        ASM_SIMP_TAC[MULT_ASSOC; GSYM EXP_ADD; ARITH_RULE
         `i < 104 ==> 576 - 5 * i + 5 * i = 576`] THEN
        ARITH_TAC;
        SUBGOAL_THEN `2 EXP 576 = 2 EXP (576 - 5 * i) * 2 EXP (5 * i)`
        SUBST1_TAC THENL
         [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN
          UNDISCH_TAC `i < 104` THEN ARITH_TAC;
          REWRITE_TAC[LT_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ; MOD_LT_EQ]]];
      REWRITE_TAC[bignum_of_wordlist] THEN
      CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
      ASM_REWRITE_TAC[word_ushr] THEN MATCH_MP_TAC(MESON[]
       `q = a /\ r = b ==> word a = word q /\ b = r`) THEN
      MATCH_MP_TAC DIVMOD_UNIQ THEN
      CONJ_TAC THENL [ALL_TAC; BOUNDER_TAC[]] THEN
      REWRITE_TAC[bignum_of_wordlist] THEN CONV_TAC WORD_BLAST];
    DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)] THEN

  (*** Sign-magnitude recoding of bitfield ***)

  SUBGOAL_THEN `val(word bf:int64) = bf` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    EXPAND_TAC "bf" THEN ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `ix = if bf < 16 then 16 - bf else bf - 16` THEN

  FIRST_X_ASSUM(MP_TAC o SPEC `word ix:int64` o MATCH_MP (MESON[]
   `read RDI s = x ==> !x'. x = x' ==> read RDI s = x'`)) THEN
  ANTS_TAC THENL
   [EXPAND_TAC "ix" THEN REWRITE_TAC[WORD_XOR_MASK] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES; WORD_NEG_SUB; WORD_NEG_0;
     WORD_SUB_0; WORD_RULE
     `word_sub (word_not x) (word_neg(word 1)) = word_neg x`] THEN
    ASM_REWRITE_TAC[WORD_SUB] THEN ASM_ARITH_TAC;
    DISCH_TAC] THEN

  (*** Constant-time selection from the table ***)

  BIGNUM_LDIGITIZE_TAC "tab_"
   `read(memory :> bytes(word_add stackpointer (word 1168),8 * 432)) s54` THEN
  X86_STEPS_TAC P521_JSCALARMUL_ALT_EXEC (55--579) THEN

  MAP_EVERY ABBREV_TAC
   [`Xt = read (memory :> bytes(word_add stackpointer (word 952),8 * 9)) s579`;
    `Zt = read (memory :> bytes(word_add stackpointer (word 1096),8 * 9)) s579`
   ] THEN
  MAP_EVERY REABBREV_TAC
   [`tab0 = read RAX s579`;
    `tab1 = read RBX s579`;
    `tab2 = read RCX s579`;
    `tab3 = read RDX s579`;
    `tab4 = read R8 s579`;
    `tab5 = read R9 s579`;
    `tab6 = read R10 s579`;
    `tab7 = read R11 s579`;
    `tab8 = read R12 s579`] THEN

  SUBGOAL_THEN
   `!P. P IN group_carrier p521_group /\ represents_p521 P (x,y',z)
        ==> represents_p521 (group_pow p521_group P ix)
               (Xt,
                bignum_of_wordlist
                 [tab0;tab1;tab2;tab3;tab4;tab5;tab6;tab7;tab8],
                Zt)`
  ASSUME_TAC THENL
   [X_GEN_TAC `P:(int#int)option` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `P:(int#int)option`) THEN
    MAP_EVERY EXPAND_TAC ["Xt"; "Zt"] THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MAP_EVERY EXPAND_TAC
     (map (fun n -> "tab"^string_of_int n) (0--8)) THEN
    SUBGOAL_THEN `ix < 17` MP_TAC THENL
     [MAP_EVERY EXPAND_TAC ["ix"; "bf"] THEN ARITH_TAC;
      SPEC_TAC(`ix:num`,`ix:num`)] THEN
    CONV_TAC EXPAND_CASES_CONV THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    ASM_REWRITE_TAC[CONJUNCT1 group_pow] THEN
    REWRITE_TAC[group_pow; P521_GROUP; represents_p521; tripled;
                weierstrass_of_jacobian; modular_decode; p_521;
                bignum_of_wordlist; INTEGER_MOD_RING_CLAUSES] THEN
    CONV_TAC(DEPTH_CONV(WORD_NUM_RED_CONV ORELSEC INVERSE_MOD_CONV));
    ALL_TAC] THEN

  (*** Optional negation of the table entry ***)

  X86_STEPS_TAC P521_JSCALARMUL_ALT_EXEC (580--611) THEN
  ABBREV_TAC
   `Yt =
    read(memory :> bytes(word_add stackpointer (word 1024),8 * 9)) s611` THEN
  SUBGOAL_THEN
   `!P. P IN group_carrier p521_group /\ represents_p521 P (x,y',z)
        ==> represents_p521 (group_zpow p521_group P (&bf - &16)) (Xt,Yt,Zt)`
  ASSUME_TAC THENL
   [X_GEN_TAC `P:(int#int)option` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(K ALL_TAC o SPEC `P:(int#int)option`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `P:(int#int)option`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN EXPAND_TAC "Yt" THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&bf - &16:int = if bf < 16 then --(&ix) else &ix`
    SUBST1_TAC THENL
     [EXPAND_TAC "ix" THEN
      SUBGOAL_THEN `bf < 32` MP_TAC THENL
       [EXPAND_TAC "bf" THEN ARITH_TAC; POP_ASSUM_LIST(K ALL_TAC)] THEN
      COND_CASES_TAC THEN ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB; GSYM NOT_LT] THEN
      ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB; LT_IMP_LE] THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    SIMP_TAC[WORD_SUB_0; VAL_EQ_0; COND_SWAP; WORD_BITVAL_EQ_0] THEN
    REWRITE_TAC[WORD_OR_EQ_0; GSYM CONJ_ASSOC] THEN
    MP_TAC(SPEC `[tab0;tab1;tab2;tab3;tab4;tab5;tab6;tab7;tab8]:int64 list`
      BIGNUM_OF_WORDLIST_EQ_0) THEN
    ASM_REWRITE_TAC[ALL; CONJ_ACI] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN

    ASM_CASES_TAC `bf < 16` THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES; WORD_NEG_0; COND_ID;
                    GROUP_NPOW; WORD_XOR_0; WORD_AND_0] THEN

    FIRST_ASSUM(MP_TAC o MATCH_MP REPRESENTS_P521_NEGATION_ALT) THEN
    ASM_SIMP_TAC[GROUP_POW; GROUP_ZPOW_NEG; GROUP_NPOW] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[WORD_XOR_0; WORD_AND_0] THEN
    REWRITE_TAC[WORD_BLAST
     `word_xor (x:int64) (word_neg(word 1)) = word_not x`] THEN
    CONV_TAC WORD_REDUCE_CONV THEN
    MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 521` THEN CONJ_TAC THENL
     [REWRITE_TAC[p_521] THEN ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN
       `word_xor tab8 (word 511):int64 =
        word_and (word 511) (word_xor tab8 (word 511))`
       (fun th -> SUBST1_TAC th THEN BOUNDER_TAC[]) THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [represents_p521]) THEN
      DISCH_THEN(MP_TAC o el 1 o CONJUNCTS) THEN
      DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
       `m < n ==> m DIV 2 EXP 512 <= n DIV 2 EXP 512`)) THEN
      CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
      REWRITE_TAC[p_521] THEN CONV_TAC NUM_REDUCE_CONV THEN
      CONV_TAC WORD_BLAST;
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [represents_p521]) THEN
    SIMP_TAC[REAL_CONGRUENCE; EXP_EQ_0; ARITH_EQ;
             GSYM REAL_OF_NUM_SUB; LT_IMP_LE] THEN
    DISCH_THEN(K ALL_TAC) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist;
                REAL_VAL_WORD_NOT; DIMINDEX_64; p_521] THEN
    CONV_TAC(ONCE_DEPTH_CONV VAL_EXPAND_CONV) THEN
    CONV_TAC(TOP_DEPTH_CONV BIT_WORD_CONV) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_BITVAL_NOT] THEN
    REAL_INTEGER_TAC;
    ALL_TAC] THEN

  (*** Final addition of the table entry ***)

  X86_STEPS_TAC P521_JSCALARMUL_ALT_EXEC (612--615) THEN
  LOCAL_JADD_TAC 616 THEN
  MAP_EVERY ABBREV_TAC
   [`X' = read (memory :> bytes(word_add stackpointer (word 736),8 * 9)) s616`;
    `Y' = read (memory :> bytes(word_add stackpointer (word 808),8 * 9)) s616`;
    `Z' = read (memory :> bytes(word_add stackpointer (word 880),8 * 9)) s616`
   ] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  (*** The final mathematics ***)

  X_GEN_TAC `P:(int#int)option` THEN STRIP_TAC THEN
  CONV_TAC(RAND_CONV EXPAND_CASES_CONV) THEN
  REWRITE_TAC[bignum_triple_from_memory] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
  ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `P:(int#int)option`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (fun th -> REWRITE_TAC[th])) THEN
  ABBREV_TAC
   `Q = group_zpow p521_group P
      (&(n DIV 2 EXP (5 * (i + 1))) -
       &(recoder DIV 2 EXP (5 * (i + 1))))` THEN
  SUBGOAL_THEN `Q IN group_carrier p521_group` ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN MATCH_MP_TAC GROUP_ZPOW THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_THEN
   `!P. represents_p521 P (Xa,Ya,Za)
        ==> represents_p521 (group_mul p521_group P P) (X2a,Y2a,Z2a)`
   (MP_TAC o SPEC `Q:(int#int)option`) THEN
  ASM_SIMP_TAC[GROUP_RULE `group_mul G x x = group_pow G x 2`] THEN
  DISCH_TAC THEN UNDISCH_THEN
   `!P. represents_p521 P (X2a,Y2a,Z2a)
        ==> represents_p521 (group_mul p521_group P P) (X4a,Y4a,Z4a)`
   (MP_TAC o SPEC `group_pow p521_group Q 2`) THEN
  ASM_SIMP_TAC[GSYM GROUP_POW_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_TAC THEN UNDISCH_THEN
   `!P. represents_p521 P (X4a,Y4a,Z4a)
        ==> represents_p521 (group_mul p521_group P P) (X8a,Y8a,Z8a)`
   (MP_TAC o SPEC `group_pow p521_group Q 4`) THEN
  ASM_SIMP_TAC[GSYM GROUP_POW_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_TAC THEN UNDISCH_THEN
   `!P. represents_p521 P (X8a,Y8a,Z8a)
        ==> represents_p521 (group_mul p521_group P P) (Xha,Yha,Zha)`
   (MP_TAC o SPEC `group_pow p521_group Q 8`) THEN
  ASM_SIMP_TAC[GSYM GROUP_POW_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_TAC THEN UNDISCH_THEN
   `!P. represents_p521 P (Xha,Yha,Zha)
        ==> represents_p521 (group_mul p521_group P P) (Xta,Yta,Zta)`
   (MP_TAC o SPEC `group_pow p521_group Q 16`) THEN
  ASM_SIMP_TAC[GSYM GROUP_POW_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL
   [`group_pow p521_group Q 32`;
    `group_zpow p521_group P (&bf - &16)`]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `P:(int#int)option`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[GSYM GROUP_NPOW] THEN EXPAND_TAC "Q" THEN
  ASM_SIMP_TAC[GSYM GROUP_ZPOW_MUL; GSYM GROUP_ZPOW_ADD] THEN
  ANTS_TAC THENL
   [SUBST1_TAC(SYM(el 1 (CONJUNCTS P521_GROUP))) THEN
    ASM_SIMP_TAC[GROUP_ZPOW_EQ; GROUP_ZPOW_EQ_ID;
                 P521_GROUP_ELEMENT_ORDER] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[INT_DIVIDES_1] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
        INT_CONG_IMP_EQ)) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC(INT_ARITH
       `&32 * max (&x) (&y) + abs(bf) + &16:int < n
        ==> abs((&x - &y) * &32 - (bf - &16)) < n`) THEN
      REWRITE_TAC[INT_OF_NUM_CLAUSES; INT_ABS_NUM] THEN
      REWRITE_TAC[ARITH_RULE `5 * (i + 1) = 5 * i + 5`; EXP_ADD] THEN
      REWRITE_TAC[GSYM DIV_DIV] THEN MATCH_MP_TAC(ARITH_RULE
        `a + c + d < n /\ b + c + d < n
         ==> 32 * MAX (a DIV 2 EXP 5) (b DIV 2 EXP 5) + c + d < n`) THEN
      CONJ_TAC THEN MATCH_MP_TAC(ARITH_RULE
       `n DIV m <= n /\ n + x < y ==> n DIV m + x < y`) THEN
      REWRITE_TAC[DIV_LE] THEN
      EXPAND_TAC "n" THEN UNDISCH_TAC `n_neg < 2 EXP 520` THEN
      MAP_EVERY EXPAND_TAC ["recoder"; "bf"] THEN
      REWRITE_TAC[n_521] THEN ARITH_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `&bf - &16:int = &0` THEN ASM_REWRITE_TAC[INT_DIVIDES_0] THEN
    UNDISCH_TAC `~(&bf - &16:int = &0)` THEN
    MATCH_MP_TAC(TAUT `(p ==> ~q) ==> p ==> q ==> r`) THEN
    MATCH_MP_TAC(INT_ARITH
     `abs(y:int) < &32 /\ (~(x = &0) ==> &1 <= abs(x))
      ==> ~(y = &0) ==> ~(x * &32 = y)`) THEN
    CONJ_TAC THENL [EXPAND_TAC "bf"; CONV_TAC INT_ARITH] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; GSYM INT_OF_NUM_REM] THEN
    CONV_TAC INT_ARITH;
    MATCH_MP_TAC EQ_IMP] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN
   `!n. n DIV 2 EXP (5 * i) =
        32 * (n DIV 2 EXP (5 * (i + 1))) + (n DIV 2 EXP (5 * i)) MOD 32`
  MP_TAC THENL
   [REWRITE_TAC[ARITH_RULE `5 * (i + 1) = 5 * i + 5`; EXP_ADD] THEN
    REWRITE_TAC[GSYM DIV_DIV] THEN ARITH_TAC;
    DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `(recoder DIV 2 EXP (5 * i)) MOD 32 = 16` SUBST1_TAC THENL
   [UNDISCH_TAC `i < 104` THEN SPEC_TAC(`i:num`,`i:num`) THEN
    EXPAND_TAC "recoder" THEN POP_ASSUM_LIST(K ALL_TAC) THEN
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN CONV_TAC INT_ARITH);;

let P521_JSCALARMUL_ALT_NOIBT_SUBROUTINE_CORRECT = time prove
 (`!res scalar point n xyz pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 4744),4744))
            [(word pc,LENGTH p521_jscalarmul_alt_tmc); (scalar,72); (point,216)] /\
        ALL (nonoverlapping (res,216))
            [(word pc,LENGTH p521_jscalarmul_alt_tmc); (word_sub stackpointer (word 4744),4752)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) p521_jscalarmul_alt_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [res;scalar;point] s /\
                  bignum_from_memory (scalar,9) s = n /\
                  bignum_triple_from_memory (point,9) s = xyz)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !P. P IN group_carrier p521_group /\
                      represents_p521 P xyz
                      ==> represents_p521
                            (group_pow p521_group P n)
                            (bignum_triple_from_memory(res,9) s))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE[memory :> bytes(res,216);
                     memory :> bytes(word_sub stackpointer (word 4744),4744)])`,
   X86_ADD_RETURN_STACK_TAC P521_JSCALARMUL_ALT_EXEC
     P521_JSCALARMUL_ALT_CORRECT `[RBX; RBP; R12; R13; R14; R15]` 4744);;

let P521_JSCALARMUL_ALT_SUBROUTINE_CORRECT = time prove
 (`!res scalar point n xyz pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 4744),4744))
            [(word pc,LENGTH p521_jscalarmul_alt_mc); (scalar,72); (point,216)] /\
        ALL (nonoverlapping (res,216))
            [(word pc,LENGTH p521_jscalarmul_alt_mc); (word_sub stackpointer (word 4744),4752)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) p521_jscalarmul_alt_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [res;scalar;point] s /\
                  bignum_from_memory (scalar,9) s = n /\
                  bignum_triple_from_memory (point,9) s = xyz)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !P. P IN group_carrier p521_group /\
                      represents_p521 P xyz
                      ==> represents_p521
                            (group_pow p521_group P n)
                            (bignum_triple_from_memory(res,9) s))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE[memory :> bytes(res,216);
                     memory :> bytes(word_sub stackpointer (word 4744),4744)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE P521_JSCALARMUL_ALT_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let p521_jscalarmul_alt_windows_mc = define_from_elf "p521_jscalarmul_alt_windows_mc"
      "x86/p521/p521_jscalarmul_alt.obj";;

let p521_jscalarmul_alt_windows_tmc = define_trimmed "p521_jscalarmul_alt_windows_tmc" p521_jscalarmul_alt_windows_mc;;

let P521_JSCALARMUL_ALT_NOIBT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!res scalar point n xyz pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 4768),4768))
            [(word pc,LENGTH p521_jscalarmul_alt_windows_tmc); (scalar,72); (point,216)] /\
        ALL (nonoverlapping (res,216))
            [(word pc,LENGTH p521_jscalarmul_alt_windows_tmc); (word_sub stackpointer (word 4768),4776)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) p521_jscalarmul_alt_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [res;scalar;point] s /\
                  bignum_from_memory (scalar,9) s = n /\
                  bignum_triple_from_memory (point,9) s = xyz)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !P. P IN group_carrier p521_group /\
                      represents_p521 P xyz
                      ==> represents_p521
                            (group_pow p521_group P n)
                            (bignum_triple_from_memory(res,9) s))
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE[memory :> bytes(res,216);
                     memory :> bytes(word_sub stackpointer (word 4768),4768)])`,
  let WINDOWS_P521_JSCALARMUL_ALT_EXEC =
    X86_MK_EXEC_RULE p521_jscalarmul_alt_windows_tmc
  and baseth =
    X86_SIMD_SHARPEN_RULE P521_JSCALARMUL_ALT_NOIBT_SUBROUTINE_CORRECT
    (X86_ADD_RETURN_STACK_TAC P521_JSCALARMUL_ALT_EXEC
     P521_JSCALARMUL_ALT_CORRECT `[RBX; RBP; R12; R13; R14; R15]` 4744) in
  let subth =
    CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
     (REWRITE_RULE[bignum_triple_from_memory] baseth) in
  REWRITE_TAC[fst WINDOWS_P521_JSCALARMUL_ALT_EXEC] THEN
  REPLICATE_TAC 6 GEN_TAC THEN WORD_FORALL_OFFSET_TAC 4768 THEN
  REWRITE_TAC[ALL; WINDOWS_C_ARGUMENTS; SOME_FLAGS;
              WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN REPEAT STRIP_TAC THEN
  ENSURES_PRESERVED_TAC "rsi_init" `RSI` THEN
  ENSURES_PRESERVED_TAC "rdi_init" `RDI` THEN
  REWRITE_TAC[bignum_triple_from_memory; WORD_RULE
    `word(8 * 9) = word 72 /\ word(16 * 9) = word 144`] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
  UNDISCH_THEN `read RSP s0 = word_add stackpointer (word 4768)`
   (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th) THEN
  RULE_ASSUM_TAC
   (CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)) THEN
  X86_STEPS_TAC WINDOWS_P521_JSCALARMUL_ALT_EXEC (1--6) THEN
  X86_SUBROUTINE_SIM_TAC
   (p521_jscalarmul_alt_windows_tmc,
    WINDOWS_P521_JSCALARMUL_ALT_EXEC,
    0x13,p521_jscalarmul_alt_tmc,subth)
   [`read RDI s`; `read RSI s`; `read RDX s`;
    `read(memory :> bytes(read RSI s,8 * 9)) s`;
    `read(memory :> bytes(read RDX s,8 * 9)) s,
     read(memory :> bytes(word_add (read RDX s) (word 72),8 * 9)) s,
     read(memory :> bytes(word_add (read RDX s) (word 144),8 * 9)) s`;
    `pc + 0x13`; `read RSP s`;
    `read (memory :> bytes64 (read RSP s)) s`] 7 THEN
  X86_STEPS_TAC WINDOWS_P521_JSCALARMUL_ALT_EXEC (8--10) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;

let P521_JSCALARMUL_ALT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!res scalar point n xyz pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 4768),4768))
            [(word pc,LENGTH p521_jscalarmul_alt_windows_mc); (scalar,72); (point,216)] /\
        ALL (nonoverlapping (res,216))
            [(word pc,LENGTH p521_jscalarmul_alt_windows_mc); (word_sub stackpointer (word 4768),4776)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) p521_jscalarmul_alt_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [res;scalar;point] s /\
                  bignum_from_memory (scalar,9) s = n /\
                  bignum_triple_from_memory (point,9) s = xyz)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !P. P IN group_carrier p521_group /\
                      represents_p521 P xyz
                      ==> represents_p521
                            (group_pow p521_group P n)
                            (bignum_triple_from_memory(res,9) s))
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE[memory :> bytes(res,216);
                     memory :> bytes(word_sub stackpointer (word 4768),4768)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE P521_JSCALARMUL_ALT_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

