(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Decoding of compressed form of point on edwards25519.                     *)
(* ========================================================================= *)

needs "Library/jacobi.ml";;
needs "x86/proofs/base.ml";;
needs "common/ecencoding.ml";;
needs "EC/edwards25519.ml";;

prioritize_int();;
prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* The code.                                                                 *)
(* ------------------------------------------------------------------------- *)

(**** print_literal_from_elf "x86/curve25519/edwards25519_decode_alt.o";;
 ****)

let edwards25519_decode_alt_mc = define_assert_from_elf "edwards25519_decode_alt_mc" "x86/curve25519/edwards25519_decode_alt.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x53;                    (* PUSH (% rbx) *)
  0x55;                    (* PUSH (% rbp) *)
  0x41; 0x54;              (* PUSH (% r12) *)
  0x41; 0x55;              (* PUSH (% r13) *)
  0x41; 0x56;              (* PUSH (% r14) *)
  0x41; 0x57;              (* PUSH (% r15) *)
  0x48; 0x81; 0xec; 0x00; 0x01; 0x00; 0x00;
                           (* SUB (% rsp) (Imm32 (word 256)) *)
  0x48; 0x89; 0xbc; 0x24; 0xe0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,224))) (% rdi) *)
  0x48; 0x8b; 0x06;        (* MOV (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0x89; 0x04; 0x24;  (* MOV (Memop Quadword (%% (rsp,0))) (% rax) *)
  0x48; 0x8b; 0x5e; 0x08;  (* MOV (% rbx) (Memop Quadword (%% (rsi,8))) *)
  0x48; 0x89; 0x5c; 0x24; 0x08;
                           (* MOV (Memop Quadword (%% (rsp,8))) (% rbx) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0x48; 0x8b; 0x4e; 0x10;  (* MOV (% rcx) (Memop Quadword (%% (rsi,16))) *)
  0x48; 0x89; 0x4c; 0x24; 0x10;
                           (* MOV (Memop Quadword (%% (rsp,16))) (% rcx) *)
  0x48; 0x8b; 0x56; 0x18;  (* MOV (% rdx) (Memop Quadword (%% (rsi,24))) *)
  0x48; 0x0f; 0xba; 0xf2; 0x3f;
                           (* BTR (% rdx) (Imm8 (word 63)) *)
  0x48; 0x89; 0x54; 0x24; 0x18;
                           (* MOV (Memop Quadword (%% (rsp,24))) (% rdx) *)
  0x48; 0x11; 0xed;        (* ADC (% rbp) (% rbp) *)
  0x48; 0x89; 0xac; 0x24; 0xe8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,232))) (% rbp) *)
  0x48; 0x83; 0xc0; 0x13;  (* ADD (% rax) (Imm8 (word 19)) *)
  0x48; 0x83; 0xd3; 0x00;  (* ADC (% rbx) (Imm8 (word 0)) *)
  0x48; 0x83; 0xd1; 0x00;  (* ADC (% rcx) (Imm8 (word 0)) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x48; 0xc1; 0xea; 0x3f;  (* SHR (% rdx) (Imm8 (word 63)) *)
  0x48; 0x89; 0x94; 0x24; 0xf0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,240))) (% rdx) *)
  0x48; 0x8d; 0xbc; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rsp,128)) *)
  0x48; 0xc7; 0xc6; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% rsi) (Imm32 (word 1)) *)
  0x48; 0x8d; 0x14; 0x24;  (* LEA (% rdx) (%% (rsp,0)) *)
  0xe8; 0xf7; 0x06; 0x00; 0x00;
                           (* CALL (Imm32 (word 1783)) *)
  0x48; 0x8b; 0x84; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,128))) *)
  0x48; 0x83; 0xe8; 0x14;  (* SUB (% rax) (Imm8 (word 20)) *)
  0x48; 0x8b; 0x9c; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,136))) *)
  0x48; 0x83; 0xdb; 0x00;  (* SBB (% rbx) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x8c; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (% rcx) (Memop Quadword (%% (rsp,144))) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x94; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,152))) *)
  0x48; 0x83; 0xda; 0x00;  (* SBB (% rdx) (Imm8 (word 0)) *)
  0x48; 0x0f; 0xba; 0xfa; 0x3f;
                           (* BTC (% rdx) (Imm8 (word 63)) *)
  0x48; 0x89; 0x44; 0x24; 0x60;
                           (* MOV (Memop Quadword (%% (rsp,96))) (% rax) *)
  0x48; 0x89; 0x5c; 0x24; 0x68;
                           (* MOV (Memop Quadword (%% (rsp,104))) (% rbx) *)
  0x48; 0x89; 0x4c; 0x24; 0x70;
                           (* MOV (Memop Quadword (%% (rsp,112))) (% rcx) *)
  0x48; 0x89; 0x54; 0x24; 0x78;
                           (* MOV (Memop Quadword (%% (rsp,120))) (% rdx) *)
  0x48; 0xb8; 0xa3; 0x78; 0x59; 0x13; 0xca; 0x4d; 0xeb; 0x75;
                           (* MOV (% rax) (Imm64 (word 8496970652267935907)) *)
  0x48; 0x89; 0x84; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,160))) (% rax) *)
  0x48; 0xb8; 0xab; 0xd8; 0x41; 0x41; 0x4d; 0x0a; 0x70; 0x00;
                           (* MOV (% rax) (Imm64 (word 31536524315187371)) *)
  0x48; 0x89; 0x84; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,168))) (% rax) *)
  0x48; 0xb8; 0x98; 0xe8; 0x79; 0x77; 0x79; 0x40; 0xc7; 0x8c;
                           (* MOV (% rax) (Imm64 (word 10144147576115030168)) *)
  0x48; 0x89; 0x84; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,176))) (% rax) *)
  0x48; 0xb8; 0x73; 0xfe; 0x6f; 0x2b; 0xee; 0x6c; 0x03; 0x52;
                           (* MOV (% rax) (Imm64 (word 5909686906226998899)) *)
  0x48; 0x89; 0x84; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,184))) (% rax) *)
  0x48; 0x8d; 0xbc; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rsp,128)) *)
  0x48; 0x8d; 0xb4; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* LEA (% rsi) (%% (rsp,160)) *)
  0x48; 0x8d; 0x94; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* LEA (% rdx) (%% (rsp,128)) *)
  0xe8; 0x91; 0x04; 0x00; 0x00;
                           (* CALL (Imm32 (word 1169)) *)
  0x48; 0x8b; 0x84; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,128))) *)
  0x48; 0x83; 0xc0; 0x01;  (* ADD (% rax) (Imm8 (word 1)) *)
  0x48; 0x8b; 0x9c; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,136))) *)
  0x48; 0x83; 0xd3; 0x00;  (* ADC (% rbx) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x8c; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (% rcx) (Memop Quadword (%% (rsp,144))) *)
  0x48; 0x83; 0xd1; 0x00;  (* ADC (% rcx) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x94; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,152))) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x48; 0x89; 0x84; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,128))) (% rax) *)
  0x48; 0x89; 0x9c; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,136))) (% rbx) *)
  0x48; 0x89; 0x8c; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,144))) (% rcx) *)
  0x48; 0x89; 0x94; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,152))) (% rdx) *)
  0x48; 0x8d; 0xbc; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rsp,160)) *)
  0x48; 0x8d; 0x74; 0x24; 0x60;
                           (* LEA (% rsi) (%% (rsp,96)) *)
  0x48; 0x8d; 0x94; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* LEA (% rdx) (%% (rsp,128)) *)
  0xe8; 0x27; 0x04; 0x00; 0x00;
                           (* CALL (Imm32 (word 1063)) *)
  0x48; 0x8d; 0x7c; 0x24; 0x40;
                           (* LEA (% rdi) (%% (rsp,64)) *)
  0x48; 0xc7; 0xc6; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% rsi) (Imm32 (word 1)) *)
  0x48; 0x8d; 0x94; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* LEA (% rdx) (%% (rsp,160)) *)
  0xe8; 0xc6; 0x05; 0x00; 0x00;
                           (* CALL (Imm32 (word 1478)) *)
  0x48; 0x8d; 0x7c; 0x24; 0x40;
                           (* LEA (% rdi) (%% (rsp,64)) *)
  0x48; 0x8d; 0x74; 0x24; 0x40;
                           (* LEA (% rsi) (%% (rsp,64)) *)
  0x48; 0x8d; 0x94; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* LEA (% rdx) (%% (rsp,160)) *)
  0xe8; 0xf7; 0x03; 0x00; 0x00;
                           (* CALL (Imm32 (word 1015)) *)
  0x48; 0x8d; 0x7c; 0x24; 0x20;
                           (* LEA (% rdi) (%% (rsp,32)) *)
  0x48; 0xc7; 0xc6; 0x02; 0x00; 0x00; 0x00;
                           (* MOV (% rsi) (Imm32 (word 2)) *)
  0x48; 0x8d; 0x54; 0x24; 0x40;
                           (* LEA (% rdx) (%% (rsp,64)) *)
  0xe8; 0x99; 0x05; 0x00; 0x00;
                           (* CALL (Imm32 (word 1433)) *)
  0x48; 0x8d; 0x7c; 0x24; 0x40;
                           (* LEA (% rdi) (%% (rsp,64)) *)
  0x48; 0x8d; 0x74; 0x24; 0x20;
                           (* LEA (% rsi) (%% (rsp,32)) *)
  0x48; 0x8d; 0x54; 0x24; 0x40;
                           (* LEA (% rdx) (%% (rsp,64)) *)
  0xe8; 0xcd; 0x03; 0x00; 0x00;
                           (* CALL (Imm32 (word 973)) *)
  0x48; 0x8d; 0x7c; 0x24; 0x20;
                           (* LEA (% rdi) (%% (rsp,32)) *)
  0x48; 0xc7; 0xc6; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% rsi) (Imm32 (word 1)) *)
  0x48; 0x8d; 0x54; 0x24; 0x40;
                           (* LEA (% rdx) (%% (rsp,64)) *)
  0xe8; 0x6f; 0x05; 0x00; 0x00;
                           (* CALL (Imm32 (word 1391)) *)
  0x48; 0x8d; 0xbc; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rsp,128)) *)
  0x48; 0x8d; 0x74; 0x24; 0x20;
                           (* LEA (% rsi) (%% (rsp,32)) *)
  0x48; 0x8d; 0x94; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* LEA (% rdx) (%% (rsp,160)) *)
  0xe8; 0x9d; 0x03; 0x00; 0x00;
                           (* CALL (Imm32 (word 925)) *)
  0x48; 0x8d; 0x7c; 0x24; 0x20;
                           (* LEA (% rdi) (%% (rsp,32)) *)
  0x48; 0xc7; 0xc6; 0x05; 0x00; 0x00; 0x00;
                           (* MOV (% rsi) (Imm32 (word 5)) *)
  0x48; 0x8d; 0x94; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* LEA (% rdx) (%% (rsp,128)) *)
  0xe8; 0x3c; 0x05; 0x00; 0x00;
                           (* CALL (Imm32 (word 1340)) *)
  0x48; 0x8d; 0x7c; 0x24; 0x40;
                           (* LEA (% rdi) (%% (rsp,64)) *)
  0x48; 0x8d; 0x74; 0x24; 0x20;
                           (* LEA (% rsi) (%% (rsp,32)) *)
  0x48; 0x8d; 0x94; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* LEA (% rdx) (%% (rsp,128)) *)
  0xe8; 0x6d; 0x03; 0x00; 0x00;
                           (* CALL (Imm32 (word 877)) *)
  0x48; 0x8d; 0x7c; 0x24; 0x20;
                           (* LEA (% rdi) (%% (rsp,32)) *)
  0x48; 0xc7; 0xc6; 0x0a; 0x00; 0x00; 0x00;
                           (* MOV (% rsi) (Imm32 (word 10)) *)
  0x48; 0x8d; 0x54; 0x24; 0x40;
                           (* LEA (% rdx) (%% (rsp,64)) *)
  0xe8; 0x0f; 0x05; 0x00; 0x00;
                           (* CALL (Imm32 (word 1295)) *)
  0x48; 0x8d; 0x7c; 0x24; 0x40;
                           (* LEA (% rdi) (%% (rsp,64)) *)
  0x48; 0x8d; 0x74; 0x24; 0x20;
                           (* LEA (% rsi) (%% (rsp,32)) *)
  0x48; 0x8d; 0x54; 0x24; 0x40;
                           (* LEA (% rdx) (%% (rsp,64)) *)
  0xe8; 0x43; 0x03; 0x00; 0x00;
                           (* CALL (Imm32 (word 835)) *)
  0x48; 0x8d; 0x7c; 0x24; 0x20;
                           (* LEA (% rdi) (%% (rsp,32)) *)
  0x48; 0xc7; 0xc6; 0x05; 0x00; 0x00; 0x00;
                           (* MOV (% rsi) (Imm32 (word 5)) *)
  0x48; 0x8d; 0x54; 0x24; 0x40;
                           (* LEA (% rdx) (%% (rsp,64)) *)
  0xe8; 0xe5; 0x04; 0x00; 0x00;
                           (* CALL (Imm32 (word 1253)) *)
  0x48; 0x8d; 0xbc; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rsp,128)) *)
  0x48; 0x8d; 0x74; 0x24; 0x20;
                           (* LEA (% rsi) (%% (rsp,32)) *)
  0x48; 0x8d; 0x94; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* LEA (% rdx) (%% (rsp,128)) *)
  0xe8; 0x13; 0x03; 0x00; 0x00;
                           (* CALL (Imm32 (word 787)) *)
  0x48; 0x8d; 0x7c; 0x24; 0x20;
                           (* LEA (% rdi) (%% (rsp,32)) *)
  0x48; 0xc7; 0xc6; 0x19; 0x00; 0x00; 0x00;
                           (* MOV (% rsi) (Imm32 (word 25)) *)
  0x48; 0x8d; 0x94; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* LEA (% rdx) (%% (rsp,128)) *)
  0xe8; 0xb2; 0x04; 0x00; 0x00;
                           (* CALL (Imm32 (word 1202)) *)
  0x48; 0x8d; 0x7c; 0x24; 0x40;
                           (* LEA (% rdi) (%% (rsp,64)) *)
  0x48; 0x8d; 0x74; 0x24; 0x20;
                           (* LEA (% rsi) (%% (rsp,32)) *)
  0x48; 0x8d; 0x94; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* LEA (% rdx) (%% (rsp,128)) *)
  0xe8; 0xe3; 0x02; 0x00; 0x00;
                           (* CALL (Imm32 (word 739)) *)
  0x48; 0x8d; 0x7c; 0x24; 0x20;
                           (* LEA (% rdi) (%% (rsp,32)) *)
  0x48; 0xc7; 0xc6; 0x32; 0x00; 0x00; 0x00;
                           (* MOV (% rsi) (Imm32 (word 50)) *)
  0x48; 0x8d; 0x54; 0x24; 0x40;
                           (* LEA (% rdx) (%% (rsp,64)) *)
  0xe8; 0x85; 0x04; 0x00; 0x00;
                           (* CALL (Imm32 (word 1157)) *)
  0x48; 0x8d; 0x7c; 0x24; 0x40;
                           (* LEA (% rdi) (%% (rsp,64)) *)
  0x48; 0x8d; 0x74; 0x24; 0x20;
                           (* LEA (% rsi) (%% (rsp,32)) *)
  0x48; 0x8d; 0x54; 0x24; 0x40;
                           (* LEA (% rdx) (%% (rsp,64)) *)
  0xe8; 0xb9; 0x02; 0x00; 0x00;
                           (* CALL (Imm32 (word 697)) *)
  0x48; 0x8d; 0x7c; 0x24; 0x20;
                           (* LEA (% rdi) (%% (rsp,32)) *)
  0x48; 0xc7; 0xc6; 0x19; 0x00; 0x00; 0x00;
                           (* MOV (% rsi) (Imm32 (word 25)) *)
  0x48; 0x8d; 0x54; 0x24; 0x40;
                           (* LEA (% rdx) (%% (rsp,64)) *)
  0xe8; 0x5b; 0x04; 0x00; 0x00;
                           (* CALL (Imm32 (word 1115)) *)
  0x48; 0x8d; 0xbc; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rsp,128)) *)
  0x48; 0x8d; 0x74; 0x24; 0x20;
                           (* LEA (% rsi) (%% (rsp,32)) *)
  0x48; 0x8d; 0x94; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* LEA (% rdx) (%% (rsp,128)) *)
  0xe8; 0x89; 0x02; 0x00; 0x00;
                           (* CALL (Imm32 (word 649)) *)
  0x48; 0x8d; 0x7c; 0x24; 0x20;
                           (* LEA (% rdi) (%% (rsp,32)) *)
  0x48; 0xc7; 0xc6; 0x7d; 0x00; 0x00; 0x00;
                           (* MOV (% rsi) (Imm32 (word 125)) *)
  0x48; 0x8d; 0x94; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* LEA (% rdx) (%% (rsp,128)) *)
  0xe8; 0x28; 0x04; 0x00; 0x00;
                           (* CALL (Imm32 (word 1064)) *)
  0x48; 0x8d; 0xbc; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rsp,128)) *)
  0x48; 0x8d; 0x74; 0x24; 0x20;
                           (* LEA (% rsi) (%% (rsp,32)) *)
  0x48; 0x8d; 0x94; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* LEA (% rdx) (%% (rsp,128)) *)
  0xe8; 0x56; 0x02; 0x00; 0x00;
                           (* CALL (Imm32 (word 598)) *)
  0x48; 0x8d; 0x7c; 0x24; 0x20;
                           (* LEA (% rdi) (%% (rsp,32)) *)
  0x48; 0xc7; 0xc6; 0x02; 0x00; 0x00; 0x00;
                           (* MOV (% rsi) (Imm32 (word 2)) *)
  0x48; 0x8d; 0x94; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* LEA (% rdx) (%% (rsp,128)) *)
  0xe8; 0xf5; 0x03; 0x00; 0x00;
                           (* CALL (Imm32 (word 1013)) *)
  0x48; 0x8d; 0x7c; 0x24; 0x20;
                           (* LEA (% rdi) (%% (rsp,32)) *)
  0x48; 0x8d; 0x74; 0x24; 0x20;
                           (* LEA (% rsi) (%% (rsp,32)) *)
  0x48; 0x8d; 0x94; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* LEA (% rdx) (%% (rsp,160)) *)
  0xe8; 0x26; 0x02; 0x00; 0x00;
                           (* CALL (Imm32 (word 550)) *)
  0x48; 0x8d; 0xbc; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rsp,128)) *)
  0x48; 0xc7; 0xc6; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% rsi) (Imm32 (word 1)) *)
  0x48; 0x8d; 0x54; 0x24; 0x20;
                           (* LEA (% rdx) (%% (rsp,32)) *)
  0xe8; 0xc5; 0x03; 0x00; 0x00;
                           (* CALL (Imm32 (word 965)) *)
  0x48; 0x8d; 0xbc; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rsp,128)) *)
  0x48; 0x8d; 0xb4; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* LEA (% rsi) (%% (rsp,128)) *)
  0x48; 0x8d; 0x94; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* LEA (% rdx) (%% (rsp,160)) *)
  0xe8; 0xf0; 0x01; 0x00; 0x00;
                           (* CALL (Imm32 (word 496)) *)
  0x48; 0x8d; 0x7c; 0x24; 0x20;
                           (* LEA (% rdi) (%% (rsp,32)) *)
  0x48; 0x8d; 0x74; 0x24; 0x60;
                           (* LEA (% rsi) (%% (rsp,96)) *)
  0x48; 0x8d; 0x54; 0x24; 0x20;
                           (* LEA (% rdx) (%% (rsp,32)) *)
  0xe8; 0xdc; 0x01; 0x00; 0x00;
                           (* CALL (Imm32 (word 476)) *)
  0x48; 0xb8; 0xb0; 0xa0; 0x0e; 0x4a; 0x27; 0x1b; 0xee; 0xc4;
                           (* MOV (% rax) (Imm64 (word 14190309331451158704)) *)
  0x48; 0x89; 0x44; 0x24; 0x40;
                           (* MOV (Memop Quadword (%% (rsp,64))) (% rax) *)
  0x48; 0xb8; 0x78; 0xe4; 0x2f; 0xad; 0x06; 0x18; 0x43; 0x2f;
                           (* MOV (% rax) (Imm64 (word 3405592160176694392)) *)
  0x48; 0x89; 0x44; 0x24; 0x48;
                           (* MOV (Memop Quadword (%% (rsp,72))) (% rax) *)
  0x48; 0xb8; 0xa7; 0xd7; 0xfb; 0x3d; 0x99; 0x00; 0x4d; 0x2b;
                           (* MOV (% rax) (Imm64 (word 3120150775007532967)) *)
  0x48; 0x89; 0x44; 0x24; 0x50;
                           (* MOV (Memop Quadword (%% (rsp,80))) (% rax) *)
  0x48; 0xb8; 0x0b; 0xdf; 0xc1; 0x4f; 0x80; 0x24; 0x83; 0x2b;
                           (* MOV (% rax) (Imm64 (word 3135389899092516619)) *)
  0x48; 0x89; 0x44; 0x24; 0x58;
                           (* MOV (Memop Quadword (%% (rsp,88))) (% rax) *)
  0x48; 0x8d; 0x7c; 0x24; 0x40;
                           (* LEA (% rdi) (%% (rsp,64)) *)
  0x48; 0x8d; 0x74; 0x24; 0x20;
                           (* LEA (% rsi) (%% (rsp,32)) *)
  0x48; 0x8d; 0x54; 0x24; 0x40;
                           (* LEA (% rdx) (%% (rsp,64)) *)
  0xe8; 0x8c; 0x01; 0x00; 0x00;
                           (* CALL (Imm32 (word 396)) *)
  0x4c; 0x8b; 0x84; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,128))) *)
  0x4c; 0x8b; 0x8c; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,136))) *)
  0x4c; 0x8b; 0x94; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (% r10) (Memop Quadword (%% (rsp,144))) *)
  0x4c; 0x8b; 0x9c; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (% r11) (Memop Quadword (%% (rsp,152))) *)
  0xb8; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 1)) *)
  0x48; 0xf7; 0xd0;        (* NOT (% rax) *)
  0x4c; 0x21; 0xc0;        (* AND (% rax) (% r8) *)
  0x4c; 0x09; 0xc8;        (* OR (% rax) (% r9) *)
  0x4c; 0x09; 0xd0;        (* OR (% rax) (% r10) *)
  0x4c; 0x09; 0xd8;        (* OR (% rax) (% r11) *)
  0x49; 0x83; 0xc0; 0x14;  (* ADD (% r8) (Imm8 (word 20)) *)
  0x49; 0xf7; 0xd1;        (* NOT (% r9) *)
  0x49; 0xf7; 0xd2;        (* NOT (% r10) *)
  0x49; 0x0f; 0xba; 0xeb; 0x3f;
                           (* BTS (% r11) (Imm8 (word 63)) *)
  0x49; 0x83; 0xc3; 0x01;  (* ADD (% r11) (Imm8 (word 1)) *)
  0x4d; 0x09; 0xc8;        (* OR (% r8) (% r9) *)
  0x4d; 0x09; 0xda;        (* OR (% r10) (% r11) *)
  0x4d; 0x09; 0xd0;        (* OR (% r8) (% r10) *)
  0x48; 0x85; 0xc0;        (* TEST (% rax) (% rax) *)
  0x4c; 0x8b; 0x64; 0x24; 0x20;
                           (* MOV (% r12) (Memop Quadword (%% (rsp,32))) *)
  0x48; 0x8b; 0x5c; 0x24; 0x40;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,64))) *)
  0x4c; 0x0f; 0x45; 0xe3;  (* CMOVNE (% r12) (% rbx) *)
  0x4c; 0x8b; 0x6c; 0x24; 0x28;
                           (* MOV (% r13) (Memop Quadword (%% (rsp,40))) *)
  0x48; 0x8b; 0x5c; 0x24; 0x48;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,72))) *)
  0x4c; 0x0f; 0x45; 0xeb;  (* CMOVNE (% r13) (% rbx) *)
  0x4c; 0x8b; 0x74; 0x24; 0x30;
                           (* MOV (% r14) (Memop Quadword (%% (rsp,48))) *)
  0x48; 0x8b; 0x5c; 0x24; 0x50;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,80))) *)
  0x4c; 0x0f; 0x45; 0xf3;  (* CMOVNE (% r14) (% rbx) *)
  0x4c; 0x8b; 0x7c; 0x24; 0x38;
                           (* MOV (% r15) (Memop Quadword (%% (rsp,56))) *)
  0x48; 0x8b; 0x5c; 0x24; 0x58;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,88))) *)
  0x4c; 0x0f; 0x45; 0xfb;  (* CMOVNE (% r15) (% rbx) *)
  0x4c; 0x89; 0x64; 0x24; 0x20;
                           (* MOV (Memop Quadword (%% (rsp,32))) (% r12) *)
  0x4c; 0x89; 0x6c; 0x24; 0x28;
                           (* MOV (Memop Quadword (%% (rsp,40))) (% r13) *)
  0x4c; 0x89; 0x74; 0x24; 0x30;
                           (* MOV (Memop Quadword (%% (rsp,48))) (% r14) *)
  0x4c; 0x89; 0x7c; 0x24; 0x38;
                           (* MOV (Memop Quadword (%% (rsp,56))) (% r15) *)
  0x4c; 0x0f; 0x44; 0xc0;  (* CMOVE (% r8) (% rax) *)
  0x49; 0xf7; 0xd8;        (* NEG (% r8) *)
  0x4d; 0x19; 0xc0;        (* SBB (% r8) (% r8) *)
  0x49; 0xf7; 0xd8;        (* NEG (% r8) *)
  0x4c; 0x09; 0x84; 0x24; 0xf0; 0x00; 0x00; 0x00;
                           (* OR (Memop Quadword (%% (rsp,240))) (% r8) *)
  0x4c; 0x8b; 0x44; 0x24; 0x20;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,32))) *)
  0x49; 0xc7; 0xc4; 0xed; 0xff; 0xff; 0xff;
                           (* MOV (% r12) (Imm32 (word 4294967277)) *)
  0x4d; 0x29; 0xc4;        (* SUB (% r12) (% r8) *)
  0x4c; 0x8b; 0x4c; 0x24; 0x28;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,40))) *)
  0x49; 0xc7; 0xc5; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r13) (Imm32 (word 4294967295)) *)
  0x4d; 0x19; 0xcd;        (* SBB (% r13) (% r9) *)
  0x4c; 0x8b; 0x54; 0x24; 0x30;
                           (* MOV (% r10) (Memop Quadword (%% (rsp,48))) *)
  0x49; 0xc7; 0xc6; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r14) (Imm32 (word 4294967295)) *)
  0x4d; 0x19; 0xd6;        (* SBB (% r14) (% r10) *)
  0x4c; 0x8b; 0x5c; 0x24; 0x38;
                           (* MOV (% r11) (Memop Quadword (%% (rsp,56))) *)
  0x49; 0xbf; 0xff; 0xff; 0xff; 0xff; 0xff; 0xff; 0xff; 0x7f;
                           (* MOV (% r15) (Imm64 (word 9223372036854775807)) *)
  0x4d; 0x19; 0xdf;        (* SBB (% r15) (% r11) *)
  0xb9; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% ecx) (Imm32 (word 1)) *)
  0x4c; 0x21; 0xc1;        (* AND (% rcx) (% r8) *)
  0x48; 0x33; 0x8c; 0x24; 0xe8; 0x00; 0x00; 0x00;
                           (* XOR (% rcx) (Memop Quadword (%% (rsp,232))) *)
  0x48; 0x8b; 0x94; 0x24; 0xf0; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,240))) *)
  0x48; 0x89; 0xd6;        (* MOV (% rsi) (% rdx) *)
  0x48; 0x09; 0xca;        (* OR (% rdx) (% rcx) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0x4c; 0x89; 0xc0;        (* MOV (% rax) (% r8) *)
  0x4c; 0x89; 0xcb;        (* MOV (% rbx) (% r9) *)
  0x4c; 0x09; 0xd0;        (* OR (% rax) (% r10) *)
  0x4c; 0x09; 0xdb;        (* OR (% rbx) (% r11) *)
  0x48; 0x09; 0xd8;        (* OR (% rax) (% rbx) *)
  0x48; 0x0f; 0x44; 0xcd;  (* CMOVE (% rcx) (% rbp) *)
  0x48; 0x0f; 0x45; 0xd6;  (* CMOVNE (% rdx) (% rsi) *)
  0x48; 0x85; 0xc9;        (* TEST (% rcx) (% rcx) *)
  0x4d; 0x0f; 0x45; 0xc4;  (* CMOVNE (% r8) (% r12) *)
  0x4d; 0x0f; 0x45; 0xcd;  (* CMOVNE (% r9) (% r13) *)
  0x4d; 0x0f; 0x45; 0xd6;  (* CMOVNE (% r10) (% r14) *)
  0x4d; 0x0f; 0x45; 0xdf;  (* CMOVNE (% r11) (% r15) *)
  0x48; 0x8b; 0xbc; 0x24; 0xe0; 0x00; 0x00; 0x00;
                           (* MOV (% rdi) (Memop Quadword (%% (rsp,224))) *)
  0x4c; 0x89; 0x07;        (* MOV (Memop Quadword (%% (rdi,0))) (% r8) *)
  0x4c; 0x89; 0x4f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% r9) *)
  0x4c; 0x89; 0x57; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r10) *)
  0x4c; 0x89; 0x5f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r11) *)
  0x48; 0x8b; 0x0c; 0x24;  (* MOV (% rcx) (Memop Quadword (%% (rsp,0))) *)
  0x48; 0x89; 0x4f; 0x20;  (* MOV (Memop Quadword (%% (rdi,32))) (% rcx) *)
  0x48; 0x8b; 0x4c; 0x24; 0x08;
                           (* MOV (% rcx) (Memop Quadword (%% (rsp,8))) *)
  0x48; 0x89; 0x4f; 0x28;  (* MOV (Memop Quadword (%% (rdi,40))) (% rcx) *)
  0x48; 0x8b; 0x4c; 0x24; 0x10;
                           (* MOV (% rcx) (Memop Quadword (%% (rsp,16))) *)
  0x48; 0x89; 0x4f; 0x30;  (* MOV (Memop Quadword (%% (rdi,48))) (% rcx) *)
  0x48; 0x8b; 0x4c; 0x24; 0x18;
                           (* MOV (% rcx) (Memop Quadword (%% (rsp,24))) *)
  0x48; 0x89; 0x4f; 0x38;  (* MOV (Memop Quadword (%% (rdi,56))) (% rcx) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0x81; 0xc4; 0x00; 0x01; 0x00; 0x00;
                           (* ADD (% rsp) (Imm32 (word 256)) *)
  0x41; 0x5f;              (* POP (% r15) *)
  0x41; 0x5e;              (* POP (% r14) *)
  0x41; 0x5d;              (* POP (% r13) *)
  0x41; 0x5c;              (* POP (% r12) *)
  0x5d;                    (* POP (% rbp) *)
  0x5b;                    (* POP (% rbx) *)
  0xc3;                    (* RET *)
  0x48; 0x89; 0xd1;        (* MOV (% rcx) (% rdx) *)
  0x48; 0x8b; 0x06;        (* MOV (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0xf7; 0x21;        (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,0))) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
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
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
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
  0x4d; 0x31; 0xf6;        (* XOR (% r14) (% r14) *)
  0x48; 0x8b; 0x46; 0x08;  (* MOV (% rax) (Memop Quadword (%% (rsi,8))) *)
  0x48; 0xf7; 0x61; 0x18;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,24))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x4d; 0x11; 0xf6;        (* ADC (% r14) (% r14) *)
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
  0x4d; 0x31; 0xff;        (* XOR (% r15) (% r15) *)
  0x48; 0x8b; 0x46; 0x10;  (* MOV (% rax) (Memop Quadword (%% (rsi,16))) *)
  0x48; 0xf7; 0x61; 0x18;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,24))) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x4d; 0x11; 0xff;        (* ADC (% r15) (% r15) *)
  0x48; 0x8b; 0x46; 0x18;  (* MOV (% rax) (Memop Quadword (%% (rsi,24))) *)
  0x48; 0xf7; 0x61; 0x10;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,16))) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x18;  (* MOV (% rax) (Memop Quadword (%% (rsi,24))) *)
  0x48; 0xf7; 0x61; 0x18;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,24))) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0xbe; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% esi) (Imm32 (word 38)) *)
  0x4c; 0x89; 0xe0;        (* MOV (% rax) (% r12) *)
  0x48; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% rsi) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xe8;        (* MOV (% rax) (% r13) *)
  0x48; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% rsi) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf0;        (* MOV (% rax) (% r14) *)
  0x48; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% rsi) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf8;        (* MOV (% rax) (% r15) *)
  0x48; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% rsi) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x48; 0x31; 0xc9;        (* XOR (% rcx) (% rcx) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x89; 0xd4;        (* MOV (% r12) (% rdx) *)
  0x49; 0x11; 0xcc;        (* ADC (% r12) (% rcx) *)
  0x4d; 0x0f; 0xa4; 0xdc; 0x01;
                           (* SHLD (% r12) (% r11) (Imm8 (word 1)) *)
  0x49; 0x8d; 0x44; 0x24; 0x01;
                           (* LEA (% rax) (%% (r12,1)) *)
  0xbe; 0x13; 0x00; 0x00; 0x00;
                           (* MOV (% esi) (Imm32 (word 19)) *)
  0x49; 0x0f; 0xba; 0xeb; 0x3f;
                           (* BTS (% r11) (Imm8 (word 63)) *)
  0x48; 0x0f; 0xaf; 0xc6;  (* IMUL (% rax) (% rsi) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xc9;        (* ADC (% r9) (% rcx) *)
  0x49; 0x11; 0xca;        (* ADC (% r10) (% rcx) *)
  0x49; 0x11; 0xcb;        (* ADC (% r11) (% rcx) *)
  0x48; 0x19; 0xc0;        (* SBB (% rax) (% rax) *)
  0x48; 0xf7; 0xd0;        (* NOT (% rax) *)
  0x48; 0x21; 0xf0;        (* AND (% rax) (% rsi) *)
  0x49; 0x29; 0xc0;        (* SUB (% r8) (% rax) *)
  0x49; 0x19; 0xc9;        (* SBB (% r9) (% rcx) *)
  0x49; 0x19; 0xca;        (* SBB (% r10) (% rcx) *)
  0x49; 0x19; 0xcb;        (* SBB (% r11) (% rcx) *)
  0x49; 0x0f; 0xba; 0xf3; 0x3f;
                           (* BTR (% r11) (Imm8 (word 63)) *)
  0x4c; 0x89; 0x07;        (* MOV (Memop Quadword (%% (rdi,0))) (% r8) *)
  0x4c; 0x89; 0x4f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% r9) *)
  0x4c; 0x89; 0x57; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r10) *)
  0x4c; 0x89; 0x5f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r11) *)
  0xc3;                    (* RET *)
  0x48; 0x8b; 0x02;        (* MOV (% rax) (Memop Quadword (%% (rdx,0))) *)
  0x48; 0x8b; 0x5a; 0x08;  (* MOV (% rbx) (Memop Quadword (%% (rdx,8))) *)
  0x48; 0x8b; 0x4a; 0x10;  (* MOV (% rcx) (Memop Quadword (%% (rdx,16))) *)
  0x48; 0x8b; 0x52; 0x18;  (* MOV (% rdx) (Memop Quadword (%% (rdx,24))) *)
  0x48; 0x89; 0x84; 0x24; 0xc8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,200))) (% rax) *)
  0x48; 0x89; 0x9c; 0x24; 0xd0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,208))) (% rbx) *)
  0x48; 0x89; 0x8c; 0x24; 0xd8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,216))) (% rcx) *)
  0x48; 0x89; 0x94; 0x24; 0xe0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,224))) (% rdx) *)
  0x48; 0x8b; 0x84; 0x24; 0xc8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,200))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x48; 0x8b; 0x84; 0x24; 0xc8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,200))) *)
  0x48; 0xf7; 0xa4; 0x24; 0xd0; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,208))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xe4;        (* XOR (% r12) (% r12) *)
  0x48; 0x8b; 0x84; 0x24; 0xd0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,208))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x84; 0x24; 0xc8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,200))) *)
  0x48; 0xf7; 0xa4; 0x24; 0xd8; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,216))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xed;        (* XOR (% r13) (% r13) *)
  0x48; 0x8b; 0x84; 0x24; 0xc8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,200))) *)
  0x48; 0xf7; 0xa4; 0x24; 0xe0; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,224))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x84; 0x24; 0xd0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,208))) *)
  0x48; 0xf7; 0xa4; 0x24; 0xd8; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,216))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xf6;        (* XOR (% r14) (% r14) *)
  0x48; 0x8b; 0x84; 0x24; 0xd0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,208))) *)
  0x48; 0xf7; 0xa4; 0x24; 0xe0; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,224))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x84; 0x24; 0xd8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,216))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xff;        (* XOR (% r15) (% r15) *)
  0x48; 0x8b; 0x84; 0x24; 0xd8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,216))) *)
  0x48; 0xf7; 0xa4; 0x24; 0xe0; 0x00; 0x00; 0x00;
                           (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rsp,224))) *)
  0x48; 0x01; 0xc0;        (* ADD (% rax) (% rax) *)
  0x48; 0x11; 0xd2;        (* ADC (% rdx) (% rdx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x84; 0x24; 0xe0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,224))) *)
  0x48; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% rax) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0xbb; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% ebx) (Imm32 (word 38)) *)
  0x4c; 0x89; 0xe0;        (* MOV (% rax) (% r12) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xe8;        (* MOV (% rax) (% r13) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf0;        (* MOV (% rax) (% r14) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x89; 0xf8;        (* MOV (% rax) (% r15) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x29; 0xca;        (* SUB (% rdx) (% rcx) *)
  0x48; 0x31; 0xc9;        (* XOR (% rcx) (% rcx) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x89; 0xd4;        (* MOV (% r12) (% rdx) *)
  0x49; 0x11; 0xcc;        (* ADC (% r12) (% rcx) *)
  0x4d; 0x0f; 0xa4; 0xdc; 0x01;
                           (* SHLD (% r12) (% r11) (Imm8 (word 1)) *)
  0x49; 0x0f; 0xba; 0xf3; 0x3f;
                           (* BTR (% r11) (Imm8 (word 63)) *)
  0xba; 0x13; 0x00; 0x00; 0x00;
                           (* MOV (% edx) (Imm32 (word 19)) *)
  0x49; 0x0f; 0xaf; 0xd4;  (* IMUL (% rdx) (% r12) *)
  0x49; 0x01; 0xd0;        (* ADD (% r8) (% rdx) *)
  0x49; 0x11; 0xc9;        (* ADC (% r9) (% rcx) *)
  0x49; 0x11; 0xca;        (* ADC (% r10) (% rcx) *)
  0x49; 0x11; 0xcb;        (* ADC (% r11) (% rcx) *)
  0x4c; 0x89; 0x84; 0x24; 0xc8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,200))) (% r8) *)
  0x4c; 0x89; 0x8c; 0x24; 0xd0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,208))) (% r9) *)
  0x4c; 0x89; 0x94; 0x24; 0xd8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,216))) (% r10) *)
  0x4c; 0x89; 0x9c; 0x24; 0xe0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,224))) (% r11) *)
  0x48; 0xff; 0xce;        (* DEC (% rsi) *)
  0x0f; 0x85; 0x35; 0xfe; 0xff; 0xff;
                           (* JNE (Imm32 (word 4294966837)) *)
  0xb8; 0x13; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 19)) *)
  0x31; 0xdb;              (* XOR (% ebx) (% ebx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x31; 0xd2;              (* XOR (% edx) (% edx) *)
  0x4c; 0x01; 0xc0;        (* ADD (% rax) (% r8) *)
  0x4c; 0x11; 0xcb;        (* ADC (% rbx) (% r9) *)
  0x4c; 0x11; 0xd1;        (* ADC (% rcx) (% r10) *)
  0x4c; 0x11; 0xda;        (* ADC (% rdx) (% r11) *)
  0x49; 0x0f; 0x49; 0xc0;  (* CMOVNS (% rax) (% r8) *)
  0x49; 0x0f; 0x49; 0xd9;  (* CMOVNS (% rbx) (% r9) *)
  0x49; 0x0f; 0x49; 0xca;  (* CMOVNS (% rcx) (% r10) *)
  0x49; 0x0f; 0x49; 0xd3;  (* CMOVNS (% rdx) (% r11) *)
  0x48; 0x0f; 0xba; 0xf2; 0x3f;
                           (* BTR (% rdx) (Imm8 (word 63)) *)
  0x48; 0x89; 0x07;        (* MOV (Memop Quadword (%% (rdi,0))) (% rax) *)
  0x48; 0x89; 0x5f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% rbx) *)
  0x48; 0x89; 0x4f; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% rcx) *)
  0x48; 0x89; 0x57; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% rdx) *)
  0xc3                     (* RET *)
];;

let edwards25519_decode_alt_tmc = define_trimmed "edwards25519_decode_alt_tmc" edwards25519_decode_alt_mc;;

let EDWARDS25519_DECODE_ALT_EXEC = X86_MK_EXEC_RULE edwards25519_decode_alt_tmc;;

(* ------------------------------------------------------------------------- *)
(* Local subroutine correctness.                                             *)
(* ------------------------------------------------------------------------- *)

let p25519redlemma = prove
 (`!n. n <= (2 EXP 64 - 1) * (p_25519 - 1)
       ==> let q = n DIV 2 EXP 255 + 1 in
           q < 2 EXP 64 /\
           q * p_25519 <= n + p_25519 /\
           n < q * p_25519 + p_25519`,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[p_25519] THEN ARITH_TAC);;

let LOCAL_MUL_P25519_CORRECT = time prove
 (`!z x y m n pc.
        nonoverlapping (word pc,0x9ae) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) edwards25519_decode_alt_tmc /\
                  read RIP s = word(pc + 0x5c0) /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,4) s = m /\
                  bignum_from_memory (y,4) s = n)
             (\s. read RIP s = word (pc + 0x777) /\
                  bignum_from_memory (z,4) s = (m * n) MOD p_25519)
        (MAYCHANGE [RIP; RSI; RAX; RBX; RCX; RDX;
                    R8; R9; R10; R11; R12; R13; R14; R15] ,,
           MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
           MAYCHANGE SOME_FLAGS)`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `y:int64`; `m:num`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_LDIGITIZE_TAC "m_" `read (memory :> bytes (x,8 * 4)) s0` THEN
  BIGNUM_LDIGITIZE_TAC "n_" `read (memory :> bytes (y,8 * 4)) s0` THEN

  (*** The initial multiplication block, similar to bignum_mul_4_8_alt ***)

  X86_ACCSTEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (1--84) (1--84) THEN
  MAP_EVERY ABBREV_TAC
   [`l = bignum_of_wordlist[mullo_s3; sum_s14; sum_s30; sum_s51]`;
    `h = bignum_of_wordlist[sum_s67; sum_s78; sum_s83; sum_s84]`] THEN
  SUBGOAL_THEN `2 EXP 256 * h + l = m * n` (SUBST1_TAC o SYM) THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"; "m"; "n"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** The initial modular reduction of the high part ***)

  SUBGOAL_THEN
    `(2 EXP 256 * h + l) MOD p_25519 = (38 * h + l) MOD p_25519`
  SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN
    ONCE_REWRITE_TAC[GSYM MOD_MULT_LMOD] THEN
    REWRITE_TAC[p_25519] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN

  (*** Instantiate the quotient approximation lemma ***)

  MP_TAC(SPEC `38 * h + l` p25519redlemma) THEN ANTS_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"] THEN REWRITE_TAC[p_25519] THEN
    CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC] THEN

  (*** Reduction from 8 digits to 5 digits ***)

  MAP_EVERY (fun n ->
    X86_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC [n] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
     `word_sub x (word_neg y):int64 = word_add x y`]) THEN
    TRY(ACCUMULATE_ARITH_TAC("s"^string_of_int n)))
   (85--109) THEN
  ABBREV_TAC
   `ca =
    bignum_of_wordlist[sum_s88; sum_s94; sum_s100; sum_s107; sum_s109]` THEN
  SUBGOAL_THEN `(38 * h + l) DIV 2 EXP 255 + 1 <= 78`
  ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `a + 1 <= b <=> a < b`] THEN
    SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN CONV_TAC NUM_REDUCE_CONV THEN
    MAP_EVERY EXPAND_TAC ["h"; "l"] THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `38 * h + l = ca` SUBST_ALL_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"; "ca"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Quotient estimate computation ***)

  X86_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (110--114) THEN
  ABBREV_TAC `t = bignum_of_wordlist
   [sum_s88; sum_s94; sum_s100;
    word_or sum_s107 (word 9223372036854775808)]` THEN
  SUBGOAL_THEN `&ca = &t + &2 pow 255 * (&(ca DIV 2 EXP 255) - &1)`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ARITH
     `c = t + e * (d - &1):real <=> c + e = t + e * d`] THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES; ARITH_RULE
    `c + d = t + 2 EXP 255 * c DIV 2 EXP 255 <=> c MOD 2 EXP 255 + d = t`] THEN
    MAP_EVERY EXPAND_TAC ["ca"; "t"] THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(4,1)] THEN
    REWRITE_TAC[MOD_MULT_ADD; ARITH_RULE
     `2 EXP 256 * n = 2 EXP 255 * 2 * n`] THEN
    REWRITE_TAC[MOD_MULT_MOD; ARITH_RULE
     `2 EXP 255 = 2 EXP 192 * 2 EXP 63`] THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(3,1)] THEN
    SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
    SUBGOAL_THEN `bignum_of_wordlist [sum_s88; sum_s94; sum_s100] < 2 EXP 192`
    (fun th -> SIMP_TAC[th; MOD_LT; DIV_LT]) THENL
     [BOUNDER_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[ADD_CLAUSES; ARITH_RULE
     `(e * x + a) + e * y:num = a + e * z <=> e * (x + y) = e * z`] THEN
    AP_TERM_TAC THEN REWRITE_TAC[BIGNUM_OF_WORDLIST_SING] THEN
    REWRITE_TAC[GSYM VAL_WORD_AND_MASK_WORD] THEN
    ONCE_REWRITE_TAC[WORD_BITWISE_RULE
     `word_or x m = word_or (word_and x (word_not m)) m`] THEN
    SIMP_TAC[VAL_WORD_OR_DISJOINT; WORD_BITWISE_RULE
     `word_and (word_and x (word_not m)) m = word 0`] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV);
    ALL_TAC] THEN
  ABBREV_TAC `hw:int64 = word_subword
    ((word_join:int64->int64->int128) sum_s109 sum_s107) (63,64)` THEN
  SUBGOAL_THEN `ca DIV 2 EXP 255 = val(hw:int64)` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `ca DIV 2 EXP 255 + 1 <= 78` THEN REWRITE_TAC[ARITH_RULE
     `n DIV 2 EXP 255 = n DIV 2 EXP 192 DIV 2 EXP 63`] THEN
    EXPAND_TAC "ca" THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    DISCH_THEN(fun th ->
     MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 64` THEN
     CONJ_TAC THENL [MP_TAC th THEN ARITH_TAC; REWRITE_TAC[VAL_BOUND_64]]) THEN
    EXPAND_TAC "hw" THEN
    SIMP_TAC[VAL_WORD_SUBWORD_JOIN; DIMINDEX_64; ARITH_LE; ARITH_LT] THEN
    REWRITE_TAC[bignum_of_wordlist; MULT_CLAUSES; ADD_CLAUSES] THEN
    REWRITE_TAC[CONG; ADD_SYM; MULT_SYM] THEN
    CONV_TAC MOD_DOWN_CONV THEN REFL_TAC;
    ALL_TAC] THEN

  REABBREV_TAC `qm = read RAX s114` THEN
  SUBGOAL_THEN `&(val(qm:int64)):real = &19 * (&(val(hw:int64)) + &1)`
  ASSUME_TAC THENL
   [EXPAND_TAC "qm" THEN
    REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_MUL; DIMINDEX_64] THEN
    REWRITE_TAC[ REAL_OF_NUM_CLAUSES] THEN CONV_TAC MOD_DOWN_CONV THEN
    CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[MULT_SYM] THEN
    MATCH_MP_TAC MOD_LT THEN
    UNDISCH_TAC `val(hw:int64) + 1 <= 78` THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** The rest of the computation ***)

  X86_ACCSTEPS_TAC EDWARDS25519_DECODE_ALT_EXEC
   [115;116;117;118;122;123;124;125] (115--130) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_UNIQ_BALANCED_REAL THEN
  MAP_EVERY EXISTS_TAC [`val(hw:int64) + 1`; `255`] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [REWRITE_TAC[p_25519] THEN ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN

  (*** Comparison computation and then the rest is easy ***)

  SUBGOAL_THEN `ca < (val(hw:int64) + 1) * p_25519 <=> ~carry_s118`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN
    EXISTS_TAC `256` THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "t" THEN
    REWRITE_TAC[p_25519; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[REAL_BITVAL_NOT] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[] THEN BOUNDER_TAC[];
    REWRITE_TAC[REAL_BITVAL_NOT] THEN EXPAND_TAC "t" THEN
    REWRITE_TAC[p_25519; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_UNMASK_64]) THEN
    REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 63 - 1`)] THEN
    REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_MOD] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_CASES_TAC `carry_s118:bool` THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV THEN
    REAL_INTEGER_TAC]);;

let LOCAL_MUL_TAC =
  X86_SUBROUTINE_SIM_TAC
   (edwards25519_decode_alt_tmc,EDWARDS25519_DECODE_ALT_EXEC,
    0x0,edwards25519_decode_alt_tmc,LOCAL_MUL_P25519_CORRECT)
  [`read RDI s`; `read RSI s`; `read RDX s`;
   `read(memory :> bytes(read RSI s,8 * 4)) s`;
   `read(memory :> bytes(read RDX s,8 * 4)) s`;
   `pc:num`];;

let LOCAL_NSQR_P25519_CORRECT = time prove
 (`!z k x n pc stackpointer.
        nonoverlapping (word pc,0x9ae) (z,8 * 4) /\
        nonoverlapping (stackpointer,264) (word pc,0x9ae) /\
        1 <= val k /\ val k <= 1000
        ==> ensures x86
             (\s. bytes_loaded s (word pc) edwards25519_decode_alt_tmc /\
                  read RIP s = word(pc + 0x778) /\
                  read RSP s = stackpointer /\
                  C_ARGUMENTS [z; k; x] s /\
                  bignum_from_memory (x,4) s = n)
             (\s. read RIP s = word (pc + 0x9ad) /\
                  bignum_from_memory (z,4) s =
                  (n EXP (2 EXP val k)) MOD p_25519)
             (MAYCHANGE [RIP; RSI; RAX; RBX; RCX; RDX; RBP;
                    R8; R9; R10; R11; R12; R13; R14; R15] ,,
              MAYCHANGE [memory :> bytes(z,8 * 4);
                memory :> bytes(word_add stackpointer (word 200),8*4)] ,,
              MAYCHANGE SOME_FLAGS)`,
  X_GEN_TAC `z:int64` THEN W64_GEN_TAC `k:num` THEN
  MAP_EVERY X_GEN_TAC [`x:int64`; `n:num`; `pc:num`; `stackpointer:int64`] THEN
  REWRITE_TAC[C_ARGUMENTS; ALL; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Top-level squaring loop ***)

  ENSURES_WHILE_PUP_TAC `k:num` `pc + 0x7a7` `pc + 0x96c`
   `\i s. (read RSP s = stackpointer /\
           read RDI s = z /\
           read RSI s = word(k - i) /\
           (read (memory :> bytes(word_add stackpointer (word 200),8 * 4)) s ==
            n EXP (2 EXP i)) (mod p_25519) /\
           (1 <= i
            ==> read(memory :> bytes(word_add stackpointer (word 200),8 * 4)) s
                < 2 * p_25519 /\
                bignum_of_wordlist
                 [read R8 s; read R9 s; read R10 s; read R11 s] =
                read (memory :> bytes(word_add stackpointer (word 200),8 * 4))
                     s)) /\
          (read ZF s <=> i = k)` THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[LE_1];

    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    BIGNUM_LDIGITIZE_TAC "x_" `read (memory :> bytes (x,8 * 4)) s0` THEN
    X86_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (1--8) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[EXP; EXP_1; CONG_REFL; SUB_0] THEN CONV_TAC NUM_REDUCE_CONV;

    ALL_TAC; (*** Main loop invariant ***)

    REPEAT STRIP_TAC THEN X86_SIM_TAC EDWARDS25519_DECODE_ALT_EXEC [1];

    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    BIGNUM_LDIGITIZE_TAC "x_"
     `read (memory :> bytes(word_add stackpointer (word 200),8 * 4)) s0` THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [BIGNUM_OF_WORDLIST_EQ]) THEN
    ASM_REWRITE_TAC[BIGNUM_OF_WORDLIST_EQ] THEN STRIP_TAC THEN
    X86_ACCSTEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (6--9) (1--18) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

    CONV_TAC(LAND_CONV BIGNUM_LEXPAND_CONV) THEN
    ASM_REWRITE_TAC[] THEN DISCARD_STATE_TAC "s18" THEN
    REWRITE_TAC[INT_OF_NUM_REM; INT_OF_NUM_CLAUSES] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
    ABBREV_TAC `m = bignum_of_wordlist [x_0; x_1; x_2; x_3]` THEN
    MAP_EVERY EXISTS_TAC
     [`255`;
      `if m < p_25519 then &m:real else &m - &p_25519`] THEN
    REPEAT CONJ_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
      REWRITE_TAC[p_25519] THEN ARITH_TAC;
      REWRITE_TAC[p_25519] THEN ARITH_TAC;
      ALL_TAC;
      FIRST_X_ASSUM(SUBST1_TAC o SYM o GEN_REWRITE_RULE I [CONG]) THEN
      ASM_SIMP_TAC[MOD_CASES] THEN
      SIMP_TAC[REAL_OF_NUM_SUB; GSYM NOT_LT] THEN MESON_TAC[]] THEN
    REWRITE_TAC[GSYM MSB_IVAL; MSB_VAL] THEN
    REWRITE_TAC[DIMINDEX_64; ARITH_RULE `64 - 1 = 63`] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [REAL_OF_NUM_ADD]) THEN
    GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [REAL_OF_NUM_CLAUSES] THEN
    DISCH_THEN(MP_TAC o AP_TERM `\x. x MOD 2 EXP 64`) THEN
    REWRITE_TAC[MOD_MULT_ADD; VAL_WORD_ADD; VAL_WORD] THEN
    CONV_TAC MOD_DOWN_CONV THEN
    REWRITE_TAC[GSYM DIMINDEX_64; VAL_MOD_REFL] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN
     `(m < p_25519 <=> m + 19 < 2 EXP 255) /\
      (&m - &p_25519:real = &(m + 19) - &2 pow 255)`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_25519] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `2 EXP 256 * bitval carry_s9 +
      bignum_of_wordlist [sum_s6; sum_s7; sum_s8; sum_s9] = m + 19`
    MP_TAC THENL
     [EXPAND_TAC "m" THEN
      REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
     `2 EXP 256 * c + s = mm
      ==> mm < 2 EXP 256 /\ (2 EXP 256 * c < 2 EXP 256 * 1 ==> c = 0)
          ==> mm = s`)) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `m < 2 * p_25519` THEN
      REWRITE_TAC[p_25519; LT_MULT_LCANCEL] THEN ARITH_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[NOT_LE; ARITH_RULE
     `x < 2 EXP 255 <=> x DIV 2 EXP 192 < 2 EXP 63`] THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "m" THEN
    REWRITE_TAC[GSYM(NUM_REDUCE_CONV `2 EXP 63 - 1`)] THEN
    REWRITE_TAC[bignum_of_wordlist; VAL_WORD_AND_MASK_WORD] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_MOD] THEN
    REAL_INTEGER_TAC] THEN

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
  REWRITE_TAC[EXP_ADD; GSYM EXP_EXP; EXP_1] THEN
  SPEC_TAC(`n EXP (2 EXP i)`,`n':num`) THEN GEN_TAC THEN

  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_LDIGITIZE_TAC "n_"
   `read (memory :> bytes (word_add stackpointer (word 200),8 * 4)) s0` THEN
  FIRST_X_ASSUM(K ALL_TAC o check (is_imp o concl)) THEN
  ABBREV_TAC `n = bignum_of_wordlist [n_0; n_1; n_2; n_3]` THEN
   FIRST_ASSUM(fun th ->
     REWRITE_TAC[MATCH_MP
      (NUMBER_RULE `!n a p. (n == a) (mod p)
                            ==> !x. (x == a EXP 2) (mod p) <=>
                                    (x == n EXP 2) (mod p)`) th]) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (free_in `n':num` o concl))) THEN

  (*** The initial squaring block, very similar to bignum_sqr_4_8_alt ***)

  X86_ACCSTEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (1--72) (1--72) THEN
  MAP_EVERY ABBREV_TAC
   [`l = bignum_of_wordlist[mullo_s2; sum_s12; sum_s26; sum_s43]`;
    `h = bignum_of_wordlist[sum_s57; sum_s66; sum_s71; sum_s72]`] THEN
  SUBGOAL_THEN `2 EXP 256 * h + l = n EXP 2` (SUBST1_TAC o SYM) THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"; "n"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** The initial modular reduction of the high part ***)

  REWRITE_TAC[CONG] THEN
  SUBGOAL_THEN
    `(2 EXP 256 * h + l) MOD p_25519 = (38 * h + l) MOD p_25519`
  SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN
    ONCE_REWRITE_TAC[GSYM MOD_MULT_LMOD] THEN
    REWRITE_TAC[p_25519] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN

  (*** Instantiate the quotient approximation lemma ***)

  MP_TAC(SPEC `38 * h + l` p25519redlemma) THEN ANTS_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"] THEN REWRITE_TAC[p_25519] THEN
    CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC] THEN

  (*** Reduction from 8 digits to 5 digits ***)

  MAP_EVERY (fun n ->
    X86_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC [n] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
     `word_sub x (word_neg y):int64 = word_add x y`]) THEN
    TRY(ACCUMULATE_ARITH_TAC("s"^string_of_int n)))
   (73--97) THEN
  ABBREV_TAC
   `ca =
    bignum_of_wordlist[sum_s76; sum_s82; sum_s88; sum_s95; sum_s97]` THEN
  SUBGOAL_THEN `(38 * h + l) DIV 2 EXP 255 + 1 <= 78`
  ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `a + 1 <= b <=> a < b`] THEN
    SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN CONV_TAC NUM_REDUCE_CONV THEN
    MAP_EVERY EXPAND_TAC ["h"; "l"] THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `38 * h + l = ca` SUBST_ALL_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"; "ca"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Quotient estimate computation ***)

  X86_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (98--101) THEN
  ABBREV_TAC `hw:int64 = word_subword
    ((word_join:int64->int64->int128) sum_s97 sum_s95) (63,64)` THEN
  SUBGOAL_THEN `ca DIV 2 EXP 255 = val(hw:int64)`
   (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th) THENL
   [UNDISCH_TAC `ca DIV 2 EXP 255 + 1 <= 78` THEN REWRITE_TAC[ARITH_RULE
     `n DIV 2 EXP 255 = n DIV 2 EXP 192 DIV 2 EXP 63`] THEN
    EXPAND_TAC "ca" THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    DISCH_THEN(fun th ->
     MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 64` THEN
     CONJ_TAC THENL [MP_TAC th THEN ARITH_TAC; REWRITE_TAC[VAL_BOUND_64]]) THEN
    EXPAND_TAC "hw" THEN
    SIMP_TAC[VAL_WORD_SUBWORD_JOIN; DIMINDEX_64; ARITH_LE; ARITH_LT] THEN
    REWRITE_TAC[bignum_of_wordlist; MULT_CLAUSES; ADD_CLAUSES] THEN
    REWRITE_TAC[CONG; ADD_SYM; MULT_SYM] THEN
    CONV_TAC MOD_DOWN_CONV THEN REFL_TAC;
    ALL_TAC] THEN

  ABBREV_TAC `qm:int64 = word_mul (word 19:int64) hw` THEN
  SUBGOAL_THEN `&(val(qm:int64)):real = &19 * &(val(hw:int64))`
  ASSUME_TAC THENL
   [EXPAND_TAC "qm" THEN
    REWRITE_TAC[VAL_WORD_MUL; DIMINDEX_64; REAL_OF_NUM_CLAUSES] THEN
    CONV_TAC WORD_REDUCE_CONV THEN MATCH_MP_TAC MOD_LT THEN
    UNDISCH_TAC `val(hw:int64) + 1 <= 78` THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** The rest of the computation ***)

  X86_ACCSTEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (102--105) (102--110) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `k - (i + 1) = k - i - 1`] THEN
    GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
    ASM_SIMP_TAC[ARITH_RULE `i < k ==> 1 <= k - i`];
    DISCH_THEN SUBST1_TAC] THEN
  VAL_INT64_TAC `k - (i + 1)` THEN
  ASM_SIMP_TAC[SUB_EQ_0; ARITH_RULE
   `i < k ==> (k <= i + 1 <=> i + 1 = k)`] THEN
  REWRITE_TAC[ARITH_RULE `1 <= i + 1`] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM CONG; num_congruent] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
  MATCH_MP_TAC(MESON[]
   `!q. (ca - q * p == ca) (mod p) /\ ca - q * p < p2 /\ x = ca - q * p
    ==> (x == ca) (mod p) /\ x:int < p2`) THEN
  EXISTS_TAC `&(val(hw:int64)):int` THEN
  CONJ_TAC THENL [CONV_TAC INTEGER_RULE; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [REWRITE_TAC[INT_ARITH `x - y:int < z <=> x < y + z`] THEN
    REWRITE_TAC[INT_ARITH `h * p + &2 * p:int = (h + &1) * p + p`] THEN
    ASM_REWRITE_TAC[INT_OF_NUM_CLAUSES];
    DISCH_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC INT_CONG_IMP_EQ THEN EXISTS_TAC `(&2:int) pow 256` THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INT_ARITH
     `y:int < p ==> &0 <= y /\ &0 <= p /\ p < e /\ &0 <= x /\ x < e
         ==> abs(x - y) < e`)) THEN
    ASM_REWRITE_TAC[INT_SUB_LE; INT_OF_NUM_CLAUSES; LE_0] THEN
    ONCE_REWRITE_TAC[ARITH_RULE
     `h * p <= ca <=> (h + 1) * p <= ca + p`] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[p_25519] THEN CONV_TAC NUM_REDUCE_CONV THEN
    BOUNDER_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[INTEGER_RULE
   `(x:int == y - z) (mod p) <=> (x + z == y) (mod p)`] THEN
  REWRITE_TAC[INT_OF_NUM_CLAUSES; GSYM num_congruent] THEN
  REWRITE_TAC[REAL_CONGRUENCE; p_25519] THEN CONV_TAC NUM_REDUCE_CONV THEN
  EXPAND_TAC "ca" THEN
  REWRITE_TAC[p_25519; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
  ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 63 - 1`)] THEN
  REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
  UNDISCH_THEN `ca DIV 2 EXP 255 = val(hw:int64)` (SUBST1_TAC o SYM) THEN
  EXPAND_TAC "ca" THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
  REWRITE_TAC[bignum_of_wordlist; ARITH_RULE
   `(l + 2 EXP 64 * h) DIV 2 EXP 63 = l DIV 2 EXP 63 + 2 * h`] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_DIV] THEN
  REAL_INTEGER_TAC);;

let LOCAL_NSQR_TAC =
  X86_SUBROUTINE_SIM_TAC
   (edwards25519_decode_alt_tmc,EDWARDS25519_DECODE_ALT_EXEC,
    0x0,edwards25519_decode_alt_tmc,LOCAL_NSQR_P25519_CORRECT)
  [`read RDI s`; `read RSI s`; `read RDX s`;
   `read(memory :> bytes(read RDX s,8 * 4)) s`;
   `pc:num`; `stackpointer:int64`];;

(* ------------------------------------------------------------------------- *)
(* Definitions and lemmas to express specification and support proof.        *)
(* ------------------------------------------------------------------------- *)

let ed25519_encode = new_definition
  `ed25519_encode (X,Y) =
        let x = num_of_int(X rem &p_25519)
        and y = num_of_int(Y rem &p_25519) in
        2 EXP 255 * x MOD 2 + y`;;

let ed25519_validencode = new_definition
  `ed25519_validencode n <=>
        ?P. P IN group_carrier edwards25519_group /\
            ed25519_encode P = n`;;

let ed25519_decode = new_definition
 `ed25519_decode n =
        @P. P IN group_carrier edwards25519_group /\
            ed25519_encode P = n`;;

let EDWARDS25519_NONZERO_DENOMINATORS = prove
 (`!y. coprime(&1 + &d_25519 * y pow 2,&p_25519)`,
  ONCE_REWRITE_TAC[GSYM INT_POW2_ABS] THEN
  REWRITE_TAC[GSYM INT_FORALL_ABS; INT_OF_NUM_CLAUSES; GSYM num_coprime] THEN
  X_GEN_TAC `y:num` THEN ONCE_REWRITE_TAC[COPRIME_SYM] THEN
  SIMP_TAC[PRIME_COPRIME_EQ; PRIME_P25519] THEN
  DISCH_THEN(MP_TAC o SPEC `inverse_mod p_25519 d_25519` o
    MATCH_MP (NUMBER_RULE
     `p divides (1 + d * y)
      ==> !d'. (d * d' == 1) (mod p) ==> p divides (y + d')`)) THEN
  REWRITE_TAC[INVERSE_MOD_RMUL_EQ] THEN REWRITE_TAC[p_25519; d_25519] THEN
  CONV_TAC(ONCE_DEPTH_CONV COPRIME_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV INVERSE_MOD_CONV) THEN
  REWRITE_TAC[num_divides; GSYM INT_OF_NUM_CLAUSES] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (INTEGER_RULE
   `p divides y + z ==> (y:int == --z) (mod p)`)) THEN
  REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[GSYM INT_CONG_RREM] THEN CONV_TAC INT_REDUCE_CONV THEN
  REWRITE_TAC[INT_OF_NUM_CLAUSES; GSYM num_congruent] THEN
  DISCH_THEN(MP_TAC o SIMPLE_EXISTS `y:num`) THEN
  REWRITE_TAC[GSYM p_25519] THEN SIMP_TAC[EULER_CRITERION; PRIME_P25519] THEN
  REWRITE_TAC[p_25519; d_25519] THEN
  CONV_TAC(DEPTH_CONV(NUM_SUB_CONV ORELSEC DIVIDES_CONV)) THEN
  REWRITE_TAC[CONG] THEN
  CONV_TAC(RAND_CONV(RAND_CONV NUM_MOD_CONV)) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_DIV_CONV) THEN
  CONV_TAC(RAND_CONV(LAND_CONV EXP_MOD_CONV)) THEN
  ARITH_TAC);;

let IN_GROUP_CARRIER_EDWARDS25519 = prove
 (`!x y. (x,y) IN group_carrier edwards25519_group <=>
         &0 <= x /\ x < &p_25519 /\ &0 <= y /\ y < &p_25519 /\
         ((&1 + &d_25519 * y pow 2) * x pow 2 == y pow 2 - &1) (mod &p_25519)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[EDWARDS25519_GROUP] THEN
  REWRITE_TAC[IN] THEN REWRITE_TAC[edwards_curve; edwards25519] THEN
  REWRITE_TAC[IN_INTEGER_MOD_RING_CARRIER; INTEGER_MOD_RING_CLAUSES] THEN
  REWRITE_TAC[p_25519; INT_OF_NUM_EQ; ARITH_EQ] THEN
  REWRITE_TAC[GSYM p_25519; GSYM CONJ_ASSOC] THEN REPEAT AP_TERM_TAC THEN
  SUBGOAL_THEN `&e_25519:int = &p_25519 - &1` SUBST1_TAC THENL
   [REWRITE_TAC[e_25519; p_25519] THEN INT_ARITH_TAC;
    CONV_TAC INT_REM_DOWN_CONV] THEN
  REWRITE_TAC[INT_REM_EQ] THEN CONV_TAC INTEGER_RULE);;

let EXISTS_IN_GROUP_CARRIER_EDWARDS25519 = prove
 (`!y. (?x. (x,&y) IN group_carrier edwards25519_group) <=>
       y < p_25519 /\
       ?x. (x EXP 2 == ((p_25519 - 1) + y EXP 2) * (1 + d_25519 * y EXP 2))
           (mod p_25519)`,
  GEN_TAC THEN REWRITE_TAC[IN_GROUP_CARRIER_EDWARDS25519] THEN
  REWRITE_TAC[GSYM INT_EXISTS_POS] THEN
  REWRITE_TAC[INT_OF_NUM_CLAUSES; LE_0] THEN
  ASM_CASES_TAC `y < p_25519` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
  SIMP_TAC[EDWARDS25519_NONZERO_DENOMINATORS; INTEGER_RULE
   `coprime(d:int,p)
    ==> ((d * n pow 2 == y - &1) (mod p) <=>
         ((d * n) pow 2 == ((p - &1) + y) * d) (mod p))`] THEN
  SUBGOAL_THEN `&p_25519 - &1:int = &(p_25519 - 1)` SUBST1_TAC THENL
   [REWRITE_TAC[p_25519] THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
    SPEC_TAC(`p_25519 - 1`,`e:num`) THEN GEN_TAC] THEN
  REWRITE_TAC[INT_OF_NUM_CLAUSES; GSYM num_congruent] THEN
  EQ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC
   `(inverse_mod p_25519 (1 + d_25519 * y EXP 2) * n) MOD p_25519` THEN
  CONJ_TAC THENL [REWRITE_TAC[MOD_LT_EQ; p_25519; ARITH_EQ]; ALL_TAC] THEN
  REWRITE_TAC[CONG] THEN CONV_TAC MOD_DOWN_CONV THEN
  REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC(NUMBER_RULE
   `(d * i == 1) (mod p) /\ (x EXP 2 == a) (mod p)
    ==> ((d * i * x) EXP 2 == a) (mod p)`) THEN
  ASM_REWRITE_TAC[INVERSE_MOD_RMUL_EQ] THEN ONCE_REWRITE_TAC[COPRIME_SYM] THEN
  REWRITE_TAC[num_coprime; GSYM INT_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[EDWARDS25519_NONZERO_DENOMINATORS]);;

let EXISTS_IN_GROUP_CARRIER_EDWARDS25519_EULER = prove
 (`!y w. ((((p_25519 - 1) + y EXP 2) * (1 + d_25519 * y EXP 2)) EXP
          (2 EXP 253 - 5) == w) (mod p_25519)
         ==> ((?x. (x,&y) IN group_carrier edwards25519_group) <=>
              y < p_25519 /\
              ((w == 0) (mod p_25519) \/
               (w == 1) (mod p_25519) \/
               (w == p_25519 - 1) (mod p_25519)))`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP (NUMBER_RULE
   `(x == w) (mod p) ==> !y:num. (w == y) (mod p) <=> (x == y) (mod p)`)) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[EXISTS_IN_GROUP_CARRIER_EDWARDS25519] THEN AP_TERM_TAC THEN
  MP_TAC(SPECL [`p_25519`; `1`] CONG_SQUARE_1_PRIME_POWER) THEN
  SIMP_TAC[EULER_CRITERION; PRIME_P25519; EXP_1; RIGHT_FORALL_IMP_THM] THEN
  ANTS_TAC THENL [REWRITE_TAC[p_25519] THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
  SIMP_TAC[EXP_EXP; CONG_0_DIVIDES; PRIME_DIVEXP_EQ; PRIME_P25519] THEN
  REWRITE_TAC[p_25519] THEN CONV_TAC NUM_REDUCE_CONV);;

let ED25519_ENCODE_INJECTIVE = prove
 (`!P Q. P IN group_carrier edwards25519_group /\
         Q IN group_carrier edwards25519_group
         ==> (ed25519_encode P = ed25519_encode Q <=> P = Q)`,
  REWRITE_TAC[GSYM INJECTIVE_ON_ALT] THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  REWRITE_TAC[IN_GROUP_CARRIER_EDWARDS25519; IMP_CONJ] THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM; GSYM INT_FORALL_POS] THEN
  REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN
  X_GEN_TAC `x1:num` THEN DISCH_TAC THEN
  X_GEN_TAC `y1:num` THEN DISCH_TAC THEN DISCH_TAC THEN
  X_GEN_TAC `x2:num` THEN DISCH_TAC THEN
  X_GEN_TAC `y2:num` THEN DISCH_TAC THEN DISCH_TAC THEN
  ASM_SIMP_TAC[ed25519_encode; INT_OF_NUM_REM; MOD_LT] THEN
  REWRITE_TAC[NUM_OF_INT_OF_NUM; LET_DEF; LET_END_DEF] THEN
  DISCH_THEN(fun th ->
    MP_TAC(AP_TERM `\x. x MOD 2 EXP 255` th) THEN
    MP_TAC(AP_TERM `\x. x DIV 2 EXP 255` th)) THEN
  SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
  SUBGOAL_THEN `!z. z < p_25519 ==> z < 2 EXP 255` MP_TAC THENL
   [REWRITE_TAC[p_25519] THEN ARITH_TAC; ASM_SIMP_TAC[MOD_LT; DIV_LT]] THEN
  DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[ADD_CLAUSES] THEN DISCH_TAC THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  ASM_REWRITE_TAC[PAIR_EQ; INT_OF_NUM_EQ] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM INT_REM_EQ])) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[INT_REM_EQ] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (INTEGER_RULE
   `(a * x pow 2 == a * y pow 2) (mod p)
    ==> coprime(a:int,p) ==> p divides ((x - y) * (x + y))`)) THEN
  REWRITE_TAC[EDWARDS25519_NONZERO_DENOMINATORS] THEN
  SIMP_TAC[PRIME_INT_DIVPROD_EQ; PRIME_P25519] THEN
  REWRITE_TAC[GSYM INT_CONG; GSYM num_congruent; CONG] THEN
  DISCH_THEN(DISJ_CASES_THEN MP_TAC) THEN ASM_SIMP_TAC[MOD_LT] THEN
  REWRITE_TAC[INT_OF_NUM_CLAUSES; GSYM num_divides] THEN
  DISCH_THEN(MP_TAC o SPEC `2` o MATCH_MP (NUMBER_RULE
   `p divides x + y
    ==> !q:num. q divides x + y /\ coprime(p,q) ==> p * q divides x + y`)) THEN
  REWRITE_TAC[DIVIDES_2; COPRIME_2; EVEN_ADD] THEN
  ASM_REWRITE_TAC[EVEN_MOD] THEN ANTS_TAC THENL
   [REWRITE_TAC[p_25519; ARITH_EVEN; ARITH_ODD];
    DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE)] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[p_25519] THEN ARITH_TAC);;

let j_25519 = define
 `j_25519 =
19681161376707505956807079304988542015446066515923890162744021073123829784752`;;

(* ------------------------------------------------------------------------- *)
(* Overall proof.                                                            *)
(* ------------------------------------------------------------------------- *)

let EDWARDS25519_DECODE_ALT_CORRECT = time prove
 (`!z c n pc stackpointer.
        ALL (nonoverlapping (stackpointer,264))
            [(word pc,0x9ae); (z,8 * 8); (c,8 * 4)] /\
        nonoverlapping (word pc,0x9ae) (z,8 * 8)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) edwards25519_decode_alt_tmc /\
                  read RIP s = word(pc + 0x11) /\
                  read RSP s = word_add stackpointer (word 8) /\
                  C_ARGUMENTS [z; c] s /\
                  read (memory :> bytes(c,32)) s = n)
             (\s. read RIP s = word (pc + 0x5ae) /\
                  C_RETURN s = word(bitval(~ed25519_validencode n)) /\
                  (ed25519_validencode n
                   ==> bignum_pair_from_memory(z,4) s =
                       paired (modular_encode (256,p_25519))
                              (ed25519_decode n)))
             (MAYCHANGE [RIP; RDI; RSI; RAX; RBX; RCX; RDX; RBP;
                         R8; R9; R10; R11; R12; R13; R14; R15] ,,
              MAYCHANGE SOME_FLAGS ,,
              MAYCHANGE [memory :> bytes(z,8 * 8);
                         memory :> bytes(stackpointer,264)])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `c:int64`; `n:num`; `pc:num`; `stackpointer:int64`] THEN
  REWRITE_TAC[ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EXISTING_PRESERVED_TAC `RSP` THEN

  (*** Initial load and split ***)

  REWRITE_TAC[ARITH_RULE `32 = 8 * 4`] THEN
  REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
  BIGNUM_TERMRANGE_TAC `4` `n:num` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NUM_REDUCE_CONV `64 * 4`]) THEN
  MAP_EVERY ABBREV_TAC [`y = n MOD 2 EXP 255`; `b = n DIV 2 EXP 255`] THEN

  ENSURES_SEQUENCE_TAC `pc + 0x69`
   `\s. read RSP s = word_add stackpointer (word 8) /\
        read (memory :> bytes64(word_add stackpointer (word 232))) s = z /\
        read (memory :> bytes64(word_add stackpointer (word 240))) s =
        word b /\
        bignum_from_memory(word_add stackpointer (word 8),4) s = y /\
        read (memory :> bytes64(word_add stackpointer (word 248))) s =
        word(bitval(p_25519 <= y))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    BIGNUM_LDIGITIZE_TAC "n_" `read (memory :> bytes (c,8 * 4)) s0` THEN
    X86_ACCSTEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (14--17) (1--19) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
    DISCARD_STATE_TAC "s19" THEN
    MATCH_MP_TAC(TAUT `(p /\ q) /\ (q ==> r) ==> p /\ q /\ r`) THEN
    CONJ_TAC THENL
     [MAP_EVERY EXPAND_TAC ["y"; "b"] THEN REWRITE_TAC[word_ushr] THEN
      MATCH_MP_TAC(MESON[]
       `q = q' /\ r = r' ==> word q' = word q /\ r' = r`) THEN
      MATCH_MP_TAC DIVMOD_UNIQ THEN
      CONJ_TAC THENL [ALL_TAC; BOUNDER_TAC[]] THEN
      EXPAND_TAC "n" THEN
      REWRITE_TAC[bignum_of_wordlist] THEN CONV_TAC WORD_BLAST;
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[word_ushr] THEN
      REWRITE_TAC[ARITH_RULE `63 = 64 - 1`; GSYM DIMINDEX_64] THEN
      REWRITE_TAC[GSYM BITVAL_MSB; MSB_VAL] THEN
      REWRITE_TAC[DIMINDEX_64; ARITH_RULE `64 - 1 = 63`] THEN
      AP_TERM_TAC THEN AP_TERM_TAC] THEN
    TRANS_TAC EQ_TRANS
     `2 EXP 255 <= bignum_of_wordlist[sum_s14;sum_s15;sum_s16;sum_s17]` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE
       `2 EXP 255 <= n <=> 2 EXP 63 <= n DIV 2 EXP 192`] THEN
      CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
      REWRITE_TAC[GSYM MSB_IVAL; MSB_VAL] THEN
      REWRITE_TAC[DIMINDEX_64] THEN ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC(ARITH_RULE
     `p + 19 = e /\ x = y + 19 ==> (e <= x <=> p <= y)`) THEN
    REWRITE_TAC[p_25519] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN

  (*** Computation of y^2 ***)

  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (1--4) THEN LOCAL_NSQR_TAC 5 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_1; EXP_1]) THEN

  (*** Computation of u ***)

  BIGNUM_LDIGITIZE_TAC "y2_"
   `read (memory :> bytes(word_add stackpointer (word 136),8 * 4)) s5` THEN
  SUBGOAL_THEN
   `read (memory :> bytes (word_add stackpointer (word 136),8 * 4)) s5 =
     y EXP 2 MOD p_25519`
  ASSUME_TAC THENL
   [CONV_TAC(LAND_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X86_ACCSTEPS_TAC EDWARDS25519_DECODE_ALT_EXEC [8;10;12;14] (6--15) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_BLAST
   `word_xor sum_s14 (word 9223372036854775808):int64 =
    word_add sum_s14 (word 9223372036854775808)`]) THEN
  ACCUMULATE_ARITH_TAC "s15" THEN
  X86_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (16--19) THEN
  ABBREV_TAC `u = (p_25519 - 1) + y EXP 2 MOD p_25519` THEN
  SUBGOAL_THEN
   `read (memory :> bytes(word_add stackpointer (word 104),8 * 4)) s19 = u`
  ASSUME_TAC THENL
   [CONV_TAC(LAND_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 256` THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
     [EXPAND_TAC "u" THEN REWRITE_TAC[p_25519] THEN ARITH_TAC;
      REWRITE_TAC[REAL_CONGRUENCE; EXP_EQ_0; ARITH_EQ]] THEN
      EXPAND_TAC "u" THEN
    SUBST1_TAC(SYM(ASSUME
     `bignum_of_wordlist [y2_0; y2_1; y2_2; y2_3] = y EXP 2 MOD p_25519`)) THEN
    REWRITE_TAC[p_25519] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[p_25519] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN POP_ASSUM MP_TAC THEN
    POP_ASSUM(fun th -> DISCH_TAC THEN ASSUME_TAC th)] THEN

  (*** Computation of v ***)

  X86_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (20--31) THEN
  SUBGOAL_THEN
    `read (memory :> bytes(word_add stackpointer (word 168),8 * 4)) s31 =
     d_25519`
  ASSUME_TAC THENL
   [CONV_TAC(LAND_CONV BIGNUM_LEXPAND_CONV) THEN
    ASM_REWRITE_TAC[bignum_of_wordlist; d_25519] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV);
    ALL_TAC] THEN
  LOCAL_MUL_TAC 32 THEN RULE_ASSUM_TAC(CONV_RULE MOD_DOWN_CONV) THEN

  BIGNUM_LDIGITIZE_TAC "d_"
   `read (memory :> bytes (word_add stackpointer (word 136),8 * 4)) s32` THEN
  X86_ACCSTEPS_TAC EDWARDS25519_DECODE_ALT_EXEC [35;37;39;41] (33--45) THEN

  ABBREV_TAC `v = 1 + (d_25519 * y EXP 2) MOD p_25519` THEN

  SUBGOAL_THEN
   `read (memory :> bytes(word_add stackpointer (word 136),8 * 4)) s45 = v`
  ASSUME_TAC THENL
   [CONV_TAC(LAND_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 256` THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
     [EXPAND_TAC "v" THEN REWRITE_TAC[p_25519] THEN ARITH_TAC;
      REWRITE_TAC[REAL_CONGRUENCE; EXP_EQ_0; ARITH_EQ]] THEN
    EXPAND_TAC "v" THEN
    SUBST1_TAC(SYM(ASSUME
     `bignum_of_wordlist [d_0; d_1; d_2; d_3] =
      (d_25519 * y EXP 2) MOD p_25519`)) THEN
    REWRITE_TAC[p_25519] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[p_25519] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN POP_ASSUM MP_TAC THEN
    POP_ASSUM(fun th -> DISCH_TAC THEN ASSUME_TAC th)] THEN

  (*** Computation of w ***)

  X86_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (46--49) THEN LOCAL_MUL_TAC 50 THEN
  ABBREV_TAC `w = (u * v) MOD p_25519` THEN

  (*** The power tower ***)

  X86_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (51--55) THEN LOCAL_NSQR_TAC 56 THEN
  X86_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (57--61) THEN LOCAL_MUL_TAC 62 THEN
  X86_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (63--67) THEN LOCAL_NSQR_TAC 68 THEN
  X86_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (69--73) THEN LOCAL_MUL_TAC 74 THEN
  X86_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (75--79) THEN LOCAL_NSQR_TAC 80 THEN
  X86_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (81--85) THEN LOCAL_MUL_TAC 86 THEN
  X86_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (87--91) THEN LOCAL_NSQR_TAC 92 THEN
  X86_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (93--97) THEN LOCAL_MUL_TAC 98 THEN
  X86_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (99--103) THEN LOCAL_NSQR_TAC 104 THEN
  X86_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (105--109) THEN LOCAL_MUL_TAC 110 THEN
  X86_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (111--115) THEN LOCAL_NSQR_TAC 116 THEN
  X86_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (117--121) THEN LOCAL_MUL_TAC 122 THEN
  X86_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (123--127) THEN LOCAL_NSQR_TAC 128 THEN
  X86_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (129--133) THEN LOCAL_MUL_TAC 134 THEN
  X86_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (135--139) THEN LOCAL_NSQR_TAC 140 THEN
  X86_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (141--145) THEN LOCAL_MUL_TAC 146 THEN
  X86_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (147--151) THEN LOCAL_NSQR_TAC 152 THEN
  X86_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (153--157) THEN LOCAL_MUL_TAC 158 THEN
  X86_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (159--163) THEN LOCAL_NSQR_TAC 164 THEN
  X86_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (165--169) THEN LOCAL_MUL_TAC 170 THEN
  X86_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (171--175) THEN LOCAL_NSQR_TAC 176 THEN
  X86_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (177--181) THEN LOCAL_MUL_TAC 182 THEN

  REABBREV_TAC
   `e =
    read (memory :> bytes (word_add stackpointer (word 40),8 * 4)) s182` THEN
  POP_ASSUM(MP_TAC o CONV_RULE MOD_DOWN_CONV) THEN
  CONV_TAC(LAND_CONV(DEPTH_CONV WORD_NUM_RED_CONV)) THEN
  REWRITE_TAC[MULT_EXP] THEN REWRITE_TAC[EXP_EXP] THEN
  REWRITE_TAC[GSYM EXP_ADD] THEN
  ONCE_REWRITE_TAC[MESON[EXP; MULT_SYM] `x EXP n * x = x EXP SUC n`] THEN
  CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN
  REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 252 - 3`)] THEN DISCH_TAC THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check
   (free_in `val(word 1:int64)` o concl))) THEN

  (*** e^2 * w computation ***)

  X86_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (183--187) THEN LOCAL_NSQR_TAC 188 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_1; EXP_1]) THEN
  X86_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (189--193) THEN LOCAL_MUL_TAC 194 THEN
  RULE_ASSUM_TAC(CONV_RULE MOD_DOWN_CONV) THEN

  (*** s = u * e ***)

  X86_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (195--199) THEN LOCAL_MUL_TAC 200 THEN
  RULE_ASSUM_TAC(CONV_RULE MOD_DOWN_CONV) THEN
  ABBREV_TAC `s = (u * e) MOD p_25519` THEN

  (*** t = j_25519 * s ***)

  X86_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (201--213) THEN
  SUBGOAL_THEN
    `read (memory :> bytes(word_add stackpointer (word 72),8 * 4)) s213 =
     j_25519`
  ASSUME_TAC THENL
   [CONV_TAC(LAND_CONV BIGNUM_LEXPAND_CONV) THEN
    ASM_REWRITE_TAC[bignum_of_wordlist; j_25519] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV);
    ALL_TAC] THEN
  LOCAL_MUL_TAC 214 THEN

  (*** Comparison with 0 or 1 ***)

  ABBREV_TAC `f = (e EXP 2 * w) MOD p_25519` THEN
  BIGNUM_LDIGITIZE_TAC "f_"
   `read (memory :> bytes(word_add stackpointer (word 136),8 * 4)) s214` THEN
  X86_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (215--225) THEN
  REABBREV_TAC `f01 = read RAX s225` THEN
  SUBGOAL_THEN
   `f01:int64 = word 0 <=>
    (w * e EXP 2 == 0) (mod p_25519) \/
    (w * e EXP 2 == 1) (mod p_25519)`
  ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_REWRITE_TAC[CONG] THEN
    REWRITE_TAC[p_25519] THEN CONV_TAC NUM_REDUCE_CONV THEN
    EXPAND_TAC "f01" THEN REWRITE_TAC[WORD_OR_EQ_0] THEN
    SUBGOAL_THEN `1 = bignum_of_wordlist[word 1;word 0;word 0;word 0]`
    SUBST1_TAC THENL
     [REWRITE_TAC[bignum_of_wordlist] THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV);
      SUBST1_TAC(SYM(ASSUME
       `bignum_of_wordlist [f_0; f_1; f_2; f_3] = f`))] THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_EQ; BIGNUM_OF_WORDLIST_EQ_0] THEN
    REWRITE_TAC[ALL; GSYM CONJ_ASSOC; GSYM RIGHT_OR_DISTRIB] THEN
    REPEAT(AP_THM_TAC THEN AP_TERM_TAC) THEN
    REWRITE_TAC[WORD_EQ_BITS_ALT; DIMINDEX_64] THEN
    CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
    CONV_TAC(TOP_DEPTH_CONV BIT_WORD_CONV) THEN
    REWRITE_TAC[GSYM CONJ_ASSOC; GSYM RIGHT_OR_DISTRIB] THEN
    REWRITE_TAC[TAUT `~p \/ p`];
    ALL_TAC] THEN

  (*** Comparison with -1 ***)

  X86_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (226--233) THEN
  REABBREV_TAC `fm1 = read R8 s233` THEN
  SUBGOAL_THEN
   `fm1:int64 = word 0 <=> (w * e EXP 2 == p_25519 - 1) (mod p_25519)`
  ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_REWRITE_TAC[CONG] THEN
    SUBGOAL_THEN `(p_25519 - 1) MOD p_25519 =
                  bignum_of_wordlist[word(2 EXP 64 - 20); word(2 EXP 64 - 1);
                                     word(2 EXP 64 - 1); word(2 EXP 63 - 1)]`
    SUBST1_TAC THENL
     [REWRITE_TAC[p_25519; bignum_of_wordlist] THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV);
      SUBST1_TAC(SYM(ASSUME
       `bignum_of_wordlist [f_0; f_1; f_2; f_3] = f`))] THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_EQ; ALL] THEN
    EXPAND_TAC "fm1" THEN REWRITE_TAC[WORD_OR_EQ_0] THEN
    REWRITE_TAC[WORD_XOR_EQ_0; GSYM CONJ_ASSOC; WORD_RULE
     `word_add x y = word 0 <=> x = word_neg y`] THEN
    REWRITE_TAC[WORD_RULE `word_not x = word 0 <=> x = word_not(word 0)`] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN REPEAT AP_TERM_TAC THEN
    REWRITE_TAC[WORD_EQ_BITS_ALT; DIMINDEX_64] THEN
    CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
    CONV_TAC(TOP_DEPTH_CONV BIT_WORD_CONV) THEN
    REWRITE_TAC[CONJ_ASSOC; TAUT `(p <=> p /\ q) <=> p ==> q`] THEN
    DISCH_THEN(K ALL_TAC) THEN
    SUBGOAL_THEN `f < 2 EXP 255` MP_TAC THENL
     [EXPAND_TAC "f" THEN REWRITE_TAC[p_25519] THEN ARITH_TAC;
      REWRITE_TAC[ARITH_RULE
       `f < 2 EXP 255 <=> f DIV 2 EXP 192 < 2 EXP 63`]] THEN
    SUBST1_TAC(SYM(ASSUME
       `bignum_of_wordlist [f_0; f_1; f_2; f_3] = f`)) THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REWRITE_TAC[ARITH_RULE `63 = 64 - 1`; GSYM DIMINDEX_64] THEN
    REWRITE_TAC[MSB_VAL; NOT_LE];
    ALL_TAC] THEN

  (*** Multiplexing of s or t ***)

  BIGNUM_LDIGITIZE_TAC "s_"
   `read (memory :> bytes(word_add stackpointer (word 40),8 * 4)) s233` THEN
  BIGNUM_LDIGITIZE_TAC "t_"
   `read (memory :> bytes(word_add stackpointer (word 72),8 * 4)) s233` THEN
  X86_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (234--250) THEN
  ABBREV_TAC `x = if (w * e EXP 2 == 0) (mod p_25519) \/
                     (w * e EXP 2 == 1) (mod p_25519)
                  then s else (s * j_25519) MOD p_25519` THEN
  SUBGOAL_THEN `x < p_25519` ASSUME_TAC THENL
   [EXPAND_TAC "x" THEN SUBST1_TAC(SYM(ASSUME `(u * e) MOD p_25519 = s`)) THEN
    COND_CASES_TAC THEN REWRITE_TAC[MOD_LT_EQ] THEN
    REWRITE_TAC[p_25519; ARITH_EQ];
    ALL_TAC] THEN

  SUBGOAL_THEN
   `read (memory :> bytes(word_add stackpointer (word 40),8 * 4)) s250 = x`
  ASSUME_TAC THENL
   [CONV_TAC(LAND_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[VAL_EQ_0; WORD_SUB_0; COND_SWAP] THEN EXPAND_TAC "x" THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN

  (*** Error indication (so far) ***)

  X86_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (251--255) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (MESON[]
   `read (memory :> m) s = a ==> read (memory :> m) s = a`)) THEN
  REWRITE_TAC[WORD_NEG_NEG; MESON[VAL_EQ_0]
   `(if val x = 0 then x else y) = word 0 <=> x = word 0 \/ y = word 0`] THEN
  ASM_REWRITE_TAC[WORD_OR_CONDITIONS; DE_MORGAN_THM; GSYM CONJ_ASSOC] THEN
  DISCH_TAC THEN

  (*** Computation of p_25519 - x ***)

  DISCARD_MATCHING_ASSUMPTIONS
   [`read (memory :> mm) s = if ~(val a = 0) then x else y`] THEN
  BIGNUM_LDIGITIZE_TAC "x_"
   `read (memory :> bytes(word_add stackpointer (word 40),8 * 4)) s255` THEN
  X86_ACCSTEPS_TAC EDWARDS25519_DECODE_ALT_EXEC [258;261;264;267] (256--267) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist [sum_s258;sum_s261;sum_s264;sum_s267] = p_25519 - x`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 256` THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [REWRITE_TAC[p_25519] THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_CONGRUENCE; EXP_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; LT_IMP_LE] THEN EXPAND_TAC "x" THEN
    REWRITE_TAC[p_25519; GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Final selection and return ***)

  BIGNUM_LDIGITIZE_TAC "y_"
   `read (memory :> bytes(word_add stackpointer (word 8),8 * 4)) s267` THEN
  X86_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (268--300) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[bignum_pair_from_memory; BIGNUM_FROM_MEMORY_BYTES] THEN
  REWRITE_TAC[WORD_RULE `word(8 * 4) = word 32`] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
  ASM_REWRITE_TAC[COND_SWAP; VAL_EQ_0; WORD_OR_EQ_0; GSYM CONJ_ASSOC] THEN
  REWRITE_TAC[MESON[]
   `(if (if p then word 0 else z) = word 0 then x else y) =
    if p \/ z = word 0 then x else y`] THEN
  DISCARD_STATE_TAC "s300" THEN

  (*** The final mathematics ***)

  ONCE_REWRITE_TAC[TAUT `p /\ r /\ q /\ s <=> p /\ q /\ r /\ s`] THEN
  ASM_REWRITE_TAC[GSYM(REWRITE_RULE[ALL]
   (SPEC `[x_0; x_1; x_2; x_3]:int64 list` BIGNUM_OF_WORDLIST_EQ_0))] THEN
  SUBGOAL_THEN `b < 2` ASSUME_TAC THENL
   [EXPAND_TAC "b" THEN UNDISCH_TAC `n < 2 EXP 256` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `word_xor (word_and (word 1) x_0) (word b):int64 =
    word(bitval(~(x MOD 2 = b)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[WORD_AND_1_BITVAL; BIT_LSB; MOD_2_CASES] THEN
    EXPAND_TAC "x" THEN
    REWRITE_TAC[bignum_of_wordlist; EVEN_MULT; EVEN_ADD; EVEN_EXP] THEN
    CONV_TAC NUM_REDUCE_CONV THEN UNDISCH_TAC `b < 2` THEN
    SPEC_TAC(`b:num`,`b:num`) THEN REWRITE_TAC[GSYM NOT_ODD; COND_SWAP] THEN
    CONV_TAC EXPAND_CASES_CONV THEN COND_CASES_TAC THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV);
    REWRITE_TAC[WORD_OR_CONDITIONS]] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM COND_RAND] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM COND_RAND] THEN
  REWRITE_TAC[TAUT `(if p then q \/ r else q) <=> (q \/ p /\ r)`] THEN
  REWRITE_TAC[ARITH_RULE `x = 0 /\ ~(x MOD 2 = b) <=> x = 0 /\ ~(b = 0)`] THEN
  REWRITE_TAC[WORD_BITVAL_EQ_0] THEN
  REWRITE_TAC[MESON[]
   `[if p then x else y] = if p then [x] else [y]`] THEN
  REWRITE_TAC[MESON[]
   `CONS (if p then x else y) (if p then u else v) =
    if p then CONS x u else CONS y v`] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN ASM_REWRITE_TAC[] THEN

  MP_TAC(SPECL [`y:num`; `w * e EXP 2`]
   EXISTS_IN_GROUP_CARRIER_EDWARDS25519_EULER) THEN
  ANTS_TAC THENL
   [EXPAND_TAC "e" THEN REWRITE_TAC[CONG] THEN
    CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[GSYM CONG] THEN
    REWRITE_TAC[EXP_EXP; GSYM(CONJUNCT2 EXP)] THEN
    CONV_TAC NUM_REDUCE_CONV THEN MATCH_MP_TAC CONG_EXP THEN
    MAP_EVERY EXPAND_TAC ["w"; "u"; "v"] THEN
    REWRITE_TAC[CONG] THEN CONV_TAC MOD_DOWN_CONV THEN REFL_TAC;
    ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN MP_TAC o MATCH_MP
   (TAUT `(p <=> q) ==> ~p /\ ~q \/ p /\ q`))
  THENL
   [REWRITE_TAC[DE_MORGAN_THM; NOT_LT] THEN
    DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~ed25519_validencode n` (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[ed25519_validencode; NOT_EXISTS_THM; FORALL_PAIR_THM] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_EXISTS_THM]) THEN
    REWRITE_TAC[IN_GROUP_CARRIER_EDWARDS25519; LET_DEF; LET_END_DEF] THEN
    REWRITE_TAC[FORALL_PAIR_THM; TAUT `~(p /\ q) <=> p ==> ~q`] THEN
    REWRITE_TAC[IMP_CONJ] THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
    REWRITE_TAC[GSYM INT_FORALL_POS; ed25519_encode; LET_DEF; LET_END_DEF] THEN
    SIMP_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_REM; MOD_LT] THEN
    REWRITE_TAC[LE_0; NUM_OF_INT_OF_NUM] THEN
    DISCH_THEN(fun th -> X_GEN_TAC `X:num` THEN DISCH_TAC THEN
      MP_TAC(SPEC `X:num` th) THEN ASM_REWRITE_TAC[]) THEN
    DISCH_THEN(fun th -> X_GEN_TAC `Y:num` THEN DISCH_TAC THEN MP_TAC th) THEN
    ONCE_REWRITE_TAC[TAUT `p ==> q ==> ~r <=> r ==> p ==> ~q`] THEN
    DISCH_THEN(MP_TAC o AP_TERM `\x. x MOD 2 EXP 255`) THEN
    REWRITE_TAC[MOD_MULT_ADD] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `Y < 2 EXP 255` (fun th -> SIMP_TAC[th; MOD_LT]) THENL
      [UNDISCH_TAC `Y < p_25519` THEN REWRITE_TAC[p_25519] THEN ARITH_TAC;
       ALL_TAC] THEN
    DISCH_THEN SUBST_ALL_TAC THEN ASM_REWRITE_TAC[];
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)] THEN
  ASM_REWRITE_TAC[GSYM NOT_LT; GSYM DE_MORGAN_THM] THEN
  SUBGOAL_THEN `(&x,&y) IN group_carrier edwards25519_group` ASSUME_TAC THENL
   [REWRITE_TAC[IN_GROUP_CARRIER_EDWARDS25519; LET_DEF; LET_END_DEF] THEN
    ASM_REWRITE_TAC[INT_OF_NUM_CLAUSES; LE_0] THEN
    SUBGOAL_THEN `(v * x EXP 2 == u) (mod p_25519)` MP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o check (is_disj o concl));
      MAP_EVERY EXPAND_TAC ["u"; "v"] THEN
      REWRITE_TAC[num_congruent; GSYM INT_OF_NUM_CLAUSES; GSYM INT_OF_NUM_REM;
                  GSYM INT_REM_EQ] THEN
      CONV_TAC INT_REM_DOWN_CONV THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[INT_REM_EQ; INTEGER_RULE
       `(e + y:int == y - &1) (mod p) <=> p divides (e + &1)`] THEN
      REWRITE_TAC[p_25519] THEN CONV_TAC NUM_REDUCE_CONV THEN
      CONV_TAC INT_REDUCE_CONV THEN REWRITE_TAC[INT_DIVIDES_REFL]] THEN
    DISCARD_MATCHING_ASSUMPTIONS [`bignum_of_wordlist l = n`] THEN
    EXPAND_TAC "x" THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[DISJ_ASSOC] THENL
     [EXPAND_TAC "s" THEN MATCH_MP_TAC CONG_TRANS THEN
      EXISTS_TAC `u * (u * v) MOD p_25519 * e EXP 2` THEN CONJ_TAC THENL
       [REWRITE_TAC[CONG] THEN CONV_TAC MOD_DOWN_CONV THEN
        AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
        ASM_REWRITE_TAC[]] THEN
      MATCH_MP_TAC(NUMBER_RULE
        `(u == 0) (mod p) \/ (x == 1) (mod p) ==> (u * x == u) (mod p)`) THEN
      FIRST_X_ASSUM(DISJ_CASES_THEN MP_TAC) THEN SIMP_TAC[] THEN
      EXPAND_TAC "e" THEN REWRITE_TAC[CONG] THEN
      CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[GSYM CONG] THEN
      REWRITE_TAC[EXP_EXP; GSYM(CONJUNCT2 EXP)] THEN
      DISCH_THEN(fun th -> DISJ1_TAC THEN MP_TAC th) THEN
      EXPAND_TAC "w" THEN REWRITE_TAC[CONG] THEN
      CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[GSYM CONG] THEN
      REWRITE_TAC[CONG_0_DIVIDES] THEN
      SIMP_TAC[PRIME_DIVEXP_EQ; PRIME_P25519; PRIME_DIVPROD_EQ] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      MATCH_MP_TAC(TAUT `~q ==> p \/ q ==> p`) THEN
      REWRITE_TAC[GSYM CONG_0_DIVIDES] THEN EXPAND_TAC "v" THEN
      REWRITE_TAC[CONG] THEN
      CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[GSYM CONG] THEN
      REWRITE_TAC[CONG_0_DIVIDES] THEN DISCH_THEN(MP_TAC o MATCH_MP(NUMBER_RULE
       `p divides n ==> coprime(n,p) ==> p = 1`)) THEN
      REWRITE_TAC[p_25519; ARITH_EQ] THEN REWRITE_TAC[GSYM p_25519] THEN
      REWRITE_TAC[num_coprime; GSYM INT_OF_NUM_CLAUSES] THEN
      REWRITE_TAC[EDWARDS25519_NONZERO_DENOMINATORS];

      MAP_EVERY EXPAND_TAC ["w"; "s"] THEN REWRITE_TAC[CONG] THEN
      CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[GSYM CONG] THEN
      MATCH_MP_TAC(NUMBER_RULE
       `(a * j EXP 2 == 1) (mod p)
        ==> ((u * v) * e EXP 2 == a) (mod p)
            ==> (v * ((u * e) * j) EXP 2 == u) (mod p)`) THEN
      REWRITE_TAC[CONG; p_25519; j_25519] THEN CONV_TAC NUM_REDUCE_CONV];
    ALL_TAC] THEN

  ASM_SIMP_TAC[ARITH_RULE `b < 2 ==> (~(b = 0) <=> b = 1)`] THEN
  CONV_TAC(LAND_CONV SYM_CONV) THEN
  ASM_CASES_TAC `x = 0 /\ b = 1` THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  ASM_REWRITE_TAC[WORD_BITVAL_EQ_0; WORD_BITVAL_EQ_1] THENL
   [REWRITE_TAC[TAUT `~p /\ (p ==> q) <=> ~p`] THEN
    REWRITE_TAC[ed25519_validencode; NOT_EXISTS_THM] THEN
    REWRITE_TAC[FORALL_PAIR_THM; TAUT `~(p /\ q) <=> p ==> ~q`] THEN
    REWRITE_TAC[IN_GROUP_CARRIER_EDWARDS25519; LET_DEF; LET_END_DEF] THEN
    REWRITE_TAC[IMP_CONJ] THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
    REWRITE_TAC[GSYM INT_FORALL_POS; ed25519_encode; LET_DEF; LET_END_DEF] THEN
    SIMP_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_REM; MOD_LT] THEN
    REWRITE_TAC[LE_0; NUM_OF_INT_OF_NUM] THEN
    X_GEN_TAC `X:num` THEN DISCH_TAC THEN
    X_GEN_TAC `Y:num` THEN DISCH_TAC THEN
    ONCE_REWRITE_TAC[TAUT `p ==> ~q <=> q ==> ~p`] THEN
    DISCH_THEN(fun th ->
      MP_TAC(AP_TERM `\x. x MOD 2 EXP 255` th) THEN
      MP_TAC(AP_TERM `\x. x DIV 2 EXP 255` th)) THEN
    SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
    FIRST_X_ASSUM(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
    SUBGOAL_THEN `Y < 2 EXP 255` (fun th -> SIMP_TAC[th; MOD_LT; DIV_LT]) THENL
     [UNDISCH_TAC `Y < p_25519` THEN REWRITE_TAC[p_25519] THEN ARITH_TAC;
      ASM_REWRITE_TAC[]] THEN
    REWRITE_TAC[ADD_CLAUSES] THEN DISCH_TAC THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
     [IN_GROUP_CARRIER_EDWARDS25519]) THEN
    REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MULT_CLAUSES] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; TAUT `p ==> ~q <=> ~(p /\ q)`] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (INTEGER_RULE
     `(&0:int == r) (mod p) /\ (a * x pow 2 == r) (mod p)
      ==> p divides a * x pow 2`)) THEN
    SIMP_TAC[INT_POW_2; PRIME_INT_DIVPROD_EQ; PRIME_P25519] THEN
    REWRITE_TAC[DE_MORGAN_THM; INT_OF_NUM_CLAUSES; GSYM num_divides] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM EXP_2] THEN DISCH_THEN(MP_TAC o MATCH_MP(NUMBER_RULE
       `p divides n ==> coprime(n,p) ==> p = 1`)) THEN
      REWRITE_TAC[p_25519; ARITH_EQ] THEN REWRITE_TAC[GSYM p_25519] THEN
      REWRITE_TAC[num_coprime; GSYM INT_OF_NUM_CLAUSES] THEN
      REWRITE_TAC[EDWARDS25519_NONZERO_DENOMINATORS];
      ASM_SIMP_TAC[DIVIDES_MOD; MOD_LT] THEN
      UNDISCH_TAC `X MOD 2 = 1` THEN ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
      SIMP_TAC[] THEN CONV_TAC NUM_REDUCE_CONV];
    REWRITE_TAC[TAUT `p /\ (p ==> q) <=> p /\ q`]] THEN

  ABBREV_TAC `x' = if x = 0 \/ x MOD 2 = b then x else p_25519 - x` THEN
  SUBGOAL_THEN `(&x',&y) IN group_carrier edwards25519_group` ASSUME_TAC THENL
   [EXPAND_TAC "x'" THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB; LT_IMP_LE] THEN
    REWRITE_TAC[IN_GROUP_CARRIER_EDWARDS25519] THEN
    ASM_REWRITE_TAC[INT_SUB_LE; INT_LT_SUB_RADD] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM]) THEN
    ASM_REWRITE_TAC[INT_OF_NUM_CLAUSES; LT_ADD; LE_0] THEN
    ASM_SIMP_TAC[LE_1; LT_IMP_LE] THEN
    FIRST_X_ASSUM(MP_TAC o last o CONJUNCTS o GEN_REWRITE_RULE I
     [IN_GROUP_CARRIER_EDWARDS25519]) THEN
    REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN CONV_TAC INTEGER_RULE;
    ALL_TAC] THEN

  SUBGOAL_THEN `ed25519_encode(&x',&y) = n` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
     [IN_GROUP_CARRIER_EDWARDS25519]) THEN
    REWRITE_TAC[INT_OF_NUM_CLAUSES; ed25519_encode; LET_DEF; LET_END_DEF;
                INT_OF_NUM_REM; NUM_OF_INT_OF_NUM] THEN
    SUBGOAL_THEN `!z. z < p_25519 ==> z < 2 EXP 255` MP_TAC THENL
     [REWRITE_TAC[p_25519] THEN ARITH_TAC; SIMP_TAC[MOD_LT]] THEN
    DISCH_THEN(K ALL_TAC) THEN STRIP_TAC THEN
    GEN_REWRITE_TAC RAND_CONV
     [ARITH_RULE `n = 2 EXP 255 * n DIV 2 EXP 255 + n MOD 2 EXP 255`] THEN
    ASM_REWRITE_TAC[EQ_ADD_RCANCEL; EQ_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ] THEN
    EXPAND_TAC "x'" THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
     [FIRST_X_ASSUM DISJ_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~(x = 0 /\ b = 1)` THEN
      ASM_SIMP_TAC[ARITH_RULE `b < 2 ==> (~(b = 1) <=> b = 0)`] THEN ARITH_TAC;
      RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM]) THEN
      REWRITE_TAC[MOD_2_CASES; EVEN_SUB] THEN ASM_REWRITE_TAC[GSYM NOT_LT] THEN
      FIRST_X_ASSUM(MP_TAC o CONJUNCT2) THEN REWRITE_TAC[MOD_2_CASES] THEN
      REWRITE_TAC[p_25519] THEN CONV_TAC NUM_REDUCE_CONV THEN
      UNDISCH_TAC `b < 2` THEN SPEC_TAC(`b:num`,`b:num`) THEN
      REWRITE_TAC[COND_SWAP] THEN CONV_TAC EXPAND_CASES_CONV THEN ARITH_TAC];
    ALL_TAC] THEN

  CONJ_TAC THENL
   [REWRITE_TAC[ed25519_validencode] THEN EXISTS_TAC `&x':int,&y:int` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ed25519_decode n = &x',&y` SUBST1_TAC THENL
   [REWRITE_TAC[ed25519_decode] THEN
    POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
    MESON_TAC[ED25519_ENCODE_INJECTIVE];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
     [IN_GROUP_CARRIER_EDWARDS25519]) THEN
  REWRITE_TAC[INT_OF_NUM_CLAUSES; ed25519_encode; LET_DEF; LET_END_DEF;
              INT_OF_NUM_REM; NUM_OF_INT_OF_NUM] THEN
  SIMP_TAC[paired; modular_encode; MOD_LT; INT_OF_NUM_REM;
           NUM_OF_INT_OF_NUM]);;

let EDWARDS25519_DECODE_ALT_NOIBT_SUBROUTINE_CORRECT = time prove
 (`!z c n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 312),312))
            [(word pc,LENGTH edwards25519_decode_alt_tmc); (z,8 * 8); (c,8 * 4)] /\
        ALL (nonoverlapping (z,8 * 8))
            [(word pc,LENGTH edwards25519_decode_alt_tmc); (word_sub stackpointer (word 312),320)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) edwards25519_decode_alt_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; c] s /\
                  read (memory :> bytes(c,32)) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  C_RETURN s = word(bitval(~ed25519_validencode n)) /\
                  (ed25519_validencode n
                   ==> bignum_pair_from_memory(z,4) s =
                       paired (modular_encode (256,p_25519))
                              (ed25519_decode n)))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 8);
                    memory :> bytes(word_sub stackpointer (word 312),312)])`,
  X86_ADD_RETURN_STACK_TAC
   EDWARDS25519_DECODE_ALT_EXEC EDWARDS25519_DECODE_ALT_CORRECT
   `[RBX; RBP; R12; R13; R14; R15]` 312);;

let EDWARDS25519_DECODE_ALT_SUBROUTINE_CORRECT = time prove
 (`!z c n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 312),312))
            [(word pc,LENGTH edwards25519_decode_alt_mc); (z,8 * 8); (c,8 * 4)] /\
        ALL (nonoverlapping (z,8 * 8))
            [(word pc,LENGTH edwards25519_decode_alt_mc); (word_sub stackpointer (word 312),320)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) edwards25519_decode_alt_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; c] s /\
                  read (memory :> bytes(c,32)) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  C_RETURN s = word(bitval(~ed25519_validencode n)) /\
                  (ed25519_validencode n
                   ==> bignum_pair_from_memory(z,4) s =
                       paired (modular_encode (256,p_25519))
                              (ed25519_decode n)))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 8);
                    memory :> bytes(word_sub stackpointer (word 312),312)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE EDWARDS25519_DECODE_ALT_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let edwards25519_decode_alt_windows_mc = define_from_elf
  "edwards25519_decode_alt_windows_mc"
  "x86/curve25519/edwards25519_decode_alt.obj";;

let edwards25519_decode_alt_windows_tmc = define_trimmed "edwards25519_decode_alt_windows_tmc" edwards25519_decode_alt_windows_mc;;

let EDWARDS25519_DECODE_ALT_NOIBT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z c n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 336),336))
            [(word pc,LENGTH edwards25519_decode_alt_windows_tmc); (z,8 * 8); (c,8 * 4)] /\
        ALL (nonoverlapping (z,8 * 8))
            [(word pc,LENGTH edwards25519_decode_alt_windows_tmc); (word_sub stackpointer (word 336),344)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) edwards25519_decode_alt_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; c] s /\
                  read (memory :> bytes(c,32)) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  C_RETURN s = word(bitval(~ed25519_validencode n)) /\
                  (ed25519_validencode n
                   ==> bignum_pair_from_memory(z,4) s =
                       paired (modular_encode (256,p_25519))
                              (ed25519_decode n)))
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 8);
                    memory :> bytes(word_sub stackpointer (word 336),336)])`,
  let WINDOWS_EDWARDS25519_DECODE_ALT_EXEC =
    X86_MK_EXEC_RULE edwards25519_decode_alt_windows_tmc
  and subth =
   X86_SIMD_SHARPEN_RULE
    (REWRITE_RULE[fst EDWARDS25519_DECODE_ALT_EXEC]
      EDWARDS25519_DECODE_ALT_NOIBT_SUBROUTINE_CORRECT)
    (X86_ADD_RETURN_STACK_TAC
      EDWARDS25519_DECODE_ALT_EXEC EDWARDS25519_DECODE_ALT_CORRECT
      `[RBX; RBP; R12; R13; R14; R15]` 312) in
  REWRITE_TAC[fst WINDOWS_EDWARDS25519_DECODE_ALT_EXEC] THEN
  REPLICATE_TAC 4 GEN_TAC THEN WORD_FORALL_OFFSET_TAC 336 THEN
  REWRITE_TAC[ALL; WINDOWS_C_ARGUMENTS; SOME_FLAGS; C_RETURN;
              WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN REPEAT STRIP_TAC THEN
  ENSURES_PRESERVED_TAC "rsi_init" `RSI` THEN
  ENSURES_PRESERVED_TAC "rdi_init" `RDI` THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC WINDOWS_EDWARDS25519_DECODE_ALT_EXEC (1--5) THEN
  X86_SUBROUTINE_SIM_TAC
   (edwards25519_decode_alt_windows_tmc,
    WINDOWS_EDWARDS25519_DECODE_ALT_EXEC,
    0x10,edwards25519_decode_alt_tmc,subth)
     [`read RDI s`; `read RSI s`;
      `read (memory :> bytes (read RSI s,32)) s`;
      `pc + 0x10`; `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]
      6 THEN
  X86_STEPS_TAC WINDOWS_EDWARDS25519_DECODE_ALT_EXEC (7--9) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;

let EDWARDS25519_DECODE_ALT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z c n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 336),336))
            [(word pc,LENGTH edwards25519_decode_alt_windows_mc); (z,8 * 8); (c,8 * 4)] /\
        ALL (nonoverlapping (z,8 * 8))
            [(word pc,LENGTH edwards25519_decode_alt_windows_mc); (word_sub stackpointer (word 336),344)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) edwards25519_decode_alt_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; c] s /\
                  read (memory :> bytes(c,32)) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  C_RETURN s = word(bitval(~ed25519_validencode n)) /\
                  (ed25519_validencode n
                   ==> bignum_pair_from_memory(z,4) s =
                       paired (modular_encode (256,p_25519))
                              (ed25519_decode n)))
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 8);
                    memory :> bytes(word_sub stackpointer (word 336),336)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE EDWARDS25519_DECODE_ALT_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

