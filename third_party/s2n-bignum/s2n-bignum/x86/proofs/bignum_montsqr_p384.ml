(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* MULX-based Montgomery squaring modulo p_384.                              *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/p384/bignum_montsqr_p384.o";;
 ****)

let bignum_montsqr_p384_mc =
  define_assert_from_elf "bignum_montsqr_p384_mc" "x86/p384/bignum_montsqr_p384.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x53;                    (* PUSH (% rbx) *)
  0x55;                    (* PUSH (% rbp) *)
  0x41; 0x54;              (* PUSH (% r12) *)
  0x41; 0x55;              (* PUSH (% r13) *)
  0x41; 0x56;              (* PUSH (% r14) *)
  0x41; 0x57;              (* PUSH (% r15) *)
  0x48; 0x8b; 0x16;        (* MOV (% rdx) (Memop Quadword (%% (rsi,0))) *)
  0xc4; 0x62; 0xb3; 0xf6; 0x56; 0x08;
                           (* MULX4 (% r10,% r9) (% rdx,Memop Quadword (%% (rsi,8))) *)
  0xc4; 0x62; 0xa3; 0xf6; 0x66; 0x18;
                           (* MULX4 (% r12,% r11) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0xc4; 0x62; 0x93; 0xf6; 0x76; 0x28;
                           (* MULX4 (% r14,% r13) (% rdx,Memop Quadword (%% (rsi,40))) *)
  0x48; 0x8b; 0x56; 0x18;  (* MOV (% rdx) (Memop Quadword (%% (rsi,24))) *)
  0xc4; 0xe2; 0x83; 0xf6; 0x4e; 0x20;
                           (* MULX4 (% rcx,% r15) (% rdx,Memop Quadword (%% (rsi,32))) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0x48; 0x8b; 0x56; 0x10;  (* MOV (% rdx) (Memop Quadword (%% (rsi,16))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1e;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x08;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0x48; 0x8b; 0x56; 0x08;  (* MOV (% rdx) (Memop Quadword (%% (rsi,8))) *)
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
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xfd;
                           (* ADCX (% r15) (% rbp) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xcd;
                           (* ADOX (% rcx) (% rbp) *)
  0x48; 0x11; 0xe9;        (* ADC (% rcx) (% rbp) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0x48; 0x8b; 0x56; 0x20;  (* MOV (% rdx) (Memop Quadword (%% (rsi,32))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1e;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0x48; 0x8b; 0x56; 0x10;  (* MOV (% rdx) (Memop Quadword (%% (rsi,16))) *)
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
  0xc4; 0xe2; 0xfb; 0xf6; 0x56; 0x28;
                           (* MULX4 (% rdx,% rax) (% rdx,Memop Quadword (%% (rsi,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xca;
                           (* ADOX (% rcx) (% rdx) *)
  0x48; 0x8b; 0x56; 0x28;  (* MOV (% rdx) (Memop Quadword (%% (rsi,40))) *)
  0xc4; 0xe2; 0xe3; 0xf6; 0x6e; 0x20;
                           (* MULX4 (% rbp,% rbx) (% rdx,Memop Quadword (%% (rsi,32))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x56; 0x18;
                           (* MULX4 (% rdx,% rax) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% rcx) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xda;
                           (* ADOX (% rbx) (% rdx) *)
  0xb8; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 0)) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% rbx) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADOX (% rbp) (% rax) *)
  0x48; 0x11; 0xc5;        (* ADC (% rbp) (% rax) *)
  0x48; 0x31; 0xc0;        (* XOR (% rax) (% rax) *)
  0x48; 0x8b; 0x16;        (* MOV (% rdx) (Memop Quadword (%% (rsi,0))) *)
  0xc4; 0xe2; 0xbb; 0xf6; 0x06;
                           (* MULX4 (% rax,% r8) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xc9;
                           (* ADCX (% r9) (% r9) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADOX (% r9) (% rax) *)
  0x48; 0x8b; 0x56; 0x08;  (* MOV (% rdx) (Memop Quadword (%% (rsi,8))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0xd2;
                           (* MULX4 (% rdx,% rax) (% rdx,% rdx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xd2;
                           (* ADCX (% r10) (% r10) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADOX (% r10) (% rax) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADCX (% r11) (% r11) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xda;
                           (* ADOX (% r11) (% rdx) *)
  0x48; 0x8b; 0x56; 0x10;  (* MOV (% rdx) (Memop Quadword (%% (rsi,16))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0xd2;
                           (* MULX4 (% rdx,% rax) (% rdx,% rdx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xe4;
                           (* ADCX (% r12) (% r12) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADOX (% r12) (% rax) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xed;
                           (* ADCX (% r13) (% r13) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xea;
                           (* ADOX (% r13) (% rdx) *)
  0x48; 0x8b; 0x56; 0x18;  (* MOV (% rdx) (Memop Quadword (%% (rsi,24))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0xd2;
                           (* MULX4 (% rdx,% rax) (% rdx,% rdx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xf6;
                           (* ADCX (% r14) (% r14) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADOX (% r14) (% rax) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xff;
                           (* ADCX (% r15) (% r15) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfa;
                           (* ADOX (% r15) (% rdx) *)
  0x48; 0x8b; 0x56; 0x20;  (* MOV (% rdx) (Memop Quadword (%% (rsi,32))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0xd2;
                           (* MULX4 (% rdx,% rax) (% rdx,% rdx) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xc9;
                           (* ADCX (% rcx) (% rcx) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADOX (% rcx) (% rax) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADCX (% rbx) (% rbx) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xda;
                           (* ADOX (% rbx) (% rdx) *)
  0x48; 0x8b; 0x56; 0x28;  (* MOV (% rdx) (Memop Quadword (%% (rsi,40))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0xf2;
                           (* MULX4 (% rsi,% rax) (% rdx,% rdx) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xed;
                           (* ADCX (% rbp) (% rbp) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADOX (% rbp) (% rax) *)
  0xb8; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 0)) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% rsi) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADOX (% rsi) (% rax) *)
  0x48; 0x89; 0x1f;        (* MOV (Memop Quadword (%% (rdi,0))) (% rbx) *)
  0x4c; 0x89; 0xc2;        (* MOV (% rdx) (% r8) *)
  0x48; 0xc1; 0xe2; 0x20;  (* SHL (% rdx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xc2;        (* ADD (% rdx) (% r8) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0xc4; 0xe2; 0xbb; 0xf6; 0xc0;
                           (* MULX4 (% rax,% r8) (% rdx,% rax) *)
  0xbb; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% ebx) (Imm32 (word 4294967295)) *)
  0xc4; 0x62; 0xe3; 0xf6; 0xc3;
                           (* MULX4 (% r8,% rbx) (% rdx,% rbx) *)
  0x48; 0x01; 0xd8;        (* ADD (% rax) (% rbx) *)
  0x49; 0x11; 0xd0;        (* ADC (% r8) (% rdx) *)
  0xbb; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% ebx) (Imm32 (word 0)) *)
  0x48; 0x11; 0xdb;        (* ADC (% rbx) (% rbx) *)
  0x49; 0x29; 0xc1;        (* SUB (% r9) (% rax) *)
  0x4d; 0x19; 0xc2;        (* SBB (% r10) (% r8) *)
  0x49; 0x19; 0xdb;        (* SBB (% r11) (% rbx) *)
  0x49; 0x83; 0xdc; 0x00;  (* SBB (% r12) (Imm8 (word 0)) *)
  0x49; 0x83; 0xdd; 0x00;  (* SBB (% r13) (Imm8 (word 0)) *)
  0x49; 0x89; 0xd0;        (* MOV (% r8) (% rdx) *)
  0x49; 0x83; 0xd8; 0x00;  (* SBB (% r8) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xca;        (* MOV (% rdx) (% r9) *)
  0x48; 0xc1; 0xe2; 0x20;  (* SHL (% rdx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xca;        (* ADD (% rdx) (% r9) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0xc4; 0xe2; 0xb3; 0xf6; 0xc0;
                           (* MULX4 (% rax,% r9) (% rdx,% rax) *)
  0xbb; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% ebx) (Imm32 (word 4294967295)) *)
  0xc4; 0x62; 0xe3; 0xf6; 0xcb;
                           (* MULX4 (% r9,% rbx) (% rdx,% rbx) *)
  0x48; 0x01; 0xd8;        (* ADD (% rax) (% rbx) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0xbb; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% ebx) (Imm32 (word 0)) *)
  0x48; 0x11; 0xdb;        (* ADC (% rbx) (% rbx) *)
  0x49; 0x29; 0xc2;        (* SUB (% r10) (% rax) *)
  0x4d; 0x19; 0xcb;        (* SBB (% r11) (% r9) *)
  0x49; 0x19; 0xdc;        (* SBB (% r12) (% rbx) *)
  0x49; 0x83; 0xdd; 0x00;  (* SBB (% r13) (Imm8 (word 0)) *)
  0x49; 0x83; 0xd8; 0x00;  (* SBB (% r8) (Imm8 (word 0)) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x49; 0x83; 0xd9; 0x00;  (* SBB (% r9) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xd2;        (* MOV (% rdx) (% r10) *)
  0x48; 0xc1; 0xe2; 0x20;  (* SHL (% rdx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xd2;        (* ADD (% rdx) (% r10) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0xc4; 0xe2; 0xab; 0xf6; 0xc0;
                           (* MULX4 (% rax,% r10) (% rdx,% rax) *)
  0xbb; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% ebx) (Imm32 (word 4294967295)) *)
  0xc4; 0x62; 0xe3; 0xf6; 0xd3;
                           (* MULX4 (% r10,% rbx) (% rdx,% rbx) *)
  0x48; 0x01; 0xd8;        (* ADD (% rax) (% rbx) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0xbb; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% ebx) (Imm32 (word 0)) *)
  0x48; 0x11; 0xdb;        (* ADC (% rbx) (% rbx) *)
  0x49; 0x29; 0xc3;        (* SUB (% r11) (% rax) *)
  0x4d; 0x19; 0xd4;        (* SBB (% r12) (% r10) *)
  0x49; 0x19; 0xdd;        (* SBB (% r13) (% rbx) *)
  0x49; 0x83; 0xd8; 0x00;  (* SBB (% r8) (Imm8 (word 0)) *)
  0x49; 0x83; 0xd9; 0x00;  (* SBB (% r9) (Imm8 (word 0)) *)
  0x49; 0x89; 0xd2;        (* MOV (% r10) (% rdx) *)
  0x49; 0x83; 0xda; 0x00;  (* SBB (% r10) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xda;        (* MOV (% rdx) (% r11) *)
  0x48; 0xc1; 0xe2; 0x20;  (* SHL (% rdx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xda;        (* ADD (% rdx) (% r11) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0xc4; 0xe2; 0xa3; 0xf6; 0xc0;
                           (* MULX4 (% rax,% r11) (% rdx,% rax) *)
  0xbb; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% ebx) (Imm32 (word 4294967295)) *)
  0xc4; 0x62; 0xe3; 0xf6; 0xdb;
                           (* MULX4 (% r11,% rbx) (% rdx,% rbx) *)
  0x48; 0x01; 0xd8;        (* ADD (% rax) (% rbx) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0xbb; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% ebx) (Imm32 (word 0)) *)
  0x48; 0x11; 0xdb;        (* ADC (% rbx) (% rbx) *)
  0x49; 0x29; 0xc4;        (* SUB (% r12) (% rax) *)
  0x4d; 0x19; 0xdd;        (* SBB (% r13) (% r11) *)
  0x49; 0x19; 0xd8;        (* SBB (% r8) (% rbx) *)
  0x49; 0x83; 0xd9; 0x00;  (* SBB (% r9) (Imm8 (word 0)) *)
  0x49; 0x83; 0xda; 0x00;  (* SBB (% r10) (Imm8 (word 0)) *)
  0x49; 0x89; 0xd3;        (* MOV (% r11) (% rdx) *)
  0x49; 0x83; 0xdb; 0x00;  (* SBB (% r11) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xe2;        (* MOV (% rdx) (% r12) *)
  0x48; 0xc1; 0xe2; 0x20;  (* SHL (% rdx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xe2;        (* ADD (% rdx) (% r12) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0xc4; 0xe2; 0x9b; 0xf6; 0xc0;
                           (* MULX4 (% rax,% r12) (% rdx,% rax) *)
  0xbb; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% ebx) (Imm32 (word 4294967295)) *)
  0xc4; 0x62; 0xe3; 0xf6; 0xe3;
                           (* MULX4 (% r12,% rbx) (% rdx,% rbx) *)
  0x48; 0x01; 0xd8;        (* ADD (% rax) (% rbx) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0xbb; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% ebx) (Imm32 (word 0)) *)
  0x48; 0x11; 0xdb;        (* ADC (% rbx) (% rbx) *)
  0x49; 0x29; 0xc5;        (* SUB (% r13) (% rax) *)
  0x4d; 0x19; 0xe0;        (* SBB (% r8) (% r12) *)
  0x49; 0x19; 0xd9;        (* SBB (% r9) (% rbx) *)
  0x49; 0x83; 0xda; 0x00;  (* SBB (% r10) (Imm8 (word 0)) *)
  0x49; 0x83; 0xdb; 0x00;  (* SBB (% r11) (Imm8 (word 0)) *)
  0x49; 0x89; 0xd4;        (* MOV (% r12) (% rdx) *)
  0x49; 0x83; 0xdc; 0x00;  (* SBB (% r12) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xea;        (* MOV (% rdx) (% r13) *)
  0x48; 0xc1; 0xe2; 0x20;  (* SHL (% rdx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xea;        (* ADD (% rdx) (% r13) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0xc4; 0xe2; 0x93; 0xf6; 0xc0;
                           (* MULX4 (% rax,% r13) (% rdx,% rax) *)
  0xbb; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% ebx) (Imm32 (word 4294967295)) *)
  0xc4; 0x62; 0xe3; 0xf6; 0xeb;
                           (* MULX4 (% r13,% rbx) (% rdx,% rbx) *)
  0x48; 0x01; 0xd8;        (* ADD (% rax) (% rbx) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0xbb; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% ebx) (Imm32 (word 0)) *)
  0x48; 0x11; 0xdb;        (* ADC (% rbx) (% rbx) *)
  0x49; 0x29; 0xc0;        (* SUB (% r8) (% rax) *)
  0x4d; 0x19; 0xe9;        (* SBB (% r9) (% r13) *)
  0x49; 0x19; 0xda;        (* SBB (% r10) (% rbx) *)
  0x49; 0x83; 0xdb; 0x00;  (* SBB (% r11) (Imm8 (word 0)) *)
  0x49; 0x83; 0xdc; 0x00;  (* SBB (% r12) (Imm8 (word 0)) *)
  0x49; 0x89; 0xd5;        (* MOV (% r13) (% rdx) *)
  0x49; 0x83; 0xdd; 0x00;  (* SBB (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x1f;        (* MOV (% rbx) (Memop Quadword (%% (rdi,0))) *)
  0x4d; 0x01; 0xc6;        (* ADD (% r14) (% r8) *)
  0x4d; 0x11; 0xcf;        (* ADC (% r15) (% r9) *)
  0x4c; 0x11; 0xd1;        (* ADC (% rcx) (% r10) *)
  0x4c; 0x11; 0xdb;        (* ADC (% rbx) (% r11) *)
  0x4c; 0x11; 0xe5;        (* ADC (% rbp) (% r12) *)
  0x4c; 0x11; 0xee;        (* ADC (% rsi) (% r13) *)
  0x41; 0xb8; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% r8d) (Imm32 (word 0)) *)
  0x4d; 0x11; 0xc0;        (* ADC (% r8) (% r8) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x4d; 0x31; 0xe4;        (* XOR (% r12) (% r12) *)
  0x4d; 0x31; 0xed;        (* XOR (% r13) (% r13) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0x4c; 0x01; 0xf0;        (* ADD (% rax) (% r14) *)
  0x41; 0xb9; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r9d) (Imm32 (word 4294967295)) *)
  0x4d; 0x11; 0xf9;        (* ADC (% r9) (% r15) *)
  0x41; 0xba; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% r10d) (Imm32 (word 1)) *)
  0x49; 0x11; 0xca;        (* ADC (% r10) (% rcx) *)
  0x49; 0x11; 0xdb;        (* ADC (% r11) (% rbx) *)
  0x49; 0x11; 0xec;        (* ADC (% r12) (% rbp) *)
  0x49; 0x11; 0xf5;        (* ADC (% r13) (% rsi) *)
  0x49; 0x83; 0xd0; 0x00;  (* ADC (% r8) (Imm8 (word 0)) *)
  0x4c; 0x0f; 0x45; 0xf0;  (* CMOVNE (% r14) (% rax) *)
  0x4d; 0x0f; 0x45; 0xf9;  (* CMOVNE (% r15) (% r9) *)
  0x49; 0x0f; 0x45; 0xca;  (* CMOVNE (% rcx) (% r10) *)
  0x49; 0x0f; 0x45; 0xdb;  (* CMOVNE (% rbx) (% r11) *)
  0x49; 0x0f; 0x45; 0xec;  (* CMOVNE (% rbp) (% r12) *)
  0x49; 0x0f; 0x45; 0xf5;  (* CMOVNE (% rsi) (% r13) *)
  0x4c; 0x89; 0x37;        (* MOV (Memop Quadword (%% (rdi,0))) (% r14) *)
  0x4c; 0x89; 0x7f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% r15) *)
  0x48; 0x89; 0x4f; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% rcx) *)
  0x48; 0x89; 0x5f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% rbx) *)
  0x48; 0x89; 0x6f; 0x20;  (* MOV (Memop Quadword (%% (rdi,32))) (% rbp) *)
  0x48; 0x89; 0x77; 0x28;  (* MOV (Memop Quadword (%% (rdi,40))) (% rsi) *)
  0x41; 0x5f;              (* POP (% r15) *)
  0x41; 0x5e;              (* POP (% r14) *)
  0x41; 0x5d;              (* POP (% r13) *)
  0x41; 0x5c;              (* POP (% r12) *)
  0x5d;                    (* POP (% rbp) *)
  0x5b;                    (* POP (% rbx) *)
  0xc3                     (* RET *)
];;

let bignum_montsqr_p384_tmc = define_trimmed "bignum_montsqr_p384_tmc" bignum_montsqr_p384_mc;;

let BIGNUM_MONTSQR_P384_EXEC = X86_MK_CORE_EXEC_RULE bignum_montsqr_p384_tmc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_384 = new_definition `p_384 = 39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319`;;

let swlemma = WORD_RULE
  `word_add (word_shl x 32) x:int64 = word(4294967297 * val x)`;;

let mmlemma = prove
 (`!h (l:int64) (x:int64).
        &2 pow 64 * &h + &(val(l:int64)):real =
        &(val(word(4294967297 * val x):int64)) * &18446744069414584321
        ==> &2 pow 64 * &h + &(val(x:int64)):real =
            &(val(word(4294967297 * val x):int64)) * &18446744069414584321`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
  REPEAT STRIP_TAC THEN FIRST_ASSUM(SUBST1_TAC o SYM) THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM VAL_CONG; DIMINDEX_64] THEN FIRST_X_ASSUM(MATCH_MP_TAC o
   MATCH_MP (NUMBER_RULE
    `p * h + l:num = y ==> (y == x) (mod p) ==> (x == l) (mod p)`)) THEN
  REWRITE_TAC[CONG; VAL_WORD; DIMINDEX_64] THEN CONV_TAC MOD_DOWN_CONV THEN
  REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC(NUMBER_RULE
   `(a * b == 1) (mod p) ==> ((a * x) * b == x) (mod p)`) THEN
  REWRITE_TAC[CONG] THEN CONV_TAC NUM_REDUCE_CONV);;

let BIGNUM_MONTSQR_P384_CORRECT = time prove
 (`!z x a pc.
        nonoverlapping (word pc,0x423) (z,8 * 6)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST bignum_montsqr_p384_tmc) /\
                  read RIP s = word(pc + 0x0a) /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = a)
             (\s. read RIP s = word (pc + 0x418) /\
                  (a EXP 2 <= 2 EXP 384 * p_384
                   ==> bignum_from_memory (z,6) s =
                       (inverse_mod p_384 (2 EXP 384) * a EXP 2) MOD p_384))
             (MAYCHANGE [RIP; RSI; RAX; RBX; RBP; RCX; RDX;
                         R8; R9; R10; R11; R12; R13; R14; R15] ,,
              MAYCHANGE [memory :> bytes(z,8 * 6)] ,,
              MAYCHANGE SOME_FLAGS)`,
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `a:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the a EXP 2 <= 2 EXP 384 * p_384  assumption ***)

  ASM_CASES_TAC `a EXP 2 <= 2 EXP 384 * p_384` THENL
   [ASM_REWRITE_TAC[]; X86_SIM_TAC BIGNUM_MONTSQR_P384_EXEC (1--230)] THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,6) s0` THEN

  (*** Simulate the main squaring and 6-fold Montgomery reduction ***)

  MAP_EVERY (fun s ->
    X86_SINGLE_STEP_TAC BIGNUM_MONTSQR_P384_EXEC s THEN
    RULE_ASSUM_TAC(REWRITE_RULE[swlemma]) THEN
    TRY(ACCUMULATE_ARITH_TAC s) THEN CLARIFY_TAC)
   (statenames "s" (1--205)) THEN

  (*** Do the congruential reasoning on the chosen multipliers ***)

  RULE_ASSUM_TAC(fun th -> try MATCH_MP mmlemma th with Failure _ -> th) THEN

  (*** Derive the main property of the pre-reduced form, which we call t ***)

  ABBREV_TAC
   `t = bignum_of_wordlist
         [sum_s198; sum_s199; sum_s200; sum_s201; sum_s202; sum_s203;
          word (bitval carry_s203)]` THEN

  SUBGOAL_THEN
   `t < 2 * p_384 /\ (2 EXP 384 * t == a EXP 2) (mod p_384)`
  STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_BITVAL]) THEN
    ACCUMULATOR_POP_ASSUM_LIST
     (STRIP_ASSUME_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ARITH_RULE
        `ab <= 2 EXP 384 * p
         ==> 2 EXP 384 * t < ab + 2 EXP 384 * p ==> t < 2 * p`)) THEN
      MAP_EVERY EXPAND_TAC ["a"; "t"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      REWRITE_TAC[p_384; REAL_ARITH `a:real < b + c <=> a - b < c`] THEN
      ASM_REWRITE_TAC[VAL_WORD_BITVAL] THEN BOUNDER_TAC[];
      REWRITE_TAC[REAL_CONGRUENCE; p_384] THEN CONV_TAC NUM_REDUCE_CONV THEN
      MAP_EVERY EXPAND_TAC ["a"; "t"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      ASM_REWRITE_TAC[VAL_WORD_BITVAL] THEN REAL_INTEGER_TAC];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Final correction stage ***)

  X86_ACCSTEPS_TAC BIGNUM_MONTSQR_P384_EXEC
   [210;212;214;215;216;217] (206--230) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  TRANS_TAC EQ_TRANS `t MOD p_384` THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[GSYM CONG] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (NUMBER_RULE
       `(e * t == a EXP 2) (mod p)
        ==> (e * i == 1) (mod p) ==> (t == i * a EXP 2) (mod p)`)) THEN
    REWRITE_TAC[INVERSE_MOD_RMUL_EQ; COPRIME_REXP; COPRIME_2] THEN
    REWRITE_TAC[p_384] THEN CONV_TAC NUM_REDUCE_CONV] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  MAP_EVERY EXISTS_TAC
   [`384`; `if t < p_384 then &t:real else &t - &p_384`] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN BOUNDER_TAC[];
    REWRITE_TAC[p_384] THEN ARITH_TAC;
    REWRITE_TAC[p_384] THEN ARITH_TAC;
    ALL_TAC;
    ASM_SIMP_TAC[MOD_CASES] THEN
    GEN_REWRITE_TAC LAND_CONV [COND_RAND] THEN
    SIMP_TAC[REAL_OF_NUM_SUB; GSYM NOT_LT]] THEN
  SUBGOAL_THEN
   `~(val(word_add (word(bitval carry_s203))
                   (word(bitval carry_s217)):int64) = 0) <=>
    p_384 <= t`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[VAL_WORD_ADD_CASES; VAL_WORD_BITVAL; DIMINDEX_64] THEN
    SIMP_TAC[BITVAL_BOUND; ARITH_RULE
     `b <= 1 /\ c <= 1 ==> b + c < 2 EXP 64`] THEN
    TRANS_TAC EQ_TRANS `2 EXP 384 <= t + (2 EXP 384 - p_384)` THEN
    CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[p_384] THEN ARITH_TAC] THEN
    TRANS_TAC EQ_TRANS
     `2 EXP 384
      <= 2 EXP 384 * (bitval carry_s203 + bitval carry_s217) +
         bignum_of_wordlist
          [sum_s210;sum_s212;sum_s214;sum_s215;sum_s216;sum_s217]` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[TAUT `(~p <=> q) <=> (~p ==> q) /\ (p ==> ~q)`] THEN
      CONJ_TAC THENL [ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; NOT_LE] THEN
      W(MP_TAC o PART_MATCH lhand
        BIGNUM_OF_WORDLIST_BOUND_LENGTH o lhand o snd) THEN
      REWRITE_TAC[LENGTH] THEN ARITH_TAC;
      AP_TERM_TAC THEN EXPAND_TAC "t" THEN
      REWRITE_TAC[p_384; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[VAL_WORD_BITVAL] THEN CONV_TAC REAL_RING];
    REWRITE_TAC[GSYM NOT_LT; COND_SWAP]] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "t" THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_384] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES; VAL_WORD_BITVAL] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let BIGNUM_MONTSQR_P384_NOIBT_SUBROUTINE_CORRECT = time prove
 (`!z x a pc stackpointer returnaddress.
        nonoverlapping (z,8 * 6) (word_sub stackpointer (word 48),56) /\
        ALL (nonoverlapping (word_sub stackpointer (word 48),48))
            [(word pc,LENGTH bignum_montsqr_p384_tmc); (x,8 * 6)] /\
        nonoverlapping (word pc,LENGTH bignum_montsqr_p384_tmc) (z,8 * 6)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_montsqr_p384_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (a EXP 2 <= 2 EXP 384 * p_384
                   ==> bignum_from_memory (z,6) s =
                       (inverse_mod p_384 (2 EXP 384) * a EXP 2) MOD p_384))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 6);
                     memory :> bytes(word_sub stackpointer (word 48),48)])`,
  X86_PROMOTE_RETURN_STACK_TAC
   bignum_montsqr_p384_tmc BIGNUM_MONTSQR_P384_CORRECT
   `[RBX; RBP; R12; R13; R14; R15]` 48);;

let BIGNUM_MONTSQR_P384_SUBROUTINE_CORRECT = time prove
 (`!z x a pc stackpointer returnaddress.
        nonoverlapping (z,8 * 6) (word_sub stackpointer (word 48),56) /\
        ALL (nonoverlapping (word_sub stackpointer (word 48),48))
            [(word pc,LENGTH bignum_montsqr_p384_mc); (x,8 * 6)] /\
        nonoverlapping (word pc,LENGTH bignum_montsqr_p384_mc) (z,8 * 6)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_montsqr_p384_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (a EXP 2 <= 2 EXP 384 * p_384
                   ==> bignum_from_memory (z,6) s =
                       (inverse_mod p_384 (2 EXP 384) * a EXP 2) MOD p_384))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 6);
                     memory :> bytes(word_sub stackpointer (word 48),48)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_MONTSQR_P384_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Show that it also works as "almost-Montgomery" if desired. That is, even  *)
(* without the further range assumption on inputs we still get a congruence. *)
(* But the output, still 384 bits, may then not be fully reduced mod p_384.  *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_AMONTSQR_P384_CORRECT = time prove
 (`!z x a pc.
        nonoverlapping (word pc,0x423) (z,8 * 6)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST bignum_montsqr_p384_tmc) /\
                  read RIP s = word(pc + 0x0a) /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = a)
             (\s. read RIP s = word (pc + 0x418) /\
                  (bignum_from_memory (z,6) s ==
                   inverse_mod p_384 (2 EXP 384) * a EXP 2) (mod p_384))
             (MAYCHANGE [RIP; RSI; RAX; RBX; RBP; RCX; RDX;
                         R8; R9; R10; R11; R12; R13; R14; R15] ,,
              MAYCHANGE [memory :> bytes(z,8 * 6)] ,,
              MAYCHANGE SOME_FLAGS)`,
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `a:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,6) s0` THEN

  (*** Simulate the main squaring and 6-fold Montgomery reduction ***)

  MAP_EVERY (fun s ->
    X86_SINGLE_STEP_TAC BIGNUM_MONTSQR_P384_EXEC s THEN
    RULE_ASSUM_TAC(REWRITE_RULE[swlemma]) THEN
    TRY(ACCUMULATE_ARITH_TAC s) THEN CLARIFY_TAC)
   (statenames "s" (1--205)) THEN

  (*** Do the congruential reasoning on the chosen multipliers ***)

  RULE_ASSUM_TAC(fun th -> try MATCH_MP mmlemma th with Failure _ -> th) THEN

  (*** Derive the main property of the pre-reduced form, which we call t ***)

  ABBREV_TAC
   `t = bignum_of_wordlist
         [sum_s198; sum_s199; sum_s200; sum_s201; sum_s202; sum_s203;
          word (bitval carry_s203)]` THEN
  SUBGOAL_THEN
   `t < 2 EXP 384 + p_384 /\ (2 EXP 384 * t == a EXP 2) (mod p_384)`
  STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_BITVAL]) THEN
    ACCUMULATOR_POP_ASSUM_LIST
     (STRIP_ASSUME_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE
       `2 EXP 384 * t <= (2 EXP 384 - 1) EXP 2 + (2 EXP 384 - 1) * p
        ==> t < 2 EXP 384 + p`) THEN
      REWRITE_TAC[p_384] THEN CONV_TAC NUM_REDUCE_CONV THEN
      MAP_EVERY EXPAND_TAC ["a"; "t"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      REWRITE_TAC[p_384; REAL_ARITH `a:real < b + c <=> a - b < c`] THEN
      ASM_REWRITE_TAC[VAL_WORD_BITVAL] THEN BOUNDER_TAC[];
      REWRITE_TAC[REAL_CONGRUENCE; p_384] THEN CONV_TAC NUM_REDUCE_CONV THEN
      MAP_EVERY EXPAND_TAC ["a"; "t"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      ASM_REWRITE_TAC[VAL_WORD_BITVAL] THEN REAL_INTEGER_TAC];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Final correction stage ***)

  X86_ACCSTEPS_TAC BIGNUM_MONTSQR_P384_EXEC
   [210;212;214;215;216;217] (206--230) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (NUMBER_RULE
       `(e * t == ab) (mod p)
        ==> (e * i == 1) (mod p) /\ (s == t) (mod p)
            ==> (s == i * ab) (mod p)`)) THEN
  REWRITE_TAC[INVERSE_MOD_RMUL_EQ; COPRIME_REXP; COPRIME_2] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[p_384] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN
   `~(val(word_add (word(bitval carry_s203))
                   (word(bitval carry_s217)):int64) = 0) <=>
    p_384 <= t`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[VAL_WORD_ADD_CASES; VAL_WORD_BITVAL; DIMINDEX_64] THEN
    SIMP_TAC[BITVAL_BOUND; ARITH_RULE
     `b <= 1 /\ c <= 1 ==> b + c < 2 EXP 64`] THEN
    TRANS_TAC EQ_TRANS `2 EXP 384 <= t + (2 EXP 384 - p_384)` THEN
    CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[p_384] THEN ARITH_TAC] THEN
    TRANS_TAC EQ_TRANS
     `2 EXP 384
      <= 2 EXP 384 * (bitval carry_s203 + bitval carry_s217) +
         bignum_of_wordlist
          [sum_s210;sum_s212;sum_s214;sum_s215;sum_s216;sum_s217]` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[TAUT `(~p <=> q) <=> (~p ==> q) /\ (p ==> ~q)`] THEN
      CONJ_TAC THENL [ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; NOT_LE] THEN
      W(MP_TAC o PART_MATCH lhand
        BIGNUM_OF_WORDLIST_BOUND_LENGTH o lhand o snd) THEN
      REWRITE_TAC[LENGTH] THEN ARITH_TAC;
      AP_TERM_TAC THEN EXPAND_TAC "t" THEN
      REWRITE_TAC[p_384; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[VAL_WORD_BITVAL] THEN CONV_TAC REAL_RING];
    REWRITE_TAC[GSYM NOT_LT; COND_SWAP]] THEN
  MATCH_MP_TAC(NUMBER_RULE `!b:num. x + b * p = y ==> (x == y) (mod p)`) THEN
  EXISTS_TAC `bitval(p_384 <= t)` THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a + b:real = c <=> c - b = a`] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`384`; `&0:real`] THEN CONJ_TAC THENL
   [UNDISCH_TAC `t < 2 EXP 384 + p_384` THEN
    REWRITE_TAC[bitval; p_384; GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC;
    REWRITE_TAC[INTEGER_CLOSED]] THEN
  CONJ_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV BIGNUM_EXPAND_CONV) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_EXPAND_CONV) THEN
  REWRITE_TAC[bitval] THEN COND_CASES_TAC THEN
  EXPAND_TAC "t" THEN REWRITE_TAC[bignum_of_wordlist] THEN
  ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  ACCUMULATOR_POP_ASSUM_LIST (MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[BITVAL_CLAUSES; p_384] THEN
  CONV_TAC WORD_REDUCE_CONV THEN REAL_INTEGER_TAC);;

let BIGNUM_AMONTSQR_P384_NOIBT_SUBROUTINE_CORRECT = time prove
 (`!z x a pc stackpointer returnaddress.
        nonoverlapping (z,8 * 6) (word_sub stackpointer (word 48),56) /\
        ALL (nonoverlapping (word_sub stackpointer (word 48),48))
            [(word pc,LENGTH bignum_montsqr_p384_tmc); (x,8 * 6)] /\
        nonoverlapping (word pc,LENGTH bignum_montsqr_p384_tmc) (z,8 * 6)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_montsqr_p384_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (bignum_from_memory (z,6) s ==
                   inverse_mod p_384 (2 EXP 384) * a EXP 2) (mod p_384))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 6);
                     memory :> bytes(word_sub stackpointer (word 48),48)])`,
  X86_PROMOTE_RETURN_STACK_TAC
   bignum_montsqr_p384_tmc BIGNUM_AMONTSQR_P384_CORRECT
   `[RBX; RBP; R12; R13; R14; R15]` 48);;

let BIGNUM_AMONTSQR_P384_SUBROUTINE_CORRECT = time prove
 (`!z x a pc stackpointer returnaddress.
        nonoverlapping (z,8 * 6) (word_sub stackpointer (word 48),56) /\
        ALL (nonoverlapping (word_sub stackpointer (word 48),48))
            [(word pc,LENGTH bignum_montsqr_p384_mc); (x,8 * 6)] /\
        nonoverlapping (word pc,LENGTH bignum_montsqr_p384_mc) (z,8 * 6)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_montsqr_p384_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (bignum_from_memory (z,6) s ==
                   inverse_mod p_384 (2 EXP 384) * a EXP 2) (mod p_384))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 6);
                     memory :> bytes(word_sub stackpointer (word 48),48)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_AMONTSQR_P384_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_montsqr_p384_windows_mc = define_from_elf
   "bignum_montsqr_p384_windows_mc" "x86/p384/bignum_montsqr_p384.obj";;

let bignum_montsqr_p384_windows_tmc = define_trimmed "bignum_montsqr_p384_windows_tmc" bignum_montsqr_p384_windows_mc;;

let BIGNUM_MONTSQR_P384_NOIBT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x a pc stackpointer returnaddress.
        nonoverlapping (z,8 * 6) (word_sub stackpointer (word 64),72) /\
        ALL (nonoverlapping (word_sub stackpointer (word 64),64))
            [(word pc,LENGTH bignum_montsqr_p384_windows_tmc); (x,8 * 6)] /\
        nonoverlapping (word pc,LENGTH bignum_montsqr_p384_windows_tmc) (z,8 * 6)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_montsqr_p384_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (a EXP 2 <= 2 EXP 384 * p_384
                   ==> bignum_from_memory (z,6) s =
                       (inverse_mod p_384 (2 EXP 384) * a EXP 2) MOD p_384))
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 6);
                     memory :> bytes(word_sub stackpointer (word 64),64)])`,
  WINDOWS_X86_WRAP_STACK_TAC
   bignum_montsqr_p384_windows_tmc bignum_montsqr_p384_tmc
   BIGNUM_MONTSQR_P384_CORRECT `[RBX; RBP; R12; R13; R14; R15]` 48);;

let BIGNUM_MONTSQR_P384_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x a pc stackpointer returnaddress.
        nonoverlapping (z,8 * 6) (word_sub stackpointer (word 64),72) /\
        ALL (nonoverlapping (word_sub stackpointer (word 64),64))
            [(word pc,LENGTH bignum_montsqr_p384_windows_mc); (x,8 * 6)] /\
        nonoverlapping (word pc,LENGTH bignum_montsqr_p384_windows_mc) (z,8 * 6)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_montsqr_p384_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (a EXP 2 <= 2 EXP 384 * p_384
                   ==> bignum_from_memory (z,6) s =
                       (inverse_mod p_384 (2 EXP 384) * a EXP 2) MOD p_384))
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 6);
                     memory :> bytes(word_sub stackpointer (word 64),64)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_MONTSQR_P384_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

let BIGNUM_AMONTSQR_P384_NOIBT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x a pc stackpointer returnaddress.
        nonoverlapping (z,8 * 6) (word_sub stackpointer (word 64),72) /\
        ALL (nonoverlapping (word_sub stackpointer (word 64),64))
            [(word pc,LENGTH bignum_montsqr_p384_windows_tmc); (x,8 * 6)] /\
        nonoverlapping (word pc,LENGTH bignum_montsqr_p384_windows_tmc) (z,8 * 6)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_montsqr_p384_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (bignum_from_memory (z,6) s ==
                   inverse_mod p_384 (2 EXP 384) * a EXP 2) (mod p_384))
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 6);
                     memory :> bytes(word_sub stackpointer (word 64),64)])`,
  WINDOWS_X86_WRAP_STACK_TAC
   bignum_montsqr_p384_windows_tmc bignum_montsqr_p384_tmc
   BIGNUM_AMONTSQR_P384_CORRECT `[RBX; RBP; R12; R13; R14; R15]` 48);;

let BIGNUM_AMONTSQR_P384_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x a pc stackpointer returnaddress.
        nonoverlapping (z,8 * 6) (word_sub stackpointer (word 64),72) /\
        ALL (nonoverlapping (word_sub stackpointer (word 64),64))
            [(word pc,LENGTH bignum_montsqr_p384_windows_mc); (x,8 * 6)] /\
        nonoverlapping (word pc,LENGTH bignum_montsqr_p384_windows_mc) (z,8 * 6)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_montsqr_p384_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (bignum_from_memory (z,6) s ==
                   inverse_mod p_384 (2 EXP 384) * a EXP 2) (mod p_384))
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 6);
                     memory :> bytes(word_sub stackpointer (word 64),64)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_AMONTSQR_P384_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

