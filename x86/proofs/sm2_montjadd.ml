(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Point addition in Montgomery-Jacobian coordinates for CC SM2 curve.       *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "common/ecencoding.ml";;
needs "EC/jacobian.ml";;
needs "EC/ccsm2.ml";;

prioritize_int();;
prioritize_real();;
prioritize_num();;

(**** print_literal_from_elf "x86/sm2/sm2_montjadd.o";;
 ****)

let sm2_montjadd_mc = define_assert_from_elf
  "sm2_montjadd_mc" "x86/sm2/sm2_montjadd.o"
[
  0x53;                    (* PUSH (% rbx) *)
  0x55;                    (* PUSH (% rbp) *)
  0x41; 0x54;              (* PUSH (% r12) *)
  0x41; 0x55;              (* PUSH (% r13) *)
  0x41; 0x56;              (* PUSH (% r14) *)
  0x41; 0x57;              (* PUSH (% r15) *)
  0x48; 0x81; 0xec; 0xe0; 0x00; 0x00; 0x00;
                           (* SUB (% rsp) (Imm32 (word 224)) *)
  0x48; 0x89; 0xd5;        (* MOV (% rbp) (% rdx) *)
  0x48; 0x8b; 0x56; 0x40;  (* MOV (% rdx) (Memop Quadword (%% (rsi,64))) *)
  0xc4; 0x62; 0xbb; 0xf6; 0xfa;
                           (* MULX4 (% r15,% r8) (% rdx,% rdx) *)
  0xc4; 0x62; 0xb3; 0xf6; 0x56; 0x48;
                           (* MULX4 (% r10,% r9) (% rdx,Memop Quadword (%% (rsi,72))) *)
  0xc4; 0x62; 0xa3; 0xf6; 0x66; 0x58;
                           (* MULX4 (% r12,% r11) (% rdx,Memop Quadword (%% (rsi,88))) *)
  0x48; 0x8b; 0x56; 0x50;  (* MOV (% rdx) (Memop Quadword (%% (rsi,80))) *)
  0xc4; 0x62; 0x93; 0xf6; 0x76; 0x58;
                           (* MULX4 (% r14,% r13) (% rdx,Memop Quadword (%% (rsi,88))) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x40;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,64))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x48;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,72))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0x48; 0x8b; 0x56; 0x58;  (* MOV (% rdx) (Memop Quadword (%% (rsi,88))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x48;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,72))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADCX (% r13) (% rcx) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADOX (% r14) (% rcx) *)
  0x49; 0x11; 0xce;        (* ADC (% r14) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xc9;
                           (* ADCX (% r9) (% r9) *)
  0xf3; 0x4d; 0x0f; 0x38; 0xf6; 0xcf;
                           (* ADOX (% r9) (% r15) *)
  0x48; 0x8b; 0x56; 0x48;  (* MOV (% rdx) (Memop Quadword (%% (rsi,72))) *)
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
  0x48; 0x8b; 0x56; 0x50;  (* MOV (% rdx) (Memop Quadword (%% (rsi,80))) *)
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
  0x48; 0x8b; 0x56; 0x58;  (* MOV (% rdx) (Memop Quadword (%% (rsi,88))) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xfa;
                           (* MULX4 (% r15,% rax) (% rdx,% rdx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xf6;
                           (* ADCX (% r14) (% r14) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADOX (% r14) (% rax) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADCX (% r15) (% rcx) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADOX (% r15) (% rcx) *)
  0x4c; 0x89; 0xc0;        (* MOV (% rax) (% r8) *)
  0x48; 0xc1; 0xe0; 0x20;  (* SHL (% rax) (Imm8 (word 32)) *)
  0x4c; 0x89; 0xc1;        (* MOV (% rcx) (% r8) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x89; 0xcb;        (* MOV (% rbx) (% rcx) *)
  0x4c; 0x29; 0xc0;        (* SUB (% rax) (% r8) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc1;        (* SUB (% r9) (% rax) *)
  0x49; 0x19; 0xca;        (* SBB (% r10) (% rcx) *)
  0x49; 0x19; 0xd3;        (* SBB (% r11) (% rdx) *)
  0x49; 0x19; 0xd8;        (* SBB (% r8) (% rbx) *)
  0x4c; 0x89; 0xc8;        (* MOV (% rax) (% r9) *)
  0x48; 0xc1; 0xe0; 0x20;  (* SHL (% rax) (Imm8 (word 32)) *)
  0x4c; 0x89; 0xc9;        (* MOV (% rcx) (% r9) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x89; 0xcb;        (* MOV (% rbx) (% rcx) *)
  0x4c; 0x29; 0xc8;        (* SUB (% rax) (% r9) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc2;        (* SUB (% r10) (% rax) *)
  0x49; 0x19; 0xcb;        (* SBB (% r11) (% rcx) *)
  0x49; 0x19; 0xd0;        (* SBB (% r8) (% rdx) *)
  0x49; 0x19; 0xd9;        (* SBB (% r9) (% rbx) *)
  0x4c; 0x89; 0xd0;        (* MOV (% rax) (% r10) *)
  0x48; 0xc1; 0xe0; 0x20;  (* SHL (% rax) (Imm8 (word 32)) *)
  0x4c; 0x89; 0xd1;        (* MOV (% rcx) (% r10) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x89; 0xcb;        (* MOV (% rbx) (% rcx) *)
  0x4c; 0x29; 0xd0;        (* SUB (% rax) (% r10) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc3;        (* SUB (% r11) (% rax) *)
  0x49; 0x19; 0xc8;        (* SBB (% r8) (% rcx) *)
  0x49; 0x19; 0xd1;        (* SBB (% r9) (% rdx) *)
  0x49; 0x19; 0xda;        (* SBB (% r10) (% rbx) *)
  0x4c; 0x89; 0xd8;        (* MOV (% rax) (% r11) *)
  0x48; 0xc1; 0xe0; 0x20;  (* SHL (% rax) (Imm8 (word 32)) *)
  0x4c; 0x89; 0xd9;        (* MOV (% rcx) (% r11) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x89; 0xcb;        (* MOV (% rbx) (% rcx) *)
  0x4c; 0x29; 0xd8;        (* SUB (% rax) (% r11) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc0;        (* SUB (% r8) (% rax) *)
  0x49; 0x19; 0xc9;        (* SBB (% r9) (% rcx) *)
  0x49; 0x19; 0xd2;        (* SBB (% r10) (% rdx) *)
  0x49; 0x19; 0xdb;        (* SBB (% r11) (% rbx) *)
  0x4d; 0x01; 0xc4;        (* ADD (% r12) (% r8) *)
  0x4d; 0x11; 0xcd;        (* ADC (% r13) (% r9) *)
  0x4d; 0x11; 0xd6;        (* ADC (% r14) (% r10) *)
  0x4d; 0x11; 0xdf;        (* ADC (% r15) (% r11) *)
  0x48; 0x19; 0xc0;        (* SBB (% rax) (% rax) *)
  0x48; 0xbb; 0x00; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rbx) (Imm64 (word 18446744069414584320)) *)
  0x48; 0x89; 0xc1;        (* MOV (% rcx) (% rax) *)
  0x48; 0x21; 0xc3;        (* AND (% rbx) (% rax) *)
  0x48; 0x0f; 0xba; 0xf1; 0x20;
                           (* BTR (% rcx) (Imm8 (word 32)) *)
  0x49; 0x29; 0xc4;        (* SUB (% r12) (% rax) *)
  0x49; 0x19; 0xdd;        (* SBB (% r13) (% rbx) *)
  0x49; 0x19; 0xc6;        (* SBB (% r14) (% rax) *)
  0x49; 0x19; 0xcf;        (* SBB (% r15) (% rcx) *)
  0x4c; 0x89; 0x24; 0x24;  (* MOV (Memop Quadword (%% (rsp,0))) (% r12) *)
  0x4c; 0x89; 0x6c; 0x24; 0x08;
                           (* MOV (Memop Quadword (%% (rsp,8))) (% r13) *)
  0x4c; 0x89; 0x74; 0x24; 0x10;
                           (* MOV (Memop Quadword (%% (rsp,16))) (% r14) *)
  0x4c; 0x89; 0x7c; 0x24; 0x18;
                           (* MOV (Memop Quadword (%% (rsp,24))) (% r15) *)
  0x48; 0x8b; 0x55; 0x40;  (* MOV (% rdx) (Memop Quadword (%% (rbp,64))) *)
  0xc4; 0x62; 0xbb; 0xf6; 0xfa;
                           (* MULX4 (% r15,% r8) (% rdx,% rdx) *)
  0xc4; 0x62; 0xb3; 0xf6; 0x55; 0x48;
                           (* MULX4 (% r10,% r9) (% rdx,Memop Quadword (%% (rbp,72))) *)
  0xc4; 0x62; 0xa3; 0xf6; 0x65; 0x58;
                           (* MULX4 (% r12,% r11) (% rdx,Memop Quadword (%% (rbp,88))) *)
  0x48; 0x8b; 0x55; 0x50;  (* MOV (% rdx) (Memop Quadword (%% (rbp,80))) *)
  0xc4; 0x62; 0x93; 0xf6; 0x75; 0x58;
                           (* MULX4 (% r14,% r13) (% rdx,Memop Quadword (%% (rbp,88))) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5d; 0x40;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rbp,64))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5d; 0x48;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rbp,72))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0x48; 0x8b; 0x55; 0x58;  (* MOV (% rdx) (Memop Quadword (%% (rbp,88))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5d; 0x48;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rbp,72))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADCX (% r13) (% rcx) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADOX (% r14) (% rcx) *)
  0x49; 0x11; 0xce;        (* ADC (% r14) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xc9;
                           (* ADCX (% r9) (% r9) *)
  0xf3; 0x4d; 0x0f; 0x38; 0xf6; 0xcf;
                           (* ADOX (% r9) (% r15) *)
  0x48; 0x8b; 0x55; 0x48;  (* MOV (% rdx) (Memop Quadword (%% (rbp,72))) *)
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
  0x48; 0x8b; 0x55; 0x50;  (* MOV (% rdx) (Memop Quadword (%% (rbp,80))) *)
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
  0x48; 0x8b; 0x55; 0x58;  (* MOV (% rdx) (Memop Quadword (%% (rbp,88))) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xfa;
                           (* MULX4 (% r15,% rax) (% rdx,% rdx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xf6;
                           (* ADCX (% r14) (% r14) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADOX (% r14) (% rax) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADCX (% r15) (% rcx) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADOX (% r15) (% rcx) *)
  0x4c; 0x89; 0xc0;        (* MOV (% rax) (% r8) *)
  0x48; 0xc1; 0xe0; 0x20;  (* SHL (% rax) (Imm8 (word 32)) *)
  0x4c; 0x89; 0xc1;        (* MOV (% rcx) (% r8) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x89; 0xcb;        (* MOV (% rbx) (% rcx) *)
  0x4c; 0x29; 0xc0;        (* SUB (% rax) (% r8) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc1;        (* SUB (% r9) (% rax) *)
  0x49; 0x19; 0xca;        (* SBB (% r10) (% rcx) *)
  0x49; 0x19; 0xd3;        (* SBB (% r11) (% rdx) *)
  0x49; 0x19; 0xd8;        (* SBB (% r8) (% rbx) *)
  0x4c; 0x89; 0xc8;        (* MOV (% rax) (% r9) *)
  0x48; 0xc1; 0xe0; 0x20;  (* SHL (% rax) (Imm8 (word 32)) *)
  0x4c; 0x89; 0xc9;        (* MOV (% rcx) (% r9) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x89; 0xcb;        (* MOV (% rbx) (% rcx) *)
  0x4c; 0x29; 0xc8;        (* SUB (% rax) (% r9) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc2;        (* SUB (% r10) (% rax) *)
  0x49; 0x19; 0xcb;        (* SBB (% r11) (% rcx) *)
  0x49; 0x19; 0xd0;        (* SBB (% r8) (% rdx) *)
  0x49; 0x19; 0xd9;        (* SBB (% r9) (% rbx) *)
  0x4c; 0x89; 0xd0;        (* MOV (% rax) (% r10) *)
  0x48; 0xc1; 0xe0; 0x20;  (* SHL (% rax) (Imm8 (word 32)) *)
  0x4c; 0x89; 0xd1;        (* MOV (% rcx) (% r10) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x89; 0xcb;        (* MOV (% rbx) (% rcx) *)
  0x4c; 0x29; 0xd0;        (* SUB (% rax) (% r10) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc3;        (* SUB (% r11) (% rax) *)
  0x49; 0x19; 0xc8;        (* SBB (% r8) (% rcx) *)
  0x49; 0x19; 0xd1;        (* SBB (% r9) (% rdx) *)
  0x49; 0x19; 0xda;        (* SBB (% r10) (% rbx) *)
  0x4c; 0x89; 0xd8;        (* MOV (% rax) (% r11) *)
  0x48; 0xc1; 0xe0; 0x20;  (* SHL (% rax) (Imm8 (word 32)) *)
  0x4c; 0x89; 0xd9;        (* MOV (% rcx) (% r11) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x89; 0xcb;        (* MOV (% rbx) (% rcx) *)
  0x4c; 0x29; 0xd8;        (* SUB (% rax) (% r11) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc0;        (* SUB (% r8) (% rax) *)
  0x49; 0x19; 0xc9;        (* SBB (% r9) (% rcx) *)
  0x49; 0x19; 0xd2;        (* SBB (% r10) (% rdx) *)
  0x49; 0x19; 0xdb;        (* SBB (% r11) (% rbx) *)
  0x4d; 0x01; 0xc4;        (* ADD (% r12) (% r8) *)
  0x4d; 0x11; 0xcd;        (* ADC (% r13) (% r9) *)
  0x4d; 0x11; 0xd6;        (* ADC (% r14) (% r10) *)
  0x4d; 0x11; 0xdf;        (* ADC (% r15) (% r11) *)
  0x48; 0x19; 0xc0;        (* SBB (% rax) (% rax) *)
  0x48; 0xbb; 0x00; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rbx) (Imm64 (word 18446744069414584320)) *)
  0x48; 0x89; 0xc1;        (* MOV (% rcx) (% rax) *)
  0x48; 0x21; 0xc3;        (* AND (% rbx) (% rax) *)
  0x48; 0x0f; 0xba; 0xf1; 0x20;
                           (* BTR (% rcx) (Imm8 (word 32)) *)
  0x49; 0x29; 0xc4;        (* SUB (% r12) (% rax) *)
  0x49; 0x19; 0xdd;        (* SBB (% r13) (% rbx) *)
  0x49; 0x19; 0xc6;        (* SBB (% r14) (% rax) *)
  0x49; 0x19; 0xcf;        (* SBB (% r15) (% rcx) *)
  0x4c; 0x89; 0xa4; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,160))) (% r12) *)
  0x4c; 0x89; 0xac; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,168))) (% r13) *)
  0x4c; 0x89; 0xb4; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,176))) (% r14) *)
  0x4c; 0x89; 0xbc; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,184))) (% r15) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x56; 0x20;  (* MOV (% rdx) (Memop Quadword (%% (rsi,32))) *)
  0xc4; 0x62; 0xbb; 0xf6; 0x4d; 0x40;
                           (* MULX4 (% r9,% r8) (% rdx,Memop Quadword (%% (rbp,64))) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x55; 0x48;
                           (* MULX4 (% r10,% rax) (% rdx,Memop Quadword (%% (rbp,72))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x5d; 0x50;
                           (* MULX4 (% r11,% rax) (% rdx,Memop Quadword (%% (rbp,80))) *)
  0x49; 0x11; 0xc2;        (* ADC (% r10) (% rax) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x65; 0x58;
                           (* MULX4 (% r12,% rax) (% rdx,Memop Quadword (%% (rbp,88))) *)
  0x49; 0x11; 0xc3;        (* ADC (% r11) (% rax) *)
  0x49; 0x11; 0xcc;        (* ADC (% r12) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x56; 0x28;  (* MOV (% rdx) (Memop Quadword (%% (rsi,40))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5d; 0x40;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rbp,64))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5d; 0x48;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rbp,72))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5d; 0x50;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rbp,80))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x6d; 0x58;
                           (* MULX4 (% r13,% rax) (% rdx,Memop Quadword (%% (rbp,88))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADOX (% r13) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADCX (% r13) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x56; 0x30;  (* MOV (% rdx) (Memop Quadword (%% (rsi,48))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5d; 0x40;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rbp,64))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5d; 0x48;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rbp,72))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5d; 0x50;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rbp,80))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x75; 0x58;
                           (* MULX4 (% r14,% rax) (% rdx,Memop Quadword (%% (rbp,88))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADOX (% r14) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADCX (% r14) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x56; 0x38;  (* MOV (% rdx) (Memop Quadword (%% (rsi,56))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5d; 0x40;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rbp,64))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5d; 0x48;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rbp,72))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5d; 0x50;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rbp,80))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x7d; 0x58;
                           (* MULX4 (% r15,% rax) (% rdx,Memop Quadword (%% (rbp,88))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADOX (% r15) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADCX (% r15) (% rcx) *)
  0x4c; 0x89; 0xc0;        (* MOV (% rax) (% r8) *)
  0x48; 0xc1; 0xe0; 0x20;  (* SHL (% rax) (Imm8 (word 32)) *)
  0x4c; 0x89; 0xc1;        (* MOV (% rcx) (% r8) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x89; 0xcb;        (* MOV (% rbx) (% rcx) *)
  0x4c; 0x29; 0xc0;        (* SUB (% rax) (% r8) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc1;        (* SUB (% r9) (% rax) *)
  0x49; 0x19; 0xca;        (* SBB (% r10) (% rcx) *)
  0x49; 0x19; 0xd3;        (* SBB (% r11) (% rdx) *)
  0x49; 0x19; 0xd8;        (* SBB (% r8) (% rbx) *)
  0x4c; 0x89; 0xc8;        (* MOV (% rax) (% r9) *)
  0x48; 0xc1; 0xe0; 0x20;  (* SHL (% rax) (Imm8 (word 32)) *)
  0x4c; 0x89; 0xc9;        (* MOV (% rcx) (% r9) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x89; 0xcb;        (* MOV (% rbx) (% rcx) *)
  0x4c; 0x29; 0xc8;        (* SUB (% rax) (% r9) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc2;        (* SUB (% r10) (% rax) *)
  0x49; 0x19; 0xcb;        (* SBB (% r11) (% rcx) *)
  0x49; 0x19; 0xd0;        (* SBB (% r8) (% rdx) *)
  0x49; 0x19; 0xd9;        (* SBB (% r9) (% rbx) *)
  0x4c; 0x89; 0xd0;        (* MOV (% rax) (% r10) *)
  0x48; 0xc1; 0xe0; 0x20;  (* SHL (% rax) (Imm8 (word 32)) *)
  0x4c; 0x89; 0xd1;        (* MOV (% rcx) (% r10) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x89; 0xcb;        (* MOV (% rbx) (% rcx) *)
  0x4c; 0x29; 0xd0;        (* SUB (% rax) (% r10) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc3;        (* SUB (% r11) (% rax) *)
  0x49; 0x19; 0xc8;        (* SBB (% r8) (% rcx) *)
  0x49; 0x19; 0xd1;        (* SBB (% r9) (% rdx) *)
  0x49; 0x19; 0xda;        (* SBB (% r10) (% rbx) *)
  0x4c; 0x89; 0xd8;        (* MOV (% rax) (% r11) *)
  0x48; 0xc1; 0xe0; 0x20;  (* SHL (% rax) (Imm8 (word 32)) *)
  0x4c; 0x89; 0xd9;        (* MOV (% rcx) (% r11) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x89; 0xcb;        (* MOV (% rbx) (% rcx) *)
  0x4c; 0x29; 0xd8;        (* SUB (% rax) (% r11) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc0;        (* SUB (% r8) (% rax) *)
  0x49; 0x19; 0xc9;        (* SBB (% r9) (% rcx) *)
  0x49; 0x19; 0xd2;        (* SBB (% r10) (% rdx) *)
  0x49; 0x19; 0xdb;        (* SBB (% r11) (% rbx) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0x4d; 0x01; 0xc4;        (* ADD (% r12) (% r8) *)
  0x4d; 0x11; 0xcd;        (* ADC (% r13) (% r9) *)
  0x4d; 0x11; 0xd6;        (* ADC (% r14) (% r10) *)
  0x4d; 0x11; 0xdf;        (* ADC (% r15) (% r11) *)
  0x48; 0x11; 0xc0;        (* ADC (% rax) (% rax) *)
  0xb9; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% ecx) (Imm32 (word 1)) *)
  0xba; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% edx) (Imm32 (word 4294967295)) *)
  0x31; 0xdb;              (* XOR (% ebx) (% ebx) *)
  0x4c; 0x01; 0xe1;        (* ADD (% rcx) (% r12) *)
  0x4c; 0x8d; 0x5a; 0x01;  (* LEA (% r11) (%% (rdx,1)) *)
  0x4c; 0x11; 0xea;        (* ADC (% rdx) (% r13) *)
  0x4c; 0x8d; 0x43; 0xff;  (* LEA (% r8) (%% (rbx,18446744073709551615)) *)
  0x4c; 0x11; 0xf3;        (* ADC (% rbx) (% r14) *)
  0x4d; 0x11; 0xfb;        (* ADC (% r11) (% r15) *)
  0x49; 0x11; 0xc0;        (* ADC (% r8) (% rax) *)
  0x4c; 0x0f; 0x42; 0xe1;  (* CMOVB (% r12) (% rcx) *)
  0x4c; 0x0f; 0x42; 0xea;  (* CMOVB (% r13) (% rdx) *)
  0x4c; 0x0f; 0x42; 0xf3;  (* CMOVB (% r14) (% rbx) *)
  0x4d; 0x0f; 0x42; 0xfb;  (* CMOVB (% r15) (% r11) *)
  0x4c; 0x89; 0xa4; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,192))) (% r12) *)
  0x4c; 0x89; 0xac; 0x24; 0xc8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,200))) (% r13) *)
  0x4c; 0x89; 0xb4; 0x24; 0xd0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,208))) (% r14) *)
  0x4c; 0x89; 0xbc; 0x24; 0xd8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,216))) (% r15) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x55; 0x20;  (* MOV (% rdx) (Memop Quadword (%% (rbp,32))) *)
  0xc4; 0x62; 0xbb; 0xf6; 0x4e; 0x40;
                           (* MULX4 (% r9,% r8) (% rdx,Memop Quadword (%% (rsi,64))) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x56; 0x48;
                           (* MULX4 (% r10,% rax) (% rdx,Memop Quadword (%% (rsi,72))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x5e; 0x50;
                           (* MULX4 (% r11,% rax) (% rdx,Memop Quadword (%% (rsi,80))) *)
  0x49; 0x11; 0xc2;        (* ADC (% r10) (% rax) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x66; 0x58;
                           (* MULX4 (% r12,% rax) (% rdx,Memop Quadword (%% (rsi,88))) *)
  0x49; 0x11; 0xc3;        (* ADC (% r11) (% rax) *)
  0x49; 0x11; 0xcc;        (* ADC (% r12) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x55; 0x28;  (* MOV (% rdx) (Memop Quadword (%% (rbp,40))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x40;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,64))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x48;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,72))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x50;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,80))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x6e; 0x58;
                           (* MULX4 (% r13,% rax) (% rdx,Memop Quadword (%% (rsi,88))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADOX (% r13) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADCX (% r13) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x55; 0x30;  (* MOV (% rdx) (Memop Quadword (%% (rbp,48))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x40;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,64))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x48;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,72))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x50;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,80))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x76; 0x58;
                           (* MULX4 (% r14,% rax) (% rdx,Memop Quadword (%% (rsi,88))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADOX (% r14) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADCX (% r14) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x55; 0x38;  (* MOV (% rdx) (Memop Quadword (%% (rbp,56))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x40;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,64))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x48;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,72))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x50;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,80))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x7e; 0x58;
                           (* MULX4 (% r15,% rax) (% rdx,Memop Quadword (%% (rsi,88))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADOX (% r15) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADCX (% r15) (% rcx) *)
  0x4c; 0x89; 0xc0;        (* MOV (% rax) (% r8) *)
  0x48; 0xc1; 0xe0; 0x20;  (* SHL (% rax) (Imm8 (word 32)) *)
  0x4c; 0x89; 0xc1;        (* MOV (% rcx) (% r8) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x89; 0xcb;        (* MOV (% rbx) (% rcx) *)
  0x4c; 0x29; 0xc0;        (* SUB (% rax) (% r8) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc1;        (* SUB (% r9) (% rax) *)
  0x49; 0x19; 0xca;        (* SBB (% r10) (% rcx) *)
  0x49; 0x19; 0xd3;        (* SBB (% r11) (% rdx) *)
  0x49; 0x19; 0xd8;        (* SBB (% r8) (% rbx) *)
  0x4c; 0x89; 0xc8;        (* MOV (% rax) (% r9) *)
  0x48; 0xc1; 0xe0; 0x20;  (* SHL (% rax) (Imm8 (word 32)) *)
  0x4c; 0x89; 0xc9;        (* MOV (% rcx) (% r9) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x89; 0xcb;        (* MOV (% rbx) (% rcx) *)
  0x4c; 0x29; 0xc8;        (* SUB (% rax) (% r9) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc2;        (* SUB (% r10) (% rax) *)
  0x49; 0x19; 0xcb;        (* SBB (% r11) (% rcx) *)
  0x49; 0x19; 0xd0;        (* SBB (% r8) (% rdx) *)
  0x49; 0x19; 0xd9;        (* SBB (% r9) (% rbx) *)
  0x4c; 0x89; 0xd0;        (* MOV (% rax) (% r10) *)
  0x48; 0xc1; 0xe0; 0x20;  (* SHL (% rax) (Imm8 (word 32)) *)
  0x4c; 0x89; 0xd1;        (* MOV (% rcx) (% r10) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x89; 0xcb;        (* MOV (% rbx) (% rcx) *)
  0x4c; 0x29; 0xd0;        (* SUB (% rax) (% r10) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc3;        (* SUB (% r11) (% rax) *)
  0x49; 0x19; 0xc8;        (* SBB (% r8) (% rcx) *)
  0x49; 0x19; 0xd1;        (* SBB (% r9) (% rdx) *)
  0x49; 0x19; 0xda;        (* SBB (% r10) (% rbx) *)
  0x4c; 0x89; 0xd8;        (* MOV (% rax) (% r11) *)
  0x48; 0xc1; 0xe0; 0x20;  (* SHL (% rax) (Imm8 (word 32)) *)
  0x4c; 0x89; 0xd9;        (* MOV (% rcx) (% r11) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x89; 0xcb;        (* MOV (% rbx) (% rcx) *)
  0x4c; 0x29; 0xd8;        (* SUB (% rax) (% r11) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc0;        (* SUB (% r8) (% rax) *)
  0x49; 0x19; 0xc9;        (* SBB (% r9) (% rcx) *)
  0x49; 0x19; 0xd2;        (* SBB (% r10) (% rdx) *)
  0x49; 0x19; 0xdb;        (* SBB (% r11) (% rbx) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0x4d; 0x01; 0xc4;        (* ADD (% r12) (% r8) *)
  0x4d; 0x11; 0xcd;        (* ADC (% r13) (% r9) *)
  0x4d; 0x11; 0xd6;        (* ADC (% r14) (% r10) *)
  0x4d; 0x11; 0xdf;        (* ADC (% r15) (% r11) *)
  0x48; 0x11; 0xc0;        (* ADC (% rax) (% rax) *)
  0xb9; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% ecx) (Imm32 (word 1)) *)
  0xba; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% edx) (Imm32 (word 4294967295)) *)
  0x31; 0xdb;              (* XOR (% ebx) (% ebx) *)
  0x4c; 0x01; 0xe1;        (* ADD (% rcx) (% r12) *)
  0x4c; 0x8d; 0x5a; 0x01;  (* LEA (% r11) (%% (rdx,1)) *)
  0x4c; 0x11; 0xea;        (* ADC (% rdx) (% r13) *)
  0x4c; 0x8d; 0x43; 0xff;  (* LEA (% r8) (%% (rbx,18446744073709551615)) *)
  0x4c; 0x11; 0xf3;        (* ADC (% rbx) (% r14) *)
  0x4d; 0x11; 0xfb;        (* ADC (% r11) (% r15) *)
  0x49; 0x11; 0xc0;        (* ADC (% r8) (% rax) *)
  0x4c; 0x0f; 0x42; 0xe1;  (* CMOVB (% r12) (% rcx) *)
  0x4c; 0x0f; 0x42; 0xea;  (* CMOVB (% r13) (% rdx) *)
  0x4c; 0x0f; 0x42; 0xf3;  (* CMOVB (% r14) (% rbx) *)
  0x4d; 0x0f; 0x42; 0xfb;  (* CMOVB (% r15) (% r11) *)
  0x4c; 0x89; 0x64; 0x24; 0x20;
                           (* MOV (Memop Quadword (%% (rsp,32))) (% r12) *)
  0x4c; 0x89; 0x6c; 0x24; 0x28;
                           (* MOV (Memop Quadword (%% (rsp,40))) (% r13) *)
  0x4c; 0x89; 0x74; 0x24; 0x30;
                           (* MOV (Memop Quadword (%% (rsp,48))) (% r14) *)
  0x4c; 0x89; 0x7c; 0x24; 0x38;
                           (* MOV (Memop Quadword (%% (rsp,56))) (% r15) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x55; 0x00;  (* MOV (% rdx) (Memop Quadword (%% (rbp,0))) *)
  0xc4; 0x62; 0xbb; 0xf6; 0x0c; 0x24;
                           (* MULX4 (% r9,% r8) (% rdx,Memop Quadword (%% (rsp,0))) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x54; 0x24; 0x08;
                           (* MULX4 (% r10,% rax) (% rdx,Memop Quadword (%% (rsp,8))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x5c; 0x24; 0x10;
                           (* MULX4 (% r11,% rax) (% rdx,Memop Quadword (%% (rsp,16))) *)
  0x49; 0x11; 0xc2;        (* ADC (% r10) (% rax) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x64; 0x24; 0x18;
                           (* MULX4 (% r12,% rax) (% rdx,Memop Quadword (%% (rsp,24))) *)
  0x49; 0x11; 0xc3;        (* ADC (% r11) (% rax) *)
  0x49; 0x11; 0xcc;        (* ADC (% r12) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x55; 0x08;  (* MOV (% rdx) (Memop Quadword (%% (rbp,8))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1c; 0x24;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x08;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x10;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,16))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x6c; 0x24; 0x18;
                           (* MULX4 (% r13,% rax) (% rdx,Memop Quadword (%% (rsp,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADOX (% r13) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADCX (% r13) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x55; 0x10;  (* MOV (% rdx) (Memop Quadword (%% (rbp,16))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1c; 0x24;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x08;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x10;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,16))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x74; 0x24; 0x18;
                           (* MULX4 (% r14,% rax) (% rdx,Memop Quadword (%% (rsp,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADOX (% r14) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADCX (% r14) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x55; 0x18;  (* MOV (% rdx) (Memop Quadword (%% (rbp,24))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1c; 0x24;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x08;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x10;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,16))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x7c; 0x24; 0x18;
                           (* MULX4 (% r15,% rax) (% rdx,Memop Quadword (%% (rsp,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADOX (% r15) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADCX (% r15) (% rcx) *)
  0x4c; 0x89; 0xc0;        (* MOV (% rax) (% r8) *)
  0x48; 0xc1; 0xe0; 0x20;  (* SHL (% rax) (Imm8 (word 32)) *)
  0x4c; 0x89; 0xc1;        (* MOV (% rcx) (% r8) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x89; 0xcb;        (* MOV (% rbx) (% rcx) *)
  0x4c; 0x29; 0xc0;        (* SUB (% rax) (% r8) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc1;        (* SUB (% r9) (% rax) *)
  0x49; 0x19; 0xca;        (* SBB (% r10) (% rcx) *)
  0x49; 0x19; 0xd3;        (* SBB (% r11) (% rdx) *)
  0x49; 0x19; 0xd8;        (* SBB (% r8) (% rbx) *)
  0x4c; 0x89; 0xc8;        (* MOV (% rax) (% r9) *)
  0x48; 0xc1; 0xe0; 0x20;  (* SHL (% rax) (Imm8 (word 32)) *)
  0x4c; 0x89; 0xc9;        (* MOV (% rcx) (% r9) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x89; 0xcb;        (* MOV (% rbx) (% rcx) *)
  0x4c; 0x29; 0xc8;        (* SUB (% rax) (% r9) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc2;        (* SUB (% r10) (% rax) *)
  0x49; 0x19; 0xcb;        (* SBB (% r11) (% rcx) *)
  0x49; 0x19; 0xd0;        (* SBB (% r8) (% rdx) *)
  0x49; 0x19; 0xd9;        (* SBB (% r9) (% rbx) *)
  0x4c; 0x89; 0xd0;        (* MOV (% rax) (% r10) *)
  0x48; 0xc1; 0xe0; 0x20;  (* SHL (% rax) (Imm8 (word 32)) *)
  0x4c; 0x89; 0xd1;        (* MOV (% rcx) (% r10) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x89; 0xcb;        (* MOV (% rbx) (% rcx) *)
  0x4c; 0x29; 0xd0;        (* SUB (% rax) (% r10) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc3;        (* SUB (% r11) (% rax) *)
  0x49; 0x19; 0xc8;        (* SBB (% r8) (% rcx) *)
  0x49; 0x19; 0xd1;        (* SBB (% r9) (% rdx) *)
  0x49; 0x19; 0xda;        (* SBB (% r10) (% rbx) *)
  0x4c; 0x89; 0xd8;        (* MOV (% rax) (% r11) *)
  0x48; 0xc1; 0xe0; 0x20;  (* SHL (% rax) (Imm8 (word 32)) *)
  0x4c; 0x89; 0xd9;        (* MOV (% rcx) (% r11) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x89; 0xcb;        (* MOV (% rbx) (% rcx) *)
  0x4c; 0x29; 0xd8;        (* SUB (% rax) (% r11) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc0;        (* SUB (% r8) (% rax) *)
  0x49; 0x19; 0xc9;        (* SBB (% r9) (% rcx) *)
  0x49; 0x19; 0xd2;        (* SBB (% r10) (% rdx) *)
  0x49; 0x19; 0xdb;        (* SBB (% r11) (% rbx) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0x4d; 0x01; 0xc4;        (* ADD (% r12) (% r8) *)
  0x4d; 0x11; 0xcd;        (* ADC (% r13) (% r9) *)
  0x4d; 0x11; 0xd6;        (* ADC (% r14) (% r10) *)
  0x4d; 0x11; 0xdf;        (* ADC (% r15) (% r11) *)
  0x48; 0x11; 0xc0;        (* ADC (% rax) (% rax) *)
  0xb9; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% ecx) (Imm32 (word 1)) *)
  0xba; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% edx) (Imm32 (word 4294967295)) *)
  0x31; 0xdb;              (* XOR (% ebx) (% ebx) *)
  0x4c; 0x01; 0xe1;        (* ADD (% rcx) (% r12) *)
  0x4c; 0x8d; 0x5a; 0x01;  (* LEA (% r11) (%% (rdx,1)) *)
  0x4c; 0x11; 0xea;        (* ADC (% rdx) (% r13) *)
  0x4c; 0x8d; 0x43; 0xff;  (* LEA (% r8) (%% (rbx,18446744073709551615)) *)
  0x4c; 0x11; 0xf3;        (* ADC (% rbx) (% r14) *)
  0x4d; 0x11; 0xfb;        (* ADC (% r11) (% r15) *)
  0x49; 0x11; 0xc0;        (* ADC (% r8) (% rax) *)
  0x4c; 0x0f; 0x42; 0xe1;  (* CMOVB (% r12) (% rcx) *)
  0x4c; 0x0f; 0x42; 0xea;  (* CMOVB (% r13) (% rdx) *)
  0x4c; 0x0f; 0x42; 0xf3;  (* CMOVB (% r14) (% rbx) *)
  0x4d; 0x0f; 0x42; 0xfb;  (* CMOVB (% r15) (% r11) *)
  0x4c; 0x89; 0x64; 0x24; 0x40;
                           (* MOV (Memop Quadword (%% (rsp,64))) (% r12) *)
  0x4c; 0x89; 0x6c; 0x24; 0x48;
                           (* MOV (Memop Quadword (%% (rsp,72))) (% r13) *)
  0x4c; 0x89; 0x74; 0x24; 0x50;
                           (* MOV (Memop Quadword (%% (rsp,80))) (% r14) *)
  0x4c; 0x89; 0x7c; 0x24; 0x58;
                           (* MOV (Memop Quadword (%% (rsp,88))) (% r15) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x16;        (* MOV (% rdx) (Memop Quadword (%% (rsi,0))) *)
  0xc4; 0x62; 0xbb; 0xf6; 0x8c; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MULX4 (% r9,% r8) (% rdx,Memop Quadword (%% (rsp,160))) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x94; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MULX4 (% r10,% rax) (% rdx,Memop Quadword (%% (rsp,168))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x9c; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MULX4 (% r11,% rax) (% rdx,Memop Quadword (%% (rsp,176))) *)
  0x49; 0x11; 0xc2;        (* ADC (% r10) (% rax) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xa4; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MULX4 (% r12,% rax) (% rdx,Memop Quadword (%% (rsp,184))) *)
  0x49; 0x11; 0xc3;        (* ADC (% r11) (% rax) *)
  0x49; 0x11; 0xcc;        (* ADC (% r12) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x56; 0x08;  (* MOV (% rdx) (Memop Quadword (%% (rsi,8))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,160))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,168))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,176))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xac; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MULX4 (% r13,% rax) (% rdx,Memop Quadword (%% (rsp,184))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADOX (% r13) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADCX (% r13) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x56; 0x10;  (* MOV (% rdx) (Memop Quadword (%% (rsi,16))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,160))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,168))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,176))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xb4; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MULX4 (% r14,% rax) (% rdx,Memop Quadword (%% (rsp,184))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADOX (% r14) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADCX (% r14) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x56; 0x18;  (* MOV (% rdx) (Memop Quadword (%% (rsi,24))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,160))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,168))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,176))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xbc; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MULX4 (% r15,% rax) (% rdx,Memop Quadword (%% (rsp,184))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADOX (% r15) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADCX (% r15) (% rcx) *)
  0x4c; 0x89; 0xc0;        (* MOV (% rax) (% r8) *)
  0x48; 0xc1; 0xe0; 0x20;  (* SHL (% rax) (Imm8 (word 32)) *)
  0x4c; 0x89; 0xc1;        (* MOV (% rcx) (% r8) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x89; 0xcb;        (* MOV (% rbx) (% rcx) *)
  0x4c; 0x29; 0xc0;        (* SUB (% rax) (% r8) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc1;        (* SUB (% r9) (% rax) *)
  0x49; 0x19; 0xca;        (* SBB (% r10) (% rcx) *)
  0x49; 0x19; 0xd3;        (* SBB (% r11) (% rdx) *)
  0x49; 0x19; 0xd8;        (* SBB (% r8) (% rbx) *)
  0x4c; 0x89; 0xc8;        (* MOV (% rax) (% r9) *)
  0x48; 0xc1; 0xe0; 0x20;  (* SHL (% rax) (Imm8 (word 32)) *)
  0x4c; 0x89; 0xc9;        (* MOV (% rcx) (% r9) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x89; 0xcb;        (* MOV (% rbx) (% rcx) *)
  0x4c; 0x29; 0xc8;        (* SUB (% rax) (% r9) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc2;        (* SUB (% r10) (% rax) *)
  0x49; 0x19; 0xcb;        (* SBB (% r11) (% rcx) *)
  0x49; 0x19; 0xd0;        (* SBB (% r8) (% rdx) *)
  0x49; 0x19; 0xd9;        (* SBB (% r9) (% rbx) *)
  0x4c; 0x89; 0xd0;        (* MOV (% rax) (% r10) *)
  0x48; 0xc1; 0xe0; 0x20;  (* SHL (% rax) (Imm8 (word 32)) *)
  0x4c; 0x89; 0xd1;        (* MOV (% rcx) (% r10) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x89; 0xcb;        (* MOV (% rbx) (% rcx) *)
  0x4c; 0x29; 0xd0;        (* SUB (% rax) (% r10) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc3;        (* SUB (% r11) (% rax) *)
  0x49; 0x19; 0xc8;        (* SBB (% r8) (% rcx) *)
  0x49; 0x19; 0xd1;        (* SBB (% r9) (% rdx) *)
  0x49; 0x19; 0xda;        (* SBB (% r10) (% rbx) *)
  0x4c; 0x89; 0xd8;        (* MOV (% rax) (% r11) *)
  0x48; 0xc1; 0xe0; 0x20;  (* SHL (% rax) (Imm8 (word 32)) *)
  0x4c; 0x89; 0xd9;        (* MOV (% rcx) (% r11) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x89; 0xcb;        (* MOV (% rbx) (% rcx) *)
  0x4c; 0x29; 0xd8;        (* SUB (% rax) (% r11) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc0;        (* SUB (% r8) (% rax) *)
  0x49; 0x19; 0xc9;        (* SBB (% r9) (% rcx) *)
  0x49; 0x19; 0xd2;        (* SBB (% r10) (% rdx) *)
  0x49; 0x19; 0xdb;        (* SBB (% r11) (% rbx) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0x4d; 0x01; 0xc4;        (* ADD (% r12) (% r8) *)
  0x4d; 0x11; 0xcd;        (* ADC (% r13) (% r9) *)
  0x4d; 0x11; 0xd6;        (* ADC (% r14) (% r10) *)
  0x4d; 0x11; 0xdf;        (* ADC (% r15) (% r11) *)
  0x48; 0x11; 0xc0;        (* ADC (% rax) (% rax) *)
  0xb9; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% ecx) (Imm32 (word 1)) *)
  0xba; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% edx) (Imm32 (word 4294967295)) *)
  0x31; 0xdb;              (* XOR (% ebx) (% ebx) *)
  0x4c; 0x01; 0xe1;        (* ADD (% rcx) (% r12) *)
  0x4c; 0x8d; 0x5a; 0x01;  (* LEA (% r11) (%% (rdx,1)) *)
  0x4c; 0x11; 0xea;        (* ADC (% rdx) (% r13) *)
  0x4c; 0x8d; 0x43; 0xff;  (* LEA (% r8) (%% (rbx,18446744073709551615)) *)
  0x4c; 0x11; 0xf3;        (* ADC (% rbx) (% r14) *)
  0x4d; 0x11; 0xfb;        (* ADC (% r11) (% r15) *)
  0x49; 0x11; 0xc0;        (* ADC (% r8) (% rax) *)
  0x4c; 0x0f; 0x42; 0xe1;  (* CMOVB (% r12) (% rcx) *)
  0x4c; 0x0f; 0x42; 0xea;  (* CMOVB (% r13) (% rdx) *)
  0x4c; 0x0f; 0x42; 0xf3;  (* CMOVB (% r14) (% rbx) *)
  0x4d; 0x0f; 0x42; 0xfb;  (* CMOVB (% r15) (% r11) *)
  0x4c; 0x89; 0xa4; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,128))) (% r12) *)
  0x4c; 0x89; 0xac; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,136))) (% r13) *)
  0x4c; 0x89; 0xb4; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,144))) (% r14) *)
  0x4c; 0x89; 0xbc; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,152))) (% r15) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x54; 0x24; 0x20;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,32))) *)
  0xc4; 0x62; 0xbb; 0xf6; 0x0c; 0x24;
                           (* MULX4 (% r9,% r8) (% rdx,Memop Quadword (%% (rsp,0))) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x54; 0x24; 0x08;
                           (* MULX4 (% r10,% rax) (% rdx,Memop Quadword (%% (rsp,8))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x5c; 0x24; 0x10;
                           (* MULX4 (% r11,% rax) (% rdx,Memop Quadword (%% (rsp,16))) *)
  0x49; 0x11; 0xc2;        (* ADC (% r10) (% rax) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x64; 0x24; 0x18;
                           (* MULX4 (% r12,% rax) (% rdx,Memop Quadword (%% (rsp,24))) *)
  0x49; 0x11; 0xc3;        (* ADC (% r11) (% rax) *)
  0x49; 0x11; 0xcc;        (* ADC (% r12) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x54; 0x24; 0x28;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,40))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1c; 0x24;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x08;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x10;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,16))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x6c; 0x24; 0x18;
                           (* MULX4 (% r13,% rax) (% rdx,Memop Quadword (%% (rsp,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADOX (% r13) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADCX (% r13) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x54; 0x24; 0x30;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,48))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1c; 0x24;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x08;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x10;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,16))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x74; 0x24; 0x18;
                           (* MULX4 (% r14,% rax) (% rdx,Memop Quadword (%% (rsp,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADOX (% r14) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADCX (% r14) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x54; 0x24; 0x38;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,56))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1c; 0x24;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x08;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x10;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,16))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x7c; 0x24; 0x18;
                           (* MULX4 (% r15,% rax) (% rdx,Memop Quadword (%% (rsp,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADOX (% r15) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADCX (% r15) (% rcx) *)
  0x4c; 0x89; 0xc0;        (* MOV (% rax) (% r8) *)
  0x48; 0xc1; 0xe0; 0x20;  (* SHL (% rax) (Imm8 (word 32)) *)
  0x4c; 0x89; 0xc1;        (* MOV (% rcx) (% r8) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x89; 0xcb;        (* MOV (% rbx) (% rcx) *)
  0x4c; 0x29; 0xc0;        (* SUB (% rax) (% r8) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc1;        (* SUB (% r9) (% rax) *)
  0x49; 0x19; 0xca;        (* SBB (% r10) (% rcx) *)
  0x49; 0x19; 0xd3;        (* SBB (% r11) (% rdx) *)
  0x49; 0x19; 0xd8;        (* SBB (% r8) (% rbx) *)
  0x4c; 0x89; 0xc8;        (* MOV (% rax) (% r9) *)
  0x48; 0xc1; 0xe0; 0x20;  (* SHL (% rax) (Imm8 (word 32)) *)
  0x4c; 0x89; 0xc9;        (* MOV (% rcx) (% r9) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x89; 0xcb;        (* MOV (% rbx) (% rcx) *)
  0x4c; 0x29; 0xc8;        (* SUB (% rax) (% r9) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc2;        (* SUB (% r10) (% rax) *)
  0x49; 0x19; 0xcb;        (* SBB (% r11) (% rcx) *)
  0x49; 0x19; 0xd0;        (* SBB (% r8) (% rdx) *)
  0x49; 0x19; 0xd9;        (* SBB (% r9) (% rbx) *)
  0x4c; 0x89; 0xd0;        (* MOV (% rax) (% r10) *)
  0x48; 0xc1; 0xe0; 0x20;  (* SHL (% rax) (Imm8 (word 32)) *)
  0x4c; 0x89; 0xd1;        (* MOV (% rcx) (% r10) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x89; 0xcb;        (* MOV (% rbx) (% rcx) *)
  0x4c; 0x29; 0xd0;        (* SUB (% rax) (% r10) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc3;        (* SUB (% r11) (% rax) *)
  0x49; 0x19; 0xc8;        (* SBB (% r8) (% rcx) *)
  0x49; 0x19; 0xd1;        (* SBB (% r9) (% rdx) *)
  0x49; 0x19; 0xda;        (* SBB (% r10) (% rbx) *)
  0x4c; 0x89; 0xd8;        (* MOV (% rax) (% r11) *)
  0x48; 0xc1; 0xe0; 0x20;  (* SHL (% rax) (Imm8 (word 32)) *)
  0x4c; 0x89; 0xd9;        (* MOV (% rcx) (% r11) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x89; 0xcb;        (* MOV (% rbx) (% rcx) *)
  0x4c; 0x29; 0xd8;        (* SUB (% rax) (% r11) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc0;        (* SUB (% r8) (% rax) *)
  0x49; 0x19; 0xc9;        (* SBB (% r9) (% rcx) *)
  0x49; 0x19; 0xd2;        (* SBB (% r10) (% rdx) *)
  0x49; 0x19; 0xdb;        (* SBB (% r11) (% rbx) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0x4d; 0x01; 0xc4;        (* ADD (% r12) (% r8) *)
  0x4d; 0x11; 0xcd;        (* ADC (% r13) (% r9) *)
  0x4d; 0x11; 0xd6;        (* ADC (% r14) (% r10) *)
  0x4d; 0x11; 0xdf;        (* ADC (% r15) (% r11) *)
  0x48; 0x11; 0xc0;        (* ADC (% rax) (% rax) *)
  0xb9; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% ecx) (Imm32 (word 1)) *)
  0xba; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% edx) (Imm32 (word 4294967295)) *)
  0x31; 0xdb;              (* XOR (% ebx) (% ebx) *)
  0x4c; 0x01; 0xe1;        (* ADD (% rcx) (% r12) *)
  0x4c; 0x8d; 0x5a; 0x01;  (* LEA (% r11) (%% (rdx,1)) *)
  0x4c; 0x11; 0xea;        (* ADC (% rdx) (% r13) *)
  0x4c; 0x8d; 0x43; 0xff;  (* LEA (% r8) (%% (rbx,18446744073709551615)) *)
  0x4c; 0x11; 0xf3;        (* ADC (% rbx) (% r14) *)
  0x4d; 0x11; 0xfb;        (* ADC (% r11) (% r15) *)
  0x49; 0x11; 0xc0;        (* ADC (% r8) (% rax) *)
  0x4c; 0x0f; 0x42; 0xe1;  (* CMOVB (% r12) (% rcx) *)
  0x4c; 0x0f; 0x42; 0xea;  (* CMOVB (% r13) (% rdx) *)
  0x4c; 0x0f; 0x42; 0xf3;  (* CMOVB (% r14) (% rbx) *)
  0x4d; 0x0f; 0x42; 0xfb;  (* CMOVB (% r15) (% r11) *)
  0x4c; 0x89; 0x64; 0x24; 0x20;
                           (* MOV (Memop Quadword (%% (rsp,32))) (% r12) *)
  0x4c; 0x89; 0x6c; 0x24; 0x28;
                           (* MOV (Memop Quadword (%% (rsp,40))) (% r13) *)
  0x4c; 0x89; 0x74; 0x24; 0x30;
                           (* MOV (Memop Quadword (%% (rsp,48))) (% r14) *)
  0x4c; 0x89; 0x7c; 0x24; 0x38;
                           (* MOV (Memop Quadword (%% (rsp,56))) (% r15) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x94; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,192))) *)
  0xc4; 0x62; 0xbb; 0xf6; 0x8c; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MULX4 (% r9,% r8) (% rdx,Memop Quadword (%% (rsp,160))) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x94; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MULX4 (% r10,% rax) (% rdx,Memop Quadword (%% (rsp,168))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x9c; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MULX4 (% r11,% rax) (% rdx,Memop Quadword (%% (rsp,176))) *)
  0x49; 0x11; 0xc2;        (* ADC (% r10) (% rax) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xa4; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MULX4 (% r12,% rax) (% rdx,Memop Quadword (%% (rsp,184))) *)
  0x49; 0x11; 0xc3;        (* ADC (% r11) (% rax) *)
  0x49; 0x11; 0xcc;        (* ADC (% r12) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x94; 0x24; 0xc8; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,200))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,160))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,168))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,176))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xac; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MULX4 (% r13,% rax) (% rdx,Memop Quadword (%% (rsp,184))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADOX (% r13) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADCX (% r13) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x94; 0x24; 0xd0; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,208))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,160))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,168))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,176))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xb4; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MULX4 (% r14,% rax) (% rdx,Memop Quadword (%% (rsp,184))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADOX (% r14) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADCX (% r14) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x94; 0x24; 0xd8; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,216))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,160))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,168))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,176))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xbc; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MULX4 (% r15,% rax) (% rdx,Memop Quadword (%% (rsp,184))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADOX (% r15) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADCX (% r15) (% rcx) *)
  0x4c; 0x89; 0xc0;        (* MOV (% rax) (% r8) *)
  0x48; 0xc1; 0xe0; 0x20;  (* SHL (% rax) (Imm8 (word 32)) *)
  0x4c; 0x89; 0xc1;        (* MOV (% rcx) (% r8) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x89; 0xcb;        (* MOV (% rbx) (% rcx) *)
  0x4c; 0x29; 0xc0;        (* SUB (% rax) (% r8) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc1;        (* SUB (% r9) (% rax) *)
  0x49; 0x19; 0xca;        (* SBB (% r10) (% rcx) *)
  0x49; 0x19; 0xd3;        (* SBB (% r11) (% rdx) *)
  0x49; 0x19; 0xd8;        (* SBB (% r8) (% rbx) *)
  0x4c; 0x89; 0xc8;        (* MOV (% rax) (% r9) *)
  0x48; 0xc1; 0xe0; 0x20;  (* SHL (% rax) (Imm8 (word 32)) *)
  0x4c; 0x89; 0xc9;        (* MOV (% rcx) (% r9) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x89; 0xcb;        (* MOV (% rbx) (% rcx) *)
  0x4c; 0x29; 0xc8;        (* SUB (% rax) (% r9) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc2;        (* SUB (% r10) (% rax) *)
  0x49; 0x19; 0xcb;        (* SBB (% r11) (% rcx) *)
  0x49; 0x19; 0xd0;        (* SBB (% r8) (% rdx) *)
  0x49; 0x19; 0xd9;        (* SBB (% r9) (% rbx) *)
  0x4c; 0x89; 0xd0;        (* MOV (% rax) (% r10) *)
  0x48; 0xc1; 0xe0; 0x20;  (* SHL (% rax) (Imm8 (word 32)) *)
  0x4c; 0x89; 0xd1;        (* MOV (% rcx) (% r10) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x89; 0xcb;        (* MOV (% rbx) (% rcx) *)
  0x4c; 0x29; 0xd0;        (* SUB (% rax) (% r10) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc3;        (* SUB (% r11) (% rax) *)
  0x49; 0x19; 0xc8;        (* SBB (% r8) (% rcx) *)
  0x49; 0x19; 0xd1;        (* SBB (% r9) (% rdx) *)
  0x49; 0x19; 0xda;        (* SBB (% r10) (% rbx) *)
  0x4c; 0x89; 0xd8;        (* MOV (% rax) (% r11) *)
  0x48; 0xc1; 0xe0; 0x20;  (* SHL (% rax) (Imm8 (word 32)) *)
  0x4c; 0x89; 0xd9;        (* MOV (% rcx) (% r11) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x89; 0xcb;        (* MOV (% rbx) (% rcx) *)
  0x4c; 0x29; 0xd8;        (* SUB (% rax) (% r11) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc0;        (* SUB (% r8) (% rax) *)
  0x49; 0x19; 0xc9;        (* SBB (% r9) (% rcx) *)
  0x49; 0x19; 0xd2;        (* SBB (% r10) (% rdx) *)
  0x49; 0x19; 0xdb;        (* SBB (% r11) (% rbx) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0x4d; 0x01; 0xc4;        (* ADD (% r12) (% r8) *)
  0x4d; 0x11; 0xcd;        (* ADC (% r13) (% r9) *)
  0x4d; 0x11; 0xd6;        (* ADC (% r14) (% r10) *)
  0x4d; 0x11; 0xdf;        (* ADC (% r15) (% r11) *)
  0x48; 0x11; 0xc0;        (* ADC (% rax) (% rax) *)
  0xb9; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% ecx) (Imm32 (word 1)) *)
  0xba; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% edx) (Imm32 (word 4294967295)) *)
  0x31; 0xdb;              (* XOR (% ebx) (% ebx) *)
  0x4c; 0x01; 0xe1;        (* ADD (% rcx) (% r12) *)
  0x4c; 0x8d; 0x5a; 0x01;  (* LEA (% r11) (%% (rdx,1)) *)
  0x4c; 0x11; 0xea;        (* ADC (% rdx) (% r13) *)
  0x4c; 0x8d; 0x43; 0xff;  (* LEA (% r8) (%% (rbx,18446744073709551615)) *)
  0x4c; 0x11; 0xf3;        (* ADC (% rbx) (% r14) *)
  0x4d; 0x11; 0xfb;        (* ADC (% r11) (% r15) *)
  0x49; 0x11; 0xc0;        (* ADC (% r8) (% rax) *)
  0x4c; 0x0f; 0x42; 0xe1;  (* CMOVB (% r12) (% rcx) *)
  0x4c; 0x0f; 0x42; 0xea;  (* CMOVB (% r13) (% rdx) *)
  0x4c; 0x0f; 0x42; 0xf3;  (* CMOVB (% r14) (% rbx) *)
  0x4d; 0x0f; 0x42; 0xfb;  (* CMOVB (% r15) (% r11) *)
  0x4c; 0x89; 0xa4; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,192))) (% r12) *)
  0x4c; 0x89; 0xac; 0x24; 0xc8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,200))) (% r13) *)
  0x4c; 0x89; 0xb4; 0x24; 0xd0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,208))) (% r14) *)
  0x4c; 0x89; 0xbc; 0x24; 0xd8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,216))) (% r15) *)
  0x48; 0x8b; 0x44; 0x24; 0x40;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,64))) *)
  0x48; 0x2b; 0x84; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* SUB (% rax) (Memop Quadword (%% (rsp,128))) *)
  0x48; 0x8b; 0x4c; 0x24; 0x48;
                           (* MOV (% rcx) (Memop Quadword (%% (rsp,72))) *)
  0x48; 0x1b; 0x8c; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* SBB (% rcx) (Memop Quadword (%% (rsp,136))) *)
  0x4c; 0x8b; 0x44; 0x24; 0x50;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,80))) *)
  0x4c; 0x1b; 0x84; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* SBB (% r8) (Memop Quadword (%% (rsp,144))) *)
  0x4c; 0x8b; 0x4c; 0x24; 0x58;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,88))) *)
  0x4c; 0x1b; 0x8c; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* SBB (% r9) (Memop Quadword (%% (rsp,152))) *)
  0x49; 0xba; 0x00; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r10) (Imm64 (word 18446744069414584320)) *)
  0x4d; 0x19; 0xdb;        (* SBB (% r11) (% r11) *)
  0x4d; 0x21; 0xda;        (* AND (% r10) (% r11) *)
  0x4c; 0x89; 0xda;        (* MOV (% rdx) (% r11) *)
  0x48; 0x0f; 0xba; 0xf2; 0x20;
                           (* BTR (% rdx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xd8;        (* ADD (% rax) (% r11) *)
  0x48; 0x89; 0x84; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,160))) (% rax) *)
  0x4c; 0x11; 0xd1;        (* ADC (% rcx) (% r10) *)
  0x48; 0x89; 0x8c; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,168))) (% rcx) *)
  0x4d; 0x11; 0xd8;        (* ADC (% r8) (% r11) *)
  0x4c; 0x89; 0x84; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,176))) (% r8) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x4c; 0x89; 0x8c; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,184))) (% r9) *)
  0x48; 0x8b; 0x44; 0x24; 0x20;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,32))) *)
  0x48; 0x2b; 0x84; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* SUB (% rax) (Memop Quadword (%% (rsp,192))) *)
  0x48; 0x8b; 0x4c; 0x24; 0x28;
                           (* MOV (% rcx) (Memop Quadword (%% (rsp,40))) *)
  0x48; 0x1b; 0x8c; 0x24; 0xc8; 0x00; 0x00; 0x00;
                           (* SBB (% rcx) (Memop Quadword (%% (rsp,200))) *)
  0x4c; 0x8b; 0x44; 0x24; 0x30;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,48))) *)
  0x4c; 0x1b; 0x84; 0x24; 0xd0; 0x00; 0x00; 0x00;
                           (* SBB (% r8) (Memop Quadword (%% (rsp,208))) *)
  0x4c; 0x8b; 0x4c; 0x24; 0x38;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,56))) *)
  0x4c; 0x1b; 0x8c; 0x24; 0xd8; 0x00; 0x00; 0x00;
                           (* SBB (% r9) (Memop Quadword (%% (rsp,216))) *)
  0x49; 0xba; 0x00; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r10) (Imm64 (word 18446744069414584320)) *)
  0x4d; 0x19; 0xdb;        (* SBB (% r11) (% r11) *)
  0x4d; 0x21; 0xda;        (* AND (% r10) (% r11) *)
  0x4c; 0x89; 0xda;        (* MOV (% rdx) (% r11) *)
  0x48; 0x0f; 0xba; 0xf2; 0x20;
                           (* BTR (% rdx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xd8;        (* ADD (% rax) (% r11) *)
  0x48; 0x89; 0x44; 0x24; 0x20;
                           (* MOV (Memop Quadword (%% (rsp,32))) (% rax) *)
  0x4c; 0x11; 0xd1;        (* ADC (% rcx) (% r10) *)
  0x48; 0x89; 0x4c; 0x24; 0x28;
                           (* MOV (Memop Quadword (%% (rsp,40))) (% rcx) *)
  0x4d; 0x11; 0xd8;        (* ADC (% r8) (% r11) *)
  0x4c; 0x89; 0x44; 0x24; 0x30;
                           (* MOV (Memop Quadword (%% (rsp,48))) (% r8) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x4c; 0x89; 0x4c; 0x24; 0x38;
                           (* MOV (Memop Quadword (%% (rsp,56))) (% r9) *)
  0x48; 0x8b; 0x94; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,160))) *)
  0xc4; 0x62; 0xbb; 0xf6; 0xfa;
                           (* MULX4 (% r15,% r8) (% rdx,% rdx) *)
  0xc4; 0x62; 0xb3; 0xf6; 0x94; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MULX4 (% r10,% r9) (% rdx,Memop Quadword (%% (rsp,168))) *)
  0xc4; 0x62; 0xa3; 0xf6; 0xa4; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MULX4 (% r12,% r11) (% rdx,Memop Quadword (%% (rsp,184))) *)
  0x48; 0x8b; 0x94; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,176))) *)
  0xc4; 0x62; 0x93; 0xf6; 0xb4; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MULX4 (% r14,% r13) (% rdx,Memop Quadword (%% (rsp,184))) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,160))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,168))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0x48; 0x8b; 0x94; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,184))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,168))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADCX (% r13) (% rcx) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADOX (% r14) (% rcx) *)
  0x49; 0x11; 0xce;        (* ADC (% r14) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xc9;
                           (* ADCX (% r9) (% r9) *)
  0xf3; 0x4d; 0x0f; 0x38; 0xf6; 0xcf;
                           (* ADOX (% r9) (% r15) *)
  0x48; 0x8b; 0x94; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,168))) *)
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
  0x48; 0x8b; 0x94; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,176))) *)
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
  0x48; 0x8b; 0x94; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,184))) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xfa;
                           (* MULX4 (% r15,% rax) (% rdx,% rdx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xf6;
                           (* ADCX (% r14) (% r14) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADOX (% r14) (% rax) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADCX (% r15) (% rcx) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADOX (% r15) (% rcx) *)
  0x4c; 0x89; 0xc0;        (* MOV (% rax) (% r8) *)
  0x48; 0xc1; 0xe0; 0x20;  (* SHL (% rax) (Imm8 (word 32)) *)
  0x4c; 0x89; 0xc1;        (* MOV (% rcx) (% r8) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x89; 0xcb;        (* MOV (% rbx) (% rcx) *)
  0x4c; 0x29; 0xc0;        (* SUB (% rax) (% r8) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc1;        (* SUB (% r9) (% rax) *)
  0x49; 0x19; 0xca;        (* SBB (% r10) (% rcx) *)
  0x49; 0x19; 0xd3;        (* SBB (% r11) (% rdx) *)
  0x49; 0x19; 0xd8;        (* SBB (% r8) (% rbx) *)
  0x4c; 0x89; 0xc8;        (* MOV (% rax) (% r9) *)
  0x48; 0xc1; 0xe0; 0x20;  (* SHL (% rax) (Imm8 (word 32)) *)
  0x4c; 0x89; 0xc9;        (* MOV (% rcx) (% r9) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x89; 0xcb;        (* MOV (% rbx) (% rcx) *)
  0x4c; 0x29; 0xc8;        (* SUB (% rax) (% r9) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc2;        (* SUB (% r10) (% rax) *)
  0x49; 0x19; 0xcb;        (* SBB (% r11) (% rcx) *)
  0x49; 0x19; 0xd0;        (* SBB (% r8) (% rdx) *)
  0x49; 0x19; 0xd9;        (* SBB (% r9) (% rbx) *)
  0x4c; 0x89; 0xd0;        (* MOV (% rax) (% r10) *)
  0x48; 0xc1; 0xe0; 0x20;  (* SHL (% rax) (Imm8 (word 32)) *)
  0x4c; 0x89; 0xd1;        (* MOV (% rcx) (% r10) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x89; 0xcb;        (* MOV (% rbx) (% rcx) *)
  0x4c; 0x29; 0xd0;        (* SUB (% rax) (% r10) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc3;        (* SUB (% r11) (% rax) *)
  0x49; 0x19; 0xc8;        (* SBB (% r8) (% rcx) *)
  0x49; 0x19; 0xd1;        (* SBB (% r9) (% rdx) *)
  0x49; 0x19; 0xda;        (* SBB (% r10) (% rbx) *)
  0x4c; 0x89; 0xd8;        (* MOV (% rax) (% r11) *)
  0x48; 0xc1; 0xe0; 0x20;  (* SHL (% rax) (Imm8 (word 32)) *)
  0x4c; 0x89; 0xd9;        (* MOV (% rcx) (% r11) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x89; 0xcb;        (* MOV (% rbx) (% rcx) *)
  0x4c; 0x29; 0xd8;        (* SUB (% rax) (% r11) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc0;        (* SUB (% r8) (% rax) *)
  0x49; 0x19; 0xc9;        (* SBB (% r9) (% rcx) *)
  0x49; 0x19; 0xd2;        (* SBB (% r10) (% rdx) *)
  0x49; 0x19; 0xdb;        (* SBB (% r11) (% rbx) *)
  0x4d; 0x01; 0xc4;        (* ADD (% r12) (% r8) *)
  0x4d; 0x11; 0xcd;        (* ADC (% r13) (% r9) *)
  0x4d; 0x11; 0xd6;        (* ADC (% r14) (% r10) *)
  0x4d; 0x11; 0xdf;        (* ADC (% r15) (% r11) *)
  0x48; 0x19; 0xc0;        (* SBB (% rax) (% rax) *)
  0x48; 0xbb; 0x00; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rbx) (Imm64 (word 18446744069414584320)) *)
  0x48; 0x89; 0xc1;        (* MOV (% rcx) (% rax) *)
  0x48; 0x21; 0xc3;        (* AND (% rbx) (% rax) *)
  0x48; 0x0f; 0xba; 0xf1; 0x20;
                           (* BTR (% rcx) (Imm8 (word 32)) *)
  0x49; 0x29; 0xc4;        (* SUB (% r12) (% rax) *)
  0x49; 0x19; 0xdd;        (* SBB (% r13) (% rbx) *)
  0x49; 0x19; 0xc6;        (* SBB (% r14) (% rax) *)
  0x49; 0x19; 0xcf;        (* SBB (% r15) (% rcx) *)
  0x4c; 0x89; 0x64; 0x24; 0x60;
                           (* MOV (Memop Quadword (%% (rsp,96))) (% r12) *)
  0x4c; 0x89; 0x6c; 0x24; 0x68;
                           (* MOV (Memop Quadword (%% (rsp,104))) (% r13) *)
  0x4c; 0x89; 0x74; 0x24; 0x70;
                           (* MOV (Memop Quadword (%% (rsp,112))) (% r14) *)
  0x4c; 0x89; 0x7c; 0x24; 0x78;
                           (* MOV (Memop Quadword (%% (rsp,120))) (% r15) *)
  0x48; 0x8b; 0x54; 0x24; 0x20;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,32))) *)
  0xc4; 0x62; 0xbb; 0xf6; 0xfa;
                           (* MULX4 (% r15,% r8) (% rdx,% rdx) *)
  0xc4; 0x62; 0xb3; 0xf6; 0x54; 0x24; 0x28;
                           (* MULX4 (% r10,% r9) (% rdx,Memop Quadword (%% (rsp,40))) *)
  0xc4; 0x62; 0xa3; 0xf6; 0x64; 0x24; 0x38;
                           (* MULX4 (% r12,% r11) (% rdx,Memop Quadword (%% (rsp,56))) *)
  0x48; 0x8b; 0x54; 0x24; 0x30;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,48))) *)
  0xc4; 0x62; 0x93; 0xf6; 0x74; 0x24; 0x38;
                           (* MULX4 (% r14,% r13) (% rdx,Memop Quadword (%% (rsp,56))) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x20;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,32))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x28;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0x48; 0x8b; 0x54; 0x24; 0x38;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,56))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x28;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADCX (% r13) (% rcx) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADOX (% r14) (% rcx) *)
  0x49; 0x11; 0xce;        (* ADC (% r14) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xc9;
                           (* ADCX (% r9) (% r9) *)
  0xf3; 0x4d; 0x0f; 0x38; 0xf6; 0xcf;
                           (* ADOX (% r9) (% r15) *)
  0x48; 0x8b; 0x54; 0x24; 0x28;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,40))) *)
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
  0x48; 0x8b; 0x54; 0x24; 0x30;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,48))) *)
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
  0x48; 0x8b; 0x54; 0x24; 0x38;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,56))) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xfa;
                           (* MULX4 (% r15,% rax) (% rdx,% rdx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xf6;
                           (* ADCX (% r14) (% r14) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADOX (% r14) (% rax) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADCX (% r15) (% rcx) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADOX (% r15) (% rcx) *)
  0x4c; 0x89; 0xc0;        (* MOV (% rax) (% r8) *)
  0x48; 0xc1; 0xe0; 0x20;  (* SHL (% rax) (Imm8 (word 32)) *)
  0x4c; 0x89; 0xc1;        (* MOV (% rcx) (% r8) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x89; 0xcb;        (* MOV (% rbx) (% rcx) *)
  0x4c; 0x29; 0xc0;        (* SUB (% rax) (% r8) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc1;        (* SUB (% r9) (% rax) *)
  0x49; 0x19; 0xca;        (* SBB (% r10) (% rcx) *)
  0x49; 0x19; 0xd3;        (* SBB (% r11) (% rdx) *)
  0x49; 0x19; 0xd8;        (* SBB (% r8) (% rbx) *)
  0x4c; 0x89; 0xc8;        (* MOV (% rax) (% r9) *)
  0x48; 0xc1; 0xe0; 0x20;  (* SHL (% rax) (Imm8 (word 32)) *)
  0x4c; 0x89; 0xc9;        (* MOV (% rcx) (% r9) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x89; 0xcb;        (* MOV (% rbx) (% rcx) *)
  0x4c; 0x29; 0xc8;        (* SUB (% rax) (% r9) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc2;        (* SUB (% r10) (% rax) *)
  0x49; 0x19; 0xcb;        (* SBB (% r11) (% rcx) *)
  0x49; 0x19; 0xd0;        (* SBB (% r8) (% rdx) *)
  0x49; 0x19; 0xd9;        (* SBB (% r9) (% rbx) *)
  0x4c; 0x89; 0xd0;        (* MOV (% rax) (% r10) *)
  0x48; 0xc1; 0xe0; 0x20;  (* SHL (% rax) (Imm8 (word 32)) *)
  0x4c; 0x89; 0xd1;        (* MOV (% rcx) (% r10) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x89; 0xcb;        (* MOV (% rbx) (% rcx) *)
  0x4c; 0x29; 0xd0;        (* SUB (% rax) (% r10) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc3;        (* SUB (% r11) (% rax) *)
  0x49; 0x19; 0xc8;        (* SBB (% r8) (% rcx) *)
  0x49; 0x19; 0xd1;        (* SBB (% r9) (% rdx) *)
  0x49; 0x19; 0xda;        (* SBB (% r10) (% rbx) *)
  0x4c; 0x89; 0xd8;        (* MOV (% rax) (% r11) *)
  0x48; 0xc1; 0xe0; 0x20;  (* SHL (% rax) (Imm8 (word 32)) *)
  0x4c; 0x89; 0xd9;        (* MOV (% rcx) (% r11) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x89; 0xcb;        (* MOV (% rbx) (% rcx) *)
  0x4c; 0x29; 0xd8;        (* SUB (% rax) (% r11) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc0;        (* SUB (% r8) (% rax) *)
  0x49; 0x19; 0xc9;        (* SBB (% r9) (% rcx) *)
  0x49; 0x19; 0xd2;        (* SBB (% r10) (% rdx) *)
  0x49; 0x19; 0xdb;        (* SBB (% r11) (% rbx) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0x4d; 0x01; 0xc4;        (* ADD (% r12) (% r8) *)
  0x4d; 0x11; 0xcd;        (* ADC (% r13) (% r9) *)
  0x4d; 0x11; 0xd6;        (* ADC (% r14) (% r10) *)
  0x4d; 0x11; 0xdf;        (* ADC (% r15) (% r11) *)
  0x48; 0x11; 0xc0;        (* ADC (% rax) (% rax) *)
  0xb9; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% ecx) (Imm32 (word 1)) *)
  0xba; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% edx) (Imm32 (word 4294967295)) *)
  0x31; 0xdb;              (* XOR (% ebx) (% ebx) *)
  0x4c; 0x01; 0xe1;        (* ADD (% rcx) (% r12) *)
  0x4c; 0x8d; 0x5a; 0x01;  (* LEA (% r11) (%% (rdx,1)) *)
  0x4c; 0x11; 0xea;        (* ADC (% rdx) (% r13) *)
  0x4c; 0x8d; 0x43; 0xff;  (* LEA (% r8) (%% (rbx,18446744073709551615)) *)
  0x4c; 0x11; 0xf3;        (* ADC (% rbx) (% r14) *)
  0x4d; 0x11; 0xfb;        (* ADC (% r11) (% r15) *)
  0x49; 0x11; 0xc0;        (* ADC (% r8) (% rax) *)
  0x4c; 0x0f; 0x42; 0xe1;  (* CMOVB (% r12) (% rcx) *)
  0x4c; 0x0f; 0x42; 0xea;  (* CMOVB (% r13) (% rdx) *)
  0x4c; 0x0f; 0x42; 0xf3;  (* CMOVB (% r14) (% rbx) *)
  0x4d; 0x0f; 0x42; 0xfb;  (* CMOVB (% r15) (% r11) *)
  0x4c; 0x89; 0x24; 0x24;  (* MOV (Memop Quadword (%% (rsp,0))) (% r12) *)
  0x4c; 0x89; 0x6c; 0x24; 0x08;
                           (* MOV (Memop Quadword (%% (rsp,8))) (% r13) *)
  0x4c; 0x89; 0x74; 0x24; 0x10;
                           (* MOV (Memop Quadword (%% (rsp,16))) (% r14) *)
  0x4c; 0x89; 0x7c; 0x24; 0x18;
                           (* MOV (Memop Quadword (%% (rsp,24))) (% r15) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x94; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,128))) *)
  0xc4; 0x62; 0xbb; 0xf6; 0x4c; 0x24; 0x60;
                           (* MULX4 (% r9,% r8) (% rdx,Memop Quadword (%% (rsp,96))) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x54; 0x24; 0x68;
                           (* MULX4 (% r10,% rax) (% rdx,Memop Quadword (%% (rsp,104))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x5c; 0x24; 0x70;
                           (* MULX4 (% r11,% rax) (% rdx,Memop Quadword (%% (rsp,112))) *)
  0x49; 0x11; 0xc2;        (* ADC (% r10) (% rax) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x64; 0x24; 0x78;
                           (* MULX4 (% r12,% rax) (% rdx,Memop Quadword (%% (rsp,120))) *)
  0x49; 0x11; 0xc3;        (* ADC (% r11) (% rax) *)
  0x49; 0x11; 0xcc;        (* ADC (% r12) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x94; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,136))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x60;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,96))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x68;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,104))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x70;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,112))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x6c; 0x24; 0x78;
                           (* MULX4 (% r13,% rax) (% rdx,Memop Quadword (%% (rsp,120))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADOX (% r13) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADCX (% r13) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x94; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,144))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x60;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,96))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x68;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,104))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x70;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,112))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x74; 0x24; 0x78;
                           (* MULX4 (% r14,% rax) (% rdx,Memop Quadword (%% (rsp,120))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADOX (% r14) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADCX (% r14) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x94; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,152))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x60;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,96))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x68;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,104))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x70;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,112))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x7c; 0x24; 0x78;
                           (* MULX4 (% r15,% rax) (% rdx,Memop Quadword (%% (rsp,120))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADOX (% r15) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADCX (% r15) (% rcx) *)
  0x4c; 0x89; 0xc0;        (* MOV (% rax) (% r8) *)
  0x48; 0xc1; 0xe0; 0x20;  (* SHL (% rax) (Imm8 (word 32)) *)
  0x4c; 0x89; 0xc1;        (* MOV (% rcx) (% r8) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x89; 0xcb;        (* MOV (% rbx) (% rcx) *)
  0x4c; 0x29; 0xc0;        (* SUB (% rax) (% r8) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc1;        (* SUB (% r9) (% rax) *)
  0x49; 0x19; 0xca;        (* SBB (% r10) (% rcx) *)
  0x49; 0x19; 0xd3;        (* SBB (% r11) (% rdx) *)
  0x49; 0x19; 0xd8;        (* SBB (% r8) (% rbx) *)
  0x4c; 0x89; 0xc8;        (* MOV (% rax) (% r9) *)
  0x48; 0xc1; 0xe0; 0x20;  (* SHL (% rax) (Imm8 (word 32)) *)
  0x4c; 0x89; 0xc9;        (* MOV (% rcx) (% r9) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x89; 0xcb;        (* MOV (% rbx) (% rcx) *)
  0x4c; 0x29; 0xc8;        (* SUB (% rax) (% r9) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc2;        (* SUB (% r10) (% rax) *)
  0x49; 0x19; 0xcb;        (* SBB (% r11) (% rcx) *)
  0x49; 0x19; 0xd0;        (* SBB (% r8) (% rdx) *)
  0x49; 0x19; 0xd9;        (* SBB (% r9) (% rbx) *)
  0x4c; 0x89; 0xd0;        (* MOV (% rax) (% r10) *)
  0x48; 0xc1; 0xe0; 0x20;  (* SHL (% rax) (Imm8 (word 32)) *)
  0x4c; 0x89; 0xd1;        (* MOV (% rcx) (% r10) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x89; 0xcb;        (* MOV (% rbx) (% rcx) *)
  0x4c; 0x29; 0xd0;        (* SUB (% rax) (% r10) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc3;        (* SUB (% r11) (% rax) *)
  0x49; 0x19; 0xc8;        (* SBB (% r8) (% rcx) *)
  0x49; 0x19; 0xd1;        (* SBB (% r9) (% rdx) *)
  0x49; 0x19; 0xda;        (* SBB (% r10) (% rbx) *)
  0x4c; 0x89; 0xd8;        (* MOV (% rax) (% r11) *)
  0x48; 0xc1; 0xe0; 0x20;  (* SHL (% rax) (Imm8 (word 32)) *)
  0x4c; 0x89; 0xd9;        (* MOV (% rcx) (% r11) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x89; 0xcb;        (* MOV (% rbx) (% rcx) *)
  0x4c; 0x29; 0xd8;        (* SUB (% rax) (% r11) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc0;        (* SUB (% r8) (% rax) *)
  0x49; 0x19; 0xc9;        (* SBB (% r9) (% rcx) *)
  0x49; 0x19; 0xd2;        (* SBB (% r10) (% rdx) *)
  0x49; 0x19; 0xdb;        (* SBB (% r11) (% rbx) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0x4d; 0x01; 0xc4;        (* ADD (% r12) (% r8) *)
  0x4d; 0x11; 0xcd;        (* ADC (% r13) (% r9) *)
  0x4d; 0x11; 0xd6;        (* ADC (% r14) (% r10) *)
  0x4d; 0x11; 0xdf;        (* ADC (% r15) (% r11) *)
  0x48; 0x11; 0xc0;        (* ADC (% rax) (% rax) *)
  0xb9; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% ecx) (Imm32 (word 1)) *)
  0xba; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% edx) (Imm32 (word 4294967295)) *)
  0x31; 0xdb;              (* XOR (% ebx) (% ebx) *)
  0x4c; 0x01; 0xe1;        (* ADD (% rcx) (% r12) *)
  0x4c; 0x8d; 0x5a; 0x01;  (* LEA (% r11) (%% (rdx,1)) *)
  0x4c; 0x11; 0xea;        (* ADC (% rdx) (% r13) *)
  0x4c; 0x8d; 0x43; 0xff;  (* LEA (% r8) (%% (rbx,18446744073709551615)) *)
  0x4c; 0x11; 0xf3;        (* ADC (% rbx) (% r14) *)
  0x4d; 0x11; 0xfb;        (* ADC (% r11) (% r15) *)
  0x49; 0x11; 0xc0;        (* ADC (% r8) (% rax) *)
  0x4c; 0x0f; 0x42; 0xe1;  (* CMOVB (% r12) (% rcx) *)
  0x4c; 0x0f; 0x42; 0xea;  (* CMOVB (% r13) (% rdx) *)
  0x4c; 0x0f; 0x42; 0xf3;  (* CMOVB (% r14) (% rbx) *)
  0x4d; 0x0f; 0x42; 0xfb;  (* CMOVB (% r15) (% r11) *)
  0x4c; 0x89; 0xa4; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,128))) (% r12) *)
  0x4c; 0x89; 0xac; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,136))) (% r13) *)
  0x4c; 0x89; 0xb4; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,144))) (% r14) *)
  0x4c; 0x89; 0xbc; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,152))) (% r15) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x54; 0x24; 0x40;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,64))) *)
  0xc4; 0x62; 0xbb; 0xf6; 0x4c; 0x24; 0x60;
                           (* MULX4 (% r9,% r8) (% rdx,Memop Quadword (%% (rsp,96))) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x54; 0x24; 0x68;
                           (* MULX4 (% r10,% rax) (% rdx,Memop Quadword (%% (rsp,104))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x5c; 0x24; 0x70;
                           (* MULX4 (% r11,% rax) (% rdx,Memop Quadword (%% (rsp,112))) *)
  0x49; 0x11; 0xc2;        (* ADC (% r10) (% rax) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x64; 0x24; 0x78;
                           (* MULX4 (% r12,% rax) (% rdx,Memop Quadword (%% (rsp,120))) *)
  0x49; 0x11; 0xc3;        (* ADC (% r11) (% rax) *)
  0x49; 0x11; 0xcc;        (* ADC (% r12) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x54; 0x24; 0x48;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,72))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x60;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,96))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x68;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,104))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x70;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,112))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x6c; 0x24; 0x78;
                           (* MULX4 (% r13,% rax) (% rdx,Memop Quadword (%% (rsp,120))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADOX (% r13) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADCX (% r13) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x54; 0x24; 0x50;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,80))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x60;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,96))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x68;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,104))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x70;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,112))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x74; 0x24; 0x78;
                           (* MULX4 (% r14,% rax) (% rdx,Memop Quadword (%% (rsp,120))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADOX (% r14) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADCX (% r14) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x54; 0x24; 0x58;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,88))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x60;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,96))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x68;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,104))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x70;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,112))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x7c; 0x24; 0x78;
                           (* MULX4 (% r15,% rax) (% rdx,Memop Quadword (%% (rsp,120))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADOX (% r15) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADCX (% r15) (% rcx) *)
  0x4c; 0x89; 0xc0;        (* MOV (% rax) (% r8) *)
  0x48; 0xc1; 0xe0; 0x20;  (* SHL (% rax) (Imm8 (word 32)) *)
  0x4c; 0x89; 0xc1;        (* MOV (% rcx) (% r8) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x89; 0xcb;        (* MOV (% rbx) (% rcx) *)
  0x4c; 0x29; 0xc0;        (* SUB (% rax) (% r8) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc1;        (* SUB (% r9) (% rax) *)
  0x49; 0x19; 0xca;        (* SBB (% r10) (% rcx) *)
  0x49; 0x19; 0xd3;        (* SBB (% r11) (% rdx) *)
  0x49; 0x19; 0xd8;        (* SBB (% r8) (% rbx) *)
  0x4c; 0x89; 0xc8;        (* MOV (% rax) (% r9) *)
  0x48; 0xc1; 0xe0; 0x20;  (* SHL (% rax) (Imm8 (word 32)) *)
  0x4c; 0x89; 0xc9;        (* MOV (% rcx) (% r9) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x89; 0xcb;        (* MOV (% rbx) (% rcx) *)
  0x4c; 0x29; 0xc8;        (* SUB (% rax) (% r9) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc2;        (* SUB (% r10) (% rax) *)
  0x49; 0x19; 0xcb;        (* SBB (% r11) (% rcx) *)
  0x49; 0x19; 0xd0;        (* SBB (% r8) (% rdx) *)
  0x49; 0x19; 0xd9;        (* SBB (% r9) (% rbx) *)
  0x4c; 0x89; 0xd0;        (* MOV (% rax) (% r10) *)
  0x48; 0xc1; 0xe0; 0x20;  (* SHL (% rax) (Imm8 (word 32)) *)
  0x4c; 0x89; 0xd1;        (* MOV (% rcx) (% r10) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x89; 0xcb;        (* MOV (% rbx) (% rcx) *)
  0x4c; 0x29; 0xd0;        (* SUB (% rax) (% r10) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc3;        (* SUB (% r11) (% rax) *)
  0x49; 0x19; 0xc8;        (* SBB (% r8) (% rcx) *)
  0x49; 0x19; 0xd1;        (* SBB (% r9) (% rdx) *)
  0x49; 0x19; 0xda;        (* SBB (% r10) (% rbx) *)
  0x4c; 0x89; 0xd8;        (* MOV (% rax) (% r11) *)
  0x48; 0xc1; 0xe0; 0x20;  (* SHL (% rax) (Imm8 (word 32)) *)
  0x4c; 0x89; 0xd9;        (* MOV (% rcx) (% r11) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x89; 0xcb;        (* MOV (% rbx) (% rcx) *)
  0x4c; 0x29; 0xd8;        (* SUB (% rax) (% r11) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc0;        (* SUB (% r8) (% rax) *)
  0x49; 0x19; 0xc9;        (* SBB (% r9) (% rcx) *)
  0x49; 0x19; 0xd2;        (* SBB (% r10) (% rdx) *)
  0x49; 0x19; 0xdb;        (* SBB (% r11) (% rbx) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0x4d; 0x01; 0xc4;        (* ADD (% r12) (% r8) *)
  0x4d; 0x11; 0xcd;        (* ADC (% r13) (% r9) *)
  0x4d; 0x11; 0xd6;        (* ADC (% r14) (% r10) *)
  0x4d; 0x11; 0xdf;        (* ADC (% r15) (% r11) *)
  0x48; 0x11; 0xc0;        (* ADC (% rax) (% rax) *)
  0xb9; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% ecx) (Imm32 (word 1)) *)
  0xba; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% edx) (Imm32 (word 4294967295)) *)
  0x31; 0xdb;              (* XOR (% ebx) (% ebx) *)
  0x4c; 0x01; 0xe1;        (* ADD (% rcx) (% r12) *)
  0x4c; 0x8d; 0x5a; 0x01;  (* LEA (% r11) (%% (rdx,1)) *)
  0x4c; 0x11; 0xea;        (* ADC (% rdx) (% r13) *)
  0x4c; 0x8d; 0x43; 0xff;  (* LEA (% r8) (%% (rbx,18446744073709551615)) *)
  0x4c; 0x11; 0xf3;        (* ADC (% rbx) (% r14) *)
  0x4d; 0x11; 0xfb;        (* ADC (% r11) (% r15) *)
  0x49; 0x11; 0xc0;        (* ADC (% r8) (% rax) *)
  0x4c; 0x0f; 0x42; 0xe1;  (* CMOVB (% r12) (% rcx) *)
  0x4c; 0x0f; 0x42; 0xea;  (* CMOVB (% r13) (% rdx) *)
  0x4c; 0x0f; 0x42; 0xf3;  (* CMOVB (% r14) (% rbx) *)
  0x4d; 0x0f; 0x42; 0xfb;  (* CMOVB (% r15) (% r11) *)
  0x4c; 0x89; 0x64; 0x24; 0x40;
                           (* MOV (Memop Quadword (%% (rsp,64))) (% r12) *)
  0x4c; 0x89; 0x6c; 0x24; 0x48;
                           (* MOV (Memop Quadword (%% (rsp,72))) (% r13) *)
  0x4c; 0x89; 0x74; 0x24; 0x50;
                           (* MOV (Memop Quadword (%% (rsp,80))) (% r14) *)
  0x4c; 0x89; 0x7c; 0x24; 0x58;
                           (* MOV (Memop Quadword (%% (rsp,88))) (% r15) *)
  0x48; 0x8b; 0x04; 0x24;  (* MOV (% rax) (Memop Quadword (%% (rsp,0))) *)
  0x48; 0x2b; 0x84; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* SUB (% rax) (Memop Quadword (%% (rsp,128))) *)
  0x48; 0x8b; 0x4c; 0x24; 0x08;
                           (* MOV (% rcx) (Memop Quadword (%% (rsp,8))) *)
  0x48; 0x1b; 0x8c; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* SBB (% rcx) (Memop Quadword (%% (rsp,136))) *)
  0x4c; 0x8b; 0x44; 0x24; 0x10;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,16))) *)
  0x4c; 0x1b; 0x84; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* SBB (% r8) (Memop Quadword (%% (rsp,144))) *)
  0x4c; 0x8b; 0x4c; 0x24; 0x18;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,24))) *)
  0x4c; 0x1b; 0x8c; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* SBB (% r9) (Memop Quadword (%% (rsp,152))) *)
  0x49; 0xba; 0x00; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r10) (Imm64 (word 18446744069414584320)) *)
  0x4d; 0x19; 0xdb;        (* SBB (% r11) (% r11) *)
  0x4d; 0x21; 0xda;        (* AND (% r10) (% r11) *)
  0x4c; 0x89; 0xda;        (* MOV (% rdx) (% r11) *)
  0x48; 0x0f; 0xba; 0xf2; 0x20;
                           (* BTR (% rdx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xd8;        (* ADD (% rax) (% r11) *)
  0x48; 0x89; 0x07;        (* MOV (Memop Quadword (%% (rdi,0))) (% rax) *)
  0x4c; 0x11; 0xd1;        (* ADC (% rcx) (% r10) *)
  0x48; 0x89; 0x4f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% rcx) *)
  0x4d; 0x11; 0xd8;        (* ADC (% r8) (% r11) *)
  0x4c; 0x89; 0x47; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r8) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x4c; 0x89; 0x4f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r9) *)
  0x48; 0x8b; 0x44; 0x24; 0x40;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,64))) *)
  0x48; 0x2b; 0x84; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* SUB (% rax) (Memop Quadword (%% (rsp,128))) *)
  0x48; 0x8b; 0x4c; 0x24; 0x48;
                           (* MOV (% rcx) (Memop Quadword (%% (rsp,72))) *)
  0x48; 0x1b; 0x8c; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* SBB (% rcx) (Memop Quadword (%% (rsp,136))) *)
  0x4c; 0x8b; 0x44; 0x24; 0x50;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,80))) *)
  0x4c; 0x1b; 0x84; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* SBB (% r8) (Memop Quadword (%% (rsp,144))) *)
  0x4c; 0x8b; 0x4c; 0x24; 0x58;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,88))) *)
  0x4c; 0x1b; 0x8c; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* SBB (% r9) (Memop Quadword (%% (rsp,152))) *)
  0x49; 0xba; 0x00; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r10) (Imm64 (word 18446744069414584320)) *)
  0x4d; 0x19; 0xdb;        (* SBB (% r11) (% r11) *)
  0x4d; 0x21; 0xda;        (* AND (% r10) (% r11) *)
  0x4c; 0x89; 0xda;        (* MOV (% rdx) (% r11) *)
  0x48; 0x0f; 0xba; 0xf2; 0x20;
                           (* BTR (% rdx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xd8;        (* ADD (% rax) (% r11) *)
  0x48; 0x89; 0x44; 0x24; 0x60;
                           (* MOV (Memop Quadword (%% (rsp,96))) (% rax) *)
  0x4c; 0x11; 0xd1;        (* ADC (% rcx) (% r10) *)
  0x48; 0x89; 0x4c; 0x24; 0x68;
                           (* MOV (Memop Quadword (%% (rsp,104))) (% rcx) *)
  0x4d; 0x11; 0xd8;        (* ADC (% r8) (% r11) *)
  0x4c; 0x89; 0x44; 0x24; 0x70;
                           (* MOV (Memop Quadword (%% (rsp,112))) (% r8) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x4c; 0x89; 0x4c; 0x24; 0x78;
                           (* MOV (Memop Quadword (%% (rsp,120))) (% r9) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x56; 0x40;  (* MOV (% rdx) (Memop Quadword (%% (rsi,64))) *)
  0xc4; 0x62; 0xbb; 0xf6; 0x8c; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MULX4 (% r9,% r8) (% rdx,Memop Quadword (%% (rsp,160))) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x94; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MULX4 (% r10,% rax) (% rdx,Memop Quadword (%% (rsp,168))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x9c; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MULX4 (% r11,% rax) (% rdx,Memop Quadword (%% (rsp,176))) *)
  0x49; 0x11; 0xc2;        (* ADC (% r10) (% rax) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xa4; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MULX4 (% r12,% rax) (% rdx,Memop Quadword (%% (rsp,184))) *)
  0x49; 0x11; 0xc3;        (* ADC (% r11) (% rax) *)
  0x49; 0x11; 0xcc;        (* ADC (% r12) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x56; 0x48;  (* MOV (% rdx) (Memop Quadword (%% (rsi,72))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,160))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,168))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,176))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xac; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MULX4 (% r13,% rax) (% rdx,Memop Quadword (%% (rsp,184))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADOX (% r13) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADCX (% r13) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x56; 0x50;  (* MOV (% rdx) (Memop Quadword (%% (rsi,80))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,160))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,168))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,176))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xb4; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MULX4 (% r14,% rax) (% rdx,Memop Quadword (%% (rsp,184))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADOX (% r14) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADCX (% r14) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x56; 0x58;  (* MOV (% rdx) (Memop Quadword (%% (rsi,88))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,160))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,168))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,176))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xbc; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MULX4 (% r15,% rax) (% rdx,Memop Quadword (%% (rsp,184))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADOX (% r15) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADCX (% r15) (% rcx) *)
  0x4c; 0x89; 0xc0;        (* MOV (% rax) (% r8) *)
  0x48; 0xc1; 0xe0; 0x20;  (* SHL (% rax) (Imm8 (word 32)) *)
  0x4c; 0x89; 0xc1;        (* MOV (% rcx) (% r8) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x89; 0xcb;        (* MOV (% rbx) (% rcx) *)
  0x4c; 0x29; 0xc0;        (* SUB (% rax) (% r8) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc1;        (* SUB (% r9) (% rax) *)
  0x49; 0x19; 0xca;        (* SBB (% r10) (% rcx) *)
  0x49; 0x19; 0xd3;        (* SBB (% r11) (% rdx) *)
  0x49; 0x19; 0xd8;        (* SBB (% r8) (% rbx) *)
  0x4c; 0x89; 0xc8;        (* MOV (% rax) (% r9) *)
  0x48; 0xc1; 0xe0; 0x20;  (* SHL (% rax) (Imm8 (word 32)) *)
  0x4c; 0x89; 0xc9;        (* MOV (% rcx) (% r9) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x89; 0xcb;        (* MOV (% rbx) (% rcx) *)
  0x4c; 0x29; 0xc8;        (* SUB (% rax) (% r9) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc2;        (* SUB (% r10) (% rax) *)
  0x49; 0x19; 0xcb;        (* SBB (% r11) (% rcx) *)
  0x49; 0x19; 0xd0;        (* SBB (% r8) (% rdx) *)
  0x49; 0x19; 0xd9;        (* SBB (% r9) (% rbx) *)
  0x4c; 0x89; 0xd0;        (* MOV (% rax) (% r10) *)
  0x48; 0xc1; 0xe0; 0x20;  (* SHL (% rax) (Imm8 (word 32)) *)
  0x4c; 0x89; 0xd1;        (* MOV (% rcx) (% r10) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x89; 0xcb;        (* MOV (% rbx) (% rcx) *)
  0x4c; 0x29; 0xd0;        (* SUB (% rax) (% r10) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc3;        (* SUB (% r11) (% rax) *)
  0x49; 0x19; 0xc8;        (* SBB (% r8) (% rcx) *)
  0x49; 0x19; 0xd1;        (* SBB (% r9) (% rdx) *)
  0x49; 0x19; 0xda;        (* SBB (% r10) (% rbx) *)
  0x4c; 0x89; 0xd8;        (* MOV (% rax) (% r11) *)
  0x48; 0xc1; 0xe0; 0x20;  (* SHL (% rax) (Imm8 (word 32)) *)
  0x4c; 0x89; 0xd9;        (* MOV (% rcx) (% r11) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x89; 0xcb;        (* MOV (% rbx) (% rcx) *)
  0x4c; 0x29; 0xd8;        (* SUB (% rax) (% r11) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc0;        (* SUB (% r8) (% rax) *)
  0x49; 0x19; 0xc9;        (* SBB (% r9) (% rcx) *)
  0x49; 0x19; 0xd2;        (* SBB (% r10) (% rdx) *)
  0x49; 0x19; 0xdb;        (* SBB (% r11) (% rbx) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0x4d; 0x01; 0xc4;        (* ADD (% r12) (% r8) *)
  0x4d; 0x11; 0xcd;        (* ADC (% r13) (% r9) *)
  0x4d; 0x11; 0xd6;        (* ADC (% r14) (% r10) *)
  0x4d; 0x11; 0xdf;        (* ADC (% r15) (% r11) *)
  0x48; 0x11; 0xc0;        (* ADC (% rax) (% rax) *)
  0xb9; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% ecx) (Imm32 (word 1)) *)
  0xba; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% edx) (Imm32 (word 4294967295)) *)
  0x31; 0xdb;              (* XOR (% ebx) (% ebx) *)
  0x4c; 0x01; 0xe1;        (* ADD (% rcx) (% r12) *)
  0x4c; 0x8d; 0x5a; 0x01;  (* LEA (% r11) (%% (rdx,1)) *)
  0x4c; 0x11; 0xea;        (* ADC (% rdx) (% r13) *)
  0x4c; 0x8d; 0x43; 0xff;  (* LEA (% r8) (%% (rbx,18446744073709551615)) *)
  0x4c; 0x11; 0xf3;        (* ADC (% rbx) (% r14) *)
  0x4d; 0x11; 0xfb;        (* ADC (% r11) (% r15) *)
  0x49; 0x11; 0xc0;        (* ADC (% r8) (% rax) *)
  0x4c; 0x0f; 0x42; 0xe1;  (* CMOVB (% r12) (% rcx) *)
  0x4c; 0x0f; 0x42; 0xea;  (* CMOVB (% r13) (% rdx) *)
  0x4c; 0x0f; 0x42; 0xf3;  (* CMOVB (% r14) (% rbx) *)
  0x4d; 0x0f; 0x42; 0xfb;  (* CMOVB (% r15) (% r11) *)
  0x4c; 0x89; 0xa4; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,160))) (% r12) *)
  0x4c; 0x89; 0xac; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,168))) (% r13) *)
  0x4c; 0x89; 0xb4; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,176))) (% r14) *)
  0x4c; 0x89; 0xbc; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,184))) (% r15) *)
  0x48; 0x8b; 0x07;        (* MOV (% rax) (Memop Quadword (%% (rdi,0))) *)
  0x48; 0x2b; 0x44; 0x24; 0x40;
                           (* SUB (% rax) (Memop Quadword (%% (rsp,64))) *)
  0x48; 0x8b; 0x4f; 0x08;  (* MOV (% rcx) (Memop Quadword (%% (rdi,8))) *)
  0x48; 0x1b; 0x4c; 0x24; 0x48;
                           (* SBB (% rcx) (Memop Quadword (%% (rsp,72))) *)
  0x4c; 0x8b; 0x47; 0x10;  (* MOV (% r8) (Memop Quadword (%% (rdi,16))) *)
  0x4c; 0x1b; 0x44; 0x24; 0x50;
                           (* SBB (% r8) (Memop Quadword (%% (rsp,80))) *)
  0x4c; 0x8b; 0x4f; 0x18;  (* MOV (% r9) (Memop Quadword (%% (rdi,24))) *)
  0x4c; 0x1b; 0x4c; 0x24; 0x58;
                           (* SBB (% r9) (Memop Quadword (%% (rsp,88))) *)
  0x49; 0xba; 0x00; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r10) (Imm64 (word 18446744069414584320)) *)
  0x4d; 0x19; 0xdb;        (* SBB (% r11) (% r11) *)
  0x4d; 0x21; 0xda;        (* AND (% r10) (% r11) *)
  0x4c; 0x89; 0xda;        (* MOV (% rdx) (% r11) *)
  0x48; 0x0f; 0xba; 0xf2; 0x20;
                           (* BTR (% rdx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xd8;        (* ADD (% rax) (% r11) *)
  0x48; 0x89; 0x07;        (* MOV (Memop Quadword (%% (rdi,0))) (% rax) *)
  0x4c; 0x11; 0xd1;        (* ADC (% rcx) (% r10) *)
  0x48; 0x89; 0x4f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% rcx) *)
  0x4d; 0x11; 0xd8;        (* ADC (% r8) (% r11) *)
  0x4c; 0x89; 0x47; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r8) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x4c; 0x89; 0x4f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r9) *)
  0x48; 0x8b; 0x84; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,128))) *)
  0x48; 0x2b; 0x07;        (* SUB (% rax) (Memop Quadword (%% (rdi,0))) *)
  0x48; 0x8b; 0x8c; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (% rcx) (Memop Quadword (%% (rsp,136))) *)
  0x48; 0x1b; 0x4f; 0x08;  (* SBB (% rcx) (Memop Quadword (%% (rdi,8))) *)
  0x4c; 0x8b; 0x84; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,144))) *)
  0x4c; 0x1b; 0x47; 0x10;  (* SBB (% r8) (Memop Quadword (%% (rdi,16))) *)
  0x4c; 0x8b; 0x8c; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,152))) *)
  0x4c; 0x1b; 0x4f; 0x18;  (* SBB (% r9) (Memop Quadword (%% (rdi,24))) *)
  0x49; 0xba; 0x00; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r10) (Imm64 (word 18446744069414584320)) *)
  0x4d; 0x19; 0xdb;        (* SBB (% r11) (% r11) *)
  0x4d; 0x21; 0xda;        (* AND (% r10) (% r11) *)
  0x4c; 0x89; 0xda;        (* MOV (% rdx) (% r11) *)
  0x48; 0x0f; 0xba; 0xf2; 0x20;
                           (* BTR (% rdx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xd8;        (* ADD (% rax) (% r11) *)
  0x48; 0x89; 0x84; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,128))) (% rax) *)
  0x4c; 0x11; 0xd1;        (* ADC (% rcx) (% r10) *)
  0x48; 0x89; 0x8c; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,136))) (% rcx) *)
  0x4d; 0x11; 0xd8;        (* ADC (% r8) (% r11) *)
  0x4c; 0x89; 0x84; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,144))) (% r8) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x4c; 0x89; 0x8c; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,152))) (% r9) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x94; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,192))) *)
  0xc4; 0x62; 0xbb; 0xf6; 0x4c; 0x24; 0x60;
                           (* MULX4 (% r9,% r8) (% rdx,Memop Quadword (%% (rsp,96))) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x54; 0x24; 0x68;
                           (* MULX4 (% r10,% rax) (% rdx,Memop Quadword (%% (rsp,104))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x5c; 0x24; 0x70;
                           (* MULX4 (% r11,% rax) (% rdx,Memop Quadword (%% (rsp,112))) *)
  0x49; 0x11; 0xc2;        (* ADC (% r10) (% rax) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x64; 0x24; 0x78;
                           (* MULX4 (% r12,% rax) (% rdx,Memop Quadword (%% (rsp,120))) *)
  0x49; 0x11; 0xc3;        (* ADC (% r11) (% rax) *)
  0x49; 0x11; 0xcc;        (* ADC (% r12) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x94; 0x24; 0xc8; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,200))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x60;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,96))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x68;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,104))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x70;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,112))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x6c; 0x24; 0x78;
                           (* MULX4 (% r13,% rax) (% rdx,Memop Quadword (%% (rsp,120))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADOX (% r13) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADCX (% r13) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x94; 0x24; 0xd0; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,208))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x60;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,96))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x68;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,104))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x70;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,112))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x74; 0x24; 0x78;
                           (* MULX4 (% r14,% rax) (% rdx,Memop Quadword (%% (rsp,120))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADOX (% r14) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADCX (% r14) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x94; 0x24; 0xd8; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,216))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x60;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,96))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x68;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,104))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x70;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,112))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x7c; 0x24; 0x78;
                           (* MULX4 (% r15,% rax) (% rdx,Memop Quadword (%% (rsp,120))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADOX (% r15) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADCX (% r15) (% rcx) *)
  0x4c; 0x89; 0xc0;        (* MOV (% rax) (% r8) *)
  0x48; 0xc1; 0xe0; 0x20;  (* SHL (% rax) (Imm8 (word 32)) *)
  0x4c; 0x89; 0xc1;        (* MOV (% rcx) (% r8) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x89; 0xcb;        (* MOV (% rbx) (% rcx) *)
  0x4c; 0x29; 0xc0;        (* SUB (% rax) (% r8) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc1;        (* SUB (% r9) (% rax) *)
  0x49; 0x19; 0xca;        (* SBB (% r10) (% rcx) *)
  0x49; 0x19; 0xd3;        (* SBB (% r11) (% rdx) *)
  0x49; 0x19; 0xd8;        (* SBB (% r8) (% rbx) *)
  0x4c; 0x89; 0xc8;        (* MOV (% rax) (% r9) *)
  0x48; 0xc1; 0xe0; 0x20;  (* SHL (% rax) (Imm8 (word 32)) *)
  0x4c; 0x89; 0xc9;        (* MOV (% rcx) (% r9) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x89; 0xcb;        (* MOV (% rbx) (% rcx) *)
  0x4c; 0x29; 0xc8;        (* SUB (% rax) (% r9) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc2;        (* SUB (% r10) (% rax) *)
  0x49; 0x19; 0xcb;        (* SBB (% r11) (% rcx) *)
  0x49; 0x19; 0xd0;        (* SBB (% r8) (% rdx) *)
  0x49; 0x19; 0xd9;        (* SBB (% r9) (% rbx) *)
  0x4c; 0x89; 0xd0;        (* MOV (% rax) (% r10) *)
  0x48; 0xc1; 0xe0; 0x20;  (* SHL (% rax) (Imm8 (word 32)) *)
  0x4c; 0x89; 0xd1;        (* MOV (% rcx) (% r10) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x89; 0xcb;        (* MOV (% rbx) (% rcx) *)
  0x4c; 0x29; 0xd0;        (* SUB (% rax) (% r10) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc3;        (* SUB (% r11) (% rax) *)
  0x49; 0x19; 0xc8;        (* SBB (% r8) (% rcx) *)
  0x49; 0x19; 0xd1;        (* SBB (% r9) (% rdx) *)
  0x49; 0x19; 0xda;        (* SBB (% r10) (% rbx) *)
  0x4c; 0x89; 0xd8;        (* MOV (% rax) (% r11) *)
  0x48; 0xc1; 0xe0; 0x20;  (* SHL (% rax) (Imm8 (word 32)) *)
  0x4c; 0x89; 0xd9;        (* MOV (% rcx) (% r11) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x89; 0xcb;        (* MOV (% rbx) (% rcx) *)
  0x4c; 0x29; 0xd8;        (* SUB (% rax) (% r11) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc0;        (* SUB (% r8) (% rax) *)
  0x49; 0x19; 0xc9;        (* SBB (% r9) (% rcx) *)
  0x49; 0x19; 0xd2;        (* SBB (% r10) (% rdx) *)
  0x49; 0x19; 0xdb;        (* SBB (% r11) (% rbx) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0x4d; 0x01; 0xc4;        (* ADD (% r12) (% r8) *)
  0x4d; 0x11; 0xcd;        (* ADC (% r13) (% r9) *)
  0x4d; 0x11; 0xd6;        (* ADC (% r14) (% r10) *)
  0x4d; 0x11; 0xdf;        (* ADC (% r15) (% r11) *)
  0x48; 0x11; 0xc0;        (* ADC (% rax) (% rax) *)
  0xb9; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% ecx) (Imm32 (word 1)) *)
  0xba; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% edx) (Imm32 (word 4294967295)) *)
  0x31; 0xdb;              (* XOR (% ebx) (% ebx) *)
  0x4c; 0x01; 0xe1;        (* ADD (% rcx) (% r12) *)
  0x4c; 0x8d; 0x5a; 0x01;  (* LEA (% r11) (%% (rdx,1)) *)
  0x4c; 0x11; 0xea;        (* ADC (% rdx) (% r13) *)
  0x4c; 0x8d; 0x43; 0xff;  (* LEA (% r8) (%% (rbx,18446744073709551615)) *)
  0x4c; 0x11; 0xf3;        (* ADC (% rbx) (% r14) *)
  0x4d; 0x11; 0xfb;        (* ADC (% r11) (% r15) *)
  0x49; 0x11; 0xc0;        (* ADC (% r8) (% rax) *)
  0x4c; 0x0f; 0x42; 0xe1;  (* CMOVB (% r12) (% rcx) *)
  0x4c; 0x0f; 0x42; 0xea;  (* CMOVB (% r13) (% rdx) *)
  0x4c; 0x0f; 0x42; 0xf3;  (* CMOVB (% r14) (% rbx) *)
  0x4d; 0x0f; 0x42; 0xfb;  (* CMOVB (% r15) (% r11) *)
  0x4c; 0x89; 0x64; 0x24; 0x60;
                           (* MOV (Memop Quadword (%% (rsp,96))) (% r12) *)
  0x4c; 0x89; 0x6c; 0x24; 0x68;
                           (* MOV (Memop Quadword (%% (rsp,104))) (% r13) *)
  0x4c; 0x89; 0x74; 0x24; 0x70;
                           (* MOV (Memop Quadword (%% (rsp,112))) (% r14) *)
  0x4c; 0x89; 0x7c; 0x24; 0x78;
                           (* MOV (Memop Quadword (%% (rsp,120))) (% r15) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x55; 0x40;  (* MOV (% rdx) (Memop Quadword (%% (rbp,64))) *)
  0xc4; 0x62; 0xbb; 0xf6; 0x8c; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MULX4 (% r9,% r8) (% rdx,Memop Quadword (%% (rsp,160))) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x94; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MULX4 (% r10,% rax) (% rdx,Memop Quadword (%% (rsp,168))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x9c; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MULX4 (% r11,% rax) (% rdx,Memop Quadword (%% (rsp,176))) *)
  0x49; 0x11; 0xc2;        (* ADC (% r10) (% rax) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xa4; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MULX4 (% r12,% rax) (% rdx,Memop Quadword (%% (rsp,184))) *)
  0x49; 0x11; 0xc3;        (* ADC (% r11) (% rax) *)
  0x49; 0x11; 0xcc;        (* ADC (% r12) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x55; 0x48;  (* MOV (% rdx) (Memop Quadword (%% (rbp,72))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,160))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,168))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,176))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xac; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MULX4 (% r13,% rax) (% rdx,Memop Quadword (%% (rsp,184))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADOX (% r13) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADCX (% r13) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x55; 0x50;  (* MOV (% rdx) (Memop Quadword (%% (rbp,80))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,160))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,168))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,176))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xb4; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MULX4 (% r14,% rax) (% rdx,Memop Quadword (%% (rsp,184))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADOX (% r14) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADCX (% r14) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x55; 0x58;  (* MOV (% rdx) (Memop Quadword (%% (rbp,88))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,160))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,168))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,176))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xbc; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MULX4 (% r15,% rax) (% rdx,Memop Quadword (%% (rsp,184))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADOX (% r15) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADCX (% r15) (% rcx) *)
  0x4c; 0x89; 0xc0;        (* MOV (% rax) (% r8) *)
  0x48; 0xc1; 0xe0; 0x20;  (* SHL (% rax) (Imm8 (word 32)) *)
  0x4c; 0x89; 0xc1;        (* MOV (% rcx) (% r8) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x89; 0xcb;        (* MOV (% rbx) (% rcx) *)
  0x4c; 0x29; 0xc0;        (* SUB (% rax) (% r8) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc1;        (* SUB (% r9) (% rax) *)
  0x49; 0x19; 0xca;        (* SBB (% r10) (% rcx) *)
  0x49; 0x19; 0xd3;        (* SBB (% r11) (% rdx) *)
  0x49; 0x19; 0xd8;        (* SBB (% r8) (% rbx) *)
  0x4c; 0x89; 0xc8;        (* MOV (% rax) (% r9) *)
  0x48; 0xc1; 0xe0; 0x20;  (* SHL (% rax) (Imm8 (word 32)) *)
  0x4c; 0x89; 0xc9;        (* MOV (% rcx) (% r9) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x89; 0xcb;        (* MOV (% rbx) (% rcx) *)
  0x4c; 0x29; 0xc8;        (* SUB (% rax) (% r9) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc2;        (* SUB (% r10) (% rax) *)
  0x49; 0x19; 0xcb;        (* SBB (% r11) (% rcx) *)
  0x49; 0x19; 0xd0;        (* SBB (% r8) (% rdx) *)
  0x49; 0x19; 0xd9;        (* SBB (% r9) (% rbx) *)
  0x4c; 0x89; 0xd0;        (* MOV (% rax) (% r10) *)
  0x48; 0xc1; 0xe0; 0x20;  (* SHL (% rax) (Imm8 (word 32)) *)
  0x4c; 0x89; 0xd1;        (* MOV (% rcx) (% r10) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x89; 0xcb;        (* MOV (% rbx) (% rcx) *)
  0x4c; 0x29; 0xd0;        (* SUB (% rax) (% r10) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc3;        (* SUB (% r11) (% rax) *)
  0x49; 0x19; 0xc8;        (* SBB (% r8) (% rcx) *)
  0x49; 0x19; 0xd1;        (* SBB (% r9) (% rdx) *)
  0x49; 0x19; 0xda;        (* SBB (% r10) (% rbx) *)
  0x4c; 0x89; 0xd8;        (* MOV (% rax) (% r11) *)
  0x48; 0xc1; 0xe0; 0x20;  (* SHL (% rax) (Imm8 (word 32)) *)
  0x4c; 0x89; 0xd9;        (* MOV (% rcx) (% r11) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x89; 0xcb;        (* MOV (% rbx) (% rcx) *)
  0x4c; 0x29; 0xd8;        (* SUB (% rax) (% r11) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc0;        (* SUB (% r8) (% rax) *)
  0x49; 0x19; 0xc9;        (* SBB (% r9) (% rcx) *)
  0x49; 0x19; 0xd2;        (* SBB (% r10) (% rdx) *)
  0x49; 0x19; 0xdb;        (* SBB (% r11) (% rbx) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0x4d; 0x01; 0xc4;        (* ADD (% r12) (% r8) *)
  0x4d; 0x11; 0xcd;        (* ADC (% r13) (% r9) *)
  0x4d; 0x11; 0xd6;        (* ADC (% r14) (% r10) *)
  0x4d; 0x11; 0xdf;        (* ADC (% r15) (% r11) *)
  0x48; 0x11; 0xc0;        (* ADC (% rax) (% rax) *)
  0xb9; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% ecx) (Imm32 (word 1)) *)
  0xba; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% edx) (Imm32 (word 4294967295)) *)
  0x31; 0xdb;              (* XOR (% ebx) (% ebx) *)
  0x4c; 0x01; 0xe1;        (* ADD (% rcx) (% r12) *)
  0x4c; 0x8d; 0x5a; 0x01;  (* LEA (% r11) (%% (rdx,1)) *)
  0x4c; 0x11; 0xea;        (* ADC (% rdx) (% r13) *)
  0x4c; 0x8d; 0x43; 0xff;  (* LEA (% r8) (%% (rbx,18446744073709551615)) *)
  0x4c; 0x11; 0xf3;        (* ADC (% rbx) (% r14) *)
  0x4d; 0x11; 0xfb;        (* ADC (% r11) (% r15) *)
  0x49; 0x11; 0xc0;        (* ADC (% r8) (% rax) *)
  0x4c; 0x0f; 0x42; 0xe1;  (* CMOVB (% r12) (% rcx) *)
  0x4c; 0x0f; 0x42; 0xea;  (* CMOVB (% r13) (% rdx) *)
  0x4c; 0x0f; 0x42; 0xf3;  (* CMOVB (% r14) (% rbx) *)
  0x4d; 0x0f; 0x42; 0xfb;  (* CMOVB (% r15) (% r11) *)
  0x4c; 0x89; 0x67; 0x40;  (* MOV (Memop Quadword (%% (rdi,64))) (% r12) *)
  0x4c; 0x89; 0x6f; 0x48;  (* MOV (Memop Quadword (%% (rdi,72))) (% r13) *)
  0x4c; 0x89; 0x77; 0x50;  (* MOV (Memop Quadword (%% (rdi,80))) (% r14) *)
  0x4c; 0x89; 0x7f; 0x58;  (* MOV (Memop Quadword (%% (rdi,88))) (% r15) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x94; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,128))) *)
  0xc4; 0x62; 0xbb; 0xf6; 0x4c; 0x24; 0x20;
                           (* MULX4 (% r9,% r8) (% rdx,Memop Quadword (%% (rsp,32))) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x54; 0x24; 0x28;
                           (* MULX4 (% r10,% rax) (% rdx,Memop Quadword (%% (rsp,40))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x5c; 0x24; 0x30;
                           (* MULX4 (% r11,% rax) (% rdx,Memop Quadword (%% (rsp,48))) *)
  0x49; 0x11; 0xc2;        (* ADC (% r10) (% rax) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x64; 0x24; 0x38;
                           (* MULX4 (% r12,% rax) (% rdx,Memop Quadword (%% (rsp,56))) *)
  0x49; 0x11; 0xc3;        (* ADC (% r11) (% rax) *)
  0x49; 0x11; 0xcc;        (* ADC (% r12) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x94; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,136))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x20;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,32))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x28;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x30;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,48))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x6c; 0x24; 0x38;
                           (* MULX4 (% r13,% rax) (% rdx,Memop Quadword (%% (rsp,56))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADOX (% r13) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADCX (% r13) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x94; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,144))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x20;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,32))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x28;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x30;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,48))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x74; 0x24; 0x38;
                           (* MULX4 (% r14,% rax) (% rdx,Memop Quadword (%% (rsp,56))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADOX (% r14) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADCX (% r14) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x94; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,152))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x20;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,32))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x28;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x30;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,48))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x7c; 0x24; 0x38;
                           (* MULX4 (% r15,% rax) (% rdx,Memop Quadword (%% (rsp,56))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADOX (% r15) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADCX (% r15) (% rcx) *)
  0x4c; 0x89; 0xc0;        (* MOV (% rax) (% r8) *)
  0x48; 0xc1; 0xe0; 0x20;  (* SHL (% rax) (Imm8 (word 32)) *)
  0x4c; 0x89; 0xc1;        (* MOV (% rcx) (% r8) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x89; 0xcb;        (* MOV (% rbx) (% rcx) *)
  0x4c; 0x29; 0xc0;        (* SUB (% rax) (% r8) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc1;        (* SUB (% r9) (% rax) *)
  0x49; 0x19; 0xca;        (* SBB (% r10) (% rcx) *)
  0x49; 0x19; 0xd3;        (* SBB (% r11) (% rdx) *)
  0x49; 0x19; 0xd8;        (* SBB (% r8) (% rbx) *)
  0x4c; 0x89; 0xc8;        (* MOV (% rax) (% r9) *)
  0x48; 0xc1; 0xe0; 0x20;  (* SHL (% rax) (Imm8 (word 32)) *)
  0x4c; 0x89; 0xc9;        (* MOV (% rcx) (% r9) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x89; 0xcb;        (* MOV (% rbx) (% rcx) *)
  0x4c; 0x29; 0xc8;        (* SUB (% rax) (% r9) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc2;        (* SUB (% r10) (% rax) *)
  0x49; 0x19; 0xcb;        (* SBB (% r11) (% rcx) *)
  0x49; 0x19; 0xd0;        (* SBB (% r8) (% rdx) *)
  0x49; 0x19; 0xd9;        (* SBB (% r9) (% rbx) *)
  0x4c; 0x89; 0xd0;        (* MOV (% rax) (% r10) *)
  0x48; 0xc1; 0xe0; 0x20;  (* SHL (% rax) (Imm8 (word 32)) *)
  0x4c; 0x89; 0xd1;        (* MOV (% rcx) (% r10) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x89; 0xcb;        (* MOV (% rbx) (% rcx) *)
  0x4c; 0x29; 0xd0;        (* SUB (% rax) (% r10) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc3;        (* SUB (% r11) (% rax) *)
  0x49; 0x19; 0xc8;        (* SBB (% r8) (% rcx) *)
  0x49; 0x19; 0xd1;        (* SBB (% r9) (% rdx) *)
  0x49; 0x19; 0xda;        (* SBB (% r10) (% rbx) *)
  0x4c; 0x89; 0xd8;        (* MOV (% rax) (% r11) *)
  0x48; 0xc1; 0xe0; 0x20;  (* SHL (% rax) (Imm8 (word 32)) *)
  0x4c; 0x89; 0xd9;        (* MOV (% rcx) (% r11) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x89; 0xcb;        (* MOV (% rbx) (% rcx) *)
  0x4c; 0x29; 0xd8;        (* SUB (% rax) (% r11) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc0;        (* SUB (% r8) (% rax) *)
  0x49; 0x19; 0xc9;        (* SBB (% r9) (% rcx) *)
  0x49; 0x19; 0xd2;        (* SBB (% r10) (% rdx) *)
  0x49; 0x19; 0xdb;        (* SBB (% r11) (% rbx) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0x4d; 0x01; 0xc4;        (* ADD (% r12) (% r8) *)
  0x4d; 0x11; 0xcd;        (* ADC (% r13) (% r9) *)
  0x4d; 0x11; 0xd6;        (* ADC (% r14) (% r10) *)
  0x4d; 0x11; 0xdf;        (* ADC (% r15) (% r11) *)
  0x48; 0x11; 0xc0;        (* ADC (% rax) (% rax) *)
  0xb9; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% ecx) (Imm32 (word 1)) *)
  0xba; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% edx) (Imm32 (word 4294967295)) *)
  0x31; 0xdb;              (* XOR (% ebx) (% ebx) *)
  0x4c; 0x01; 0xe1;        (* ADD (% rcx) (% r12) *)
  0x4c; 0x8d; 0x5a; 0x01;  (* LEA (% r11) (%% (rdx,1)) *)
  0x4c; 0x11; 0xea;        (* ADC (% rdx) (% r13) *)
  0x4c; 0x8d; 0x43; 0xff;  (* LEA (% r8) (%% (rbx,18446744073709551615)) *)
  0x4c; 0x11; 0xf3;        (* ADC (% rbx) (% r14) *)
  0x4d; 0x11; 0xfb;        (* ADC (% r11) (% r15) *)
  0x49; 0x11; 0xc0;        (* ADC (% r8) (% rax) *)
  0x4c; 0x0f; 0x42; 0xe1;  (* CMOVB (% r12) (% rcx) *)
  0x4c; 0x0f; 0x42; 0xea;  (* CMOVB (% r13) (% rdx) *)
  0x4c; 0x0f; 0x42; 0xf3;  (* CMOVB (% r14) (% rbx) *)
  0x4d; 0x0f; 0x42; 0xfb;  (* CMOVB (% r15) (% r11) *)
  0x4c; 0x89; 0xa4; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,128))) (% r12) *)
  0x4c; 0x89; 0xac; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,136))) (% r13) *)
  0x4c; 0x89; 0xb4; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,144))) (% r14) *)
  0x4c; 0x89; 0xbc; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,152))) (% r15) *)
  0x48; 0x8b; 0x84; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,128))) *)
  0x48; 0x2b; 0x44; 0x24; 0x60;
                           (* SUB (% rax) (Memop Quadword (%% (rsp,96))) *)
  0x48; 0x8b; 0x8c; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (% rcx) (Memop Quadword (%% (rsp,136))) *)
  0x48; 0x1b; 0x4c; 0x24; 0x68;
                           (* SBB (% rcx) (Memop Quadword (%% (rsp,104))) *)
  0x4c; 0x8b; 0x84; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,144))) *)
  0x4c; 0x1b; 0x44; 0x24; 0x70;
                           (* SBB (% r8) (Memop Quadword (%% (rsp,112))) *)
  0x4c; 0x8b; 0x8c; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,152))) *)
  0x4c; 0x1b; 0x4c; 0x24; 0x78;
                           (* SBB (% r9) (Memop Quadword (%% (rsp,120))) *)
  0x49; 0xba; 0x00; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r10) (Imm64 (word 18446744069414584320)) *)
  0x4d; 0x19; 0xdb;        (* SBB (% r11) (% r11) *)
  0x4d; 0x21; 0xda;        (* AND (% r10) (% r11) *)
  0x4c; 0x89; 0xda;        (* MOV (% rdx) (% r11) *)
  0x48; 0x0f; 0xba; 0xf2; 0x20;
                           (* BTR (% rdx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xd8;        (* ADD (% rax) (% r11) *)
  0x48; 0x89; 0x47; 0x20;  (* MOV (Memop Quadword (%% (rdi,32))) (% rax) *)
  0x4c; 0x11; 0xd1;        (* ADC (% rcx) (% r10) *)
  0x48; 0x89; 0x4f; 0x28;  (* MOV (Memop Quadword (%% (rdi,40))) (% rcx) *)
  0x4d; 0x11; 0xd8;        (* ADC (% r8) (% r11) *)
  0x4c; 0x89; 0x47; 0x30;  (* MOV (Memop Quadword (%% (rdi,48))) (% r8) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x4c; 0x89; 0x4f; 0x38;  (* MOV (Memop Quadword (%% (rdi,56))) (% r9) *)
  0x48; 0x81; 0xc4; 0xe0; 0x00; 0x00; 0x00;
                           (* ADD (% rsp) (Imm32 (word 224)) *)
  0x41; 0x5f;              (* POP (% r15) *)
  0x41; 0x5e;              (* POP (% r14) *)
  0x41; 0x5d;              (* POP (% r13) *)
  0x41; 0x5c;              (* POP (% r12) *)
  0x5d;                    (* POP (% rbp) *)
  0x5b;                    (* POP (% rbx) *)
  0xc3                     (* RET *)
];;

let SM2_MONTJADD_EXEC = X86_MK_CORE_EXEC_RULE sm2_montjadd_mc;;

(* ------------------------------------------------------------------------- *)
(* Common supporting definitions and lemmas for component proofs.            *)
(* ------------------------------------------------------------------------- *)

let p_sm2 = new_definition `p_sm2 = 0xFFFFFFFEFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000FFFFFFFFFFFFFFFF`;;

let ccsm2 = define
 `ccsm2 =
    (integer_mod_ring p_sm2,
     ring_neg (integer_mod_ring p_sm2) (&3),
     &b_sm2:int)`;;

let ccsm2_encode = new_definition
  `ccsm2_encode = montgomery_encode(256,p_sm2)`;;

let nintlemma = prove
 (`&(num_of_int(x rem &p_sm2)) = x rem &p_sm2`,
  MATCH_MP_TAC INT_OF_NUM_OF_INT THEN MATCH_MP_TAC INT_REM_POS THEN
  REWRITE_TAC[INT_OF_NUM_EQ; p_sm2] THEN CONV_TAC NUM_REDUCE_CONV);;

let unilemma0 = prove
 (`x = a MOD p_sm2 ==> x < p_sm2 /\ &x = &a rem &p_sm2`,
  REWRITE_TAC[INT_OF_NUM_REM; p_sm2] THEN ARITH_TAC);;

let unilemma1 = prove
 (`&x = a rem &p_sm2 ==> x < p_sm2 /\ &x = a rem &p_sm2`,
  SIMP_TAC[GSYM INT_OF_NUM_LT; INT_LT_REM_EQ; p_sm2] THEN INT_ARITH_TAC);;

let unilemma2 = prove
 (`X = num_of_int(x rem &p_sm2) ==> X < p_sm2 /\ &X = x rem &p_sm2`,
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM INT_OF_NUM_LT; nintlemma; INT_LT_REM_EQ] THEN
  REWRITE_TAC[INT_OF_NUM_LT; p_sm2] THEN CONV_TAC NUM_REDUCE_CONV);;

let lemont = prove
 (`(&i * x * y) rem &p_sm2 = (&i * x rem &p_sm2 * y rem &p_sm2) rem &p_sm2`,
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[]);;

let pumont = prove
 (`(&(inverse_mod p_sm2 (2 EXP 256)) *
    (&2 pow 256 * x) rem &p_sm2 * (&2 pow 256 * y) rem &p_sm2) rem &p_sm2 =
   (&2 pow 256 * x * y) rem &p_sm2`,
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[INT_REM_EQ] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `(i * t:int == &1) (mod p)
    ==> (i * (t * x) * (t * y) == t * x * y) (mod p)`) THEN
  REWRITE_TAC[GSYM num_congruent; INT_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[INVERSE_MOD_LMUL_EQ; COPRIME_REXP; COPRIME_2; p_sm2] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let lvs =
 ["x_1",[`RSI`;`0`];
  "y_1",[`RSI`;`32`];
  "z_1",[`RSI`;`64`];
  "x_2",[`RBP`;`0`];
  "y_2",[`RBP`;`32`];
  "z_2",[`RBP`;`64`];
  "x_3",[`RDI`;`0`];
  "y_3",[`RDI`;`32`];
  "z_3",[`RDI`;`64`];
  "z1sq",[`RSP`;`0`];
  "ww",[`RSP`;`0`];
  "yd",[`RSP`;`32`];
  "y2a",[`RSP`;`32`];
  "x2a",[`RSP`;`64`];
  "zzx2",[`RSP`;`64`];
  "zz",[`RSP`;`96`];
  "t1",[`RSP`;`96`];
  "t2",[`RSP`;`128`];
  "x1a",[`RSP`;`128`];
  "zzx1",[`RSP`;`128`];
  "xd",[`RSP`;`160`];
  "z2sq",[`RSP`;`160`];
  "y1a",[`RSP`;`192`]];;

(* ------------------------------------------------------------------------- *)
(* Instances of montsqr.                                                     *)
(* ------------------------------------------------------------------------- *)

let LOCAL_MONTSQR_SM2_TAC =
  X86_MACRO_SIM_ABBREV_TAC (X86_TRIM_EXEC_RULE sm2_montjadd_mc) 113 lvs
  `!(t:x86state) pcin pcout p3 n3 p1 n1.
    !a. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = a
    ==>
    nonoverlapping (word pc,0x256e) (word_add (read p3 t) (word n3),32)
    ==> ensures x86
         (\s. bytes_loaded s (word pc) (BUTLAST sm2_montjadd_mc) /\
              read RIP s = pcin /\
              read RSP s = read RSP t /\
              read RDI s = read RDI t /\
              read RSI s = read RSI t /\
              read RBP s = read RBP t /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s =
              a)
             (\s. read RIP s = pcout /\
                  (a EXP 2 <= 2 EXP 256 * p_sm2
                   ==> read(memory :> bytes(word_add (read p3 t) (word n3),
                        8 * 4)) s =
                       (inverse_mod p_sm2 (2 EXP 256) * a EXP 2) MOD p_sm2))
           (MAYCHANGE [RIP; RAX; RBX; RCX; RDX;
                       R8; R9; R10; R11; R12; R13; R14; R15] ,,
            MAYCHANGE
             [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
            MAYCHANGE SOME_FLAGS)`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the a EXP 2 <= 2 EXP 256 * p_sm2  assumption ***)

  ASM_CASES_TAC `a EXP 2 <= 2 EXP 256 * p_sm2` THENL
   [ASM_REWRITE_TAC[]; X86_SIM_TAC SM2_MONTJADD_EXEC (1--113)] THEN
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "x_" o lhand o concl) THEN

  X86_ACCSTEPS_TAC SM2_MONTJADD_EXEC (1--94) (1--95) THEN
  ABBREV_TAC
   `t = bignum_of_wordlist
         [sum_s91; sum_s92; sum_s93; sum_s94; word(bitval carry_s94)]` THEN
  SUBGOAL_THEN
   `t < 2 * p_sm2 /\ (2 EXP 256 * t == a EXP 2) (mod p_sm2)`
  STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_BITVAL]) THEN
    ACCUMULATOR_POP_ASSUM_LIST
     (STRIP_ASSUME_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ARITH_RULE
        `ab <= 2 EXP 256 * p
         ==> 2 EXP 256 * t < ab + 2 EXP 256 * p ==> t < 2 * p`)) THEN
      MAP_EVERY EXPAND_TAC ["a"; "t"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      REWRITE_TAC[p_sm2; REAL_ARITH `a:real < b + c <=> a - b < c`] THEN
      ASM_REWRITE_TAC[VAL_WORD_BITVAL] THEN BOUNDER_TAC[];
      REWRITE_TAC[REAL_CONGRUENCE; p_sm2] THEN CONV_TAC NUM_REDUCE_CONV THEN
      MAP_EVERY EXPAND_TAC ["a"; "t"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      ASM_REWRITE_TAC[VAL_WORD_BITVAL] THEN REAL_INTEGER_TAC];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Final correction stage ***)

  X86_ACCSTEPS_TAC SM2_MONTJADD_EXEC [99;101;103;104;105] (96--113) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  TRANS_TAC EQ_TRANS `t MOD p_sm2` THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[GSYM CONG] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (NUMBER_RULE
       `(e * t == a EXP 2) (mod p)
        ==> (e * i == 1) (mod p) ==> (t == i * a EXP 2) (mod p)`)) THEN
    REWRITE_TAC[INVERSE_MOD_RMUL_EQ; COPRIME_REXP; COPRIME_2] THEN
    REWRITE_TAC[p_sm2] THEN CONV_TAC NUM_REDUCE_CONV] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  MAP_EVERY EXISTS_TAC
   [`256`; `if t < p_sm2 then &t:real else &t - &p_sm2`] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN BOUNDER_TAC[];
    REWRITE_TAC[p_sm2] THEN ARITH_TAC;
    REWRITE_TAC[p_sm2] THEN ARITH_TAC;
    ALL_TAC;
    ASM_SIMP_TAC[MOD_CASES] THEN
    GEN_REWRITE_TAC LAND_CONV [COND_RAND] THEN
    SIMP_TAC[REAL_OF_NUM_SUB; GSYM NOT_LT]] THEN
  SUBGOAL_THEN `carry_s105 <=> p_sm2 <= t` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `320` THEN
    EXPAND_TAC "t" THEN
    REWRITE_TAC[p_sm2; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[VAL_WORD_BITVAL] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    REWRITE_TAC[GSYM NOT_LT; COND_SWAP]] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "t" THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_sm2] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES; VAL_WORD_BITVAL] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instances of montmul.                                                     *)
(* ------------------------------------------------------------------------- *)

let LOCAL_MONTMUL_SM2_TAC =
  X86_MACRO_SIM_ABBREV_TAC (X86_TRIM_EXEC_RULE sm2_montjadd_mc) 127 lvs
  `!(t:x86state) pcin pcout p3 n3 p1 n1 p2 n2.
    !a. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = a
    ==>
    !b. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) t = b
    ==>
    nonoverlapping (word pc,0x256e) (word_add (read p3 t) (word n3),32)
    ==> ensures x86
         (\s. bytes_loaded s (word pc) (BUTLAST sm2_montjadd_mc) /\
              read RIP s = pcin /\
              read RSP s = read RSP t /\
              read RDI s = read RDI t /\
              read RSI s = read RSI t /\
              read RBP s = read RBP t /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s =
              a /\
              read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) s =
              b)
             (\s. read RIP s = pcout /\
                  (a * b <= 2 EXP 256 * p_sm2
                   ==> read(memory :> bytes(word_add (read p3 t) (word n3),
                            8 * 4)) s =
                       (inverse_mod p_sm2 (2 EXP 256) * a * b) MOD p_sm2))
             (MAYCHANGE [RIP; RAX; RBX; RCX; RDX;
                         R8; R9; R10; R11; R12; R13; R14; R15] ,,
             MAYCHANGE
               [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
             MAYCHANGE SOME_FLAGS)`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the a * b <= 2 EXP 256 * p_sm2  assumption ***)

  ASM_CASES_TAC `a * b <= 2 EXP 256 * p_sm2` THENL
   [ASM_REWRITE_TAC[]; X86_SIM_TAC SM2_MONTJADD_EXEC (1--127)] THEN
  ENSURES_INIT_TAC "s1" THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "y_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "x_" o lhand o concl) THEN

  (*** Simulate the core pre-reduced result accumulation ***)

  X86_ACCSTEPS_TAC SM2_MONTJADD_EXEC (2--109) (2--110) THEN
  ABBREV_TAC
   `t = bignum_of_wordlist
         [sum_s106; sum_s107; sum_s108; sum_s109; word(bitval carry_s109)]` THEN
  SUBGOAL_THEN
   `t < 2 * p_sm2 /\ (2 EXP 256 * t == a * b) (mod p_sm2)`
  STRIP_ASSUME_TAC THENL
   [ACCUMULATOR_POP_ASSUM_LIST
     (STRIP_ASSUME_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ARITH_RULE
        `ab <= 2 EXP 256 * p
         ==> 2 EXP 256 * t < ab + 2 EXP 256 * p ==> t < 2 * p`)) THEN
      MAP_EVERY EXPAND_TAC ["a"; "b"; "t"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      REWRITE_TAC[p_sm2; REAL_ARITH `a:real < b + c <=> a - b < c`] THEN
      ASM_REWRITE_TAC[VAL_WORD_BITVAL] THEN BOUNDER_TAC[];
      REWRITE_TAC[REAL_CONGRUENCE; p_sm2] THEN CONV_TAC NUM_REDUCE_CONV THEN
      MAP_EVERY EXPAND_TAC ["a"; "b"; "t"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      ASM_REWRITE_TAC[VAL_WORD_BITVAL] THEN REAL_INTEGER_TAC];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Final correction stage ***)

  X86_ACCSTEPS_TAC SM2_MONTJADD_EXEC [114;116;118;119;120] (111--128) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  TRANS_TAC EQ_TRANS `t MOD p_sm2` THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[GSYM CONG] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (NUMBER_RULE
       `(e * t == a * b) (mod p)
        ==> (e * i == 1) (mod p) ==> (t == i * a * b) (mod p)`)) THEN
    REWRITE_TAC[INVERSE_MOD_RMUL_EQ; COPRIME_REXP; COPRIME_2] THEN
    REWRITE_TAC[p_sm2] THEN CONV_TAC NUM_REDUCE_CONV] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  MAP_EVERY EXISTS_TAC
   [`256`; `if t < p_sm2 then &t:real else &t - &p_sm2`] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN BOUNDER_TAC[];
    REWRITE_TAC[p_sm2] THEN ARITH_TAC;
    REWRITE_TAC[p_sm2] THEN ARITH_TAC;
    ALL_TAC;
    ASM_SIMP_TAC[MOD_CASES] THEN
    GEN_REWRITE_TAC LAND_CONV [COND_RAND] THEN
    SIMP_TAC[REAL_OF_NUM_SUB; GSYM NOT_LT]] THEN
  SUBGOAL_THEN `carry_s120 <=> p_sm2 <= t` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `320` THEN
    EXPAND_TAC "t" THEN
    REWRITE_TAC[p_sm2; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[VAL_WORD_BITVAL] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    REWRITE_TAC[GSYM NOT_LT; COND_SWAP]] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "t" THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_sm2] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES; VAL_WORD_BITVAL] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instances of sub.                                                         *)
(* ------------------------------------------------------------------------- *)

let LOCAL_SUB_SM2_TAC =
  X86_MACRO_SIM_ABBREV_TAC (X86_TRIM_EXEC_RULE sm2_montjadd_mc) 21 lvs
  `!(t:x86state) pcin pcout p3 n3 p1 n1 p2 n2.
    !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = m
    ==>
    !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) t = n
    ==>
    nonoverlapping (word pc,0x256e) (word_add (read p3 t) (word n3),32)
    ==> ensures x86
         (\s. bytes_loaded s (word pc) (BUTLAST sm2_montjadd_mc) /\
              read RIP s = pcin /\
              read RSP s = read RSP t /\
              read RDI s = read RDI t /\
              read RSI s = read RSI t /\
              read RBP s = read RBP t /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s =
              m /\
              read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) s =
              n)
             (\s. read RIP s = pcout /\
                  (m < p_sm2 /\ n < p_sm2
                   ==> &(read(memory :> bytes(word_add (read p3 t) (word n3),
                            8 * 4)) s) = (&m - &n) rem &p_sm2))
          (MAYCHANGE [RIP; RAX; RDX; RCX; R8; R9; R10; R11] ,,
           MAYCHANGE
               [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
           MAYCHANGE SOME_FLAGS)`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "m_" o lhand o concl) THEN

  X86_ACCSTEPS_TAC SM2_MONTJADD_EXEC (1--8) (1--8) THEN

  SUBGOAL_THEN `carry_s8 <=> m < n` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `256` THEN
    MAP_EVERY EXPAND_TAC ["m"; "n"] THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN

  X86_ACCSTEPS_TAC SM2_MONTJADD_EXEC (14--21) (9--21) THEN

  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  CONV_TAC(LAND_CONV(RAND_CONV BIGNUM_EXPAND_CONV)) THEN
  ASM_REWRITE_TAC[] THEN DISCARD_STATE_TAC "s21" THEN

  CONV_TAC SYM_CONV THEN MATCH_MP_TAC INT_REM_UNIQ THEN
  EXISTS_TAC `--(&(bitval(m < n))):int` THEN REWRITE_TAC[INT_ABS_NUM] THEN
  REWRITE_TAC[INT_ARITH `m - n:int = --b * p + z <=> z = b * p + m - n`] THEN
  REWRITE_TAC[int_eq; int_le; int_lt] THEN
  REWRITE_TAC[int_add_th; int_mul_th; int_of_num_th; int_sub_th] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL;
              GSYM REAL_OF_NUM_POW] THEN
  MATCH_MP_TAC(REAL_ARITH
  `!t:real. p < t /\
            (&0 <= a /\ a < p) /\
            (&0 <= z /\ z < t) /\
            ((&0 <= z /\ z < t) /\ (&0 <= a /\ a < t) ==> z = a)
            ==> z = a /\ &0 <= z /\ z < p`) THEN
  EXISTS_TAC `(&2:real) pow 256` THEN

  CONJ_TAC THENL [REWRITE_TAC[p_sm2] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`m < p_sm2`; `n < p_sm2`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN
    ASM_CASES_TAC `&m:real < &n` THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC[p_sm2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; STRIP_TAC] THEN

  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`256`; `&0:real`] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [REAL_INTEGER_TAC; ALL_TAC] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  REWRITE_TAC[WORD_AND_MASK] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  MAP_EVERY EXPAND_TAC ["m"; "n"] THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW; p_sm2] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instances of amontsqr.                                                    *)
(* ------------------------------------------------------------------------- *)

let LOCAL_AMONTSQR_SM2_TAC =
  X86_MACRO_SIM_ABBREV_TAC (X86_TRIM_EXEC_RULE sm2_montjadd_mc) 106 lvs
  `!(t:x86state) pcin pcout p3 n3 p1 n1.
    !a. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = a
    ==>
    nonoverlapping (word pc,0x256e) (word_add (read p3 t) (word n3),32)
    ==> ensures x86
         (\s. bytes_loaded s (word pc) (BUTLAST sm2_montjadd_mc) /\
              read RIP s = pcin /\
              read RSP s = read RSP t /\
              read RDI s = read RDI t /\
              read RSI s = read RSI t /\
              read RBP s = read RBP t /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s =
              a)
         (\s. read RIP s = pcout /\
              read(memory :> bytes(word_add (read p3 t) (word n3),8 * 4)) s
              < 2 EXP 256 /\
              (read(memory :> bytes(word_add (read p3 t) (word n3),8 * 4)) s ==
               inverse_mod p_sm2 (2 EXP 256) * a EXP 2) (mod p_sm2))
          (MAYCHANGE [RIP; RAX; RBX; RCX; RDX;
                      R8; R9; R10; R11; R12; R13; R14; R15] ,,
           MAYCHANGE
            [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
           MAYCHANGE SOME_FLAGS)`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "x_" o lhand o concl) THEN

  X86_ACCSTEPS_TAC SM2_MONTJADD_EXEC (1--93) (1--94) THEN
  ABBREV_TAC
   `t = bignum_of_wordlist
         [sum_s90; sum_s91; sum_s92; sum_s93; word(bitval carry_s93)]` THEN
  SUBGOAL_THEN
   `t < 2 EXP 256 + p_sm2 /\ (2 EXP 256 * t == a EXP 2) (mod p_sm2)`
  STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_BITVAL]) THEN
    ACCUMULATOR_POP_ASSUM_LIST
     (STRIP_ASSUME_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE
       `2 EXP 256 * t <= (2 EXP 256 - 1) EXP 2 + (2 EXP 256 - 1) * p
        ==> t < 2 EXP 256 + p`) THEN
      REWRITE_TAC[p_sm2] THEN CONV_TAC NUM_REDUCE_CONV THEN
      MAP_EVERY EXPAND_TAC ["a"; "t"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      REWRITE_TAC[p_sm2; REAL_ARITH `a:real < b + c <=> a - b < c`] THEN
      ASM_REWRITE_TAC[VAL_WORD_BITVAL] THEN BOUNDER_TAC[];
      REWRITE_TAC[REAL_CONGRUENCE; p_sm2] THEN CONV_TAC NUM_REDUCE_CONV THEN
      MAP_EVERY EXPAND_TAC ["a"; "t"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      ASM_REWRITE_TAC[VAL_WORD_BITVAL] THEN REAL_INTEGER_TAC];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Final correction stage ***)

  X86_ACCSTEPS_TAC SM2_MONTJADD_EXEC [99;100;101;102] (95--106) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV BIGNUM_EXPAND_CONV) THEN
    ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (NUMBER_RULE
       `(e * t == ab) (mod p)
        ==> (e * i == 1) (mod p) /\ (s == t) (mod p)
            ==> (s == i * ab) (mod p)`)) THEN
  REWRITE_TAC[INVERSE_MOD_RMUL_EQ; COPRIME_REXP; COPRIME_2] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[p_sm2] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN

  SUBGOAL_THEN `carry_s93 <=> 2 EXP 256 <= t` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `256` THEN
    EXPAND_TAC "t" THEN
    REWRITE_TAC[p_sm2; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[VAL_WORD_BITVAL] THEN
    REWRITE_TAC[VAL_WORD_BITVAL] THEN BOUNDER_TAC[];
    ABBREV_TAC `b <=> 2 EXP 256 <= t`] THEN
  MATCH_MP_TAC(NUMBER_RULE `!b:num. x + b * p = y ==> (x == y) (mod p)`) THEN
  EXISTS_TAC `bitval b` THEN REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a + b:real = c <=> c - b = a`] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`256`; `&0:real`] THEN CONJ_TAC THENL
   [EXPAND_TAC "b" THEN UNDISCH_TAC `t < 2 EXP 256 + p_sm2` THEN
    REWRITE_TAC[bitval; p_sm2; GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC;
    REWRITE_TAC[INTEGER_CLOSED]] THEN
  CONJ_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV BIGNUM_EXPAND_CONV) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_EXPAND_CONV) THEN
  EXPAND_TAC "t" THEN REWRITE_TAC[bignum_of_wordlist] THEN
  ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  ACCUMULATOR_POP_ASSUM_LIST (MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[BITVAL_CLAUSES; p_sm2] THEN
  CONV_TAC WORD_REDUCE_CONV THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Overall point operation proof.                                            *)
(* ------------------------------------------------------------------------- *)

let SM2_MONTJADD_CORRECT = time prove
 (`!p3 p1 t1 p2 t2 pc stackpointer.
        ALLPAIRS nonoverlapping
         [(p3,96); (stackpointer,224)]
         [(word pc,0x256e); (p1,96); (p2,96)] /\
        nonoverlapping (p3,96) (stackpointer,224)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST sm2_montjadd_mc) /\
                  read RIP s = word(pc + 0x11) /\
                  read RSP s = stackpointer /\
                  C_ARGUMENTS [p3; p1; p2] s /\
                  bignum_triple_from_memory (p1,4) s = t1 /\
                  bignum_triple_from_memory (p2,4) s = t2)
             (\s. read RIP s = word (pc + 0x255c) /\
                  (!x1 y1 z1 x2 y2 z2.
                        ~(z1 = &0) /\ ~(z2 = &0) /\
                        ~(jacobian_eq (integer_mod_ring p_sm2)
                                      (x1,y1,z1) (x2,y2,z2)) /\
                        ~(jacobian_eq (integer_mod_ring p_sm2)
                                      (jacobian_neg ccsm2 (x1,y1,z1))
                                      (x2,y2,z2)) /\
                        t1 = tripled ccsm2_encode (x1,y1,z1) /\
                        t2 = tripled ccsm2_encode (x2,y2,z2)
                        ==> bignum_triple_from_memory(p3,4) s =
                            tripled ccsm2_encode
                             (jacobian_add ccsm2 (x1,y1,z1) (x2,y2,z2))))
          (MAYCHANGE [RIP; RAX; RBX; RCX; RDX; RBP;
                      R8; R9; R10; R11; R12; R13; R14; R15] ,,
           MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [memory :> bytes(p3,96);
                      memory :> bytes(stackpointer,224)])`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`p3:int64`; `p1:int64`; `x1:num`; `y1:num`; `z1:num`; `p2:int64`;
    `x2:num`; `y2:num`; `z2:num`; `pc:num`; `stackpointer:int64`] THEN
  REWRITE_TAC[ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS; PAIR_EQ; bignum_triple_from_memory] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN

  LOCAL_AMONTSQR_SM2_TAC 1 ["z1sq";"z_1"] THEN
  LOCAL_AMONTSQR_SM2_TAC 0 ["z2sq";"z_2"] THEN
  LOCAL_MONTMUL_SM2_TAC 0 ["y1a";"z_2";"y_1"] THEN
  LOCAL_MONTMUL_SM2_TAC 0 ["y2a";"z_1";"y_2"] THEN
  LOCAL_MONTMUL_SM2_TAC 0 ["x2a";"z1sq";"x_2"] THEN
  LOCAL_MONTMUL_SM2_TAC 0 ["x1a";"z2sq";"x_1"] THEN
  LOCAL_MONTMUL_SM2_TAC 0 ["y2a";"z1sq";"y2a"] THEN
  LOCAL_MONTMUL_SM2_TAC 0 ["y1a";"z2sq";"y1a"] THEN
  LOCAL_SUB_SM2_TAC 0 ["xd";"x2a";"x1a"] THEN
  LOCAL_SUB_SM2_TAC 0 ["yd";"y2a";"y1a"] THEN
  LOCAL_AMONTSQR_SM2_TAC 0 ["zz";"xd"] THEN
  LOCAL_MONTSQR_SM2_TAC 0 ["ww";"yd"] THEN
  LOCAL_MONTMUL_SM2_TAC 0 ["zzx1";"zz";"x1a"] THEN
  LOCAL_MONTMUL_SM2_TAC 0 ["zzx2";"zz";"x2a"] THEN
  LOCAL_SUB_SM2_TAC 0 ["x_3";"ww";"zzx1"] THEN
  LOCAL_SUB_SM2_TAC 0 ["t1";"zzx2";"zzx1"] THEN
  LOCAL_MONTMUL_SM2_TAC 0 ["xd";"xd";"z_1"] THEN
  LOCAL_SUB_SM2_TAC 0 ["x_3";"x_3";"zzx2"] THEN
  LOCAL_SUB_SM2_TAC 0 ["t2";"zzx1";"x_3"] THEN
  LOCAL_MONTMUL_SM2_TAC 0 ["t1";"t1";"y1a"] THEN
  LOCAL_MONTMUL_SM2_TAC 0 ["z_3";"xd";"z_2"] THEN
  LOCAL_MONTMUL_SM2_TAC 0 ["t2";"yd";"t2"] THEN
  LOCAL_SUB_SM2_TAC 0 ["y_3";"t2";"t1"] THEN

  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCARD_STATE_TAC "s26" THEN
  DISCARD_MATCHING_ASSUMPTIONS [`nonoverlapping_modulo a b c`] THEN

  MAP_EVERY X_GEN_TAC
   [`x1':int`; `y1':int`; `z1':int`; `x2':int`; `y2':int`; `z2':int`] THEN
  REPLICATE_TAC 4 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[tripled; ccsm2_encode; montgomery_encode; PAIR_EQ] THEN

  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN
   (STRIP_ASSUME_TAC o MATCH_MP unilemma2)) THEN

  REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_imp o concl))) THEN
  REPEAT(ANTS_TAC THENL
   [REWRITE_TAC[p_sm2] THEN RULE_ASSUM_TAC(REWRITE_RULE[p_sm2]) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM BOUNDER_TAC[];
    (DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP unilemma0) ORELSE
     DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP unilemma1))]) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o GEN_REWRITE_RULE I [GSYM NOT_LE])) THEN

  RULE_ASSUM_TAC(REWRITE_RULE
   [num_congruent; GSYM INT_OF_NUM_CLAUSES; GSYM INT_OF_NUM_REM]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM INT_REM_EQ]) THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE[GSYM INT_SUB_REM; GSYM INT_ADD_REM]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INT_POW_2]) THEN
  RULE_ASSUM_TAC(GEN_REWRITE_RULE (RAND_CONV o TRY_CONV) [lemont]) THEN

  ASM_REWRITE_TAC[jacobian_add; ccsm2] THEN
  ASM_REWRITE_TAC[GSYM ccsm2] THEN
  REWRITE_TAC[INTEGER_MOD_RING_CLAUSES] THEN
  CONV_TAC INT_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC INT_REM_DOWN_CONV THEN
  REWRITE_TAC[tripled; ccsm2_encode; montgomery_encode] THEN
  REWRITE_TAC[PAIR_EQ; GSYM INT_OF_NUM_EQ; nintlemma] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN

  ASM_REWRITE_TAC[pumont; INT_REM_REM; GSYM INT_ADD_LDISTRIB;
                GSYM INT_ADD_LDISTRIB; GSYM INT_SUB_LDISTRIB;
                INT_SUB_REM; INT_ADD_REM] THEN

  REPEAT CONJ_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  INT_ARITH_TAC);;

let SM2_MONTJADD_SUBROUTINE_CORRECT = time prove
 (`!p3 p1 t1 p2 t2 pc stackpointer returnaddress.
        ALLPAIRS nonoverlapping
         [(p3,96); (word_sub stackpointer (word 272),272)]
         [(word pc,0x256e); (p1,96); (p2,96)] /\
        nonoverlapping (p3,96) (word_sub stackpointer (word 272),280)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) sm2_montjadd_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [p3; p1; p2] s /\
                  bignum_triple_from_memory (p1,4) s = t1 /\
                  bignum_triple_from_memory (p2,4) s = t2)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!x1 y1 z1 x2 y2 z2.
                        ~(z1 = &0) /\ ~(z2 = &0) /\
                        ~(jacobian_eq (integer_mod_ring p_sm2)
                                      (x1,y1,z1) (x2,y2,z2)) /\
                        ~(jacobian_eq (integer_mod_ring p_sm2)
                                      (jacobian_neg ccsm2 (x1,y1,z1))
                                      (x2,y2,z2)) /\
                        t1 = tripled ccsm2_encode (x1,y1,z1) /\
                        t2 = tripled ccsm2_encode (x2,y2,z2)
                        ==> bignum_triple_from_memory(p3,4) s =
                            tripled ccsm2_encode
                             (jacobian_add ccsm2 (x1,y1,z1) (x2,y2,z2))))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(p3,96);
                      memory :> bytes(word_sub stackpointer (word 272),272)])`,
  X86_PROMOTE_RETURN_STACK_TAC sm2_montjadd_mc SM2_MONTJADD_CORRECT
    `[RBX; RBP; R12; R13; R14; R15]` 272);;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let windows_sm2_montjadd_mc = define_from_elf "windows_sm2_montjadd_mc"
      "x86/sm2/sm2_montjadd.obj";;

let WINDOWS_SM2_MONTJADD_SUBROUTINE_CORRECT = time prove
 (`!p3 p1 t1 p2 t2 pc stackpointer returnaddress.
        ALLPAIRS nonoverlapping
         [(p3,96); (word_sub stackpointer (word 288),288)]
         [(word pc,0x257b); (p1,96); (p2,96)] /\
        nonoverlapping (p3,96) (word_sub stackpointer (word 288),296)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) windows_sm2_montjadd_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [p3; p1; p2] s /\
                  bignum_triple_from_memory (p1,4) s = t1 /\
                  bignum_triple_from_memory (p2,4) s = t2)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!x1 y1 z1 x2 y2 z2.
                        ~(z1 = &0) /\ ~(z2 = &0) /\
                        ~(jacobian_eq (integer_mod_ring p_sm2)
                                      (x1,y1,z1) (x2,y2,z2)) /\
                        ~(jacobian_eq (integer_mod_ring p_sm2)
                                      (jacobian_neg ccsm2 (x1,y1,z1))
                                      (x2,y2,z2)) /\
                        t1 = tripled ccsm2_encode (x1,y1,z1) /\
                        t2 = tripled ccsm2_encode (x2,y2,z2)
                        ==> bignum_triple_from_memory(p3,4) s =
                            tripled ccsm2_encode
                             (jacobian_add ccsm2 (x1,y1,z1) (x2,y2,z2))))
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(p3,96);
                      memory :> bytes(word_sub stackpointer (word 288),288)])`,
  WINDOWS_X86_WRAP_STACK_TAC
   windows_sm2_montjadd_mc sm2_montjadd_mc
   SM2_MONTJADD_CORRECT
    `[RBX; RBP; R12; R13; R14; R15]` 272);;
