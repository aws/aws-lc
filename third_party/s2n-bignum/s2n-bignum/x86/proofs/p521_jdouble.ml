(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Point doubling in Jacobian coordinates for NIST p521 curve.               *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "common/ecencoding.ml";;
needs "EC/jacobian.ml";;
needs "EC/nistp521.ml";;

prioritize_int();;
prioritize_real();;
prioritize_num();;

(**** print_literal_from_elf "x86/p521/p521_jdouble.o";;
 ****)

let p521_jdouble_mc = define_assert_from_elf
  "p521_jdouble_mc" "x86/p521/p521_jdouble.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x53;                    (* PUSH (% rbx) *)
  0x41; 0x54;              (* PUSH (% r12) *)
  0x41; 0x55;              (* PUSH (% r13) *)
  0x41; 0x56;              (* PUSH (% r14) *)
  0x41; 0x57;              (* PUSH (% r15) *)
  0x48; 0x81; 0xec; 0x38; 0x02; 0x00; 0x00;
                           (* SUB (% rsp) (Imm32 (word 568)) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x96; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsi,144))) *)
  0xc4; 0xe2; 0xb3; 0xf6; 0x86; 0x98; 0x00; 0x00; 0x00;
                           (* MULX4 (% rax,% r9) (% rdx,Memop Quadword (%% (rsi,152))) *)
  0x4c; 0x89; 0x8c; 0x24; 0x00; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,512))) (% r9) *)
  0xc4; 0xe2; 0xab; 0xf6; 0x9e; 0xa0; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% r10) (% rdx,Memop Quadword (%% (rsi,160))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0x4c; 0x89; 0x94; 0x24; 0x08; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,520))) (% r10) *)
  0xc4; 0xe2; 0xa3; 0xf6; 0x86; 0xa8; 0x00; 0x00; 0x00;
                           (* MULX4 (% rax,% r11) (% rdx,Memop Quadword (%% (rsi,168))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADCX (% r11) (% rbx) *)
  0xc4; 0xe2; 0x9b; 0xf6; 0x9e; 0xb0; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% r12) (% rdx,Memop Quadword (%% (rsi,176))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xc4; 0xe2; 0x93; 0xf6; 0x86; 0xb8; 0x00; 0x00; 0x00;
                           (* MULX4 (% rax,% r13) (% rdx,Memop Quadword (%% (rsi,184))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADCX (% r13) (% rbx) *)
  0xc4; 0xe2; 0x8b; 0xf6; 0x9e; 0xc0; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% r14) (% rdx,Memop Quadword (%% (rsi,192))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xc4; 0x62; 0x83; 0xf6; 0x86; 0xc8; 0x00; 0x00; 0x00;
                           (* MULX4 (% r8,% r15) (% rdx,Memop Quadword (%% (rsi,200))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADCX (% r15) (% rbx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc1;
                           (* ADCX (% r8) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x96; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsi,152))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9e; 0xa0; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,160))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0x4c; 0x89; 0x9c; 0x24; 0x10; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,528))) (% r11) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9e; 0xa8; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,168))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0x4c; 0x89; 0xa4; 0x24; 0x18; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,536))) (% r12) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9e; 0xb0; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,176))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9e; 0xb8; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,184))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9e; 0xc0; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,192))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x8e; 0xc8; 0x00; 0x00; 0x00;
                           (* MULX4 (% r9,% rax) (% rdx,Memop Quadword (%% (rsi,200))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc9;
                           (* ADOX (% r9) (% rcx) *)
  0x48; 0x8b; 0x96; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsi,176))) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x96; 0xb8; 0x00; 0x00; 0x00;
                           (* MULX4 (% r10,% rax) (% rdx,Memop Quadword (%% (rsi,184))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd1;
                           (* ADOX (% r10) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd1;
                           (* ADCX (% r10) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x96; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsi,160))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9e; 0xa8; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,168))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0x4c; 0x89; 0xac; 0x24; 0x20; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,544))) (% r13) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9e; 0xb0; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,176))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0x4c; 0x89; 0xb4; 0x24; 0x28; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,552))) (% r14) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9e; 0xb8; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,184))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9e; 0xc0; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,192))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9e; 0xc8; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,200))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0x48; 0x8b; 0x96; 0xc0; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsi,192))) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x9e; 0xb0; 0x00; 0x00; 0x00;
                           (* MULX4 (% r11,% rax) (% rdx,Memop Quadword (%% (rsi,176))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd9;
                           (* ADOX (% r11) (% rcx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xa6; 0xb8; 0x00; 0x00; 0x00;
                           (* MULX4 (% r12,% rax) (% rdx,Memop Quadword (%% (rsi,184))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe1;
                           (* ADOX (% r12) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe1;
                           (* ADCX (% r12) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x96; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsi,168))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9e; 0xb0; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,176))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0x4c; 0x89; 0xbc; 0x24; 0x30; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,560))) (% r15) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9e; 0xb8; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,184))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9e; 0xc0; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,192))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9e; 0xc8; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,200))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0x48; 0x8b; 0x96; 0xc8; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsi,200))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9e; 0xb0; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,176))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xae; 0xb8; 0x00; 0x00; 0x00;
                           (* MULX4 (% r13,% rax) (% rdx,Memop Quadword (%% (rsi,184))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADOX (% r13) (% rcx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xb6; 0xc0; 0x00; 0x00; 0x00;
                           (* MULX4 (% r14,% rax) (% rdx,Memop Quadword (%% (rsi,192))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADOX (% r14) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADCX (% r14) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x96; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsi,144))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rax) (% rdx,% rdx) *)
  0x48; 0x89; 0x84; 0x24; 0xf8; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,504))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x00; 0x02; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,512))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% rax) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% rax) (% rbx) *)
  0x48; 0x89; 0x84; 0x24; 0x00; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,512))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x08; 0x02; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,520))) *)
  0x48; 0x8b; 0x96; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsi,152))) *)
  0xc4; 0xe2; 0xeb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rdx) (% rdx,% rdx) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% rax) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xc2;
                           (* ADOX (% rax) (% rdx) *)
  0x48; 0x89; 0x84; 0x24; 0x08; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,520))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x10; 0x02; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,528))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% rax) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% rax) (% rbx) *)
  0x48; 0x89; 0x84; 0x24; 0x10; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,528))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x18; 0x02; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,536))) *)
  0x48; 0x8b; 0x96; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsi,160))) *)
  0xc4; 0xe2; 0xeb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rdx) (% rdx,% rdx) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% rax) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xc2;
                           (* ADOX (% rax) (% rdx) *)
  0x48; 0x89; 0x84; 0x24; 0x18; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,536))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x20; 0x02; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,544))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% rax) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% rax) (% rbx) *)
  0x48; 0x89; 0x84; 0x24; 0x20; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,544))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x28; 0x02; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,552))) *)
  0x48; 0x8b; 0x96; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsi,168))) *)
  0xc4; 0xe2; 0xeb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rdx) (% rdx,% rdx) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% rax) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xc2;
                           (* ADOX (% rax) (% rdx) *)
  0x48; 0x89; 0x84; 0x24; 0x28; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,552))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x30; 0x02; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,560))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% rax) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% rax) (% rbx) *)
  0x48; 0x89; 0x84; 0x24; 0x30; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,560))) (% rax) *)
  0x48; 0x8b; 0x96; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsi,176))) *)
  0xc4; 0xe2; 0xeb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rdx) (% rdx,% rdx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% r8) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc2;
                           (* ADOX (% r8) (% rdx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xc9;
                           (* ADCX (% r9) (% r9) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0x48; 0x8b; 0x96; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsi,184))) *)
  0xc4; 0xe2; 0xeb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rdx) (% rdx,% rdx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xd2;
                           (* ADCX (% r10) (% r10) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd2;
                           (* ADOX (% r10) (% rdx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADCX (% r11) (% r11) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0x48; 0x8b; 0x96; 0xc0; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsi,192))) *)
  0xc4; 0xe2; 0xeb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rdx) (% rdx,% rdx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xe4;
                           (* ADCX (% r12) (% r12) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe2;
                           (* ADOX (% r12) (% rdx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xed;
                           (* ADCX (% r13) (% r13) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0x48; 0x8b; 0x96; 0xc8; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsi,200))) *)
  0xc4; 0x62; 0xeb; 0xf6; 0xfa;
                           (* MULX4 (% r15,% rdx) (% rdx,% rdx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xf6;
                           (* ADCX (% r14) (% r14) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf2;
                           (* ADOX (% r14) (% rdx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADCX (% r15) (% rcx) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADOX (% r15) (% rcx) *)
  0x48; 0x8b; 0x96; 0xd0; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsi,208))) *)
  0x48; 0x89; 0xd1;        (* MOV (% rcx) (% rdx) *)
  0x48; 0x0f; 0xaf; 0xc9;  (* IMUL (% rcx) (% rcx) *)
  0x48; 0x01; 0xd2;        (* ADD (% rdx) (% rdx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9e; 0x90; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,144))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9e; 0x98; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,152))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9e; 0xa0; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,160))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9e; 0xa8; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,168))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9e; 0xb0; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,176))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9e; 0xb8; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,184))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9e; 0xc0; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,192))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9e; 0xc8; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,200))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% rcx) (% rbx) *)
  0x48; 0x83; 0xd1; 0x00;  (* ADC (% rcx) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xc0;        (* MOV (% rax) (% r8) *)
  0x48; 0x25; 0xff; 0x01; 0x00; 0x00;
                           (* AND (% rax) (Imm32 (word 511)) *)
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
  0x49; 0x0f; 0xac; 0xcf; 0x09;
                           (* SHRD (% r15) (% rcx) (Imm8 (word 9)) *)
  0x48; 0xc1; 0xe9; 0x09;  (* SHR (% rcx) (Imm8 (word 9)) *)
  0x48; 0x01; 0xc1;        (* ADD (% rcx) (% rax) *)
  0xf9;                    (* STCF *)
  0x4c; 0x13; 0x84; 0x24; 0xf8; 0x01; 0x00; 0x00;
                           (* ADC (% r8) (Memop Quadword (%% (rsp,504))) *)
  0x4c; 0x13; 0x8c; 0x24; 0x00; 0x02; 0x00; 0x00;
                           (* ADC (% r9) (Memop Quadword (%% (rsp,512))) *)
  0x4c; 0x13; 0x94; 0x24; 0x08; 0x02; 0x00; 0x00;
                           (* ADC (% r10) (Memop Quadword (%% (rsp,520))) *)
  0x4c; 0x13; 0x9c; 0x24; 0x10; 0x02; 0x00; 0x00;
                           (* ADC (% r11) (Memop Quadword (%% (rsp,528))) *)
  0x4c; 0x13; 0xa4; 0x24; 0x18; 0x02; 0x00; 0x00;
                           (* ADC (% r12) (Memop Quadword (%% (rsp,536))) *)
  0x4c; 0x13; 0xac; 0x24; 0x20; 0x02; 0x00; 0x00;
                           (* ADC (% r13) (Memop Quadword (%% (rsp,544))) *)
  0x4c; 0x13; 0xb4; 0x24; 0x28; 0x02; 0x00; 0x00;
                           (* ADC (% r14) (Memop Quadword (%% (rsp,552))) *)
  0x4c; 0x13; 0xbc; 0x24; 0x30; 0x02; 0x00; 0x00;
                           (* ADC (% r15) (Memop Quadword (%% (rsp,560))) *)
  0x48; 0x81; 0xd1; 0x00; 0xfe; 0xff; 0xff;
                           (* ADC (% rcx) (Imm32 (word 4294966784)) *)
  0xf5;                    (* CMC *)
  0x49; 0x83; 0xd8; 0x00;  (* SBB (% r8) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x04; 0x24;  (* MOV (Memop Quadword (%% (rsp,0))) (% r8) *)
  0x49; 0x83; 0xd9; 0x00;  (* SBB (% r9) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x4c; 0x24; 0x08;
                           (* MOV (Memop Quadword (%% (rsp,8))) (% r9) *)
  0x49; 0x83; 0xda; 0x00;  (* SBB (% r10) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x54; 0x24; 0x10;
                           (* MOV (Memop Quadword (%% (rsp,16))) (% r10) *)
  0x49; 0x83; 0xdb; 0x00;  (* SBB (% r11) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x5c; 0x24; 0x18;
                           (* MOV (Memop Quadword (%% (rsp,24))) (% r11) *)
  0x49; 0x83; 0xdc; 0x00;  (* SBB (% r12) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x64; 0x24; 0x20;
                           (* MOV (Memop Quadword (%% (rsp,32))) (% r12) *)
  0x49; 0x83; 0xdd; 0x00;  (* SBB (% r13) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x6c; 0x24; 0x28;
                           (* MOV (Memop Quadword (%% (rsp,40))) (% r13) *)
  0x49; 0x83; 0xde; 0x00;  (* SBB (% r14) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x74; 0x24; 0x30;
                           (* MOV (Memop Quadword (%% (rsp,48))) (% r14) *)
  0x49; 0x83; 0xdf; 0x00;  (* SBB (% r15) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x7c; 0x24; 0x38;
                           (* MOV (Memop Quadword (%% (rsp,56))) (% r15) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x48; 0x81; 0xe1; 0xff; 0x01; 0x00; 0x00;
                           (* AND (% rcx) (Imm32 (word 511)) *)
  0x48; 0x89; 0x4c; 0x24; 0x40;
                           (* MOV (Memop Quadword (%% (rsp,64))) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x56; 0x48;  (* MOV (% rdx) (Memop Quadword (%% (rsi,72))) *)
  0xc4; 0xe2; 0xb3; 0xf6; 0x46; 0x50;
                           (* MULX4 (% rax,% r9) (% rdx,Memop Quadword (%% (rsi,80))) *)
  0x4c; 0x89; 0x8c; 0x24; 0x00; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,512))) (% r9) *)
  0xc4; 0xe2; 0xab; 0xf6; 0x5e; 0x58;
                           (* MULX4 (% rbx,% r10) (% rdx,Memop Quadword (%% (rsi,88))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0x4c; 0x89; 0x94; 0x24; 0x08; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,520))) (% r10) *)
  0xc4; 0xe2; 0xa3; 0xf6; 0x46; 0x60;
                           (* MULX4 (% rax,% r11) (% rdx,Memop Quadword (%% (rsi,96))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADCX (% r11) (% rbx) *)
  0xc4; 0xe2; 0x9b; 0xf6; 0x5e; 0x68;
                           (* MULX4 (% rbx,% r12) (% rdx,Memop Quadword (%% (rsi,104))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xc4; 0xe2; 0x93; 0xf6; 0x46; 0x70;
                           (* MULX4 (% rax,% r13) (% rdx,Memop Quadword (%% (rsi,112))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADCX (% r13) (% rbx) *)
  0xc4; 0xe2; 0x8b; 0xf6; 0x5e; 0x78;
                           (* MULX4 (% rbx,% r14) (% rdx,Memop Quadword (%% (rsi,120))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xc4; 0x62; 0x83; 0xf6; 0x86; 0x80; 0x00; 0x00; 0x00;
                           (* MULX4 (% r8,% r15) (% rdx,Memop Quadword (%% (rsi,128))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADCX (% r15) (% rbx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc1;
                           (* ADCX (% r8) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x56; 0x50;  (* MOV (% rdx) (Memop Quadword (%% (rsi,80))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x58;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,88))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0x4c; 0x89; 0x9c; 0x24; 0x10; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,528))) (% r11) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x60;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,96))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0x4c; 0x89; 0xa4; 0x24; 0x18; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,536))) (% r12) *)
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
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x78;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,120))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x8e; 0x80; 0x00; 0x00; 0x00;
                           (* MULX4 (% r9,% rax) (% rdx,Memop Quadword (%% (rsi,128))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc9;
                           (* ADOX (% r9) (% rcx) *)
  0x48; 0x8b; 0x56; 0x68;  (* MOV (% rdx) (Memop Quadword (%% (rsi,104))) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x56; 0x70;
                           (* MULX4 (% r10,% rax) (% rdx,Memop Quadword (%% (rsi,112))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd1;
                           (* ADOX (% r10) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd1;
                           (* ADCX (% r10) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x56; 0x58;  (* MOV (% rdx) (Memop Quadword (%% (rsi,88))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x60;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,96))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0x4c; 0x89; 0xac; 0x24; 0x20; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,544))) (% r13) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x68;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,104))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0x4c; 0x89; 0xb4; 0x24; 0x28; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,552))) (% r14) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x70;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,112))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x78;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,120))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9e; 0x80; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,128))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0x48; 0x8b; 0x56; 0x78;  (* MOV (% rdx) (Memop Quadword (%% (rsi,120))) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x5e; 0x68;
                           (* MULX4 (% r11,% rax) (% rdx,Memop Quadword (%% (rsi,104))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd9;
                           (* ADOX (% r11) (% rcx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x66; 0x70;
                           (* MULX4 (% r12,% rax) (% rdx,Memop Quadword (%% (rsi,112))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe1;
                           (* ADOX (% r12) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe1;
                           (* ADCX (% r12) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x56; 0x60;  (* MOV (% rdx) (Memop Quadword (%% (rsi,96))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x68;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,104))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0x4c; 0x89; 0xbc; 0x24; 0x30; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,560))) (% r15) *)
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
  0xc4; 0xe2; 0xfb; 0xf6; 0x9e; 0x80; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,128))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0x48; 0x8b; 0x96; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsi,128))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x68;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,104))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x6e; 0x70;
                           (* MULX4 (% r13,% rax) (% rdx,Memop Quadword (%% (rsi,112))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADOX (% r13) (% rcx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x76; 0x78;
                           (* MULX4 (% r14,% rax) (% rdx,Memop Quadword (%% (rsi,120))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADOX (% r14) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADCX (% r14) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x56; 0x48;  (* MOV (% rdx) (Memop Quadword (%% (rsi,72))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rax) (% rdx,% rdx) *)
  0x48; 0x89; 0x84; 0x24; 0xf8; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,504))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x00; 0x02; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,512))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% rax) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% rax) (% rbx) *)
  0x48; 0x89; 0x84; 0x24; 0x00; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,512))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x08; 0x02; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,520))) *)
  0x48; 0x8b; 0x56; 0x50;  (* MOV (% rdx) (Memop Quadword (%% (rsi,80))) *)
  0xc4; 0xe2; 0xeb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rdx) (% rdx,% rdx) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% rax) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xc2;
                           (* ADOX (% rax) (% rdx) *)
  0x48; 0x89; 0x84; 0x24; 0x08; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,520))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x10; 0x02; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,528))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% rax) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% rax) (% rbx) *)
  0x48; 0x89; 0x84; 0x24; 0x10; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,528))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x18; 0x02; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,536))) *)
  0x48; 0x8b; 0x56; 0x58;  (* MOV (% rdx) (Memop Quadword (%% (rsi,88))) *)
  0xc4; 0xe2; 0xeb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rdx) (% rdx,% rdx) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% rax) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xc2;
                           (* ADOX (% rax) (% rdx) *)
  0x48; 0x89; 0x84; 0x24; 0x18; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,536))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x20; 0x02; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,544))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% rax) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% rax) (% rbx) *)
  0x48; 0x89; 0x84; 0x24; 0x20; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,544))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x28; 0x02; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,552))) *)
  0x48; 0x8b; 0x56; 0x60;  (* MOV (% rdx) (Memop Quadword (%% (rsi,96))) *)
  0xc4; 0xe2; 0xeb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rdx) (% rdx,% rdx) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% rax) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xc2;
                           (* ADOX (% rax) (% rdx) *)
  0x48; 0x89; 0x84; 0x24; 0x28; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,552))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x30; 0x02; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,560))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% rax) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% rax) (% rbx) *)
  0x48; 0x89; 0x84; 0x24; 0x30; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,560))) (% rax) *)
  0x48; 0x8b; 0x56; 0x68;  (* MOV (% rdx) (Memop Quadword (%% (rsi,104))) *)
  0xc4; 0xe2; 0xeb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rdx) (% rdx,% rdx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% r8) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc2;
                           (* ADOX (% r8) (% rdx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xc9;
                           (* ADCX (% r9) (% r9) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0x48; 0x8b; 0x56; 0x70;  (* MOV (% rdx) (Memop Quadword (%% (rsi,112))) *)
  0xc4; 0xe2; 0xeb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rdx) (% rdx,% rdx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xd2;
                           (* ADCX (% r10) (% r10) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd2;
                           (* ADOX (% r10) (% rdx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADCX (% r11) (% r11) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0x48; 0x8b; 0x56; 0x78;  (* MOV (% rdx) (Memop Quadword (%% (rsi,120))) *)
  0xc4; 0xe2; 0xeb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rdx) (% rdx,% rdx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xe4;
                           (* ADCX (% r12) (% r12) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe2;
                           (* ADOX (% r12) (% rdx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xed;
                           (* ADCX (% r13) (% r13) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0x48; 0x8b; 0x96; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsi,128))) *)
  0xc4; 0x62; 0xeb; 0xf6; 0xfa;
                           (* MULX4 (% r15,% rdx) (% rdx,% rdx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xf6;
                           (* ADCX (% r14) (% r14) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf2;
                           (* ADOX (% r14) (% rdx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADCX (% r15) (% rcx) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADOX (% r15) (% rcx) *)
  0x48; 0x8b; 0x96; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsi,136))) *)
  0x48; 0x89; 0xd1;        (* MOV (% rcx) (% rdx) *)
  0x48; 0x0f; 0xaf; 0xc9;  (* IMUL (% rcx) (% rcx) *)
  0x48; 0x01; 0xd2;        (* ADD (% rdx) (% rdx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x48;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,72))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x50;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,80))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x58;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,88))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x60;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,96))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x68;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,104))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x70;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,112))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x78;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,120))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9e; 0x80; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,128))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% rcx) (% rbx) *)
  0x48; 0x83; 0xd1; 0x00;  (* ADC (% rcx) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xc0;        (* MOV (% rax) (% r8) *)
  0x48; 0x25; 0xff; 0x01; 0x00; 0x00;
                           (* AND (% rax) (Imm32 (word 511)) *)
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
  0x49; 0x0f; 0xac; 0xcf; 0x09;
                           (* SHRD (% r15) (% rcx) (Imm8 (word 9)) *)
  0x48; 0xc1; 0xe9; 0x09;  (* SHR (% rcx) (Imm8 (word 9)) *)
  0x48; 0x01; 0xc1;        (* ADD (% rcx) (% rax) *)
  0xf9;                    (* STCF *)
  0x4c; 0x13; 0x84; 0x24; 0xf8; 0x01; 0x00; 0x00;
                           (* ADC (% r8) (Memop Quadword (%% (rsp,504))) *)
  0x4c; 0x13; 0x8c; 0x24; 0x00; 0x02; 0x00; 0x00;
                           (* ADC (% r9) (Memop Quadword (%% (rsp,512))) *)
  0x4c; 0x13; 0x94; 0x24; 0x08; 0x02; 0x00; 0x00;
                           (* ADC (% r10) (Memop Quadword (%% (rsp,520))) *)
  0x4c; 0x13; 0x9c; 0x24; 0x10; 0x02; 0x00; 0x00;
                           (* ADC (% r11) (Memop Quadword (%% (rsp,528))) *)
  0x4c; 0x13; 0xa4; 0x24; 0x18; 0x02; 0x00; 0x00;
                           (* ADC (% r12) (Memop Quadword (%% (rsp,536))) *)
  0x4c; 0x13; 0xac; 0x24; 0x20; 0x02; 0x00; 0x00;
                           (* ADC (% r13) (Memop Quadword (%% (rsp,544))) *)
  0x4c; 0x13; 0xb4; 0x24; 0x28; 0x02; 0x00; 0x00;
                           (* ADC (% r14) (Memop Quadword (%% (rsp,552))) *)
  0x4c; 0x13; 0xbc; 0x24; 0x30; 0x02; 0x00; 0x00;
                           (* ADC (% r15) (Memop Quadword (%% (rsp,560))) *)
  0x48; 0x81; 0xd1; 0x00; 0xfe; 0xff; 0xff;
                           (* ADC (% rcx) (Imm32 (word 4294966784)) *)
  0xf5;                    (* CMC *)
  0x49; 0x83; 0xd8; 0x00;  (* SBB (% r8) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x44; 0x24; 0x48;
                           (* MOV (Memop Quadword (%% (rsp,72))) (% r8) *)
  0x49; 0x83; 0xd9; 0x00;  (* SBB (% r9) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x4c; 0x24; 0x50;
                           (* MOV (Memop Quadword (%% (rsp,80))) (% r9) *)
  0x49; 0x83; 0xda; 0x00;  (* SBB (% r10) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x54; 0x24; 0x58;
                           (* MOV (Memop Quadword (%% (rsp,88))) (% r10) *)
  0x49; 0x83; 0xdb; 0x00;  (* SBB (% r11) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x5c; 0x24; 0x60;
                           (* MOV (Memop Quadword (%% (rsp,96))) (% r11) *)
  0x49; 0x83; 0xdc; 0x00;  (* SBB (% r12) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x64; 0x24; 0x68;
                           (* MOV (Memop Quadword (%% (rsp,104))) (% r12) *)
  0x49; 0x83; 0xdd; 0x00;  (* SBB (% r13) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x6c; 0x24; 0x70;
                           (* MOV (Memop Quadword (%% (rsp,112))) (% r13) *)
  0x49; 0x83; 0xde; 0x00;  (* SBB (% r14) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x74; 0x24; 0x78;
                           (* MOV (Memop Quadword (%% (rsp,120))) (% r14) *)
  0x49; 0x83; 0xdf; 0x00;  (* SBB (% r15) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xbc; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,128))) (% r15) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x48; 0x81; 0xe1; 0xff; 0x01; 0x00; 0x00;
                           (* AND (% rcx) (Imm32 (word 511)) *)
  0x48; 0x89; 0x8c; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,136))) (% rcx) *)
  0xf9;                    (* STCF *)
  0x48; 0x8b; 0x06;        (* MOV (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0x13; 0x04; 0x24;  (* ADC (% rax) (Memop Quadword (%% (rsp,0))) *)
  0x48; 0x8b; 0x5e; 0x08;  (* MOV (% rbx) (Memop Quadword (%% (rsi,8))) *)
  0x48; 0x13; 0x5c; 0x24; 0x08;
                           (* ADC (% rbx) (Memop Quadword (%% (rsp,8))) *)
  0x4c; 0x8b; 0x46; 0x10;  (* MOV (% r8) (Memop Quadword (%% (rsi,16))) *)
  0x4c; 0x13; 0x44; 0x24; 0x10;
                           (* ADC (% r8) (Memop Quadword (%% (rsp,16))) *)
  0x4c; 0x8b; 0x4e; 0x18;  (* MOV (% r9) (Memop Quadword (%% (rsi,24))) *)
  0x4c; 0x13; 0x4c; 0x24; 0x18;
                           (* ADC (% r9) (Memop Quadword (%% (rsp,24))) *)
  0x4c; 0x8b; 0x56; 0x20;  (* MOV (% r10) (Memop Quadword (%% (rsi,32))) *)
  0x4c; 0x13; 0x54; 0x24; 0x20;
                           (* ADC (% r10) (Memop Quadword (%% (rsp,32))) *)
  0x4c; 0x8b; 0x5e; 0x28;  (* MOV (% r11) (Memop Quadword (%% (rsi,40))) *)
  0x4c; 0x13; 0x5c; 0x24; 0x28;
                           (* ADC (% r11) (Memop Quadword (%% (rsp,40))) *)
  0x4c; 0x8b; 0x66; 0x30;  (* MOV (% r12) (Memop Quadword (%% (rsi,48))) *)
  0x4c; 0x13; 0x64; 0x24; 0x30;
                           (* ADC (% r12) (Memop Quadword (%% (rsp,48))) *)
  0x4c; 0x8b; 0x6e; 0x38;  (* MOV (% r13) (Memop Quadword (%% (rsi,56))) *)
  0x4c; 0x13; 0x6c; 0x24; 0x38;
                           (* ADC (% r13) (Memop Quadword (%% (rsp,56))) *)
  0x4c; 0x8b; 0x76; 0x40;  (* MOV (% r14) (Memop Quadword (%% (rsi,64))) *)
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
  0x48; 0x8b; 0x06;        (* MOV (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0x2b; 0x04; 0x24;  (* SUB (% rax) (Memop Quadword (%% (rsp,0))) *)
  0x48; 0x8b; 0x56; 0x08;  (* MOV (% rdx) (Memop Quadword (%% (rsi,8))) *)
  0x48; 0x1b; 0x54; 0x24; 0x08;
                           (* SBB (% rdx) (Memop Quadword (%% (rsp,8))) *)
  0x4c; 0x8b; 0x46; 0x10;  (* MOV (% r8) (Memop Quadword (%% (rsi,16))) *)
  0x4c; 0x1b; 0x44; 0x24; 0x10;
                           (* SBB (% r8) (Memop Quadword (%% (rsp,16))) *)
  0x4c; 0x8b; 0x4e; 0x18;  (* MOV (% r9) (Memop Quadword (%% (rsi,24))) *)
  0x4c; 0x1b; 0x4c; 0x24; 0x18;
                           (* SBB (% r9) (Memop Quadword (%% (rsp,24))) *)
  0x4c; 0x8b; 0x56; 0x20;  (* MOV (% r10) (Memop Quadword (%% (rsi,32))) *)
  0x4c; 0x1b; 0x54; 0x24; 0x20;
                           (* SBB (% r10) (Memop Quadword (%% (rsp,32))) *)
  0x4c; 0x8b; 0x5e; 0x28;  (* MOV (% r11) (Memop Quadword (%% (rsi,40))) *)
  0x4c; 0x1b; 0x5c; 0x24; 0x28;
                           (* SBB (% r11) (Memop Quadword (%% (rsp,40))) *)
  0x4c; 0x8b; 0x66; 0x30;  (* MOV (% r12) (Memop Quadword (%% (rsi,48))) *)
  0x4c; 0x1b; 0x64; 0x24; 0x30;
                           (* SBB (% r12) (Memop Quadword (%% (rsp,48))) *)
  0x4c; 0x8b; 0x6e; 0x38;  (* MOV (% r13) (Memop Quadword (%% (rsi,56))) *)
  0x4c; 0x1b; 0x6c; 0x24; 0x38;
                           (* SBB (% r13) (Memop Quadword (%% (rsp,56))) *)
  0x4c; 0x8b; 0x76; 0x40;  (* MOV (% r14) (Memop Quadword (%% (rsi,64))) *)
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
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x94; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,288))) *)
  0xc4; 0x62; 0xbb; 0xf6; 0x8c; 0x24; 0x68; 0x01; 0x00; 0x00;
                           (* MULX4 (% r9,% r8) (% rdx,Memop Quadword (%% (rsp,360))) *)
  0x4c; 0x89; 0x84; 0x24; 0xf8; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,504))) (% r8) *)
  0xc4; 0x62; 0xe3; 0xf6; 0x94; 0x24; 0x70; 0x01; 0x00; 0x00;
                           (* MULX4 (% r10,% rbx) (% rdx,Memop Quadword (%% (rsp,368))) *)
  0x49; 0x11; 0xd9;        (* ADC (% r9) (% rbx) *)
  0xc4; 0x62; 0xe3; 0xf6; 0x9c; 0x24; 0x78; 0x01; 0x00; 0x00;
                           (* MULX4 (% r11,% rbx) (% rdx,Memop Quadword (%% (rsp,376))) *)
  0x49; 0x11; 0xda;        (* ADC (% r10) (% rbx) *)
  0xc4; 0x62; 0xe3; 0xf6; 0xa4; 0x24; 0x80; 0x01; 0x00; 0x00;
                           (* MULX4 (% r12,% rbx) (% rdx,Memop Quadword (%% (rsp,384))) *)
  0x49; 0x11; 0xdb;        (* ADC (% r11) (% rbx) *)
  0xc4; 0x62; 0xe3; 0xf6; 0xac; 0x24; 0x88; 0x01; 0x00; 0x00;
                           (* MULX4 (% r13,% rbx) (% rdx,Memop Quadword (%% (rsp,392))) *)
  0x49; 0x11; 0xdc;        (* ADC (% r12) (% rbx) *)
  0xc4; 0x62; 0xe3; 0xf6; 0xb4; 0x24; 0x90; 0x01; 0x00; 0x00;
                           (* MULX4 (% r14,% rbx) (% rdx,Memop Quadword (%% (rsp,400))) *)
  0x49; 0x11; 0xdd;        (* ADC (% r13) (% rbx) *)
  0xc4; 0x62; 0xe3; 0xf6; 0xbc; 0x24; 0x98; 0x01; 0x00; 0x00;
                           (* MULX4 (% r15,% rbx) (% rdx,Memop Quadword (%% (rsp,408))) *)
  0x49; 0x11; 0xde;        (* ADC (% r14) (% rbx) *)
  0xc4; 0x62; 0xe3; 0xf6; 0x84; 0x24; 0xa0; 0x01; 0x00; 0x00;
                           (* MULX4 (% r8,% rbx) (% rdx,Memop Quadword (%% (rsp,416))) *)
  0x49; 0x11; 0xdf;        (* ADC (% r15) (% rbx) *)
  0x49; 0x11; 0xc8;        (* ADC (% r8) (% rcx) *)
  0x48; 0x8b; 0x94; 0x24; 0x28; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,296))) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x68; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,360))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0x4c; 0x89; 0x8c; 0x24; 0x00; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,512))) (% r9) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x70; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,368))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x78; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,376))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x80; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,384))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x88; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,392))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x90; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,400))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x98; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,408))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x8c; 0x24; 0xa0; 0x01; 0x00; 0x00;
                           (* MULX4 (% r9,% rax) (% rdx,Memop Quadword (%% (rsp,416))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc9;
                           (* ADOX (% r9) (% rcx) *)
  0x49; 0x11; 0xc9;        (* ADC (% r9) (% rcx) *)
  0x48; 0x8b; 0x94; 0x24; 0x30; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,304))) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x68; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,360))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0x4c; 0x89; 0x94; 0x24; 0x08; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,520))) (% r10) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x70; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,368))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x78; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,376))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x80; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,384))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x88; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,392))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x90; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,400))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x98; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,408))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x94; 0x24; 0xa0; 0x01; 0x00; 0x00;
                           (* MULX4 (% r10,% rax) (% rdx,Memop Quadword (%% (rsp,416))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd1;
                           (* ADOX (% r10) (% rcx) *)
  0x49; 0x11; 0xca;        (* ADC (% r10) (% rcx) *)
  0x48; 0x8b; 0x94; 0x24; 0x38; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,312))) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x68; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,360))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0x4c; 0x89; 0x9c; 0x24; 0x10; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,528))) (% r11) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x70; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,368))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x78; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,376))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x80; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,384))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x88; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,392))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x90; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,400))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x98; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,408))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x9c; 0x24; 0xa0; 0x01; 0x00; 0x00;
                           (* MULX4 (% r11,% rax) (% rdx,Memop Quadword (%% (rsp,416))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd9;
                           (* ADOX (% r11) (% rcx) *)
  0x49; 0x11; 0xcb;        (* ADC (% r11) (% rcx) *)
  0x48; 0x8b; 0x94; 0x24; 0x40; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,320))) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x68; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,360))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0x4c; 0x89; 0xa4; 0x24; 0x18; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,536))) (% r12) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x70; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,368))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x78; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,376))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x80; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,384))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x88; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,392))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x90; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,400))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x98; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,408))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xa4; 0x24; 0xa0; 0x01; 0x00; 0x00;
                           (* MULX4 (% r12,% rax) (% rdx,Memop Quadword (%% (rsp,416))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe1;
                           (* ADOX (% r12) (% rcx) *)
  0x49; 0x11; 0xcc;        (* ADC (% r12) (% rcx) *)
  0x48; 0x8b; 0x94; 0x24; 0x48; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,328))) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x68; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,360))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0x4c; 0x89; 0xac; 0x24; 0x20; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,544))) (% r13) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x70; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,368))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x78; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,376))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x80; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,384))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x88; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,392))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x90; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,400))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x98; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,408))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xac; 0x24; 0xa0; 0x01; 0x00; 0x00;
                           (* MULX4 (% r13,% rax) (% rdx,Memop Quadword (%% (rsp,416))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADOX (% r13) (% rcx) *)
  0x49; 0x11; 0xcd;        (* ADC (% r13) (% rcx) *)
  0x48; 0x8b; 0x94; 0x24; 0x50; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,336))) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x68; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,360))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0x4c; 0x89; 0xb4; 0x24; 0x28; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,552))) (% r14) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x70; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,368))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x78; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,376))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x80; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,384))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x88; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,392))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x90; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,400))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x98; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,408))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xb4; 0x24; 0xa0; 0x01; 0x00; 0x00;
                           (* MULX4 (% r14,% rax) (% rdx,Memop Quadword (%% (rsp,416))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADOX (% r14) (% rcx) *)
  0x49; 0x11; 0xce;        (* ADC (% r14) (% rcx) *)
  0x48; 0x8b; 0x94; 0x24; 0x58; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,344))) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x68; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,360))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0x4c; 0x89; 0xbc; 0x24; 0x30; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,560))) (% r15) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x70; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,368))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x78; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,376))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x80; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,384))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x88; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,392))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x90; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,400))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x98; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,408))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xbc; 0x24; 0xa0; 0x01; 0x00; 0x00;
                           (* MULX4 (% r15,% rax) (% rdx,Memop Quadword (%% (rsp,416))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADOX (% r15) (% rcx) *)
  0x49; 0x11; 0xcf;        (* ADC (% r15) (% rcx) *)
  0x48; 0x8b; 0x94; 0x24; 0xa8; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,424))) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,288))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x28; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,296))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x30; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,304))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x38; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,312))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x40; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,320))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x48; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,328))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x50; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,336))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x58; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,344))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xd9;
                           (* ADOX (% rbx) (% rcx) *)
  0x48; 0x11; 0xd9;        (* ADC (% rcx) (% rbx) *)
  0x48; 0x8b; 0x94; 0x24; 0x60; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,352))) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x68; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,360))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x70; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,368))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x78; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,376))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x80; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,384))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x88; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,392))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x90; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,400))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x98; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,408))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xa0; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,416))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% rcx) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xa8; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,424))) *)
  0x48; 0x11; 0xc1;        (* ADC (% rcx) (% rax) *)
  0x4c; 0x89; 0xc0;        (* MOV (% rax) (% r8) *)
  0x48; 0x25; 0xff; 0x01; 0x00; 0x00;
                           (* AND (% rax) (Imm32 (word 511)) *)
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
  0x49; 0x0f; 0xac; 0xcf; 0x09;
                           (* SHRD (% r15) (% rcx) (Imm8 (word 9)) *)
  0x48; 0xc1; 0xe9; 0x09;  (* SHR (% rcx) (Imm8 (word 9)) *)
  0x48; 0x01; 0xc1;        (* ADD (% rcx) (% rax) *)
  0xf9;                    (* STCF *)
  0x4c; 0x13; 0x84; 0x24; 0xf8; 0x01; 0x00; 0x00;
                           (* ADC (% r8) (Memop Quadword (%% (rsp,504))) *)
  0x4c; 0x13; 0x8c; 0x24; 0x00; 0x02; 0x00; 0x00;
                           (* ADC (% r9) (Memop Quadword (%% (rsp,512))) *)
  0x4c; 0x13; 0x94; 0x24; 0x08; 0x02; 0x00; 0x00;
                           (* ADC (% r10) (Memop Quadword (%% (rsp,520))) *)
  0x4c; 0x13; 0x9c; 0x24; 0x10; 0x02; 0x00; 0x00;
                           (* ADC (% r11) (Memop Quadword (%% (rsp,528))) *)
  0x4c; 0x13; 0xa4; 0x24; 0x18; 0x02; 0x00; 0x00;
                           (* ADC (% r12) (Memop Quadword (%% (rsp,536))) *)
  0x4c; 0x13; 0xac; 0x24; 0x20; 0x02; 0x00; 0x00;
                           (* ADC (% r13) (Memop Quadword (%% (rsp,544))) *)
  0x4c; 0x13; 0xb4; 0x24; 0x28; 0x02; 0x00; 0x00;
                           (* ADC (% r14) (Memop Quadword (%% (rsp,552))) *)
  0x4c; 0x13; 0xbc; 0x24; 0x30; 0x02; 0x00; 0x00;
                           (* ADC (% r15) (Memop Quadword (%% (rsp,560))) *)
  0x48; 0x81; 0xd1; 0x00; 0xfe; 0xff; 0xff;
                           (* ADC (% rcx) (Imm32 (word 4294966784)) *)
  0xf5;                    (* CMC *)
  0x49; 0x83; 0xd8; 0x00;  (* SBB (% r8) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x84; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,144))) (% r8) *)
  0x49; 0x83; 0xd9; 0x00;  (* SBB (% r9) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x8c; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,152))) (% r9) *)
  0x49; 0x83; 0xda; 0x00;  (* SBB (% r10) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x94; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,160))) (% r10) *)
  0x49; 0x83; 0xdb; 0x00;  (* SBB (% r11) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x9c; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,168))) (% r11) *)
  0x49; 0x83; 0xdc; 0x00;  (* SBB (% r12) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xa4; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,176))) (% r12) *)
  0x49; 0x83; 0xdd; 0x00;  (* SBB (% r13) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xac; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,184))) (% r13) *)
  0x49; 0x83; 0xde; 0x00;  (* SBB (% r14) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xb4; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,192))) (% r14) *)
  0x49; 0x83; 0xdf; 0x00;  (* SBB (% r15) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xbc; 0x24; 0xc8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,200))) (% r15) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x48; 0x81; 0xe1; 0xff; 0x01; 0x00; 0x00;
                           (* AND (% rcx) (Imm32 (word 511)) *)
  0x48; 0x89; 0x8c; 0x24; 0xd0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,208))) (% rcx) *)
  0xf9;                    (* STCF *)
  0x48; 0x8b; 0x46; 0x48;  (* MOV (% rax) (Memop Quadword (%% (rsi,72))) *)
  0x48; 0x13; 0x86; 0x90; 0x00; 0x00; 0x00;
                           (* ADC (% rax) (Memop Quadword (%% (rsi,144))) *)
  0x48; 0x8b; 0x5e; 0x50;  (* MOV (% rbx) (Memop Quadword (%% (rsi,80))) *)
  0x48; 0x13; 0x9e; 0x98; 0x00; 0x00; 0x00;
                           (* ADC (% rbx) (Memop Quadword (%% (rsi,152))) *)
  0x4c; 0x8b; 0x46; 0x58;  (* MOV (% r8) (Memop Quadword (%% (rsi,88))) *)
  0x4c; 0x13; 0x86; 0xa0; 0x00; 0x00; 0x00;
                           (* ADC (% r8) (Memop Quadword (%% (rsi,160))) *)
  0x4c; 0x8b; 0x4e; 0x60;  (* MOV (% r9) (Memop Quadword (%% (rsi,96))) *)
  0x4c; 0x13; 0x8e; 0xa8; 0x00; 0x00; 0x00;
                           (* ADC (% r9) (Memop Quadword (%% (rsi,168))) *)
  0x4c; 0x8b; 0x56; 0x68;  (* MOV (% r10) (Memop Quadword (%% (rsi,104))) *)
  0x4c; 0x13; 0x96; 0xb0; 0x00; 0x00; 0x00;
                           (* ADC (% r10) (Memop Quadword (%% (rsi,176))) *)
  0x4c; 0x8b; 0x5e; 0x70;  (* MOV (% r11) (Memop Quadword (%% (rsi,112))) *)
  0x4c; 0x13; 0x9e; 0xb8; 0x00; 0x00; 0x00;
                           (* ADC (% r11) (Memop Quadword (%% (rsi,184))) *)
  0x4c; 0x8b; 0x66; 0x78;  (* MOV (% r12) (Memop Quadword (%% (rsi,120))) *)
  0x4c; 0x13; 0xa6; 0xc0; 0x00; 0x00; 0x00;
                           (* ADC (% r12) (Memop Quadword (%% (rsi,192))) *)
  0x4c; 0x8b; 0xae; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (% r13) (Memop Quadword (%% (rsi,128))) *)
  0x4c; 0x13; 0xae; 0xc8; 0x00; 0x00; 0x00;
                           (* ADC (% r13) (Memop Quadword (%% (rsi,200))) *)
  0x4c; 0x8b; 0xb6; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (% r14) (Memop Quadword (%% (rsi,136))) *)
  0x4c; 0x13; 0xb6; 0xd0; 0x00; 0x00; 0x00;
                           (* ADC (% r14) (Memop Quadword (%% (rsi,208))) *)
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
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x94; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,144))) *)
  0xc4; 0xe2; 0xb3; 0xf6; 0x84; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MULX4 (% rax,% r9) (% rdx,Memop Quadword (%% (rsp,152))) *)
  0x4c; 0x89; 0x8c; 0x24; 0x00; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,512))) (% r9) *)
  0xc4; 0xe2; 0xab; 0xf6; 0x9c; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% r10) (% rdx,Memop Quadword (%% (rsp,160))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0x4c; 0x89; 0x94; 0x24; 0x08; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,520))) (% r10) *)
  0xc4; 0xe2; 0xa3; 0xf6; 0x84; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MULX4 (% rax,% r11) (% rdx,Memop Quadword (%% (rsp,168))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADCX (% r11) (% rbx) *)
  0xc4; 0xe2; 0x9b; 0xf6; 0x9c; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% r12) (% rdx,Memop Quadword (%% (rsp,176))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xc4; 0xe2; 0x93; 0xf6; 0x84; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MULX4 (% rax,% r13) (% rdx,Memop Quadword (%% (rsp,184))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADCX (% r13) (% rbx) *)
  0xc4; 0xe2; 0x8b; 0xf6; 0x9c; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% r14) (% rdx,Memop Quadword (%% (rsp,192))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xc4; 0x62; 0x83; 0xf6; 0x84; 0x24; 0xc8; 0x00; 0x00; 0x00;
                           (* MULX4 (% r8,% r15) (% rdx,Memop Quadword (%% (rsp,200))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADCX (% r15) (% rbx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc1;
                           (* ADCX (% r8) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x94; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,152))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,160))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0x4c; 0x89; 0x9c; 0x24; 0x10; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,528))) (% r11) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,168))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0x4c; 0x89; 0xa4; 0x24; 0x18; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,536))) (% r12) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,176))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,184))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,192))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x8c; 0x24; 0xc8; 0x00; 0x00; 0x00;
                           (* MULX4 (% r9,% rax) (% rdx,Memop Quadword (%% (rsp,200))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc9;
                           (* ADOX (% r9) (% rcx) *)
  0x48; 0x8b; 0x94; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,176))) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x94; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MULX4 (% r10,% rax) (% rdx,Memop Quadword (%% (rsp,184))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd1;
                           (* ADOX (% r10) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd1;
                           (* ADCX (% r10) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x94; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,160))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,168))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0x4c; 0x89; 0xac; 0x24; 0x20; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,544))) (% r13) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,176))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0x4c; 0x89; 0xb4; 0x24; 0x28; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,552))) (% r14) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,184))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,192))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xc8; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,200))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0x48; 0x8b; 0x94; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,192))) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x9c; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MULX4 (% r11,% rax) (% rdx,Memop Quadword (%% (rsp,176))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd9;
                           (* ADOX (% r11) (% rcx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xa4; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MULX4 (% r12,% rax) (% rdx,Memop Quadword (%% (rsp,184))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe1;
                           (* ADOX (% r12) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe1;
                           (* ADCX (% r12) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x94; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,168))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,176))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0x4c; 0x89; 0xbc; 0x24; 0x30; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,560))) (% r15) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,184))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,192))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xc8; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,200))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0x48; 0x8b; 0x94; 0x24; 0xc8; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,200))) *)
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
  0xc4; 0x62; 0xfb; 0xf6; 0xb4; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* MULX4 (% r14,% rax) (% rdx,Memop Quadword (%% (rsp,192))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADOX (% r14) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADCX (% r14) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x94; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,144))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rax) (% rdx,% rdx) *)
  0x48; 0x89; 0x84; 0x24; 0xf8; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,504))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x00; 0x02; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,512))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% rax) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% rax) (% rbx) *)
  0x48; 0x89; 0x84; 0x24; 0x00; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,512))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x08; 0x02; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,520))) *)
  0x48; 0x8b; 0x94; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,152))) *)
  0xc4; 0xe2; 0xeb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rdx) (% rdx,% rdx) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% rax) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xc2;
                           (* ADOX (% rax) (% rdx) *)
  0x48; 0x89; 0x84; 0x24; 0x08; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,520))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x10; 0x02; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,528))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% rax) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% rax) (% rbx) *)
  0x48; 0x89; 0x84; 0x24; 0x10; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,528))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x18; 0x02; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,536))) *)
  0x48; 0x8b; 0x94; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,160))) *)
  0xc4; 0xe2; 0xeb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rdx) (% rdx,% rdx) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% rax) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xc2;
                           (* ADOX (% rax) (% rdx) *)
  0x48; 0x89; 0x84; 0x24; 0x18; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,536))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x20; 0x02; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,544))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% rax) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% rax) (% rbx) *)
  0x48; 0x89; 0x84; 0x24; 0x20; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,544))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x28; 0x02; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,552))) *)
  0x48; 0x8b; 0x94; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,168))) *)
  0xc4; 0xe2; 0xeb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rdx) (% rdx,% rdx) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% rax) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xc2;
                           (* ADOX (% rax) (% rdx) *)
  0x48; 0x89; 0x84; 0x24; 0x28; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,552))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x30; 0x02; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,560))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% rax) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% rax) (% rbx) *)
  0x48; 0x89; 0x84; 0x24; 0x30; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,560))) (% rax) *)
  0x48; 0x8b; 0x94; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,176))) *)
  0xc4; 0xe2; 0xeb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rdx) (% rdx,% rdx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% r8) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc2;
                           (* ADOX (% r8) (% rdx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xc9;
                           (* ADCX (% r9) (% r9) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0x48; 0x8b; 0x94; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,184))) *)
  0xc4; 0xe2; 0xeb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rdx) (% rdx,% rdx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xd2;
                           (* ADCX (% r10) (% r10) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd2;
                           (* ADOX (% r10) (% rdx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADCX (% r11) (% r11) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0x48; 0x8b; 0x94; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,192))) *)
  0xc4; 0xe2; 0xeb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rdx) (% rdx,% rdx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xe4;
                           (* ADCX (% r12) (% r12) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe2;
                           (* ADOX (% r12) (% rdx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xed;
                           (* ADCX (% r13) (% r13) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0x48; 0x8b; 0x94; 0x24; 0xc8; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,200))) *)
  0xc4; 0x62; 0xeb; 0xf6; 0xfa;
                           (* MULX4 (% r15,% rdx) (% rdx,% rdx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xf6;
                           (* ADCX (% r14) (% r14) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf2;
                           (* ADOX (% r14) (% rdx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADCX (% r15) (% rcx) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADOX (% r15) (% rcx) *)
  0x48; 0x8b; 0x94; 0x24; 0xd0; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,208))) *)
  0x48; 0x89; 0xd1;        (* MOV (% rcx) (% rdx) *)
  0x48; 0x0f; 0xaf; 0xc9;  (* IMUL (% rcx) (% rcx) *)
  0x48; 0x01; 0xd2;        (* ADD (% rdx) (% rdx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,144))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,152))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
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
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,184))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,192))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xc8; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,200))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% rcx) (% rbx) *)
  0x48; 0x83; 0xd1; 0x00;  (* ADC (% rcx) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xc0;        (* MOV (% rax) (% r8) *)
  0x48; 0x25; 0xff; 0x01; 0x00; 0x00;
                           (* AND (% rax) (Imm32 (word 511)) *)
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
  0x49; 0x0f; 0xac; 0xcf; 0x09;
                           (* SHRD (% r15) (% rcx) (Imm8 (word 9)) *)
  0x48; 0xc1; 0xe9; 0x09;  (* SHR (% rcx) (Imm8 (word 9)) *)
  0x48; 0x01; 0xc1;        (* ADD (% rcx) (% rax) *)
  0xf9;                    (* STCF *)
  0x4c; 0x13; 0x84; 0x24; 0xf8; 0x01; 0x00; 0x00;
                           (* ADC (% r8) (Memop Quadword (%% (rsp,504))) *)
  0x4c; 0x13; 0x8c; 0x24; 0x00; 0x02; 0x00; 0x00;
                           (* ADC (% r9) (Memop Quadword (%% (rsp,512))) *)
  0x4c; 0x13; 0x94; 0x24; 0x08; 0x02; 0x00; 0x00;
                           (* ADC (% r10) (Memop Quadword (%% (rsp,520))) *)
  0x4c; 0x13; 0x9c; 0x24; 0x10; 0x02; 0x00; 0x00;
                           (* ADC (% r11) (Memop Quadword (%% (rsp,528))) *)
  0x4c; 0x13; 0xa4; 0x24; 0x18; 0x02; 0x00; 0x00;
                           (* ADC (% r12) (Memop Quadword (%% (rsp,536))) *)
  0x4c; 0x13; 0xac; 0x24; 0x20; 0x02; 0x00; 0x00;
                           (* ADC (% r13) (Memop Quadword (%% (rsp,544))) *)
  0x4c; 0x13; 0xb4; 0x24; 0x28; 0x02; 0x00; 0x00;
                           (* ADC (% r14) (Memop Quadword (%% (rsp,552))) *)
  0x4c; 0x13; 0xbc; 0x24; 0x30; 0x02; 0x00; 0x00;
                           (* ADC (% r15) (Memop Quadword (%% (rsp,560))) *)
  0x48; 0x81; 0xd1; 0x00; 0xfe; 0xff; 0xff;
                           (* ADC (% rcx) (Imm32 (word 4294966784)) *)
  0xf5;                    (* CMC *)
  0x49; 0x83; 0xd8; 0x00;  (* SBB (% r8) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x84; 0x24; 0xb0; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,432))) (% r8) *)
  0x49; 0x83; 0xd9; 0x00;  (* SBB (% r9) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x8c; 0x24; 0xb8; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,440))) (% r9) *)
  0x49; 0x83; 0xda; 0x00;  (* SBB (% r10) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x94; 0x24; 0xc0; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,448))) (% r10) *)
  0x49; 0x83; 0xdb; 0x00;  (* SBB (% r11) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x9c; 0x24; 0xc8; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,456))) (% r11) *)
  0x49; 0x83; 0xdc; 0x00;  (* SBB (% r12) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xa4; 0x24; 0xd0; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,464))) (% r12) *)
  0x49; 0x83; 0xdd; 0x00;  (* SBB (% r13) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xac; 0x24; 0xd8; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,472))) (% r13) *)
  0x49; 0x83; 0xde; 0x00;  (* SBB (% r14) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xb4; 0x24; 0xe0; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,480))) (% r14) *)
  0x49; 0x83; 0xdf; 0x00;  (* SBB (% r15) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xbc; 0x24; 0xe8; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,488))) (% r15) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x48; 0x81; 0xe1; 0xff; 0x01; 0x00; 0x00;
                           (* AND (% rcx) (Imm32 (word 511)) *)
  0x48; 0x89; 0x8c; 0x24; 0xf0; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,496))) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x54; 0x24; 0x48;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,72))) *)
  0xc4; 0x62; 0xbb; 0xf6; 0x0e;
                           (* MULX4 (% r9,% r8) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x4c; 0x89; 0x84; 0x24; 0xf8; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,504))) (% r8) *)
  0xc4; 0x62; 0xe3; 0xf6; 0x56; 0x08;
                           (* MULX4 (% r10,% rbx) (% rdx,Memop Quadword (%% (rsi,8))) *)
  0x49; 0x11; 0xd9;        (* ADC (% r9) (% rbx) *)
  0xc4; 0x62; 0xe3; 0xf6; 0x5e; 0x10;
                           (* MULX4 (% r11,% rbx) (% rdx,Memop Quadword (%% (rsi,16))) *)
  0x49; 0x11; 0xda;        (* ADC (% r10) (% rbx) *)
  0xc4; 0x62; 0xe3; 0xf6; 0x66; 0x18;
                           (* MULX4 (% r12,% rbx) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0x49; 0x11; 0xdb;        (* ADC (% r11) (% rbx) *)
  0xc4; 0x62; 0xe3; 0xf6; 0x6e; 0x20;
                           (* MULX4 (% r13,% rbx) (% rdx,Memop Quadword (%% (rsi,32))) *)
  0x49; 0x11; 0xdc;        (* ADC (% r12) (% rbx) *)
  0xc4; 0x62; 0xe3; 0xf6; 0x76; 0x28;
                           (* MULX4 (% r14,% rbx) (% rdx,Memop Quadword (%% (rsi,40))) *)
  0x49; 0x11; 0xdd;        (* ADC (% r13) (% rbx) *)
  0xc4; 0x62; 0xe3; 0xf6; 0x7e; 0x30;
                           (* MULX4 (% r15,% rbx) (% rdx,Memop Quadword (%% (rsi,48))) *)
  0x49; 0x11; 0xde;        (* ADC (% r14) (% rbx) *)
  0xc4; 0x62; 0xe3; 0xf6; 0x46; 0x38;
                           (* MULX4 (% r8,% rbx) (% rdx,Memop Quadword (%% (rsi,56))) *)
  0x49; 0x11; 0xdf;        (* ADC (% r15) (% rbx) *)
  0x49; 0x11; 0xc8;        (* ADC (% r8) (% rcx) *)
  0x48; 0x8b; 0x54; 0x24; 0x50;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,80))) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1e;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0x4c; 0x89; 0x8c; 0x24; 0x00; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,512))) (% r9) *)
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
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc9;
                           (* ADOX (% r9) (% rcx) *)
  0x49; 0x11; 0xc9;        (* ADC (% r9) (% rcx) *)
  0x48; 0x8b; 0x54; 0x24; 0x58;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,88))) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1e;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0x4c; 0x89; 0x94; 0x24; 0x08; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,520))) (% r10) *)
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
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd1;
                           (* ADOX (% r10) (% rcx) *)
  0x49; 0x11; 0xca;        (* ADC (% r10) (% rcx) *)
  0x48; 0x8b; 0x54; 0x24; 0x60;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,96))) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1e;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0x4c; 0x89; 0x9c; 0x24; 0x10; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,528))) (% r11) *)
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
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd9;
                           (* ADOX (% r11) (% rcx) *)
  0x49; 0x11; 0xcb;        (* ADC (% r11) (% rcx) *)
  0x48; 0x8b; 0x54; 0x24; 0x68;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,104))) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1e;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0x4c; 0x89; 0xa4; 0x24; 0x18; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,536))) (% r12) *)
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
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe1;
                           (* ADOX (% r12) (% rcx) *)
  0x49; 0x11; 0xcc;        (* ADC (% r12) (% rcx) *)
  0x48; 0x8b; 0x54; 0x24; 0x70;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,112))) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1e;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0x4c; 0x89; 0xac; 0x24; 0x20; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,544))) (% r13) *)
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
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADOX (% r13) (% rcx) *)
  0x49; 0x11; 0xcd;        (* ADC (% r13) (% rcx) *)
  0x48; 0x8b; 0x54; 0x24; 0x78;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,120))) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1e;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0x4c; 0x89; 0xb4; 0x24; 0x28; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,552))) (% r14) *)
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
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADOX (% r14) (% rcx) *)
  0x49; 0x11; 0xce;        (* ADC (% r14) (% rcx) *)
  0x48; 0x8b; 0x94; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,128))) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1e;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0x4c; 0x89; 0xbc; 0x24; 0x30; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,560))) (% r15) *)
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
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADOX (% r15) (% rcx) *)
  0x49; 0x11; 0xcf;        (* ADC (% r15) (% rcx) *)
  0x48; 0x8b; 0x56; 0x40;  (* MOV (% rdx) (Memop Quadword (%% (rsi,64))) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x48;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,72))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x50;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,80))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x58;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,88))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
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
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x78;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,120))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,128))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xd9;
                           (* ADOX (% rbx) (% rcx) *)
  0x48; 0x11; 0xd9;        (* ADC (% rcx) (% rbx) *)
  0x48; 0x8b; 0x94; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,136))) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1e;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
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
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x38;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,56))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% rcx) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x40;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,64))) *)
  0x48; 0x11; 0xc1;        (* ADC (% rcx) (% rax) *)
  0x4c; 0x89; 0xc0;        (* MOV (% rax) (% r8) *)
  0x48; 0x25; 0xff; 0x01; 0x00; 0x00;
                           (* AND (% rax) (Imm32 (word 511)) *)
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
  0x49; 0x0f; 0xac; 0xcf; 0x09;
                           (* SHRD (% r15) (% rcx) (Imm8 (word 9)) *)
  0x48; 0xc1; 0xe9; 0x09;  (* SHR (% rcx) (Imm8 (word 9)) *)
  0x48; 0x01; 0xc1;        (* ADD (% rcx) (% rax) *)
  0x4c; 0x03; 0x84; 0x24; 0xf8; 0x01; 0x00; 0x00;
                           (* ADD (% r8) (Memop Quadword (%% (rsp,504))) *)
  0x4c; 0x89; 0x84; 0x24; 0xd8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,216))) (% r8) *)
  0x4c; 0x13; 0x8c; 0x24; 0x00; 0x02; 0x00; 0x00;
                           (* ADC (% r9) (Memop Quadword (%% (rsp,512))) *)
  0x4c; 0x89; 0x8c; 0x24; 0xe0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,224))) (% r9) *)
  0x4c; 0x13; 0x94; 0x24; 0x08; 0x02; 0x00; 0x00;
                           (* ADC (% r10) (Memop Quadword (%% (rsp,520))) *)
  0x4c; 0x89; 0x94; 0x24; 0xe8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,232))) (% r10) *)
  0x4c; 0x13; 0x9c; 0x24; 0x10; 0x02; 0x00; 0x00;
                           (* ADC (% r11) (Memop Quadword (%% (rsp,528))) *)
  0x4c; 0x89; 0x9c; 0x24; 0xf0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,240))) (% r11) *)
  0x4c; 0x13; 0xa4; 0x24; 0x18; 0x02; 0x00; 0x00;
                           (* ADC (% r12) (Memop Quadword (%% (rsp,536))) *)
  0x4c; 0x89; 0xa4; 0x24; 0xf8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,248))) (% r12) *)
  0x4c; 0x13; 0xac; 0x24; 0x20; 0x02; 0x00; 0x00;
                           (* ADC (% r13) (Memop Quadword (%% (rsp,544))) *)
  0x4c; 0x89; 0xac; 0x24; 0x00; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,256))) (% r13) *)
  0x4c; 0x13; 0xb4; 0x24; 0x28; 0x02; 0x00; 0x00;
                           (* ADC (% r14) (Memop Quadword (%% (rsp,552))) *)
  0x4c; 0x89; 0xb4; 0x24; 0x08; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,264))) (% r14) *)
  0x4c; 0x13; 0xbc; 0x24; 0x30; 0x02; 0x00; 0x00;
                           (* ADC (% r15) (Memop Quadword (%% (rsp,560))) *)
  0x4c; 0x89; 0xbc; 0x24; 0x10; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,272))) (% r15) *)
  0x48; 0x83; 0xd1; 0x00;  (* ADC (% rcx) (Imm8 (word 0)) *)
  0x48; 0x89; 0x8c; 0x24; 0x18; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,280))) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x94; 0x24; 0x68; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,360))) *)
  0xc4; 0xe2; 0xb3; 0xf6; 0x84; 0x24; 0x70; 0x01; 0x00; 0x00;
                           (* MULX4 (% rax,% r9) (% rdx,Memop Quadword (%% (rsp,368))) *)
  0x4c; 0x89; 0x8c; 0x24; 0x00; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,512))) (% r9) *)
  0xc4; 0xe2; 0xab; 0xf6; 0x9c; 0x24; 0x78; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% r10) (% rdx,Memop Quadword (%% (rsp,376))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0x4c; 0x89; 0x94; 0x24; 0x08; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,520))) (% r10) *)
  0xc4; 0xe2; 0xa3; 0xf6; 0x84; 0x24; 0x80; 0x01; 0x00; 0x00;
                           (* MULX4 (% rax,% r11) (% rdx,Memop Quadword (%% (rsp,384))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADCX (% r11) (% rbx) *)
  0xc4; 0xe2; 0x9b; 0xf6; 0x9c; 0x24; 0x88; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% r12) (% rdx,Memop Quadword (%% (rsp,392))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xc4; 0xe2; 0x93; 0xf6; 0x84; 0x24; 0x90; 0x01; 0x00; 0x00;
                           (* MULX4 (% rax,% r13) (% rdx,Memop Quadword (%% (rsp,400))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADCX (% r13) (% rbx) *)
  0xc4; 0xe2; 0x8b; 0xf6; 0x9c; 0x24; 0x98; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% r14) (% rdx,Memop Quadword (%% (rsp,408))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xc4; 0x62; 0x83; 0xf6; 0x84; 0x24; 0xa0; 0x01; 0x00; 0x00;
                           (* MULX4 (% r8,% r15) (% rdx,Memop Quadword (%% (rsp,416))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADCX (% r15) (% rbx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc1;
                           (* ADCX (% r8) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x94; 0x24; 0x70; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,368))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x78; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,376))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0x4c; 0x89; 0x9c; 0x24; 0x10; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,528))) (% r11) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x80; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,384))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0x4c; 0x89; 0xa4; 0x24; 0x18; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,536))) (% r12) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x88; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,392))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x90; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,400))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x98; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,408))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x8c; 0x24; 0xa0; 0x01; 0x00; 0x00;
                           (* MULX4 (% r9,% rax) (% rdx,Memop Quadword (%% (rsp,416))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc9;
                           (* ADOX (% r9) (% rcx) *)
  0x48; 0x8b; 0x94; 0x24; 0x88; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,392))) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x94; 0x24; 0x90; 0x01; 0x00; 0x00;
                           (* MULX4 (% r10,% rax) (% rdx,Memop Quadword (%% (rsp,400))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd1;
                           (* ADOX (% r10) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd1;
                           (* ADCX (% r10) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x94; 0x24; 0x78; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,376))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x80; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,384))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0x4c; 0x89; 0xac; 0x24; 0x20; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,544))) (% r13) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x88; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,392))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0x4c; 0x89; 0xb4; 0x24; 0x28; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,552))) (% r14) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x90; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,400))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x98; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,408))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xa0; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,416))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0x48; 0x8b; 0x94; 0x24; 0x98; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,408))) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x9c; 0x24; 0x88; 0x01; 0x00; 0x00;
                           (* MULX4 (% r11,% rax) (% rdx,Memop Quadword (%% (rsp,392))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd9;
                           (* ADOX (% r11) (% rcx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xa4; 0x24; 0x90; 0x01; 0x00; 0x00;
                           (* MULX4 (% r12,% rax) (% rdx,Memop Quadword (%% (rsp,400))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe1;
                           (* ADOX (% r12) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe1;
                           (* ADCX (% r12) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x94; 0x24; 0x80; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,384))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x88; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,392))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0x4c; 0x89; 0xbc; 0x24; 0x30; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,560))) (% r15) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x90; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,400))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x98; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,408))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xa0; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,416))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0x48; 0x8b; 0x94; 0x24; 0xa0; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,416))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x88; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,392))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xac; 0x24; 0x90; 0x01; 0x00; 0x00;
                           (* MULX4 (% r13,% rax) (% rdx,Memop Quadword (%% (rsp,400))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADOX (% r13) (% rcx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xb4; 0x24; 0x98; 0x01; 0x00; 0x00;
                           (* MULX4 (% r14,% rax) (% rdx,Memop Quadword (%% (rsp,408))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADOX (% r14) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADCX (% r14) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x94; 0x24; 0x68; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,360))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rax) (% rdx,% rdx) *)
  0x48; 0x89; 0x84; 0x24; 0xf8; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,504))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x00; 0x02; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,512))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% rax) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% rax) (% rbx) *)
  0x48; 0x89; 0x84; 0x24; 0x00; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,512))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x08; 0x02; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,520))) *)
  0x48; 0x8b; 0x94; 0x24; 0x70; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,368))) *)
  0xc4; 0xe2; 0xeb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rdx) (% rdx,% rdx) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% rax) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xc2;
                           (* ADOX (% rax) (% rdx) *)
  0x48; 0x89; 0x84; 0x24; 0x08; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,520))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x10; 0x02; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,528))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% rax) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% rax) (% rbx) *)
  0x48; 0x89; 0x84; 0x24; 0x10; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,528))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x18; 0x02; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,536))) *)
  0x48; 0x8b; 0x94; 0x24; 0x78; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,376))) *)
  0xc4; 0xe2; 0xeb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rdx) (% rdx,% rdx) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% rax) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xc2;
                           (* ADOX (% rax) (% rdx) *)
  0x48; 0x89; 0x84; 0x24; 0x18; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,536))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x20; 0x02; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,544))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% rax) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% rax) (% rbx) *)
  0x48; 0x89; 0x84; 0x24; 0x20; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,544))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x28; 0x02; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,552))) *)
  0x48; 0x8b; 0x94; 0x24; 0x80; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,384))) *)
  0xc4; 0xe2; 0xeb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rdx) (% rdx,% rdx) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% rax) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xc2;
                           (* ADOX (% rax) (% rdx) *)
  0x48; 0x89; 0x84; 0x24; 0x28; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,552))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x30; 0x02; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,560))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% rax) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% rax) (% rbx) *)
  0x48; 0x89; 0x84; 0x24; 0x30; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,560))) (% rax) *)
  0x48; 0x8b; 0x94; 0x24; 0x88; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,392))) *)
  0xc4; 0xe2; 0xeb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rdx) (% rdx,% rdx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% r8) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc2;
                           (* ADOX (% r8) (% rdx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xc9;
                           (* ADCX (% r9) (% r9) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0x48; 0x8b; 0x94; 0x24; 0x90; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,400))) *)
  0xc4; 0xe2; 0xeb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rdx) (% rdx,% rdx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xd2;
                           (* ADCX (% r10) (% r10) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd2;
                           (* ADOX (% r10) (% rdx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADCX (% r11) (% r11) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0x48; 0x8b; 0x94; 0x24; 0x98; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,408))) *)
  0xc4; 0xe2; 0xeb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rdx) (% rdx,% rdx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xe4;
                           (* ADCX (% r12) (% r12) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe2;
                           (* ADOX (% r12) (% rdx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xed;
                           (* ADCX (% r13) (% r13) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0x48; 0x8b; 0x94; 0x24; 0xa0; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,416))) *)
  0xc4; 0x62; 0xeb; 0xf6; 0xfa;
                           (* MULX4 (% r15,% rdx) (% rdx,% rdx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xf6;
                           (* ADCX (% r14) (% r14) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf2;
                           (* ADOX (% r14) (% rdx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADCX (% r15) (% rcx) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADOX (% r15) (% rcx) *)
  0x48; 0x8b; 0x94; 0x24; 0xa8; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,424))) *)
  0x48; 0x89; 0xd1;        (* MOV (% rcx) (% rdx) *)
  0x48; 0x0f; 0xaf; 0xc9;  (* IMUL (% rcx) (% rcx) *)
  0x48; 0x01; 0xd2;        (* ADD (% rdx) (% rdx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x68; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,360))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x70; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,368))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x78; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,376))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x80; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,384))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x88; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,392))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x90; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,400))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x98; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,408))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xa0; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,416))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% rcx) (% rbx) *)
  0x48; 0x83; 0xd1; 0x00;  (* ADC (% rcx) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xc0;        (* MOV (% rax) (% r8) *)
  0x48; 0x25; 0xff; 0x01; 0x00; 0x00;
                           (* AND (% rax) (Imm32 (word 511)) *)
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
  0x49; 0x0f; 0xac; 0xcf; 0x09;
                           (* SHRD (% r15) (% rcx) (Imm8 (word 9)) *)
  0x48; 0xc1; 0xe9; 0x09;  (* SHR (% rcx) (Imm8 (word 9)) *)
  0x48; 0x01; 0xc1;        (* ADD (% rcx) (% rax) *)
  0xf9;                    (* STCF *)
  0x4c; 0x13; 0x84; 0x24; 0xf8; 0x01; 0x00; 0x00;
                           (* ADC (% r8) (Memop Quadword (%% (rsp,504))) *)
  0x4c; 0x13; 0x8c; 0x24; 0x00; 0x02; 0x00; 0x00;
                           (* ADC (% r9) (Memop Quadword (%% (rsp,512))) *)
  0x4c; 0x13; 0x94; 0x24; 0x08; 0x02; 0x00; 0x00;
                           (* ADC (% r10) (Memop Quadword (%% (rsp,520))) *)
  0x4c; 0x13; 0x9c; 0x24; 0x10; 0x02; 0x00; 0x00;
                           (* ADC (% r11) (Memop Quadword (%% (rsp,528))) *)
  0x4c; 0x13; 0xa4; 0x24; 0x18; 0x02; 0x00; 0x00;
                           (* ADC (% r12) (Memop Quadword (%% (rsp,536))) *)
  0x4c; 0x13; 0xac; 0x24; 0x20; 0x02; 0x00; 0x00;
                           (* ADC (% r13) (Memop Quadword (%% (rsp,544))) *)
  0x4c; 0x13; 0xb4; 0x24; 0x28; 0x02; 0x00; 0x00;
                           (* ADC (% r14) (Memop Quadword (%% (rsp,552))) *)
  0x4c; 0x13; 0xbc; 0x24; 0x30; 0x02; 0x00; 0x00;
                           (* ADC (% r15) (Memop Quadword (%% (rsp,560))) *)
  0x48; 0x81; 0xd1; 0x00; 0xfe; 0xff; 0xff;
                           (* ADC (% rcx) (Imm32 (word 4294966784)) *)
  0xf5;                    (* CMC *)
  0x49; 0x83; 0xd8; 0x00;  (* SBB (% r8) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x84; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,288))) (% r8) *)
  0x49; 0x83; 0xd9; 0x00;  (* SBB (% r9) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x8c; 0x24; 0x28; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,296))) (% r9) *)
  0x49; 0x83; 0xda; 0x00;  (* SBB (% r10) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x94; 0x24; 0x30; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,304))) (% r10) *)
  0x49; 0x83; 0xdb; 0x00;  (* SBB (% r11) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x9c; 0x24; 0x38; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,312))) (% r11) *)
  0x49; 0x83; 0xdc; 0x00;  (* SBB (% r12) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xa4; 0x24; 0x40; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,320))) (% r12) *)
  0x49; 0x83; 0xdd; 0x00;  (* SBB (% r13) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xac; 0x24; 0x48; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,328))) (% r13) *)
  0x49; 0x83; 0xde; 0x00;  (* SBB (% r14) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xb4; 0x24; 0x50; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,336))) (% r14) *)
  0x49; 0x83; 0xdf; 0x00;  (* SBB (% r15) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xbc; 0x24; 0x58; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,344))) (% r15) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x48; 0x81; 0xe1; 0xff; 0x01; 0x00; 0x00;
                           (* AND (% rcx) (Imm32 (word 511)) *)
  0x48; 0x89; 0x8c; 0x24; 0x60; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,352))) (% rcx) *)
  0x48; 0xc7; 0xc2; 0x09; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Imm32 (word 9)) *)
  0x48; 0x8b; 0x9c; 0x24; 0xf0; 0x01; 0x00; 0x00;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,496))) *)
  0x48; 0x81; 0xf3; 0xff; 0x01; 0x00; 0x00;
                           (* XOR (% rbx) (Imm32 (word 511)) *)
  0x48; 0x8b; 0x84; 0x24; 0xb0; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,432))) *)
  0x48; 0xf7; 0xd0;        (* NOT (% rax) *)
  0xc4; 0x62; 0xbb; 0xf6; 0xc8;
                           (* MULX4 (% r9,% r8) (% rdx,% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0xb8; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,440))) *)
  0x48; 0xf7; 0xd0;        (* NOT (% rax) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xd0;
                           (* MULX4 (% r10,% rax) (% rdx,% rax) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0xc0; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,448))) *)
  0x48; 0xf7; 0xd0;        (* NOT (% rax) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xd8;
                           (* MULX4 (% r11,% rax) (% rdx,% rax) *)
  0x49; 0x11; 0xc2;        (* ADC (% r10) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0xc8; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,456))) *)
  0x48; 0xf7; 0xd0;        (* NOT (% rax) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xe0;
                           (* MULX4 (% r12,% rax) (% rdx,% rax) *)
  0x49; 0x11; 0xc3;        (* ADC (% r11) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0xd0; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,464))) *)
  0x48; 0xf7; 0xd0;        (* NOT (% rax) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xe8;
                           (* MULX4 (% r13,% rax) (% rdx,% rax) *)
  0x49; 0x11; 0xc4;        (* ADC (% r12) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0xd8; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,472))) *)
  0x48; 0xf7; 0xd0;        (* NOT (% rax) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xf0;
                           (* MULX4 (% r14,% rax) (% rdx,% rax) *)
  0x49; 0x11; 0xc5;        (* ADC (% r13) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0xe0; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,480))) *)
  0x48; 0xf7; 0xd0;        (* NOT (% rax) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xf8;
                           (* MULX4 (% r15,% rax) (% rdx,% rax) *)
  0x49; 0x11; 0xc6;        (* ADC (% r14) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0xe8; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,488))) *)
  0x48; 0xf7; 0xd0;        (* NOT (% rax) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0xc8;
                           (* MULX4 (% rcx,% rax) (% rdx,% rax) *)
  0x49; 0x11; 0xc7;        (* ADC (% r15) (% rax) *)
  0xc4; 0xe2; 0xe3; 0xf6; 0xc3;
                           (* MULX4 (% rax,% rbx) (% rdx,% rbx) *)
  0x48; 0x11; 0xcb;        (* ADC (% rbx) (% rcx) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0x48; 0xc7; 0xc2; 0x0c; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Imm32 (word 12)) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x8c; 0x24; 0xd8; 0x00; 0x00; 0x00;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsp,216))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc9;
                           (* ADOX (% r9) (% rcx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x8c; 0x24; 0xe0; 0x00; 0x00; 0x00;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsp,224))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd1;
                           (* ADOX (% r10) (% rcx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x8c; 0x24; 0xe8; 0x00; 0x00; 0x00;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsp,232))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd9;
                           (* ADOX (% r11) (% rcx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x8c; 0x24; 0xf0; 0x00; 0x00; 0x00;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsp,240))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe1;
                           (* ADOX (% r12) (% rcx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x8c; 0x24; 0xf8; 0x00; 0x00; 0x00;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsp,248))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADOX (% r13) (% rcx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x8c; 0x24; 0x00; 0x01; 0x00; 0x00;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsp,256))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADOX (% r14) (% rcx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x8c; 0x24; 0x08; 0x01; 0x00; 0x00;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsp,264))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADOX (% r15) (% rcx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x8c; 0x24; 0x10; 0x01; 0x00; 0x00;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsp,272))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xd9;
                           (* ADOX (% rbx) (% rcx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x8c; 0x24; 0x18; 0x01; 0x00; 0x00;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsp,280))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% rbx) (% rax) *)
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
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x54; 0x24; 0x48;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,72))) *)
  0xc4; 0xe2; 0xb3; 0xf6; 0x44; 0x24; 0x50;
                           (* MULX4 (% rax,% r9) (% rdx,Memop Quadword (%% (rsp,80))) *)
  0x4c; 0x89; 0x8c; 0x24; 0x00; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,512))) (% r9) *)
  0xc4; 0xe2; 0xab; 0xf6; 0x5c; 0x24; 0x58;
                           (* MULX4 (% rbx,% r10) (% rdx,Memop Quadword (%% (rsp,88))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0x4c; 0x89; 0x94; 0x24; 0x08; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,520))) (% r10) *)
  0xc4; 0xe2; 0xa3; 0xf6; 0x44; 0x24; 0x60;
                           (* MULX4 (% rax,% r11) (% rdx,Memop Quadword (%% (rsp,96))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADCX (% r11) (% rbx) *)
  0xc4; 0xe2; 0x9b; 0xf6; 0x5c; 0x24; 0x68;
                           (* MULX4 (% rbx,% r12) (% rdx,Memop Quadword (%% (rsp,104))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xc4; 0xe2; 0x93; 0xf6; 0x44; 0x24; 0x70;
                           (* MULX4 (% rax,% r13) (% rdx,Memop Quadword (%% (rsp,112))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADCX (% r13) (% rbx) *)
  0xc4; 0xe2; 0x8b; 0xf6; 0x5c; 0x24; 0x78;
                           (* MULX4 (% rbx,% r14) (% rdx,Memop Quadword (%% (rsp,120))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xc4; 0x62; 0x83; 0xf6; 0x84; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MULX4 (% r8,% r15) (% rdx,Memop Quadword (%% (rsp,128))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADCX (% r15) (% rbx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc1;
                           (* ADCX (% r8) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x54; 0x24; 0x50;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,80))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x58;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,88))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0x4c; 0x89; 0x9c; 0x24; 0x10; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,528))) (% r11) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x60;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,96))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0x4c; 0x89; 0xa4; 0x24; 0x18; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,536))) (% r12) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x68;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,104))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x70;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,112))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x78;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,120))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x8c; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MULX4 (% r9,% rax) (% rdx,Memop Quadword (%% (rsp,128))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc9;
                           (* ADOX (% r9) (% rcx) *)
  0x48; 0x8b; 0x54; 0x24; 0x68;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,104))) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x54; 0x24; 0x70;
                           (* MULX4 (% r10,% rax) (% rdx,Memop Quadword (%% (rsp,112))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd1;
                           (* ADOX (% r10) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd1;
                           (* ADCX (% r10) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x54; 0x24; 0x58;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,88))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x60;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,96))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0x4c; 0x89; 0xac; 0x24; 0x20; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,544))) (% r13) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x68;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,104))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0x4c; 0x89; 0xb4; 0x24; 0x28; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,552))) (% r14) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x70;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,112))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x78;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,120))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,128))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0x48; 0x8b; 0x54; 0x24; 0x78;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,120))) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x5c; 0x24; 0x68;
                           (* MULX4 (% r11,% rax) (% rdx,Memop Quadword (%% (rsp,104))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd9;
                           (* ADOX (% r11) (% rcx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x64; 0x24; 0x70;
                           (* MULX4 (% r12,% rax) (% rdx,Memop Quadword (%% (rsp,112))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe1;
                           (* ADOX (% r12) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe1;
                           (* ADCX (% r12) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x54; 0x24; 0x60;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,96))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x68;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,104))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0x4c; 0x89; 0xbc; 0x24; 0x30; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,560))) (% r15) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x70;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,112))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x78;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,120))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,128))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0x48; 0x8b; 0x94; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,128))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x68;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,104))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x6c; 0x24; 0x70;
                           (* MULX4 (% r13,% rax) (% rdx,Memop Quadword (%% (rsp,112))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADOX (% r13) (% rcx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x74; 0x24; 0x78;
                           (* MULX4 (% r14,% rax) (% rdx,Memop Quadword (%% (rsp,120))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADOX (% r14) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADCX (% r14) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x54; 0x24; 0x48;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,72))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rax) (% rdx,% rdx) *)
  0x48; 0x89; 0x84; 0x24; 0xf8; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,504))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x00; 0x02; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,512))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% rax) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% rax) (% rbx) *)
  0x48; 0x89; 0x84; 0x24; 0x00; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,512))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x08; 0x02; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,520))) *)
  0x48; 0x8b; 0x54; 0x24; 0x50;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,80))) *)
  0xc4; 0xe2; 0xeb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rdx) (% rdx,% rdx) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% rax) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xc2;
                           (* ADOX (% rax) (% rdx) *)
  0x48; 0x89; 0x84; 0x24; 0x08; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,520))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x10; 0x02; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,528))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% rax) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% rax) (% rbx) *)
  0x48; 0x89; 0x84; 0x24; 0x10; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,528))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x18; 0x02; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,536))) *)
  0x48; 0x8b; 0x54; 0x24; 0x58;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,88))) *)
  0xc4; 0xe2; 0xeb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rdx) (% rdx,% rdx) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% rax) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xc2;
                           (* ADOX (% rax) (% rdx) *)
  0x48; 0x89; 0x84; 0x24; 0x18; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,536))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x20; 0x02; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,544))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% rax) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% rax) (% rbx) *)
  0x48; 0x89; 0x84; 0x24; 0x20; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,544))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x28; 0x02; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,552))) *)
  0x48; 0x8b; 0x54; 0x24; 0x60;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,96))) *)
  0xc4; 0xe2; 0xeb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rdx) (% rdx,% rdx) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% rax) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xc2;
                           (* ADOX (% rax) (% rdx) *)
  0x48; 0x89; 0x84; 0x24; 0x28; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,552))) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0x30; 0x02; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,560))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% rax) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% rax) (% rbx) *)
  0x48; 0x89; 0x84; 0x24; 0x30; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,560))) (% rax) *)
  0x48; 0x8b; 0x54; 0x24; 0x68;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,104))) *)
  0xc4; 0xe2; 0xeb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rdx) (% rdx,% rdx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% r8) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc2;
                           (* ADOX (% r8) (% rdx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xc9;
                           (* ADCX (% r9) (% r9) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0x48; 0x8b; 0x54; 0x24; 0x70;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,112))) *)
  0xc4; 0xe2; 0xeb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rdx) (% rdx,% rdx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xd2;
                           (* ADCX (% r10) (% r10) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd2;
                           (* ADOX (% r10) (% rdx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADCX (% r11) (% r11) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0x48; 0x8b; 0x54; 0x24; 0x78;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,120))) *)
  0xc4; 0xe2; 0xeb; 0xf6; 0xda;
                           (* MULX4 (% rbx,% rdx) (% rdx,% rdx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xe4;
                           (* ADCX (% r12) (% r12) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe2;
                           (* ADOX (% r12) (% rdx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xed;
                           (* ADCX (% r13) (% r13) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0x48; 0x8b; 0x94; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,128))) *)
  0xc4; 0x62; 0xeb; 0xf6; 0xfa;
                           (* MULX4 (% r15,% rdx) (% rdx,% rdx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xf6;
                           (* ADCX (% r14) (% r14) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf2;
                           (* ADOX (% r14) (% rdx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADCX (% r15) (% rcx) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADOX (% r15) (% rcx) *)
  0x48; 0x8b; 0x94; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,136))) *)
  0x48; 0x89; 0xd1;        (* MOV (% rcx) (% rdx) *)
  0x48; 0x0f; 0xaf; 0xc9;  (* IMUL (% rcx) (% rcx) *)
  0x48; 0x01; 0xd2;        (* ADD (% rdx) (% rdx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x48;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,72))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x50;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,80))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x58;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,88))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
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
  0xc4; 0xe2; 0xfb; 0xf6; 0x5c; 0x24; 0x78;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,120))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,128))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% rcx) (% rbx) *)
  0x48; 0x83; 0xd1; 0x00;  (* ADC (% rcx) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xc0;        (* MOV (% rax) (% r8) *)
  0x48; 0x25; 0xff; 0x01; 0x00; 0x00;
                           (* AND (% rax) (Imm32 (word 511)) *)
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
  0x49; 0x0f; 0xac; 0xcf; 0x09;
                           (* SHRD (% r15) (% rcx) (Imm8 (word 9)) *)
  0x48; 0xc1; 0xe9; 0x09;  (* SHR (% rcx) (Imm8 (word 9)) *)
  0x48; 0x01; 0xc1;        (* ADD (% rcx) (% rax) *)
  0xf9;                    (* STCF *)
  0x4c; 0x13; 0x84; 0x24; 0xf8; 0x01; 0x00; 0x00;
                           (* ADC (% r8) (Memop Quadword (%% (rsp,504))) *)
  0x4c; 0x13; 0x8c; 0x24; 0x00; 0x02; 0x00; 0x00;
                           (* ADC (% r9) (Memop Quadword (%% (rsp,512))) *)
  0x4c; 0x13; 0x94; 0x24; 0x08; 0x02; 0x00; 0x00;
                           (* ADC (% r10) (Memop Quadword (%% (rsp,520))) *)
  0x4c; 0x13; 0x9c; 0x24; 0x10; 0x02; 0x00; 0x00;
                           (* ADC (% r11) (Memop Quadword (%% (rsp,528))) *)
  0x4c; 0x13; 0xa4; 0x24; 0x18; 0x02; 0x00; 0x00;
                           (* ADC (% r12) (Memop Quadword (%% (rsp,536))) *)
  0x4c; 0x13; 0xac; 0x24; 0x20; 0x02; 0x00; 0x00;
                           (* ADC (% r13) (Memop Quadword (%% (rsp,544))) *)
  0x4c; 0x13; 0xb4; 0x24; 0x28; 0x02; 0x00; 0x00;
                           (* ADC (% r14) (Memop Quadword (%% (rsp,552))) *)
  0x4c; 0x13; 0xbc; 0x24; 0x30; 0x02; 0x00; 0x00;
                           (* ADC (% r15) (Memop Quadword (%% (rsp,560))) *)
  0x48; 0x81; 0xd1; 0x00; 0xfe; 0xff; 0xff;
                           (* ADC (% rcx) (Imm32 (word 4294966784)) *)
  0xf5;                    (* CMC *)
  0x49; 0x83; 0xd8; 0x00;  (* SBB (% r8) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x84; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,288))) (% r8) *)
  0x49; 0x83; 0xd9; 0x00;  (* SBB (% r9) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x8c; 0x24; 0x28; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,296))) (% r9) *)
  0x49; 0x83; 0xda; 0x00;  (* SBB (% r10) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x94; 0x24; 0x30; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,304))) (% r10) *)
  0x49; 0x83; 0xdb; 0x00;  (* SBB (% r11) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x9c; 0x24; 0x38; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,312))) (% r11) *)
  0x49; 0x83; 0xdc; 0x00;  (* SBB (% r12) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xa4; 0x24; 0x40; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,320))) (% r12) *)
  0x49; 0x83; 0xdd; 0x00;  (* SBB (% r13) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xac; 0x24; 0x48; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,328))) (% r13) *)
  0x49; 0x83; 0xde; 0x00;  (* SBB (% r14) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xb4; 0x24; 0x50; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,336))) (% r14) *)
  0x49; 0x83; 0xdf; 0x00;  (* SBB (% r15) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xbc; 0x24; 0x58; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,344))) (% r15) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x48; 0x81; 0xe1; 0xff; 0x01; 0x00; 0x00;
                           (* AND (% rcx) (Imm32 (word 511)) *)
  0x48; 0x89; 0x8c; 0x24; 0x60; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,352))) (% rcx) *)
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
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x94; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,144))) *)
  0xc4; 0x62; 0xbb; 0xf6; 0x8c; 0x24; 0xb0; 0x01; 0x00; 0x00;
                           (* MULX4 (% r9,% r8) (% rdx,Memop Quadword (%% (rsp,432))) *)
  0x4c; 0x89; 0x84; 0x24; 0xf8; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,504))) (% r8) *)
  0xc4; 0x62; 0xe3; 0xf6; 0x94; 0x24; 0xb8; 0x01; 0x00; 0x00;
                           (* MULX4 (% r10,% rbx) (% rdx,Memop Quadword (%% (rsp,440))) *)
  0x49; 0x11; 0xd9;        (* ADC (% r9) (% rbx) *)
  0xc4; 0x62; 0xe3; 0xf6; 0x9c; 0x24; 0xc0; 0x01; 0x00; 0x00;
                           (* MULX4 (% r11,% rbx) (% rdx,Memop Quadword (%% (rsp,448))) *)
  0x49; 0x11; 0xda;        (* ADC (% r10) (% rbx) *)
  0xc4; 0x62; 0xe3; 0xf6; 0xa4; 0x24; 0xc8; 0x01; 0x00; 0x00;
                           (* MULX4 (% r12,% rbx) (% rdx,Memop Quadword (%% (rsp,456))) *)
  0x49; 0x11; 0xdb;        (* ADC (% r11) (% rbx) *)
  0xc4; 0x62; 0xe3; 0xf6; 0xac; 0x24; 0xd0; 0x01; 0x00; 0x00;
                           (* MULX4 (% r13,% rbx) (% rdx,Memop Quadword (%% (rsp,464))) *)
  0x49; 0x11; 0xdc;        (* ADC (% r12) (% rbx) *)
  0xc4; 0x62; 0xe3; 0xf6; 0xb4; 0x24; 0xd8; 0x01; 0x00; 0x00;
                           (* MULX4 (% r14,% rbx) (% rdx,Memop Quadword (%% (rsp,472))) *)
  0x49; 0x11; 0xdd;        (* ADC (% r13) (% rbx) *)
  0xc4; 0x62; 0xe3; 0xf6; 0xbc; 0x24; 0xe0; 0x01; 0x00; 0x00;
                           (* MULX4 (% r15,% rbx) (% rdx,Memop Quadword (%% (rsp,480))) *)
  0x49; 0x11; 0xde;        (* ADC (% r14) (% rbx) *)
  0xc4; 0x62; 0xe3; 0xf6; 0x84; 0x24; 0xe8; 0x01; 0x00; 0x00;
                           (* MULX4 (% r8,% rbx) (% rdx,Memop Quadword (%% (rsp,488))) *)
  0x49; 0x11; 0xdf;        (* ADC (% r15) (% rbx) *)
  0x49; 0x11; 0xc8;        (* ADC (% r8) (% rcx) *)
  0x48; 0x8b; 0x94; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,152))) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xb0; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,432))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0x4c; 0x89; 0x8c; 0x24; 0x00; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,512))) (% r9) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xb8; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,440))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xc0; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,448))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xc8; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,456))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xd0; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,464))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xd8; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,472))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xe0; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,480))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x8c; 0x24; 0xe8; 0x01; 0x00; 0x00;
                           (* MULX4 (% r9,% rax) (% rdx,Memop Quadword (%% (rsp,488))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc9;
                           (* ADOX (% r9) (% rcx) *)
  0x49; 0x11; 0xc9;        (* ADC (% r9) (% rcx) *)
  0x48; 0x8b; 0x94; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,160))) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xb0; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,432))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0x4c; 0x89; 0x94; 0x24; 0x08; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,520))) (% r10) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xb8; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,440))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xc0; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,448))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xc8; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,456))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xd0; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,464))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xd8; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,472))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xe0; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,480))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x94; 0x24; 0xe8; 0x01; 0x00; 0x00;
                           (* MULX4 (% r10,% rax) (% rdx,Memop Quadword (%% (rsp,488))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd1;
                           (* ADOX (% r10) (% rcx) *)
  0x49; 0x11; 0xca;        (* ADC (% r10) (% rcx) *)
  0x48; 0x8b; 0x94; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,168))) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xb0; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,432))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0x4c; 0x89; 0x9c; 0x24; 0x10; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,528))) (% r11) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xb8; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,440))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xc0; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,448))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xc8; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,456))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xd0; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,464))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xd8; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,472))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xe0; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,480))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x9c; 0x24; 0xe8; 0x01; 0x00; 0x00;
                           (* MULX4 (% r11,% rax) (% rdx,Memop Quadword (%% (rsp,488))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd9;
                           (* ADOX (% r11) (% rcx) *)
  0x49; 0x11; 0xcb;        (* ADC (% r11) (% rcx) *)
  0x48; 0x8b; 0x94; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,176))) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xb0; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,432))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0x4c; 0x89; 0xa4; 0x24; 0x18; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,536))) (% r12) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xb8; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,440))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xc0; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,448))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xc8; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,456))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xd0; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,464))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xd8; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,472))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xe0; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,480))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xa4; 0x24; 0xe8; 0x01; 0x00; 0x00;
                           (* MULX4 (% r12,% rax) (% rdx,Memop Quadword (%% (rsp,488))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe1;
                           (* ADOX (% r12) (% rcx) *)
  0x49; 0x11; 0xcc;        (* ADC (% r12) (% rcx) *)
  0x48; 0x8b; 0x94; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,184))) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xb0; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,432))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0x4c; 0x89; 0xac; 0x24; 0x20; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,544))) (% r13) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xb8; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,440))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xc0; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,448))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xc8; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,456))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xd0; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,464))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xd8; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,472))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xe0; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,480))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xac; 0x24; 0xe8; 0x01; 0x00; 0x00;
                           (* MULX4 (% r13,% rax) (% rdx,Memop Quadword (%% (rsp,488))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADOX (% r13) (% rcx) *)
  0x49; 0x11; 0xcd;        (* ADC (% r13) (% rcx) *)
  0x48; 0x8b; 0x94; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,192))) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xb0; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,432))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0x4c; 0x89; 0xb4; 0x24; 0x28; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,552))) (% r14) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xb8; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,440))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xc0; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,448))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xc8; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,456))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xd0; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,464))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xd8; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,472))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xe0; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,480))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xb4; 0x24; 0xe8; 0x01; 0x00; 0x00;
                           (* MULX4 (% r14,% rax) (% rdx,Memop Quadword (%% (rsp,488))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADOX (% r14) (% rcx) *)
  0x49; 0x11; 0xce;        (* ADC (% r14) (% rcx) *)
  0x48; 0x8b; 0x94; 0x24; 0xc8; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,200))) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xb0; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,432))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0x4c; 0x89; 0xbc; 0x24; 0x30; 0x02; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,560))) (% r15) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xb8; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,440))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xc0; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,448))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xc8; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,456))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xd0; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,464))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xd8; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,472))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xe0; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,480))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xbc; 0x24; 0xe8; 0x01; 0x00; 0x00;
                           (* MULX4 (% r15,% rax) (% rdx,Memop Quadword (%% (rsp,488))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADOX (% r15) (% rcx) *)
  0x49; 0x11; 0xcf;        (* ADC (% r15) (% rcx) *)
  0x48; 0x8b; 0x94; 0x24; 0xf0; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,496))) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,144))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,152))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
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
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,184))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,192))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xc8; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,200))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xd9;
                           (* ADOX (% rbx) (% rcx) *)
  0x48; 0x11; 0xd9;        (* ADC (% rcx) (% rbx) *)
  0x48; 0x8b; 0x94; 0x24; 0xd0; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,208))) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xb0; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,432))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xb8; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,440))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xc0; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,448))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xc8; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,456))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xd0; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,464))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xd8; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,472))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xe0; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,480))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xe8; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,488))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% rcx) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xf0; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,496))) *)
  0x48; 0x11; 0xc1;        (* ADC (% rcx) (% rax) *)
  0x4c; 0x89; 0xc0;        (* MOV (% rax) (% r8) *)
  0x48; 0x25; 0xff; 0x01; 0x00; 0x00;
                           (* AND (% rax) (Imm32 (word 511)) *)
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
  0x49; 0x0f; 0xac; 0xcf; 0x09;
                           (* SHRD (% r15) (% rcx) (Imm8 (word 9)) *)
  0x48; 0xc1; 0xe9; 0x09;  (* SHR (% rcx) (Imm8 (word 9)) *)
  0x48; 0x01; 0xc1;        (* ADD (% rcx) (% rax) *)
  0x4c; 0x03; 0x84; 0x24; 0xf8; 0x01; 0x00; 0x00;
                           (* ADD (% r8) (Memop Quadword (%% (rsp,504))) *)
  0x4c; 0x89; 0x84; 0x24; 0x68; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,360))) (% r8) *)
  0x4c; 0x13; 0x8c; 0x24; 0x00; 0x02; 0x00; 0x00;
                           (* ADC (% r9) (Memop Quadword (%% (rsp,512))) *)
  0x4c; 0x89; 0x8c; 0x24; 0x70; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,368))) (% r9) *)
  0x4c; 0x13; 0x94; 0x24; 0x08; 0x02; 0x00; 0x00;
                           (* ADC (% r10) (Memop Quadword (%% (rsp,520))) *)
  0x4c; 0x89; 0x94; 0x24; 0x78; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,376))) (% r10) *)
  0x4c; 0x13; 0x9c; 0x24; 0x10; 0x02; 0x00; 0x00;
                           (* ADC (% r11) (Memop Quadword (%% (rsp,528))) *)
  0x4c; 0x89; 0x9c; 0x24; 0x80; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,384))) (% r11) *)
  0x4c; 0x13; 0xa4; 0x24; 0x18; 0x02; 0x00; 0x00;
                           (* ADC (% r12) (Memop Quadword (%% (rsp,536))) *)
  0x4c; 0x89; 0xa4; 0x24; 0x88; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,392))) (% r12) *)
  0x4c; 0x13; 0xac; 0x24; 0x20; 0x02; 0x00; 0x00;
                           (* ADC (% r13) (Memop Quadword (%% (rsp,544))) *)
  0x4c; 0x89; 0xac; 0x24; 0x90; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,400))) (% r13) *)
  0x4c; 0x13; 0xb4; 0x24; 0x28; 0x02; 0x00; 0x00;
                           (* ADC (% r14) (Memop Quadword (%% (rsp,552))) *)
  0x4c; 0x89; 0xb4; 0x24; 0x98; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,408))) (% r14) *)
  0x4c; 0x13; 0xbc; 0x24; 0x30; 0x02; 0x00; 0x00;
                           (* ADC (% r15) (Memop Quadword (%% (rsp,560))) *)
  0x4c; 0x89; 0xbc; 0x24; 0xa0; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,416))) (% r15) *)
  0x48; 0x83; 0xd1; 0x00;  (* ADC (% rcx) (Imm8 (word 0)) *)
  0x48; 0x89; 0x8c; 0x24; 0xa8; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,424))) (% rcx) *)
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
  0x48; 0xc7; 0xc2; 0x03; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Imm32 (word 3)) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x8c; 0x24; 0x68; 0x01; 0x00; 0x00;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsp,360))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc9;
                           (* ADOX (% r9) (% rcx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x8c; 0x24; 0x70; 0x01; 0x00; 0x00;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsp,368))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd1;
                           (* ADOX (% r10) (% rcx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x8c; 0x24; 0x78; 0x01; 0x00; 0x00;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsp,376))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd9;
                           (* ADOX (% r11) (% rcx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x8c; 0x24; 0x80; 0x01; 0x00; 0x00;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsp,384))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe1;
                           (* ADOX (% r12) (% rcx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x8c; 0x24; 0x88; 0x01; 0x00; 0x00;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsp,392))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADOX (% r13) (% rcx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x8c; 0x24; 0x90; 0x01; 0x00; 0x00;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsp,400))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADOX (% r14) (% rcx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x8c; 0x24; 0x98; 0x01; 0x00; 0x00;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsp,408))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADOX (% r15) (% rcx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x8c; 0x24; 0xa0; 0x01; 0x00; 0x00;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsp,416))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xd9;
                           (* ADOX (% rbx) (% rcx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x8c; 0x24; 0xa8; 0x01; 0x00; 0x00;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsp,424))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% rbx) (% rax) *)
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
  0x48; 0x81; 0xc4; 0x38; 0x02; 0x00; 0x00;
                           (* ADD (% rsp) (Imm32 (word 568)) *)
  0x41; 0x5f;              (* POP (% r15) *)
  0x41; 0x5e;              (* POP (% r14) *)
  0x41; 0x5d;              (* POP (% r13) *)
  0x41; 0x5c;              (* POP (% r12) *)
  0x5b;                    (* POP (% rbx) *)
  0xc3                     (* RET *)
];;

let p521_jdouble_tmc = define_trimmed "p521_jdouble_tmc" p521_jdouble_mc;;

let P521_JDOUBLE_EXEC = X86_MK_CORE_EXEC_RULE p521_jdouble_tmc;;

(* ------------------------------------------------------------------------- *)
(* Common supporting definitions and lemmas for component proofs.            *)
(* ------------------------------------------------------------------------- *)

let lvs =
 ["x_1",[`RSI`;`0`];
  "y_1",[`RSI`;`72`];
  "z_1",[`RSI`;`144`];
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

let DESUM_RULE' = cache DESUM_RULE and DECARRY_RULE' = cache DECARRY_RULE;;

(* ------------------------------------------------------------------------- *)
(* Instances of sqr.                                                         *)
(* ------------------------------------------------------------------------- *)

let LOCAL_SQR_P521_TAC =
  X86_MACRO_SIM_ABBREV_TAC (X86_TRIM_EXEC_RULE p521_jdouble_tmc) 231 lvs
  `!(t:x86state) pcin pcout p3 n3 p1 n1.
    !n. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 9)) t = n
    ==>
    nonoverlapping (word pc,0x3ded) (stackpointer,568) /\
    nonoverlapping (read RDI t,216) (stackpointer,568) /\
    nonoverlapping (read RSI t,216) (stackpointer,568) /\
    nonoverlapping (word pc,0x3ded) (read RDI t,216)
    ==> ensures x86
         (\s. bytes_loaded s (word pc) (BUTLAST p521_jdouble_tmc) /\
              read RIP s = pcin /\
              read RSP s = read RSP t /\
              read RDI s = read RDI t /\
              read RSI s = read RSI t /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 9)) s =
              n)
             (\s. read RIP s = pcout /\
                  (n < p_521
                   ==> read(memory :> bytes(word_add (read p3 t) (word n3),
                       8 * 9)) s = (n EXP 2) MOD p_521))
           (MAYCHANGE [RIP; RAX; RBX; RDX; RCX;
                       R8; R9; R10; R11; R12; R13; R14; R15] ,,
            MAYCHANGE
             [memory :> bytes(word_add (read p3 t) (word n3),8 * 9);
              memory :> bytes(word_add stackpointer (word 504),64)] ,,
            MAYCHANGE SOME_FLAGS)`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the n < p_521 assumption for simplicity's sake ***)

  ASM_CASES_TAC `n < p_521` THENL
   [ASM_REWRITE_TAC[]; X86_SIM_TAC P521_JDOUBLE_EXEC (1--231)] THEN

  (*** Digitize, deduce the bound on the top word specifically ***)

  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN
  SUBGOAL_THEN `n DIV 2 EXP 512 < 2 EXP 9` MP_TAC THENL
   [UNDISCH_TAC `n < p_521` THEN REWRITE_TAC[p_521] THEN ARITH_TAC;
    FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (funpow 3 LAND_CONV) [SYM th]) THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV)) THEN
    DISCH_TAC] THEN

  (*** Simulate core squaring, with manual tweaks for small high digit ***)

  X86_ACCSTEPS_TAC P521_JDOUBLE_EXEC (1--160) (1--160) THEN
  X86_ACCSTEPS_TAC P521_JDOUBLE_EXEC (165--189) (161--189) THEN
  SUBGOAL_THEN
   `&(val(word_add n_8 n_8:int64)):real = &2 * &(val n_8) /\
    &(val(word_mul n_8 n_8:int64)):real = &(val n_8) pow 2`
  (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
   [REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_MUL; DIMINDEX_64] THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES; MULT_2; EXP_2] THEN
    CONJ_TAC THEN MATCH_MP_TAC MOD_LT THENL
     [ALL_TAC;
      REWRITE_TAC[ARITH_RULE `2 EXP 64 = 2 EXP 32 * 2 EXP 32`] THEN
      MATCH_MP_TAC LT_MULT2 THEN CONJ_TAC] THEN
    UNDISCH_TAC `val(n_8:int64) < 2 EXP 9` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `bitval(2 EXP 64 <= val(n_8:int64) + val n_8) = 0`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[BITVAL_EQ_0] THEN
    UNDISCH_TAC `val(n_8:int64) < 2 EXP 9` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `bitval(~(ival(n_8:int64) + ival n_8 = ival (word_add n_8 n_8))) = 0`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[BITVAL_EQ_0] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC INT_CONG_IMP_EQ THEN
    EXISTS_TAC `(&2:int) pow dimindex(:64)` THEN
    REWRITE_TAC[ICONG_WORD_ADD] THEN
    MP_TAC(ISPEC `word_add n_8 n_8:int64` IVAL_BOUND) THEN
    SUBST1_TAC(ISPEC `n_8:int64` INT_IVAL) THEN
    UNDISCH_TAC `val(n_8:int64) < 2 EXP 9` THEN
    REWRITE_TAC[DIMINDEX_64; GSYM INT_OF_NUM_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC INT_ARITH;
    ALL_TAC] THEN

  (*** Introduce more systematic names for the high part digits ***)

  REABBREV_TAC `h0 = read R8 s189` THEN POP_ASSUM SUBST_ALL_TAC THEN
  REABBREV_TAC `h1 = read R9 s189` THEN POP_ASSUM SUBST_ALL_TAC THEN
  REABBREV_TAC `h2 = read R10 s189` THEN POP_ASSUM SUBST_ALL_TAC THEN
  REABBREV_TAC `h3 = read R11 s189` THEN POP_ASSUM SUBST_ALL_TAC THEN
  REABBREV_TAC `h4 = read R12 s189` THEN POP_ASSUM SUBST_ALL_TAC THEN
  REABBREV_TAC `h5 = read R13 s189` THEN POP_ASSUM SUBST_ALL_TAC THEN
  REABBREV_TAC `h6 = read R14 s189` THEN POP_ASSUM SUBST_ALL_TAC THEN
  REABBREV_TAC `h7 = read R15 s189` THEN POP_ASSUM SUBST_ALL_TAC THEN
  REABBREV_TAC `h8 = read RCX s189` THEN POP_ASSUM SUBST_ALL_TAC THEN

  (*** Show that the core squaring operation is correct ***)

  SUBGOAL_THEN
   `2 EXP 512 * bignum_of_wordlist[h0;h1;h2;h3;h4;h5;h6;h7;h8] +
    bignum_from_memory(word_add stackpointer (word 504),8) s189 =
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
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o
      filter (is_ratconst o rand o concl) o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES])] THEN

  (*** Now simulate the rotation part ***)

  X86_STEPS_TAC P521_JDOUBLE_EXEC (190--201) THEN

  (*** Break up into high and low parts ***)

  ABBREV_TAC `h = (n EXP 2) DIV 2 EXP 521` THEN
  ABBREV_TAC `l = (n EXP 2) MOD 2 EXP 521` THEN
  SUBGOAL_THEN `h < p_521 /\ l <= p_521` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"] THEN REWRITE_TAC[p_521] THEN
    CONJ_TAC THENL [ALL_TAC; ARITH_TAC] THEN
    SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN
    TRANS_TAC LET_TRANS `(p_521 - 1) EXP 2` THEN
    REWRITE_TAC[EXP_MONO_LE] THEN UNDISCH_TAC `n < p_521` THEN
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `n EXP 2 MOD p_521 = (h + l) MOD p_521` SUBST1_TAC THENL
   [SUBST1_TAC(SYM(SPECL
     [`n EXP 2`; `2 EXP 521`] (CONJUNCT2 DIVISION_SIMP))) THEN
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
     [mullo_s101; sum_s105; sum_s111; sum_s115; sum_s121; sum_s125; sum_s131;
      sum_s135]`
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

  X86_ACCSTEPS_TAC P521_JDOUBLE_EXEC (202--211) (202--211) THEN
  SUBGOAL_THEN
   `&(val(word_add (word_ushr h8 9) (word_and h0 (word 511):int64))):real =
    &(val(word_ushr h8 9:int64)) + &(val(word_and h0 (word 511):int64))`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_CLAUSES; VAL_WORD_ADD; DIMINDEX_64] THEN
    MATCH_MP_TAC MOD_LT THEN
    REWRITE_TAC[VAL_WORD_AND_MASK_WORD; ARITH_RULE `511 = 2 EXP 9 - 1`] THEN
    REWRITE_TAC[VAL_WORD_USHR] THEN
    MP_TAC(SPEC `h8:int64` VAL_BOUND_64) THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `carry_s211 <=> p_521 <= h + l` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `576` THEN
    MAP_EVERY EXPAND_TAC ["h"; "l"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_521] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN

  (*** The final correction ***)

  X86_ACCSTEPS_TAC P521_JDOUBLE_EXEC (212--231) (212--231) THEN
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
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
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

(* ------------------------------------------------------------------------- *)
(* Instances of mul.                                                         *)
(* ------------------------------------------------------------------------- *)

let LOCAL_MUL_P521_TAC =
  X86_MACRO_SIM_ABBREV_TAC (X86_TRIM_EXEC_RULE p521_jdouble_tmc) 312 lvs
  `!(t:x86state) pcin pcout p3 n3 p1 n1 p2 n2.
    !a. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 9)) t = a
    ==>
    !b. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 9)) t = b
    ==>
    nonoverlapping (word pc,0x3ded) (stackpointer,568) /\
    nonoverlapping (read RDI t,216) (stackpointer,568) /\
    nonoverlapping (read RSI t,216) (stackpointer,568) /\
    nonoverlapping (word pc,0x3ded) (read RDI t,216)
    ==> ensures x86
         (\s. bytes_loaded s (word pc) (BUTLAST p521_jdouble_tmc) /\
              read RIP s = pcin /\
              read RSP s = read RSP t /\
              read RDI s = read RDI t /\
              read RSI s = read RSI t /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 9)) s =
              a /\
              read(memory :> bytes(word_add (read p2 t) (word n2),8 * 9)) s =
              b)
         (\s. read RIP s = pcout /\
              (a < p_521 /\ b < p_521
               ==> read(memory :> bytes(word_add (read p3 t) (word n3),
                        8 * 9)) s = (a * b) MOD p_521))
         (MAYCHANGE [RIP; RAX; RBX; RCX; RDX;
                     R8; R9; R10; R11; R12; R13; R14; R15] ,,
          MAYCHANGE
            [memory :> bytes(word_add (read p3 t) (word n3),8 * 9);
             memory :> bytes(word_add stackpointer (word 504),64)] ,,
         MAYCHANGE SOME_FLAGS)`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the a < p_521 /\ b < p_521 assumption for simplicity ***)

  ASM_CASES_TAC `a < p_521 /\ b < p_521` THENL
   [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC);
    X86_SIM_TAC P521_JDOUBLE_EXEC (2--313)] THEN

  (*** Digitize, deduce the bound on the top words ***)

  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s1" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "y_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "x_" o lhand o concl) THEN
  SUBGOAL_THEN
   `a DIV 2 EXP 512 < 2 EXP 9 /\ b DIV 2 EXP 512 < 2 EXP 9`
  MP_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`a < p_521`; `b < p_521`] THEN
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    MAP_EVERY EXPAND_TAC ["a"; "b"] THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN

  (*** Simulate the initial multiplication ***)

  X86_ACCSTEPS_TAC P521_JDOUBLE_EXEC (2--271) (2--271) THEN

  (*** Introduce more systematic names for the high part digits ***)

  REABBREV_TAC `h0 = read R8 s271` THEN POP_ASSUM SUBST_ALL_TAC THEN
  REABBREV_TAC `h1 = read R9 s271` THEN POP_ASSUM SUBST_ALL_TAC THEN
  REABBREV_TAC `h2 = read R10 s271` THEN POP_ASSUM SUBST_ALL_TAC THEN
  REABBREV_TAC `h3 = read R11 s271` THEN POP_ASSUM SUBST_ALL_TAC THEN
  REABBREV_TAC `h4 = read R12 s271` THEN POP_ASSUM SUBST_ALL_TAC THEN
  REABBREV_TAC `h5 = read R13 s271` THEN POP_ASSUM SUBST_ALL_TAC THEN
  REABBREV_TAC `h6 = read R14 s271` THEN POP_ASSUM SUBST_ALL_TAC THEN
  REABBREV_TAC `h7 = read R15 s271` THEN POP_ASSUM SUBST_ALL_TAC THEN
  REABBREV_TAC `h8 = read RCX s271` THEN POP_ASSUM SUBST_ALL_TAC THEN

  (*** Show that the core multiplication operation is correct ***)

  SUBGOAL_THEN
   `2 EXP 512 * bignum_of_wordlist[h0;h1;h2;h3;h4;h5;h6;h7;h8] +
    bignum_from_memory(word_add stackpointer (word 504),8) s271 =
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
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o
      filter (is_ratconst o rand o concl) o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES])] THEN

  (*** Now simulate the rotation part ***)

  X86_STEPS_TAC P521_JDOUBLE_EXEC (272--283) THEN

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
     [mullo_s4; sum_s24; sum_s52; sum_s80; sum_s108; sum_s136; sum_s164;
      sum_s192]`
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

  X86_ACCSTEPS_TAC P521_JDOUBLE_EXEC (284--293) (284--293) THEN
  SUBGOAL_THEN
   `&(val(word_add (word_ushr h8 9) (word_and h0 (word 511):int64))):real =
    &(val(word_ushr h8 9:int64)) + &(val(word_and h0 (word 511):int64))`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_CLAUSES; VAL_WORD_ADD; DIMINDEX_64] THEN
    MATCH_MP_TAC MOD_LT THEN
    REWRITE_TAC[VAL_WORD_AND_MASK_WORD; ARITH_RULE `511 = 2 EXP 9 - 1`] THEN
    REWRITE_TAC[VAL_WORD_USHR] THEN
    MP_TAC(SPEC `h8:int64` VAL_BOUND_64) THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `carry_s293 <=> p_521 <= h + l` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `576` THEN
    MAP_EVERY EXPAND_TAC ["h"; "l"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_521] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN

  (*** The final correction ***)

  X86_ACCSTEPS_TAC P521_JDOUBLE_EXEC (294--313) (294--313) THEN
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
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
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

(* ------------------------------------------------------------------------- *)
(* Instances of add.                                                         *)
(* ------------------------------------------------------------------------- *)

let LOCAL_ADD_P521_TAC =
  X86_MACRO_SIM_ABBREV_TAC (X86_TRIM_EXEC_RULE p521_jdouble_tmc) 40 lvs
  `!(t:x86state) pcin pcout p3 n3 p1 n1 p2 n2.
    !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 9)) t = m
    ==>
    !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 9)) t = n
    ==>
    nonoverlapping (word pc,0x3ded) (word_add (read p3 t) (word n3),72)
    ==> ensures x86
         (\s. bytes_loaded s (word pc) (BUTLAST p521_jdouble_tmc) /\
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
    X86_SIM_TAC P521_JDOUBLE_EXEC (1--40)] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "m_" o lhand o concl) THEN

  (*** Initial non-overflowing addition s = x + y + 1 ***)

  X86_ACCSTEPS_TAC P521_JDOUBLE_EXEC [3;5;7;9;11;13;15;17;19] (1--19) THEN
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

  X86_STEPS_TAC P521_JDOUBLE_EXEC (20--21) THEN
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
  X86_STEPS_TAC P521_JDOUBLE_EXEC [22] THEN
  SUBGOAL_THEN
   `val(if p_521 <= m + n then word 512 else word 0:int64) < 512 <=>
    ~(p_521 <= m + n)`
  SUBST_ALL_TAC THENL
   [COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN

  (*** The final optional subtraction of either 1 or 2^521 ***)

  X86_ACCSTEPS_TAC P521_JDOUBLE_EXEC
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

(* ------------------------------------------------------------------------- *)
(* Instances of sub.                                                         *)
(* ------------------------------------------------------------------------- *)

let LOCAL_SUB_P521_TAC =
  X86_MACRO_SIM_ABBREV_TAC (X86_TRIM_EXEC_RULE p521_jdouble_tmc) 37 lvs
  `!(t:x86state) pcin pcout p3 n3 p1 n1 p2 n2.
    !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 9)) t = m
    ==>
    !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 9)) t = n
    ==>
    nonoverlapping (word pc,0x3ded) (word_add (read p3 t) (word n3),72)
    ==> ensures x86
         (\s. bytes_loaded s (word pc) (BUTLAST p521_jdouble_tmc) /\
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

  X86_ACCSTEPS_TAC P521_JDOUBLE_EXEC [2;4;6;8;10;12;14;16;18] (1--18) THEN

  SUBGOAL_THEN `carry_s18 <=> m < n` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `576` THEN
    MAP_EVERY EXPAND_TAC ["m"; "n"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN

  (*** Further optional subtraction mod 2^521 ***)

  X86_ACCSTEPS_TAC P521_JDOUBLE_EXEC
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

(* ------------------------------------------------------------------------- *)
(* Instances of weakmul.                                                     *)
(* ------------------------------------------------------------------------- *)

let LOCAL_WEAKMUL_P521_TAC =
  X86_MACRO_SIM_ABBREV_TAC (X86_TRIM_EXEC_RULE p521_jdouble_tmc) 300 lvs
  `!(t:x86state) pcin pcout p3 n3 p1 n1 p2 n2.
    !a. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 9)) t = a
    ==>
    !b. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 9)) t = b
    ==>
    nonoverlapping (word pc,0x3ded) (stackpointer,568) /\
    nonoverlapping (read RDI t,216) (stackpointer,568) /\
    nonoverlapping (read RSI t,216) (stackpointer,568) /\
    nonoverlapping (word pc,0x3ded) (read RDI t,216)
    ==> ensures x86
         (\s. bytes_loaded s (word pc) (BUTLAST p521_jdouble_tmc) /\
              read RIP s = pcin /\
              read RSP s = read RSP t /\
              read RDI s = read RDI t /\
              read RSI s = read RSI t /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 9)) s =
              a /\
              read(memory :> bytes(word_add (read p2 t) (word n2),8 * 9)) s =
              b)
         (\s. read RIP s = pcout /\
              (a < p_521 /\ b < p_521
               ==> read(memory :> bytes(word_add (read p3 t) (word n3),
                        8 * 9)) s < 2 * p_521 /\
                   (read(memory :> bytes(word_add (read p3 t) (word n3),
                        8 * 9)) s == a * b) (mod p_521)))
         (MAYCHANGE [RIP; RAX; RBX; RCX; RDX;
                     R8; R9; R10; R11; R12; R13; R14; R15] ,,
          MAYCHANGE
            [memory :> bytes(word_add (read p3 t) (word n3),8 * 9);
             memory :> bytes(word_add stackpointer (word 504),64)] ,,
         MAYCHANGE SOME_FLAGS)`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the a < p_521 /\ b < p_521 assumption for simplicity ***)

  ASM_CASES_TAC `a < p_521 /\ b < p_521` THENL
   [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC);
    X86_SIM_TAC P521_JDOUBLE_EXEC (2--301)] THEN

  (*** Digitize, deduce the bound on the top words ***)

  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s1" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "y_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "x_" o lhand o concl) THEN
  SUBGOAL_THEN
   `a DIV 2 EXP 512 < 2 EXP 9 /\ b DIV 2 EXP 512 < 2 EXP 9`
  MP_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`a < p_521`; `b < p_521`] THEN
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    MAP_EVERY EXPAND_TAC ["a"; "b"] THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN

  (*** Simulate the initial multiplication ***)

  X86_ACCSTEPS_TAC P521_JDOUBLE_EXEC (2--271) (2--271) THEN

  (*** Introduce more systematic names for the high part digits ***)

  REABBREV_TAC `h0 = read R8 s271` THEN POP_ASSUM SUBST_ALL_TAC THEN
  REABBREV_TAC `h1 = read R9 s271` THEN POP_ASSUM SUBST_ALL_TAC THEN
  REABBREV_TAC `h2 = read R10 s271` THEN POP_ASSUM SUBST_ALL_TAC THEN
  REABBREV_TAC `h3 = read R11 s271` THEN POP_ASSUM SUBST_ALL_TAC THEN
  REABBREV_TAC `h4 = read R12 s271` THEN POP_ASSUM SUBST_ALL_TAC THEN
  REABBREV_TAC `h5 = read R13 s271` THEN POP_ASSUM SUBST_ALL_TAC THEN
  REABBREV_TAC `h6 = read R14 s271` THEN POP_ASSUM SUBST_ALL_TAC THEN
  REABBREV_TAC `h7 = read R15 s271` THEN POP_ASSUM SUBST_ALL_TAC THEN
  REABBREV_TAC `h8 = read RCX s271` THEN POP_ASSUM SUBST_ALL_TAC THEN

  (*** Show that the core multiplication operation is correct ***)

  SUBGOAL_THEN
   `2 EXP 512 * bignum_of_wordlist[h0;h1;h2;h3;h4;h5;h6;h7;h8] +
    bignum_from_memory(word_add stackpointer (word 504),8) s271 =
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
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o
      filter (is_ratconst o rand o concl) o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES])] THEN

  (*** Now simulate the rotation part ***)

  X86_STEPS_TAC P521_JDOUBLE_EXEC (272--283) THEN

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
  REWRITE_TAC[CONG] THEN
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
     [mullo_s4; sum_s24; sum_s52; sum_s80; sum_s108; sum_s136; sum_s164;
      sum_s192]`
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

  (*** Now the simple addition of h + l as the result ***)

  X86_ACCSTEPS_TAC P521_JDOUBLE_EXEC
   [284;286;288;290;292;294;296;298;300] (284--301) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  MATCH_MP_TAC(MESON[]
   `x' < a /\ x = x' ==> x < a /\ x MOD p = x' MOD p`) THEN
  CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`h < p_521`; `l <= p_521`] THEN ARITH_TAC;
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`576`; `&0:real`] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0] THEN
    MAP_EVERY UNDISCH_TAC [`h < p_521`; `l <= p_521`] THEN
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    REWRITE_TAC[INTEGER_CLOSED]] THEN
  MAP_EVERY EXPAND_TAC ["h"; "l"] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_521] THEN
  ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
  REWRITE_TAC[VAL_WORD_AND_MASK_WORD; ARITH_RULE `511 = 2 EXP 9 - 1`] THEN
  REWRITE_TAC[REAL_OF_NUM_MOD] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instance (12,9) of cmsub (the only one used in this code).                *)
(* ------------------------------------------------------------------------- *)

let LOCAL_CMSUBC9_P521_TAC =
  X86_MACRO_SIM_ABBREV_TAC (X86_TRIM_EXEC_RULE p521_jdouble_tmc) 99 lvs
  `!(t:x86state) pcin pcout p3 n3 p1 n1 p2 n2.
    !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 9)) t = m
    ==>
    !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 9)) t = n
    ==> nonoverlapping (word pc,0x3ded) (word_add (read p3 t) (word n3),72)
    ==> ensures x86
         (\s. bytes_loaded s (word pc) (BUTLAST p521_jdouble_tmc) /\
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
    X86_SIM_TAC P521_JDOUBLE_EXEC (1--99)] THEN

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

  X86_ACCSTEPS_TAC P521_JDOUBLE_EXEC (1--64) (1--64) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist
     [sum_s40; sum_s43; sum_s46; sum_s49;
      sum_s52; sum_s55; sum_s58; sum_s61; sum_s64] = ca`
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

  X86_STEPS_TAC P521_JDOUBLE_EXEC (65--74) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_AND_ASSOC; DIMINDEX_64]) THEN
  MAP_EVERY ABBREV_TAC
   [`h:int64 = word_ushr sum_s64 9`;
    `d:int64 = word_or sum_s64 (word 18446744073709551104)`;
    `dd:int64 = word_and sum_s43 (word_and sum_s46 (word_and sum_s49
      (word_and sum_s52 (word_and sum_s55 (word_and sum_s58 sum_s61)))))`] THEN

  (*** The comparison in its direct condensed form ***)

  X86_ACCSTEPS_TAC P521_JDOUBLE_EXEC [76;78;80] (75--80) THEN

  SUBGOAL_THEN
   `&(val (word_add h (word 1):int64)):real = &(val h) + &1`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_CLAUSES; VAL_WORD_ADD_CASES] THEN
    REWRITE_TAC[DIMINDEX_64; VAL_WORD_1] THEN
    MATCH_MP_TAC(MESON[] `p ==> (if p then x else y) = x`) THEN
    SUBST1_TAC(SYM(ASSUME `word_ushr sum_s64 9 = (h:int64)`)) THEN
    CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `carry_s80 <=>
    2 EXP 192 <=
      2 EXP 128 * val(d:int64) + 2 EXP 64 * val(dd:int64) +
      val(h:int64) + val(sum_s40:int64) + 1`
  (ASSUME_TAC o SYM) THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `192` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Finish the simulation before completing the mathematics ***)

  X86_ACCSTEPS_TAC P521_JDOUBLE_EXEC
   [81;83;85;87;89;91;93;95;97] (81--99) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  DISCARD_STATE_TAC "s99" THEN

  (*** Evaluate d and un-condense the inequality ***)

  SUBGOAL_THEN
   `val(d:int64) = 2 EXP 9 * (2 EXP 55 - 1) + val(sum_s64:int64) MOD 2 EXP 9`
  SUBST_ALL_TAC THENL
   [EXPAND_TAC "d" THEN ONCE_REWRITE_TAC[WORD_BITWISE_RULE
     `word_or a b = word_or b (word_and a (word_not b))`] THEN
    SIMP_TAC[VAL_WORD_OR_DISJOINT; WORD_BITWISE_RULE
     `word_and x (word_and y (word_not x)) = word 0`] THEN
    REWRITE_TAC[GSYM VAL_WORD_AND_MASK_WORD] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV;
    ALL_TAC] THEN

  SUBGOAL_THEN
   `2 EXP 512 * val(sum_s64:int64) MOD 2 EXP 9 +
    bignum_of_wordlist
     [sum_s40; sum_s43; sum_s46; sum_s49; sum_s52; sum_s55; sum_s58; sum_s61] =
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
   `2 EXP 521 <= ca MOD 2 EXP 521 + val(h:int64) + 1 <=> carry_s80`
  MP_TAC THENL
   [REMOVE_THEN "*" (SUBST1_TAC o SYM) THEN EXPAND_TAC "carry_s80" THEN
    ONCE_REWRITE_TAC[bignum_of_wordlist] THEN
    MATCH_MP_TAC(TAUT
     `!p q. ((p ==> ~r) /\ (q ==> ~s)) /\ (p <=> q) /\ (~p /\ ~q ==> (r <=> s))
            ==> (r <=> s)`) THEN
    MAP_EVERY EXISTS_TAC
     [`bignum_of_wordlist
        [sum_s43; sum_s46; sum_s49; sum_s52; sum_s55; sum_s58; sum_s61] <
       2 EXP (64 * 7) - 1`;
      `val(dd:int64) < 2 EXP 64 - 1`] THEN
    CONJ_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC(ARITH_RULE
      `2 EXP 64 * b + d < 2 EXP 64 * (a + 1) + c ==> a < b ==> ~(c <= d)`) THEN
      MP_TAC(SPEC `h:int64` VAL_BOUND_64) THEN
      MP_TAC(SPEC `sum_s40:int64` VAL_BOUND_64) THEN ARITH_TAC;
      SIMP_TAC[BIGNUM_OF_WORDLIST_LT_MAX; LENGTH; ARITH_EQ; ARITH_SUC]] THEN
    REWRITE_TAC[GSYM NOT_ALL] THEN MP_TAC(ISPEC `dd:int64` VAL_EQ_MAX) THEN
    SIMP_TAC[VAL_BOUND_64; DIMINDEX_64; ARITH_RULE
      `a < n ==> (a < n - 1 <=> ~(a = n - 1))`] THEN
    DISCH_THEN SUBST1_TAC THEN EXPAND_TAC "dd" THEN
    REWRITE_TAC[WORD_NOT_AND; ALL; WORD_OR_EQ_0] THEN
    REWRITE_TAC[WORD_RULE `word_not d = e <=> d = word_not e`] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC) THEN
    REWRITE_TAC[bignum_of_wordlist] THEN CONV_TAC WORD_REDUCE_CONV THEN
    MP_TAC(ARITH_RULE `val(sum_s64:int64) MOD 2 EXP 9 = 511 \/
                       val(sum_s64:int64) MOD 2 EXP 9 < 511`) THEN
    MP_TAC(SPEC `h:int64` VAL_BOUND_64) THEN
    MP_TAC(SPEC `sum_s40:int64` VAL_BOUND_64) THEN ARITH_TAC;
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

(* ------------------------------------------------------------------------- *)
(* Instances of cmsub41 (there is only one).                                 *)
(* ------------------------------------------------------------------------- *)

let LOCAL_CMSUB41_P521_TAC =
  X86_MACRO_SIM_ABBREV_TAC (X86_TRIM_EXEC_RULE p521_jdouble_tmc) 80 lvs
  `!(t:x86state) pcin pcout p3 n3 p1 n1 p2 n2.
    !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 9)) t = m
    ==>
    !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 9)) t = n
    ==> nonoverlapping (word pc,0x3ded) (word_add (read p3 t) (word n3),72)
    ==> ensures x86
         (\s. bytes_loaded s (word pc) (BUTLAST p521_jdouble_tmc) /\
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
    X86_SIM_TAC P521_JDOUBLE_EXEC (1--80)] THEN

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

  X86_ACCSTEPS_TAC P521_JDOUBLE_EXEC
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

  X86_STEPS_TAC P521_JDOUBLE_EXEC (46--55) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_AND_ASSOC; DIMINDEX_64]) THEN
  MAP_EVERY ABBREV_TAC
   [`h:int64 = word_ushr sum_s45 9`;
    `d:int64 = word_or sum_s45 (word 18446744073709551104)`;
    `dd:int64 = word_and sum_s26 (word_and sum_s29 (word_and sum_s32
      (word_and sum_s35 (word_and sum_s38 (word_and sum_s41 sum_s44)))))`] THEN

  (*** The comparison in its direct condensed form ***)

  X86_ACCSTEPS_TAC P521_JDOUBLE_EXEC [57;59;61] (56--61) THEN

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

  X86_ACCSTEPS_TAC P521_JDOUBLE_EXEC
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

(* ------------------------------------------------------------------------- *)
(* Instances of cmsub38 (there is only one).                                 *)
(* ------------------------------------------------------------------------- *)

let LOCAL_CMSUB38_P521_TAC =
  X86_MACRO_SIM_ABBREV_TAC (X86_TRIM_EXEC_RULE p521_jdouble_tmc) 90 lvs
  `!(t:x86state) pcin pcout p3 n3 p1 n1 p2 n2.
    !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 9)) t = m
    ==>
    !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 9)) t = n
    ==> nonoverlapping (word pc,0x3ded) (word_add (read p3 t) (word n3),72)
    ==> ensures x86
         (\s. bytes_loaded s (word pc) (BUTLAST p521_jdouble_tmc) /\
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
    X86_SIM_TAC P521_JDOUBLE_EXEC (1--90)] THEN

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

  X86_ACCSTEPS_TAC P521_JDOUBLE_EXEC (30--55) (1--55) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist
     [sum_s31; sum_s34; sum_s37; sum_s40;
      sum_s43; sum_s46; sum_s49; sum_s52; sum_s55] = ca`
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

  X86_STEPS_TAC P521_JDOUBLE_EXEC (56--65) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_AND_ASSOC; DIMINDEX_64]) THEN
  MAP_EVERY ABBREV_TAC
   [`h:int64 = word_ushr sum_s55 9`;
    `d:int64 = word_or sum_s55 (word 18446744073709551104)`;
    `dd:int64 = word_and sum_s34 (word_and sum_s37 (word_and sum_s40
      (word_and sum_s43 (word_and sum_s46 (word_and sum_s49 sum_s52)))))`] THEN

  (*** The comparison in its direct condensed form ***)

  X86_ACCSTEPS_TAC P521_JDOUBLE_EXEC [67;69;71] (66--71) THEN

  SUBGOAL_THEN
   `&(val (word_add h (word 1):int64)):real = &(val h) + &1`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_CLAUSES; VAL_WORD_ADD_CASES] THEN
    REWRITE_TAC[DIMINDEX_64; VAL_WORD_1] THEN
    MATCH_MP_TAC(MESON[] `p ==> (if p then x else y) = x`) THEN
    SUBST1_TAC(SYM(ASSUME `word_ushr sum_s55 9 = (h:int64)`)) THEN
    CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `carry_s71 <=>
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

  X86_ACCSTEPS_TAC P521_JDOUBLE_EXEC
   [72;74;76;78;80;82;84;86;88] (72--90) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  DISCARD_STATE_TAC "s90" THEN

  (*** Evaluate d and un-condense the inequality ***)

  SUBGOAL_THEN
   `val(d:int64) = 2 EXP 9 * (2 EXP 55 - 1) + val(sum_s55:int64) MOD 2 EXP 9`
  SUBST_ALL_TAC THENL
   [EXPAND_TAC "d" THEN ONCE_REWRITE_TAC[WORD_BITWISE_RULE
     `word_or a b = word_or b (word_and a (word_not b))`] THEN
    SIMP_TAC[VAL_WORD_OR_DISJOINT; WORD_BITWISE_RULE
     `word_and x (word_and y (word_not x)) = word 0`] THEN
    REWRITE_TAC[GSYM VAL_WORD_AND_MASK_WORD] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV;
    ALL_TAC] THEN

  SUBGOAL_THEN
   `2 EXP 512 * val(sum_s55:int64) MOD 2 EXP 9 +
    bignum_of_wordlist
     [sum_s31; sum_s34; sum_s37; sum_s40; sum_s43; sum_s46; sum_s49; sum_s52] =
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
   `2 EXP 521 <= ca MOD 2 EXP 521 + val(h:int64) + 1 <=> carry_s71`
  MP_TAC THENL
   [REMOVE_THEN "*" (SUBST1_TAC o SYM) THEN EXPAND_TAC "carry_s71" THEN
    ONCE_REWRITE_TAC[bignum_of_wordlist] THEN
    MATCH_MP_TAC(TAUT
     `!p q. ((p ==> ~r) /\ (q ==> ~s)) /\ (p <=> q) /\ (~p /\ ~q ==> (r <=> s))
            ==> (r <=> s)`) THEN
    MAP_EVERY EXISTS_TAC
     [`bignum_of_wordlist
        [sum_s34; sum_s37; sum_s40; sum_s43; sum_s46; sum_s49; sum_s52] <
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
    MP_TAC(ARITH_RULE `val(sum_s55:int64) MOD 2 EXP 9 = 511 \/
                       val(sum_s55:int64) MOD 2 EXP 9 < 511`) THEN
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

(* ------------------------------------------------------------------------- *)
(* Overall point operation proof.                                            *)
(* ------------------------------------------------------------------------- *)

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

let represents_p521 = new_definition
 `represents_p521 P (x,y,z) <=>
        x < p_521 /\ y < p_521 /\ z < p_521 /\
        weierstrass_of_jacobian (integer_mod_ring p_521)
         (tripled (modular_decode (576,p_521)) (x,y,z)) = P`;;

let P521_JDOUBLE_CORRECT = time prove
 (`!p3 p1 t1 pc stackpointer.
        ALL (nonoverlapping (stackpointer,568))
            [(word pc,0x3ded); (p1,216); (p3,216)] /\
        nonoverlapping (p3,216) (word pc,0x3ded)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST p521_jdouble_tmc) /\
                  read RIP s = word(pc + 0x10) /\
                  read RSP s = stackpointer /\
                  C_ARGUMENTS [p3; p1] s /\
                  bignum_triple_from_memory (p1,9) s = t1)
             (\s. read RIP s = word (pc + 0x3ddc) /\
                  !P. represents_p521 P t1
                      ==> represents_p521 (group_mul p521_group P P)
                            (bignum_triple_from_memory(p3,9) s))
          (MAYCHANGE [RIP; RAX; RBX; RCX; RDX; R8; R9;
                      R10; R11; R12; R13; R14; R15] ,,
           MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [memory :> bytes(p3,216);
                      memory :> bytes(stackpointer,568)])`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`p3:int64`; `p1:int64`; `x:num`; `y:num`; `z:num`;
    `pc:num`; `stackpointer:int64`] THEN
  REWRITE_TAC[ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS; PAIR_EQ; bignum_triple_from_memory] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN

  LOCAL_SQR_P521_TAC 0 ["z2";"z_1"] THEN
  LOCAL_SQR_P521_TAC 0 ["y2";"y_1"] THEN
  LOCAL_ADD_P521_TAC 0 ["t1";"x_1";"z2"] THEN
  LOCAL_SUB_P521_TAC 0 ["t2";"x_1";"z2"] THEN
  LOCAL_MUL_P521_TAC 0 ["x2p";"t1";"t2"] THEN
  LOCAL_ADD_P521_TAC 0 ["t1";"y_1";"z_1"] THEN
  LOCAL_SQR_P521_TAC 0 ["x4p";"x2p"] THEN
  LOCAL_WEAKMUL_P521_TAC 0 ["xy2";"x_1";"y2"] THEN
  LOCAL_SQR_P521_TAC 0 ["t2";"t1"] THEN
  LOCAL_CMSUBC9_P521_TAC 0 ["d";"xy2";"x4p"] THEN
  LOCAL_SUB_P521_TAC 0 ["t1";"t2";"z2"] THEN
  LOCAL_SQR_P521_TAC 0 ["y4";"y2"] THEN
  LOCAL_SUB_P521_TAC 0 ["z_3";"t1";"y2"] THEN
  LOCAL_WEAKMUL_P521_TAC 0 ["dx2";"d";"x2p"] THEN
  LOCAL_CMSUB41_P521_TAC 0 ["x_3";"xy2";"d"] THEN
  LOCAL_CMSUB38_P521_TAC 0 ["y_3";"dx2";"y4"] THEN

  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCARD_STATE_TAC "s16" THEN
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

let P521_JDOUBLE_NOIBT_SUBROUTINE_CORRECT = time prove
 (`!p3 p1 t1 pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 608),608))
            [(word pc,LENGTH p521_jdouble_tmc); (p1,216)] /\
        ALL (nonoverlapping (p3,216))
            [(word pc,LENGTH p521_jdouble_tmc); (word_sub stackpointer (word 608),616)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) p521_jdouble_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [p3; p1] s /\
                  bignum_triple_from_memory (p1,9) s = t1)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !P. represents_p521 P t1
                      ==> represents_p521 (group_mul p521_group P P)
                            (bignum_triple_from_memory(p3,9) s))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(p3,216);
                      memory :> bytes(word_sub stackpointer (word 608),608)])`,
  X86_PROMOTE_RETURN_STACK_TAC p521_jdouble_tmc P521_JDOUBLE_CORRECT
    `[RBX; R12; R13; R14; R15]` 608);;

let P521_JDOUBLE_SUBROUTINE_CORRECT = time prove
 (`!p3 p1 t1 pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 608),608))
            [(word pc,LENGTH p521_jdouble_mc); (p1,216)] /\
        ALL (nonoverlapping (p3,216))
            [(word pc,LENGTH p521_jdouble_mc); (word_sub stackpointer (word 608),616)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) p521_jdouble_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [p3; p1] s /\
                  bignum_triple_from_memory (p1,9) s = t1)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !P. represents_p521 P t1
                      ==> represents_p521 (group_mul p521_group P P)
                            (bignum_triple_from_memory(p3,9) s))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(p3,216);
                      memory :> bytes(word_sub stackpointer (word 608),608)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE P521_JDOUBLE_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let p521_jdouble_windows_mc = define_from_elf "p521_jdouble_windows_mc"
      "x86/p521/p521_jdouble.obj";;

let p521_jdouble_windows_tmc = define_trimmed "p521_jdouble_windows_tmc" p521_jdouble_windows_mc;;

let P521_JDOUBLE_NOIBT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!p3 p1 t1 pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 624),624))
            [(word pc,LENGTH p521_jdouble_windows_tmc); (p1,216)] /\
        ALL (nonoverlapping (p3,216))
            [(word pc,LENGTH p521_jdouble_windows_tmc); (word_sub stackpointer (word 624),632)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) p521_jdouble_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [p3; p1] s /\
                  bignum_triple_from_memory (p1,9) s = t1)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !P. represents_p521 P t1
                      ==> represents_p521 (group_mul p521_group P P)
                            (bignum_triple_from_memory(p3,9) s))
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(p3,216);
                      memory :> bytes(word_sub stackpointer (word 624),624)])`,
  WINDOWS_X86_WRAP_STACK_TAC
   p521_jdouble_windows_tmc p521_jdouble_tmc
   P521_JDOUBLE_CORRECT
    `[RBX; R12; R13; R14; R15]` 608);;

let P521_JDOUBLE_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!p3 p1 t1 pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 624),624))
            [(word pc,LENGTH p521_jdouble_windows_mc); (p1,216)] /\
        ALL (nonoverlapping (p3,216))
            [(word pc,LENGTH p521_jdouble_windows_mc); (word_sub stackpointer (word 624),632)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) p521_jdouble_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [p3; p1] s /\
                  bignum_triple_from_memory (p1,9) s = t1)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !P. represents_p521 P t1
                      ==> represents_p521 (group_mul p521_group P P)
                            (bignum_triple_from_memory(p3,9) s))
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(p3,216);
                      memory :> bytes(word_sub stackpointer (word 624),624)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE P521_JDOUBLE_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

