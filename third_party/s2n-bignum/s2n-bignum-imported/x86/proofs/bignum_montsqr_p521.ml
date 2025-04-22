(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Montgomery squaring modulo p_521.                                         *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/p521/bignum_montsqr_p521.o";;
 ****)

let bignum_montsqr_p521_mc = define_assert_from_elf "bignum_montsqr_p521_mc" "x86/p521/bignum_montsqr_p521.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x55;                    (* PUSH (% rbp) *)
  0x41; 0x54;              (* PUSH (% r12) *)
  0x41; 0x55;              (* PUSH (% r13) *)
  0x41; 0x56;              (* PUSH (% r14) *)
  0x41; 0x57;              (* PUSH (% r15) *)
  0x48; 0x83; 0xec; 0x40;  (* SUB (% rsp) (Imm8 (word 64)) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0x48; 0x8b; 0x16;        (* MOV (% rdx) (Memop Quadword (%% (rsi,0))) *)
  0xc4; 0xe2; 0xb3; 0xf6; 0x46; 0x08;
                           (* MULX4 (% rax,% r9) (% rdx,Memop Quadword (%% (rsi,8))) *)
  0x4c; 0x89; 0x4c; 0x24; 0x08;
                           (* MOV (Memop Quadword (%% (rsp,8))) (% r9) *)
  0xc4; 0xe2; 0xab; 0xf6; 0x4e; 0x10;
                           (* MULX4 (% rcx,% r10) (% rdx,Memop Quadword (%% (rsi,16))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0x4c; 0x89; 0x54; 0x24; 0x10;
                           (* MOV (Memop Quadword (%% (rsp,16))) (% r10) *)
  0xc4; 0xe2; 0xa3; 0xf6; 0x46; 0x18;
                           (* MULX4 (% rax,% r11) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd9;
                           (* ADCX (% r11) (% rcx) *)
  0xc4; 0xe2; 0x9b; 0xf6; 0x4e; 0x20;
                           (* MULX4 (% rcx,% r12) (% rdx,Memop Quadword (%% (rsi,32))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xc4; 0xe2; 0x93; 0xf6; 0x46; 0x28;
                           (* MULX4 (% rax,% r13) (% rdx,Memop Quadword (%% (rsi,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADCX (% r13) (% rcx) *)
  0xc4; 0xe2; 0x8b; 0xf6; 0x4e; 0x30;
                           (* MULX4 (% rcx,% r14) (% rdx,Memop Quadword (%% (rsi,48))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xc4; 0x62; 0x83; 0xf6; 0x46; 0x38;
                           (* MULX4 (% r8,% r15) (% rdx,Memop Quadword (%% (rsi,56))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADCX (% r15) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc5;
                           (* ADCX (% r8) (% rbp) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0x48; 0x8b; 0x56; 0x08;  (* MOV (% rdx) (Memop Quadword (%% (rsi,8))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x4e; 0x10;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsi,16))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe1;
                           (* ADOX (% r12) (% rcx) *)
  0x4c; 0x89; 0x5c; 0x24; 0x18;
                           (* MOV (Memop Quadword (%% (rsp,24))) (% r11) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x4e; 0x18;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADOX (% r13) (% rcx) *)
  0x4c; 0x89; 0x64; 0x24; 0x20;
                           (* MOV (Memop Quadword (%% (rsp,32))) (% r12) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x4e; 0x20;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsi,32))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADOX (% r14) (% rcx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x4e; 0x28;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsi,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADOX (% r15) (% rcx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x4e; 0x30;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsi,48))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc1;
                           (* ADOX (% r8) (% rcx) *)
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
  0xc4; 0xe2; 0xfb; 0xf6; 0x4e; 0x18;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADOX (% r14) (% rcx) *)
  0x4c; 0x89; 0x6c; 0x24; 0x28;
                           (* MOV (Memop Quadword (%% (rsp,40))) (% r13) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x4e; 0x20;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsi,32))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADOX (% r15) (% rcx) *)
  0x4c; 0x89; 0x74; 0x24; 0x30;
                           (* MOV (Memop Quadword (%% (rsp,48))) (% r14) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x4e; 0x28;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsi,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc1;
                           (* ADOX (% r8) (% rcx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x4e; 0x30;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsi,48))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc9;
                           (* ADOX (% r9) (% rcx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x4e; 0x38;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsi,56))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd1;
                           (* ADOX (% r10) (% rcx) *)
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
  0xc4; 0xe2; 0xfb; 0xf6; 0x4e; 0x20;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsi,32))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc1;
                           (* ADOX (% r8) (% rcx) *)
  0x4c; 0x89; 0x7c; 0x24; 0x38;
                           (* MOV (Memop Quadword (%% (rsp,56))) (% r15) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x4e; 0x28;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsi,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc9;
                           (* ADOX (% r9) (% rcx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x4e; 0x30;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsi,48))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd1;
                           (* ADOX (% r10) (% rcx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x4e; 0x38;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsi,56))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd9;
                           (* ADOX (% r11) (% rcx) *)
  0x48; 0x8b; 0x56; 0x38;  (* MOV (% rdx) (Memop Quadword (%% (rsi,56))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x4e; 0x20;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsi,32))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe1;
                           (* ADOX (% r12) (% rcx) *)
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
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0x48; 0x8b; 0x16;        (* MOV (% rdx) (Memop Quadword (%% (rsi,0))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0xca;
                           (* MULX4 (% rcx,% rax) (% rdx,% rdx) *)
  0x48; 0x89; 0x04; 0x24;  (* MOV (Memop Quadword (%% (rsp,0))) (% rax) *)
  0x48; 0x8b; 0x44; 0x24; 0x08;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,8))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% rax) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xc1;
                           (* ADOX (% rax) (% rcx) *)
  0x48; 0x89; 0x44; 0x24; 0x08;
                           (* MOV (Memop Quadword (%% (rsp,8))) (% rax) *)
  0x48; 0x8b; 0x44; 0x24; 0x10;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,16))) *)
  0x48; 0x8b; 0x56; 0x08;  (* MOV (% rdx) (Memop Quadword (%% (rsi,8))) *)
  0xc4; 0xe2; 0xeb; 0xf6; 0xca;
                           (* MULX4 (% rcx,% rdx) (% rdx,% rdx) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% rax) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xc2;
                           (* ADOX (% rax) (% rdx) *)
  0x48; 0x89; 0x44; 0x24; 0x10;
                           (* MOV (Memop Quadword (%% (rsp,16))) (% rax) *)
  0x48; 0x8b; 0x44; 0x24; 0x18;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,24))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% rax) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xc1;
                           (* ADOX (% rax) (% rcx) *)
  0x48; 0x89; 0x44; 0x24; 0x18;
                           (* MOV (Memop Quadword (%% (rsp,24))) (% rax) *)
  0x48; 0x8b; 0x44; 0x24; 0x20;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,32))) *)
  0x48; 0x8b; 0x56; 0x10;  (* MOV (% rdx) (Memop Quadword (%% (rsi,16))) *)
  0xc4; 0xe2; 0xeb; 0xf6; 0xca;
                           (* MULX4 (% rcx,% rdx) (% rdx,% rdx) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% rax) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xc2;
                           (* ADOX (% rax) (% rdx) *)
  0x48; 0x89; 0x44; 0x24; 0x20;
                           (* MOV (Memop Quadword (%% (rsp,32))) (% rax) *)
  0x48; 0x8b; 0x44; 0x24; 0x28;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,40))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% rax) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xc1;
                           (* ADOX (% rax) (% rcx) *)
  0x48; 0x89; 0x44; 0x24; 0x28;
                           (* MOV (Memop Quadword (%% (rsp,40))) (% rax) *)
  0x48; 0x8b; 0x44; 0x24; 0x30;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,48))) *)
  0x48; 0x8b; 0x56; 0x18;  (* MOV (% rdx) (Memop Quadword (%% (rsi,24))) *)
  0xc4; 0xe2; 0xeb; 0xf6; 0xca;
                           (* MULX4 (% rcx,% rdx) (% rdx,% rdx) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% rax) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xc2;
                           (* ADOX (% rax) (% rdx) *)
  0x48; 0x89; 0x44; 0x24; 0x30;
                           (* MOV (Memop Quadword (%% (rsp,48))) (% rax) *)
  0x48; 0x8b; 0x44; 0x24; 0x38;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,56))) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% rax) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xc1;
                           (* ADOX (% rax) (% rcx) *)
  0x48; 0x89; 0x44; 0x24; 0x38;
                           (* MOV (Memop Quadword (%% (rsp,56))) (% rax) *)
  0x48; 0x8b; 0x56; 0x20;  (* MOV (% rdx) (Memop Quadword (%% (rsi,32))) *)
  0xc4; 0xe2; 0xeb; 0xf6; 0xca;
                           (* MULX4 (% rcx,% rdx) (% rdx,% rdx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% r8) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc2;
                           (* ADOX (% r8) (% rdx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xc9;
                           (* ADCX (% r9) (% r9) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc9;
                           (* ADOX (% r9) (% rcx) *)
  0x48; 0x8b; 0x56; 0x28;  (* MOV (% rdx) (Memop Quadword (%% (rsi,40))) *)
  0xc4; 0xe2; 0xeb; 0xf6; 0xca;
                           (* MULX4 (% rcx,% rdx) (% rdx,% rdx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xd2;
                           (* ADCX (% r10) (% r10) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd2;
                           (* ADOX (% r10) (% rdx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADCX (% r11) (% r11) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd9;
                           (* ADOX (% r11) (% rcx) *)
  0x48; 0x8b; 0x56; 0x30;  (* MOV (% rdx) (Memop Quadword (%% (rsi,48))) *)
  0xc4; 0xe2; 0xeb; 0xf6; 0xca;
                           (* MULX4 (% rcx,% rdx) (% rdx,% rdx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xe4;
                           (* ADCX (% r12) (% r12) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe2;
                           (* ADOX (% r12) (% rdx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xed;
                           (* ADCX (% r13) (% r13) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADOX (% r13) (% rcx) *)
  0x48; 0x8b; 0x56; 0x38;  (* MOV (% rdx) (Memop Quadword (%% (rsi,56))) *)
  0xc4; 0x62; 0xeb; 0xf6; 0xfa;
                           (* MULX4 (% r15,% rdx) (% rdx,% rdx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xf6;
                           (* ADCX (% r14) (% r14) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf2;
                           (* ADOX (% r14) (% rdx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xfd;
                           (* ADCX (% r15) (% rbp) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfd;
                           (* ADOX (% r15) (% rbp) *)
  0x48; 0x8b; 0x56; 0x40;  (* MOV (% rdx) (Memop Quadword (%% (rsi,64))) *)
  0x48; 0x89; 0xd5;        (* MOV (% rbp) (% rdx) *)
  0x48; 0x0f; 0xaf; 0xed;  (* IMUL (% rbp) (% rbp) *)
  0x48; 0x01; 0xd2;        (* ADD (% rdx) (% rdx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x0e;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc9;
                           (* ADOX (% r9) (% rcx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x4e; 0x08;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsi,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd1;
                           (* ADOX (% r10) (% rcx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x4e; 0x10;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsi,16))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd9;
                           (* ADOX (% r11) (% rcx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x4e; 0x18;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe1;
                           (* ADOX (% r12) (% rcx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x4e; 0x20;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsi,32))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADOX (% r13) (% rcx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x4e; 0x28;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsi,40))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADOX (% r14) (% rcx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x4e; 0x30;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsi,48))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADOX (% r15) (% rcx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x4e; 0x38;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsi,56))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADOX (% rbp) (% rcx) *)
  0x48; 0x83; 0xd5; 0x00;  (* ADC (% rbp) (Imm8 (word 0)) *)
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
  0x49; 0x0f; 0xac; 0xef; 0x09;
                           (* SHRD (% r15) (% rbp) (Imm8 (word 9)) *)
  0x48; 0xc1; 0xed; 0x09;  (* SHR (% rbp) (Imm8 (word 9)) *)
  0x48; 0x01; 0xc5;        (* ADD (% rbp) (% rax) *)
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
  0x48; 0x81; 0xd5; 0x00; 0xfe; 0xff; 0xff;
                           (* ADC (% rbp) (Imm32 (word 4294966784)) *)
  0xf5;                    (* CMC *)
  0x49; 0x83; 0xd8; 0x00;  (* SBB (% r8) (Imm8 (word 0)) *)
  0x49; 0x83; 0xd9; 0x00;  (* SBB (% r9) (Imm8 (word 0)) *)
  0x49; 0x83; 0xda; 0x00;  (* SBB (% r10) (Imm8 (word 0)) *)
  0x49; 0x83; 0xdb; 0x00;  (* SBB (% r11) (Imm8 (word 0)) *)
  0x49; 0x83; 0xdc; 0x00;  (* SBB (% r12) (Imm8 (word 0)) *)
  0x49; 0x83; 0xdd; 0x00;  (* SBB (% r13) (Imm8 (word 0)) *)
  0x49; 0x83; 0xde; 0x00;  (* SBB (% r14) (Imm8 (word 0)) *)
  0x49; 0x83; 0xdf; 0x00;  (* SBB (% r15) (Imm8 (word 0)) *)
  0x48; 0x83; 0xdd; 0x00;  (* SBB (% rbp) (Imm8 (word 0)) *)
  0x48; 0x81; 0xe5; 0xff; 0x01; 0x00; 0x00;
                           (* AND (% rbp) (Imm32 (word 511)) *)
  0x4c; 0x89; 0xc0;        (* MOV (% rax) (% r8) *)
  0x4d; 0x0f; 0xac; 0xc8; 0x37;
                           (* SHRD (% r8) (% r9) (Imm8 (word 55)) *)
  0x4c; 0x89; 0x07;        (* MOV (Memop Quadword (%% (rdi,0))) (% r8) *)
  0x4d; 0x0f; 0xac; 0xd1; 0x37;
                           (* SHRD (% r9) (% r10) (Imm8 (word 55)) *)
  0x4c; 0x89; 0x4f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% r9) *)
  0x4d; 0x0f; 0xac; 0xda; 0x37;
                           (* SHRD (% r10) (% r11) (Imm8 (word 55)) *)
  0x48; 0xc1; 0xe0; 0x09;  (* SHL (% rax) (Imm8 (word 9)) *)
  0x4c; 0x89; 0x57; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r10) *)
  0x4d; 0x0f; 0xac; 0xe3; 0x37;
                           (* SHRD (% r11) (% r12) (Imm8 (word 55)) *)
  0x4c; 0x89; 0x5f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r11) *)
  0x4d; 0x0f; 0xac; 0xec; 0x37;
                           (* SHRD (% r12) (% r13) (Imm8 (word 55)) *)
  0x4c; 0x89; 0x67; 0x20;  (* MOV (Memop Quadword (%% (rdi,32))) (% r12) *)
  0x48; 0x09; 0xc5;        (* OR (% rbp) (% rax) *)
  0x4d; 0x0f; 0xac; 0xf5; 0x37;
                           (* SHRD (% r13) (% r14) (Imm8 (word 55)) *)
  0x4c; 0x89; 0x6f; 0x28;  (* MOV (Memop Quadword (%% (rdi,40))) (% r13) *)
  0x4d; 0x0f; 0xac; 0xfe; 0x37;
                           (* SHRD (% r14) (% r15) (Imm8 (word 55)) *)
  0x4c; 0x89; 0x77; 0x30;  (* MOV (Memop Quadword (%% (rdi,48))) (% r14) *)
  0x49; 0x0f; 0xac; 0xef; 0x37;
                           (* SHRD (% r15) (% rbp) (Imm8 (word 55)) *)
  0x4c; 0x89; 0x7f; 0x38;  (* MOV (Memop Quadword (%% (rdi,56))) (% r15) *)
  0x48; 0xc1; 0xed; 0x37;  (* SHR (% rbp) (Imm8 (word 55)) *)
  0x48; 0x89; 0x6f; 0x40;  (* MOV (Memop Quadword (%% (rdi,64))) (% rbp) *)
  0x48; 0x83; 0xc4; 0x40;  (* ADD (% rsp) (Imm8 (word 64)) *)
  0x41; 0x5f;              (* POP (% r15) *)
  0x41; 0x5e;              (* POP (% r14) *)
  0x41; 0x5d;              (* POP (% r13) *)
  0x41; 0x5c;              (* POP (% r12) *)
  0x5d;                    (* POP (% rbp) *)
  0xc3                     (* RET *)
];;

let bignum_montsqr_p521_tmc = define_trimmed "bignum_montsqr_p521_tmc" bignum_montsqr_p521_mc;;

let BIGNUM_MONTSQR_P521_EXEC = X86_MK_CORE_EXEC_RULE bignum_montsqr_p521_tmc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_521 = new_definition `p_521 = 6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057151`;;

let P_521 = prove
 (`p_521 = 2 EXP 521 - 1`,
  REWRITE_TAC[p_521] THEN CONV_TAC NUM_REDUCE_CONV);;

let P_521_AS_WORDLIST = prove
 (`p_521 =
   bignum_of_wordlist
    [word_not(word 0);word_not(word 0);word_not(word 0);word_not(word 0);
     word_not(word 0);word_not(word 0);word_not(word 0);word_not(word 0);
     word(0x1FF)]`,
  REWRITE_TAC[p_521; bignum_of_wordlist] THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV);;

let BIGNUM_FROM_MEMORY_EQ_P521 = prove
 (`bignum_of_wordlist[n0;n1;n2;n3;n4;n5;n6;n7;n8] = p_521 <=>
   (!i. i < 64
        ==> bit i n0 /\ bit i n1 /\ bit i n2 /\ bit i n3 /\
            bit i n4 /\ bit i n5 /\ bit i n6 /\ bit i n7) /\
   (!i. i < 9 ==> bit i n8) /\ (!i. i < 64 ==> 9 <= i ==> ~bit i n8)`,
  REWRITE_TAC[P_521_AS_WORDLIST; BIGNUM_OF_WORDLIST_EQ] THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; DIMINDEX_64] THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV THEN
  CONV_TAC CONJ_ACI_RULE);;

let BIGNUM_FROM_MEMORY_LE_P521 = prove
 (`bignum_of_wordlist[n0;n1;n2;n3;n4;n5;n6;n7;n8] <= p_521 <=>
   !i. i < 64 ==> 9 <= i ==> ~bit i n8`,
  SIMP_TAC[P_521; ARITH_RULE `p_521 = 2 EXP 521 - 1 ==>
    (n <= p_521 <=> n DIV 2 EXP (8 * 64) < 2 EXP 9)`] THEN
  REWRITE_TAC[TOP_DEPTH_CONV num_CONV `8`; MULT_CLAUSES; EXP_ADD] THEN
  REWRITE_TAC[GSYM DIV_DIV; BIGNUM_OF_WORDLIST_DIV; EXP; DIV_1] THEN
  REWRITE_TAC[BIGNUM_OF_WORDLIST_SING; GSYM UPPER_BITS_ZERO] THEN
  MP_TAC(ISPEC `n8:int64` BIT_TRIVIAL) THEN REWRITE_TAC[DIMINDEX_64] THEN
  MESON_TAC[NOT_LE]);;

let BIGNUM_FROM_MEMORY_LT_P521 = prove
 (`bignum_of_wordlist[n0;n1;n2;n3;n4;n5;n6;n7;n8] < p_521 <=>
   (!i. i < 64 ==> 9 <= i ==> ~bit i n8) /\
   ~((!i. i < 64
          ==> bit i n0 /\ bit i n1 /\ bit i n2 /\ bit i n3 /\
              bit i n4 /\ bit i n5 /\ bit i n6 /\ bit i n7) /\
     (!i. i < 9 ==> bit i n8))`,
  GEN_REWRITE_TAC LAND_CONV [LT_LE] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_EQ_P521; BIGNUM_FROM_MEMORY_LE_P521] THEN
  MESON_TAC[]);;

let BIGNUM_MONTSQR_P521_CORRECT = time prove
 (`!z x n pc stackpointer.
        ALL (nonoverlapping (stackpointer,64))
            [(word pc,0x515); (z,8 * 9); (x,8 * 9)] /\
        nonoverlapping (z,8 * 9) (word pc,0x515)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST bignum_montsqr_p521_tmc) /\
                  read RIP s = word(pc + 0xd) /\
                  read RSP s = stackpointer /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,9) s = n)
             (\s. read RIP s = word (pc + 0x507) /\
                  (n < p_521
                   ==> bignum_from_memory (z,9) s =
                       (inverse_mod p_521 (2 EXP 576) * n EXP 2) MOD p_521))
          (MAYCHANGE [RIP; RAX; RBP; RCX; RDX;
                      R8; R9; R10; R11; R12; R13; R14; R15] ,,
           MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [memory :> bignum(z,9);
                      memory :> bytes(stackpointer,64)])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `n:num`; `pc:num`; `stackpointer:int64`] THEN
  REWRITE_TAC[ALL; C_ARGUMENTS; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the n < p_521 assumption for simplicity's sake ***)

  ASM_CASES_TAC `n < p_521` THENL
   [ASM_REWRITE_TAC[]; X86_SIM_TAC BIGNUM_MONTSQR_P521_EXEC (1--243)] THEN

  (*** Digitize, deduce the bound on the top word specifically ***)

  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_LDIGITIZE_TAC "n_" `read (memory :> bytes (x,8 * 9)) s0` THEN
  SUBGOAL_THEN `n DIV 2 EXP 512 < 2 EXP 9` MP_TAC THENL
   [UNDISCH_TAC `n < p_521` THEN REWRITE_TAC[p_521] THEN ARITH_TAC;
    FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (funpow 3 LAND_CONV) [SYM th]) THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV)) THEN
    DISCH_TAC] THEN

  (*** Simulate core squaring, with manual tweaks for small high digit ***)

  X86_ACCSTEPS_TAC BIGNUM_MONTSQR_P521_EXEC (1--160) (1--160) THEN
  X86_ACCSTEPS_TAC BIGNUM_MONTSQR_P521_EXEC (165--189) (161--189) THEN
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
  REABBREV_TAC `h8 = read RBP s189` THEN POP_ASSUM SUBST_ALL_TAC THEN

  (*** Show that the core squaring operation is correct ***)

  SUBGOAL_THEN
   `2 EXP 512 * bignum_of_wordlist[h0;h1;h2;h3;h4;h5;h6;h7;h8] +
    bignum_from_memory(stackpointer,8) s189 =
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

  X86_STEPS_TAC BIGNUM_MONTSQR_P521_EXEC (190--201) THEN

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
  SUBGOAL_THEN
   `(inverse_mod p_521 (2 EXP 576) * n EXP 2) MOD p_521 =
    (inverse_mod p_521 (2 EXP 576) * (h + l)) MOD p_521` SUBST1_TAC THENL
   [SUBST1_TAC(SYM(SPECL
     [`n EXP 2`; `2 EXP 521`] (CONJUNCT2 DIVISION_SIMP))) THEN
    ASM_REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC(NUMBER_RULE
     `(e == 1) (mod p) ==> (i * (e * h + l) == i * (h + l)) (mod p)`) THEN
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

  X86_ACCSTEPS_TAC BIGNUM_MONTSQR_P521_EXEC (202--211) (202--211) THEN
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
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN

  (*** The correction ***)

  X86_ACCSTEPS_TAC BIGNUM_MONTSQR_P521_EXEC (213--221) (212--243) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `bignum_of_wordlist
     [sum_s213;sum_s214;sum_s215;sum_s216;
      sum_s217;sum_s218;sum_s219;sum_s220;
      word_and sum_s221 (word 511)] =
    (h + l) MOD p_521`
   MP_TAC THENL
   [CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
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
      SIMP_TAC[REAL_OF_NUM_CLAUSES; REAL_OF_NUM_SUB;
               COND_SWAP; GSYM NOT_LE] THEN
      MESON_TAC[]];
    ALL_TAC] THEN

  (*** The final rotation for the Montgomery ingredient ***)

  CONV_TAC(RAND_CONV(LAND_CONV BIGNUM_LEXPAND_CONV)) THEN
  ASM_REWRITE_TAC[DIMINDEX_64] THEN
  CONV_TAC(BINOP_CONV SYM_CONV) THEN REWRITE_TAC[MOD_UNIQUE] THEN
  REWRITE_TAC[p_521] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_EQ_CONV) THEN
  REWRITE_TAC[GSYM p_521] THEN
  MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
   [REWRITE_TAC[BIGNUM_FROM_MEMORY_LT_P521] THEN
    CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[BIT_WORD_USHR; BIT_WORD_AND; BIT_WORD_OR; BIT_WORD_SHL;
             BIT_WORD_JOIN; BIT_WORD_SUBWORD; DIMINDEX_64; DIMINDEX_128] THEN
    CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC WORD_RED_CONV)) THEN
    GEN_REWRITE_TAC I [CONTRAPOS_THM] THEN
    CONV_TAC(BINOP_CONV CONJ_CANON_CONV) THEN
    DISCH_THEN ACCEPT_TAC;
    MATCH_MP_TAC(NUMBER_RULE
     `!a. (a * i == 1) (mod p) /\ (a * q == n) (mod p)
          ==> (x == n) (mod p) ==> (i * x == q) (mod p)`) THEN
    EXISTS_TAC `2 EXP 576` THEN
    REWRITE_TAC[INVERSE_MOD_RMUL_EQ; COPRIME_REXP; COPRIME_2; p_521] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[REAL_CONGRUENCE] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[val_def; DIMINDEX_64; bignum_of_wordlist] THEN
    REWRITE_TAC[ARITH_RULE `i < 64 <=> 0 <= i /\ i <= 63`] THEN
    REWRITE_TAC[GSYM IN_NUMSEG; IN_GSPEC] THEN
    REWRITE_TAC[BIT_WORD_USHR; BIT_WORD_AND; BIT_WORD_OR; BIT_WORD_SHL;
             BIT_WORD_JOIN; BIT_WORD_SUBWORD; DIMINDEX_64; DIMINDEX_128] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC(ONCE_DEPTH_CONV EXPAND_NSUM_CONV) THEN
    CONV_TAC(DEPTH_CONV
     (NUM_RED_CONV ORELSEC WORD_RED_CONV ORELSEC
      GEN_REWRITE_CONV I [BITVAL_CLAUSES])) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REAL_INTEGER_TAC]);;

let BIGNUM_MONTSQR_P521_NOIBT_SUBROUTINE_CORRECT = prove
 (`!z x n pc stackpointer returnaddress.
        ALL (nonoverlapping (z,8 * 9))
            [(word pc,LENGTH bignum_montsqr_p521_tmc); (word_sub stackpointer (word 104),112)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 104),104))
            [(word pc,LENGTH bignum_montsqr_p521_tmc); (x,8 * 9)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_montsqr_p521_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,9) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (n < p_521
                   ==> bignum_from_memory (z,9) s =
                       (inverse_mod p_521 (2 EXP 576) * n EXP 2) MOD p_521))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 9);
                     memory :> bytes(word_sub stackpointer (word 104),104)])`,
  X86_PROMOTE_RETURN_STACK_TAC
   bignum_montsqr_p521_tmc BIGNUM_MONTSQR_P521_CORRECT
   `[RBP; R12; R13; R14; R15]` 104);;

let BIGNUM_MONTSQR_P521_SUBROUTINE_CORRECT = prove
 (`!z x n pc stackpointer returnaddress.
        ALL (nonoverlapping (z,8 * 9))
            [(word pc,LENGTH bignum_montsqr_p521_mc); (word_sub stackpointer (word 104),112)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 104),104))
            [(word pc,LENGTH bignum_montsqr_p521_mc); (x,8 * 9)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_montsqr_p521_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,9) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (n < p_521
                   ==> bignum_from_memory (z,9) s =
                       (inverse_mod p_521 (2 EXP 576) * n EXP 2) MOD p_521))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 9);
                     memory :> bytes(word_sub stackpointer (word 104),104)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_MONTSQR_P521_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_montsqr_p521_windows_mc = define_from_elf
   "bignum_montsqr_p521_windows_mc" "x86/p521/bignum_montsqr_p521.obj";;

let bignum_montsqr_p521_windows_tmc = define_trimmed "bignum_montsqr_p521_windows_tmc" bignum_montsqr_p521_windows_mc;;

let BIGNUM_MONTSQR_P521_NOIBT_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!z x n pc stackpointer returnaddress.
        ALL (nonoverlapping (z,8 * 9))
            [(word pc,LENGTH bignum_montsqr_p521_windows_tmc); (word_sub stackpointer (word 120),128)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 120),120))
            [(word pc,LENGTH bignum_montsqr_p521_windows_tmc); (x,8 * 9)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_montsqr_p521_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,9) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (n < p_521
                   ==> bignum_from_memory (z,9) s =
                       (inverse_mod p_521 (2 EXP 576) * n EXP 2) MOD p_521))
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 9);
                     memory :> bytes(word_sub stackpointer (word 120),120)])`,
  WINDOWS_X86_WRAP_STACK_TAC
   bignum_montsqr_p521_windows_tmc bignum_montsqr_p521_tmc
   BIGNUM_MONTSQR_P521_CORRECT `[RBP; R12; R13; R14; R15]` 104);;

let BIGNUM_MONTSQR_P521_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!z x n pc stackpointer returnaddress.
        ALL (nonoverlapping (z,8 * 9))
            [(word pc,LENGTH bignum_montsqr_p521_windows_mc); (word_sub stackpointer (word 120),128)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 120),120))
            [(word pc,LENGTH bignum_montsqr_p521_windows_mc); (x,8 * 9)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_montsqr_p521_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,9) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (n < p_521
                   ==> bignum_from_memory (z,9) s =
                       (inverse_mod p_521 (2 EXP 576) * n EXP 2) MOD p_521))
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 9);
                     memory :> bytes(word_sub stackpointer (word 120),120)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_MONTSQR_P521_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

