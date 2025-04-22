(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* ARM instruction decoding.                                                 *)
(* ========================================================================= *)

let XREG_SP = new_definition `XREG_SP n = registers :> element n`;;
let WREG_SP = new_definition `WREG_SP n = XREG_SP n :> zerotop_32`;;
let XREG' = new_definition `XREG' (n:5 word) = XREG (val n)`;;
let WREG' = new_definition `WREG' (n:5 word) = WREG (val n)`;;
let QREG' = new_definition `QREG' (n:5 word) = QREG (val n)`;;
let DREG' = new_definition `DREG' (n:5 word) = DREG (val n)`;;

let QLANE = define
 `QLANE reg 8 ix = QREG' reg :> LANE_B ix /\
  QLANE reg 16 ix = QREG' reg :> LANE_H ix /\
  QLANE reg 32 ix = QREG' reg :> LANE_S ix /\
  QLANE reg 64 ix = QREG' reg :> LANE_D ix`;;

let arm_logop = new_definition `arm_logop (opc:2 word) N
    (Rd:(armstate,N word)component) Rn Rm =
  bitmatch opc with
  | [0:2] -> SOME ((if N then arm_BIC else arm_AND) Rd Rn Rm)
  | [1:2] -> SOME ((if N then arm_ORN else arm_ORR) Rd Rn Rm)
  | [2:2] -> SOME ((if N then arm_EON else arm_EOR) Rd Rn Rm)
  | [3:2] -> SOME ((if N then arm_BICS else arm_ANDS) Rd Rn Rm)`;;

let arm_adcop = new_definition `arm_adcop op S:
    (armstate,N word)component->(armstate,N word)component->
    (armstate,N word)component->armstate->armstate->bool =
  if op then if S then arm_SBCS else arm_SBC
        else if S then arm_ADCS else arm_ADC`;;

let arm_addop = new_definition `arm_addop op S:
    (armstate,N word)component->(armstate,N word)component->
    (armstate,N word)component->armstate->armstate->bool =
  if op then if S then arm_SUBS else arm_SUB
        else if S then arm_ADDS else arm_ADD`;;

let arm_movop = new_definition `arm_movop (opc:2 word)
    (Rd:(armstate,N word)component) imm pos =
  bitmatch opc with
  | [0:2] -> SOME (arm_MOVN Rd imm pos)
  | [2:2] -> SOME (arm_MOVZ Rd imm pos)
  | [3:2] -> SOME (arm_MOVK Rd imm pos)
  | _ -> NONE`;;

let arm_csop = new_definition `arm_csop op o2:
    (armstate,N word)component->(armstate,N word)component->
    (armstate,N word)component->condition->armstate->armstate->bool =
  if op then if o2 then arm_CSNEG else arm_CSINV
        else if o2 then arm_CSINC else arm_CSEL`;;

let arm_ccop = new_definition
 `arm_ccop op (Rn:(armstate,N word)component) Rm nzcv cond =
   if op then SOME(arm_CCMP Rn Rm nzcv cond)
   else SOME(arm_CCMN Rn Rm nzcv cond)`;;

let arm_lsvop = new_definition `arm_lsvop (op2:2 word)
    (Rd:(armstate,N word)component) Rn Rm =
  bitmatch op2 with
  | [0:2] -> SOME (arm_LSLV Rd Rn Rm)
  | [1:2] -> SOME (arm_LSRV Rd Rn Rm)
  | [2:2] -> SOME (arm_ASRV Rd Rn Rm)
  | [3:2] -> SOME (arm_RORV Rd Rn Rm)`;;

let arm_bfmop = new_definition `arm_bfmop (u:bool)
    (Rd:(armstate,N word)component) Rn immr imms =
  if u then SOME(arm_UBFM Rd Rn immr imms)
  else SOME(arm_SBFM Rd Rn immr imms)`;;

let arm_ldst = new_definition `arm_ldst ld x Rt =
  if x then (if ld then arm_LDR else arm_STR) (XREG' Rt)
       else (if ld then arm_LDR else arm_STR) (WREG' Rt)`;;
let arm_ldst_q = new_definition `arm_ldst_q ld Rt =
  (if ld then arm_LDR else arm_STR) (QREG' Rt)`;;
let arm_ldst_d = new_definition `arm_ldst_d ld Rt =
  (if ld then arm_LDR else arm_STR) (DREG' Rt)`;;
let arm_ldstb = new_definition `arm_ldstb ld Rt =
  (if ld then arm_LDRB else arm_STRB) (WREG' Rt)`;;
let arm_ldstp = new_definition `arm_ldstp ld x Rt Rt2 =
  if x then (if ld then arm_LDP else arm_STP) (XREG' Rt) (XREG' Rt2)
       else (if ld then arm_LDP else arm_STP) (WREG' Rt) (WREG' Rt2)`;;
let arm_ldstp_d = new_definition `arm_ldstp_d ld Rt Rt2 =
  (if ld then arm_LDP else arm_STP) (DREG' Rt) (DREG' Rt2)`;;
let arm_ldstp_q = new_definition `arm_ldstp_q ld Rt Rt2 =
  (if ld then arm_LDP else arm_STP) (QREG' Rt) (QREG' Rt2)`;;
let arm_ldstp_2q = new_definition `arm_ldstp_2q ld Rt =
  let Rtt:(5 word) = word ((val Rt + 1) MOD 32) in
  (if ld then arm_LDP else arm_STP) (QREG' Rt) (QREG' Rtt)`;;
let arm_ldst2 = new_definition `arm_ldst2 ld Rt =
  let Rtt:(5 word) = word ((val Rt + 1) MOD 32) in
  (if ld then arm_LD2 else arm_ST2) (QREG' Rt) (QREG' Rtt)`;;

(* The 'AdvSimdExpandImm' shared function in the A64 ISA specification.
   This definition takes one 8-bit word and expands it to 64 bit according to
   op and cmode. *)
let arm_adv_simd_expand_imm = new_definition
  `(arm_adv_simd_expand_imm:(8)word->(1)word->(4)word->((64)word)option)
      abcdefgh op cmode =
    if val cmode = 14 /\ val op = 1 then
      let rep8 = \(x:bool). if x then (word 255:(8)word) else (word 0) in
      let res: (64)word =
        word_join (rep8 (bit 7 abcdefgh))
          (word_join (rep8 (bit 6 abcdefgh))
            (word_join (rep8 (bit 5 abcdefgh))
              (word_join (rep8 (bit 4 abcdefgh))
                (word_join (rep8 (bit 3 abcdefgh))
                  (word_join (rep8 (bit 2 abcdefgh))
                    (word_join (rep8 (bit 1 abcdefgh))
                               (rep8 (bit 0 abcdefgh)):(16)word)
                  :(24)word)
                :(32)word)
              :(40)word)
            :(48)word)
          :(56)word) in
      SOME res
    else if cmode = word 0b1000 \/ cmode = word 0b1001 then
      SOME(word_duplicate (word_join (word 0:byte) abcdefgh:int16))
    else if cmode = word 0b1010 \/ cmode = word 0b1011 then
       SOME(word_duplicate (word_join abcdefgh (word 0:byte):int16))
    else // Other cases are uncovered.
      NONE`;;

let decode_bitmask = new_definition `!N immr imms.
  decode_bitmask (N:bool) (immr:6 word) (imms:6 word):(N word)option =
  let len = 6 - word_clz (word_join (word1 N) (word_not imms):7 word) in
  if len >= 1 /\ (N ==> dimindex(:N) = 64) then
    let size = 2 EXP len in
    let S = val imms MOD size in
    if S = 2 EXP len - 1 then NONE else
    SOME (word_of_bits {i | (i + val immr) MOD size <= S})
  else NONE`;;

let decode_shift = new_definition
 `decode_shift (sty:2 word) =
    bitmatch sty with
      [0b00:2] -> LSL
    | [0b01:2] -> LSR
    | [0b10:2] -> ASR
    | [0b11:2] -> ROR`;;

let decode_extendtype = new_definition
 `decode_extendtype (ety:3 word) =
    bitmatch ety with
      [0b000:3] -> UXTB
    | [0b001:3] -> UXTH
    | [0b010:3] -> UXTW
    | [0b011:3] -> UXTX
    | [0b100:3] -> SXTB
    | [0b101:3] -> SXTH
    | [0b110:3] -> SXTW
    | [0b111:3] -> SXTX`;;

(* Decodes the 4-byte word w.
   To see the instruction's official bit formats, you will want to read the
   "Arm A64 Instruction Set Architecture" document from online. *)
let decode = new_definition `!w:int32. decode w =
  bitmatch w:int32 with
  | [sf; op; S; 0b11010000:8; Rm:5; 0:6; Rn:5; Rd:5] ->
    SOME (if sf then arm_adcop op S (XREG' Rd) (XREG' Rn) (XREG' Rm)
                else arm_adcop op S (WREG' Rd) (WREG' Rn) (WREG' Rm))
  | [sf; op; S; 0b100010:6; sh; imm12:12; Rn:5; Rd:5] ->
    let val = if sh then val imm12 * 2 EXP 12 else val imm12 in
    SOME (if sf
      then arm_addop op S (if S then XREG' Rd else XREG_SP Rd)
                          (XREG_SP Rn) (rvalue (word val))
      else arm_addop op S (if S then WREG' Rd else WREG_SP Rd)
                          (WREG_SP Rn) (rvalue (word val)))
  | [sf; op; S; 0b01011:5; sty:2; 0:1; Rm:5; sam:6; Rn:5; Rd:5] ->
    if sty = word 0b11 then NONE
    else if sf then
       SOME(arm_addop op S (XREG' Rd) (XREG' Rn)
                           (Shiftedreg (XREG' Rm) (decode_shift sty) (val sam)))
    else if val sam < 32 then
       SOME(arm_addop op S (WREG' Rd) (WREG' Rn)
                           (Shiftedreg (WREG' Rm) (decode_shift sty) (val sam)))
    else NONE
  | [sf; op; S; 0b01011001:8; Rm:5; option:3; imm3:3; Rn:5; Rd:5] ->
    let sam = val imm3 in
    let ety = decode_extendtype option in
    if sam > 4 then NONE
    else if sf then
       if option = word 0b011 \/ option = word 0b111 then
         SOME(arm_addop op S (if S then XREG' Rd else XREG_SP Rd) (XREG_SP Rn)
                 (Shiftedreg (Extendedreg (XREG' Rm) ety) LSL sam))
       else
         SOME(arm_addop op S (if S then XREG' Rd else XREG_SP Rd) (XREG_SP Rn)
                 (Shiftedreg (Extendedreg (WREG' Rm) ety) LSL sam))
    else
       SOME(arm_addop op S (if S then WREG' Rd else WREG_SP Rd) (WREG_SP Rn)
               (Shiftedreg (Extendedreg (WREG' Rm) ety) LSL sam))
  | [sf; opc:2; 0b100100:6; N; immr:6; imms:6; Rn:5; Rd:5] ->
    if sf then
      decode_bitmask N immr imms >>= \imm.
      arm_logop opc F
       (if opc = word 3 then XREG' Rd else XREG_SP Rd)
       (XREG' Rn) (rvalue imm)
    else if N then NONE else
      decode_bitmask N immr imms >>= \imm.
      arm_logop opc F
       (if opc = word 3 then WREG' Rd else WREG_SP Rd)
       (WREG' Rn) (rvalue imm)
  | [op; 0b00101:5; imm26:26] ->
    SOME ((if op then arm_BL else arm_B) (word (val imm26 * 4)))
  | [0b01010100:8; imm19:19; 0:1; cond:4] ->
    SOME (arm_Bcond (Condition cond) (word (val imm19 * 4)))
  | [sf; 0b011010:6; op; imm19:19; Rt:5] ->
    SOME ((if sf then (if op then arm_CBNZ else arm_CBZ) (XREG' Rt)
                 else (if op then arm_CBNZ else arm_CBZ) (WREG' Rt))
      (word (val imm19 * 4)))
  | [sf; op; 0b011010100:9; Rm:5; cond:4; 0:1; o2; Rn:5; Rd:5] ->
    SOME ((if sf
      then arm_csop op o2 (XREG' Rd) (XREG' Rn) (XREG' Rm)
      else arm_csop op o2 (WREG' Rd) (WREG' Rn) (WREG' Rm)) (Condition cond))
  | [sf; op; 0b111010010:9; Rm:5; cond:4; 0b00:2; Rn:5; 0b0:1; nzcv:4] ->
    if sf then arm_ccop op (XREG' Rn) (XREG' Rm) nzcv (Condition cond)
    else arm_ccop op (WREG' Rn) (WREG' Rm) nzcv (Condition cond)
  | [sf; op; 0b111010010:9; imm5:5; cond:4; 0b10:2; Rn:5; 0b0:1; nzcv:4] ->
    if sf then arm_ccop op (XREG' Rn) (rvalue(word_zx imm5)) nzcv (Condition cond)
    else arm_ccop op (WREG' Rn) (rvalue(word_zx imm5)) nzcv (Condition cond)
  | [sf; opc:2; 0b01010:5; sty:2; N; Rm:5; sam:6; Rn:5; Rd:5] ->
    if sf then
       arm_logop opc N (XREG' Rd) (XREG' Rn)
                       (Shiftedreg (XREG' Rm) (decode_shift sty) (val sam))
    else if val sam < 32 then
       arm_logop opc N (WREG' Rd) (WREG' Rn)
                       (Shiftedreg (WREG' Rm) (decode_shift sty) (val sam))
    else NONE
  | [sf; opc:2; 0b100101:6; hw:2; imm16:16; Rd:5] ->
    if sf then arm_movop opc (XREG' Rd) imm16 (val hw * 16)
          else if val hw >= 2 then NONE else
               arm_movop opc (WREG' Rd) imm16 (val hw * 16)
  | [sf; 0b00100111:8; N; 0:1; Rm:5; imms:6; Rn:5; Rd:5] ->
    if ~(sf <=> N) then NONE
    else if sf then SOME (arm_EXTR (XREG' Rd) (XREG' Rn) (XREG' Rm) (val imms))
    else if val imms >= 32 then NONE
    else SOME (arm_EXTR (WREG' Rd) (WREG' Rn) (WREG' Rm) (val imms))
  | [sf; 0b0011010110:10; Rm:5; 0b0010:4; op2:2; Rn:5; Rd:5] ->
    if sf then arm_lsvop op2 (XREG' Rd) (XREG' Rn) (XREG' Rm)
          else arm_lsvop op2 (WREG' Rd) (WREG' Rn) (WREG' Rm)
  | [sf; uopc; 0b0100110:7; N; immr:6; imms:6; Rn:5; Rd:5] ->
    if ~(sf <=> N) then NONE
    else if sf then arm_bfmop uopc (XREG' Rd) (XREG' Rn) (val immr) (val imms)
    else if val immr >= 32 \/ val imms >= 32 then NONE
    else arm_bfmop uopc (WREG' Rd) (WREG' Rn) (val immr) (val imms)
  | [sf; 0b01100110:8; N; immr:6; imms:6; Rn:5; Rd:5] ->
    if ~(sf <=> N) then NONE
    else if sf then SOME(arm_BFM (XREG' Rd) (XREG' Rn) (val immr) (val imms))
    else if val immr >= 32 \/ val imms >= 32 then NONE
    else SOME(arm_BFM (WREG' Rd) (WREG' Rn) (val immr) (val imms))
  | [sf; 0b101101011000000000100:21; Rn:5; Rd:5] ->
    SOME (if sf then arm_CLZ (XREG' Rd) (XREG' Rn)
          else arm_CLZ (WREG' Rd) (WREG' Rn))
  | [sf; 0b0011011000:10; Rm:5; o0; Ra:5; Rn:5; Rd:5] ->
    SOME (if sf then (if o0 then arm_MSUB else arm_MADD)
                  (XREG' Rd) (XREG' Rn) (XREG' Rm) (XREG' Ra)
                else (if o0 then arm_MSUB else arm_MADD)
                  (WREG' Rd) (WREG' Rn) (WREG' Rm) (WREG' Ra))
  | [0b1101011001011111000000:22; Rn:5; 0:5] ->
    SOME (arm_RET (XREG' Rn))
  | [0b10011011010:11; Rm:5; 0b011111:6; Rn:5; Rd:5] ->
    SOME (arm_SMULH (XREG' Rd) (XREG' Rn) (XREG' Rm))
  | [0b10011011110:11; Rm:5; 0b011111:6; Rn:5; Rd:5] ->
    SOME (arm_UMULH (XREG' Rd) (XREG' Rn) (XREG' Rm))
  | [0b10011011101:11; Rm:5; o0; Ra:5; Rn:5; Rd:5] ->
    SOME ((if o0 then arm_UMSUBL else arm_UMADDL)
          (XREG' Rd) (WREG' Rn) (WREG' Rm) (XREG' Ra))
  | [0:1; immlo:2; 0b10000:5; immhi:19; Rd:5] ->
    SOME (arm_ADR (XREG' Rd) (word_join immhi immlo))
  | [1:1; immlo:2; 0b10000:5; immhi:19; Rd:5] ->
    SOME (arm_ADRP (XREG' Rd) (word_join immhi immlo))
  | [1:1; x; 0b1110000:7; ld; 0:1; imm9:9; 0b01:2; Rn:5; Rt:5] ->
    SOME (arm_ldst ld x Rt (XREG_SP Rn) (Postimmediate_Offset (word_sx imm9)))
  | [1:1; x; 0b1110000:7; ld; 0:1; imm9:9; 0b11:2; Rn:5; Rt:5] ->
    SOME (arm_ldst ld x Rt (XREG_SP Rn) (Preimmediate_Offset (word_sx imm9)))
  | [1:1; x; 0b1110010:7; ld; imm12:12; Rn:5; Rt:5] ->
    SOME (arm_ldst ld x Rt (XREG_SP Rn)
      (Immediate_Offset (word (val imm12 * if x then 8 else 4))))
  | [1:1; x; 0b1110000:7; ld; 1:1; Rm:5; 0b011:3; S; 0b10:2; Rn:5; Rt:5] ->
    SOME (arm_ldst ld x Rt (XREG_SP Rn)
      (if S then Shiftreg_Offset (XREG' Rm) (if x then 3 else 2)
            else Register_Offset (XREG' Rm)))
  | [0b001110000:9; ld; 0b0:1; imm9:9; 0b01:2; Rn:5; Rt:5] ->
    SOME (arm_ldstb ld Rt (XREG_SP Rn) (Postimmediate_Offset (word_sx imm9)))
  | [0b001110000:9; ld; 0b0:1; imm9:9; 0b11:2; Rn:5; Rt:5] ->
    SOME (arm_ldstb ld Rt (XREG_SP Rn) (Preimmediate_Offset (word_sx imm9)))
  | [0b001110010:9; ld; imm12:12; Rn:5; Rt:5] ->
    SOME (arm_ldstb ld Rt (XREG_SP Rn) (Immediate_Offset (word_zx imm12)))
    // LDRB/STRB shifted register, no shift: option:011 S:0
  | [0b001110000:9; ld; 0b1:1; Rm:5; 0b011010:6; Rn:5; Rt:5] ->
    SOME (arm_ldstb ld Rt (XREG_SP Rn) (Register_Offset (XREG' Rm)))

  | [x; 0b010100:6; pre; 0b1:1; ld; imm7:7; Rt2:5; Rn:5; Rt:5] ->
    SOME (arm_ldstp ld x Rt Rt2 (XREG_SP Rn)
      ((if pre then Preimmediate_Offset else Postimmediate_Offset)
        (iword (ival imm7 * &(if x then 8 else 4)))))
  | [x; 0b01010010:8; ld; imm7:7; Rt2:5; Rn:5; Rt:5] ->
    SOME (arm_ldstp ld x Rt Rt2 (XREG_SP Rn)
      (Immediate_Offset (iword (ival imm7 * &(if x then 8 else 4)))))

  // NOP
  | [0b11010101000000110010000000011111:32] ->
    SOME arm_NOP

  // SIMD ld,st operations
  // LDR/STR (immediate, SIMD&FP), Unsigned offset, no writeback
  // Currently only supports sizes 128 and 64 (not 32, 16 or 8)
  | [0b00:2; 0b111101:6; 0b1:1; is_ld; imm12:12; Rn:5; Rt:5] ->
    SOME (arm_ldst_q is_ld Rt (XREG_SP Rn) (Immediate_Offset (word (val imm12 * 16))))
  | [0b11:2; 0b111101:6; 0b0:1; is_ld; imm12:12; Rn:5; Rt:5] ->
    SOME (arm_ldst_d is_ld Rt (XREG_SP Rn) (Immediate_Offset (word (val imm12 * 8))))
  // Post-immediate offset, size 128 only
  | [0b00:2; 0b1111001:7; is_ld; 0:1; imm9:9; 0b01:2; Rn:5; Rt:5] ->
    SOME (arm_ldst_q is_ld Rt (XREG_SP Rn) (Postimmediate_Offset (word_sx imm9)))

  // LDP/STP (signed offset, SIMD&FP), only sizes 128 and 64
  | [0b10:2; 0b1011010:7; is_ld; imm7:7; Rt2:5; Rn:5; Rt:5] ->
    SOME (arm_ldstp_q is_ld Rt Rt2 (XREG_SP Rn)
     (Immediate_Offset (iword (ival imm7 * &16))))
  | [0b01:2; 0b1011010:7; is_ld; imm7:7; Rt2:5; Rn:5; Rt:5] ->
    SOME (arm_ldstp_d is_ld Rt Rt2 (XREG_SP Rn)
     (Immediate_Offset (iword (ival imm7 * &8))))

  // LDR/STR (immediate, SIMD&FP), Pre-index (has writeback)
  | [0b00:2; 0b1111001:7; is_ld; 0:1; imm9:9; 0b11:2; Rn:5; Rt:5] ->
    SOME (arm_ldst_q is_ld Rt (XREG_SP Rn) (Preimmediate_Offset (word_sx imm9)))

  // LDUR/STUR, only size 128
  | [0b00:2; 0b1111001:7; is_ld; 0:1; imm9:9; 0b00:2; Rn:5; Rt:5] ->
    SOME (arm_ldst_q is_ld Rt (XREG_SP Rn) (Immediate_Offset (word_sx imm9)))

  // LD1/ST1 (multiple structures), 1 register,
  //   Post-immediate offset and post-register offset, and no offset.
  //
  // NOTE: On little-endian machines, LD1/ST1 with 1 register is equivalent to
  // simply loading/storing the whole word.
  // On big-endian machines, for LD1/ST1, each lane is byte-reversed
  // but the lane order is kept the same. For LDR/STR, the whole register is
  // byte-reversed. This results in different hehaviour for LD1/ST1 vs LDR/STR
  // when running on big-endian machines.
  // See https://llvm.org/docs/BigEndianNEON.html#ldr-and-ld1
  //
  // Since instructions are modeled only for little-endian, the optimization
  // that reuses functions of LDR/STR for LD1/ST1 is okay.

  // datasize = 64
  // Post-immediate offset and post-register offset
  | [0:1; 0:1; 0b0011001:7; is_ld; 0:1; Rm:5; 0b0111:4; size:2; Rn:5; Rt:5] ->
    SOME (arm_ldst_d is_ld Rt (XREG_SP Rn)
    (if val Rm = 31 then (Postimmediate_Offset (word 8))
                    else Postreg_Offset (XREG' Rm)))
  // No offset
  | [0:1; 0:1; 0b0011000:7; is_ld; 0b000000:6; 0b0111:4; size:2; Rn:5; Rt:5] ->
    SOME (arm_ldst_d is_ld Rt (XREG_SP Rn) No_Offset)

  // datasize = 128
  // Post-immediate offset and post-register offset
  | [0:1; 1:1; 0b0011001:7; is_ld; 0:1; Rm:5; 0b0111:4; size:2; Rn:5; Rt:5] ->
    SOME (arm_ldst_q is_ld Rt (XREG_SP Rn)
      (if val Rm = 31 then (Postimmediate_Offset (word 16))
                      else Postreg_Offset (XREG' Rm)))
  // No offset
  | [0:1; 1:1; 0b0011000:7; is_ld; 0b000000:6; 0b0111:4; size:2; Rn:5; Rt:5] ->
    SOME (arm_ldst_q is_ld Rt (XREG_SP Rn) No_Offset)

  // LD1/ST1 (multiple structures), 2 registers,
  //   Post-index with immediate offset, datasize = 128
  // Similar to LDP of SIMD registers, assuming little-endian architecture.
  | [0:1; 1:1; 0b0011001:7; is_ld; 0:1; 0b11111:5; 0b1010:4; size:2; Rn:5; Rt:5] ->
    SOME (arm_ldstp_2q is_ld Rt (XREG_SP Rn) (Postimmediate_Offset (word 32)))
  //   No offset, datasize = 128
  | [0:1; 1:1; 0b0011000:7; is_ld; 0b000000:6; 0b1010:4; size:2; Rn:5; Rt:5] ->
    SOME (arm_ldstp_2q is_ld Rt (XREG_SP Rn) No_Offset)

  // LD2/ST2 (multiple structures), 2 registers, immediate offset, Post-immediate offset
  // datasize = 64
  | [0:1; 0:1; 0b0011001:7; is_ld; 0:1; 0b11111:5; 0b1000:4; size:2; Rn:5; Rt:5] ->
    if size = (word 0b11:(2)word) then NONE // "UNDEFINED"
    else
      let esize = 8 * 2 EXP (val size) in
      SOME (arm_ldst2 is_ld Rt (XREG_SP Rn) (Postimmediate_Offset (word 16)) 64 esize)
  // datasize = 128
  | [0:1; 1:1; 0b0011001:7; is_ld; 0:1; 0b11111:5; 0b1000:4; size:2; Rn:5; Rt:5] ->
    let esize = 8 * 2 EXP (val size) in
    SOME (arm_ldst2 is_ld Rt (XREG_SP Rn) (Postimmediate_Offset (word 32)) 128 esize)

  // LD1R, Post-immediate offset, size 64 and 128
  | [0b0:1; q; 0b001101110111111100:18; size:2; Rn:5; Rt:5] ->
    let esize = 8 * (2 EXP (val size)) in
    let datasize = if q then 128 else 64 in
    let off = word (esize DIV 8) in
    SOME (arm_LD1R (QREG' Rt) (XREG_SP Rn) (Postimmediate_Offset off) esize datasize)

  // SIMD operations
  | [0:1; q; u; 0b01110:5; size:2; 1:1; Rm:5; 0b100001:6; Rn:5; Rd:5] ->
    // ADD and SUB
    if size = (word 0b11:(2)word) /\ ~q then NONE // "UNDEFINED"
    else
      let esize = 8 * (2 EXP (val size)) in
      let datasize = if q then 128 else 64 in
      SOME ((if u then arm_SUB_VEC else arm_ADD_VEC)
            (QREG' Rd) (QREG' Rn) (QREG' Rm) esize datasize)

  | [0:1; q; 0b001110001:9; Rm:5; 0b000111:6; Rn:5; Rd:5] ->
    // AND
    SOME (arm_AND_VEC (QREG' Rd) (QREG' Rn) (QREG' Rm) (if q then 128 else 64))

  | [0:1; q; 0b001110011:9; Rm:5; 0b000111:6; Rn:5; Rd:5] ->
    // BIC (vector)
    SOME (arm_BIC_VEC (QREG' Rd) (QREG' Rn) (QREG' Rm) (if q then 128 else 64))

  | [0:1; q; 0b101110:6; size:2; 1:1; Rm:5; 0b001101:6; Rn:5; Rd:5] ->
    // CMHI (vector)
    if size = word 0b11 /\ ~q then NONE else
    let esize = 8 * 2 EXP val size in
    let datasize = if q then 128 else 64 in
    SOME (arm_CMHI_VEC (QREG' Rd) (QREG' Rn) (QREG' Rm) esize datasize)

  | [0:1; q; 0b101110001:9; Rm:5; 0b000111:6; Rn:5; Rd:5] ->
    // EOR
    SOME (arm_EOR_VEC (QREG' Rd) (QREG' Rn) (QREG' Rm) (if q then 128 else 64))

  | [0:1; q; 0b101110101:9; Rm:5; 0b000111:6; Rn:5; Rd:5] ->
    // BIT
    SOME (arm_BIT (QREG' Rd) (QREG' Rn) (QREG' Rm) (if q then 128 else 64))

  // Two sizes of FCSEL, not allowing FP16 case at all
  | [0b00011110:8; 0b00:2; 0b1:1; Rm:5; cond:4; 0b11:2; Rn:5; Rd:5] ->
    SOME (arm_FCSEL (QREG' Rd) (QREG' Rn) (QREG' Rm) (Condition cond) 32)
  | [0b00011110:8; 0b01:2; 0b1:1; Rm:5; cond:4; 0b11:2; Rn:5; Rd:5] ->
    SOME (arm_FCSEL (QREG' Rd) (QREG' Rn) (QREG' Rm) (Condition cond) 64)

  | [0:1; q; 0b001110:6; size:2; 0b100000010110:12; Rn:5; Rd:5] ->
    // CNT (count bits in each byte of 64-bit or 128-bit word)
    if ~(size = word 0b00) then NONE else
    let datasize = if q then 128 else 64 in
    SOME (arm_CNT (QREG' Rd) (QREG' Rn) datasize)

  | [0:1; q; 0b001110000:9; imm5:5; 0b000011:6; Rn:5; Rd:5] ->
    // DUP (general)
    let size = word_ctz imm5 in
    if size > 3 then NONE else
    if size = 3 /\ ~q then NONE else
    let esize = 8 * 2 EXP size in
    let datasize = if q then 128 else 64 in
    SOME (arm_DUP_GEN (QREG' Rd) (XREG' Rn) esize datasize)

  | [0:1; q; 0b101110000:9; Rm:5; 0:1; imm4:4; 0:1; Rn:5; Rd:5] ->
    // EXT
    if ~q /\ bit 3 imm4 then NONE // "UNDEFINED"
    else if q then
      let pos = (val imm4) * 8 in
      // datasize is fixed to 128.
      SOME (arm_EXT (QREG' Rd) (QREG' Rn) (QREG' Rm) pos)
    else NONE

  | [0:1; q; 1:1; 0b011110:6; immh:4; abc:3; cmode:4; 0b01:2; defgh:5; Rd:5] ->
    // MOVI, USHR (Vector), USRA (Vector), SLI (Vector), SRI (vector)
    if val immh = 0 then
      // MOVI, 128-bit only
      if cmode = word 0b1110 /\ q then
        let abcdefgh:(8)word = word_join abc defgh in
        let imm = arm_adv_simd_expand_imm abcdefgh (word 1:(1)word) cmode in
        match imm with
        | SOME imm -> SOME (arm_MOVI (QREG' Rd) imm)
        | NONE -> NONE
      // BIC (vector immediate), 16-bit size only
      else if cmode = word 0b1001 \/ cmode = word 0b1011 then
        let abcdefgh:(8)word = word_join abc defgh in
        let datasize = if q then 128 else 64 in
        match arm_adv_simd_expand_imm abcdefgh (word 1:(1)word) cmode with
          SOME imm ->
            let imm2 = if q then word_duplicate imm else word_zx imm in
            SOME (arm_BIC_VEC (QREG' Rd) (QREG' Rd) (rvalue imm2) datasize)
         | NONE -> NONE
      else NONE
    else if cmode = (word 0b0000:(4)word) then
      // USHR
      if bit 3 immh /\ ~q then NONE // "UNDEFINED"
      else
        let immb = abc in
        let Rn = defgh in
        let esize = 8 * 2 EXP (3 - word_clz immh) in
        let datasize = if q then 128 else 64 in
        let amt = 2 * esize - val(word_join immh immb:7 word) in
        SOME (arm_USHR_VEC (QREG' Rd) (QREG' Rn) amt esize datasize)
    else if cmode = (word 0b0001:(4)word) then
      // USRA
      if bit 3 immh /\ ~q then NONE // "UNDEFINED"
      else
        let immb = abc in
        let Rn = defgh in
        let esize = 8 * 2 EXP (3 - word_clz immh) in
        let datasize = if q then 128 else 64 in
        let elements = datasize DIV esize in
        let shift = (esize * 2) - val(word_join immh immb:(7)word) in
        // unsigned is true, round is false, accumulate is true
        SOME (arm_USRA_VEC (QREG' Rd) (QREG' Rn) shift esize datasize)
    else if cmode = (word 0b0101:(4)word) then
      // SLI (vector)
      let immb = abc in
      let Rn = defgh in
      // if immh = 0, this is MOVI
      if bit 3 immh /\ ~q then NONE // "UNDEFINED"
      else
        let esize = 8 * 2 EXP (3 - word_clz immh) in
        let datasize = if q then 128 else 64 in
        let elements = datasize DIV esize in
        let shift = val (word_join immh immb:(7)word) - esize in
        SOME (arm_SLI_VEC (QREG' Rd) (QREG' Rn) shift datasize esize)
    else if cmode = (word 0b0100:(4)word) then
      // SRI (vector)
      let immb = abc in
      let Rn = defgh in
      if bit 3 immh /\ ~q then NONE
      else
        let esize = 8 * 2 EXP (3 - word_clz immh) in
        let datasize = if q then 128 else 64 in
        let shift = (esize * 2) - val (word_join immh immb:(7)word) in
        SOME (arm_SRI_VEC (QREG' Rd) (QREG' Rn) shift esize datasize)
    else NONE

  | [0b0001111000100110000000:22; Rn:5; Rd:5] ->
    // FMOV (single, to general)
    SOME (arm_FMOV_FtoI (WREG' Rd) (QREG' Rn) 0 32)

  | [0b1001111001100110000000:22; Rn:5; Rd:5] ->
    // FMOV (double, to general)
    SOME (arm_FMOV_FtoI (XREG' Rd) (QREG' Rn) 0 64)

  | [0b1001111010101110000000:22; Rn:5; Rd:5] ->
    // FMOV (double high part, to general)
    SOME (arm_FMOV_FtoI (XREG' Rd) (QREG' Rn) 1 64)

  | [0b1001111001100111000000:22; Rn:5; Rd:5] ->
    // FMOV (double, from general)
    SOME (arm_FMOV_ItoF (QREG' Rd) (XREG' Rn) 0)

  | [0b1001111010101111000000:22; Rn:5; Rd:5] ->
    // FMOV (double high part, from general)
    SOME (arm_FMOV_ItoF (QREG' Rd) (XREG' Rn) 1)

  | [0:1; q; 0b101111:6; sz:2; L:1; M:1; R:4; 0b0100:4; H:1; 0:1; Rn:5; Rd:5] ->
    // MLS (by element)
    if sz = word 0b00 \/ sz = word 0b11 then NONE else // "UNDEFINED"
    let ix = if sz = word 0b01 then 4 * val H + 2 * val L + val M
             else 2 * val H + val L in
    let Rm = if sz = word 0b01 then word_zx R else word_join M R in
    let esize = 8 * 2 EXP val sz in
    let datasize = if q then 128 else 64 in
    SOME (arm_MLS_VEC (QREG' Rd) (QREG' Rn) (QLANE Rm esize ix) esize datasize)

  | [0:1; q; 0b101110:6; size:2; 0b1:1; Rm:5; 0b100101:6; Rn:5; Rd:5] ->
    // MLS (vector)
    if size = word 0b11 then NONE // "UNDEFINED"
    else
      let esize = 8 * (2 EXP (val size)) in
      let datasize = if q then 128 else 64 in
      SOME (arm_MLS_VEC (QREG' Rd) (QREG' Rn) (QREG' Rm) esize datasize)

  | [0:1; q; 0b001111:6; sz:2; L:1; M:1; R:4; 0b1000:4; H:1; 0:1; Rn:5; Rd:5] ->
    // MUL (by element)
    if sz = word 0b00 \/ sz = word 0b11 then NONE else // "UNDEFINED"
    let ix = if sz = word 0b01 then 4 * val H + 2 * val L + val M
             else 2 * val H + val L in
    let Rm = if sz = word 0b01 then word_zx R else word_join M R in
    let esize = 8 * 2 EXP val sz in
    let datasize = if q then 128 else 64 in
    SOME (arm_MUL_VEC (QREG' Rd) (QREG' Rn) (QLANE Rm esize ix) esize datasize)

  | [0:1; q; 0b001110:6; size:2; 0b1:1; Rm:5; 0b100111:6; Rn:5; Rd:5] ->
    // MUL (vector)
    if size = word 0b11 then NONE // "UNDEFINED"
    else
      let esize = 8 * (2 EXP (val size)) in
      let datasize = if q then 128 else 64 in
      SOME (arm_MUL_VEC (QREG' Rd) (QREG' Rn) (QREG' Rm) esize datasize)

  | [0:1; q; 0b001110101:9; Rm:5; 0b000111:6; Rn:5; Rd:5] ->
    // MOV, ORR
    SOME (arm_ORR_VEC (QREG' Rd) (QREG' Rn) (QREG' Rm) (if q then 128 else 64))

  | [0:1; q; 0b001110:6; size:2; 0b100000000010:12; Rn:5; Rd:5] ->
    // REV64
    if ~q then NONE // datasize = 64 is unsupported yet
    else if size = (word 0b11: (2)word) then NONE // "UNDEFINED"
    else
      let esize:(64)word = word_shl (word 0b1000: (64)word) (val size) in
      SOME (arm_REV64_VEC (QREG' Rd) (QREG' Rn) (val esize))

  | [0b01101110000:11; imm5:5; 0:1; imm4:4; 1:1; Rn:5; Rd:5] ->
    // INS, or "MOV (element)"
    let size = word_ctz imm5 in
    if size > 3 then NONE else
    let esize = 8 * 2 EXP size in
    let dst_index = esize * val(word_subword imm5 (size+1,4-size):5 word) in
    let src_index = esize * val(word_subword imm4 (size,4-size):4 word) in
    let idxdsize = if bit 3 imm4 then 128 else 64 in
    SOME (arm_INS (QREG' Rd) (QREG' Rn) dst_index src_index esize idxdsize)

 | [0b01001110000:11; imm5:5; 0b000111:6; Rn:5; Rd:5] ->
    // INS (general)
    let size = word_ctz imm5 in
    if size > 3 then NONE else
    let esize = 8 * 2 EXP size in
    let ix = esize * val(word_subword imm5 (size+1,4-size):5 word) in
    if size = 3 then SOME (arm_INS_GEN (QREG' Rd) (XREG' Rn) ix esize)
    else SOME (arm_INS_GEN (QREG' Rd) (WREG' Rn) ix esize)

  | [0b01011110000:11; Rm:5; 0b010000:6; Rn:5; Rd:5] ->
    // SHA256H
    SOME (arm_SHA256H (QREG' Rd) (QREG' Rn) (QREG' Rm))

  | [0b01011110000:11; Rm:5; 0b010100:6; Rn:5; Rd:5] ->
    // SHA256H2
    SOME (arm_SHA256H2 (QREG' Rd) (QREG' Rn) (QREG' Rm))

  | [0b0101111000101000001010:22; Rn:5; Rd:5] ->
    // SHA256SU0
    SOME (arm_SHA256SU0 (QREG' Rd) (QREG' Rn))

  | [0b01011110000:11; Rm:5; 0b011000:6; Rn:5; Rd:5] ->
    // SHA256SU1
    SOME (arm_SHA256SU1 (QREG' Rd) (QREG' Rn) (QREG' Rm))

  | [0b11001110011:11; Rm:5; 0b100000:6; Rn:5; Rd:5] ->
    // SHA512H
    SOME (arm_SHA512H (QREG' Rd) (QREG' Rn) (QREG' Rm))

  | [0b11001110011:11; Rm:5; 0b100001:6; Rn:5; Rd:5] ->
    // SHA512H2
    SOME (arm_SHA512H2 (QREG' Rd) (QREG' Rn) (QREG' Rm))

  | [0b1100111011000000100000:22; Rn:5; Rd:5] ->
    // SHA512SU0
    SOME (arm_SHA512SU0 (QREG' Rd) (QREG' Rn))

  | [0b11001110011:11; Rm:5; 0b100010:6; Rn:5; Rd:5] ->
    // SHA512SU1
    SOME (arm_SHA512SU1 (QREG' Rd) (QREG' Rn) (QREG' Rm))

  | [0b0100111000101000010010:22; Rn:5; Rd:5] ->
    // AESE
    SOME (arm_AESE (QREG' Rd) (QREG' Rn))

  | [0b0100111000101000011010:22; Rn:5; Rd:5] ->
    // AESMC
    SOME (arm_AESMC (QREG' Rd) (QREG' Rn))

  | [0b0100111000101000010110:22; Rn:5; Rd:5] ->
    // AESD
    SOME (arm_AESD (QREG' Rd) (QREG' Rn))

  | [0b0100111000101000011110:22; Rn:5; Rd:5] ->
    // AESIMC
    SOME (arm_AESIMC (QREG' Rd) (QREG' Rn))

  | [0b11001110011:11; Rm:5; 0b100011:6; Rn:5; Rd:5] ->
    // RAX1
    SOME (arm_RAX1 (QREG' Rd) (QREG' Rn) (QREG' Rm))

  | [0:1; q; 0b0011110:7; immh:4; immb:3; 0b010101:6; Rn:5; Rd:5] ->
    // SHL
    if immh = (word 0b0: (4)word) then NONE // "asimdimm case"
    else if bit 3 immh /\ ~q then NONE // "UNDEFINED"
    else
      let esize = 8 * 2 EXP (3 - word_clz immh) in
      let datasize = if q then 128 else 64 in
      let amt = val(word_join immh immb:7 word) - esize in
      SOME (arm_SHL_VEC (QREG' Rd) (QREG' Rn) amt esize datasize)

  | [0:1; q; 0b0011110:7; immh:4; immb:3; 0b100001:6; Rn:5; Rd:5] ->
    // SHRN
    if q then NONE // writing to the upper part is unsupported yet
    else if immh = (word 0b0:(4)word) then NONE // "asimdimm case"
    else if bit 3 immh then NONE // "UNDEFINED"
    else
      let esize = 8 * 2 EXP (3 - word_clz immh) in
      // datasize is 64, part is 0
      let elements = 64 DIV esize in
      let shift = (2 * esize) - val(word_join immh immb: (7)word) in
      // round is false
      SOME (arm_SHRN (QREG' Rd) (QREG' Rn) shift esize)

  | [0:1; q; 0b001111:6; sz:2; L:1; M:1; R:4; 0b1100:4; H:1; 0:1; Rn:5; Rd:5] ->
    // SQDMULH (by element)
    if sz = word 0b00 \/ sz = word 0b11 then NONE else // "UNDEFINED"
    let ix = if sz = word 0b01 then 4 * val H + 2 * val L + val M
             else 2 * val H + val L in
    let Rm = if sz = word 0b01 then word_zx R else word_join M R in
    let esize = 8 * 2 EXP val sz in
    let datasize = if q then 128 else 64 in
    SOME (arm_SQDMULH_VEC (QREG' Rd) (QREG' Rn) (QLANE Rm esize ix) esize datasize)

  | [0:1; q; 0b001110:6; sz:2; 1:1; Rm:5; 0b101101:6; Rn:5; Rd:5] ->
    // SQDMULH (vector)
    if sz = word 0b00 \/ sz = word 0b11 then NONE else // "UNDEFINED"
    let esize = 8 * 2 EXP val sz in
    let datasize = if q then 128 else 64 in
    SOME (arm_SQDMULH_VEC (QREG' Rd) (QREG' Rn) (QREG' Rm) esize datasize)

  | [0:1; q; 0b001111:6; sz:2; L:1; M:1; R:4; 0b1101:4; H:1; 0:1; Rn:5; Rd:5] ->
    // SQRDMULH (by element)
    if sz = word 0b00 \/ sz = word 0b11 then NONE else // "UNDEFINED"
    let ix = if sz = word 0b01 then 4 * val H + 2 * val L + val M
             else 2 * val H + val L in
    let Rm = if sz = word 0b01 then word_zx R else word_join M R in
    let esize = 8 * 2 EXP val sz in
    let datasize = if q then 128 else 64 in
    SOME (arm_SQRDMULH_VEC (QREG' Rd) (QREG' Rn) (QLANE Rm esize ix) esize datasize)

  | [0:1; q; 0b101110:6; sz:2; 1:1; Rm:5; 0b101101:6; Rn:5; Rd:5] ->
    // SQRDMULH (vector)
    if sz = word 0b00 \/ sz = word 0b11 then NONE else // "UNDEFINED"
    let esize = 8 * 2 EXP val sz in
    let datasize = if q then 128 else 64 in
    SOME (arm_SQRDMULH_VEC (QREG' Rd) (QREG' Rn) (QREG' Rm) esize datasize)

  | [0:1; q; 0b0011110:7; immh:4; immb:3; 0b001001:6; Rn:5; Rd:5] ->
    // SRSHR
    if immh = (word 0b0: (4)word) then NONE // "asimdimm case"
    else if bit 3 immh /\ ~q then NONE // "UNDEFINED"
    else
      let esize = 8 * 2 EXP (3 - word_clz immh) in
      let datasize = if q then 128 else 64 in
      let amt = 2 * esize - val(word_join immh immb:7 word) in
      SOME (arm_SRSHR_VEC (QREG' Rd) (QREG' Rn) amt esize datasize)

  | [0:1; q; 0b0011110:7; immh:4; immb:3; 0b000001:6; Rn:5; Rd:5] ->
    // SSHR
    if immh = (word 0b0: (4)word) then NONE // "asimdimm case"
    else if bit 3 immh /\ ~q then NONE // "UNDEFINED"
    else
      let esize = 8 * 2 EXP (3 - word_clz immh) in
      let datasize = if q then 128 else 64 in
      let amt = 2 * esize - val(word_join immh immb:7 word) in
      SOME (arm_SSHR_VEC (QREG' Rd) (QREG' Rn) amt esize datasize)

  | [0:1; q; 0b001110:6; size:2; 0:1; Rm:5; 0:1; op; 0b1010:4; Rn:5; Rd:5] ->
    // TRN1 and TRN2
    if size = (word 0b11:(2)word) /\ ~q then NONE // "UNDEFINED"
    else
      let esize = 8 * (2 EXP (val size)) in
      let datasize = if q then 128 else 64 in
      SOME ((if op then arm_TRN2 else arm_TRN1)
            (QREG' Rd) (QREG' Rn) (QREG' Rm) esize datasize)

  | [0:1; q; 0b101110:6; size:2; 0b100000001010:12; Rn:5; Rd:5] ->
    // UADDLP
    if ~q then NONE // datasize = 128 is unsupported yet
    else if size = (word 0b11: (2)word) then NONE // "UNDEFINED"
    else
      let esize: (64)word = word_shl (word 8: (64)word) (val size) in
      SOME (arm_UADDLP (QREG' Rd) (QREG' Rn) (val esize))

  | [0:1; q; 0b101110:6; size:2; 0b110000001110:12; Rn:5; Rd:5] ->
    // UADDLV
    if size = word 0b10 /\ ~q \/ size = word 0b11 then NONE else
    let esize = 8 * 2 EXP (val size) in
    let datasize = if q then 128 else 64 in
    let elements = datasize DIV esize in
    SOME(arm_UADDLV (QREG' Rd) (QREG' Rn) elements esize)

  | [0:1; q; 0b101110:6; size:2; 0b1:1; Rm:5; 0b100000:6; Rn:5; Rd:5] ->
    // UMLAL (vector, Q = 0). UMLAL2 (vector, Q=1)
    if size = (word 0b11: (2)word) then NONE // "UNDEFINED"
    else
      let esize: (64)word = word_shl (word 8: (64)word) (val size) in
      if q then
        SOME (arm_UMLAL2_VEC (QREG' Rd) (QREG' Rn) (QREG' Rm) (val esize))
      else
        SOME (arm_UMLAL_VEC (QREG' Rd) (QREG' Rn) (QREG' Rm) (val esize))

  | [0:1; q; 0b101110:6; size:2; 0b1:1; Rm:5; 0b101000:6; Rn:5; Rd:5] ->
    // UMLSL (vector, Q = 0). UMLSL2 (vector, Q=1)
    if size = (word 0b11: (2)word) then NONE // "UNDEFINED"
    else
      let esize: (64)word = word_shl (word 8: (64)word) (val size) in
      if q then
        SOME (arm_UMLSL2_VEC (QREG' Rd) (QREG' Rn) (QREG' Rm) (val esize))
      else
        SOME (arm_UMLSL_VEC (QREG' Rd) (QREG' Rn) (QREG' Rm) (val esize))

  | [0:1; q; 0b001110:6; size:2; 0b1:1; Rm:5; 0b100000:6; Rn:5; Rd:5] ->
    // SMLAL (vector, Q = 0). SMLAL2 (vector, Q=1)
    if size = (word 0b11: (2)word) then NONE // "UNDEFINED"
    else
      let esize: (64)word = word_shl (word 8: (64)word) (val size) in
      if q then
        SOME (arm_SMLAL2_VEC (QREG' Rd) (QREG' Rn) (QREG' Rm) (val esize))
      else
        SOME (arm_SMLAL_VEC (QREG' Rd) (QREG' Rn) (QREG' Rm) (val esize))

  | [0:1; q; 0b001110:6; size:2; 0b1:1; Rm:5; 0b101000:6; Rn:5; Rd:5] ->
    // SMSL (vector, Q = 0). SMLSL2 (vector, Q=1)
    if size = (word 0b11: (2)word) then NONE // "UNDEFINED"
    else
      let esize: (64)word = word_shl (word 8: (64)word) (val size) in
      if q then
        SOME (arm_SMLSL2_VEC (QREG' Rd) (QREG' Rn) (QREG' Rm) (val esize))
      else
        SOME (arm_SMLSL_VEC (QREG' Rd) (QREG' Rn) (QREG' Rm) (val esize))

  | [0:1; q; 0b001110000:9; imm5:5; 0b001111:6; Rn:5; Rd:5] ->
    // UMOV
    if q /\ word_subword imm5 (0,4) = (word 0b1000: 4 word) then // v.d
      SOME (arm_UMOV (XREG' Rd) (QREG' Rn) (val (word_subword imm5 (4,1): 1 word)) 8)
    else if ~q /\ word_subword imm5 (0,3) = (word 0b100: 3 word) then // v.s
      SOME (arm_UMOV (WREG' Rd) (QREG' Rn) (val (word_subword imm5 (3,2): 2 word)) 4)
    else NONE // v.h, v.b are unsupported

  | [0:1; q; 0b101110:6; size:2; 1:1; Rm:5; 0b110000:6; Rn:5; Rd:5] ->
    // UMULL (vector, Q = 0). UMULL2 (vector, Q = 1)
    if size = (word 0b11:(2)word) then NONE // UNDEFINED
    else
      let esize = 8 * (2 EXP val size) in // the bitwidth of src elements
      // datasize is 64. elements is datasize / esize.
      if q then
        SOME (arm_UMULL2_VEC (QREG' Rd) (QREG' Rn) (QREG' Rm) esize)
      else
        SOME (arm_UMULL_VEC (QREG' Rd) (QREG' Rn) (QREG' Rm) esize)

  | [0:1; q; 0b001110:6; size:2; 1:1; Rm:5; 0b110000:6; Rn:5; Rd:5] ->
    // SMULL (vector, Q = 0). SMULL2 (vector, Q = 1)
    if size = (word 0b11:(2)word) then NONE // UNDEFINED
    else
      let esize = 8 * (2 EXP val size) in // the bitwidth of src elements
      // datasize is 64. elements is datasize / esize.
      if q then
        SOME (arm_SMULL2_VEC (QREG' Rd) (QREG' Rn) (QREG' Rm) esize)
      else
        SOME (arm_SMULL_VEC (QREG' Rd) (QREG' Rn) (QREG' Rm) esize)

  | [0:1; q; 0b001110:6; size:2; 0b0:1; Rm:5; 0b000110:6; Rn:5; Rd:5] ->
    // UZP1
    if ~q then NONE // datasize = 64 is unsupported yet
    else
      let esize: (64)word = word_shl (word 8: (64)word) (val size) in
      SOME (arm_UZP1 (QREG' Rd) (QREG' Rn) (QREG' Rm) (val esize))

  | [0:1; q; 0b001110:6; size:2; 0b0:1; Rm:5; 0b010110:6; Rn:5; Rd:5] ->
    // UZP2
    if ~q then NONE // datasize = 64 is unsupported yet
    else
      let esize: (64)word = word_shl (word 8: (64)word) (val size) in
      SOME (arm_UZP2 (QREG' Rd) (QREG' Rn) (QREG' Rm) (val esize))

  | [0:1; 0:1; 0b001110:6; size:2; 0b100001001010:12; Rn:5; Rd:5] ->
    // XTN
    if size = (word 0b11: (2)word) then NONE // "UNDEFINED"
    else
      let esize: (64)word = word_shl (word 8: (64)word) (val size) in
      SOME (arm_XTN (QREG' Rd) (QREG' Rn) (val esize))

  | [0:1; q; 0b001110:6; size:2; 0:1; Rm:5; 0:1; op; 0b1110:4; Rn:5; Rd:5] ->
    // ZIP1 (op = 0) and ZIP2 (op = 1)
    if size = (word 0b11:(2)word) /\ ~q then NONE // "UNDEFINED"
    else
      let esize = 8 * (2 EXP (val size)) in
      let datasize = if q then 128 else 64 in
      let elements = datasize DIV esize in
      // part is 1 or 0 according to op, pairs is elements / 2
      if op then SOME(arm_ZIP2 (QREG' Rd) (QREG' Rn) (QREG' Rm) esize datasize)
      else SOME(arm_ZIP1 (QREG' Rd) (QREG' Rn) (QREG' Rm) esize datasize)

  | [0:1; q; 0b001110000:9; Rm:5; 0b000000:6; Rn:5; Rd:5] ->
    // TBL (single register, i.e. len = 0, only)
    let datasize = if q then 128 else 64 in
    SOME(arm_TBL (QREG' Rd) [QREG' Rn] (QREG' Rm) datasize)

  | [0b11001110000:11; Rm:5; 0:1; Ra:5; Rn:5; Rd:5] ->
    // EOR3
    SOME (arm_EOR3 (QREG' Rd) (QREG' Rn) (QREG' Rm) (QREG' Ra))

  | [0b11001110001:11; Rm:5; 0:1; Ra:5; Rn:5; Rd:5] ->
    // BCAX
    SOME (arm_BCAX (QREG' Rd) (QREG' Rn) (QREG' Rm) (QREG' Ra))

  | [0b11001110100:11; Rm:5; imm6:6; Rn:5; Rd:5] ->
    // XAR
    SOME (arm_XAR (QREG' Rd) (QREG' Rn) (QREG' Rm) imm6)

  | _ -> NONE`;;

(* ------------------------------------------------------------------------- *)
(* Decode tactics.                                                           *)
(* ------------------------------------------------------------------------- *)

(*** Add encoders for target instructions of relocation entries. *)
let encode_BL = new_definition `encode_BL n =
  0x94000000 + val (iword (n div &4):26 word)`;;

let decode_encode_BL = prove (`decode (word (encode_BL n)) =
  SOME (arm_BL (word (val (iword (n div &4):26 word) * 4)))`,
  MATCH_MP_TAC (
    let th = SPEC `word (encode_BL n):int32` decode in
    let tm = rhs (concl th) in
    let A, tr = bm_build_tree (rhs (concl th)) in
    let a = Array.init 32 (fun i -> Some ((0x94000000 land (1 lsl i)) != 0)) in
    (DISCH_ALL o REWRITE_RULE [] o INST [`T`,`op:bool`] o TRANS th)
      (hd (snd (snd (get_dt a (bm_add_pos tr tm)))))) THEN
  REWRITE_TAC [encode_BL] THEN
  SPEC_TAC (`iword (n div &4):26 word`,`w:26 word`) THEN
  REWRITE_TAC [FORALL_VAL_GEN; VAL_WORD; CONSPAT_pat_set; NILPAT_pat_set;
    word1; bitval] THEN
  CONV_TAC (DEPTH_CONV UNWIND_CONV THENC ONCE_DEPTH_CONV DIMINDEX_CONV THENC
    NUM_REDUCE_CONV) THEN IMP_REWRITE_TAC [MOD_LT] THEN ARITH_TAC);;

let encode_ADR = new_definition `encode_ADR (dstreg:(5)word) (immhi:(19)word) (immlo:(2)word) =
  0x10000000 + val (immlo) * 2 EXP 29 +
               val (immhi) * 2 EXP 5 +
               val dstreg`;;

let decode_encode_ADR = prove (`decode (word (encode_ADR dstreg immhi immlo)) =
  SOME (arm_ADR (XREG' dstreg) (word_join immhi immlo:(21)word))`,
  MATCH_MP_TAC (
    let th = SPEC `word (encode_ADR dstreg immhi immlo):int32` decode in
    let tm = rhs (concl th) in
    let A, tr = bm_build_tree (rhs (concl th)) in
    let a = Array.init 32 (fun i -> Some ((0x10000000 land (1 lsl i)) != 0)) in
    (DISCH_ALL o REWRITE_RULE [] o TRANS th)
      (hd (snd (snd (get_dt a (bm_add_pos tr tm)))))) THEN
  REWRITE_TAC [encode_ADR] THEN
  MAP_EVERY SPEC_TAC [`immlo:2 word`,`immlo:2 word`;`immhi:(19)word`,`immhi:(19)word`;`dstreg:(5)word`,`dstreg:(5)word`] THEN
  REWRITE_TAC [FORALL_VAL_GEN; VAL_WORD; CONSPAT_pat_set; NILPAT_pat_set;
    word1; bitval] THEN
  CONV_TAC (DEPTH_CONV UNWIND_CONV THENC ONCE_DEPTH_CONV DIMINDEX_CONV THENC
    NUM_REDUCE_CONV) THEN IMP_REWRITE_TAC [MOD_LT] THEN ARITH_TAC);;

let encode_ADRP = new_definition `encode_ADRP (dstreg:(5)word) (immhi:(19)word) (immlo:(2)word) =
  0x90000000 + val (immlo) * 2 EXP 29 +
               val (immhi) * 2 EXP 5 +
               val dstreg`;;

let decode_encode_ADRP = prove (`decode (word (encode_ADRP dstreg immhi immlo)) =
  SOME (arm_ADRP (XREG' dstreg) (word_join immhi immlo:(21)word))`,
  MATCH_MP_TAC (
    let th = SPEC `word (encode_ADRP dstreg immhi immlo):int32` decode in
    let tm = rhs (concl th) in
    let A, tr = bm_build_tree (rhs (concl th)) in
    let a = Array.init 32 (fun i -> Some ((0x90000000 land (1 lsl i)) != 0)) in
    (DISCH_ALL o REWRITE_RULE [] o TRANS th)
      (hd (snd (snd (get_dt a (bm_add_pos tr tm)))))) THEN
  REWRITE_TAC [encode_ADRP] THEN
  MAP_EVERY SPEC_TAC [`immlo:2 word`,`immlo:2 word`;`immhi:(19)word`,`immhi:(19)word`;`dstreg:(5)word`,`dstreg:(5)word`] THEN
  REWRITE_TAC [FORALL_VAL_GEN; VAL_WORD; CONSPAT_pat_set; NILPAT_pat_set;
    word1; bitval] THEN
  CONV_TAC (DEPTH_CONV UNWIND_CONV THENC ONCE_DEPTH_CONV DIMINDEX_CONV THENC
    NUM_REDUCE_CONV) THEN IMP_REWRITE_TAC [MOD_LT] THEN ARITH_TAC);;

let encode_ADD_rri64 = new_definition `encode_ADD_rri64 (dstreg:(5)word) (srcreg:(5)word) (imm12:(12)word) =
  0x91000000 + val (imm12) * 2 EXP 10 +
               val srcreg * 2 EXP 5 +
               val dstreg`;;

let decode_encode_ADD_rri64 = prove (
  `decode (word (encode_ADD_rri64 dstreg srcreg imm12)) =
    SOME (arm_ADD (XREG_SP dstreg) (XREG_SP srcreg) (rvalue (word (val imm12))))`,
  MATCH_MP_TAC (
    let th = SPEC `word (encode_ADD_rri64 dstreg srcreg imm12):int32` decode in
    let tm = rhs (concl th) in
    let A, tr = bm_build_tree (rhs (concl th)) in
    let a = Array.init 32 (fun i -> Some ((0x91000000 land (1 lsl i)) != 0)) in
    (DISCH_ALL o CONV_RULE (ONCE_DEPTH_CONV let_CONV) o REWRITE_RULE [arm_addop] o
      INST [`T`,`sf:bool`;`F`,`S:bool`;`F`,`op:bool`;`F`,`sh:bool`] o TRANS th)
      (hd (snd (snd (get_dt a (bm_add_pos tr tm)))))) THEN
  REWRITE_TAC [encode_ADD_rri64] THEN
  MAP_EVERY SPEC_TAC [`imm12:12 word`,`imm12:12 word`;`dstreg:(5)word`,`dstreg:(5)word`;
      `srcreg:(5)word`,`srcreg:(5)word`] THEN
  REWRITE_TAC [FORALL_VAL_GEN; VAL_WORD; CONSPAT_pat_set; NILPAT_pat_set;
    word1; bitval] THEN
  CONV_TAC (DEPTH_CONV UNWIND_CONV THENC ONCE_DEPTH_CONV DIMINDEX_CONV THENC
    NUM_REDUCE_CONV) THEN IMP_REWRITE_TAC [MOD_LT] THEN ARITH_TAC);;


let split_32_64 F =
  let a = F `:32` and b = F `:64` in
  fun ty -> match Num.int_of_num (dest_finty ty) with
  | 32 -> a
  | 64 -> b
  | _ -> failwith "split_32_64";;

let REG_CONV =
  let xs = [|X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10;X11;X12;X13;X14;X15;
             X16;X17;X18;X19;X20;X21;X22;X23;X24;X25;X26;X27;X28;X29;X30;XZR|]
  and ws = [|W0; W1; W2; W3; W4; W5; W6; W7; W8; W9; W10;W11;W12;W13;W14;W15;
             W16;W17;W18;W19;W20;W21;W22;W23;W24;W25;W26;W27;W28;W29;W30;WZR|]
  and qs = [|Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9; Q10;Q11;Q12;Q13;Q14;Q15;
             Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31|]
  and ds = [|D0; D1; D2; D3; D4; D5; D6; D7; D8; D9; D10;D11;D12;D13;D14;D15;
          D16;D17;D18;D19;D20;D21;D22;D23;D24;D25;D26;D27;D28;D29;D30;D31|] in
  List.iter (fun A -> Array.iteri (fun i th -> A.(i) <- SYM th) A) [xs;ws;qs;ds];
  let _ =
    let th1,th2 = (CONJ_PAIR o prove) (`XREG 31 = XZR /\ WREG 31 = WZR`,
      REWRITE_TAC [ARM_ZERO_REGISTER]) in
    xs.(31) <- th1; ws.(31) <- th2 in
  let xsp,wsp =
    let xth = REWRITE_RULE [GSYM XREG_SP; GE;
        REWRITE_RULE [GSYM NOT_LE] (ASSUME `n < 31`)] (SYM XREG) in
    let wth = REWRITE_RULE [xth; GSYM WREG] (SPEC `word n:5 word` WREG_SP) in
    let sp = REWRITE_RULE [GSYM XREG_SP] SP in
    let wsp = REWRITE_RULE [GSYM WREG_SP; sp] WSP in
    let F spth regth A = Array.mapi (fun i th ->
      if i = 31 then SYM spth else
      let th' = INST [mk_numeral (num i),`n:num`] regth in
      TRANS (PROVE_HYP (EQT_ELIM (NUM_RED_CONV (hd (hyp th')))) th') th) A in
    F sp xth xs, F wsp wth ws in
  let xs',ws',qs',ds' =
    let F th' A = Array.mapi (fun i ->
      TRANS (CONV_RULE (RAND_CONV (RAND_CONV WORD_RED_CONV))
        (SPEC (mk_comb (`word:num->5 word`, mk_numeral (num i))) th'))) A in
    F XREG' xs, F WREG' ws, F QREG' qs,F DREG' ds in
  function
  | Comb(Const("XREG",_),n) -> xs.(Num.int_of_num (dest_numeral n))
  | Comb(Const("WREG",_),n) -> ws.(Num.int_of_num (dest_numeral n))
  | Comb(Const("XREG'",_),Comb(Const("word",_),n)) ->
    xs'.(Num.int_of_num (dest_numeral n))
  | Comb(Const("WREG'",_),Comb(Const("word",_),n)) ->
    ws'.(Num.int_of_num (dest_numeral n))
  | Comb(Const("QREG'",_),Comb(Const("word",_),n)) ->
    qs'.(Num.int_of_num (dest_numeral n))
  | Comb(Const("DREG'",_),Comb(Const("word",_),n)) ->
    ds'.(Num.int_of_num (dest_numeral n))
  | Comb(Const("XREG_SP",_),Comb(Const("word",_),n)) ->
    xsp.(Num.int_of_num (dest_numeral n))
  | Comb(Const("WREG_SP",_),Comb(Const("word",_),n)) ->
    wsp.(Num.int_of_num (dest_numeral n))
  | _ -> failwith "REG_CONV";;

let QLANE_CONV =
  GEN_REWRITE_CONV I [QLANE] THENC LAND_CONV REG_CONV;;

let CONDITION_CONV =
  let pths =
    let l = map SYM CONDITION_CLAUSES in
    Array.init 16 (fun i -> find ((=) i o
      Num.int_of_num o dest_numeral o rand o rand o lhs o concl) l) in
  function
  | Comb(Const("Condition",_),Comb(Const("word",_),n)) ->
    pths.(Num.int_of_num (dest_numeral n))
  | _ -> failwith "CONDITION_CONV";;

let bool_split pth =
  let pthT = pth `T` and pthF = pth `F` in
  function
  | Const("T",_) -> pthT
  | Const("F",_) -> pthF
  | e -> failwith "bool_split";;

let BINARY_NSUM_CONV =
  let pth0 = prove (`nsum {i | i < 0 /\ p i} f = _0`,
     REWRITE_TAC [LT; EMPTY_GSPEC; NSUM_CLAUSES; NUMERAL])
  and pthS = prove (`SUC a' = a ==>
    nsum {i | i < a /\ p i} (\i. 2 EXP i) =
    (if p 0 then BIT1 else BIT0)
      (nsum {i | i < a' /\ p (SUC i)} (\i. 2 EXP i))`,
    DISCH_THEN (SUBST1_TAC o SYM) THEN
    MP_TAC (ISPECL [`SUC`; `\i. 2 EXP i`;
      `{i | i < a' /\ p (SUC i)}`] NSUM_IMAGE) THEN
    ANTS_TAC THENL [METIS_TAC [SUC_INJ]; ALL_TAC] THEN
    REWRITE_TAC [o_DEF; EXP; NSUM_LMUL] THEN
    COND_CASES_TAC THENL (map (fun t ->
      SUBGOAL_THEN t (SUBST1_TAC) THENL [
        REWRITE_TAC [EXTENSION; IN_ELIM_THM; IN_INSERT; IN_IMAGE] THEN
        GEN_TAC THEN DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN SUBST1_TAC)
          (SPEC `x:num` num_CASES) THEN
        ASM_REWRITE_TAC [CONJUNCT1 LT; LT_0; LT_SUC; SUC_INJ;
          ARITH_RULE `~(0 = SUC n)`] THEN
        CONV_TAC (ONCE_DEPTH_CONV UNWIND_CONV) THEN REFL_TAC;
        DISCH_THEN (fun th ->
          CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [BIT0; BIT1])) THEN
          IMP_REWRITE_TAC [GSYM MULT_2; SYM th; NSUM_CLAUSES; IN_IMAGE;
            ARITH_RULE `~(0 = SUC n)`; ARITH_RULE `2 EXP 0 + x = SUC x`] THEN
          MATCH_MP_TAC FINITE_IMAGE THEN ASSUME_TAC th THEN
          MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{i:num | i < a'}` THEN
          REWRITE_TAC [FINITE_NUMSEG_LT; SUBSET; IN_ELIM_THM] THEN
          METIS_TAC [])])
      [`{i | i < SUC a' /\ p i} =
        0 INSERT IMAGE SUC {i | i < a' /\ p (SUC i)}`;
       `{i | i < SUC a' /\ p i} = IMAGE SUC {i | i < a' /\ p (SUC i)}`]))
  and zero_conv = TRY_CONV (PART_MATCH lhs (REWRITE_RULE [NUMERAL] BIT0_0)) in
  fun conv -> function
  | Comb(Comb(Const("nsum",_),s),f) as t when aconv f `\i. 2 EXP i` ->
    let rec go n =
      if n = 0 then PART_MATCH lhs pth0 else
      PART_MATCH lhs (MATCH_MP pthS
        (NUM_SUC_CONV (mk_comb (`SUC`, mk_numeral (num (n-1)))))) THENC
      COMB2_CONV
        (RATOR_CONV (LAND_CONV (TRY_CONV BETA_CONV THENC conv)) THENC REWRITE_CONV [])
        (go (n-1)) THENC zero_conv in
    let _,ls,_ = term_match [] `{i:num | i < a /\ p i}` s in
    (go (Num.int_of_num (dest_numeral (vsubst ls `a:num`))) THENC
      PART_MATCH lhs (SYM (SPEC_ALL NUMERAL))) t
  | _ -> failwith "BINARY_NSUM_CONV";;

let DECODE_BITMASK_CONV =
  let pths = split_32_64 (fun ty -> bool_split (fun n ->
    Array.init 64 (fun r -> Array.init 64 (fun s -> lazy (
      let r = mk_comb (`word:num->6 word`, mk_numeral (num r))
      and s = mk_comb (`word:num->6 word`, mk_numeral (num s)) in
      CONV_RULE (WORD_REDUCE_CONV THENC
        NUM_REDUCE_CONV THENC ONCE_DEPTH_CONV let_CONV THENC
        NUM_REDUCE_CONV THENC ONCE_DEPTH_CONV let_CONV THENC
        NUM_REDUCE_CONV THENC ONCE_DEPTH_CONV let_CONV THENC
        NUM_REDUCE_CONV THENC REWRITE_CONV [
          WORD_OF_BITS_AS_WORD; IN_ELIM_THM; DIMINDEX_32; DIMINDEX_64] THENC
        TRY_CONV (funpow 3 RAND_CONV (BINARY_NSUM_CONV NUM_REDUCE_CONV)))
      (REWRITE_RULE [word1; bitval]
        (SPECL [n; r; s] (INST_TYPE [ty,`:N`] decode_bitmask)))))))) in
  function
  | Comb(Comb(Comb(Const("decode_bitmask",_),n),
      Comb(Const("word",_),immr)),Comb(Const("word",_),imms)) as t ->
    let nty = dest_word_ty (hd (snd (dest_type (type_of t)))) in
    Lazy.force (pths nty n)
      .(Num.int_of_num (dest_numeral immr))
      .(Num.int_of_num (dest_numeral imms))
  | _ -> failwith "DECODE_BITMASK_CONV";;

let DECODE_SHIFT_CONV =
  GEN_REWRITE_CONV I [decode_shift] THENC
  BITMATCH_SEQ_CONV;;

let DECODE_EXTENDTYPE_CONV =
  GEN_REWRITE_CONV I [decode_extendtype] THENC
  BITMATCH_SEQ_CONV;;

let dest_component = function
| Tyapp("component", [A; B]) -> A, B
| _ -> failwith "dest_component";;

let OPERAND_ALIAS_CONV =
  GEN_REWRITE_CONV ONCE_DEPTH_CONV [SHIFTEDREG_TRIVIAL];;

let ALIAS_CONV =
  let self = ref NO_CONV in
  let ALIAS_CONV t = !self t in
  let net = basic_net() in
  let specialize th f =
    let g ty xth =
      let th' = INST_TYPE (map (fun ty' -> ty,ty')
        (type_vars_in_term (concl th))) th in
      try f (CONV_RULE (CHANGED_CONV (REWRITE_CONV [SYM xth])) th')
      with _ -> I in
    g `:64` XZR_ZR o g `:32` WZR_ZR o f th in
  let f th =
    if can (find_term
        (fun e -> `invert_condition cc` = e) o lhs) (concl th) then
      let th = REWRITE_RULE [INVERT_CONDITION_TWICE]
        (INST [`invert_condition cc`,`cc:condition`] th) in
      specialize th (fun th ->
        net_of_conv (lhs (concl th)) (REWR_CONV th THENC
          REWRITE_CONV [invert_condition] THENC TRY_CONV ALIAS_CONV))
    else specialize th (fun th ->
      net_of_conv (lhs (concl th)) (REWR_CONV th)) in
  let net = itlist (f o SYM o SPEC_ALL) ARM_INSTRUCTION_ALIASES net in
  let arith_sideconv = DEPTH_CONV(DIMINDEX_CONV ORELSEC NUM_RED_CONV) in
  let MOVZ_CONV =
    (fun th -> MP th (EQT_ELIM (NUM_LT_CONV (lhand (concl th))))) o
    PART_MATCH (lhs o rand) (GSYM arm_MOVZ_ALT)
  and ASR_CONV =
    (fun th -> MP th (EQT_ELIM(arith_sideconv(lhand(concl th))))) o
    PART_MATCH (lhs o rand) arm_ASR_ALIAS
  and LSR_CONV =
    (fun th -> MP th (EQT_ELIM(arith_sideconv(lhand(concl th))))) o
    PART_MATCH (lhs o rand) arm_LSR_ALIAS
  and LSL_CONV =
    (fun th -> MP th (EQT_ELIM (arith_sideconv(lhand(concl th))))) o
    PART_MATCH (lhs o rand) arm_LSL_ALIAS THENC
    RAND_CONV arith_sideconv in
  let net = itlist (uncurry net_of_conv)
    [`arm_MOVZ (Rd:(armstate,N word)component) (word imm) 0`,MOVZ_CONV;
     `arm_SBFM (Rd:(armstate,N word)component) Rn immr imms`,ASR_CONV;
     `arm_UBFM (Rd:(armstate,N word)component) Rn immr imms`,
     (LSR_CONV ORELSEC LSL_CONV)]
    net in
  self := ONCE_DEPTH_CONV (REWRITES_CONV net);
  OPERAND_ALIAS_CONV THENC ALIAS_CONV;;

let PURE_DECODE_CONV =
  let open Compute in

  let custom_word_red_conv_list =
    (* No WORD_IWORD_CONV *)
    filter (fun pat,_ ->
      if is_comb pat then let c = fst (strip_comb pat) in
        not (is_const c && name_of c = "iword")
      else true) word_red_conv_list in
  let custom_word_compute_add_convs =
    let convlist = map (fun pat,the_conv ->
      let c,args = strip_comb pat in (c,length args,the_conv))
      custom_word_red_conv_list in
    fun (compset:Compute.compset) ->
      itlist (fun newc () -> Compute.add_conv newc compset) convlist () in

  let decode_rw =
    let rw = bool_compset() in
    (* avoid folding the branches of conditional expression before evaluating
       its condition *)
    set_skip rw `COND: bool -> A -> A -> A` (Some 1);
    set_skip rw `_MATCH:A->(A->B->bool)->B` (Some 1);
    set_skip rw `_BITMATCH:(N)word->(num->B->bool)->B` (Some 1);
    (* basic expressions *)
    custom_word_compute_add_convs rw;
    int_compute_add_convs rw;
    num_compute_add_convs rw;
    add_thms [obind; LET_END_DEF] rw;
    (* Do not add _BITMATCH. These will be covered by conceal_bitmatch. *)
    add_conv (`_MATCH:A->(A->B->bool)->B`, 2, MATCH_CONV) rw;

    (* components and instructions *)
    List.iter (fun tm -> add_conv (tm, 1, REG_CONV) rw) [`XREG'`; `WREG'`; `QREG'`; `DREG'`; `XREG_SP`; `WREG_SP`];
    add_thms [arm_adcop; arm_addop; arm_adv_simd_expand_imm;
              arm_bfmop; arm_ccop; arm_csop;
              arm_ldst; arm_ldst_q; arm_ldst_d; arm_ldstb; arm_ldstp; arm_ldstp_q; arm_ldstp_d;
              arm_ldst2; arm_ldstp_2q] rw;
    (* .. that have bitmatch exprs inside *)
    List.iter (fun def_th ->
        let Some (conceal_th, opaque_const, opaque_arity, opaque_def, opaque_conv) =
            conceal_bitmatch (concl def_th) in
        (* bitmatch concealed under opaque_const *)
        let concealed_def_th = GEN_REWRITE_RULE I [conceal_th] def_th in
        add_thms [concealed_def_th] rw;
        (* add a conversion for this *)
        add_conv (opaque_const, opaque_arity, opaque_conv) rw
      ) [arm_logop; arm_movop; arm_lsvop];

    add_thms [QLANE] rw;
    add_conv (`Condition`, 1, CONDITION_CONV) rw;
    (* decode fns that have bitmatch exprs inside *)
    List.iter (fun def_th ->
        let Some (conceal_th, opaque_const, opaque_arity, opaque_def, opaque_conv) =
            conceal_bitmatch (concl def_th) in
        (* bitmatch concealed under opaque_const *)
        let concealed_def_th = GEN_REWRITE_RULE I [conceal_th] def_th in
        add_thms [concealed_def_th] rw;
        (* add a conversion for this *)
        add_conv (opaque_const, opaque_arity, opaque_conv) rw
      ) [decode; decode_shift; decode_extendtype];

    (* decode functions *)
    add_conv (`decode_bitmask`, 3, DECODE_BITMASK_CONV) rw;
    (* adding decode_encode* lemmas after decode gives higher priority
       to these rules *)
    add_thms [decode_encode_BL; decode_encode_ADR;
              decode_encode_ADRP; decode_encode_ADD_rri64] rw;

    rw in
  let the_conv = WEAK_CBV_CONV decode_rw in
  fun t ->
    try
      let th = the_conv t in
      let c = concl th in (* c should be: `decode .. = SOME ...` *)
      let r,_ = dest_comb (rhs c) in
      if is_const r && name_of r = "SOME" then th else failwith ""
    with _ -> failwith ("PURE_DECODE_CONV: " ^ (string_of_term t));;

let DECODE_CONV tm =
  let th = PURE_DECODE_CONV tm in
  try CONV_RULE (RAND_CONV (RAND_CONV ALIAS_CONV)) th
  with _ -> th;;

(* ------------------------------------------------------------------------- *)
(* Testing and preparation.                                                  *)
(* ------------------------------------------------------------------------- *)

let rec decode_all = function
| Const("NIL",_) -> []
| tm ->
  let th1 = READ_WORD_CONV (mk_comb (`read_int32`, tm)) in
  let a,next = dest_pair (rand (rhs (concl th1))) in
  let th = DECODE_CONV (mk_comb (`decode`, a)) in
  let h = try rand (rhs (concl th))
    with Failure msg ->
      let msg' = "Term `" ^ (string_of_term (concl th)) ^ "`: " ^ msg in
      failwith msg' in
  h :: decode_all next;;

let dest_cons4 =
  let assert_byte n = function
  | Comb(Const("word",_),a) -> dest_numeral a = num n
  | _ -> false in
  fun n t -> match t with
  | Comb(Comb(Const("CONS",_),a1), Comb(Comb(Const("CONS",_),a2),
      Comb(Comb(Const("CONS",_),a3), Comb(Comb(Const("CONS",_),a4),tm)))) when
    0 <= n && n <= 0xffffffff &&
    assert_byte (n land 0xff) a1 &&
    assert_byte ((n lsr 8) land 0xff) a2 &&
    assert_byte ((n lsr 16) land 0xff) a3 &&
    assert_byte ((n lsr 24) land 0xff) a4 -> tm
  | _ -> failwith ("dest_cons4: 4-byte inst code " ^ string_of_int n ^
                   " != first 4 bytes of " ^ string_of_term t);;

(* Asserts that the input term is the given list of words, and returns it. *)
let assert_word_list tm ls =
  if type_of tm = `:byte list` then
    let rec go = function
    | [], Const("NIL",_) -> ()
    | n::ls, tm -> go (ls, dest_cons4 n tm)
    | _ -> failwith "assert_word_list" in
    go (ls, tm)
  else failwith "assert_word_list";
  tm;;

let define_word_list name tm =
  try new_definition (mk_eq (mk_var (name, `:byte list`), tm))
  with Failure _ ->
    new_definition (mk_eq (mk_mconst (name, `:byte list`), tm));;

let define_assert_word_list name tm ls =
  define_word_list name (assert_word_list tm ls);;

(* define `name args = tm` where the type of tm is `:byte list` *)
let define_relocated_mc name (args, tm:term list * term): thm =
  let rec mk_tm_comb f A = function
  | [] -> f (name, A)
  | (v::vs) -> mk_comb (mk_tm_comb f (mk_fun_ty (type_of v) A) vs, v) in
  let args0,args = args,rev args in
  try new_definition (list_mk_forall
    (args0, mk_eq (mk_tm_comb mk_var `:byte list` args, tm)))
  with Failure _ ->
    new_definition (list_mk_forall
      (args0, mk_eq (mk_tm_comb mk_mconst `:byte list` args, tm)));;

needs "common/elf.ml";;

let make_fn_word_list, make_fn_word_list_reloc =
  let print_list rhs_col =
    let indent = "\n" ^ String.make rhs_col ' ' in
    fun rels start end_ head bs dec ->
      let buf = Buffer.create 1024 in
      Buffer.add_string buf start;
      let rec go pc prev_inst_printer = function
      | [] -> prev_inst_printer ""
      | (inst::l) ->
        let () = prev_inst_printer ";" in
        go (pc + 4) (fun s ->
          (* s is either "" or ";" *)
          let opcode = get_int_le bs pc 4 in
          match rels pc with
          | None ->
          (Printf.bprintf buf "  %s0x%08x%s" head opcode s;
            let space_size = String.length head + String.length s + 12 in
            Printf.bprintf buf "%s(* %s *)\n"
              (if space_size < rhs_col then String.make (rhs_col - space_size) ' '
              else indent)
            (string_of_term inst))

          | Some (Arm_call26,sym,addend) ->
          Printf.bprintf buf "  BL (mk_var(\"%s\",`:num`),%d,%d)%s\n" sym addend pc s

          | Some (Arm_adr_prel_lo21,sym,addend) ->
          let dstreg = opcode land 31 in
          Printf.bprintf buf "  ADR (mk_var(\"%s\",`:num`),%d,%d,%d)%s\n" sym addend pc dstreg s

          | Some (Arm_adr_prel_pg_hi21,sym,addend) ->
          let dstreg = opcode land 31 in
          Printf.bprintf buf "  ADRP (mk_var(\"%s\",`:num`),%d,%d,%d)%s\n" sym addend pc dstreg s

          | Some (Arm_add_abs_lo12_nc,sym,addend) ->
          let dstreg = opcode land 31 in
          let srcreg = (opcode lsr 5) land 31 in
          Printf.bprintf buf "  ADD_rri64 (mk_var(\"%s\",`:num`),%d,%d,%d)%s\n"
              sym addend dstreg srcreg s

          | Some (Arm_condbr19,sym,0) -> failwith "unsupported Arm_condbr19") l in
      go 0 (fun _ -> ()) dec;
      Printf.bprintf buf end_;
      Buffer.contents buf in
  print_list 20 (fun _ -> None) "[\n" "];;\n" "",
  let print_list_reloc = print_list 24 in
  fun (bstext, constants, rels) ->
    let r = ref rels in
    let f i = match !r with
    | (ty,(off,sym,add)) :: rels when off = i -> r := rels; Some (ty,sym,add)
    | _ -> None in
    (* The input argument of function X must match that of append_reloc_X.
     * ex) BL: append_reloc_BL
     *)
    print_list_reloc f "(fun w BL ADR ADRP ADD_rri64 -> [\n" "]);;\n" "w " bstext;;
(*
let trim_ret_core dec =
  let m1 = Array.length dec - 1 in
  if m1 < 0 then failwith "trim_ret: empty" else
  let lr,r = dec.(m1) in
  if r <> `RET` then
    failwith "trim_ret: function does not end with RET" else
  let rec go a b i j =
    match if i < j then
      match dec.(i), dec.(j) with
      | (n,Comb(Const("PUSH",_),tm)), (m,Comb(Const("POP",_),tm'))
        when tm = tm' -> Some(a+n,b+m,tm)
      | _ -> None
    else None with
    | Some(a',b',tm) -> let ls,r = go a' b' (i+1) (j-1) in tm::ls, r
    | None -> [], (a, b, Array.sub dec i (j+1-i)) in
  go 0 lr 0 (m1-1);;

let trim_ret ((bs:term array), dec) =
  let ls,(a,b,dec) = trim_ret_core (Array.of_list dec) in
  ls, a, (Array.sub bs a (Array.length bs - b - a), Array.to_list dec);; *)

let rec dest_mc_list = function
| Const("NIL",_) -> []
| Comb(Comb(Const("CONS",_),a),t) -> a :: dest_mc_list t
| Comb(Comb(Const("APPEND",_),a),t) -> a :: dest_mc_list t
| _ -> failwith "dest_mc_list";;

let rec term_of_mc_list =
  let nil = `NIL:byte list`
  and cons = `CONS:byte->byte list->byte list`
  and append = `APPEND:byte list->byte list->byte list` in
  function
  | [] -> nil
  | (Comb(Const("word",_),_) as a) :: ls ->
    mk_comb (mk_comb (cons, a), term_of_mc_list ls)
  | a :: ls -> mk_comb (mk_comb (append, a), term_of_mc_list ls);;
(*
let trim_ret_off tm =
  let _,n,bs = trim_ret (Array.of_list (dest_mc_list tm), decode_all tm) in
  n,term_of_mc_list (Array.to_list (fst bs));;

let trim_ret' = snd o trim_ret_off;; *)

let N_SUBLIST_CONV =
  let pth1,pth2 =
    W f_f_ (PART_MATCH lhs o SPEC_ALL) (CONJ_PAIR (GSYM APPEND))
  and pth3 = PART_MATCH lhs (SPEC_ALL APPEND_ASSOC) in
  fun th ->
    let rec right tm = function
    | Const("NIL",_) -> pth1 tm
    | Comb(Comb(Const("CONS",_),_),l) ->
      let f,tm' = dest_comb tm in
      let th = AP_TERM f (right tm' l) in
      TRANS th (pth2 (rhs (concl th)))
    | Comb(Comb(Const("APPEND",_),_),l) ->
      let f,tm' = dest_comb tm in
      let th = AP_TERM f (right tm' l) in
      TRANS th (pth3 (rhs (concl th)))
    | _ -> failwith "N_SUBLIST_CONV" in
    let rec left n tm = if n = 0 then
      let th = SYM th in
      let th1 = right tm (lhs (concl th)) in
      let th2 = CONV_RULE (RAND_CONV (LAND_CONV (K th))) th1 in
      TRANS th2 (pth1 (rhs (concl th2)))
    else
      let f,tm' = dest_comb tm in
      let th = AP_TERM f (left (n-1) tm') in
      TRANS th (pth2 (rhs (concl th))) in
    left;;
(*
  let test1 = new_definition `test1 = [1;2;3;4]`;;
  N_SUBLIST_CONV test1 1 `[0;1;2;3;4;5]`;;

  - : thm = |- [0; 1; 2; 3; 4; 5] = APPEND [0] (APPEND test1 [5])
*)
(*
let define_trim_ret_thm name th =
  let th = SPEC_ALL th in
  let df,tm1 = dest_eq (concl th) in
  let n, tm = trim_ret_off tm1 in
  let rec args ls = function
  | Comb(f,v) -> args (v::ls) f
  | _ -> ls in
  let defn = define_relocated_mc name (args [] df, tm) in
  defn, TRANS th (N_SUBLIST_CONV (SPEC_ALL defn) n tm1);; *)

let define_from_elf name file =
  define_word_list name (term_of_bytes (load_elf_contents_arm file));;

let define_assert_from_elf name file =
  define_assert_word_list name (term_of_bytes (load_elf_contents_arm file));;

let print_literal_from_elf file =
  let bs = load_elf_contents_arm file in
  print_string (make_fn_word_list bs (decode_all (term_of_bytes bs)));;

let save_literal_from_elf deffile objfile =
  let bs = load_elf_contents_arm objfile in
  let ls = make_fn_word_list bs (decode_all (term_of_bytes bs)) in
  file_of_string deffile ls;;

let mk_bytelist = C (curry mk_list) `:byte`;;

let extract_coda_from_elf =
  let rec try_decode_all = function
  | Const("NIL",_) -> []
  | tm ->
    let th1 = READ_WORD_CONV (mk_comb (`read_int32`, tm)) in
    let a,next = dest_pair (rand (rhs (concl th1))) in
    try rand(rhs(concl(DECODE_CONV (mk_comb (`decode`, a)))))::
        try_decode_all next
    with Failure _ -> [] in
  fun possize file ->
    let bs = load_elf_contents_arm file in
    let bt = term_of_bytes bs in
    let bl = dest_list bt in
    let codesize = if 0 <= possize && possize <= length bl then possize
                   else 4 * length(try_decode_all bt) in
    (mk_bytelist F_F mk_bytelist) (chop_list codesize bl);;

let stringize_coda_from_elf possize file =
   let bs = load_elf_contents_arm file in
   let ct,dt = extract_coda_from_elf possize file in
   let cs = make_fn_word_list bs (decode_all ct) in
   let ds = string_of_term(mk_list(map rand (dest_list dt),`:num`)) in
   cs ^ ds ^ ";;\n";;

let print_coda_from_elf possize file =
  Format.print_string (stringize_coda_from_elf possize file);;

let save_coda_from_elf deffile possize objfile =
  file_of_string deffile (stringize_coda_from_elf possize objfile);;

let define_coda_from_elf possize codename dataname file =
  let ct,dt = extract_coda_from_elf possize file in
  let cdef = define_word_list codename ct in
  let ddef = define_word_list dataname dt in
  cdef,ddef;;

let define_coda_literal_from_elf codename dataname file codelist datalist =
  let ct,dt = extract_coda_from_elf (4 * length codelist) file in
  let databytes =
    mk_bytelist
     (map (curry mk_comb `word:num->byte` o mk_small_numeral) datalist) in
  if databytes <> dt then failwith "data part mismatch" else
  let cdef = define_assert_word_list codename ct codelist in
  let ddef = define_word_list dataname dt in
  cdef,ddef;;

(* Usage:
Use
  print_literal_from_elf "arm/generic/bignum_madd.o";;
to print the assembly listing, and copy it into the code below:

let bignum_madd_subroutine =
define_assert_from_elf "bignum_madd_subroutine" "arm/generic/bignum_madd.o" [
  0x53;                    (* PUSH (% rbx) *)
...
  0xc3                     (* RET *)
];;

let bignum_madd_mc = define_word_list "bignum_madd_mc"
  (trim_ret' (rhs (concl bignum_madd_subroutine)));; *)

(*** term_of_relocs_arm returns a pair
    (a list of new HOL Light variables that represent the symbolic addresses,
     a HOL Light term that represents the 'symbolic' byte list).

    assert_relocs takes a pair
    (a list of HOL Light vars for the symbolic addresses,
     the symbolic byte list term)
    as well as the large OCaml function printed by print_literal_relocs_from_elf, and checks whether the OCaml function
    matches the symbolic byte list term.
 ***)
let term_of_relocs_arm, assert_relocs =
  (* The append_reloc_* functions implement 5.7.3.3. Relocation operations
     in https://github.com/ARM-software/abi-aa/blob/main/aaelf64/aaelf64.rst#5733relocation-operations .
     To search, remove the "R_AARCH64_" prefix and find the remaining
     string (e.g., "CALL26").
  *)

  (* R_AARCH64_CALL26 *)
  let reloc_BL = `APPEND (bytelist_of_num 4
      (encode_BL (&(v + addend) - &(pc + i))))` in
  let append_reloc_BL (sym,addend,pcofs: term*int*int) next_instbytes =
    curry mk_comb
      (vsubst [sym,`v:num`; mk_small_numeral addend,`addend:num`;
               mk_small_numeral pcofs,`i:num`] reloc_BL)
      next_instbytes in

  (* R_AARCH64_ADR_PREL_LO21 *)
  let reloc_ADR = `APPEND (bytelist_of_num 4
      (encode_ADR (word dstreg)
          (word_subword
            (word_sub (word (sym + addend):int64) (word (pc + pcofs)))
            (2,19):(19)word)
          (word_subword
            (word_sub (word (sym + addend):int64) (word (pc + pcofs)))
            (0,2):(2)word)))` in
  let append_reloc_ADR (sym,addend,pcofs,dstreg: term*int*int*int) next_instbytes =
    curry mk_comb (vsubst
      [mk_small_numeral dstreg,`dstreg:num`;
        sym,`sym:num`; mk_small_numeral addend,`addend:num`;
        mk_small_numeral pcofs,`pcofs:num`] reloc_ADR)
      next_instbytes in

  (* R_AARCH64_ADR_PREL_PG_HI21 *)
  let reloc_ADRP = `APPEND (bytelist_of_num 4
      (encode_ADRP (word dstreg)
        (word_subword (word_sub
            (word_and (word (sym + addend)) (word 0xFFFFFFFFFFFFF000))
            (word_and (word (pc + pcofs)) (word 0xFFFFFFFFFFFFF000)):int64)
          (14,19):(19)word)
        (word_subword (word_sub
            (word_and (word (sym + addend)) (word 0xFFFFFFFFFFFFF000))
            (word_and (word (pc + pcofs)) (word 0xFFFFFFFFFFFFF000)):int64)
          (12,2):(2)word)))` in
  let append_reloc_ADRP (sym,addend,pcofs,dstreg: term*int*int*int) next_instbytes =
    curry mk_comb (vsubst
      [mk_small_numeral dstreg,`dstreg:num`;
        sym,`sym:num`; mk_small_numeral addend,`addend:num`;
        mk_small_numeral pcofs,`pcofs:num`] reloc_ADRP)
      next_instbytes in

  (* R_AARCH64_ADD_ABS_LO12_NC *)
  let reloc_ADD_rri64 = `APPEND (bytelist_of_num 4
      (encode_ADD_rri64 (word dstreg) (word srcreg)
        (word_subword (word (sym + addend):int64) (0,12):(12)word)))` in
  let append_reloc_ADD_rri64 (sym,addend,dstreg,srcreg: term*int*int*int) next_instbytes =
      curry mk_comb (vsubst
        [mk_small_numeral dstreg,`dstreg:num`;
         mk_small_numeral srcreg,`srcreg:num`;
         sym,`sym:num`; mk_small_numeral addend,`addend:num`] reloc_ADD_rri64)
        next_instbytes in

  ((* term_of_relocs_arm *)
   term_of_relocs (fun bstext,ty,pcoffset,sym,addend -> 4,
    let opcode = get_int_le bstext pcoffset 4 in
    if ty = Arm_call26 then
      if opcode = 0x94000000 (* BL with zero immediate *)
      then append_reloc_BL (sym,addend,pcoffset)
      else failwith "Cannot apply R_AARCH64_CALL26"

    else if ty = Arm_adr_prel_lo21 then
      if opcode land 0x9FFFFFE0 = 0x10000000 (* ADR with zero imm. *)
      then append_reloc_ADR (sym,addend,pcoffset,(opcode land 31))
      else failwith "Cannot apply R_AARCH64_ADR_PREL_LO21"

    else if ty = Arm_adr_prel_pg_hi21 then
      if opcode land 0x9FFFFFE0 = 0x90000000 (* ADRP with zero imm. *)
      then append_reloc_ADRP (sym,addend,pcoffset,(opcode land 31))
      else failwith "Cannot apply R_AARCH64_ADR_PREL_PG_HI21"

    else if ty = Arm_add_abs_lo12_nc then
      if opcode land 0xFFFFFC00 = 0x91000000 (* ADD with zero imm. *)
      then
        let dstreg = opcode land 31 in
        let srcreg = (opcode lsr 5) land 31 in
        append_reloc_ADD_rri64 (sym,addend,dstreg,srcreg)
      else failwith "Cannot apply R_AARCH64_ADD_ABS_LO12_NC"

    else failwith "unsupported relocation kind")),

  ((* assert_relocs *)
   (* consume_word: check that tm[0..3] is n in little endian & increment pc *)
    let assert_word n (pc,tm) = pc+4, dest_cons4 n tm in
    let assert_reloc_maker append_reloc_fn arg (pc,code) =
      (* code is `APPEND (the symbolic expression for opcode) (next insts)`. *)
      let reloc_opcode, next_insns = dest_comb code in
      try
        (* Reproduce the symbolic opcode using the append_reloc fn and
           compare whether it is syntactically equal to the already
           embedded one *)
        append_reloc_fn arg next_insns = reloc_opcode;
        pc+4, next_insns
      with _ -> failwith ("could not check opcode " ^ (string_of_term reloc_opcode)) in

    (* opcode_fn is the large OCaml function printed by print_literal_relocs_from_elf *)
    fun (args,tm) opcode_fn ->
      let opcode_fn_implemented = opcode_fn
          (* This order should match the fn args printed by
            make_fn_word_list_reloc *)
          assert_word (* w *)
          (assert_reloc_maker append_reloc_BL) (* BL *)
          (assert_reloc_maker append_reloc_ADR) (* ADR *)
          (assert_reloc_maker append_reloc_ADRP) (* ADRP *)
          (assert_reloc_maker append_reloc_ADD_rri64) (* ADD_rri64 *) in
      if type_of tm = `:byte list` then
        match rev_itlist I opcode_fn_implemented (0,tm) with
        | _,Const("NIL",_) -> ()
        | _ -> failwith "assert_relocs"
      else failwith "assert_relocs";
      (args,tm));;

let define_assert_relocs name (tm:term list * term) printed_opcodes_fn
    (constants:(string * bytes) list)
    :(thm(*machine code def*) * thm list(*data definitions of constants*)) =
  assert_relocs tm printed_opcodes_fn;
  let mc_def = define_relocated_mc name tm in
  let mc_def_canonicalized =
    (* break APPEND(4-byte list, list) to 4 consecutive CONSs. *)
    let blth = (LAND_CONV (TOP_DEPTH_CONV num_CONV) THENC
                REWRITE_CONV[bytelist_of_num]) `bytelist_of_num 4 x` in
    REWRITE_RULE[APPEND; blth] mc_def in
  let datatype = `:((8)word)list` in
  (mc_def_canonicalized,
   map (fun (name,data) ->
      let dataterm = term_of_bytes data in (* returns (8)word list *)
      let defname = name ^ "_data" in
      (try new_definition(mk_eq(mk_var(defname,datatype), dataterm))
        with Failure _ ->
            new_definition(mk_eq(mk_mconst(defname,datatype), dataterm)))
    ) constants);;

let assert_relocs_from_elf (file:string) printed_opcodes_fn =
  let filebytes = load_file file in
  let text,constants,rel = load_elf_arm filebytes in
  assert_relocs (term_of_relocs_arm (text,constants,rel)) printed_opcodes_fn;;

let define_assert_relocs_from_elf name (file:string) printed_opcodes_fn =
  let filebytes = load_file file in
  let text,constants,rel = load_elf_arm filebytes in
  let mc_def,constants_data_defs = define_assert_relocs
      name (term_of_relocs_arm (text,constants,rel)) printed_opcodes_fn
      constants in
  (mc_def,constants_data_defs);;

let print_literal_relocs_from_elf (file:string) =
  let filebytes = load_file file in
  let bs = load_elf_arm filebytes in
  print_string (make_fn_word_list_reloc bs
    (decode_all (snd (term_of_relocs_arm bs))));;

let save_literal_relocs_from_elf (deffile:string) (objfile:string) =
  let filebytes = load_file objfile in
  let bs = load_elf_arm filebytes in
  let ls = make_fn_word_list_reloc bs
    (decode_all (snd (term_of_relocs_arm bs))) in
  file_of_string deffile ls;;
