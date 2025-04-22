(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Simplified model of aarch64 (64-bit ARM) semantics.                       *)
(* ========================================================================= *)

(*** We start with defining an observable microarchitectural event.
 *** This is used to describe the safety property of assembly programs such as
 *** the constant-time property.
 *** We define that an instruction raises an observable microarchitectural
 *** event if its cycles/power consumption/anything that can be observed by
 *** a side-channel attacker can vary depending on the inputs of
 *** the instruction. For example, instructions taking a constant number of
 *** cycles like ADD do not raise an observable event, whereas cond branch does.
 *** Its kinds (EventLoad/Store/...) describe the events distinguishable from
 *** each other by the attacker, and their parameters describe the values
 *** that are inputs and/or outputs of the instructions that will affect the
 *** observed cycles/etc.
 *** An opcode of instruction is not a parameter of the event, even if the
 *** number of taken cycles may depend on opcode. This relies on an assumption
 *** that a program is public information.
 *** One instruction can raise multiple events (e.g., one that reads PC from
 *** the memory and jumps to the address, even though this case will not exist
 *** in Arm).
 ***)
let armevent_INDUCT, armevent_RECURSION = define_type
  "armevent =
    // (address, byte length)
    EventLoad (int64#num)
    // (address, byte length)
    | EventStore (int64#num)
    // (src pc, destination pc)
    | EventJump (int64#int64)
  ";;

(*** For convenience we lump the stack pointer in as general register 31.
 *** The indexing is cleaner for a 32-bit enumeration via words, and in
 *** fact in some settings this may be interpreted correctly when register 31
 *** is used in an encoding (in our setting it means the zero register).
 ***
 *** As with x86 we assume a full 64-bit address space even though in practice
 *** it is often restricted to smaller (signed) portions
 ***
 *** We just have the basic flags and ignore exception masking flags, other
 *** system level stuff (for now)
 ***)

let armstate_INDUCT,armstate_RECURSION,armstate_COMPONENTS =
  define_auto_record_type
   "armstate =
     { PC: int64;                       // One 64-bit program counter
       registers : 5 word->int64;       // 31 general-purpose registers plus SP
       simdregisters: 5 word->int128;   // 32 SIMD registers
       flags: 4 word;                   // NZCV flags
       memory: 64 word -> byte;         // memory
       events: armevent list            // Observable uarch events
     }";;

let bytes_loaded = new_definition
 `bytes_loaded s pc l <=>
     read (memory :> bytelist(pc,LENGTH l)) s = l`;;

let bytes_loaded_nil = prove (`bytes_loaded s pc []`, REWRITE_TAC [
  bytes_loaded; READ_COMPONENT_COMPOSE; LENGTH; bytelist_clauses]);;

let bytes_loaded_append = prove
 (`bytes_loaded s pc (APPEND l1 l2) <=>
   bytes_loaded s pc l1 /\ bytes_loaded s (word_add pc (word (LENGTH l1))) l2`,
  REWRITE_TAC [bytes_loaded; READ_COMPONENT_COMPOSE; read_bytelist_append]);;

let bytes_loaded_unique = METIS [bytes_loaded]
 `!s pc l1 l2. bytes_loaded s pc l1 ==> bytes_loaded s pc l2 ==>
  LENGTH l1 = LENGTH l2 ==> l1 = l2`;;

let bytes_loaded_update = METIS [bytes_loaded]
 `!l n. LENGTH l = n ==> !s pc. bytes_loaded s pc l ==>
  !s'. read(memory :> bytelist(pc,n)) s' = read(memory :> bytelist(pc,n)) s ==>
    bytes_loaded s' pc l`;;

let bytes_loaded_of_append3 = prove
 (`!l l1 l2 l3. l = APPEND l1 (APPEND l2 l3) ==>
   !s pc. bytes_loaded s (word pc) l ==>
          bytes_loaded s (word (pc + LENGTH l1)) l2`,
  REWRITE_TAC [WORD_ADD] THEN METIS_TAC [bytes_loaded_append]);;

let BYTES_LOADED_SUB_LIST = prove
 (`!s pc l m n.
        bytes_loaded s pc l
        ==> bytes_loaded s (word_add pc (word m)) (SUB_LIST(m,n) l)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`l:byte list`; `m + n:num`] SUB_LIST_TOPSPLIT) THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) THEN
  REWRITE_TAC[bytes_loaded_append] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  REWRITE_TAC[SUB_LIST_SPLIT; ADD_CLAUSES; bytes_loaded_append] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  REWRITE_TAC[LENGTH_SUB_LIST; SUB_0; MIN] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[LE_CASES; SUB_LIST_TRIVIAL; bytes_loaded_nil]);;

let BYTES_LOADED_TRIM_LIST = prove
 (`!s pc l m n.
        bytes_loaded s pc l
        ==> bytes_loaded s (word_add pc (word m)) (TRIM_LIST(m,n) l)`,
  REWRITE_TAC[BYTES_LOADED_SUB_LIST; TRIM_LIST]);;

let aligned_bytes_loaded = new_definition
 `aligned_bytes_loaded s pc l <=>
  4 divides val pc /\ bytes_loaded s pc l`;;

let DIVIDES_4_VAL_WORD_64 = prove
 (`4 divides val (word pc:int64) <=> 4 divides pc`,
  let th1 = MATCH_MP DIVIDES_EXP_LE_IMP (ARITH_RULE `2 <= 64`) in
  let th2 = REWRITE_RULE [ARITH_RULE `2 EXP 2 = 4`] (SPEC `2` th1) in
  let th3 = MATCH_MP CONG_DIVIDES_MODULUS (CONJ
    (SPECL [`pc:num`; `2 EXP 64`] CONG_MOD) th2) in
  REWRITE_TAC [VAL_WORD; DIMINDEX_64; MATCH_MP CONG_DIVIDES th3]);;

let aligned_bytes_loaded_word = prove
 (`aligned_bytes_loaded s (word pc) l <=>
   4 divides pc /\ bytes_loaded s (word pc) l`,
  REWRITE_TAC [aligned_bytes_loaded; DIVIDES_4_VAL_WORD_64]);;

let aligned_bytes_loaded_append_left = prove
 (`aligned_bytes_loaded s pc (APPEND l1 l2) ==> aligned_bytes_loaded s pc l1`,
  REWRITE_TAC [aligned_bytes_loaded; bytes_loaded_append] THEN
  METIS_TAC []);;

let aligned_bytes_loaded_append = prove
 (`4 divides LENGTH l1 ==>
   (aligned_bytes_loaded s pc (APPEND l1 l2) <=>
    aligned_bytes_loaded s pc l1 /\
    aligned_bytes_loaded s (word_add pc (word (LENGTH l1))) l2)`,
  SPEC1_TAC `pc:int64` THEN REWRITE_TAC [FORALL_WORD; GSYM WORD_ADD;
    aligned_bytes_loaded_word; bytes_loaded_append] THEN
  METIS_TAC [DIVIDES_ADD]);;

let aligned_bytes_loaded_append_alt = prove
 (`aligned_bytes_loaded s pc (APPEND l1 l2) <=>
   aligned_bytes_loaded s pc l1 /\
   bytes_loaded s (word_add pc (word (LENGTH l1))) l2`,
  REWRITE_TAC[aligned_bytes_loaded; bytes_loaded_append; CONJ_ASSOC]);;

let aligned_bytes_loaded_unique =
  METIS [aligned_bytes_loaded; bytes_loaded_unique]
  `!s pc l1 l2.
   aligned_bytes_loaded s pc l1 ==> aligned_bytes_loaded s pc l2 ==>
   LENGTH l1 = LENGTH l2 ==> l1 = l2`;;

let aligned_bytes_loaded_update =
  METIS [aligned_bytes_loaded; bytes_loaded_update]
 `!l n. LENGTH l = n ==> !s pc. aligned_bytes_loaded s pc l ==>
  !s'. read(memory :> bytelist(pc,n)) s' = read(memory :> bytelist(pc,n)) s ==>
    aligned_bytes_loaded s' pc l`;;

let aligned_bytes_loaded_of_append3 = prove
 (`!l l1 l2 l3. l = APPEND l1 (APPEND l2 l3) ==> 4 divides LENGTH l1 ==>
   !s pc. aligned_bytes_loaded s (word pc) l ==>
          aligned_bytes_loaded s (word (pc + LENGTH l1)) l2`,
  REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [WORD_ADD] THEN
  METIS_TAC [aligned_bytes_loaded_append; aligned_bytes_loaded_append_left]);;

let ALIGNED_BYTES_LOADED_SUB_LIST = prove
 (`!s pc l m n.
        aligned_bytes_loaded s pc l /\ 4 divides m
        ==> aligned_bytes_loaded s (word_add pc (word m)) (SUB_LIST(m,n) l)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[aligned_bytes_loaded] THEN
  SIMP_TAC[BYTES_LOADED_SUB_LIST; VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[GSYM (NUM_EXP_CONV `2 EXP 2`)] THEN
  REWRITE_TAC[DIVIDES_MOD; MOD_MOD_EXP_MIN] THEN
  ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[] THEN CONV_TAC NUM_REDUCE_CONV);;

let ALIGNED_BYTES_LOADED_SUB_LIST = prove
 (`(!s pc l m n.
        aligned_bytes_loaded s pc l /\ 4 divides m
        ==> aligned_bytes_loaded s (word_add pc (word m)) (SUB_LIST(m,n) l)) /\
   (!s pc l n.
        aligned_bytes_loaded s pc l
        ==> aligned_bytes_loaded s pc (SUB_LIST(0,n) l))`,
  REWRITE_TAC[ALIGNED_BYTES_LOADED_SUB_LIST] THEN
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC(RATOR_CONV o RAND_CONV)
    [GSYM (fst (CONJ_PAIR WORD_ADD_0))] THEN
  IMP_REWRITE_TAC[WORD_ADD;ALIGNED_BYTES_LOADED_SUB_LIST] THEN
  CONV_TAC NUM_DIVIDES_CONV);;

let ALIGNED_BYTES_LOADED_TRIM_LIST = prove
 (`!s pc l m n.
        aligned_bytes_loaded s pc l /\ 4 divides m
        ==> aligned_bytes_loaded s (word_add pc (word m)) (TRIM_LIST(m,n) l)`,
  REWRITE_TAC[ALIGNED_BYTES_LOADED_SUB_LIST; TRIM_LIST]);;

(* ------------------------------------------------------------------------- *)
(* Tweak for aligned_bytes_loaded s (word pc) (APPEND program data)          *)
(* ------------------------------------------------------------------------- *)

let ALIGNED_BYTES_LOADED_APPEND_CLAUSE = prove
 (`aligned_bytes_loaded s (word pc) (APPEND prog data) /\
   read PC s = pcin /\
   rest <=>
   aligned_bytes_loaded s (word pc) prog /\
   read PC s = pcin /\
   bytes_loaded s (word(pc + LENGTH prog)) data /\
   rest`,
  REWRITE_TAC[aligned_bytes_loaded_append_alt; GSYM WORD_ADD; CONJ_ACI]);;

(* ------------------------------------------------------------------------- *)
(* Individual flags. The numbering matches "nzcv" immediates, but does not   *)
(* otherwise matter for the current model since they are used individually.  *)
(* ------------------------------------------------------------------------- *)

let NF = define `NF = flags :> bitelement 3`;;

let ZF = define `ZF = flags :> bitelement 2`;;

let CF = define `CF = flags :> bitelement 1`;;

let VF = define `VF = flags :> bitelement 0`;;

add_component_alias_thms [NF; ZF; CF; VF];;

(* ------------------------------------------------------------------------- *)
(* The zero register: zero as source, ignored as destination.                *)
(* This isn't literally a state component but is naturally considered one.   *)
(* ------------------------------------------------------------------------- *)

let XZR = define `XZR:(armstate,int64)component = rvalue(word 0)`;;

let WZR = define `WZR = XZR :> bottom_32`;;

add_component_alias_thms [XZR; WZR];;

(*** We also define a generic ZR to aid in alias definitions below ***)

let ZR = define `ZR:(armstate,N word)component = rvalue(word 0)`;;

(* ------------------------------------------------------------------------- *)
(* Main integer registers, defaulting to zero register for >= 31.            *)
(* ------------------------------------------------------------------------- *)

let XREG = define
  `XREG n = if n >= 31 then XZR else registers :> element(word n)`;;

(*** To precompute the case split add the whole slew individually ***)

add_component_alias_thms
 (map (fun n -> let tm = mk_comb(`XREG`,mk_small_numeral n) in
                (GEN_REWRITE_CONV I [XREG] THENC NUM_REDUCE_CONV) tm)
      (0--31));;

let  X0 = define ` X0 = XREG  0`;;
let  X1 = define ` X1 = XREG  1`;;
let  X2 = define ` X2 = XREG  2`;;
let  X3 = define ` X3 = XREG  3`;;
let  X4 = define ` X4 = XREG  4`;;
let  X5 = define ` X5 = XREG  5`;;
let  X6 = define ` X6 = XREG  6`;;
let  X7 = define ` X7 = XREG  7`;;
let  X8 = define ` X8 = XREG  8`;;
let  X9 = define ` X9 = XREG  9`;;
let X10 = define `X10 = XREG 10`;;
let X11 = define `X11 = XREG 11`;;
let X12 = define `X12 = XREG 12`;;
let X13 = define `X13 = XREG 13`;;
let X14 = define `X14 = XREG 14`;;
let X15 = define `X15 = XREG 15`;;
let X16 = define `X16 = XREG 16`;;
let X17 = define `X17 = XREG 17`;;
let X18 = define `X18 = XREG 18`;;
let X19 = define `X19 = XREG 19`;;
let X20 = define `X20 = XREG 20`;;
let X21 = define `X21 = XREG 21`;;
let X22 = define `X22 = XREG 22`;;
let X23 = define `X23 = XREG 23`;;
let X24 = define `X24 = XREG 24`;;
let X25 = define `X25 = XREG 25`;;
let X26 = define `X26 = XREG 26`;;
let X27 = define `X27 = XREG 27`;;
let X28 = define `X28 = XREG 28`;;
let X29 = define `X29 = XREG 29`;;
let X30 = define `X30 = XREG 30`;;

add_component_alias_thms
 [ X0;  X1;  X2;  X3;  X4;  X5;  X6;  X7;
   X8;  X9; X10; X11; X12; X13; X14; X15;
  X16; X17; X18; X19; X20; X21; X22; X23;
  X24; X25; X26; X27; X28; X29; X30];;

(* ------------------------------------------------------------------------- *)
(* Stack pointer.                                                            *)
(* ------------------------------------------------------------------------- *)

let SP = define `SP = registers :> element (word 31)`;;

add_component_alias_thms [SP];;

(* ------------------------------------------------------------------------- *)
(* 32-bit versions of the main integer registers. NB! As lvalues all these   *)
(* zero the top 32 bits, which matches the usual 64-bit mode behavior.       *)
(* To get pure alternatives use "bottom_32" instead of "zerotop_32".         *)
(* ------------------------------------------------------------------------- *)

let WREG = define `WREG n = XREG n :> zerotop_32`;;

let WSP = define `WSP = SP :> zerotop_32`;;

add_component_alias_thms [WREG; WSP];;

let  W0 = define ` W0 = WREG  0`;;
let  W1 = define ` W1 = WREG  1`;;
let  W2 = define ` W2 = WREG  2`;;
let  W3 = define ` W3 = WREG  3`;;
let  W4 = define ` W4 = WREG  4`;;
let  W5 = define ` W5 = WREG  5`;;
let  W6 = define ` W6 = WREG  6`;;
let  W7 = define ` W7 = WREG  7`;;
let  W8 = define ` W8 = WREG  8`;;
let  W9 = define ` W9 = WREG  9`;;
let W10 = define `W10 = WREG 10`;;
let W11 = define `W11 = WREG 11`;;
let W12 = define `W12 = WREG 12`;;
let W13 = define `W13 = WREG 13`;;
let W14 = define `W14 = WREG 14`;;
let W15 = define `W15 = WREG 15`;;
let W16 = define `W16 = WREG 16`;;
let W17 = define `W17 = WREG 17`;;
let W18 = define `W18 = WREG 18`;;
let W19 = define `W19 = WREG 19`;;
let W20 = define `W20 = WREG 20`;;
let W21 = define `W21 = WREG 21`;;
let W22 = define `W22 = WREG 22`;;
let W23 = define `W23 = WREG 23`;;
let W24 = define `W24 = WREG 24`;;
let W25 = define `W25 = WREG 25`;;
let W26 = define `W26 = WREG 26`;;
let W27 = define `W27 = WREG 27`;;
let W28 = define `W28 = WREG 28`;;
let W29 = define `W29 = WREG 29`;;
let W30 = define `W30 = WREG 30`;;

add_component_alias_thms
 [ W0;  W1;  W2;  W3;  W4;  W5;  W6;  W7;
   W8;  W9; W10; W11; W12; W13; W14; W15;
  W16; W17; W18; W19; W20; W21; W22; W23;
  W24; W25; W26; W27; W28; W29; W30];;

(* ------------------------------------------------------------------------- *)
(* Shifted register operands. The ROR one is only encodable for some logical *)
(* operations, not arithmetic ones, and the shift itself is an immediate     *)
(* that has to be < the word size in the 32-bit operand case. All that is    *)
(* deferred to the decoder. The lvalue form is likewise not actually meant   *)
(* to be used, and for simplicity is the same as the core register.          *)
(* ------------------------------------------------------------------------- *)

let regshift_INDUCT,regshift_RECURSION = define_type
  "regshift = LSL | LSR | ASR | ROR";;

let regshift_operation = define
 `regshift_operation LSL = word_shl /\
  regshift_operation LSR = word_ushr /\
  regshift_operation ASR = word_ishr /\
  regshift_operation ROR = word_ror`;;

let Shiftedreg_DEF = define
 `Shiftedreg reg sty sam =
        component((\s. regshift_operation sty (read reg s) sam),write reg)`;;

let SHIFTEDREG_TRIVIAL = prove
 (`!reg:(armstate,N word)component. Shiftedreg reg LSL 0 = reg`,
  REWRITE_TAC[COMPONENT_EQ; read; write; Shiftedreg_DEF;
              regshift_operation; WORD_SHL_ZERO; ETA_AX]);;

(* ------------------------------------------------------------------------- *)
(* Extended register operands. Again the lvalue form is arbitrary.           *)
(* ------------------------------------------------------------------------- *)

let extendtype_INDUCT,extendtype_RECURSION = define_type
  "extendtype = UXTB | UXTH | UXTW | UXTX | SXTB | SXTH | SXTW | SXTX";;

(*** For flexibility, this takes arbitrary input and output word sizes ***)

let extendreg_operation = define
 `extendreg_operation UXTB x = word_zx (word_zx x:byte) /\
  extendreg_operation UXTH x = word_zx (word_zx x:int16) /\
  extendreg_operation UXTW x = word_zx (word_zx x:int32) /\
  extendreg_operation UXTX x = word_zx (word_zx x:int64) /\
  extendreg_operation SXTB x = word_sx (word_zx x:byte) /\
  extendreg_operation SXTH x = word_sx (word_zx x:int16) /\
  extendreg_operation SXTW x = word_sx (word_zx x:int32) /\
  extendreg_operation SXTX x = word_sx (word_zx x:int64)`;;

let Extendedreg_DEF = define
 `Extendedreg reg ety =
        component((\s. extendreg_operation ety (read reg s)),ARB)`;;

(* ------------------------------------------------------------------------- *)
(* The main SIMD register parts                                              *)
(* ------------------------------------------------------------------------- *)

let QREG = define `QREG n = simdregisters :> element(word n)`;;

let DREG = define `DREG n = QREG n :> zerotop_64`;;

let SREG = define `SREG n = DREG n :> zerotop_32`;;

let HREG = define `HREG n = SREG n :> zerotop_16`;;

let BREG = define `BREG n = HREG n :> zerotop_8`;;

add_component_alias_thms [QREG; DREG; SREG; HREG; BREG];;

let  Q0 = define ` Q0 = QREG  0`;;
let  Q1 = define ` Q1 = QREG  1`;;
let  Q2 = define ` Q2 = QREG  2`;;
let  Q3 = define ` Q3 = QREG  3`;;
let  Q4 = define ` Q4 = QREG  4`;;
let  Q5 = define ` Q5 = QREG  5`;;
let  Q6 = define ` Q6 = QREG  6`;;
let  Q7 = define ` Q7 = QREG  7`;;
let  Q8 = define ` Q8 = QREG  8`;;
let  Q9 = define ` Q9 = QREG  9`;;
let Q10 = define `Q10 = QREG 10`;;
let Q11 = define `Q11 = QREG 11`;;
let Q12 = define `Q12 = QREG 12`;;
let Q13 = define `Q13 = QREG 13`;;
let Q14 = define `Q14 = QREG 14`;;
let Q15 = define `Q15 = QREG 15`;;
let Q16 = define `Q16 = QREG 16`;;
let Q17 = define `Q17 = QREG 17`;;
let Q18 = define `Q18 = QREG 18`;;
let Q19 = define `Q19 = QREG 19`;;
let Q20 = define `Q20 = QREG 20`;;
let Q21 = define `Q21 = QREG 21`;;
let Q22 = define `Q22 = QREG 22`;;
let Q23 = define `Q23 = QREG 23`;;
let Q24 = define `Q24 = QREG 24`;;
let Q25 = define `Q25 = QREG 25`;;
let Q26 = define `Q26 = QREG 26`;;
let Q27 = define `Q27 = QREG 27`;;
let Q28 = define `Q28 = QREG 28`;;
let Q29 = define `Q29 = QREG 29`;;
let Q30 = define `Q30 = QREG 30`;;
let Q31 = define `Q31 = QREG 31`;;

add_component_alias_thms
 [ Q0;  Q1;  Q2;  Q3;  Q4;  Q5;  Q6;  Q7;
   Q8;  Q9; Q10; Q11; Q12; Q13; Q14; Q15;
  Q16; Q17; Q18; Q19; Q20; Q21; Q22; Q23;
  Q24; Q25; Q26; Q27; Q28; Q29; Q30; Q31];;

let  D0 = define ` D0 = DREG  0`;;
let  D1 = define ` D1 = DREG  1`;;
let  D2 = define ` D2 = DREG  2`;;
let  D3 = define ` D3 = DREG  3`;;
let  D4 = define ` D4 = DREG  4`;;
let  D5 = define ` D5 = DREG  5`;;
let  D6 = define ` D6 = DREG  6`;;
let  D7 = define ` D7 = DREG  7`;;
let  D8 = define ` D8 = DREG  8`;;
let  D9 = define ` D9 = DREG  9`;;
let D10 = define `D10 = DREG 10`;;
let D11 = define `D11 = DREG 11`;;
let D12 = define `D12 = DREG 12`;;
let D13 = define `D13 = DREG 13`;;
let D14 = define `D14 = DREG 14`;;
let D15 = define `D15 = DREG 15`;;
let D16 = define `D16 = DREG 16`;;
let D17 = define `D17 = DREG 17`;;
let D18 = define `D18 = DREG 18`;;
let D19 = define `D19 = DREG 19`;;
let D20 = define `D20 = DREG 20`;;
let D21 = define `D21 = DREG 21`;;
let D22 = define `D22 = DREG 22`;;
let D23 = define `D23 = DREG 23`;;
let D24 = define `D24 = DREG 24`;;
let D25 = define `D25 = DREG 25`;;
let D26 = define `D26 = DREG 26`;;
let D27 = define `D27 = DREG 27`;;
let D28 = define `D28 = DREG 28`;;
let D29 = define `D29 = DREG 29`;;
let D30 = define `D30 = DREG 30`;;
let D31 = define `D31 = DREG 31`;;

add_component_alias_thms
 [ D0;  D1;  D2;  D3;  D4;  D5;  D6;  D7;
   D8;  D9; D10; D11; D12; D13; D14; D15;
  D16; D17; D18; D19; D20; D21; D22; D23;
  D24; D25; D26; D27; D28; D29; D30; D31];;

(* ------------------------------------------------------------------------- *)
(* Additional subcomponents for individual lanes of a SIMD register.         *)
(* These effectively duplicate the chosen lane so that it can be treated as  *)
(* another SIMD value when used in elementwise contexts. It is only intended *)
(* for reading, hence the dummy identity function in the other direction.    *)
(* ------------------------------------------------------------------------- *)

let LANE_B = define
 `LANE_B i =
  through((\w:int128. word_duplicate (word_subword w (8*i,8):byte)),I)`;;

let LANE_H = define
 `LANE_H i =
  through((\w:int128. word_duplicate (word_subword w (16*i,16):int16)),I)`;;

let LANE_S = define
 `LANE_S i =
  through((\w:int128. word_duplicate (word_subword w (32*i,32):int32)),I)`;;

let LANE_D = define
 `LANE_D i =
  through((\w:int128. word_duplicate (word_subword w (64*i,64):int64)),I)`;;

(* ------------------------------------------------------------------------- *)
(* The zero registers are all basically what we expect                       *)
(* ------------------------------------------------------------------------- *)

let ARM_ZERO_REGISTER = prove
 (`ZR = rvalue(word 0) /\
   XZR = rvalue(word 0) /\
   XREG 31 = rvalue(word 0) /\
   WZR = rvalue(word 0) /\
   WREG 31 = rvalue(word 0)`,
  REWRITE_TAC[XZR; WZR; XREG; WREG; GE; LE_REFL; COMPONENT_COMPOSE_RVALUE] THEN
  REWRITE_TAC[ZR] THEN CONJ_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; bottom_32; bottomhalf; READ_SUBWORD_0] THEN
  REWRITE_TAC[zerotop_32; read; through; WORD_ZX_0]);;

let XZR_ZR = prove
 (`XZR = ZR`,
  REWRITE_TAC[ARM_ZERO_REGISTER; ZR]);;

let WZR_ZR = prove
 (`WZR = ZR`,
  REWRITE_TAC[ARM_ZERO_REGISTER; ZR]);;

(*** We use ZR in some aliases but we only want these two cases ***)

add_component_alias_thms [GSYM XZR_ZR; GSYM WZR_ZR];;

(* ------------------------------------------------------------------------- *)
(* Condition codes via 4-bit encoding (ARM reference manual C.1.2.4)         *)
(* ------------------------------------------------------------------------- *)

let condition_INDUCT,condition_RECURSION = define_type
 "condition = Condition (4 word)";;

let Condition_EQ = define `Condition_EQ = Condition(word 0b0000)`;;
let Condition_NE = define `Condition_NE = Condition(word 0b0001)`;;
let Condition_CS = define `Condition_CS = Condition(word 0b0010)`;;
let Condition_HS = define `Condition_HS = Condition(word 0b0010)`;;
let Condition_CC = define `Condition_CC = Condition(word 0b0011)`;;
let Condition_LO = define `Condition_LO = Condition(word 0b0011)`;;
let Condition_MI = define `Condition_MI = Condition(word 0b0100)`;;
let Condition_PL = define `Condition_PL = Condition(word 0b0101)`;;
let Condition_VS = define `Condition_VS = Condition(word 0b0110)`;;
let Condition_VC = define `Condition_VC = Condition(word 0b0111)`;;
let Condition_HI = define `Condition_HI = Condition(word 0b1000)`;;
let Condition_LS = define `Condition_LS = Condition(word 0b1001)`;;
let Condition_GE = define `Condition_GE = Condition(word 0b1010)`;;
let Condition_LT = define `Condition_LT = Condition(word 0b1011)`;;
let Condition_GT = define `Condition_GT = Condition(word 0b1100)`;;
let Condition_LE = define `Condition_LE = Condition(word 0b1101)`;;
let Condition_AL = define `Condition_AL = Condition(word 0b1110)`;;
let Condition_NV = define `Condition_NV = Condition(word 0b1111)`;;

let CONDITION_CLAUSES =
  [Condition_EQ; Condition_NE; Condition_CS; Condition_HS;
   Condition_CC; Condition_LO; Condition_MI; Condition_PL;
   Condition_VS; Condition_VC; Condition_HI; Condition_LS;
   Condition_GE; Condition_LT; Condition_GT; Condition_LE;
   Condition_AL; Condition_NV];;

(* ------------------------------------------------------------------------- *)
(* Semantics of conditions. Note that NV = AL! (see C.1.2.4).                *)
(* We can't yet define functions by pattern-matching over words, so we need  *)
(* to justify the definition we want via an uglier unpacking.                *)
(* ------------------------------------------------------------------------- *)

let condition_semantics =
  let th = prove
   (`?f. (!s. f Condition_EQ s <=> read ZF s) /\
         (!s. f Condition_NE s <=> ~read ZF s) /\
         (!s. f Condition_CS s <=> read CF s) /\
         (!s. f Condition_HS s <=> read CF s) /\
         (!s. f Condition_CC s <=> ~read CF s) /\
         (!s. f Condition_LO s <=> ~read CF s) /\
         (!s. f Condition_MI s <=> read NF s) /\
         (!s. f Condition_PL s <=> ~read NF s) /\
         (!s. f Condition_VS s <=> read VF s) /\
         (!s. f Condition_VC s <=> ~read VF s) /\
         (!s. f Condition_HI s <=> read CF s /\ ~read ZF s) /\
         (!s. f Condition_LS s <=> ~(read CF s /\ ~read ZF s)) /\
         (!s. f Condition_GE s <=> (read NF s <=> read VF s)) /\
         (!s. f Condition_LT s <=> ~(read NF s <=> read VF s)) /\
         (!s. f Condition_GT s <=> ~read ZF s /\ (read NF s <=> read VF s)) /\
         (!s. f Condition_LE s <=>
                ~(~read ZF s /\ (read NF s <=> read VF s))) /\
         (!s. f Condition_AL s <=> T) /\
         (!s. f Condition_NV s <=> T)`,
    ONCE_REWRITE_TAC[GSYM FUN_EQ_THM] THEN REWRITE_TAC[ETA_AX] THEN
    W(MP_TAC o DISCH_ALL o instantiate_casewise_recursion o snd) THEN
    REWRITE_TAC[IMP_IMP] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC CONDITION_CLAUSES THEN
    REWRITE_TAC[injectivity "condition"; WORD_EQ; CONG] THEN
    CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[SUPERADMISSIBLE_CONST] THEN
    EXISTS_TAC `\(x:condition) (y:condition). F` THEN
    REWRITE_TAC[WF_FALSE]) in
  new_specification ["condition_semantics"] th;;

(* ------------------------------------------------------------------------- *)
(* Inversion of conditions (used in aliases like CSET and CSETM)             *)
(* ------------------------------------------------------------------------- *)

let invert_condition =
 let th = prove
   (`?f. f Condition_EQ = Condition_NE /\
         f Condition_NE = Condition_EQ /\
         f Condition_CS = Condition_CC /\
         f Condition_HS = Condition_LO /\
         f Condition_CC = Condition_CS /\
         f Condition_LO = Condition_HS /\
         f Condition_MI = Condition_PL /\
         f Condition_PL = Condition_MI /\
         f Condition_VS = Condition_VC /\
         f Condition_VC = Condition_VS /\
         f Condition_HI = Condition_LS /\
         f Condition_LS = Condition_HI /\
         f Condition_GE = Condition_LT /\
         f Condition_LT = Condition_GE /\
         f Condition_GT = Condition_LE /\
         f Condition_LE = Condition_GT /\
         f Condition_AL = Condition_NV /\
         f Condition_NV = Condition_AL`,
    W(MP_TAC o DISCH_ALL o instantiate_casewise_recursion o snd) THEN
    REWRITE_TAC[IMP_IMP] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC CONDITION_CLAUSES THEN
    REWRITE_TAC[injectivity "condition"; WORD_EQ; CONG] THEN
    CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[SUPERADMISSIBLE_CONST] THEN
    EXISTS_TAC `\(x:condition) (y:condition). F` THEN
    REWRITE_TAC[WF_FALSE]) in
  new_specification ["invert_condition"] th;;

let INVERT_CONDITION = prove
 (`!w. invert_condition(Condition w) = Condition(word_xor w (word 1))`,
  ONCE_REWRITE_TAC[FORALL_VAL_GEN] THEN
  REWRITE_TAC[DIMINDEX_4] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  REWRITE_TAC[REWRITE_RULE CONDITION_CLAUSES invert_condition]);;

let INVERT_CONDITION_TWICE = prove
 (`!cc. invert_condition(invert_condition cc) = cc`,
  MATCH_MP_TAC condition_INDUCT THEN REWRITE_TAC[INVERT_CONDITION;
    WORD_BITWISE_RULE `word_xor (word_xor a b) b = a`]);;

(*** Because of the special treatment of NV this is a bit ugly ***)
(*** But that is made quite explicit in the ARM documentation  ***)
(*** See "ConditionHolds" pseudocode with just this case split ***)
(*** There might be an argument for not defining Condition_NV  ***)

let CONDITION_SEMANTICS_INVERT_CONDITION = prove
 (`!cc s. condition_semantics (invert_condition cc) s =
                if cc = Condition_AL \/ cc = Condition_NV
                then condition_semantics cc s
                else ~(condition_semantics cc s)`,
  GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN GEN_TAC THEN
  MATCH_MP_TAC condition_INDUCT THEN
  ONCE_REWRITE_TAC[FORALL_VAL_GEN] THEN
  REWRITE_TAC[DIMINDEX_4] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  REWRITE_TAC[REWRITE_RULE CONDITION_CLAUSES invert_condition] THEN
  REWRITE_TAC[REWRITE_RULE CONDITION_CLAUSES condition_semantics] THEN
  REWRITE_TAC(injectivity "condition" :: CONDITION_CLAUSES) THEN
  CONV_TAC WORD_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* Addressing modes and offsets for loads and stores (LDP, LDR, STP, STR)    *)
(* ------------------------------------------------------------------------- *)

(*** We don't support quite all the addressing modes in C1.3.3.
 *** In particular we ignore extended 32-bit registers, which we'll never use
 ***
 *** We have a numeric parameter in the Shiftreg_Offset but it's only
 *** allowed to be log_2(transfer_size), i.e. usually 3. We also just treat all
 *** immediates as 64-bit without worrying about the actual limits.
 ***)

let offset_INDUCT,offset_RECURSION = define_type
 "offset =
    Register_Offset ((armstate,int64)component)      // [base, reg]
  | Shiftreg_Offset ((armstate,int64)component) num  // [base, reg, LSL k]
  | Postreg_Offset ((armstate, int64)component)      // [base], [reg]
  | Immediate_Offset (64 word)                       // [base, #n] or [base]
  | Preimmediate_Offset (64 word)                    // [base, #n]!
  | Postimmediate_Offset (64 word)                   // [base], #n
 ";;

let no_offset = define `No_Offset = Immediate_Offset (word 0)`;;

(*** This defines the actual address offset used, so 0 for post-index ***)

let offset_address = define
 `offset_address (Register_Offset r) s = read r s /\
  offset_address (Shiftreg_Offset r k) s = word_shl (read r s) k /\
  offset_address (Postreg_Offset r) s = word 0 /\
  offset_address (Immediate_Offset w) s = w /\
  offset_address (Preimmediate_Offset w) s = w /\
  offset_address (Postimmediate_Offset w) s = word 0`;;

(*** This one defines the offset to add to the register ***)

let offset_writeback = define
 `offset_writeback (Register_Offset r) s = word 0 /\
  offset_writeback (Shiftreg_Offset r k) s = word 0 /\
  offset_writeback (Postreg_Offset r) s = read r s /\
  offset_writeback (Immediate_Offset w) s = word 0 /\
  offset_writeback (Preimmediate_Offset w) s = w /\
  offset_writeback (Postimmediate_Offset w) s = w`;;

let offset_writesback = define
 `(offset_writesback (Register_Offset r) <=> F) /\
  (offset_writesback (Shiftreg_Offset r k) <=> F) /\
  (offset_writesback (Postreg_Offset r) <=> T) /\
  (offset_writesback (Immediate_Offset w) <=> F) /\
  (offset_writesback (Preimmediate_Offset w) <=> T) /\
  (offset_writesback (Postimmediate_Offset w) <=> T)`;;

(* ------------------------------------------------------------------------- *)
(* Shorthand for the set of all flags for modification lists.                *)
(* ------------------------------------------------------------------------- *)

let SOME_FLAGS = new_definition
 `SOME_FLAGS = [NF; ZF; CF; VF]`;;

(* ------------------------------------------------------------------------- *)
(* ABI things: Procedure Call Standard for the Arm Architecture,             *)
(*   https://github.com/ARM-software/abi-aa/releases                         *)
(* "A subroutine invocation must preserve r19-r29 and SP. In all versions of *)
(* the procedure call standard r16, r17, r29 and r30 have special roles".    *)
(* There's also some stuff implying one should avoid r18. I'm conservative   *)
(* in this and just  treat all >= 18 as to be preserved and throw in SP too  *)
(* even though it's not "really" a general-purpose register.                 *)
(* ------------------------------------------------------------------------- *)

let C_ARGUMENTS = define
 `(C_ARGUMENTS [a0;a1;a2;a3;a4;a5;a6;a7] s <=>
        read X0 s = a0 /\ read X1 s = a1 /\
        read X2 s = a2 /\ read X3 s = a3 /\
        read X4 s = a4 /\ read X5 s = a5 /\
        read X6 s = a6 /\ read X7 s = a7) /\
  (C_ARGUMENTS [a0;a1;a2;a3;a4;a5;a6] s <=>
        read X0 s = a0 /\ read X1 s = a1 /\
        read X2 s = a2 /\ read X3 s = a3 /\
        read X4 s = a4 /\ read X5 s = a5 /\
        read X6 s = a6) /\
  (C_ARGUMENTS [a0;a1;a2;a3;a4;a5] s <=>
        read X0 s = a0 /\ read X1 s = a1 /\
        read X2 s = a2 /\ read X3 s = a3 /\
        read X4 s = a4 /\ read X5 s = a5) /\
  (C_ARGUMENTS [a0;a1;a2;a3;a4] s <=>
        read X0 s = a0 /\ read X1 s = a1 /\
        read X2 s = a2 /\ read X3 s = a3 /\
        read X4 s = a4) /\
  (C_ARGUMENTS [a0;a1;a2;a3] s <=>
        read X0 s = a0 /\ read X1 s = a1 /\
        read X2 s = a2 /\ read X3 s = a3) /\
  (C_ARGUMENTS [a0;a1;a2] s <=>
        read X0 s = a0 /\ read X1 s = a1 /\
        read X2 s = a2) /\
  (C_ARGUMENTS [a0;a1] s <=>
        read X0 s = a0 /\ read X1 s = a1) /\
  (C_ARGUMENTS [a0] s <=>
        read X0 s = a0) /\
  (C_ARGUMENTS [] s <=>
        T)`;;

let C_RETURN = define
 `C_RETURN = read X0`;;

let PRESERVED_GPRS = define
 `PRESERVED_GPRS =
    [X18; X19; X20; X21; X22; X23; X24;
     X25; X26; X27; X28; X29; X30; SP]`;;

let MODIFIABLE_GPRS = define
 `MODIFIABLE_GPRS =
    [ X0;  X1;  X2;  X3;  X4;  X5;  X6;  X7;  X8;
      X9; X10; X11; X12; X13; X14; X15; X16; X17]`;;

(* SIMD registers: "Registers v8-v15 must be preserved by a callee across
    subroutine calls; the remaining registers (v0-v7, v16-v31) do not need to
    be preserved (or should be preserved by the caller). Additionally, only
    the bottom 64 bits of each value stored in v8-v15 need to be preserved"
 *)

let MODIFIABLE_SIMD_REGS = define
 `MODIFIABLE_SIMD_REGS =
    [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q16; Q17; Q18; Q19; Q20; Q21;
      Q22; Q23; Q24; Q25; Q26; Q27; Q28; Q29; Q30; Q31]`;;

let MODIFIABLE_UPPER_SIMD_REGS = define
 `MODIFIABLE_UPPER_SIMD_REGS =
   [Q8 :> tophalf; Q9 :> tophalf; Q10 :> tophalf; Q11 :> tophalf;
    Q12 :> tophalf; Q13 :> tophalf; Q14 :> tophalf; Q15 :> tophalf]`;;

let MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI = REWRITE_RULE
    [SOME_FLAGS; MODIFIABLE_GPRS; MODIFIABLE_SIMD_REGS;
     MODIFIABLE_UPPER_SIMD_REGS]
 (new_definition `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI =
    MAYCHANGE [PC] ,, MAYCHANGE MODIFIABLE_GPRS ,,
    MAYCHANGE MODIFIABLE_SIMD_REGS ,,
    MAYCHANGE MODIFIABLE_UPPER_SIMD_REGS ,, MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]`);;

(* ------------------------------------------------------------------------- *)
(* Mask-creating version of a comparison-type operation.                     *)
(* ------------------------------------------------------------------------- *)

let masking = new_definition
 `(masking p:N word->N word->N word) x y = word_neg(word(bitval(p x y)))`;;

(* ------------------------------------------------------------------------- *)
(* General register-register instructions.                                   *)
(* ------------------------------------------------------------------------- *)

let arm_ADC = define
 `arm_ADC Rd Rm Rn =
    \s. let m = read Rm s
        and n = read Rn s
        and c = bitval(read CF s) in
        let d:N word = word_add (word_add m n) (word c) in
        (Rd := d) s`;;

let arm_ADCS = define
 `arm_ADCS Rd Rm Rn =
    \s. let m = read Rm s
        and n = read Rn s
        and c = bitval(read CF s) in
        let d:N word = word_add (word_add m n) (word c) in
        (Rd := d ,,
         NF := (ival d < &0) ,,
         ZF := (val d = 0) ,,
         CF := ~(val m + val n + c = val d) ,,
         VF := ~(ival m + ival n + &c = ival d)) s`;;

let arm_ADD = define
 `arm_ADD Rd Rm Rn =
    \s. let m = read Rm s
        and n = read Rn s in
        let d:N word = word_add m n in
        (Rd := d) s`;;

let arm_ADD_VEC = define
 `arm_ADD_VEC Rd Rn Rm esize datasize =
    \s. let n = read Rn s in
        let m = read Rm s in
        if datasize = 128 then
          let d:(128)word =
            if esize = 64 then simd2 word_add n m
            else if esize = 32 then simd4 word_add n m
            else if esize = 16 then simd8 word_add n m
            else simd16 word_add n m in
          (Rd := d) s
        else
          let n:(64)word = word_subword n (0,64) in
          let m:(64)word = word_subword m (0,64) in
          let d:(64)word =
            if esize = 32 then simd2 word_add n m
            else if esize = 16 then simd4 word_add n m
            else simd8 word_add n m in
          (Rd := word_zx d:(128)word) s`;;

let arm_ADDS = define
 `arm_ADDS Rd Rm Rn =
    \s. let m = read Rm s
        and n = read Rn s in
        let d:N word = word_add m n in
        (Rd := d ,,
         NF := (ival d < &0) ,,
         ZF := (val d = 0) ,,
         CF := ~(val m + val n = val d) ,,
         VF := ~(ival m + ival n = ival d)) s`;;

let arm_ADR = define
 `arm_ADR Rd (off:21 word) =
    \s. let d = word_add (word_sub (read PC s) (word 4)) (word_sx off) in
        (Rd := d) s`;;

let arm_ADRP = define
 `arm_ADRP Rd (off:21 word) =
    \s. let pc0 = word_sub (read PC s) (word 4) in
        // get its 4KB(=2^12) page boundary
        let pc_page = word_and pc0 (word 0xFFFFFFFFFFFFF000) in
        let off0 = word_sx (word_join off (word 0:(12)word):(33)word) in
        let d = word_add pc_page off0 in
        (Rd := d) s`;;

let arm_AND = define
 `arm_AND Rd Rm Rn =
    \s. let m = read Rm s
        and n = read Rn s in
        let d:N word = word_and m n in
        (Rd := d) s`;;

let arm_AND_VEC = define
 `arm_AND_VEC Rd Rn Rm datasize =
    \s. let m = read Rm s
        and n = read Rn s in
        if datasize = 128 then
          let d:(128)word = word_and m n in
          (Rd := d) s
        else
          let d:(64)word = word_subword (word_and m n) (0,64) in
          (Rd := word_zx d:(128)word) s`;;

let arm_ANDS = define
 `arm_ANDS Rd Rm Rn =
    \s. let m = read Rm s
        and n = read Rn s in
        let d:N word = word_and m n in
        (Rd := d ,,
         NF := (ival d < &0) ,,
         ZF := (val d = 0) ,,
         CF := F ,,
         VF := F) s`;;

let arm_ASRV = define
 `arm_ASRV Rd Rm Rn =
    \s. let m = read Rm s
        and n = read Rn s in
        let d:N word = word_jshr m n in
        (Rd := d) s`;;

(*** For unconditional branch the offset is encoded as a 26-bit word   ***)
(*** This is turned into a 28-bit word when multiplied by 4, then sx   ***)
(*** Note that this is a longer immediate than in conditional branches ***)

let arm_B = define
 `arm_B (off:28 word) =
    \s. let pc = word_sub (read PC s) (word 4) in
        let pc_next = word_add pc (word_sx off) in
        (PC := pc_next ,,
         events := CONS (EventJump (pc,pc_next)) (read events s)) s`;;

let arm_BFM = define
 `arm_BFM Rd Rn immr imms =
    \s:armstate.
      let x:N word = read Rn s
      and d:N word = read Rd s in
      let y:N word =
        if imms >= immr then
          word_insert d (0,(imms-immr)+1) (word_ushr x immr)
        else
          word_insert d (dimindex(:N) - immr,imms+1) x in
      (Rd := y) s`;;

let arm_BIC = define
 `arm_BIC Rd Rm Rn =
    \s. let m = read Rm s
        and n = read Rn s in
        let d:N word = word_and m (word_not n) in
        (Rd := d) s`;;

let arm_BIC_VEC = define
 `arm_BIC_VEC Rd Rn Rm datasize =
    \s. let n = read Rn s
        and m = word_not(read Rm s) in
        if datasize = 128 then
          let d:(128)word = word_and n m in
          (Rd := d) s
        else
          let d:(64)word = word_subword (word_and n m) (0,64) in
          (Rd := word_zx d:(128)word) s`;;

let arm_BICS = define
 `arm_BICS Rd Rm Rn =
    \s. let m = read Rm s
        and n = read Rn s in
        let d:N word = word_and m (word_not n) in
        (Rd := d ,,
         NF := (ival d < &0) ,,
         ZF := (val d = 0) ,,
         CF := F ,,
         VF := F) s`;;

let arm_BIT = define
 `arm_BIT Rd Rn Rm datasize =
    \s. let m = read Rm s
        and n = read Rn s
        and d = read Rd s in
        let out:(128)word = word_or (word_and d (word_not m)) (word_and n m) in
        if datasize = 128 then
          (Rd := out) s
        else
          let out':(64)word = word_subword out (0,64) in
          (Rd := word_zx out':(128)word) s`;;

(*** As with x86, we have relative and absolute versions of branch & link ***)
(*** The absolute one gives a natural way of handling linker-insertions.  ***)

let arm_BL = define
 `arm_BL (off:28 word) =
    \s. let pc_incr = read PC s in
        let pc = word_sub pc_incr (word 4) in
        let pc_next = word_add pc (word_sx off) in
        (X30 := pc_incr ,,
         PC := pc_next ,,
         events := CONS (EventJump (pc,pc_next)) (read events s)) s`;;

let arm_BL_ABSOLUTE = define
 `arm_BL_ABSOLUTE (target:64 word) =
    \s. let pc_incr = read PC s in
        let pc = word_sub pc_incr (word 4) in
        (X30 := pc_incr ,,
         PC := target ,,
         events := CONS (EventJump (pc,target)) (read events s)) s`;;

(*** For conditional branches, including CBZ and CBNZ the offset is       ***)
(*** encoded as a 19-bit word that's turned into a 21-bit word multiplied ***)
(*** by 4 then sign-extended.                                             ***)

let arm_Bcond = define
 `arm_Bcond cc (off:21 word) =
        \s. let pc = word_sub (read PC s) (word 4) in
            let pc_next = if condition_semantics cc s
                   then word_add pc (word_sx off)
                   else read PC s in
            (PC := pc_next ,,
             events := CONS (EventJump (pc,pc_next)) (read events s)) s`;;

let arm_CBNZ = define
 `arm_CBNZ Rt (off:21 word) =
        \s. let pc = word_sub (read PC s) (word 4) in
            let pc_next = if ~(read Rt s = word 0)
                   then word_add pc (word_sx off)
                   else read PC s in
            (PC := pc_next ,,
             events := CONS (EventJump (pc,pc_next)) (read events s)) s`;;

let arm_CBZ = define
 `arm_CBZ Rt (off:21 word)  =
        \s. let pc = word_sub (read PC s) (word 4) in
            let pc_next = if read Rt s = word 0
                   then word_add pc (word_sx off)
                   else read PC s in
            (PC := pc_next ,,
             events := CONS (EventJump (pc,pc_next)) (read events s)) s`;;

let arm_CCMN = define
 `arm_CCMN Rm Rn (nzcv:4 word) cc =
    \s. let m = read Rm s
        and n = read Rn s
        and p = condition_semantics cc s in
        let d:N word = word_add m n in
        (NF := (if p then ival d < &0 else bit 3 nzcv) ,,
         ZF := (if p then val d = 0 else bit 2 nzcv) ,,
         CF := (if p then ~(val m + val n = val d) else bit 1 nzcv) ,,
         VF := (if p then ~(ival m + ival n = ival d) else bit 0 nzcv)) s`;;

let arm_CCMP = define
 `arm_CCMP Rm Rn (nzcv:4 word) cc =
    \s. let m = read Rm s
        and n = read Rn s
        and p = condition_semantics cc s in
        let d:N word = word_sub m n in
        (NF := (if p then ival d < &0 else bit 3 nzcv) ,,
         ZF := (if p then val d = 0 else bit 2 nzcv) ,,
         CF := (if p then &(val m) - &(val n):int = &(val d)
                else bit 1 nzcv) ,,
         VF := (if p then ~(ival m - ival n = ival d) else bit 0 nzcv)) s`;;

let arm_CLZ = define
 `arm_CLZ Rd Rn =
        \s. (Rd := (word(word_clz (read Rn s:N word)):N word)) s`;;

let arm_CMHI_VEC = define
 `arm_CMHI_VEC Rd Rn Rm esize datasize =
    \s:armstate.
        let n = read Rn s in
        let m = read Rm s in
        if datasize = 128 then
          let d:(128)word =
            if esize = 64 then simd2 (masking word_ugt) n m
            else if esize = 32 then simd4 (masking word_ugt) n m
            else if esize = 16 then simd8 (masking word_ugt) n m
            else simd16 (masking word_ugt) n m in
          (Rd := d) s
        else
          let n:(64)word = word_subword n (0,64) in
          let m:(64)word = word_subword m (0,64) in
          let d:(64)word =
            if esize = 32 then simd2 (masking word_ugt) n m
            else if esize = 16 then simd4 (masking word_ugt) n m
            else simd8 (masking word_ugt) n m in
          (Rd := word_zx d:(128)word) s`;;

let arm_CNT = define
 `arm_CNT Rd Rn datasize =
    \s:armstate.
        let n = read Rn s in
        if datasize = 128 then
          let d:(128)word = usimd16 (word o word_popcount) n in
          (Rd := d) s
        else
          let n':int64 = word_subword n (0,64) in
          let d:int64 = usimd8 (word o word_popcount) n' in
          (Rd := word_zx d) s`;;

let arm_CSEL = define
 `arm_CSEL Rd Rn Rm cc =
        \s. (Rd := if condition_semantics cc s
                   then read Rn s
                   else read Rm s) s`;;

let arm_CSINC = define
 `arm_CSINC Rd Rn Rm cc =
        \s. (Rd := if condition_semantics cc s
                   then read Rn s
                   else word_add (read Rm s) (word 1)) s`;;

let arm_CSINV = define
 `arm_CSINV Rd Rn Rm cc =
        \s. (Rd := if condition_semantics cc s
                   then read Rn s
                   else word_not(read Rm s)) s`;;

let arm_CSNEG = define
 `arm_CSNEG Rd Rn Rm cc =
        \s. (Rd := if condition_semantics cc s
                   then read Rn s
                   else word_neg(read Rm s)) s`;;

(* DUP (general) *)
let arm_DUP_GEN = define
 `arm_DUP_GEN Rd Rn esize datasize =
    \s. let n:int64 = read Rn (s:armstate) in
        if datasize = 128 then
          let d:(128)word =
            if esize = 64 then word_duplicate n
            else if esize = 32 then word_duplicate (word_zx n:32 word)
            else if esize = 16 then word_duplicate (word_zx n:16 word)
            else word_duplicate (word_zx n:8 word) in
          (Rd := d) s
        else
          let d:64 word =
            if esize = 32 then word_duplicate (word_zx n:32 word)
            else if esize = 16 then word_duplicate (word_zx n:16 word)
            else word_duplicate (word_zx n:8 word) in
          (Rd := word_zx d:(128)word) s`;;

let arm_EON = define
 `arm_EON Rd Rm Rn =
    \s. let m = read Rm s
        and n = read Rn s in
        let d:N word = word_xor m (word_not n) in
        (Rd := d) s`;;

let arm_EOR = define
 `arm_EOR Rd Rm Rn =
    \s. let m = read Rm s
        and n = read Rn s in
        let d:N word = word_xor m n in
        (Rd := d) s`;;

let arm_EOR_VEC = define
 `arm_EOR_VEC Rd Rn Rm datasize =
    \s. let m = read Rm s
        and n = read Rn s in
        if datasize = 128 then
          let d:(128)word = word_xor m n in
          (Rd := d) s
        else
          let d:(64)word = word_subword (word_xor m n) (0,64) in
          (Rd := word_zx d:(128)word) s`;;

let arm_EXT = define
 `arm_EXT Rd Rn Rm pos =
    \s. let m:N word = read Rm s
        and n:N word = read Rn s in
        let mn:(N tybit0)word = word_join m n in
        let d:N word = word_subword mn (pos,dimindex(:N)):(N)word in
        (Rd := d) s`;;

(*** The lsb argument is forced modulo the wordsize here, but that should
 *** happen implicitly from the size of the immediate when using the decoder.
 ***)

let arm_EXTR = define
 `arm_EXTR Rd Rn Rm lsb =
    \s. let n:N word = read Rn s
        and m:N word = read Rm s
        and l = lsb MOD dimindex(:N) in
        let concat:(N tybit0)word = word_join n m in
        let d:N word = word_subword concat (l,dimindex(:N)) in
        (Rd := d) s`;;

let arm_FCSEL = define
 `arm_FCSEL Rd Rn Rm cc datasize =
   \s. let n:int128 = read Rn s
       and m:int128 = read Rm s
       and p = condition_semantics cc s in
       (Rd := word_subword (if p then n else m) (0,datasize)) s`;;

let arm_INS = define
 `arm_INS Rd Rn destindex srcindex esize datasize =
    \s:armstate.
        let d:int128 = read Rd s
        and n:int128 = read Rn s in
        let n':int128 = word_subword n (0,datasize) in
        let n'':int128 = word_subword n' (srcindex,esize) in
        let d':(128)word = word_insert d (destindex,esize) n'' in
        (Rd := d') s`;;

let arm_INS_GEN = define
 `arm_INS_GEN Rd Rn ix esize =
    \s:armstate.
        let d:int128 = read Rd s
        and n:N word = read Rn s in
        let d':int128 = word_insert d (ix,esize) n in
        (Rd := d') s`;;

let arm_LSLV = define
 `arm_LSLV Rd Rm Rn =
    \s. let m = read Rm s
        and n = read Rn s in
        let d:N word = word_jshl m n in
        (Rd := d) s`;;

let arm_LSRV = define
 `arm_LSRV Rd Rm Rn =
    \s. let m = read Rm s
        and n = read Rn s in
        let d:N word = word_jushr m n in
        (Rd := d) s`;;

let arm_MADD = define
 `arm_MADD Rd Rn Rm Ra =
    \s. let n:N word = read Rn s
        and m:N word = read Rm s
        and a:N word = read Ra s in
        let d:N word = word(val a + val n * val m) in
        (Rd := d) s`;;

let arm_MLS_VEC = define
 `arm_MLS_VEC Rd Rn Rm esize datasize =
    \s. let d = read Rd s
        and n = read Rn s
        and m = read Rm s in
        if datasize = 128 then
          let d':(128)word =
            if esize = 32 then simd4 word_sub d (simd4 word_mul n m)
            else if esize = 16 then simd8 word_sub d (simd8 word_mul n m)
            else simd16 word_sub d (simd16 word_mul n m) in
          (Rd := d') s
        else
          let d:(64)word = word_subword d (0,64)
          and n:(64)word = word_subword n (0,64)
          and m:(64)word = word_subword m (0,64) in
          let d':(64)word =
            if esize = 32 then simd2 word_sub d (simd2 word_mul n m)
            else if esize = 16 then simd4 word_sub d (simd4 word_mul n m)
            else simd8 word_sub d (simd8 word_mul n m) in
          (Rd := word_zx d':(128)word) (s:armstate)`;;

let arm_MOVI = define
 `arm_MOVI (Rd:(armstate,N word)component) (imm:int64) =
    \s. let immN:N word = if dimindex(:N) = 128
          then word_join imm imm:(N)word
          else word (val imm):(N)word // identity
        in
        (Rd := immN) s`;;

let arm_MOVK = define
 `arm_MOVK (Rd:(armstate,N word)component) (imm:int16) pos =
    Rd :> subword(pos,16) := imm`;;

let arm_MOVN = define
 `arm_MOVN (Rd:(armstate,N word)component) (imm:int16) pos =
    Rd := word_not (word (val imm * 2 EXP pos))`;;

let arm_MOVZ = define
 `arm_MOVZ (Rd:(armstate,N word)component) (imm:int16) pos =
    Rd := word (val imm * 2 EXP pos)`;;

let arm_FMOV_FtoI = define
 `arm_FMOV_FtoI Rd Rn (part:num) esize  =
    \s. let n:(128)word = read Rn s in
        let intval = word_subword n (part*esize,esize) in
        (Rd := intval) s
    `;;

let arm_FMOV_ItoF = define
 `arm_FMOV_ItoF Rd Rn (part:num) =
    \s. let fltval:(64)word = read Rn s in
        let d:(128)word = read Rd s in
        if part = 0
        then (Rd := word_zx fltval:(128)word) s
        else (Rd := word_insert d (64, 64) fltval) s
    `;;

let arm_MSUB = define
 `arm_MSUB Rd Rn Rm Ra =
    \s. let n:N word = read Rn s
        and m:N word = read Rm s
        and a:N word = read Ra s in
        let d:N word = iword(ival a - ival n * ival m) in
        (Rd := d) s`;;

let arm_MUL_VEC = define
 `arm_MUL_VEC Rd Rn Rm esize datasize =
    \s. let n = read Rn s in
        let m = read Rm s in
        if datasize = 128 then
          let d:(128)word =
            if esize = 32 then simd4 word_mul n m
            else if esize = 16 then simd8 word_mul n m
            else simd16 word_mul n m in
          (Rd := d) s
        else
          let n:(64)word = word_subword n (0,64) in
          let m:(64)word = word_subword m (0,64) in
          let d:(64)word =
            if esize = 32 then simd2 word_mul n m
            else if esize = 16 then simd4 word_mul n m
            else simd8 word_mul n m in
          (Rd := word_zx d:(128)word) s`;;

let arm_NOP = new_definition
  `arm_NOP = \s s':armstate. s = s'`;;

let arm_ORN = define
 `arm_ORN Rd Rm Rn =
    \s. let m = read Rm s
        and n = read Rn s in
        let d:N word = word_or m (word_not n) in
        (Rd := d) s`;;

let arm_ORR = define
 `arm_ORR Rd Rm Rn =
    \s. let m = read Rm s
        and n = read Rn s in
        let d:N word = word_or m n in
        (Rd := d) s`;;

let arm_ORR_VEC = define
 `arm_ORR_VEC Rd Rn Rm datasize =
    \s. let m = read Rm s
        and n = read Rn s in
        if datasize = 128 then
          let d:(128)word = word_or m n in
          (Rd := d) s
        else
          let d:(64)word = word_subword (word_or m n) (0,64) in
          (Rd := word_zx d:(128)word) s`;;

(*** The default RET uses X30. ***)

let arm_RET = define
 `arm_RET Rn =
    \s. let pc = word_sub (read PC s) (word 4) in
        let pc_next = read Rn s in
        (PC := pc_next ,,
         events := CONS (EventJump (pc,pc_next)) (read events s)) s`;;

let arm_REV64_VEC = define
 `arm_REV64_VEC Rd Rn esize =
    \s. let n:(128)word = read Rn (s:armstate) in
        let n_reversed32 = usimd2 (\x. word_join
          (word_subword x (0,32):(32)word) (word_subword x (32,32):(32)word)
          : (64)word) n in
        if esize = 32 then (Rd := n_reversed32) s else
        let n_reversed16 = usimd4 (\x. word_join
          (word_subword x (0,16):(16)word) (word_subword x (16,16):(16)word)
          : (32)word) n_reversed32 in
        if esize = 16 then (Rd := n_reversed16) s else
        let n_reversed8 = usimd8 (\x. word_join
          (word_subword x (0,8):(8)word) (word_subword x (8,8):(8)word)
          : (16)word) n_reversed16 in
        (Rd := n_reversed8) s`;;

let arm_RORV = define
 `arm_RORV Rd Rm Rn =
    \s. let m = read Rm s
        and n = read Rn s in
        let d:N word = word_jror m n in
        (Rd := d) s`;;

(*** Note that the carry flag is inverted for subtractions ***)
(*** Flag set means no borrow, flag clear means borrow.    ***)
(*** The (signed) overflow flag is as usual.               ***)

let arm_SBC = define
 `arm_SBC Rd Rm Rn =
    \s. let m = read Rm s
        and n = read Rn s
        and c = bitval(~read CF s) in
        let d:N word = word_sub m (word_add n (word c)) in
        (Rd := d) s`;;

let arm_SBCS = define
 `arm_SBCS Rd Rm Rn =
    \s. let m = read Rm s
        and n = read Rn s
        and c = bitval(~read CF s) in
        let d:N word = word_sub m (word_add n (word c)) in
        (Rd := d ,,
         NF := (ival d < &0) ,,
         ZF := (val d = 0) ,,
         CF := (&(val m) - (&(val n) + &c):int = &(val d)) ,,
         VF := ~(ival m - (ival n + &c) = ival d)) s`;;

let arm_SBFM = define
 `arm_SBFM Rd Rn immr imms =
    \s. let x:N word = read Rn (s:armstate) in
        let y:N word =
          if imms >= immr then
            word_sxfrom (imms - immr) (word_subword x (immr,(imms-immr)+1))
          else
            word_sxfrom (dimindex(:N) - (immr - imms))
             (word_shl (word_subword x (0,imms+1)) (dimindex(:N) - immr)) in
        (Rd := y) s`;;

let arm_SHL_VEC = define
 `arm_SHL_VEC Rd Rn amt esize datasize =
    \s. let n = read Rn s in
        if datasize = 128 then
          let d:(128)word =
            if esize = 64 then usimd2 (\x. word_shl x amt) n
            else if esize = 32 then usimd4 (\x. word_shl x amt) n
            else if esize = 16 then usimd8 (\x. word_shl x amt) n
            else usimd16 (\x. word_shl x amt) n in
          (Rd := d) s
        else
          let n:(64)word = word_subword n (0,64) in
          let d:(64)word =
            if esize = 32 then usimd2 (\x. word_shl x amt) n
            else if esize = 16 then usimd4 (\x. word_shl x amt) n
            else usimd8 (\x. word_shl x amt) n in
          (Rd := word_zx d:(128)word) s`;;

let word_ishr_round = new_definition
 `(word_ishr_round:N word ->num->N word) x n =
  iword((ival x + &2 pow n div &2) div (&2 pow n))`;;

let arm_SRSHR_VEC = define
 `arm_SRSHR_VEC Rd Rn amt esize datasize =
    \s. let n = read Rn (s:armstate) in
        if datasize = 128 then
          let d:(128)word =
            if esize = 64 then usimd2 (\x. word_ishr_round x amt) n
            else if esize = 32 then usimd4 (\x. word_ishr_round x amt) n
            else if esize = 16 then usimd8 (\x. word_ishr_round x amt) n
            else usimd16 (\x. word_ishr_round x amt) n in
          (Rd := d) s
        else
          let n:(64)word = word_subword n (0,64) in
          let d:(64)word =
            if esize = 32 then usimd2 (\x. word_ishr_round x amt) n
            else if esize = 16 then usimd4 (\x. word_ishr_round x amt) n
            else usimd8 (\x. word_ishr_round x amt) n in
          (Rd := word_zx d:(128)word) s`;;

let arm_SSHR_VEC = define
 `arm_SSHR_VEC Rd Rn amt esize datasize =
    \s. let n = read Rn (s:armstate) in
        if datasize = 128 then
          let d:(128)word =
            if esize = 64 then usimd2 (\x. word_ishr x amt) n
            else if esize = 32 then usimd4 (\x. word_ishr x amt) n
            else if esize = 16 then usimd8 (\x. word_ishr x amt) n
            else usimd16 (\x. word_ishr x amt) n in
          (Rd := d) s
        else
          let n:(64)word = word_subword n (0,64) in
          let d:(64)word =
            if esize = 32 then usimd2 (\x. word_ishr x amt) n
            else if esize = 16 then usimd4 (\x. word_ishr x amt) n
            else usimd8 (\x. word_ishr x amt) n in
          (Rd := word_zx d:(128)word) s`;;

(* SLI (vector) *)
let arm_SLI_VEC = define
 `arm_SLI_VEC Rd Rn shiftamnt datasize esize =
    \s. let n:(128)word = read Rn s
        and d:(128)word = read Rd s in
        let mask = (2 EXP shiftamnt) - 1 in
        let op8  = (\ni (di:  8 word). word_or (word_shl ni shiftamnt) (word_and di (word mask))) in
        let op16 = (\ni (di: 16 word). word_or (word_shl ni shiftamnt) (word_and di (word mask))) in
        let op32 = (\ni (di: 32 word). word_or (word_shl ni shiftamnt) (word_and di (word mask))) in
        let op64 = (\ni (di: 64 word). word_or (word_shl ni shiftamnt) (word_and di (word mask))) in
        if datasize = 128 then
          let d:(128)word =
            if esize = 64 then simd2 op64 n d
            else if esize = 32 then simd4 op32 n d
            else if esize = 16 then simd8 op16 n d
            else simd16 op8 n d in
          (Rd := d) s
        else
        let n:(64)word = word_subword n (0, 64) in
        let d:(64)word = word_subword d (0, 64) in
          let d:(64)word =
            if esize = 32 then simd2 op32 n d
            else if esize = 16 then simd4 op16 n d
            else simd8 op8 n d in
          (Rd := word_zx d:(128)word) s`;;

(* SRI (vector) *)
let arm_SRI_VEC = define
 `arm_SRI_VEC Rd Rn shiftamnt esize datasize =
   \s. let n:(128)word = read Rn s in
       let d:(128)word = read Rd s in
       let mask = (2 EXP (esize - shiftamnt)) - 1 in
       if datasize = 128 then
         let d:(128)word = if esize = 64 then
             simd2 (\ni di. word_or
               (word_ushr ni shiftamnt) (word_and di (word_not (word mask)))) n d
           else if esize = 32 then
             simd4 (\ni di. word_or
               (word_ushr ni shiftamnt) (word_and di (word_not (word mask)))) n d
           else if esize = 16 then
             simd8 (\ni di. word_or
               (word_ushr ni shiftamnt) (word_and di (word_not (word mask)))) n d
           else
             simd16 (\ni di. word_or
               (word_ushr ni shiftamnt) (word_and di (word_not (word mask)))) n d in
         (Rd := d) s
       else
         let nd:(64)word = word_subword n (0, 64) in
         let dd:(64)word = word_subword d (0, 64) in
         let dd:(64)word = if esize = 32 then
             simd2 (\ni di. word_or
               (word_ushr ni shiftamnt) (word_and di (word_not (word mask)))) nd dd
           else if esize = 16 then
             simd4 (\ni di. word_or
               (word_ushr ni shiftamnt) (word_and di (word_not (word mask)))) nd dd
           else
             simd8 (\ni di. word_or
               (word_ushr ni shiftamnt) (word_and di (word_not (word mask)))) nd dd in
         (Rd := word_zx dd:(128)word) s`;;

let arm_SHRN = define
 `arm_SHRN Rd Rn amnt esize = // esize is Rd's element size
    \s. let n:(128)word = read Rn s in
        let res:(64)word =
          if esize = 32 then
            usimd2 (\(x:(64)word).
              word_subword (word_ushr x amnt) (0,32):(32)word) n
          else if esize = 16 then
            usimd4 (\(x:(32)word).
              word_subword (word_ushr x amnt) (0,16):(16)word) n
          else // esize = 8
            usimd8 (\(x:(16)word).
              word_subword (word_ushr x amnt) (0,8):(8)word) n in
        // equivalent to word_zx res:(128)word, but use word_subword instead
        (Rd := word_subword res (0,128)) s`;;

let arm_SMULH = define
 `arm_SMULH Rd Rn Rm =
    \s. let n:N word = read Rn (s:armstate)
        and m:N word = read Rm s in
        let d:N word = iword((ival n * ival m) div (&2 pow dimindex(:N))) in
        (Rd := d) s`;;

let word_2smulh = define
 `(word_2smulh:N word->N word->N word) x y =
  iword_saturate((&2 * ival x * ival y) div &2 pow dimindex(:N))`;;

let arm_SQDMULH_VEC = define
 `arm_SQDMULH_VEC Rd Rn Rm esize datasize =
    \s. let n = read Rn (s:armstate)
        and m = read Rm s in
        if datasize = 128 then
          let d:(128)word =
            if esize = 32 then simd4 word_2smulh n m
            else if esize = 16 then simd8 word_2smulh n m
            else simd16 word_2smulh n m in
          (Rd := d) s
        else
          let n:(64)word = word_subword n (0,64) in
          let m:(64)word = word_subword m (0,64) in
          let d:(64)word =
            if esize = 32 then simd2 word_2smulh n m
            else if esize = 16 then simd4 word_2smulh n m
            else simd8 word_2smulh n m in
          (Rd := word_zx d:(128)word) s`;;

let word_2smulh_round = define
 `(word_2smulh_round:N word->N word->N word) x y =
    iword_saturate((&2 * ival x * ival y + &2 pow (dimindex(:N) - 1)) div
                    &2 pow dimindex(:N))`;;

let arm_SQRDMULH_VEC = define
 `arm_SQRDMULH_VEC Rd Rn Rm esize datasize =
    \s. let n = read Rn (s:armstate)
        and m = read Rm s in
        if datasize = 128 then
          let d:(128)word =
            if esize = 32 then simd4 word_2smulh_round n m
            else if esize = 16 then simd8 word_2smulh_round n m
            else simd16 word_2smulh_round n m in
          (Rd := d) s
        else
          let n:(64)word = word_subword n (0,64) in
          let m:(64)word = word_subword m (0,64) in
          let d:(64)word =
            if esize = 32 then simd2 word_2smulh_round n m
            else if esize = 16 then simd4 word_2smulh_round n m
            else simd8 word_2smulh_round n m in
          (Rd := word_zx d:(128)word) s`;;

let arm_SUB = define
 `arm_SUB Rd Rm Rn =
    \s. let m = read Rm s
        and n = read Rn s in
        let d:N word = word_sub m n in
        (Rd := d) s`;;

let arm_SUB_VEC = define
 `arm_SUB_VEC Rd Rn Rm esize datasize =
    \s. let n = read Rn s in
        let m = read Rm s in
        if datasize = 128 then
          let d:(128)word =
            if esize = 64 then simd2 word_sub n m
            else if esize = 32 then simd4 word_sub n m
            else if esize = 16 then simd8 word_sub n m
            else simd16 word_sub n m in
          (Rd := d) s
        else
          let n:(64)word = word_subword n (0,64) in
          let m:(64)word = word_subword m (0,64) in
          let d:(64)word =
            if esize = 32 then simd2 word_sub n m
            else if esize = 16 then simd4 word_sub n m
            else simd8 word_sub n m in
          (Rd := word_zx d:(128)word) s`;;

let arm_SUBS = define
 `arm_SUBS Rd Rm Rn =
    \s. let m = read Rm s
        and n = read Rn s in
        let d:N word = word_sub m n in
        (Rd := d ,,
         NF := (ival d < &0) ,,
         ZF := (val d = 0) ,,
         CF := (&(val m) - &(val n):int = &(val d)) ,,
         VF := ~(ival m - ival n = ival d)) s`;;

let arm_UADDLP = define
 `arm_UADDLP Rd Rn esize =
    \s. let n = read Rn (s:armstate) in
        if esize = 32 then
          let res = usimd2
            (\x. word_add (word_zx (word_subword x (0,32):(32)word):(64)word)
                          (word_zx (word_subword x (32,32):(32)word):(64)word)) n in
          (Rd := res) s
        else if esize = 16 then
          let res = usimd4
            (\x. word_add (word_zx (word_subword x (0,16):(32)word):(32)word)
                          (word_zx (word_subword x (16,16):(32)word):(32)word)) n in
          (Rd := res) s
        else // esize=8
          let res = usimd8
            (\x. word_add (word_zx (word_subword x (0,8):(32)word):(16)word)
                          (word_zx (word_subword x (8,8):(32)word):(16)word)) n in
          (Rd := res) s`;;

let arm_UADDLV = define
 `arm_UADDLV Rd Rn elements esize =
    \s:armstate.
        let n:128 word = read Rn s in
        let d = nsum (0..elements-1)
                    (\i. val(word_subword n (esize*i,esize):int128)) in
         (Rd := (word d:128 word)) s`;;

let arm_UBFM = define
 `arm_UBFM Rd Rn immr imms =
    \s. let x:N word = read Rn (s:armstate) in
        let y:N word =
          if imms >= immr then word_subword x (immr,(imms-immr)+1)
          else word_shl (word_subword x (0,imms+1)) (dimindex(:N) - immr) in
        (Rd := y) s`;;

let arm_UMADDL = define
 `arm_UMADDL Rd Rn Rm Ra =
    \s. let n:int32 = read Rn (s:armstate)
        and m:int32 = read Rm s
        and a:int64 = read Ra s in
        let d:int64 = word(val a + val n * val m) in
        (Rd := d) s`;;

let arm_UMLAL_VEC = define
 `arm_UMLAL_VEC Rd Rn Rm esize =
    \s. let n:(128)word = read Rn (s:armstate) in
        let m:(128)word = read Rm (s:armstate) in
        let d:(128)word = read Rd (s:armstate) in
        let nlow:(64)word = word_subword n (0,64) in
        let mlow:(64)word = word_subword m (0,64) in
        if esize = 32 then
          let nlowzx = usimd2 (word_zx:(32)word->(64)word) nlow in
          let mlowzx = usimd2 (word_zx:(32)word->(64)word) mlow in
          (Rd := simd2 word_add (simd2 word_mul nlowzx mlowzx) d) s
        else if esize = 16 then
          let nlowzx = usimd4 (word_zx:(16)word->(32)word) nlow in
          let mlowzx = usimd4 (word_zx:(16)word->(32)word) mlow in
          (Rd := simd4 word_add (simd4 word_mul nlowzx mlowzx) d) s
        else // esize=8
          let nlowzx = usimd8 (word_zx:(8)word->(16)word) nlow in
          let mlowzx = usimd8 (word_zx:(8)word->(16)word) mlow in
          (Rd := simd8 word_add (simd8 word_mul nlowzx mlowzx) d) s`;;

let arm_UMLAL2_VEC = define
 `arm_UMLAL2_VEC Rd Rn Rm esize =
    \s. let n:(128)word = read Rn (s:armstate) in
        let m:(128)word = read Rm (s:armstate) in
        let d:(128)word = read Rd (s:armstate) in
        let nhi:(64)word = word_subword n (64,64) in
        let mhi:(64)word = word_subword m (64,64) in
        if esize = 32 then
          let nhizx = usimd2 (word_zx:(32)word->(64)word) nhi in
          let mhizx = usimd2 (word_zx:(32)word->(64)word) mhi in
          (Rd := simd2 word_add (simd2 word_mul nhizx mhizx) d) s
        else if esize = 16 then
          let nhizx = usimd4 (word_zx:(16)word->(32)word) nhi in
          let mhizx = usimd4 (word_zx:(16)word->(32)word) mhi in
          (Rd := simd4 word_add (simd4 word_mul nhizx mhizx) d) s
        else // esize=8
          let nhizx = usimd8 (word_zx:(8)word->(16)word) nhi in
          let mhizx = usimd8 (word_zx:(8)word->(16)word) mhi in
          (Rd := simd8 word_add (simd8 word_mul nhizx mhizx) d) s`;;

let arm_UMLSL_VEC = define
 `arm_UMLSL_VEC Rd Rn Rm esize =
    \s. let n:(128)word = read Rn (s:armstate) in
        let m:(128)word = read Rm (s:armstate) in
        let d:(128)word = read Rd (s:armstate) in
        let nlow:(64)word = word_subword n (0,64) in
        let mlow:(64)word = word_subword m (0,64) in
        if esize = 32 then
          let nlowzx = usimd2 (word_zx:(32)word->(64)word) nlow in
          let mlowzx = usimd2 (word_zx:(32)word->(64)word) mlow in
          (Rd := simd2 word_sub d (simd2 word_mul nlowzx mlowzx)) s
        else if esize = 16 then
          let nlowzx = usimd4 (word_zx:(16)word->(32)word) nlow in
          let mlowzx = usimd4 (word_zx:(16)word->(32)word) mlow in
          (Rd := simd4 word_sub d (simd4 word_mul nlowzx mlowzx)) s
        else // esize=8
          let nlowzx = usimd8 (word_zx:(8)word->(16)word) nlow in
          let mlowzx = usimd8 (word_zx:(8)word->(16)word) mlow in
          (Rd := simd8 word_sub d (simd8 word_mul nlowzx mlowzx)) s`;;

let arm_UMLSL2_VEC = define
 `arm_UMLSL2_VEC Rd Rn Rm esize =
    \s. let n:(128)word = read Rn (s:armstate) in
        let m:(128)word = read Rm (s:armstate) in
        let d:(128)word = read Rd (s:armstate) in
        let nhi:(64)word = word_subword n (64,64) in
        let mhi:(64)word = word_subword m (64,64) in
        if esize = 32 then
          let nhizx = usimd2 (word_zx:(32)word->(64)word) nhi in
          let mhizx = usimd2 (word_zx:(32)word->(64)word) mhi in
          (Rd := simd2 word_sub d (simd2 word_mul nhizx mhizx)) s
        else if esize = 16 then
          let nhizx = usimd4 (word_zx:(16)word->(32)word) nhi in
          let mhizx = usimd4 (word_zx:(16)word->(32)word) mhi in
          (Rd := simd4 word_sub d (simd4 word_mul nhizx mhizx)) s
        else // esize=8
          let nhizx = usimd8 (word_zx:(8)word->(16)word) nhi in
          let mhizx = usimd8 (word_zx:(8)word->(16)word) mhi in
          (Rd := simd8 word_sub d (simd8 word_mul nhizx mhizx)) s`;;

let arm_SMLAL_VEC = define
 `arm_SMLAL_VEC Rd Rn Rm esize =
    \s. let n:(128)word = read Rn (s:armstate) in
        let m:(128)word = read Rm (s:armstate) in
        let d:(128)word = read Rd (s:armstate) in
        let nlow:(64)word = word_subword n (0,64) in
        let mlow:(64)word = word_subword m (0,64) in
        if esize = 32 then
          let nlowsx = usimd2 (word_sx:(32)word->(64)word) nlow in
          let mlowsx = usimd2 (word_sx:(32)word->(64)word) mlow in
          (Rd := simd2 word_add (simd2 word_mul nlowsx mlowsx) d) s
        else if esize = 16 then
          let nlowsx = usimd4 (word_sx:(16)word->(32)word) nlow in
          let mlowsx = usimd4 (word_sx:(16)word->(32)word) mlow in
          (Rd := simd4 word_add (simd4 word_mul nlowsx mlowsx) d) s
        else // esize=8
          let nlowsx = usimd8 (word_sx:(8)word->(16)word) nlow in
          let mlowsx = usimd8 (word_sx:(8)word->(16)word) mlow in
          (Rd := simd8 word_add (simd8 word_mul nlowsx mlowsx) d) s`;;

let arm_SMLAL2_VEC = define
 `arm_SMLAL2_VEC Rd Rn Rm esize =
    \s. let n:(128)word = read Rn (s:armstate) in
        let m:(128)word = read Rm (s:armstate) in
        let d:(128)word = read Rd (s:armstate) in
        let nhi:(64)word = word_subword n (64,64) in
        let mhi:(64)word = word_subword m (64,64) in
        if esize = 32 then
          let nhisx = usimd2 (word_sx:(32)word->(64)word) nhi in
          let mhisx = usimd2 (word_sx:(32)word->(64)word) mhi in
          (Rd := simd2 word_add (simd2 word_mul nhisx mhisx) d) s
        else if esize = 16 then
          let nhisx = usimd4 (word_sx:(16)word->(32)word) nhi in
          let mhisx = usimd4 (word_sx:(16)word->(32)word) mhi in
          (Rd := simd4 word_add (simd4 word_mul nhisx mhisx) d) s
        else // esize=8
          let nhisx = usimd8 (word_sx:(8)word->(16)word) nhi in
          let mhisx = usimd8 (word_sx:(8)word->(16)word) mhi in
          (Rd := simd8 word_add (simd8 word_mul nhisx mhisx) d) s`;;

let arm_SMLSL_VEC = define
 `arm_SMLSL_VEC Rd Rn Rm esize =
    \s. let n:(128)word = read Rn (s:armstate) in
        let m:(128)word = read Rm (s:armstate) in
        let d:(128)word = read Rd (s:armstate) in
        let nlow:(64)word = word_subword n (0,64) in
        let mlow:(64)word = word_subword m (0,64) in
        if esize = 32 then
          let nlowsx = usimd2 (word_sx:(32)word->(64)word) nlow in
          let mlowsx = usimd2 (word_sx:(32)word->(64)word) mlow in
          (Rd := simd2 word_sub d (simd2 word_mul nlowsx mlowsx)) s
        else if esize = 16 then
          let nlowsx = usimd4 (word_sx:(16)word->(32)word) nlow in
          let mlowsx = usimd4 (word_sx:(16)word->(32)word) mlow in
          (Rd := simd4 word_sub d (simd4 word_mul nlowsx mlowsx)) s
        else // esize=8
          let nlowsx = usimd8 (word_sx:(8)word->(16)word) nlow in
          let mlowsx = usimd8 (word_sx:(8)word->(16)word) mlow in
          (Rd := simd8 word_sub d (simd8 word_mul nlowsx mlowsx)) s`;;

let arm_SMLSL2_VEC = define
 `arm_SMLSL2_VEC Rd Rn Rm esize =
    \s. let n:(128)word = read Rn (s:armstate) in
        let m:(128)word = read Rm (s:armstate) in
        let d:(128)word = read Rd (s:armstate) in
        let nhi:(64)word = word_subword n (64,64) in
        let mhi:(64)word = word_subword m (64,64) in
        if esize = 32 then
          let nhisx = usimd2 (word_sx:(32)word->(64)word) nhi in
          let mhisx = usimd2 (word_sx:(32)word->(64)word) mhi in
          (Rd := simd2 word_sub d (simd2 word_mul nhisx mhisx)) s
        else if esize = 16 then
          let nhisx = usimd4 (word_sx:(16)word->(32)word) nhi in
          let mhisx = usimd4 (word_sx:(16)word->(32)word) mhi in
          (Rd := simd4 word_sub d (simd4 word_mul nhisx mhisx)) s
        else // esize=8
          let nhisx = usimd8 (word_sx:(8)word->(16)word) nhi in
          let mhisx = usimd8 (word_sx:(8)word->(16)word) mhi in
          (Rd := simd8 word_sub d (simd8 word_mul nhisx mhisx)) s`;;

let arm_UMSUBL = define
 `arm_UMSUBL Rd Rn Rm Ra =
    \s. let n:int32 = read Rn (s:armstate)
        and m:int32 = read Rm s
        and a:int64 = read Ra s in
        let d:int64 = iword(&(val a) - &(val n) * &(val m)) in
        (Rd := d) s`;;

let arm_UMOV = define
 `arm_UMOV Rd Rn idx size =
   \s. let n = read Rn (s:armstate) in
       let d:N word = word_subword n (idx*size*8,size*8) in
       (Rd := d) s`;;

let arm_UMULH = define
 `arm_UMULH Rd Rn Rm =
    \s. let n:N word = read Rn (s:armstate)
        and m:N word = read Rm s in
        let d:N word = word((val n * val m) DIV (2 EXP dimindex(:N))) in
        (Rd := d) s`;;

let arm_UMULL_VEC = define
 `arm_UMULL_VEC Rd Rn Rm esize =
    \s. // Get the low halfs
        let nl:(64)word = word_subword (read Rn s:(128)word) (0,64):(64)word in
        let ml:(64)word = word_subword (read Rm s:(128)word) (0,64):(64)word in
        if esize = 32 then
          let nlzx:(128)word = usimd2 (word_zx:(32)word->(64)word) nl in
          let mlzx:(128)word = usimd2 (word_zx:(32)word->(64)word) ml in
          (Rd := simd2 word_mul nlzx mlzx) s
        else if esize = 16 then
          let nlzx:(128)word = usimd4 (word_zx:(16)word->(32)word) nl in
          let mlzx:(128)word = usimd4 (word_zx:(16)word->(32)word) ml in
          (Rd := simd4 word_mul nlzx mlzx) s
        else // esize = 8
          let nlzx:(128)word = usimd8 (word_zx:(8)word->(16)word) nl in
          let mlzx:(128)word = usimd8 (word_zx:(8)word->(16)word) ml in
          (Rd := simd8 word_mul nlzx mlzx) s`;;

let arm_UMULL2_VEC = define
 `arm_UMULL2_VEC Rd Rn Rm esize =
    \s. // Get the low halfs
        let nl:(64)word = word_subword (read Rn s:(128)word) (64,64):(64)word in
        let ml:(64)word = word_subword (read Rm s:(128)word) (64,64):(64)word in
        if esize = 32 then
          let nlzx:(128)word = usimd2 (word_zx:(32)word->(64)word) nl in
          let mlzx:(128)word = usimd2 (word_zx:(32)word->(64)word) ml in
          (Rd := simd2 word_mul nlzx mlzx) s
        else if esize = 16 then
          let nlzx:(128)word = usimd4 (word_zx:(16)word->(32)word) nl in
          let mlzx:(128)word = usimd4 (word_zx:(16)word->(32)word) ml in
          (Rd := simd4 word_mul nlzx mlzx) s
        else // esize = 8
          let nlzx:(128)word = usimd8 (word_zx:(8)word->(16)word) nl in
          let mlzx:(128)word = usimd8 (word_zx:(8)word->(16)word) ml in
          (Rd := simd8 word_mul nlzx mlzx) s`;;

let arm_SMULL_VEC = define
 `arm_SMULL_VEC Rd Rn Rm esize =
    \s. // Get the low halfs
        let nl:(64)word = word_subword (read Rn s:(128)word) (0,64):(64)word in
        let ml:(64)word = word_subword (read Rm s:(128)word) (0,64):(64)word in
        if esize = 32 then
          let nlsx:(128)word = usimd2 (word_sx:(32)word->(64)word) nl in
          let mlsx:(128)word = usimd2 (word_sx:(32)word->(64)word) ml in
          (Rd := simd2 word_mul nlsx mlsx) s
        else if esize = 16 then
          let nlsx:(128)word = usimd4 (word_sx:(16)word->(32)word) nl in
          let mlsx:(128)word = usimd4 (word_sx:(16)word->(32)word) ml in
          (Rd := simd4 word_mul nlsx mlsx) s
        else // esize = 8
          let nlsx:(128)word = usimd8 (word_sx:(8)word->(16)word) nl in
          let mlsx:(128)word = usimd8 (word_sx:(8)word->(16)word) ml in
          (Rd := simd8 word_mul nlsx mlsx) s`;;

let arm_SMULL2_VEC = define
 `arm_SMULL2_VEC Rd Rn Rm esize =
    \s. // Get the low halfs
        let nl:(64)word = word_subword (read Rn s:(128)word) (64,64):(64)word in
        let ml:(64)word = word_subword (read Rm s:(128)word) (64,64):(64)word in
        if esize = 32 then
          let nlsx:(128)word = usimd2 (word_sx:(32)word->(64)word) nl in
          let mlsx:(128)word = usimd2 (word_sx:(32)word->(64)word) ml in
          (Rd := simd2 word_mul nlsx mlsx) s
        else if esize = 16 then
          let nlsx:(128)word = usimd4 (word_sx:(16)word->(32)word) nl in
          let mlsx:(128)word = usimd4 (word_sx:(16)word->(32)word) ml in
          (Rd := simd4 word_mul nlsx mlsx) s
        else // esize = 8
          let nlsx:(128)word = usimd8 (word_sx:(8)word->(16)word) nl in
          let mlsx:(128)word = usimd8 (word_sx:(8)word->(16)word) ml in
          (Rd := simd8 word_mul nlsx mlsx) s`;;

let arm_USHR_VEC = define
 `arm_USHR_VEC Rd Rn amt esize datasize =
    \s. let n = read Rn s in
        if datasize = 128 then
          let d:(128)word =
            if esize = 64 then usimd2 (\x. word_ushr x amt) n
            else if esize = 32 then usimd4 (\x. word_ushr x amt) n
            else if esize = 16 then usimd8 (\x. word_ushr x amt) n
            else usimd16 (\x. word_ushr x amt) n in
          (Rd := d) s
        else
          let n:(64)word = word_subword n (0,64) in
          let d:(64)word =
            if esize = 32 then usimd2 (\x. word_ushr x amt) n
            else if esize = 16 then usimd4 (\x. word_ushr x amt) n
            else usimd8 (\x. word_ushr x amt) n in
          (Rd := word_zx d:(128)word) s`;;

let arm_USRA_VEC = define
 `arm_USRA_VEC Rd Rn shift esize datasize =
    \s. let n:(128)word = read Rn s in
        let n:(128)word =
          if esize = 64 then usimd2 (\x. word_ushr x shift) n
          else if esize = 32 then usimd4 (\x. word_ushr x shift) n
          else if esize = 16 then usimd8 (\x. word_ushr x shift) n
          else usimd16 (\x. word_ushr x shift) n in
        let d:(128)word = read Rd s in
        if datasize = 128 then
          let d:(128)word =
            if esize = 64 then simd2 word_add d n
            else if esize = 32 then simd4 word_add d n
            else if esize = 16 then simd8 word_add d n
            else simd16 word_add d n in
          (Rd := d) s
        else // datasize = 64
          let n:(64)word = word_subword n (0,64):(64)word in
          let d:(64)word = word_subword d (0,64):(64)word in
          let d:(64)word =
            if esize = 32 then simd2 word_add d n
            else if esize = 16 then simd4 word_add d n
            else simd8 word_add d n in
          (Rd := word_zx d:(128)word) s`;;

let arm_UZP1 = define
 `arm_UZP1 Rd Rn Rm esize =
    \s. let n:(128)word = read Rn (s:armstate) in
        let m:(128)word = read Rm (s:armstate) in
        if esize = 64 then
          let neven:(64)word = word_subword n (0,64) in
          let meven:(64)word = word_subword m (0,64) in
          (Rd := (word_join meven neven:(128)word)) s
        else if esize = 32 then
          let neven:(64)word = usimd2 (\x. word_subword x (0,32): (32)word) n in
          let meven:(64)word = usimd2 (\x. word_subword x (0,32): (32)word) m in
          (Rd := (word_join meven neven:(128)word)) s
        else if esize = 16 then
          let neven:(64)word = usimd4 (\x. word_subword x (0,16): (16)word) n in
          let meven:(64)word = usimd4 (\x. word_subword x (0,16): (16)word) m in
          (Rd := (word_join meven neven:(128)word)) s
        else // esize=8
          let neven:(64)word = usimd8 (\x. word_subword x (0,8): (8)word) n in
          let meven:(64)word = usimd8 (\x. word_subword x (0,8): (8)word) m in
          (Rd := (word_join meven neven:(128)word)) s`;;

let arm_UZP2 = define
 `arm_UZP2 Rd Rn Rm esize =
    \s. let n:(128)word = read Rn (s:armstate) in
        let m:(128)word = read Rm (s:armstate) in
        if esize = 64 then
          let nodd:(64)word = word_subword n (64,64) in
          let modd:(64)word = word_subword m (64,64) in
          (Rd := (word_join modd nodd:(128)word)) s
        else if esize = 32 then
          let nodd:(64)word = usimd2 (\x. word_subword x (32,32): (32)word) n in
          let modd:(64)word = usimd2 (\x. word_subword x (32,32): (32)word) m in
          (Rd := (word_join modd nodd:(128)word)) s
        else if esize = 16 then
          let nodd:(64)word = usimd4 (\x. word_subword x (16,16): (16)word) n in
          let modd:(64)word = usimd4 (\x. word_subword x (16,16): (16)word) m in
          (Rd := (word_join modd nodd:(128)word)) s
        else // esize=8
          let nodd:(64)word = usimd8 (\x. word_subword x (8,8): (8)word) n in
          let modd:(64)word = usimd8 (\x. word_subword x (8,8): (8)word) m in
          (Rd := (word_join modd nodd:(128)word)) s`;;

let arm_XTN = define
 `arm_XTN Rd Rn esize =
    \s. let n:(128)word = read Rn (s:armstate) in
        if esize = 32 then
          let nlow:(64)word = usimd2 (\x. word_subword x (0,32): (32)word) n in
          (Rd := (word_zx nlow:(128)word)) s
        else if esize = 16 then
          let nlow:(64)word = usimd4 (\x. word_subword x (0,16): (16)word) n in
          (Rd := (word_zx nlow:(128)word)) s
        else // esize=8
          let nlow:(64)word = usimd8 (\x. word_subword x (0,8): (8)word) n in
          (Rd := (word_zx nlow:(128)word)) s`;;


let word_split_lohi = new_definition
 `(word_split_lohi:(N tybit0)word->((N)word # (N)word)) x =
    (word_subword x (0,dimindex(:N)):(N)word,
     word_subword x (dimindex(:N),dimindex(:N)):(N)word)`;;

let word_split_lo = new_definition
 `(word_split_lo:(N tybit0)word->(N)word) x =
    word_subword x (0,dimindex(:N)):(N)word`;;

let word_split_hi = new_definition
 `(word_split_hi:(N tybit0)word->(N)word) x =
    word_subword x (dimindex(:N),dimindex(:N)):(N)word`;;

(* Given x = [xlo; xhi] (LSB to MSB) and y = [ylo; yhi],
   return [xlo;ylo;xhi;yhi]. *)
let word_interleave2 = new_definition
 `(word_interleave2:(N tybit0)word->(N tybit0)word->((N tybit0)tybit0)word)
      x y =
    let xlo,xhi = word_split_lohi x in
    let ylo,yhi = word_split_lohi y in
    word_join (word_join yhi xhi:(N tybit0)word)
              (word_join ylo xlo:(N tybit0)word)`;;

(* Given x = [x0;x1;x2;x3] (LSB to MSB) and y = [y0;y1;y2;y3],
   return [x0;y0;x1;y1;x2;y2;x3;y3]. *)
let word_interleave4 = new_definition
 `(word_interleave4:((N tybit0)tybit0)word->((N tybit0)tybit0)word
      ->(((N tybit0)tybit0)tybit0)word)
      x y =
    let xlo,xhi = word_split_lohi x in
    let ylo,yhi = word_split_lohi y in
    word_join (word_interleave2 xhi yhi) (word_interleave2 xlo ylo)`;;

let word_interleave8 = new_definition
 `(word_interleave8:(((N tybit0)tybit0)tybit0)word
      ->(((N tybit0)tybit0)tybit0)word
      ->((((N tybit0)tybit0)tybit0)tybit0)word)
      x y =
    let xlo,xhi = word_split_lohi x in
    let ylo,yhi = word_split_lohi y in
    word_join (word_interleave4 xhi yhi) (word_interleave4 xlo ylo)`;;

let word_interleave16 = new_definition
 `(word_interleave16:((((N tybit0)tybit0)tybit0)tybit0)word
      ->((((N tybit0)tybit0)tybit0)tybit0)word
      ->(((((N tybit0)tybit0)tybit0)tybit0)tybit0)word)
      x y =
    let xlo,xhi = word_split_lohi x in
    let ylo,yhi = word_split_lohi y in
    word_join (word_interleave8 xhi yhi) (word_interleave8 xlo ylo)`;;

let arm_ZIP1 = new_definition
 `arm_ZIP1 Rd Rn Rm esize datasize =
    \s. let n = read Rn s in
        let m = read Rm s in
        if datasize = 128 then
          let n:(64)word = word_subword n (0,64) in
          let m:(64)word = word_subword m (0,64) in
          let d:(128)word =
            if esize = 64 then word_join m n
            else if esize = 32 then word_interleave2 n m
            else if esize = 16 then word_interleave4 n m
            else word_interleave8 n m in // esize = 8
          (Rd := d) s
        else // datasize = 64
          let n:(32)word = word_subword n (0,32) in
          let m:(32)word = word_subword m (0,32) in
          let d:(64)word =
            if esize = 32 then word_join m n:(64)word
            else if esize = 16 then word_interleave2 n m
            else word_interleave4 n m in // esize = 8
          (Rd := word_zx d:(128)word) s // overwrite high bits with zero
          `;;

let arm_ZIP2 = new_definition
 `arm_ZIP2 Rd Rn Rm esize datasize =
    \s. let n = read Rn s in
        let m = read Rm s in
        if datasize = 128 then
          let n:(64)word = word_subword n (64,64) in
          let m:(64)word = word_subword m (64,64) in
          let d:(128)word =
            if esize = 64 then word_join m n
            else if esize = 32 then word_interleave2 n m
            else if esize = 16 then word_interleave4 n m
            else word_interleave8 n m in // esize = 8
          (Rd := d) s
        else // datasize = 64
          let n:(32)word = word_subword n (32,32) in
          let m:(32)word = word_subword m (32,32) in
          let d:(64)word =
            if esize = 32 then word_join m n:(64)word
            else if esize = 16 then word_interleave2 n m
            else word_interleave4 n m in // esize = 8
          (Rd := word_zx d:(128)word) s // overwrite high bits with zero
          `;;

(* Given x = [xlo; xhi] (LSB to MSB) and y = [ylo; yhi], return [xlo;ylo]. *)

let word_interleave_lo = define
 `(word_interleave_lo:((N)tybit0)word->((N)tybit0)word->((N)tybit0)word) x y =
  word_join (word_subword y (0,dimindex(:N)):N word)
            (word_subword x (0,dimindex(:N)):N word)`;;

let word_interleave_hi = define
 `(word_interleave_hi:((N)tybit0)word->((N)tybit0)word->((N)tybit0)word) x y =
  word_join (word_subword y (dimindex(:N),dimindex(:N)):N word)
            (word_subword x (dimindex(:N),dimindex(:N)):N word)`;;

let arm_TRN1 = define
 `arm_TRN1 Rd Rn Rm esize datasize =
    \s. let n = read Rn s in
        let m = read Rm s in
        if datasize = 128 then
          let d:(128)word =
            if esize = 64 then word_interleave_lo n m
            else if esize = 32 then simd2 word_interleave_lo n m
            else if esize = 16 then simd4 word_interleave_lo n m
            else simd8 word_interleave_lo n m in
          (Rd := d) s
        else
          let n:(64)word = word_subword n (0,64) in
          let m:(64)word = word_subword m (0,64) in
          let d:(64)word =
            if esize = 32 then word_interleave_lo n m
            else if esize = 16 then simd2 word_interleave_lo n m
            else simd4 word_interleave_lo n m in
          (Rd := word_zx d:(128)word) s`;;

let arm_TRN2 = define
 `arm_TRN2 Rd Rn Rm esize datasize =
    \s. let n = read Rn s in
        let m = read Rm s in
        if datasize = 128 then
          let d:(128)word =
            if esize = 64 then word_interleave_hi n m
            else if esize = 32 then simd2 word_interleave_hi n m
            else if esize = 16 then simd4 word_interleave_hi n m
            else simd8 word_interleave_hi n m in
          (Rd := d) s
        else
          let n:(64)word = word_subword n (0,64) in
          let m:(64)word = word_subword m (0,64) in
          let d:(64)word =
            if esize = 32 then word_interleave_hi n m
            else if esize = 16 then simd2 word_interleave_hi n m
            else simd4 word_interleave_hi n m in
          (Rd := word_zx d:(128)word) s`;;

let arm_TBL = define
 `arm_TBL Rd [Rn] Rm datasize =
    \s:armstate.
        let n:int128 = read Rn s in
        let m = read Rm s in
        if datasize = 128 then
          let d = usimd16 (\x. word_subword n (8 * val x,8):byte) m in
          (Rd := d) s
        else
          let d =
             usimd8 (\x. word_subword n (8 * val x,8):byte) (word_zx m:int64) in
          (Rd := word_zx d:(128)word) s`;;

(* ------------------------------------------------------------------------- *)
(* Load and store instructions.                                              *)
(* ------------------------------------------------------------------------- *)

(*** The use of SP as a base register is special-cased because
 *** according to the architecture "when the base register is SP
 *** the stack pointer is required to be quadword (16 byte, 128 bit)
 *** aligned prior to the address calculation and write-backs ---
 *** misalignment will cause a stack alignment fault". As usual we
 *** model the "fault" with a completely undefined end state. Note
 *** that this restriction is different from 32-bit ARM: the register
 *** SP itself may for us be unaligned when not used in addressing.
 ***
 *** In the case where there is a writeback to the register being
 *** loaded/stored, the manual actually gives a more precise ramification
 *** of the undefined behavior, but we assume a worst-case completely
 *** undefined state. I am not sure if a pre/post of zero is encodable
 *** but I consider even that as a writeback.
 ***)

let arm_LDR = define
 `arm_LDR (Rt:(armstate,N word)component) Rn off =
    \s. let base = read Rn s in
        let addr = word_add base (offset_address off s) in
        (if (Rn = SP ==> aligned 16 base) /\
            (offset_writesback off ==> orthogonal_components Rt Rn)
         then
           Rt := read (memory :> wbytes addr) s ,,
           events := CONS (EventLoad (addr,dimindex (:N) DIV 8))
                          (read events s) ,,
           (if offset_writesback off
            then Rn := word_add base (offset_writeback off s)
            else (=))
         else ASSIGNS entirety) s`;;

let arm_STR = define
 `arm_STR (Rt:(armstate,N word)component) Rn off =
    \s. let base = read Rn s in
        let addr = word_add base (offset_address off s) in
        (if (Rn = SP ==> aligned 16 base) /\
            (offset_writesback off ==> orthogonal_components Rt Rn)
         then
           memory :> wbytes addr := read Rt s ,,
           events := CONS (EventStore (addr,dimindex (:N) DIV 8))
                          (read events s) ,,
           (if offset_writesback off
            then Rn := word_add base (offset_writeback off s)
            else (=))
         else ASSIGNS entirety) s`;;

let arm_LDRB = define
 `arm_LDRB (Rt:(armstate,N word)component) Rn off =
    \s. let base = read Rn s in
        let addr = word_add base (offset_address off s) in
        (if (Rn = SP ==> aligned 16 base) /\
            (offset_writesback off ==> orthogonal_components Rt Rn)
         then
           Rt := word_zx (read (memory :> bytes8 addr) s) ,,
           events := CONS (EventLoad (addr,1)) (read events s) ,,
           (if offset_writesback off
            then Rn := word_add base (offset_writeback off s)
            else (=))
         else ASSIGNS entirety) s`;;

let arm_STRB = define
 `arm_STRB (Rt:(armstate,N word)component) Rn off =
    \s. let base = read Rn s in
        let addr = word_add base (offset_address off s) in
        (if (Rn = SP ==> aligned 16 base) /\
            (offset_writesback off ==> orthogonal_components Rt Rn)
         then
           memory :> bytes8 addr := word_zx (read Rt s) ,,
           events := CONS (EventStore (addr,1)) (read events s) ,,
           (if offset_writesback off
            then Rn := word_add base (offset_writeback off s)
            else (=))
         else ASSIGNS entirety) s`;;

(*** the actually encodable offsets are a bit more limited for LDP ***)
(*** But this is all ignored at the present level and left to decoder ***)

let arm_LDP = define
 `arm_LDP (Rt1:(armstate,N word)component)
          (Rt2:(armstate,N word)component) Rn off =
    \s. let base = read Rn s in
        let addr = word_add base (offset_address off s) in
        (if (Rn = SP ==> aligned 16 base) /\
            orthogonal_components Rt1 Rt2 /\
            (offset_writesback off
             ==> orthogonal_components Rt1 Rn /\ orthogonal_components Rt2 Rn)
         then
           let w = dimindex(:N) DIV 8 in
           Rt1 := read (memory :> wbytes addr) s ,,
           Rt2 := read (memory :> wbytes(word_add addr (word w))) s ,,
           events := CONS (EventLoad (addr,2 * w)) (read events s) ,,
           (if offset_writesback off
            then Rn := word_add base (offset_writeback off s)
            else (=))
         else ASSIGNS entirety) s`;;

let arm_STP = define
 `arm_STP (Rt1:(armstate,N word)component)
          (Rt2:(armstate,N word)component) Rn off =
    \s. let base = read Rn s in
        let addr = word_add base (offset_address off s) in
        (if (Rn = SP ==> aligned 16 base) /\
            (offset_writesback off
             ==> orthogonal_components Rt1 Rn /\ orthogonal_components Rt2 Rn)
         then
           let w = dimindex(:N) DIV 8 in
           memory :> wbytes addr := read Rt1 s ,,
           memory :> wbytes(word_add addr (word w)) := read Rt2 s ,,
           events := CONS (EventStore (addr,2 * w)) (read events s) ,,
           (if offset_writesback off
            then Rn := word_add base (offset_writeback off s)
            else (=))
         else ASSIGNS entirety) s`;;

(* There is a bit of duplication in the following defintions.
  We have to do this because one step in symbolic execution
  doesn't handle let binding of pairs. *)
let word_deinterleave2_x = new_definition
  `(word_deinterleave2_x:
    ((N tybit0)tybit0)word->(N tybit0)word)
      z =
    let zlo = word_split_lo z in
    let zhi = word_split_hi z in
    let xlo = word_split_lo zlo in
    let xhi = word_split_lo zhi in
    word_join xhi xlo`;;

let word_deinterleave2_y = new_definition
  `(word_deinterleave2_y:
    ((N tybit0)tybit0)word->(N tybit0)word)
      z =
    let zlo = word_split_lo z in
    let zhi = word_split_hi z in
    let ylo = word_split_hi zlo in
    let yhi = word_split_hi zhi in
    word_join yhi ylo`;;

let word_deinterleave4_x = new_definition
  `(word_deinterleave4_x:
      (((N tybit0)tybit0)tybit0)word
      ->((N tybit0)tybit0)word)
      z =
    let zlo = word_split_lo z in
    let zhi = word_split_hi z in
    let xlo = word_deinterleave2_x zlo in
    let xhi = word_deinterleave2_x zhi in
    word_join xhi xlo`;;

let word_deinterleave4_y = new_definition
  `(word_deinterleave4_y:
      (((N tybit0)tybit0)tybit0)word
      ->((N tybit0)tybit0)word)
      z =
    let zlo = word_split_lo z in
    let zhi = word_split_hi z in
    let ylo = word_deinterleave2_y zlo in
    let yhi = word_deinterleave2_y zhi in
    word_join yhi ylo`;;

let word_deinterleave8_x = new_definition
  `(word_deinterleave8_x:
      ((((N tybit0)tybit0)tybit0)tybit0)word
      ->(((N tybit0)tybit0)tybit0)word)
      z =
    let zlo = word_split_lo z in
    let zhi = word_split_hi z in
    let xlo = word_deinterleave4_x zlo in
    let xhi = word_deinterleave4_x zhi in
    word_join xhi xlo`;;

let word_deinterleave8_y = new_definition
  `(word_deinterleave8_y:
      ((((N tybit0)tybit0)tybit0)tybit0)word
      ->(((N tybit0)tybit0)tybit0)word)
      z =
    let zlo = word_split_lo z in
    let zhi = word_split_hi z in
    let ylo = word_deinterleave4_y zlo in
    let yhi = word_deinterleave4_y zhi in
    word_join yhi ylo`;;

let word_deinterleave16_x = new_definition
  `(word_deinterleave16_x:
     (((((N tybit0)tybit0)tybit0)tybit0)tybit0)word
    ->((((N tybit0)tybit0)tybit0)tybit0)word)
      z =
    let zlo = word_split_lo z in
    let zhi = word_split_hi z in
    let xlo = word_deinterleave8_x zlo in
    let xhi = word_deinterleave8_x zhi in
    word_join xhi xlo`;;

let word_deinterleave16_y = new_definition
  `(word_deinterleave16_y:
     (((((N tybit0)tybit0)tybit0)tybit0)tybit0)word
    ->((((N tybit0)tybit0)tybit0)tybit0)word)
      z =
    let zlo = word_split_lo z in
    let zhi = word_split_hi z in
    let ylo = word_deinterleave8_y zlo in
    let yhi = word_deinterleave8_y zhi in
    word_join yhi ylo`;;

(* Association of ,, is not well understood by symbolic execution.
   So instead of doing `((a := x ,, b := y) ,, c := z) s`, we do
   `(a := x ,, b := y ,, c := z) s` *)
let arm_LD2 = define
  `arm_LD2 Rt Rtt Rn off datasize esize =
    \s. let address = read Rn s in
        let eaddr = word_add address (offset_address off s) in
        (if (Rn = SP ==> aligned 16 address) /\
            (offset_writesback off ==> orthogonal_components Rt Rn)
         then
           (if datasize = 128 then
              let tmp:(256 word) = read (memory :> wbytes eaddr) s in
              let (x:128 word) =
                if esize = 64 then word_deinterleave2_x tmp
                else if esize = 32 then word_deinterleave4_x tmp
                else if esize = 16 then word_deinterleave8_x tmp
                else word_deinterleave16_x tmp in
              let (y:128 word) =
                if esize = 64 then word_deinterleave2_y tmp
                else if esize = 32 then word_deinterleave4_y tmp
                else if esize = 16 then word_deinterleave8_y tmp
                else word_deinterleave16_y tmp in
              (Rt := x),, (Rtt := y) ,,
              events := CONS (EventLoad (eaddr,32)) (read events s) ,,
              (if offset_writesback off
               then Rn := word_add address (offset_writeback off s)
               else (=))
            else
              let tmp:(128 word) = read (memory :> wbytes eaddr) s in
              let (x:64 word) =
                if esize = 32 then word_deinterleave2_x tmp
                else if esize = 16 then word_deinterleave4_x tmp
                else word_deinterleave8_x tmp in
              let (y:64 word) =
                if esize = 32 then word_deinterleave2_y tmp
                else if esize = 16 then word_deinterleave4_y tmp
                else word_deinterleave8_y tmp in
              (Rt := word_zx x:(128)word),, (Rtt := word_zx y:(128)word) ,,
              events := CONS (EventLoad (eaddr,16)) (read events s) ,,
              (if offset_writesback off
               then Rn := word_add address (offset_writeback off s)
               else (=)))
         else ASSIGNS entirety) s`;;

let arm_ST2 = define
  `arm_ST2 Rt Rtt Rn off datasize esize =
    \s. let address = read Rn s in
        let eaddr = word_add address (offset_address off s) in
        (if (Rn = SP ==> aligned 16 address) /\
            (offset_writesback off ==> orthogonal_components Rt Rn)
         then
           let (x:128 word) = read Rt s in
           let (y:128 word) = read Rtt s in
           (if datasize = 128 then
              let (tmp:256 word) =
                if esize = 64 then word_interleave2 x y
                else if esize = 32 then word_interleave4 x y
                else if esize = 16 then word_interleave8 x y
                else word_interleave16 x y in
              memory :> wbytes eaddr := tmp
            else
              let (x:64 word) = word_subword x (0, 64) in
              let (y:64 word) = word_subword y (0, 64) in
              let (tmp:128 word) =
                if esize = 32 then word_interleave2 x y
                else if esize = 16 then word_interleave4 x y
                else word_interleave8 x y in
              memory :> wbytes eaddr := tmp) ,,
            events := CONS (EventStore (eaddr,datasize DIV 4)) (read events s) ,,
           (if offset_writesback off
            then Rn := word_add address (offset_writeback off s)
            else (=))
         else ASSIGNS entirety) s`;;

let arm_LD1R = define
  `arm_LD1R (Rt:(armstate,(128)word)component) Rn off esize datasize =
    \s. let base = read Rn s in
        let addr = word_add base (offset_address off s) in
        (if (Rn = SP ==> aligned 16 base) /\
            (offset_writesback off ==> orthogonal_components Rt Rn)
         then
           (if datasize = 128 then
              let (replicated:128 word) =
                (if esize = 64 then
                  word_duplicate ((read (memory :> wbytes addr) s):(64)word)
                else if esize = 32 then
                  word_duplicate ((read (memory :> wbytes addr) s):(32)word)
                else if esize = 16 then
                  word_duplicate ((read (memory :> wbytes addr) s):(16)word)
                else
                  word_duplicate ((read (memory :> wbytes addr) s):(8)word)) in
              (Rt := replicated)
            else
              let (replicated:64 word) =
                (if esize = 64 then read (memory :> wbytes addr) s
                else if esize = 32 then
                  word_duplicate ((read (memory :> wbytes addr) s):(32)word)
                else if esize = 16 then
                  word_duplicate ((read (memory :> wbytes addr) s):(16)word)
                else
                  word_duplicate ((read (memory :> wbytes addr) s):(8)word)) in
              (Rt := (word_zx replicated):(128)word)) ,,
            events := CONS (EventLoad (addr,esize DIV 8)) (read events s) ,,
            (if offset_writesback off
             then Rn := word_add base (offset_writeback off s)
             else (=))
         else ASSIGNS entirety) s`;;

(* ------------------------------------------------------------------------- *)
(* SHA-related SIMD operations                                               *)
(* ------------------------------------------------------------------------- *)

let arm_SHA256H = define
 `arm_SHA256H Rd Rn Rm =
    \s:armstate.
        let d = read Rd s
        and n = read Rn s
        and m = read Rm s in
        let d' = sha256h d n m in
        (Rd := d') s`;;

let arm_SHA256H2 = define
 `arm_SHA256H2 Rd Rn Rm =
    \s:armstate.
        let d = read Rd s
        and n = read Rn s
        and m = read Rm s in
        let d' = sha256h2 d n m in
        (Rd := d') s`;;

let arm_SHA256SU0 = define
 `arm_SHA256SU0 Rd Rm =
    \s:armstate.
        let d = read Rd s
        and m = read Rm s in
        let d' = sha256su0 d m in
        (Rd := d') s`;;

let arm_SHA256SU1 = define
 `arm_SHA256SU1 Rd Rn Rm =
    \s:armstate.
        let d = read Rd s
        and n = read Rn s
        and m = read Rm s in
        let d' = sha256su1 d n m in
        (Rd := d') s`;;

let arm_SHA512H = define
 `arm_SHA512H Rd Rn Rm =
    \s:armstate.
        let d = read Rd s
        and n = read Rn s
        and m = read Rm s in
        let d' = sha512h d n m in
        (Rd := d') s`;;

let arm_SHA512H2 = define
 `arm_SHA512H2 Rd Rn Rm =
    \s:armstate.
        let d = read Rd s
        and n = read Rn s
        and m = read Rm s in
        let d' = sha512h2 d n m in
        (Rd := d') s`;;

let arm_SHA512SU0 = define
 `arm_SHA512SU0 Rd Rm =
    \s:armstate.
        let d = read Rd s
        and m = read Rm s in
        let d' = sha512su0 d m in
        (Rd := d') s`;;

let arm_SHA512SU1 = define
 `arm_SHA512SU1 Rd Rn Rm =
    \s:armstate.
        let d = read Rd s
        and n = read Rn s
        and m = read Rm s in
        let d' = sha512su1 d n m in
        (Rd := d') s`;;

let arm_RAX1 = define
 `arm_RAX1 Rd Rn Rm =
    \s:armstate.
      let n:int128 = read Rn s
      and m:int128 = read Rm s in
      let hi:int64 = word_subword m (64,64)
      and lo:int64 = word_subword m (0,64) in
      let d' = word_xor n (word_join (word_rol hi 1) (word_rol lo 1)) in
      (Rd := d') s`;;

(* ------------------------------------------------------------------------- *)
(* Cryptographic four-register                                               *)
(* ------------------------------------------------------------------------- *)

let arm_EOR3 = define
 `arm_EOR3 Rd Rn Rm Ra =
    \s:armstate.
      let n:int128 = read Rn s
      and m:int128 = read Rm s
      and a:int128 = read Ra s in
      let d':int128 = word_xor (word_xor n m) a in
      (Rd := d') s`;;

let arm_BCAX = define
 `arm_BCAX Rd Rn Rm Ra =
    \s:armstate.
      let n:int128 = read Rn s
      and m:int128 = read Rm s
      and a:int128 = read Ra s in
      let d':int128 = word_xor n (word_and m (word_not a)) in
      (Rd := d') s`;;


(* ------------------------------------------------------------------------- *)
(* Cryptographic AES                                                         *)
(* ------------------------------------------------------------------------- *)
let arm_AESE = define
 `arm_AESE Rd Rn =
    \s:armstate.
        let d = read Rd s
        and n = read Rn s in
        let d' = aese d n in
        (Rd := d') s`;;

let arm_AESMC = define
 `arm_AESMC Rd Rn =
    \s:armstate.
        let n = read Rn s in
        let d' = aesmc n in
        (Rd := d') s`;;

let arm_AESD = define
  `arm_AESD Rd Rn =
     \s:armstate.
       let d = read Rd s
       and n = read Rn s in
       let d' = aesd d n in
       (Rd := d') s`;;

let arm_AESIMC = define
  `arm_AESIMC Rd Rn =
     \s:armstate.
       let n = read Rn s in
       let d' = aesimc n in
       (Rd := d') s`;;

(* ------------------------------------------------------------------------- *)
(* XAR : Exclusive-OR and Rotate                                             *)
(* ------------------------------------------------------------------------- *)

let arm_XAR = define
  `arm_XAR Rd Rn Rm imm6 =
    \s:armstate.
      let n:int128 = read Rn s
      and m:int128 = read Rm s in
      let tmp:int128 = word_xor n m in
      let hi:int64 = word_subword tmp (64,64)
      and lo:int64 = word_subword tmp (0,64) in
      let d':int128 = word_join (word_ror hi (val imm6)) (word_ror lo (val imm6)) in
      (Rd := d') s`;;

(* ------------------------------------------------------------------------- *)
(* Pseudo-instructions that are defined by ARM as aliases.                   *)
(* ------------------------------------------------------------------------- *)

let arm_BEQ = define `arm_BEQ = arm_Bcond Condition_EQ`;;
let arm_BNE = define `arm_BNE = arm_Bcond Condition_NE`;;
let arm_BCS = define `arm_BCS = arm_Bcond Condition_CS`;;
let arm_BHS = define `arm_BHS = arm_Bcond Condition_HS`;;
let arm_BCC = define `arm_BCC = arm_Bcond Condition_CC`;;
let arm_BLO = define `arm_BLO = arm_Bcond Condition_LO`;;
let arm_BMI = define `arm_BMI = arm_Bcond Condition_MI`;;
let arm_BPL = define `arm_BPL = arm_Bcond Condition_PL`;;
let arm_BVS = define `arm_BVS = arm_Bcond Condition_VS`;;
let arm_BVC = define `arm_BVC = arm_Bcond Condition_VC`;;
let arm_BHI = define `arm_BHI = arm_Bcond Condition_HI`;;
let arm_BLS = define `arm_BLS = arm_Bcond Condition_LS`;;
let arm_BGE = define `arm_BGE = arm_Bcond Condition_GE`;;
let arm_BLT = define `arm_BLT = arm_Bcond Condition_LT`;;
let arm_BGT = define `arm_BGT = arm_Bcond Condition_GT`;;
let arm_BLE = define `arm_BLE = arm_Bcond Condition_LE`;;
let arm_BAL = define `arm_BAL = arm_Bcond Condition_AL`;;
let arm_BNV = define `arm_BNV = arm_Bcond Condition_NV`;;

let arm_CINC = define
 `arm_CINC Rd Rn cc = arm_CSINC Rd Rn Rn (invert_condition cc)`;;

let arm_CINV = define
 `arm_CINV Rd Rn cc = arm_CSINV Rd Rn Rn (invert_condition cc)`;;

let arm_CNEG = define
 `arm_CNEG Rd Rn cc = arm_CSNEG Rd Rn Rn (invert_condition cc)`;;

let arm_CMN = define `arm_CMN Rm Rn = arm_ADDS ZR Rm Rn`;;
let arm_CMP = define `arm_CMP Rm Rn = arm_SUBS ZR Rm Rn`;;

let arm_CSET = define
  `arm_CSET Rd cc = arm_CSINC Rd ZR ZR (invert_condition cc)`;;

let arm_CSETM = define
  `arm_CSETM Rd cc = arm_CSINV Rd ZR ZR (invert_condition cc)`;;

let arm_MOV = define `arm_MOV Rd Rm = arm_ORR Rd ZR Rm`;;
let arm_MOV_VEC = define
 `arm_MOV_VEC Rd Rn datasize = arm_ORR_VEC Rd Rn Rn datasize`;;

let arm_MNEG = define `arm_MNEG Rd Rn Rm = arm_MSUB Rd Rn Rm ZR`;;
let arm_MUL = define `arm_MUL Rd Rn Rm = arm_MADD Rd Rn Rm ZR`;;

let arm_MVN = define `arm_MVN Rd Rm = arm_ORN Rd ZR Rm`;;

let arm_NEG = define `arm_NEG Rd Rm = arm_SUB Rd ZR Rm`;;
let arm_NEGS = define `arm_NEGS Rd Rm = arm_SUBS Rd ZR Rm`;;

let arm_NGC = define `arm_NGC Rd Rm = arm_SBC Rd ZR Rm`;;
let arm_NGCS = define `arm_NGCS Rd Rm = arm_SBCS Rd ZR Rm`;;

let arm_ROR = define `arm_ROR Rd Rs lsb = arm_EXTR Rd Rs Rs lsb`;;

let arm_TST = define `arm_TST Rm Rn = arm_ANDS ZR Rm Rn`;;

let arm_UMNEGL = define `arm_UMNEGL Rd Rn Rm = arm_UMSUBL Rd Rn Rm XZR`;;
let arm_UMULL = define `arm_UMULL Rd Rn Rm = arm_UMADDL Rd Rn Rm XZR`;;

let ARM_INSTRUCTION_ALIASES =
 [arm_BEQ; arm_BNE; arm_BCS; arm_BHS; arm_BCC;
  arm_BLO; arm_BMI; arm_BPL; arm_BVS; arm_BVC;
  arm_BHI; arm_BLS; arm_BGE; arm_BLT; arm_BGT;
  arm_BLE; arm_BAL; arm_BNV; arm_CINC; arm_CINV;
  arm_CNEG; arm_CMN; arm_CMP;arm_CSET; arm_CSETM;
  arm_MOV; arm_MOV_VEC;
  arm_MNEG; arm_MUL; arm_MVN; arm_NEG;
  arm_NEGS; arm_NGC; arm_NGCS; arm_ROR; arm_TST;
  arm_UMNEGL; arm_UMULL];;

(* ------------------------------------------------------------------------- *)
(* These three are treated by ARM as aliases, but since they are such        *)
(* natural top-level operations we define them a priori then prove           *)
(* they are equivalent to their xBFM instances given some sideconditions.    *)
(* The decoder will return them directly instead of expanding to SBFM/UBFM.  *)
(*                                                                           *)
(* Note that you can't actually encode a left shift by zero bits; it         *)
(* is instead interpreted as a right shift by zero bits. However the alias   *)
(* arm_LSL with a zero shift does in fact mean the same thing anyway.        *)
(* ------------------------------------------------------------------------- *)

let arm_ASR = define
 `arm_ASR Rd Rn imm =
    \s. let x:N word = read Rn (s:armstate) in
        let y = word_ishr x imm in
        (Rd := y) s`;;

let arm_LSL = define
 `arm_LSL Rd Rn imm =
        \s. let x:N word = read Rn (s:armstate) in
            let y = word_shl x imm in
            (Rd := y) s`;;

let arm_LSR = define
 `arm_LSR Rd Rn imm =
       \s. let x:N word = read Rn (s:armstate) in
           let y = word_ushr x imm in
           (Rd := y) s`;;

let arm_ASR_ALIAS = prove
 (`immr < dimindex(:N) /\ imms = dimindex(:N) - 1
   ==> arm_SBFM (Rd:(armstate,N word)component) Rn immr imms =
       arm_ASR Rd Rn immr`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  X_GEN_TAC `s:armstate` THEN ASM_REWRITE_TAC[arm_ASR; arm_SBFM] THEN
  LET_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[ARITH_RULE `r < n ==> n - 1 >= r`] THEN
  REWRITE_TAC[word_sxfrom] THEN
  ASM_SIMP_TAC[ARITH_RULE `r < n ==> n - 1 - (n - 1 - r) = r`] THEN
  SIMP_TAC[WORD_EQ_BITS_ALT; BIT_WORD_ISHR; BIT_WORD_SHL;
           BIT_WORD_SUBWORD] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  ASM_SIMP_TAC[ARITH_RULE `r < n ==> r + n - 1 - r = n - 1`] THEN
  REWRITE_TAC[ARITH_RULE `r + (i + r) - r:num = i + r`] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let arm_LSL_ALIAS = prove
 (`immr < dimindex(:N) /\ imms + 1 = immr
   ==> arm_UBFM (Rd:(armstate,N word)component) Rn immr imms =
       arm_LSL Rd Rn (dimindex(:N) - immr)`,
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
  GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  X_GEN_TAC `s:armstate` THEN ASM_REWRITE_TAC[arm_LSL; arm_UBFM] THEN
  LET_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[ARITH_RULE `~(s >= s + 1)`] THEN
  ASM_SIMP_TAC[MOD_CASES; DIMINDEX_GE_1; ARITH_RULE `1 <= n ==> n - d < 2 * n`;
               ARITH_RULE `1 <= n ==> (n - d < n <=> ~(d = 0))`] THEN
  SIMP_TAC[COND_SWAP; SUB_0; SUB_REFL; GE] THEN
  ASM_CASES_TAC `imm = 0` THEN
  ASM_SIMP_TAC[LE_0; SUB_0; SUB_ADD; DIMINDEX_GE_1; GSYM WORD_ZX_SUBWORD;
               WORD_ZX_TRIVIAL; WORD_SHL_ZERO] THEN
  ASM_SIMP_TAC[ARITH_RULE `d < n ==> ~(n - d <= n - 1 - d)`] THEN
  ASM_SIMP_TAC[ARITH_RULE `d:num < n ==> n - (n - d) = d`] THEN
  ASM_SIMP_TAC[ARITH_RULE `d < n ==> n - 1 - d + 1 = n - d`] THEN
  MATCH_MP_TAC WORD_SHL_SUBWORD THEN ARITH_TAC);;

let arm_LSR_ALIAS = prove
 (`immr < dimindex(:N) /\ imms = dimindex(:N) - 1
   ==> arm_UBFM (Rd:(armstate,N word)component) Rn immr imms =
       arm_LSR Rd Rn immr`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  X_GEN_TAC `s:armstate` THEN ASM_REWRITE_TAC[arm_LSR; arm_UBFM] THEN
  LET_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[ARITH_RULE `d < n ==> n - 1 >= d`] THEN
  ASM_SIMP_TAC[ARITH_RULE `d < n ==> n - 1 - d + 1 = n - d`] THEN
  REWRITE_TAC[WORD_USHR_AS_SUBWORD]);;

(* ------------------------------------------------------------------------- *)
(* The ROR alias does amount to the same thing as the word_ror operation.    *)
(* ------------------------------------------------------------------------- *)

let arm_ROR_ALT = prove
 (`arm_ROR Rd Rs lsb =
    \s:armstate. (Rd := word_ror (read Rs s) lsb) s`,
  GEN_REWRITE_TAC I [FUN_EQ_THM] THEN X_GEN_TAC `s:armstate` THEN
  REWRITE_TAC[arm_ROR; arm_EXTR] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ONCE_REWRITE_TAC[WORD_ROR_MOD] THEN
  SIMP_TAC[WORD_SUBWORD_JOIN_SELF; LE_REFL; LT_IMP_LE; MOD_LT_EQ;
           DIMINDEX_NONZERO]);;

(* ------------------------------------------------------------------------- *)
(* The conditional comparison instructions expressed in another way.         *)
(* ------------------------------------------------------------------------- *)

let arm_CCMN_ALT = prove
 (`arm_CCMN Rm Rn nzcv cc s =
   if condition_semantics cc s then arm_CMN Rm Rn s else (flags := nzcv) s`,
  REWRITE_TAC[arm_CCMN; arm_CMN; arm_ADDS] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARM_ZERO_REGISTER; WRITE_RVALUE; seq; assign; UNWIND_THM1] THEN
  ABS_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  SPEC_TAC(`s:armstate`,`s:armstate`) THEN MATCH_MP_TAC armstate_INDUCT THEN
  REWRITE_TAC[NF; ZF; CF; VF; WRITE_COMPONENT_COMPOSE] THEN
  REWRITE_TAC[armstate_COMPONENTS] THEN
  REPEAT GEN_TAC THEN REPEAT(AP_TERM_TAC ORELSE AP_THM_TAC) THEN
  GEN_REWRITE_TAC I [WORD_EQ_BITS_ALT] THEN
  REWRITE_TAC[GSYM READ_BITELEMENT; READ_WRITE_BITELEMENT_GEN; DIMINDEX_4] THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV);;

let arm_CCMP_ALT = prove
 (`arm_CCMP Rm Rn nzcv cc s =
   if condition_semantics cc s then arm_CMP Rm Rn s else (flags := nzcv) s`,
  REWRITE_TAC[arm_CCMP; arm_CMP; arm_SUBS] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARM_ZERO_REGISTER; WRITE_RVALUE; seq; assign; UNWIND_THM1] THEN
  ABS_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  SPEC_TAC(`s:armstate`,`s:armstate`) THEN MATCH_MP_TAC armstate_INDUCT THEN
  REWRITE_TAC[NF; ZF; CF; VF; WRITE_COMPONENT_COMPOSE] THEN
  REWRITE_TAC[armstate_COMPONENTS] THEN
  REPEAT GEN_TAC THEN REPEAT(AP_TERM_TAC ORELSE AP_THM_TAC) THEN
  GEN_REWRITE_TAC I [WORD_EQ_BITS_ALT] THEN
  REWRITE_TAC[GSYM READ_BITELEMENT; READ_WRITE_BITELEMENT_GEN; DIMINDEX_4] THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* Not true aliases, but this actually reflects how the ARM manual does      *)
(* it. I guess this inverted carry trick goes back to the System/360 if not  *)
(* before, and was also the way to do subtraction with borrow on the 6502.   *)
(* http://www.righto.com/2012/12/the-6502-overflow-flag-explained.html       *)
(* The same thing for SUBS and SUBS but they don't naturally look as tidy.   *)
(* ------------------------------------------------------------------------- *)

let ARM_SBC_ALT = prove
 (`!Rd Rm Rn:(armstate,N word)component.
        arm_SBC Rd Rm Rn = arm_ADC Rd Rm (Rn :> evaluate word_not)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  X_GEN_TAC `s:armstate` THEN REWRITE_TAC[] THEN
  REWRITE_TAC[arm_ADC; arm_SBC; READ_COMPONENT_COMPOSE] THEN
  REWRITE_TAC[READ_WRITE_EVALUATE] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[WORD_BITVAL_NOT] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

let ARM_SBCS_ALT = prove
 (`!Rd Rm Rn:(armstate,N word)component.
        arm_SBCS Rd Rm Rn = arm_ADCS Rd Rm (Rn :> evaluate word_not)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  X_GEN_TAC `s:armstate` THEN REWRITE_TAC[] THEN
  REWRITE_TAC[arm_ADCS; arm_SBCS; READ_COMPONENT_COMPOSE] THEN
  REWRITE_TAC[READ_WRITE_EVALUATE] THEN
  MAP_EVERY ABBREV_TAC
   [`x = read (Rm:(armstate,N word)component) s`;
    `y = read (Rn:(armstate,N word)component) s`;
    `c = read CF s`] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[NOCARRY_WORD_SBB; CARRY_WORD_ADC] THEN
  REWRITE_TAC[IVAL_WORD_NOT; VAL_WORD_NOT; INT_BITVAL_NOT] THEN
  REWRITE_TAC[WORD_BITVAL_NOT; WORD_NOT_AS_SUB] THEN
  REWRITE_TAC[WORD_RULE
   `word_add (word_add x (word_sub (word_neg y) d)) c =
    word_sub x (word_add y (word_sub d c))`] THEN
  REWRITE_TAC[GSYM WORD_BITVAL_NOT] THEN AP_THM_TAC THEN
  REPLICATE_TAC 3 AP_TERM_TAC THEN REWRITE_TAC[INT_ARITH
   `x + --(y + &1) + c:int = x - (y + &1 - c)`] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  BOOL_CASES_TAC `c:bool` THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  MP_TAC(ISPEC `x:N word` VAL_BOUND) THEN
  MP_TAC(ISPEC `y:N word` VAL_BOUND) THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* An integer-style variant more analogous to arm_MSUB                       *)
(* ------------------------------------------------------------------------- *)

let ARM_MADD_ALT = prove
 (`!Rd Rm Rn Ra:(armstate,N word)component.
        arm_MADD Rd Rn Rm Ra =
        \s. let n:N word = read Rn s
            and m:N word = read Rm s
            and a:N word = read Ra s in
            let d:N word = iword(ival a + ival n * ival m) in
            (Rd := d) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[arm_MADD; WORD_IWORD] THEN
  ABS_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[IWORD_EQ; GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_MUL] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `(a:int == a') (mod x) /\ (n == n') (mod x) /\ (m == m') (mod x)
    ==> (a' + n' * m' == a + n * m) (mod x)`) THEN
  REWRITE_TAC[IVAL_VAL_CONG]);;

(* ------------------------------------------------------------------------- *)
(* Alternatives with more convenient carry propagation predicates.           *)
(* ------------------------------------------------------------------------- *)

let arm_ADCS_ALT = prove
 (`arm_ADCS Rd Rm Rn =
    \s. let m = read Rm s
        and n = read Rn s
        and c = bitval(read CF s) in
        let d:int64 = word_add (word_add m n) (word c) in
        (Rd := d ,,
         NF := (ival d < &0) ,,
         ZF := (val d = 0) ,,
         CF := (2 EXP 64 <= val m + val n + c) ,,
         VF := ~(ival m + ival n + &c = ival d)) s`,
  REWRITE_TAC[arm_ADCS] THEN ABS_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[CARRY64_ADC]);;

let arm_ADDS_ALT = prove
 (`arm_ADDS Rd Rm Rn =
    \s. let m = read Rm s
        and n = read Rn s in
        let d:int64 = word_add m n in
        (Rd := d ,,
         NF := (ival d < &0) ,,
         ZF := (val d = 0) ,,
         CF := (2 EXP 64 <= val m + val n) ,,
         VF := ~(ival m + ival n = ival d)) s`,
  REWRITE_TAC[arm_ADDS] THEN ABS_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[CARRY64_ADD]);;

let arm_SBCS_ALT = prove
 (`arm_SBCS Rd Rm Rn =
    \s. let m = read Rm s
        and n = read Rn s
        and c = bitval(~read CF s) in
        let d:int64 = word_sub m (word_add n (word c)) in
        (Rd := d ,,
         NF := (ival d < &0) ,,
         ZF := (val d = 0) ,,
         CF := ~(val m < val n + c) ,,
         VF := ~(ival m - (ival n + &c) = ival d)) s`,
  REWRITE_TAC[arm_SBCS] THEN ABS_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[NOCARRY64_SBB; NOT_LT]);;

let arm_SUBS_ALT = prove
 (`arm_SUBS Rd Rm Rn =
    \s. let m = read Rm s
        and n = read Rn s in
        let d:int64 = word_sub m n in
        (Rd := d ,,
         NF := (ival d < &0) ,,
         ZF := (val d = 0) ,,
         CF := ~(val m < val n) ,,
         VF := ~(ival m - ival n = ival d)) s`,
  REWRITE_TAC[arm_SUBS] THEN ABS_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[NOCARRY64_SUB; NOT_LT]);;

let arm_CBNZ_ALT = prove
 (`arm_CBNZ Rt (off:21 word) =
        \s. let pc_next = if ~(val(read Rt s) = 0)
                   then word_add (word_sub (read PC s) (word 4)) (word_sx off)
                   else read PC s in
            (PC := pc_next ,,
             events := CONS (EventJump
                (word_sub (read PC s) (word 4),pc_next))
                (read events s)) s`,
  REWRITE_TAC[VAL_EQ_0; arm_CBNZ] THEN
  CONV_TAC (DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[]);;

let arm_CBZ_ALT = prove
 (`arm_CBZ Rt (off:21 word) =
        \s. let pc_next = if val(read Rt s) = 0
                   then word_add (word_sub (read PC s) (word 4)) (word_sx off)
                   else read PC s in
            (PC := pc_next ,,
             events := CONS (EventJump
                (word_sub (read PC s) (word 4),pc_next))
                (read events s)) s`,
  REWRITE_TAC[VAL_EQ_0; arm_CBZ] THEN
  CONV_TAC (DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* MOV is an alias of MOVZ when Rm is an immediate                           *)
(* ------------------------------------------------------------------------- *)

let arm_MOVZ_ALT = prove (`imm < 65536 ==>
   arm_MOV Rd (rvalue (word imm:N word)) = arm_MOVZ Rd (word imm) 0`,
  REWRITE_TAC [arm_MOVZ; arm_ORR; arm_MOV; ZR; rvalue; read] THEN
  CONV_TAC (DEPTH_CONV let_CONV) THEN
  REWRITE_TAC [WORD_OR_0; EXP; MULT_CLAUSES; WORD_VAL; ETA_AX] THEN
  DISCH_THEN (fun th -> IMP_REWRITE_TAC [VAL_WORD_EQ; DIMINDEX_16] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ACCEPT_TAC th));;

let arm_MOVK_ALT =
  REWRITE_RULE[assign; WRITE_COMPONENT_COMPOSE; read; write; subword]
    arm_MOVK;;

(* ------------------------------------------------------------------------- *)
(* Alternative definitions of NEON instructions that unfold simdN/usimdN.    *)
(* ------------------------------------------------------------------------- *)

(*** Compatibility with earlier definition ***)

let WORD_DUPLICATE_64_128 = prove
 (`(word_duplicate:int64->int128) x = word_join x x`,
  ONCE_REWRITE_TAC[GSYM WORD_DUPLICATE_DOUBLE] THEN
  REWRITE_TAC[WORD_DUPLICATE_REFL]);;

let all_simd_rules =
   [usimd16;usimd8;usimd4;usimd2;simd16;simd8;simd4;simd2;
    o_THM; masking;
    WORD_DUPLICATE_64_128;
    word_interleave16;
    word_interleave8;word_interleave4;word_interleave2;word_split_lohi;
    word_interleave_lo; word_interleave_hi;
    word_split_hi; word_split_lo;
    word_deinterleave2_x; word_deinterleave2_y;
    word_deinterleave4_x; word_deinterleave4_y;
    word_deinterleave8_x; word_deinterleave8_y;
    word_deinterleave16_x; word_deinterleave16_y];;

let EXPAND_SIMD_RULE =
  CONV_RULE (TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) o
  CONV_RULE (DEPTH_CONV DIMINDEX_CONV) o REWRITE_RULE all_simd_rules;;

let arm_ADD_VEC_ALT =    EXPAND_SIMD_RULE arm_ADD_VEC;;
let arm_CMHI_VEC_ALT =   EXPAND_SIMD_RULE arm_CMHI_VEC;;
let arm_CNT_ALT =        EXPAND_SIMD_RULE arm_CNT;;
let arm_DUP_GEN_ALT =    EXPAND_SIMD_RULE arm_DUP_GEN;;
let arm_MLS_VEC_ALT =    EXPAND_SIMD_RULE arm_MLS_VEC;;
let arm_MUL_VEC_ALT =    EXPAND_SIMD_RULE arm_MUL_VEC;;
let arm_REV64_VEC_ALT =  EXPAND_SIMD_RULE arm_REV64_VEC;;
let arm_SHL_VEC_ALT =    EXPAND_SIMD_RULE arm_SHL_VEC;;
let arm_SSHR_VEC_ALT =   EXPAND_SIMD_RULE arm_SSHR_VEC;;
let arm_SHRN_ALT =       EXPAND_SIMD_RULE arm_SHRN;;
let arm_SLI_VEC_ALT =    EXPAND_SIMD_RULE arm_SLI_VEC;;
let arm_SMLAL_VEC_ALT =  EXPAND_SIMD_RULE arm_SMLAL_VEC;;
let arm_SMLAL2_VEC_ALT = EXPAND_SIMD_RULE arm_SMLAL2_VEC;;
let arm_SMLSL_VEC_ALT =  EXPAND_SIMD_RULE arm_SMLSL_VEC;;
let arm_SMLSL2_VEC_ALT = EXPAND_SIMD_RULE arm_SMLSL2_VEC;;
let arm_SMULL_VEC_ALT =  EXPAND_SIMD_RULE arm_SMULL_VEC;;
let arm_SMULL2_VEC_ALT = EXPAND_SIMD_RULE arm_SMULL2_VEC;;
let arm_SRI_VEC_ALT =    EXPAND_SIMD_RULE arm_SRI_VEC;;
let arm_SUB_VEC_ALT =    EXPAND_SIMD_RULE arm_SUB_VEC;;
let arm_TBL_ALT =        EXPAND_SIMD_RULE arm_TBL;;
let arm_TRN1_ALT =       EXPAND_SIMD_RULE arm_TRN1;;
let arm_TRN2_ALT =       EXPAND_SIMD_RULE arm_TRN2;;
let arm_UADDLP_ALT =     EXPAND_SIMD_RULE arm_UADDLP;;
let arm_UMLAL_VEC_ALT =  EXPAND_SIMD_RULE arm_UMLAL_VEC;;
let arm_UMLAL2_VEC_ALT = EXPAND_SIMD_RULE arm_UMLAL2_VEC;;
let arm_UMLSL_VEC_ALT =  EXPAND_SIMD_RULE arm_UMLSL_VEC;;
let arm_UMLSL2_VEC_ALT = EXPAND_SIMD_RULE arm_UMLSL2_VEC;;
let arm_UMULL_VEC_ALT =  EXPAND_SIMD_RULE arm_UMULL_VEC;;
let arm_UMULL2_VEC_ALT = EXPAND_SIMD_RULE arm_UMULL2_VEC;;
let arm_USHR_VEC_ALT =   EXPAND_SIMD_RULE arm_USHR_VEC;;
let arm_USRA_VEC_ALT =   EXPAND_SIMD_RULE arm_USRA_VEC;;
let arm_UZP1_ALT =       EXPAND_SIMD_RULE arm_UZP1;;
let arm_UZP2_ALT =       EXPAND_SIMD_RULE arm_UZP2;;
let arm_XTN_ALT =        EXPAND_SIMD_RULE arm_XTN;;
let arm_ZIP1_ALT =       EXPAND_SIMD_RULE arm_ZIP1;;
let arm_ZIP2_ALT =       EXPAND_SIMD_RULE arm_ZIP2;;
let arm_LD2_ALT =        EXPAND_SIMD_RULE arm_LD2;;
let arm_ST2_ALT =        EXPAND_SIMD_RULE arm_ST2;;

let arm_SQDMULH_VEC_ALT =
  REWRITE_RULE[word_2smulh] (EXPAND_SIMD_RULE arm_SQDMULH_VEC);;

let arm_SQRDMULH_VEC_ALT =
  REWRITE_RULE[word_2smulh_round] (EXPAND_SIMD_RULE arm_SQRDMULH_VEC);;

let arm_SRSHR_VEC_ALT =
  REWRITE_RULE[word_ishr_round] (EXPAND_SIMD_RULE arm_SRSHR_VEC);;

let arm_UADDLV_ALT =
  (end_itlist CONJ o
   map (REWRITE_RULE[WORD_ADD; WORD_VAL] o
        CONV_RULE(TOP_DEPTH_CONV let_CONV) o
        CONV_RULE
         (NUM_REDUCE_CONV THENC
          ONCE_DEPTH_CONV EXPAND_NSUM_CONV THENC
          NUM_REDUCE_CONV) o
        GEN_REWRITE_CONV I [arm_UADDLV]))
  [`arm_UADDLV Rd Rn 8 8`;
   `arm_UADDLV Rd Rn 16 8`;
   `arm_UADDLV Rd Rn 4 16`;
   `arm_UADDLV Rd Rn 8 16`;
   `arm_UADDLV Rd Rn 4 32`];;

(* ------------------------------------------------------------------------- *)
(* Collection of standard forms of non-aliased instructions                  *)
(* We separate the load/store instructions for a different treatment.        *)
(* ------------------------------------------------------------------------- *)

let ARM_OPERATION_CLAUSES =
  map (CONV_RULE(TOP_DEPTH_CONV let_CONV) o SPEC_ALL)
    (*** Alphabetically sorted, new alphabet appears in the next line ***)
      [arm_ADC; arm_ADCS_ALT; arm_ADD; arm_ADD_VEC_ALT; arm_ADDS_ALT; arm_ADR;
       arm_ADRP; arm_AND; arm_AND_VEC; arm_ANDS; arm_ASR; arm_ASRV;
       arm_B; arm_BCAX; arm_BFM; arm_BIC; arm_BIC_VEC; arm_BICS; arm_BIT;
       arm_BL; arm_BL_ABSOLUTE; arm_Bcond;
       arm_CBNZ_ALT; arm_CBZ_ALT; arm_CCMN; arm_CCMP; arm_CLZ;
       arm_CMHI_VEC_ALT; arm_CNT_ALT;
       arm_CSEL; arm_CSINC; arm_CSINV; arm_CSNEG;
       arm_DUP_GEN_ALT;
       arm_EON; arm_EOR; arm_EOR_VEC; arm_EOR3; arm_EXT; arm_EXTR;
       arm_FCSEL; arm_FMOV_FtoI; arm_FMOV_ItoF; arm_INS; arm_INS_GEN;
       arm_LSL; arm_LSLV; arm_LSR; arm_LSRV;
       arm_MADD;
       arm_MLS_VEC_ALT;
       arm_MOVI; arm_MOVK_ALT; arm_MOVN; arm_MOVZ; arm_MSUB;
       arm_MUL_VEC_ALT;
       arm_NOP;
       arm_ORN; arm_ORR; arm_ORR_VEC;
       arm_RET; arm_REV64_VEC_ALT; arm_RORV;
       arm_SBC; arm_SBCS_ALT; arm_SBFM; arm_SHL_VEC_ALT; arm_SHRN_ALT;
       arm_SRSHR_VEC_ALT;
       arm_SSHR_VEC_ALT;
       arm_SLI_VEC_ALT; arm_SRI_VEC_ALT;
       arm_SMLAL_VEC_ALT; arm_SMLAL2_VEC_ALT;
       arm_SMLSL_VEC_ALT; arm_SMLSL2_VEC_ALT;
       arm_SMULL_VEC_ALT; arm_SMULL2_VEC_ALT;
       arm_SMULH;
       arm_SQDMULH_VEC_ALT;
       arm_SQRDMULH_VEC_ALT;
       arm_SUB; arm_SUB_VEC_ALT; arm_SUBS_ALT;
       arm_TBL_ALT;
       arm_TRN1_ALT; arm_TRN2_ALT;
       arm_UADDLP_ALT; arm_UADDLV_ALT; arm_UBFM; arm_UMOV; arm_UMADDL;
       arm_UMLAL_VEC_ALT; arm_UMLAL2_VEC_ALT;
       arm_UMLSL_VEC_ALT; arm_UMLSL2_VEC_ALT;
       arm_UMSUBL;
       arm_UMULL_VEC_ALT; arm_UMULL2_VEC_ALT;
       arm_UMULH;
       arm_USHR_VEC_ALT; arm_USRA_VEC_ALT; arm_UZP1_ALT;
       arm_UZP2_ALT;
       arm_XAR; arm_XTN_ALT;
       arm_ZIP1_ALT; arm_ZIP2_ALT;
    (*** 32-bit backups since the ALT forms are 64-bit only ***)
       INST_TYPE[`:32`,`:N`] arm_ADCS;
       INST_TYPE[`:32`,`:N`] arm_ADDS;
       INST_TYPE[`:32`,`:N`] arm_SBCS;
       INST_TYPE[`:32`,`:N`] arm_SUBS;
    (*** AES instructions ***)
       arm_AESE;
       arm_AESMC;
       arm_AESD;
       arm_AESIMC;
    (*** SHA256 & SHA512 instructions from Carl Kwan ***)
       arm_RAX1;
       arm_SHA256H;
       arm_SHA256H2;
       arm_SHA256SU0;
       arm_SHA256SU1;
       arm_SHA512H;
       arm_SHA512H2;
       arm_SHA512SU0;
       arm_SHA512SU1 ];;

let ARM_LOAD_STORE_CLAUSES =
  map (CONV_RULE(TOP_DEPTH_CONV let_CONV) o SPEC_ALL)
      [arm_LDR; arm_STR; arm_LDRB; arm_STRB; arm_LDP; arm_STP;
       arm_LD2_ALT; arm_ST2_ALT; arm_LD1R];;
