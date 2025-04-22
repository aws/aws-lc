(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Simplified model of x86 semantics.                                        *)
(* ========================================================================= *)

let x86_print_log = ref false;;

(* ------------------------------------------------------------------------- *)
(* Size in bits corresponding to the tags.                                   *)
(* ------------------------------------------------------------------------- *)

let bytesize = define
 `bytesize Byte = 8 /\
  bytesize Word = 16 /\
  bytesize Doubleword = 32 /\
  bytesize Quadword = 64`;;

let regsize = define
 `regsize Full_64 = 64 /\
  regsize Lower_32 = 32 /\
  regsize Lower_16 = 16 /\
  regsize Upper_8 = 8 /\
  regsize Lower_8 = 8`;;

let simdregsize = define
 `simdregsize Full_512 = 512 /\
  simdregsize Lower_256 = 256 /\
  simdregsize Lower_128 = 128`;;

let register_size = define
 `register_size (Gpr n w) = regsize w`;;

let simdregister_size = define
 `simdregister_size (Simdreg n w) = simdregsize w`;;

let operand_size = define
 `operand_size (Register r) = register_size r /\
  operand_size (Simdregister s) = simdregister_size s /\
  operand_size (Imm8 i8) = 8 /\
  operand_size (Imm16 i16) = 16 /\
  operand_size (Imm32 i32) = 32 /\
  operand_size (Imm64 i64) = 64 /\
  operand_size (Memop w b) = bytesize w`;;

(* ------------------------------------------------------------------------- *)
(* The semantics.                                                            *)
(* ------------------------------------------------------------------------- *)

(*** Note: we currently treat memory as a full 64-bit address space.
 *** In current processors, especially AMD, there are some canonicality
 *** assumptions (address must be sign-extended 48 bit value, i.e. the
 *** top 16 bits must be all 0s or all 1s). We can add those later when
 *** considering general memory protection properly.
 ***)

let x86state_INDUCT,x86state_RECURSION,x86state_COMPONENTS =
  define_auto_record_type
   "x86state =
     { RIP : int64;                       // instruction pointer (RIP)
       registers : (4)word -> (64)word;   // 2^4=16 GP registers, 64 bits each
       simdregisters: (5)word->(512)word; // 2^5=32 ZMM registers, 512 bits each
       maskregisters: (3)word->(64)word;  // 2^3=8 opmasks, can be up to 64-bit
       rflags : int64;                    // rflags register (top 32 reserved)
       memory : int64 -> byte             // Memory
     }";;

let FORALL_X86STATE = prove
 (`!P. (!i r z k f m. P(x86state_RECORD i r z k f m)) <=> (!s. P s)`,
  GEN_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN
  REWRITE_TAC[x86state_INDUCT]);;

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

let BYTES_LOADED_BUTLAST = prove
 (`!s pc l. bytes_loaded s pc l ==> bytes_loaded s pc (BUTLAST l)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `l:byte list = []` THEN ASM_REWRITE_TAC[BUTLAST] THEN
  FIRST_X_ASSUM(fun th ->
   GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
     [SYM(MATCH_MP APPEND_BUTLAST_LAST th)]) THEN
  SIMP_TAC[bytes_loaded_append]);;

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

(* ------------------------------------------------------------------------- *)
(* Tweak for bytes_loaded s (word pc) (APPEND program data)                  *)
(* ------------------------------------------------------------------------- *)

let BYTES_LOADED_APPEND_CLAUSE = prove
 (`bytes_loaded s (word pc) (APPEND prog data) /\
   read RIP s = pcin /\
   rest <=>
   bytes_loaded s (word pc) prog /\
   read RIP s = pcin /\
   bytes_loaded s (word(pc + LENGTH prog)) data /\
   rest`,
  REWRITE_TAC[bytes_loaded_append; GSYM WORD_ADD; CONJ_ACI]);;

(* ------------------------------------------------------------------------- *)
(* Shorthands for individual flags.                                          *)
(* ------------------------------------------------------------------------- *)

(*** Note: this does not build in the conception that some bits
 *** (e.g. 1) are "reserved" and always 0 or 1. That could be added
 *** to the semantics of any instructions operating on the flags register.
 ***)

let CF = define `CF = rflags :> bitelement 0`;;

let PF = define `PF = rflags :> bitelement 2`;;

let AF = define `AF = rflags :> bitelement 4`;;

let ZF = define `ZF = rflags :> bitelement 6`;;

let SF = define `SF = rflags :> bitelement 7`;;

let OF = define `OF = rflags :> bitelement 11`;;

add_component_alias_thms [CF; PF; AF; ZF; SF; OF];;

(* ------------------------------------------------------------------------- *)
(* Shorthands for the general-purpose registers.                             *)
(* ------------------------------------------------------------------------- *)

let RAX = define `RAX = registers :> element (word  0)`
and RCX = define `RCX = registers :> element (word  1)`
and RDX = define `RDX = registers :> element (word  2)`
and RBX = define `RBX = registers :> element (word  3)`
and RSP = define `RSP = registers :> element (word  4)`
and RBP = define `RBP = registers :> element (word  5)`
and RSI = define `RSI = registers :> element (word  6)`
and RDI = define `RDI = registers :> element (word  7)`
and  R8 = define ` R8 = registers :> element (word  8)`
and  R9 = define ` R9 = registers :> element (word  9)`
and R10 = define `R10 = registers :> element (word 10)`
and R11 = define `R11 = registers :> element (word 11)`
and R12 = define `R12 = registers :> element (word 12)`
and R13 = define `R13 = registers :> element (word 13)`
and R14 = define `R14 = registers :> element (word 14)`
and R15 = define `R15 = registers :> element (word 15)`;;

add_component_alias_thms
 [RAX; RCX; RDX; RBX; RSP; RBP; RSI; RDI;
   R8;  R9; R10; R11; R12; R13; R14; R15];;

let  EAX = define ` EAX = RAX :> bottom_32`
and  ECX = define ` ECX = RCX :> bottom_32`
and  EDX = define ` EDX = RDX :> bottom_32`
and  EBX = define ` EBX = RBX :> bottom_32`
and  ESP = define ` ESP = RSP :> bottom_32`
and  EBP = define ` EBP = RBP :> bottom_32`
and  ESI = define ` ESI = RSI :> bottom_32`
and  EDI = define ` EDI = RDI :> bottom_32`
and  R8D = define ` R8D =  R8 :> bottom_32`
and  R9D = define ` R9D =  R9 :> bottom_32`
and R10D = define `R10D = R10 :> bottom_32`
and R11D = define `R11D = R11 :> bottom_32`
and R12D = define `R12D = R12 :> bottom_32`
and R13D = define `R13D = R13 :> bottom_32`
and R14D = define `R14D = R14 :> bottom_32`
and R15D = define `R15D = R15 :> bottom_32`;;

add_component_alias_thms
  [ EAX;  ECX;  EDX;  EBX;  ESP;  EBP;  ESI;  EDI;
    R8D;  R9D; R10D; R11D; R12D; R13D; R14D; R15D];;

let AX = define `AX = EAX :> bottom_16`
and CX = define `CX = ECX :> bottom_16`
and DX = define `DX = EDX :> bottom_16`
and BX = define `BX = EBX :> bottom_16`
and SP = define `SP = ESP :> bottom_16`
and BP = define `BP = EBP :> bottom_16`
and SI = define `SI = ESI :> bottom_16`
and DI = define `DI = EDI :> bottom_16`;;

add_component_alias_thms [AX; CX; DX; BX; SP; BP; SI; DI];;

let AH = define `AH = AX :> top_8`;;
let AL = define `AL = AX :> bottom_8`;;
let BH = define `BH = BX :> top_8`;;
let BL = define `BL = BX :> bottom_8`;;
let CH = define `CH = CX :> top_8`;;
let CL = define `CL = CX :> bottom_8`;;
let DH = define `DH = DX :> top_8`;;
let DL = define `DL = DX :> bottom_8`;;
let SPL = define `SPL = SP :> bottom_8`;;
let BPL = define `BPL = BP :> bottom_8`;;
let SIL = define `SIL = SI :> bottom_8`;;
let DIL = define `DIL = DI :> bottom_8`;;

add_component_alias_thms
  [AH; AL; BH; BL; CH; CL; DH; DL; SPL; BPL; SIL; DIL];;

(* ------------------------------------------------------------------------- *)
(* Shorthands for the SIMD registers.                                        *)
(*                                                                           *)
(* Note that the treatment of XMMs within YMMs within ZMMs zero-extends      *)
(* all writes, e.g. a 128-bit XMM operation will set the top 384 bits        *)
(* of the ZMM register to zero. This is the specified behavior               *)
(* *WHEN THE XMM OPERATION IS VEX-ENCODED*, which is the default form of     *)
(* XMM operation in the decoder. See the next section for an alternative     *)
(* behaviour for SSE and AESNI instructions. See section 15.5 of Intel's     *)
(* ISA Combined Manual, "Accessing XMM, YMM and ZMM Registers"               *)
(* ------------------------------------------------------------------------- *)

let ZMM0  = define `ZMM0  = simdregisters :> element(word 0)`
and ZMM1  = define `ZMM1  = simdregisters :> element(word 1)`
and ZMM2  = define `ZMM2  = simdregisters :> element(word 2)`
and ZMM3  = define `ZMM3  = simdregisters :> element(word 3)`
and ZMM4  = define `ZMM4  = simdregisters :> element(word 4)`
and ZMM5  = define `ZMM5  = simdregisters :> element(word 5)`
and ZMM6  = define `ZMM6  = simdregisters :> element(word 6)`
and ZMM7  = define `ZMM7  = simdregisters :> element(word 7)`
and ZMM8  = define `ZMM8  = simdregisters :> element(word 8)`
and ZMM9  = define `ZMM9  = simdregisters :> element(word 9)`
and ZMM10 = define `ZMM10 = simdregisters :> element(word 10)`
and ZMM11 = define `ZMM11 = simdregisters :> element(word 11)`
and ZMM12 = define `ZMM12 = simdregisters :> element(word 12)`
and ZMM13 = define `ZMM13 = simdregisters :> element(word 13)`
and ZMM14 = define `ZMM14 = simdregisters :> element(word 14)`
and ZMM15 = define `ZMM15 = simdregisters :> element(word 15)`
and ZMM16 = define `ZMM16 = simdregisters :> element(word 16)`
and ZMM17 = define `ZMM17 = simdregisters :> element(word 17)`
and ZMM18 = define `ZMM18 = simdregisters :> element(word 18)`
and ZMM19 = define `ZMM19 = simdregisters :> element(word 19)`
and ZMM20 = define `ZMM20 = simdregisters :> element(word 20)`
and ZMM21 = define `ZMM21 = simdregisters :> element(word 21)`
and ZMM22 = define `ZMM22 = simdregisters :> element(word 22)`
and ZMM23 = define `ZMM23 = simdregisters :> element(word 23)`
and ZMM24 = define `ZMM24 = simdregisters :> element(word 24)`
and ZMM25 = define `ZMM25 = simdregisters :> element(word 25)`
and ZMM26 = define `ZMM26 = simdregisters :> element(word 26)`
and ZMM27 = define `ZMM27 = simdregisters :> element(word 27)`
and ZMM28 = define `ZMM28 = simdregisters :> element(word 28)`
and ZMM29 = define `ZMM29 = simdregisters :> element(word 29)`
and ZMM30 = define `ZMM30 = simdregisters :> element(word 30)`
and ZMM31 = define `ZMM31 = simdregisters :> element(word 31)`;;

add_component_alias_thms
 [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7;
  ZMM8; ZMM9; ZMM10; ZMM11; ZMM12; ZMM13; ZMM14; ZMM15;
  ZMM16; ZMM17; ZMM18; ZMM19; ZMM20; ZMM21; ZMM22; ZMM23;
  ZMM24; ZMM25; ZMM26; ZMM27; ZMM28; ZMM29; ZMM30; ZMM31];;

let YMM0  = define `YMM0  = ZMM0  :> zerotop_256`
and YMM1  = define `YMM1  = ZMM1  :> zerotop_256`
and YMM2  = define `YMM2  = ZMM2  :> zerotop_256`
and YMM3  = define `YMM3  = ZMM3  :> zerotop_256`
and YMM4  = define `YMM4  = ZMM4  :> zerotop_256`
and YMM5  = define `YMM5  = ZMM5  :> zerotop_256`
and YMM6  = define `YMM6  = ZMM6  :> zerotop_256`
and YMM7  = define `YMM7  = ZMM7  :> zerotop_256`
and YMM8  = define `YMM8  = ZMM8  :> zerotop_256`
and YMM9  = define `YMM9  = ZMM9  :> zerotop_256`
and YMM10 = define `YMM10 = ZMM10 :> zerotop_256`
and YMM11 = define `YMM11 = ZMM11 :> zerotop_256`
and YMM12 = define `YMM12 = ZMM12 :> zerotop_256`
and YMM13 = define `YMM13 = ZMM13 :> zerotop_256`
and YMM14 = define `YMM14 = ZMM14 :> zerotop_256`
and YMM15 = define `YMM15 = ZMM15 :> zerotop_256`;;

add_component_alias_thms
 [YMM0; YMM1; YMM2; YMM3; YMM4; YMM5; YMM6; YMM7;
  YMM8; YMM9; YMM10; YMM11; YMM12; YMM13; YMM14; YMM15];;

let XMM0  = define `XMM0  = YMM0  :> zerotop_128`
and XMM1  = define `XMM1  = YMM1  :> zerotop_128`
and XMM2  = define `XMM2  = YMM2  :> zerotop_128`
and XMM3  = define `XMM3  = YMM3  :> zerotop_128`
and XMM4  = define `XMM4  = YMM4  :> zerotop_128`
and XMM5  = define `XMM5  = YMM5  :> zerotop_128`
and XMM6  = define `XMM6  = YMM6  :> zerotop_128`
and XMM7  = define `XMM7  = YMM7  :> zerotop_128`
and XMM8  = define `XMM8  = YMM8  :> zerotop_128`
and XMM9  = define `XMM9  = YMM9  :> zerotop_128`
and XMM10 = define `XMM10 = YMM10 :> zerotop_128`
and XMM11 = define `XMM11 = YMM11 :> zerotop_128`
and XMM12 = define `XMM12 = YMM12 :> zerotop_128`
and XMM13 = define `XMM13 = YMM13 :> zerotop_128`
and XMM14 = define `XMM14 = YMM14 :> zerotop_128`
and XMM15 = define `XMM15 = YMM15 :> zerotop_128`;;

add_component_alias_thms
 [XMM0; XMM1; XMM2; XMM3; XMM4; XMM5; XMM6; XMM7;
  XMM8; XMM9; XMM10; XMM11; XMM12; XMM13; XMM14; XMM15];;

(*** Note that K0 is actually hardwired to all-1s              ***)
(*** So strictly we should have left it out of the state above ***)

let K0 = define `K0:(x86state,(64)word)component = rvalue(word_not(word 0))`;;
let K1 = define `K1 = maskregisters :> element(word 1)`;;
let K2 = define `K2 = maskregisters :> element(word 2)`;;
let K3 = define `K3 = maskregisters :> element(word 3)`;;
let K4 = define `K4 = maskregisters :> element(word 4)`;;
let K5 = define `K5 = maskregisters :> element(word 5)`;;
let K6 = define `K6 = maskregisters :> element(word 6)`;;
let K7 = define `K7 = maskregisters :> element(word 7)`;;

(* ------------------------------------------------------------------------- *)
(* Shorthands for the SSE&AESNI SIMD registers                               *)
(*                                                                           *)
(* Note that when writing to the lowerhalf (XMM of YMM) of SIMD registers,   *)
(* SSE and AESNI instructions will keep the upperhalf as is. This is         *)
(* different from the behaviour *WHEN THE XMM OPERATION IS VEX-ENCODED*.     *)
(* Interally, the symbolic simulation will reduce reads of SSE SIMD          *)
(* registers to reads of VEX registers using READ_YMM_SSE_EQUIV theorems.    *)
(* See section 15.5 of Intel's ISA Combined Manual,                          *)
(* "Accessing XMM, YMM and ZMM Registers"                                    *)
(* ------------------------------------------------------------------------- *)

let YMM0_SSE  = define `YMM0_SSE  = ZMM0  :> bottom_256`
and YMM1_SSE  = define `YMM1_SSE  = ZMM1  :> bottom_256`
and YMM2_SSE  = define `YMM2_SSE  = ZMM2  :> bottom_256`
and YMM3_SSE  = define `YMM3_SSE  = ZMM3  :> bottom_256`
and YMM4_SSE  = define `YMM4_SSE  = ZMM4  :> bottom_256`
and YMM5_SSE  = define `YMM5_SSE  = ZMM5  :> bottom_256`
and YMM6_SSE  = define `YMM6_SSE  = ZMM6  :> bottom_256`
and YMM7_SSE  = define `YMM7_SSE  = ZMM7  :> bottom_256`
and YMM8_SSE  = define `YMM8_SSE  = ZMM8  :> bottom_256`
and YMM9_SSE  = define `YMM9_SSE  = ZMM9  :> bottom_256`
and YMM10_SSE = define `YMM10_SSE = ZMM10 :> bottom_256`
and YMM11_SSE = define `YMM11_SSE = ZMM11 :> bottom_256`
and YMM12_SSE = define `YMM12_SSE = ZMM12 :> bottom_256`
and YMM13_SSE = define `YMM13_SSE = ZMM13 :> bottom_256`
and YMM14_SSE = define `YMM14_SSE = ZMM14 :> bottom_256`
and YMM15_SSE = define `YMM15_SSE = ZMM15 :> bottom_256`;;

add_component_alias_thms
 [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM3_SSE;
  YMM4_SSE; YMM5_SSE; YMM6_SSE; YMM7_SSE;
  YMM8_SSE; YMM9_SSE; YMM10_SSE; YMM11_SSE;
  YMM12_SSE; YMM13_SSE; YMM14_SSE; YMM15_SSE];;

let READ_YMM_SSE_TAC SSE_fn fn =
  STRIP_TAC THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; SSE_fn; fn;
    READ_SUBWORD; DIMINDEX_256; bottom_256; zerotop_256;
    bottomhalf; through; read] THEN
  (* BITBLAST_TAC works too *)
  MATCH_MP_TAC WORD_SUBWORD_EQUAL_WORD_ZX_POS0 THEN
  REWRITE_TAC[DIMINDEX_256; DIMINDEX_512] THEN
  CONV_TAC(NUM_REDUCE_CONV) ;;

let READ_YMM_SSE_EQUIV:thm list = map (fun (goal,ssereg,reg) ->
  prove(goal, READ_YMM_SSE_TAC ssereg reg))
   [(`!s:x86state. read YMM0_SSE s = read YMM0 s`,YMM0_SSE,YMM0);
    (`!s:x86state. read YMM1_SSE s = read YMM1 s`,YMM1_SSE,YMM1);
    (`!s:x86state. read YMM2_SSE s = read YMM2 s`,YMM2_SSE,YMM2);
    (`!s:x86state. read YMM3_SSE s = read YMM3 s`,YMM3_SSE,YMM3);
    (`!s:x86state. read YMM4_SSE s = read YMM4 s`,YMM4_SSE,YMM4);
    (`!s:x86state. read YMM5_SSE s = read YMM5 s`,YMM5_SSE,YMM5);
    (`!s:x86state. read YMM6_SSE s = read YMM6 s`,YMM6_SSE,YMM6);
    (`!s:x86state. read YMM7_SSE s = read YMM7 s`,YMM7_SSE,YMM7);
    (`!s:x86state. read YMM8_SSE s = read YMM8 s`,YMM8_SSE,YMM8);
    (`!s:x86state. read YMM9_SSE s = read YMM9 s`,YMM9_SSE,YMM9);
    (`!s:x86state. read YMM10_SSE s = read YMM10 s`,YMM10_SSE,YMM10);
    (`!s:x86state. read YMM11_SSE s = read YMM11 s`,YMM11_SSE,YMM11);
    (`!s:x86state. read YMM12_SSE s = read YMM12 s`,YMM12_SSE,YMM12);
    (`!s:x86state. read YMM13_SSE s = read YMM13 s`,YMM13_SSE,YMM13);
    (`!s:x86state. read YMM14_SSE s = read YMM14 s`,YMM14_SSE,YMM14);
    (`!s:x86state. read YMM15_SSE s = read YMM15 s`,YMM15_SSE,YMM15);]

let XMM0_SSE  = define `XMM0_SSE  = YMM0_SSE  :> bottom_128`
and XMM1_SSE  = define `XMM1_SSE  = YMM1_SSE  :> bottom_128`
and XMM2_SSE  = define `XMM2_SSE  = YMM2_SSE  :> bottom_128`
and XMM3_SSE  = define `XMM3_SSE  = YMM3_SSE  :> bottom_128`
and XMM4_SSE  = define `XMM4_SSE  = YMM4_SSE  :> bottom_128`
and XMM5_SSE  = define `XMM5_SSE  = YMM5_SSE  :> bottom_128`
and XMM6_SSE  = define `XMM6_SSE  = YMM6_SSE  :> bottom_128`
and XMM7_SSE  = define `XMM7_SSE  = YMM7_SSE  :> bottom_128`
and XMM8_SSE  = define `XMM8_SSE  = YMM8_SSE  :> bottom_128`
and XMM9_SSE  = define `XMM9_SSE  = YMM9_SSE  :> bottom_128`
and XMM10_SSE = define `XMM10_SSE = YMM10_SSE :> bottom_128`
and XMM11_SSE = define `XMM11_SSE = YMM11_SSE :> bottom_128`
and XMM12_SSE = define `XMM12_SSE = YMM12_SSE :> bottom_128`
and XMM13_SSE = define `XMM13_SSE = YMM13_SSE :> bottom_128`
and XMM14_SSE = define `XMM14_SSE = YMM14_SSE :> bottom_128`
and XMM15_SSE = define `XMM15_SSE = YMM15_SSE :> bottom_128`;;

add_component_alias_thms
 [XMM0_SSE; XMM1_SSE; XMM2_SSE; XMM3_SSE;
  XMM4_SSE; XMM5_SSE; XMM6_SSE; XMM7_SSE;
  XMM8_SSE; XMM9_SSE; XMM10_SSE; XMM11_SSE;
  XMM12_SSE; XMM13_SSE; XMM14_SSE; XMM15_SSE];;

(* ------------------------------------------------------------------------- *)
(* Semantics of conditions.                                                  *)
(* ------------------------------------------------------------------------- *)

let condition_semantics = define
 `(condition_semantics Unconditional s <=>
        T) /\
  (condition_semantics Condition_B s <=>
        read CF s) /\
  (condition_semantics Condition_BE s <=>
        read CF s \/ read ZF s) /\
  (condition_semantics Condition_L s <=>
        ~(read SF s <=> read OF s)) /\
  (condition_semantics Condition_LE s <=>
        ~(read SF s <=> read OF s) \/ read ZF s) /\
  (condition_semantics Condition_NB s <=>
        ~read CF s) /\
  (condition_semantics Condition_NBE s <=>
        ~(read CF s \/ read ZF s)) /\
  (condition_semantics Condition_NL s <=>
        (read SF s <=> read OF s)) /\
  (condition_semantics Condition_NLE s <=>
        (read SF s <=> read OF s) /\ ~read ZF s) /\
  (condition_semantics Condition_NO s <=>
        ~read OF s) /\
  (condition_semantics Condition_NP s <=>
        ~read PF s) /\
  (condition_semantics Condition_NS s <=>
        ~read SF s) /\
  (condition_semantics Condition_NZ s <=>
        ~read ZF s) /\
  (condition_semantics Condition_O s <=>
        read OF s) /\
  (condition_semantics Condition_P s <=>
        read PF s) /\
  (condition_semantics Condition_S s <=>
        read SF s) /\
  (condition_semantics Condition_Z s <=>
        read ZF s)`;;

(* ------------------------------------------------------------------------- *)
(* Exceptions. Currently the semantics is basically "some arbitrary state".  *)
(* But we distinguish things so this can become a more accurate model later. *)
(* In general there is also a 64-bit data field with some exceptions         *)
(* ------------------------------------------------------------------------- *)

let raise_exception = new_definition
 `raise_exception (b:byte) :x86state->x86state->bool =
    ASSIGNS entirety`;;

let raise_exception_with = new_definition
 `raise_exception_with (b:byte) (d:int64) :x86state->x86state->bool =
    ASSIGNS entirety`;;

let x86_Exception_DE = new_definition
  `x86_Exception_DE = (word 0x00 :byte)`;;

let x86_Exception_DB = new_definition
  `x86_Exception_DB = (word 0x01 :byte)`;;

let x86_Exception_NMI = new_definition
  `x86_Exception_NMI = (word 0x02 :byte)`;;

let x86_Exception_BP = new_definition
  `x86_Exception_BP = (word 0x03:byte)`;;

let x86_Exception_OF = new_definition
  `x86_Exception_OF = (word 0x04 :byte)`;;

let x86_Exception_BR = new_definition
  `x86_Exception_BR = (word 0x05 :byte)`;;

let x86_Exception_UD = new_definition
  `x86_Exception_UD = (word 0x06 :byte)`;;

let x86_Exception_NM = new_definition
  `x86_Exception_NM = (word 0x07 :byte)`;;

let x86_Exception_DF = new_definition
  `x86_Exception_DF = (word 0x08 :byte)`;;

let x86_Exception_TS = new_definition
  `x86_Exception_TS = (word 0x0A :byte)`;;

let x86_Exception_NP = new_definition
  `x86_Exception_NP = (word 0x0B :byte)`;;

let x86_Exception_SS = new_definition
  `x86_Exception_SS = (word 0x0C :byte)`;;

let x86_Exception_GP = new_definition
  `x86_Exception_GP = (word 0x0D :byte)`;;

let x86_Exception_PF = new_definition
  `x86_Exception_PF = (word 0x0E :byte)`;;

let x86_Exception_MF = new_definition
  `x86_Exception_MF = (word 0x10 :byte)`;;

let x86_Exception_AC = new_definition
  `x86_Exception_AC = (word 0x11 :byte)`;;

let x86_Exception_MC = new_definition
  `x86_Exception_MC = (word 0x12 :byte)`;;

let x86_Exception_XF = new_definition
  `x86_Exception_XF = (word 0x13 :byte)`;;

let x86_Exception_VE = new_definition
  `x86_Exception_VE = (word 0x14 :byte)`;;

let x86_Exception_SX = new_definition
  `x86_Exception_SX = (word 0x1E :byte)`;;

(* ------------------------------------------------------------------------- *)
(* The core operations with generic sizes, to be instantiated to any of      *)
(* 8, 16, 32 or 64. In effect this is a kind of shallow embedding of x86.    *)
(* ------------------------------------------------------------------------- *)

let x86_ADC = new_definition
 `x86_ADC dest src s =
        let x = read dest s and y = read src s and c = bitval(read CF s) in
        let z = word_add (word_add x y) (word c) in
        (dest := (z:N word) ,,
         ZF := (val z = 0) ,,
         SF := (ival z < &0) ,,
         PF := word_evenparity(word_zx z:byte) ,,
         CF := ~(val x + val y + c = val z) ,,
         OF := ~(ival x + ival y + &c = ival z) ,,
         AF := ~(val(word_zx x:nybble) + val(word_zx y:nybble) + c =
                 val(word_zx z:nybble))) s`;;

let x86_ADCX = new_definition
 `x86_ADCX dest src s =
        let x = read dest s and y = read src s and c = bitval(read CF s) in
        let z = word_add (word_add x y) (word c) in
        (dest := (z:N word) ,,
         CF := ~(val x + val y + c = val z)) s`;;

let x86_ADD = new_definition
 `x86_ADD dest src s =
        let x = read dest s and y = read src s in
        let z = word_add x y in
        (dest := (z:N word) ,,
         ZF := (val z = 0) ,,
         SF := (ival z < &0) ,,
         PF := word_evenparity(word_zx z:byte) ,,
         CF := ~(val x + val y = val z) ,,
         OF := ~(ival x + ival y = ival z) ,,
         AF := ~(val(word_zx x:nybble) + val(word_zx y:nybble) =
                 val(word_zx z:nybble))) s`;;

let x86_ADOX = new_definition
 `x86_ADOX dest src s =
        let x = read dest s and y = read src s and c = bitval(read OF s) in
        let z = word_add (word_add x y) (word c) in
        (dest := (z:N word) ,,
         OF := ~(val x + val y + c = val z)) s`;;

(* AESENC does not modify DEST[MAXVL-1:128] *)
let x86_AESENC = new_definition
  `x86_AESENC dest src s =
     let state = read dest s and roundkey = read src s in
     let new_state = aesenc state roundkey in
     (dest := new_state) s`;;

(* AESENCLAST does not modify DEST[MAXVL-1:128] *)
let x86_AESENCLAST = new_definition
  `x86_AESENCLAST dest src s =
     let state = read dest s and roundkey = read src s in
     let new_state = aesenclast state roundkey in
     (dest := new_state) s`;;

(* AESDEC does not modify DEST[MAXVL-1:128] *)
let x86_AESDEC = new_definition
  `x86_AESDEC dest src s =
     let state = read dest s and roundkey = read src s in
     let new_state = aesdec state roundkey in
     (dest := new_state) s`;;

(* AESDECLAST does not modify DEST[MAXVL-1:128] *)
let x86_AESDECLAST = new_definition
  `x86_AESDECLAST dest src s =
     let state = read dest s and roundkey = read src s in
     let new_state = aesdeclast state roundkey in
     (dest := new_state) s`;;

(* AESDECLAST does not modify DEST[MAXVL-1:128] *)
let x86_AESKEYGENASSIST = new_definition
  `x86_AESKEYGENASSIST dest src imm8 s =
     let x = read src s in
     let imm8 = read imm8 s in
     let res = aeskeygenassist x imm8 in
     (dest := res) s`;;

let x86_AND = new_definition
 `x86_AND dest src s =
        let x = read dest s and y = read src s in
        let z = word_and x y in
        (dest := (z:N word) ,,
         ZF := (val z = 0) ,,
         SF := (ival z < &0) ,,
         PF := word_evenparity(word_zx z:byte) ,,
         CF := F ,,
         OF := F ,,
         UNDEFINED_VALUES[AF]) s`;;

(*** These are similar to TZCNT and (less so, dual) LZCNT. Besides one
 *** being dualized, they are officially undefined on zero inputs.
 *** The flag settings are also different: the input determines ZF and
 *** the others are undefined (on TZCNT/LZCNT the output determines ZF).
 *** They have the merit of being pure x86-64 and not needing even
 *** moderately recent extensions.
 ***)

let x86_BSF = new_definition
 `x86_BSF dest src s =
        let x:N word = read src s in
        let z:N word = word(word_ctz x) in
        ((if x = word 0 then UNDEFINED_VALUES[dest] else dest := (z:N word)) ,,
         ZF := (val x = 0) ,,
         UNDEFINED_VALUES[CF;OF;SF;PF;AF]) s`;;

let x86_BSR = new_definition
 `x86_BSR dest src s =
        let x:N word = read src s in
        let z:N word = word(dimindex(:N) - 1 - word_clz x) in
        ((if x = word 0 then UNDEFINED_VALUES[dest] else dest := (z:N word)) ,,
         ZF := (val x = 0) ,,
         UNDEFINED_VALUES[CF;OF;SF;PF;AF]) s`;;

let x86_BSWAP = new_definition
 `x86_BSWAP dest s =
        let x:((((N)tybit0)tybit0)tybit0)word = read dest s in
        let x' = word_bytereverse x in
        (dest := x') s`;;

(*** These four amount to the core operations for BT, BTC, BTR and BTS.
 *** When the first operand is a register this is the entire thing.
 *** With memory operands however, the upper part is used to offset the
 *** address (presumably DIV means Euclidean division?) and sometimes
 *** assemblers even support that kind of thing for immediates. So the
 *** dispatch needs to treat different operands differently, unless we
 *** choose to define some more generic "bit" of a state components.
 ***)

let x86_BT = new_definition
 `x86_BT dest src s =
        let (x:N word) = read dest s and y = read src s in
        let c = val y MOD dimindex(:N) in
        let b = bit c x in
        (CF := b ,,
         UNDEFINED_VALUES[SF;PF;OF;AF]) s`;;

let x86_BTC = new_definition
 `x86_BTC dest src s =
        let (x:N word) = read dest s and y = read src s in
        let c = val y MOD dimindex(:N) in
        let b = bit c x in
        (dest :> bitelement c := ~b ,,
         CF := b ,,
         UNDEFINED_VALUES[SF;PF;OF;AF]) s`;;

let x86_BTR = new_definition
 `x86_BTR dest src s =
        let (x:N word) = read dest s and y = read src s in
        let c = val y MOD dimindex(:N) in
        let b = bit c x in
        (dest :> bitelement c := F ,,
         CF := b ,,
         UNDEFINED_VALUES[SF;PF;OF;AF]) s`;;

let x86_BTS = new_definition
 `x86_BTS dest src s =
        let (x:N word) = read dest s and y = read src s in
        let c = val y MOD dimindex(:N) in
        let b = bit c x in
        (dest :> bitelement c := T ,,
         CF := b ,,
         UNDEFINED_VALUES[SF;PF;OF;AF]) s`;;

let x86_CLC = new_definition
 `x86_CLC s =
        (CF := F) s`;;

let x86_CMC = new_definition
 `x86_CMC s =
        let c = read CF s in
        (CF := ~c) s`;;

let x86_CMOV = new_definition
 `x86_CMOV cc dest src s =
        (dest := (if condition_semantics cc s then read src s
                  else read dest s)) s`;;

let x86_CMP = new_definition
 `x86_CMP dest src s =
        let x = read dest s and y = read src s in
        let (z:N word) = word_sub x y in
        (ZF := (val z = 0) ,,
         SF := (ival z < &0) ,,
         PF := word_evenparity(word_zx z:byte) ,,
         CF := ~(&(val x) - &(val y):int = &(val z)) ,,
         OF := ~(ival x - ival y = ival z) ,,
         AF := ~(&(val(word_zx x:nybble)) - &(val(word_zx y:nybble)):int =
                 &(val(word_zx z:nybble)))) s`;;

let x86_DEC = new_definition
 `x86_DEC dest s =
        let x = read dest s in
        let z = word_sub x (word 1) in
        (dest := (z:N word) ,,
         ZF := (val z = 0) ,,
         SF := (ival z < &0) ,,
         PF := word_evenparity(word_zx z:byte) ,,
         OF := ~(ival x - &1 = ival z) ,,
         AF := ~(&(val(word_zx x:nybble)) - &1:int =
                 &(val(word_zx z:nybble)))) s`;;

(*** Again we make the operands explicit in this function. In the
 *** final dispatch most of the sources and destinations are implicit
 *** and drawn from RAX / RDX and its shorter versions
 ***)

let x86_DIV2 = new_definition
 `x86_DIV2 (dest_quo,dest_rem) (src_hi,src_lo) divisor s =
        let x = 2 EXP dimindex(:N) * val(read src_hi s:N word) +
                val(read src_lo s:N word)
        and y = val(read divisor s:N word) in
        if y = 0 then
          raise_exception x86_Exception_DE s
        else
          let q = x DIV y and r = x MOD y in
          if 2 EXP dimindex(:N) <= q then
            raise_exception x86_Exception_DE s
          else
           (dest_quo := (word q:N word) ,,
            dest_rem := (word r:N word) ,,
            UNDEFINED_VALUES [CF;ZF;ZF; PF;OF;ZF]) s`;;

(*** This is the ENDBR64 instruction, which is treated as a NOP. On
 *** machines without CET enabled, including older machines from
 *** before the feature existed, this is indeed how it behaves. We
 *** do not attempt to model the restrictions that are imposed when
 *** CET is enabled, and such restrictions arguably belong on the
 *** indirect branches themselves, of which there are none in
 *** s2n-bignum itself.
 ***)

let x86_ENDBR64 = new_definition
 `x86_ENDBR64 (s:x86state) = \s'. s = s'`;;

(*** There are really four different multiplies here.
 ***
 *** 1. x86_IMUL: a signed multiply with the same length for operands
 ***    and result, corresponding to the "two operand" and "three operand"
 ***    forms in the manual, with three operands to allow flexibility at this
 ***    level. Note that as usual the result is signed/unsigned-agnostic in
 ***    this setting. But the overflow and carry settings are *both* signed.

 *** 2. x86_IMUL2: A signed two-part multiply, corresponding to the
 ***    "one-operand form" in the manuals. The carry and overflow seem to
 ***    be set in the same way and as one would expect, according to recent
 ***    documentation and a few experiments. However much older manuals say
 ***    something different. (Whether the top is something other than all
 ***    0s or all 1s --- implying for example 2^31 * 2^32 would not set it.)

 *** 3. x86_MUL2: An unsigned two-part signed multiply. The detection of
 ***    CF=OF is based on whether the top is nonzero. The code for this is
 ***    further below following alphabetical order.

 *** 4. x86_MULX4: An unsigned 2-part multiply without affecting flags. In
 ***    the final dispatch the first source is explicit (edx/rdx). Note that
 ***    it's important to assign the high part *second* to match the ISA
 ***    manual "if the first and second operands are identical, it will contain
 ***    the high half of the multiplication results". In others we happen to
 ***    do it the other way round, but maybe for uniformity should change that.
 ***)

let x86_IMUL3 = new_definition
 `x86_IMUL3 dest (src1,src2) s =
        let x = read src1 s and y = read src2 s in
        let z = word_mul x y in
        (dest := (z:N word) ,,
         CF := ~(ival x * ival y = ival z) ,,
         OF := ~(ival x * ival y = ival z) ,,
         UNDEFINED_VALUES[ZF;SF;PF;AF]) s`;;

let x86_IMUL = new_definition
 `x86_IMUL dest src = x86_IMUL3 dest (dest,src)`;;

let x86_IMUL2 = new_definition
 `x86_IMUL2 (dest_hi,dest_lo) src s =
        let (x:N word) = read dest_lo s and (y:N word) = read src s in
        let z = iword(ival x * ival y):(N tybit0)word in
        let z_hi:N word = word_zx (word_ushr z (dimindex(:N)))
        and z_lo:N word = word_zx z in
        (dest_hi := z_hi ,,
         dest_lo := z_lo ,,
         CF := ~(ival x * ival y = ival z_lo) ,,
         OF := ~(ival x * ival y = ival z_lo) ,,
         UNDEFINED_VALUES[ZF;SF;PF;AF]) s`;;

let x86_INC = new_definition
 `x86_INC dest s =
        let x = read dest s in
        let z = word_add x (word 1) in
        (dest := (z:N word) ,,
         ZF := (val z = 0) ,,
         SF := (ival z < &0) ,,
         PF := word_evenparity(word_zx z:byte) ,,
         OF := ~(ival x + &1 = ival z) ,,
         AF := ~(val(word_zx x:nybble) + 1 =
                 val(word_zx z:nybble))) s`;;

(*** At this level this is trivial: the EA is from operand decoding ***)

let x86_LEA = new_definition
 `x86_LEA dest ea s =
        (dest := ea) s`;;

let x86_LZCNT = new_definition
 `x86_LZCNT dest src s =
        let x:N word = read src s in
        let z:N word = word(word_clz x) in
        (dest := (z:N word) ,,
         CF := (val x = 0) ,,
         ZF := (val z = 0) ,,
         UNDEFINED_VALUES[OF;SF;PF;AF]) s`;;

let x86_MOV = new_definition
 `x86_MOV dest src s =
        let x = read src s in (dest := x) s`;;

let x86_MOVAPS = new_definition
 `x86_MOVAPS dest src s =
    let x = read src s in (dest := x) s`;;

let x86_MOVDQA = new_definition
 `x86_MOVDQA dest src s =
    let x = read src s in (dest := x) s`;;

let x86_MOVDQU = new_definition
`x86_MOVDQU dest src s =
   let x = read src s in (dest := x) s`;;

let x86_MOVUPS = new_definition
 `x86_MOVUPS dest src s =
    let x = read src s in (dest := x) s`;;

(*** These are rare cases with distinct source and destination
 *** operand sizes. There is a 32-bit to 64-bit version of MOVSX(D),
 *** whereas the corresponding MOVZX is not encodable; the operation
 *** can be done anyway by the usual 32-bit MOV in 64-bit mode.
 ***
 *** A bit bizarrely there are same-size versions of MOVSXD.
 *** These are really just freaks of decoding, with semantics
 *** equivalent to MOV, and use is actively discouraged in
 *** the Intel manuals ("The use of MOVSXD without REX.W in
 *** 64-bit mode is discouraged".) However, we do handle
 *** the 32->32 case anyway, though not the 16->16 case, in
 *** line with the general policy of rejecting operand size
 *** override prefixes unless the instructions are useful.
 ***)

let x86_MOVSX = new_definition
 `x86_MOVSX dest src s =
        let (x:M word) = read src s in
        let (x':N word) = word_sx x in
        (dest := x') s`;;

let x86_MOVZX = new_definition
 `x86_MOVZX dest src s =
        let (x:M word) = read src s in
        let (x':N word) = word_zx x in
        (dest := x') s`;;

(*** See comments above for IMUL. No other version of unsigned mul ***)

let x86_MULX4 = new_definition
 `x86_MULX4 (dest_hi,dest_lo) (src1,src2) s =
        let (x:N word) = read src1 s and (y:N word) = read src2 s in
        let z = word(val x * val y):(N tybit0)word in
        let z_hi:N word = word_zx (word_ushr z (dimindex(:N)))
        and z_lo:N word = word_zx z in
        (dest_lo := z_lo ,,
         dest_hi := z_hi) s`;;

let x86_MUL2 = new_definition
 `x86_MUL2 (dest_hi,dest_lo) src s =
        let (x:N word) = read dest_lo s and (y:N word) = read src s in
        let z = word(val x * val y):(N tybit0)word in
        let z_hi:N word = word_zx (word_ushr z (dimindex(:N)))
        and z_lo:N word = word_zx z in
        (dest_hi := z_hi ,,
         dest_lo := z_lo ,,
         CF := ~(z_hi = word 0) ,,
         OF := ~(z_hi = word 0) ,,
         UNDEFINED_VALUES[ZF;SF;PF;AF]) s`;;

(*** Note that the Intel documentation states the CF setting very explicitly
 *** as "the source operand is nonzero". So I copy that here. But it is just
 *** the same as the uniform value you'd get from 0 - x

  WORD_ARITH
   `&(val(word_sub x y)):int = &(val x) - &(val y) <=> val y <= val x`;;

  WORD_ARITH
    `-- (&(val x)):int = &(val(word_neg x)) <=> x = word 0`;;

 ***)

let x86_NEG = new_definition
 `x86_NEG dest s =
        let x = read dest s in
        let z = word_neg x in
        (dest := (z:N word) ,,
         ZF := (val z = 0) ,,
         SF := (ival z < &0) ,,
         PF := word_evenparity(word_zx z:byte) ,,
         CF := ~(x = word 0) ,,
         OF := ~(-- ival x = ival z) ,,
         AF := ~(-- &(val(word_zx x:nybble)):int =
                 &(val(word_zx z:nybble)))) s`;;

let x86_NOP = new_definition
 `x86_NOP (s:x86state) = \s'. s = s'`;;

(*
  The multi-byte form of NOP is available on processors with model encoding:
  CPUID.01H.EAX[Bytes 11:8] = 0110B or 1111B
*)
let x86_NOP_N = new_definition
 `x86_NOP_N dest (s:x86state) = \s'. s = s'`;;

(*** In contrast to most logical ops, NOT doesn't affect any flags ***)

let x86_NOT = new_definition
 `x86_NOT dest s =
        let x = read dest s in
        let z = word_not x in
        (dest := (z:N word)) s`;;

let x86_OR = new_definition
 `x86_OR dest src s =
        let x = read dest s and y = read src s in
        let z = word_or x y in
        (dest := (z:N word) ,,
         ZF := (val z = 0) ,,
         SF := (ival z < &0) ,,
         PF := word_evenparity(word_zx z:byte) ,,
         CF := F ,,
         OF := F ,,
         UNDEFINED_VALUES[AF]) s`;;

let x86_PADDD = new_definition
  `x86_PADDD dest src s =
    let x = read dest s in
    let y = read src s in
    let res:(128)word = simd4 word_add x y in
    (dest := res) s`;;

let x86_PADDQ = new_definition
  `x86_PADDQ dest src s =
    let x = read dest s in
    let y = read src s in
    let res:(128)word = simd2 word_add x y in
    (dest := res) s`;;

let x86_PAND = new_definition
  `x86_PAND dest src s =
    let x = read dest s in
    let y = read src s in
    (dest := word_and x y) s`;;

let x86_PCMPGTD = new_definition
  `x86_PCMPGTD dest src s =
    let x = read dest s in
    let y = read src s in
    let res:(128)word = simd4 (\(x:32 word) (y:32 word).
        if word_igt x y then (word 0xffffffff) else (word 0))
        x y in
    (dest := res) s`;;

(*** Push and pop are a bit odd in several ways. First of all, there is  ***)
(*** an implicit memory operand so this doesn't have quite the same      ***)
(*** "shallowness": we refer to the memory component explicitly. And we  ***)
(*** need to adjust the sizes dynamically and hence use x:num inside.    ***)
(*** Note that in 64-bit mode you can only have sizes 16 or 64 so the    ***)
(*** full genericity of this function is not used in our setting.        ***)
(*** Finally, we ignore all the versions with segment registers.         ***)
(*** The handling of pushing and popping RSP itself is an obvious corner ***)
(*** case in which the documentation is poor, and completely different   ***)
(*** (at least in style if not intended meaning) in the Intel and AMD    ***)
(*** manuals. Nevertheless I believe the treatment here is right.        ***)

let x86_POP = new_definition
 `x86_POP dest s =
        let n = dimindex(:N) DIV 8 in
        let p = read RSP s in
        let x:N word = word(read (memory :> bytes(p,n)) s) in
        let p' = word_add p (word n) in
        (RSP := p' ,,
         dest := x) s`;;

let x86_PUSH = new_definition
 `x86_PUSH src s =
        let n = dimindex(:N) DIV 8 in
        let p = read RSP s
        and x = val(read src s:N word) in
        let p' = word_sub p (word n) in
        (RSP := p' ,,
         memory :> bytes(p',n) := x) s`;;

let x86_PSHUFD = new_definition
 `x86_PSHUFD dest src imm8 s =
    let src = read src s in
    let od = read imm8 s in
    let res:(128)word = usimd4 (\(od:(2)word).
        word_subword src ((val od)*32,32)) od in
    (dest := res) s`;;

let x86_PSRAD = new_definition
  `x86_PSRAD dest imm8 s =
    let d = read dest s in
    let count_src = val (read imm8 s) in
    let count = if count_src > 31 then 32 else count_src in
    let res:(128)word = usimd4 (\x. word_ishr x count) d in
    (dest := res) s`;;

let x86_PXOR = new_definition
  `x86_PXOR dest src s =
    let x = read dest s in
    let y = read src s in
    (dest := word_xor x y) s`;;

(*** Out of alphabetical order as PUSH is a subroutine ***)

let x86_CALL = new_definition
 `x86_CALL target =
    x86_PUSH RIP ,, RIP := target`;;

(*** We don't distinguish near/far and don't have the form with the ***)
(*** additional "release more bytes" argument, so it's quite simple ***)

let x86_RET = new_definition
 `x86_RET s =
        let p = read RSP s in
        let p' = word_add p (word 8)
        and ip' = read (memory :> bytes64 p) s in
        (RSP := p' ,, RIP := ip') s`;;

(*** Shift and rotate operations mask to 5 bits, or 6 bits in 64-bit     ***)
(*** Actually it's even more complicated for RCL and RCR in general:     ***)
(*** for sizes 8 and 16 they go mod 9 and 17 (natural enough) but then   ***)
(*** 32-bit and 64-bit forms just mask as in the others. Not generic.    ***)

(*** It's not quite enough to just use the native size, as certain       ***)
(*** things are different in case case masked_shift IN {0,1} (e.g. OF)   ***)
(*** We assume that the masked value comes in from the decoder           ***)
(*** Our underlying rotate functions are modulo anyway.                  ***)
(*** It is at least clearly stated that SF, ZF, AF, PF are unaffected    ***)
(*** It's also stated that no flags are affected for zero masked count   ***)
(*** The manual is confusing about "affected" versus "defined" on the    ***)
(*** OF result for counts > 1.                                           ***)

(*** Note that in the unpacking of the actual instructions below we can  ***)
(*** assume the shift is an 8-bit operand (an immediate or CL, in fact   ***)
(*** in the actual encodings.)                                           ***)

(*** Note that RCL and RCR don't special case the zero for CF, since     ***)
(*** it will anyway be the input CF in that case                         ***)

(*** The OF definitions are confusing but I hope correct.                ***)

let x86_RCL = new_definition
 `x86_RCL dest c s =
        let x = read dest s
        and cin = read CF s in
        let xx:((1,N)finite_sum)word = word_join (word(bitval cin):1 word) x in
        let zz = word_rol xx c in
        let z = word_subword zz (0,dimindex(:N))
        and cout = bit (dimindex(:N)) zz in
        (dest := (z:N word) ,,
         CF := cout ,,
         (if c = 0 then
               OF := read OF s
          else if c = 1 then
               OF := ~(bit (dimindex(:N)-1) z = cout)
          else UNDEFINED_VALUES[OF])) s`;;

let x86_RCR = new_definition
 `x86_RCR dest c s =
        let x = read dest s
        and cin = read CF s in
        let xx:((1,N)finite_sum)word = word_join (word(bitval cin):1 word) x in
        let zz = word_ror xx c in
        let z = word_subword zz (0,dimindex(:N))
        and cout = bit (dimindex(:N)) zz in
        (dest := (z:N word) ,,
         CF := cout ,,
         (if c = 0 then
            OF := read OF s
          else if c = 1 then
            OF := ~(bit (dimindex(:N)-1) z = bit (dimindex(:N)-2) z)
          else UNDEFINED_VALUES[OF])) s`;;

let x86_ROL = new_definition
 `x86_ROL dest c s =
        let x = read dest s in
        let z = word_rol x c in
        (dest := (z:N word) ,,
         CF := (if c = 0 then read CF s else bit 0 z) ,,
         (if c = 0 then
            OF := read OF s
          else if c = 1 then
            OF := ~(bit (dimindex(:N)-1) z = bit 0 z)
          else UNDEFINED_VALUES[OF])) s`;;

let x86_ROR = new_definition
 `x86_ROR dest c s =
        let x = read dest s in
        let z = word_ror x c in
        (dest := (z:N word) ,,
         CF := (if c = 0 then read CF s else bit (dimindex(:N)-1) z) ,,
         (if c = 0 then
            OF := read OF s
          else if c = 1 then
            OF := ~(bit (dimindex(:N)-1) z = bit (dimindex(:N)-2) z)
          else UNDEFINED_VALUES[OF])) s`;;

(*** Note that SAL and SHL are the same thing ***)

let x86_SAR = new_definition
 `x86_SAR dest c s =
      let x = read dest s in
      let z = word_ishr x c in
      (dest := (z:N word) ,,
       ZF := (if c = 0 then read ZF s else val z = 0) ,,
       SF := (if c = 0 then read SF s else ival z < &0) ,,
       PF := (if c = 0 then read PF s else word_evenparity(word_zx z:byte)) ,,
       CF := (if c = 0 then read CF s else bit 0 (word_ishr x (c - 1))) ,,
       (if c = 0 then
          OF := read OF s
        else if c = 1 then
          OF := F
        else UNDEFINED_VALUES[OF]) ,,
       (if c = 0 then
          AF := read AF s
        else UNDEFINED_VALUES[AF])) s`;;

let x86_SBB = new_definition
 `x86_SBB dest src s =
        let x = read dest s and y = read src s and c = bitval(read CF s) in
        let z = word_sub x (word_add y (word c)) in
        (dest := (z:N word) ,,
         ZF := (val z = 0) ,,
         SF := (ival z < &0) ,,
         PF := word_evenparity(word_zx z:byte) ,,
         CF := ~(&(val x) - (&(val y) + &c):int = &(val z)) ,,
         OF := ~(ival x - (ival y + &c) = ival z) ,,
         AF := ~(&(val(word_zx x:nybble)) -
                 (&(val(word_zx y:nybble)) + &c):int =
                 &(val(word_zx z:nybble)))) s`;;

(*** Note: SET is only ever applied to 8-bit operands, so we build
 *** this into the type, in contrast to most of the other cases where
 *** this is generic
 ***)

let x86_SET = new_definition
 `x86_SET cc dest s =
          (dest := (if condition_semantics cc s then
                    word 1:byte else word 0)) s`;;

let x86_SHL = new_definition
 `x86_SHL dest c s =
      let x = read dest s in
      let z = word_shl x c in
      (dest := (z:N word) ,,
       ZF := (if c = 0 then read ZF s else val z = 0) ,,
       SF := (if c = 0 then read SF s else ival z < &0) ,,
       PF := (if c = 0 then read PF s else word_evenparity(word_zx z:byte)) ,,
       CF := (if c = 0 then read CF s
              else bit (dimindex(:N)-1) (word_shl x (c - 1))) ,,
       (if c = 0 then
          OF := read OF s
        else if c = 1 then
          OF := ~(bit (dimindex(:N)-1) x = bit (dimindex(:N)-2) x)
        else UNDEFINED_VALUES[OF]) ,,
       (if c = 0 then
          AF := read AF s
        else UNDEFINED_VALUES[AF])) s`;;

let x86_SHLD = new_definition
 `x86_SHLD dest src c s =
      let h:N word = read dest s
      and l:N word = read src s in
      let concat:(N tybit0)word = word_join h l in
      let z:N word = word_subword concat (dimindex(:N) - c,dimindex(:N)) in
      (dest := (z:N word) ,,
       ZF := (if c = 0 then read ZF s else val z = 0) ,,
       SF := (if c = 0 then read SF s else ival z < &0) ,,
       PF := (if c = 0 then read PF s else word_evenparity(word_zx z:byte)) ,,
       CF := (if c = 0 then read CF s else bit (dimindex(:N) - c) h) ,,
       (if c = 0 then
          OF := read OF s
        else if c = 1 then
          OF := ~(bit (dimindex(:N)-1) z = bit (dimindex(:N)-1) h)
        else UNDEFINED_VALUES[OF]) ,,
       (if c = 0 then
          AF := read AF s
        else UNDEFINED_VALUES[AF])) s`;;

let x86_SHR = new_definition
 `x86_SHR dest c s =
      let x = read dest s in
      let z = word_ushr x c in
      (dest := (z:N word) ,,
       ZF := (if c = 0 then read ZF s else val z = 0) ,,
       SF := (if c = 0 then read SF s else ival z < &0) ,,
       PF := (if c = 0 then read PF s else word_evenparity(word_zx z:byte)) ,,
       CF := (if c = 0 then read CF s else bit 0 (word_ushr x (c - 1))) ,,
       (if c = 0 then
          OF := read OF s
        else if c = 1 then
          OF := bit (dimindex(:N)-1) x
        else UNDEFINED_VALUES[OF]) ,,
       (if c = 0 then
          AF := read AF s
        else UNDEFINED_VALUES[AF])) s`;;

let x86_SHRD = new_definition
 `x86_SHRD dest src c s =
      let h:N word = read src s
      and l:N word = read dest s in
      let concat:(N tybit0)word = word_join h l in
      let z:N word = word_subword concat (c,dimindex(:N)) in
      (dest := (z:N word) ,,
       ZF := (if c = 0 then read ZF s else val z = 0) ,,
       SF := (if c = 0 then read SF s else ival z < &0) ,,
       PF := (if c = 0 then read PF s else word_evenparity(word_zx z:byte)) ,,
       CF := (if c = 0 then read CF s else bit (c - 1) l) ,,
       (if c = 0 then
          OF := read OF s
        else if c = 1 then
          OF := ~(bit (dimindex(:N)-1) z = bit (dimindex(:N)-1) l)
        else UNDEFINED_VALUES[OF]) ,,
       (if c = 0 then
          AF := read AF s
        else UNDEFINED_VALUES[AF])) s`;;

let x86_STC = new_definition
 `x86_STC s =
        (CF := T) s`;;

let x86_SUB = new_definition
 `x86_SUB dest src s =
        let x = read dest s and y = read src s in
        let z = word_sub x y in
        (dest := (z:N word) ,,
         ZF := (val z = 0) ,,
         SF := (ival z < &0) ,,
         PF := word_evenparity(word_zx z:byte) ,,
         CF := ~(&(val x) - &(val y):int = &(val z)) ,,
         OF := ~(ival x - ival y = ival z) ,,
         AF := ~(&(val(word_zx x:nybble)) - &(val(word_zx y:nybble)):int =
                 &(val(word_zx z:nybble)))) s`;;

(*** This is roughly AND just for some condition codes ***)

let x86_TEST = new_definition
 `x86_TEST dest src s =
        let x = read dest s and y = read src s in
        let z = word_and x y in
        (ZF := (val z = 0) ,,
         SF := (ival z < &0) ,,
         PF := word_evenparity(word_zx z:byte) ,,
         CF := F ,,
         OF := F ,,
         UNDEFINED_VALUES[AF]) s`;;

let x86_TZCNT = new_definition
 `x86_TZCNT dest src s =
        let x:N word = read src s in
        let z:N word = word(word_ctz x) in
        (dest := (z:N word) ,,
         CF := (val x = 0) ,,
         ZF := (val z = 0) ,,
         UNDEFINED_VALUES[OF;SF;PF;AF]) s`;;

let x86_VPXOR = new_definition
 `x86_VPXOR dest src1 src2 (s:x86state) =
        let x = read src1 s
        and y = read src2 s in
        let z = word_xor x y in
        (dest := (z:N word)) s`;;

(* Only deal with register-register exchange *)
let x86_XCHG = new_definition
 `x86_XCHG dest src s =
    let temp = read dest s in
    (dest := read src s ,, src := temp) s`;;

let x86_XOR = new_definition
 `x86_XOR dest src s =
        let x = read dest s and y = read src s in
        let z = word_xor x y in
        (dest := (z:N word) ,,
         ZF := (val z = 0) ,,
         SF := (ival z < &0) ,,
         PF := word_evenparity(word_zx z:byte) ,,
         CF := F ,,
         OF := F ,,
         UNDEFINED_VALUES[AF]) s`;;

(* ------------------------------------------------------------------------- *)
(* State components of various sizes corresponding to GPRs.                  *)
(* We also have a generic one "GPR" mapping to a number in all cases.        *)
(* ------------------------------------------------------------------------- *)

let GPR8 = define
 `GPR8 (Gpr reg Upper_8) =
        registers :> element reg :> bottom_32 :> bottom_16 :> top_8  /\
  GPR8 (Gpr reg Lower_8) =
        registers :> element reg :> bottom_32 :> bottom_16 :> bottom_8 `;;

let GPR16 = define
 `GPR16 (Gpr reg Lower_16) =
        registers :> element reg :> bottom_32 :> bottom_16`;;

let GPR32 = define
 `GPR32 (Gpr reg Lower_32) = registers :> element reg :> bottom_32`;;

(*** This is the behavior in 64-bit mode. ***)

let GPR32_Z = define
 `GPR32_Z (Gpr reg Lower_32) = registers :> element reg :> zerotop_32`;;

let GPR64 = define
 `GPR64 (Gpr reg Full_64) = registers :> element reg`;;

let GPR = define
  `GPR (Gpr reg Full_64) =
        registers :> element reg :> asnumber /\
   GPR (Gpr reg Lower_32) =
        registers :> element reg :> bottom_32 :> asnumber /\
   GPR (Gpr reg Lower_16) =
        registers :> element reg :> bottom_32 :> bottom_16 :> asnumber /\
   GPR (Gpr reg Upper_8) =
        registers :> element reg :>
            bottom_32 :> bottom_16 :> top_8 :> asnumber /\
   GPR (Gpr reg Lower_8) =
        registers :> element reg :>
            bottom_32 :> bottom_16 :> bottom_8 :> asnumber`;;

(*** The zero-top-on-write behavior when VEX-encoded, which we assume ***)

let SIMD256 = define
 `SIMD256 (Simdreg reg Lower_256) =
      simdregisters :> element reg :> zerotop_256`;;

let SIMD128 = define
 `SIMD128 (Simdreg reg Lower_128) =
    simdregisters :> element reg :> zerotop_256 :> zerotop_128`;;

let SIMD128_SSE = define
 `SIMD128_SSE (Simdreg reg Lower_128) =
    simdregisters :> element reg :> bottom_256 :> bottom_128`;;

(* ------------------------------------------------------------------------- *)
(* Decoding of a bsid address, always returning a 64-bit word.               *)
(* ------------------------------------------------------------------------- *)

let bsid_semantics = define
 `bsid_semantics(Bsid obase oind scl disp) s =
   (let bv = match obase with SOME base -> read (GPR base) s | NONE -> 0
    and iv = match oind with SOME ind -> read (GPR ind) s | NONE -> 0 in
    word(bv + 2 EXP (val scl) * iv + val disp):64 word) /\
  bsid_semantics(Riprel off) s = word(val(read RIP s) + val off)`;;

(* ------------------------------------------------------------------------- *)
(* Translate an operand to a state component of given size.                  *)
(* Generally, the only "type casts" we want are for immediates,              *)
(* which are always sign-extended. Leave other things undefined.             *)
(* Note: this is in 64-bit mode only. Of course things are different in      *)
(* other modes; particularly the "zerotop" stuff does not apply then.        *)
(* ------------------------------------------------------------------------- *)

let OPERAND256 = define
 `OPERAND256 (Simdregister r) s =
        (if simdregister_size r = 256 then SIMD256 r else ARB) /\
  OPERAND256 (Memop w ea) s =
       (if w = Word256 then memory :> bytes256 (bsid_semantics ea s)
        else ARB)`;;

let OPERAND128 = define
 `OPERAND128 (Simdregister r) s =
        (if simdregister_size r = 128 then SIMD128 r else ARB) /\
  OPERAND128 (Memop w ea) s =
       (if w = Word128 then memory :> bytes128 (bsid_semantics ea s)
        else ARB)`;;

let OPERAND128_SSE = define
 `OPERAND128_SSE (Simdregister r) s =
        (if simdregister_size r = 128 then SIMD128_SSE r else ARB) /\
  OPERAND128_SSE (Memop w ea) s =
       (if w = Word128 then memory :> bytes128 (bsid_semantics ea s)
        else ARB)`;;

let OPERAND64 = define
 `OPERAND64 (Register r) s =
        (if register_size r = 64 then GPR64 r else ARB) /\
  OPERAND64 (Imm8 imm8) s = rvalue(word_sx imm8) /\
  OPERAND64 (Imm16 imm16) s = rvalue(word_sx imm16) /\
  OPERAND64 (Imm32 imm32) s = rvalue(word_sx imm32) /\
  OPERAND64 (Imm64 imm64) s = rvalue imm64 /\
  OPERAND64 (Memop w ea) s =
       (if w = Quadword then memory :> bytes64 (bsid_semantics ea s)
        else ARB)`;;

let OPERAND32 = define
 `OPERAND32 (Register r) s =
        (if register_size r = 32 then GPR32_Z r else ARB) /\
  OPERAND32 (Imm8 imm8) s = rvalue(word_sx imm8) /\
  OPERAND32 (Imm16 imm16) s = rvalue(word_sx imm16) /\
  OPERAND32 (Imm32 imm32) s = rvalue imm32 /\
  OPERAND32 (Memop w ea) s =
       (if w = Doubleword then memory :> bytes32 (bsid_semantics ea s)
        else ARB)`;;

let OPERAND16 = define
 `OPERAND16 (Register r) s =
        (if register_size r = 16 then GPR16 r else ARB) /\
  OPERAND16 (Imm8 imm8) s = rvalue(word_sx imm8) /\
  OPERAND16 (Imm16 imm16) s = rvalue imm16 /\
  OPERAND16 (Memop w ea) s =
       (if w = Word then memory :> bytes16 (bsid_semantics ea s)
        else ARB)`;;

let OPERAND8 = define
 `OPERAND8 (Register r) s =
        (if register_size r = 8 then GPR8 r else ARB) /\
  OPERAND8 (Imm8 imm8) s = rvalue imm8 /\
  OPERAND8 (Memop w ea) s =
       (if w = Byte then memory :> bytes8 (bsid_semantics ea s)
        else ARB)`;;

let aligned_OPERAND128 = define
 `(aligned_OPERAND128 (Simdregister r) s <=> T) /\
  (aligned_OPERAND128 (Memop w ea) s <=> aligned 16 (bsid_semantics ea s))`;;

(* ------------------------------------------------------------------------- *)
(* Stating assumptions about instruction decoding                            *)
(* ------------------------------------------------------------------------- *)

let x86_decode = new_definition `x86_decode s pc (len,inst) <=>
  ?l. bytes_loaded s pc l /\ LENGTH l = len /\ decode l = SOME (inst, [])`;;

let X86_DECODE_CONS = prove
 (`!s pc l i l' n.
   bytes_loaded s (word pc) l ==> decode_len l (n,i) l' ==>
   x86_decode s (word pc) (n,i) /\ bytes_loaded s (word (pc + n)) l'`,
  REPEAT GEN_TAC THEN DISCH_THEN (fun bl -> DISCH_THEN (fun th ->
    let th1,th2 = CONJ_PAIR (REWRITE_RULE [decode_len] th) in
    let th1 = MATCH_MP
      (REWRITE_RULE [list_linear_f; list_linear] list_linear_decode) th1 in
    C CHOOSE_THEN th1 (fun th ->
      let th3,th4 = CONJ_PAIR th in
      REWRITE_TAC [SYM (REWRITE_RULE [EQ_ADD_LCANCEL]
        (CONV_RULE (LAND_CONV (ONCE_REWRITE_CONV [ADD_SYM]))
          ((REWRITE_RULE [th3; LENGTH_APPEND] th2))))] THEN
      let bl1,bl2 = CONJ_PAIR (REWRITE_RULE [th3; bytes_loaded_append] bl) in
      REWRITE_TAC [x86_decode; WORD_ADD; bl2] THEN
      EXISTS_TAC `l'':byte list` THEN REWRITE_TAC [bl1;
        REWRITE_RULE [APPEND_NIL] (SPEC `[]:byte list` th4)]))));;

let x86_decode_unique = prove
 (`!s pc x y. x86_decode s pc x ==> x86_decode s pc y ==> x = y`,
  REWRITE_TAC [FORALL_PAIR_THM; x86_decode] THEN REPEAT GEN_TAC THEN
  SPECL_TAC [`p1:num`; `p1':num`; `p2:instruction`; `p2':instruction`] THEN
  MATCH_MP_TAC WLOG_LE THEN CONJ_TAC THENL [METIS_TAC []; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  POP_ASSUM_LIST (fun [d2;l2;b2; d1;l1;b1; h] ->
    let th = MATCH_MP exists_list_split (REWRITE_RULE [SYM l2] h) in
    REPEAT_TCL CHOOSE_THEN (fun th ->
      let th1,th2 = CONJ_PAIR th in
      let th3,th4 = CONJ_PAIR (REWRITE_RULE [th1; bytes_loaded_append] b2) in
      let th = MP (MATCH_MP (MATCH_MP bytes_loaded_unique b1) th3)
        (TRANS l1 (SYM th2)) in
      let d1 = REWRITE_RULE [th; APPEND_NIL; UNWIND_THM1] (MATCH_MP
        (REWRITE_RULE [list_linear_f; list_linear] list_linear_decode) d1) in
      let d2 = REWRITE_RULE [th1; d1; OPTION_INJ; PAIR_EQ] d2 in
      REWRITE_TAC [d2;
        REWRITE_RULE [th1; d2; APPEND_NIL; SYM th; l1] l2]) th));;

let X86_DECODES_THM =
  let pth = (UNDISCH_ALL o prove)
   (`i = i' ==> pc + n = pc' ==>
     bytes_loaded s (word pc) l ==> decode_len l (n,i) l' ==>
     x86_decode s (word pc) (n,i') /\ bytes_loaded s (word pc') l'`,
    REPEAT (DISCH_THEN (SUBST1_TAC o SYM)) THEN
    MATCH_ACCEPT_TAC X86_DECODE_CONS)
  and pth_pc = (UNDISCH o ARITH_RULE) `n + m:num = p ==> (pc + n) + m = pc + p`
  and ei,ei' = `i:instruction`,`i':instruction`
  and pl,el,el' = `(+):num->num->num`,`l:byte list`,`l':byte list`
  and en,em,ep,epc,epc' = `n:num`,`m:num`,`p:num`,`pc:num`,`pc':num` in
  (* go returns a list of pairs of x86_decode theorem and its PC offset. *)
  let rec go th =
    let l = rand (concl th) in
    let th1 = DECODE_LEN_THM l in
    let (n,i),l' = (dest_pair o rand F_F I) (dest_comb (concl th1)) in
    let th2 = REWRITE_CONV X86_INSTRUCTION_ALIASES i in
    let i' = rhs (concl th2) in
    let pc = rand (lhand (concl th)) in
    let th3,pcofs = match pc with
    | Comb(Comb(Const("+",_),pc),a) ->
      let th = NUM_ADD_CONV (mk_comb (mk_comb (pl, a), n)) in
      PROVE_HYP th (INST [pc,epc; a,en; n,em; rhs (concl th),ep] pth_pc),a
    | _ -> REFL (mk_comb (mk_comb (pl, pc), n)),`0` in
    let pc' = rhs (concl th3) in
    let th' = (PROVE_HYP th2 o PROVE_HYP th3 o PROVE_HYP th o PROVE_HYP th1)
      (INST [i,ei; i',ei'; pc,epc; n,en; pc',epc'; l,el; l',el'] pth) in
    match l' with
    | Const("NIL",_) -> [CONJUNCT1 th',pcofs]
    | _ -> let dth,bth = CONJ_PAIR th' in (dth,pcofs)::(go bth) in
  fun th ->
    let decodes:(thm*term) list = (go o
      (fun dth -> EQ_MP dth (ASSUME (lhs (concl dth)))) o
      AP_TERM `bytes_loaded s (word pc)`) th in
    map (fun th,pcofs -> ((GENL [`s:x86state`; `pc:num`] o DISCH_ALL) th, pcofs))
      decodes;;

let X86_MK_EXEC_RULE th0 =
  let th0 = INST [`pc':num`,`pc:num`] (SPEC_ALL th0) in
  let th1 = AP_TERM `LENGTH:byte list->num` th0 in
  let th2 =
    (REWRITE_CONV [LENGTH_BYTELIST_OF_NUM; LENGTH_BYTELIST_OF_INT;
      LENGTH; LENGTH_APPEND] THENC NUM_REDUCE_CONV) (rhs (concl th1)) in
  (* Length *)
  let execth1 = TRANS th1 th2 in
  (* Decode *)
  let execth2_raw:(thm*term) list = X86_DECODES_THM th0 in
  let (decode_arr:thm option array) = Array.make
    (dest_small_numeral (snd (dest_eq (concl execth1)))) None in
  let _ = List.iter (fun decode_th,pcofs ->
    decode_arr.(dest_small_numeral pcofs) <- Some decode_th)
    execth2_raw in
  (execth1,decode_arr);;

(* ------------------------------------------------------------------------- *)
(* Execution of a single instruction.                                        *)
(* ------------------------------------------------------------------------- *)

(*** note that this is in 64-bit mode (e.g. matters for ROL masking) ***)

(*** We also only support relative jump  at the moment ***)

let x86_execute = define
 `x86_execute instr s =
    match instr with
      ADC dest src ->
        (match operand_size dest with
           64 -> x86_ADC (OPERAND64 dest s) (OPERAND64 src s)
         | 32 -> x86_ADC (OPERAND32 dest s) (OPERAND32 src s)
         | 16 -> x86_ADC (OPERAND16 dest s) (OPERAND16 src s)
         | 8 -> x86_ADC (OPERAND8 dest s) (OPERAND8 src s)) s
    | ADCX dest src ->
        (match operand_size dest with
           64 -> x86_ADCX (OPERAND64 dest s) (OPERAND64 src s)
         | 32 -> x86_ADCX (OPERAND32 dest s) (OPERAND32 src s)) s
    | ADD dest src ->
        (match operand_size dest with
           64 -> x86_ADD (OPERAND64 dest s) (OPERAND64 src s)
         | 32 -> x86_ADD (OPERAND32 dest s) (OPERAND32 src s)
         | 16 -> x86_ADD (OPERAND16 dest s) (OPERAND16 src s)
         | 8 -> x86_ADD (OPERAND8 dest s) (OPERAND8 src s)) s
    | ADOX dest src ->
        (match operand_size dest with
           64 -> x86_ADOX (OPERAND64 dest s) (OPERAND64 src s)
         | 32 -> x86_ADOX (OPERAND32 dest s) (OPERAND32 src s)) s
    | AESDEC dest src ->
        x86_AESDEC (OPERAND128_SSE dest s) (OPERAND128_SSE src s) s
    | AESDECLAST dest src ->
        x86_AESDECLAST (OPERAND128_SSE dest s) (OPERAND128_SSE src s) s
    | AESENC dest src ->
        x86_AESENC (OPERAND128_SSE dest s) (OPERAND128_SSE src s) s
    | AESENCLAST dest src ->
        x86_AESENCLAST (OPERAND128_SSE dest s) (OPERAND128_SSE src s) s
    | AESKEYGENASSIST dest src imm8 ->
        x86_AESKEYGENASSIST (OPERAND128_SSE dest s) (OPERAND128_SSE src s) (OPERAND8 imm8 s) s
    | AND dest src ->
        (match operand_size dest with
           64 -> x86_AND (OPERAND64 dest s) (OPERAND64 src s)
         | 32 -> x86_AND (OPERAND32 dest s) (OPERAND32 src s)
         | 16 -> x86_AND (OPERAND16 dest s) (OPERAND16 src s)
         | 8 -> x86_AND (OPERAND8 dest s) (OPERAND8 src s)) s
    | BSF dest src ->
        (match operand_size dest with
           64 -> x86_BSF (OPERAND64 dest s) (OPERAND64 src s)
         | 32 -> x86_BSF (OPERAND32 dest s) (OPERAND32 src s)
         | 16 -> x86_BSF (OPERAND16 dest s) (OPERAND16 src s)) s
    | BSR dest src ->
        (match operand_size dest with
           64 -> x86_BSR (OPERAND64 dest s) (OPERAND64 src s)
         | 32 -> x86_BSR (OPERAND32 dest s) (OPERAND32 src s)
         | 16 -> x86_BSR (OPERAND16 dest s) (OPERAND16 src s)) s
    | BSWAP dest ->
        (match operand_size dest with
           64 -> x86_BSWAP (OPERAND64 dest s)
         | 32 -> x86_BSWAP (OPERAND32 dest s)) s
    | BT dest src ->
        (match operand_size dest with
           64 -> x86_BT (OPERAND64 dest s) (OPERAND64 src s)
         | 32 -> x86_BT (OPERAND32 dest s) (OPERAND32 src s)
         | 16 -> x86_BT (OPERAND16 dest s) (OPERAND16 src s)
         | 8 -> x86_BT (OPERAND8 dest s) (OPERAND8 src s)) s
    | BTC dest src ->
        (match operand_size dest with
           64 -> x86_BTC (OPERAND64 dest s) (OPERAND64 src s)
         | 32 -> x86_BTC (OPERAND32 dest s) (OPERAND32 src s)
         | 16 -> x86_BTC (OPERAND16 dest s) (OPERAND16 src s)
         | 8 -> x86_BTC (OPERAND8 dest s) (OPERAND8 src s)) s
    | BTR dest src ->
        (match operand_size dest with
           64 -> x86_BTR (OPERAND64 dest s) (OPERAND64 src s)
         | 32 -> x86_BTR (OPERAND32 dest s) (OPERAND32 src s)
         | 16 -> x86_BTR (OPERAND16 dest s) (OPERAND16 src s)
         | 8 -> x86_BTR (OPERAND8 dest s) (OPERAND8 src s)) s
    | BTS dest src ->
        (match operand_size dest with
           64 -> x86_BTS (OPERAND64 dest s) (OPERAND64 src s)
         | 32 -> x86_BTS (OPERAND32 dest s) (OPERAND32 src s)
         | 16 -> x86_BTS (OPERAND16 dest s) (OPERAND16 src s)
         | 8 -> x86_BTS (OPERAND8 dest s) (OPERAND8 src s)) s
    | CALL off ->
        (let ip' = word_add (read RIP s)
                            (read (OPERAND64 off s) s) in
         x86_CALL ip' s)
    | CALL_ABSOLUTE target ->
        x86_CALL target s
    | CLC ->
        x86_CLC s
    | CMC ->
        x86_CMC s
    | CMOV cc dest src ->
        (match operand_size dest with
           64 -> x86_CMOV cc (OPERAND64 dest s) (OPERAND64 src s)
         | 32 -> x86_CMOV cc (OPERAND32 dest s) (OPERAND32 src s)
         | 16 -> x86_CMOV cc (OPERAND16 dest s) (OPERAND16 src s)
         | 8 -> x86_CMOV cc (OPERAND8 dest s) (OPERAND8 src s)) s
    | CMP dest src ->
        (match operand_size dest with
           64 -> x86_CMP (OPERAND64 dest s) (OPERAND64 src s)
         | 32 -> x86_CMP (OPERAND32 dest s) (OPERAND32 src s)
         | 16 -> x86_CMP (OPERAND16 dest s) (OPERAND16 src s)
         | 8 -> x86_CMP (OPERAND8 dest s) (OPERAND8 src s)) s
    | DEC dest ->
        (match operand_size dest with
           64 -> x86_DEC (OPERAND64 dest s)
         | 32 -> x86_DEC (OPERAND32 dest s)
         | 16 -> x86_DEC (OPERAND16 dest s)
         | 8 -> x86_DEC (OPERAND8 dest s)) s
    | DIV2 (dest1,dest2) (src1,src2) src3 ->
        (match operand_size dest1 with
           64 -> x86_DIV2 (OPERAND64 dest1 s,OPERAND64 dest2 s)
                          (OPERAND64 src1 s,OPERAND64 src2 s)
                          (OPERAND64 src3 s)
         | 32 -> x86_DIV2 (OPERAND32 dest1 s,OPERAND32 dest2 s)
                          (OPERAND32 src1 s,OPERAND32 src2 s)
                          (OPERAND32 src3 s)
         | 16 -> x86_DIV2 (OPERAND16 dest1 s,OPERAND16 dest2 s)
                          (OPERAND16 src1 s,OPERAND16 src2 s)
                          (OPERAND16 src3 s)
         | 8 -> x86_DIV2 (OPERAND8 dest1 s,OPERAND8 dest2 s)
                         (OPERAND8 src1 s,OPERAND8 src2 s)
                         (OPERAND8 src3 s)) s
    | ENDBR64 ->
        x86_ENDBR64 s
    | IMUL3 dest (src1,src2) ->
        (match operand_size dest with
           64 -> x86_IMUL3 (OPERAND64 dest s)
                           (OPERAND64 src1 s,OPERAND64 src2 s)
         | 32 -> x86_IMUL3 (OPERAND32 dest s)
                           (OPERAND32 src1 s, OPERAND32 src2 s)
         | 16 -> x86_IMUL3 (OPERAND16 dest s)
                           (OPERAND16 src1 s,OPERAND16 src2 s)
         | 8 -> x86_IMUL3 (OPERAND8 dest s)
                          (OPERAND8 src1 s,OPERAND8 src2 s)) s
    | IMUL2 (dest1,dest2) src ->
        (match operand_size dest2 with
           64 -> x86_IMUL2 (OPERAND64 dest1 s,OPERAND64 dest2 s)
                          (OPERAND64 src s)
         | 32 -> x86_IMUL2 (OPERAND32 dest1 s,OPERAND32 dest2 s)
                          (OPERAND32 src s)
         | 16 -> x86_IMUL2 (OPERAND16 dest1 s,OPERAND16 dest2 s)
                          (OPERAND16 src s)
         | 8 -> x86_IMUL2 (OPERAND8 dest1 s,OPERAND8 dest2 s)
                          (OPERAND8 src s)) s
    | INC dest ->
        (match operand_size dest with
           64 -> x86_INC (OPERAND64 dest s)
         | 32 -> x86_INC (OPERAND32 dest s)
         | 16 -> x86_INC (OPERAND16 dest s)
         | 8 -> x86_INC (OPERAND8 dest s)) s
    | JUMP cc off ->
        (RIP :=
           if condition_semantics cc s
           then word_add (read RIP s)
                         (read (OPERAND64 off s) s)
           else read RIP s) s
    | LEA dest bsid ->
        (match operand_size dest with
          64 -> (OPERAND64 dest s) := (bsid_semantics bsid s)
        | 32 -> (OPERAND32 dest s) := word_sx(bsid_semantics bsid s)
        | 16 -> (OPERAND16 dest s) := word_sx(bsid_semantics bsid s)
        | 8 -> (OPERAND8 dest s) := word_sx(bsid_semantics bsid s)) s
    | LZCNT dest src ->
        (match operand_size dest with
           64 -> x86_LZCNT (OPERAND64 dest s) (OPERAND64 src s)
         | 32 -> x86_LZCNT (OPERAND32 dest s) (OPERAND32 src s)
         | 16 -> x86_LZCNT (OPERAND16 dest s) (OPERAND16 src s)) s
    | MOV dest src ->
        (match operand_size dest with
           64 -> x86_MOV (OPERAND64 dest s) (OPERAND64 src s)
         | 32 -> x86_MOV (OPERAND32 dest s) (OPERAND32 src s)
         | 16 -> x86_MOV (OPERAND16 dest s) (OPERAND16 src s)
         | 8 -> x86_MOV (OPERAND8 dest s) (OPERAND8 src s)) s
    | MOVAPS dest src ->
        if aligned_OPERAND128 src s /\ aligned_OPERAND128 dest s
        then x86_MOVAPS (OPERAND128_SSE dest s) (OPERAND128_SSE src s) s
        else (\s'. F)
    | MOVDQA dest src ->
        if aligned_OPERAND128 src s /\ aligned_OPERAND128 dest s
        then x86_MOVDQA (OPERAND128_SSE dest s) (OPERAND128_SSE src s) s
        else (\s'. F)
    | MOVDQU dest src ->
        x86_MOVDQU (OPERAND128_SSE dest s) (OPERAND128_SSE src s) s
    | MOVSX dest src ->
        (match (operand_size dest,operand_size src) with
           (64,32) -> x86_MOVSX (OPERAND64 dest s) (OPERAND32 src s)
         | (64,16) -> x86_MOVSX (OPERAND64 dest s) (OPERAND16 src s)
         | (64,8) -> x86_MOVSX (OPERAND64 dest s) (OPERAND8 src s)
         | (32,32) -> x86_MOVSX (OPERAND32 dest s) (OPERAND32 src s)
         | (32,16) -> x86_MOVSX (OPERAND32 dest s) (OPERAND16 src s)
         | (32,8) -> x86_MOVSX (OPERAND32 dest s) (OPERAND8 src s)
         | (16,8) -> x86_MOVSX (OPERAND16 dest s) (OPERAND8 src s)) s
    | MOVUPS dest src ->
         x86_MOVUPS (OPERAND128_SSE dest s) (OPERAND128_SSE src s) s
    | MOVZX dest src ->
        (match (operand_size dest,operand_size src) with
           (64,16) -> x86_MOVZX (OPERAND64 dest s) (OPERAND16 src s)
         | (64,8) -> x86_MOVZX (OPERAND64 dest s) (OPERAND8 src s)
         | (32,16) -> x86_MOVZX (OPERAND32 dest s) (OPERAND16 src s)
         | (32,8) -> x86_MOVZX (OPERAND32 dest s) (OPERAND8 src s)
         | (16,8) -> x86_MOVZX (OPERAND16 dest s) (OPERAND8 src s)) s
    | MUL2 (dest1,dest2) src ->
        (match operand_size dest2 with
           64 -> x86_MUL2 (OPERAND64 dest1 s,OPERAND64 dest2 s)
                         (OPERAND64 src s)
         | 32 -> x86_MUL2 (OPERAND32 dest1 s,OPERAND32 dest2 s)
                         (OPERAND32 src s)
         | 16 -> x86_MUL2 (OPERAND16 dest1 s,OPERAND16 dest2 s)
                         (OPERAND16 src s)
         | 8 -> x86_MUL2 (OPERAND8 dest1 s,OPERAND8 dest2 s)
                         (OPERAND8 src s)) s
    | MULX4 (dest1,dest2) (src1,src2) ->
        (match operand_size dest2 with
           64 -> x86_MULX4 (OPERAND64 dest1 s,OPERAND64 dest2 s)
                           (OPERAND64 src1 s,OPERAND64 src2 s)
         | 32 -> x86_MULX4 (OPERAND32 dest1 s,OPERAND32 dest2 s)
                           (OPERAND32 src1 s,OPERAND32 src2 s)) s
    | NEG dest ->
        (match operand_size dest with
           64 -> x86_NEG (OPERAND64 dest s)
         | 32 -> x86_NEG (OPERAND32 dest s)
         | 16 -> x86_NEG (OPERAND16 dest s)
         | 8 -> x86_NEG (OPERAND8 dest s)) s
    | NOP ->
        x86_NOP s
    | NOP_N dest ->
        (match operand_size dest with
           32 -> x86_NOP_N (OPERAND32 dest s)
         | 16 -> x86_NOP_N (OPERAND16 dest s)) s
    | NOT dest ->
        (match operand_size dest with
           64 -> x86_NOT (OPERAND64 dest s)
         | 32 -> x86_NOT (OPERAND32 dest s)
         | 16 -> x86_NOT (OPERAND16 dest s)
         | 8 -> x86_NOT (OPERAND8 dest s)) s
    | OR dest src ->
        (match operand_size dest with
           64 -> x86_OR (OPERAND64 dest s) (OPERAND64 src s)
         | 32 -> x86_OR (OPERAND32 dest s) (OPERAND32 src s)
         | 16 -> x86_OR (OPERAND16 dest s) (OPERAND16 src s)
         | 8 -> x86_OR (OPERAND8 dest s) (OPERAND8 src s)) s
    | PADDD dest src ->
        x86_PADDD (OPERAND128_SSE dest s) (OPERAND128_SSE src s) s
    | PADDQ dest src ->
        x86_PADDQ (OPERAND128_SSE dest s) (OPERAND128_SSE src s) s
    | PAND dest src ->
        x86_PAND (OPERAND128_SSE dest s) (OPERAND128_SSE src s) s
    | PCMPGTD dest src ->
        x86_PCMPGTD (OPERAND128_SSE dest s) (OPERAND128_SSE src s) s
    | POP dest ->
        (match operand_size dest with
           64 -> x86_POP (OPERAND64 dest s)
         | 16 -> x86_POP (OPERAND16 dest s)) s
    | PSHUFD dest src imm8 ->
        x86_PSHUFD (OPERAND128_SSE dest s) (OPERAND128_SSE src s) (OPERAND8 imm8 s) s
    | PSRAD dest imm8 ->
        x86_PSRAD (OPERAND128_SSE dest s) (OPERAND8 imm8 s) s
    | PUSH src ->
        (match operand_size src with
           64 -> x86_PUSH (OPERAND64 src s)
         | 16 -> x86_PUSH (OPERAND16 src s)) s
    | PXOR dest src ->
        x86_PXOR (OPERAND128_SSE dest s) (OPERAND128_SSE src s) s
    | RCL dest src ->
        (match operand_size dest with
           64 -> x86_RCL (OPERAND64 dest s)
                         (val(read (OPERAND8 src s) s) MOD 64)
         | 32 -> x86_RCL (OPERAND32 dest s)
                        (val(read (OPERAND8 src s) s) MOD 32)
         | 16 -> x86_RCL (OPERAND16 dest s)
                        (val(read (OPERAND8 src s) s) MOD 32)
         | 8 -> x86_RCL (OPERAND8 dest s)
                        (val(read (OPERAND8 src s) s) MOD 32)) s
    | RCR dest src ->
        (match operand_size dest with
           64 -> x86_RCR (OPERAND64 dest s)
                        (val(read (OPERAND8 src s) s) MOD 64)
         | 32 -> x86_RCR (OPERAND32 dest s)
                        (val(read (OPERAND8 src s) s) MOD 32)
         | 16 -> x86_RCR (OPERAND16 dest s)
                        (val(read (OPERAND8 src s) s) MOD 32)
         | 8 -> x86_RCR (OPERAND8 dest s)
                        (val(read (OPERAND8 src s) s) MOD 32)) s
    | RET ->
        x86_RET s
    | ROL dest src ->
        (match operand_size dest with
           64 -> x86_ROL (OPERAND64 dest s)
                         (val(read (OPERAND8 src s) s) MOD 64)
         | 32 -> x86_ROL (OPERAND32 dest s)
                        (val(read (OPERAND8 src s) s) MOD 32)
         | 16 -> x86_ROL (OPERAND16 dest s)
                        (val(read (OPERAND8 src s) s) MOD 32)
         | 8 -> x86_ROL (OPERAND8 dest s)
                        (val(read (OPERAND8 src s) s) MOD 32)) s
    | ROR dest src ->
        (match operand_size dest with
           64 -> x86_ROR (OPERAND64 dest s)
                        (val(read (OPERAND8 src s) s) MOD 64)
         | 32 -> x86_ROR (OPERAND32 dest s)
                        (val(read (OPERAND8 src s) s) MOD 32)
         | 16 -> x86_ROR (OPERAND16 dest s)
                        (val(read (OPERAND8 src s) s) MOD 32)
         | 8 -> x86_ROR (OPERAND8 dest s)
                        (val(read (OPERAND8 src s) s) MOD 32)) s
    | SAR dest src ->
        (match operand_size dest with
           64 -> x86_SAR (OPERAND64 dest s)
                        (val(read (OPERAND8 src s) s) MOD 64)
         | 32 -> x86_SAR (OPERAND32 dest s)
                        (val(read (OPERAND8 src s) s) MOD 32)
         | 16 -> x86_SAR (OPERAND16 dest s)
                        (val(read (OPERAND8 src s) s) MOD 32)
         | 8 -> x86_SAR (OPERAND8 dest s)
                        (val(read (OPERAND8 src s) s) MOD 32)) s
    | SBB dest src ->
        (match operand_size dest with
           64 -> x86_SBB (OPERAND64 dest s) (OPERAND64 src s)
         | 32 -> x86_SBB (OPERAND32 dest s) (OPERAND32 src s)
         | 16 -> x86_SBB (OPERAND16 dest s) (OPERAND16 src s)
         | 8 -> x86_SBB (OPERAND8 dest s) (OPERAND8 src s)) s
    | SET cc dest ->
        (match operand_size dest with
           8 -> x86_SET cc (OPERAND8 dest s)
         | _ -> ARB) s
    | SHL dest src ->
        (match operand_size dest with
           64 -> x86_SHL (OPERAND64 dest s)
                        (val(read (OPERAND8 src s) s) MOD 64)
         | 32 -> x86_SHL (OPERAND32 dest s)
                        (val(read (OPERAND8 src s) s) MOD 32)
         | 16 -> x86_SHL (OPERAND16 dest s)
                        (val(read (OPERAND8 src s) s) MOD 32)
         | 8 -> x86_SHL (OPERAND8 dest s)
                        (val(read (OPERAND8 src s) s) MOD 32)) s
    | SHLD dest src c ->
        (match operand_size dest with
           64 -> x86_SHLD (OPERAND64 dest s) (OPERAND64 src s)
                          (val(read (OPERAND8 c s) s) MOD 64)
         | 32 -> x86_SHLD (OPERAND32 dest s) (OPERAND32 src s)
                          (val(read (OPERAND8 c s) s) MOD 32)
         | 16 -> x86_SHLD (OPERAND16 dest s) (OPERAND16 src s)
                          (val(read (OPERAND8 c s) s) MOD 32)
         | 8 -> x86_SHLD (OPERAND8 dest s) (OPERAND8 src s)
                         (val(read (OPERAND8 c s) s) MOD 32)) s
    | SHR dest src ->
        (match operand_size dest with
           64 -> x86_SHR (OPERAND64 dest s)
                        (val(read (OPERAND8 src s) s) MOD 64)
         | 32 -> x86_SHR (OPERAND32 dest s)
                        (val(read (OPERAND8 src s) s) MOD 32)
         | 16 -> x86_SHR (OPERAND16 dest s)
                        (val(read (OPERAND8 src s) s) MOD 32)
         | 8 -> x86_SHR (OPERAND8 dest s)
                        (val(read (OPERAND8 src s) s) MOD 32)) s
    | SHRD dest src c ->
        (match operand_size dest with
           64 -> x86_SHRD (OPERAND64 dest s) (OPERAND64 src s)
                          (val(read (OPERAND8 c s) s) MOD 64)
         | 32 -> x86_SHRD (OPERAND32 dest s) (OPERAND32 src s)
                          (val(read (OPERAND8 c s) s) MOD 32)
         | 16 -> x86_SHRD (OPERAND16 dest s) (OPERAND16 src s)
                          (val(read (OPERAND8 c s) s) MOD 32)
         | 8 -> x86_SHRD (OPERAND8 dest s) (OPERAND8 src s)
                         (val(read (OPERAND8 c s) s) MOD 32)) s
    | STCF ->
        x86_STC s
    | SUB dest src ->
        (match operand_size dest with
           64 -> x86_SUB (OPERAND64 dest s) (OPERAND64 src s)
         | 32 -> x86_SUB (OPERAND32 dest s) (OPERAND32 src s)
         | 16 -> x86_SUB (OPERAND16 dest s) (OPERAND16 src s)
         | 8 -> x86_SUB (OPERAND8 dest s) (OPERAND8 src s)) s
    | TEST dest src ->
        (match operand_size dest with
           64 -> x86_TEST (OPERAND64 dest s) (OPERAND64 src s)
         | 32 -> x86_TEST (OPERAND32 dest s) (OPERAND32 src s)
         | 16 -> x86_TEST (OPERAND16 dest s) (OPERAND16 src s)
         | 8 -> x86_TEST (OPERAND8 dest s) (OPERAND8 src s)) s
    | TZCNT dest src ->
        (match operand_size dest with
           64 -> x86_TZCNT (OPERAND64 dest s) (OPERAND64 src s)
         | 32 -> x86_TZCNT (OPERAND32 dest s) (OPERAND32 src s)
         | 16 -> x86_TZCNT (OPERAND16 dest s) (OPERAND16 src s)) s
    | VPXOR dest src1 src2 ->
        (match operand_size dest with
          256 -> x86_VPXOR (OPERAND256 dest s) (OPERAND256 src1 s) (OPERAND256 src2 s)
        | 128 -> x86_VPXOR (OPERAND128 dest s) (OPERAND128 src1 s) (OPERAND128 src2 s)) s
    | XCHG dest src ->
        (match operand_size dest with
          64 -> x86_XCHG (OPERAND64 dest s) (OPERAND64 src s)
        | 32 -> x86_XCHG (OPERAND32 dest s) (OPERAND32 src s)
        | 16 -> x86_XCHG (OPERAND16 dest s) (OPERAND16 src s)
        | 8 -> x86_XCHG (OPERAND8 dest s) (OPERAND8 src s)) s
    | XOR dest src ->
        (match operand_size dest with
           64 -> x86_XOR (OPERAND64 dest s) (OPERAND64 src s)
         | 32 -> x86_XOR (OPERAND32 dest s) (OPERAND32 src s)
         | 16 -> x86_XOR (OPERAND16 dest s) (OPERAND16 src s)
         | 8 -> x86_XOR (OPERAND8 dest s) (OPERAND8 src s)) s
    | _ -> (\s'. F)`;;

(* ------------------------------------------------------------------------- *)
(* Now the basic fetch-decode-execute cycle.                                 *)
(* ------------------------------------------------------------------------- *)

(*** Note that we *always* increment the instruction pointer first. This is
 *** consistent with the fact that relative offsets in JMP, CALL are
 *** relative to the *next* instruction, so we can use current PC in
 *** the execution of control flow instructions.
 ***)

let x86 = define
 `x86 s s' <=>
    ?len instr. x86_decode s (read RIP s) (len,instr) /\
                (RIP := word_add (read RIP s) (word len) ,,
                x86_execute instr) s s'`;;

(* ------------------------------------------------------------------------- *)
(* Shorthand for the set of all flags for modification lists.                *)
(* ------------------------------------------------------------------------- *)

let SOME_FLAGS = new_definition
 `SOME_FLAGS = [CF; PF; AF; ZF; SF; OF]`;;

(* ------------------------------------------------------------------------- *)
(* Standard System V AMD64 ABI as used on modern Unix/Linux/Mac OS.          *)
(* ------------------------------------------------------------------------- *)

(*** This is for the "System V AMD64 ABI", i.e. modern unixes     ***)
(*** We don't talk about the stack or FP arguments yet            ***)

let C_ARGUMENTS = define
 `(C_ARGUMENTS [a1;a2;a3;a4;a5;a6] s <=>
        read RDI s = a1 /\ read RSI s = a2 /\ read RDX s = a3 /\
        read RCX s = a4 /\ read  R8 s = a5 /\ read  R9 s = a6) /\
  (C_ARGUMENTS [a1;a2;a3;a4;a5] s <=>
        read RDI s = a1 /\ read RSI s = a2 /\ read RDX s = a3 /\
        read RCX s = a4 /\ read  R8 s = a5) /\
  (C_ARGUMENTS [a1;a2;a3;a4] s <=>
        read RDI s = a1 /\ read RSI s = a2 /\ read RDX s = a3 /\
        read RCX s = a4) /\
  (C_ARGUMENTS [a1;a2;a3] s <=>
        read RDI s = a1 /\ read RSI s = a2 /\ read RDX s = a3) /\
  (C_ARGUMENTS [a1;a2] s <=>
        read RDI s = a1 /\ read RSI s = a2) /\
  (C_ARGUMENTS [a1] s <=>
        read RDI s = a1) /\
  (C_ARGUMENTS [] s <=>
        T)`;;

let C_RETURN = define
 `C_RETURN = read RAX`;;

let PRESERVED_GPRS = define
 `PRESERVED_GPRS = [RSP; RBX; RBP; R12; R13; R14; R15]`;;

let MODIFIABLE_GPRS = define
 `MODIFIABLE_GPRS = [RAX; RCX; RDX; RSI; RDI; R8; R9; R10; R11]`;;

let MODIFIABLE_ZMMS = define
 `MODIFIABLE_ZMMS =
   [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7;
    ZMM8; ZMM9; ZMM10; ZMM11; ZMM12; ZMM13; ZMM14; ZMM15;
    ZMM16; ZMM17; ZMM18; ZMM19; ZMM20; ZMM21; ZMM22; ZMM23;
    ZMM24; ZMM25; ZMM26; ZMM27; ZMM28; ZMM29; ZMM30; ZMM31]`;;

let MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI = REWRITE_RULE
    [SOME_FLAGS; MODIFIABLE_GPRS; MODIFIABLE_ZMMS]
 (new_definition `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI =
    MAYCHANGE [RIP] ,, MAYCHANGE MODIFIABLE_GPRS ,,
    MAYCHANGE MODIFIABLE_ZMMS ,, MAYCHANGE SOME_FLAGS`);;

(* ------------------------------------------------------------------------- *)
(* Microsoft x86 fastcall ABI (the return value is in fact the same).        *)
(* ------------------------------------------------------------------------- *)

let WINDOWS_C_ARGUMENTS = define
 `(WINDOWS_C_ARGUMENTS [a1;a2;a3;a4;a5;a6] s <=>
        read RCX s = a1 /\ read RDX s = a2 /\ read R8 s = a3 /\
        read R9 s = a4 /\
        read (memory :> bytes64 (word_add (read RSP s) (word 40))) s = a5 /\
        read (memory :> bytes64 (word_add (read RSP s) (word 48))) s = a6) /\
  (WINDOWS_C_ARGUMENTS [a1;a2;a3;a4;a5] s <=>
        read RCX s = a1 /\ read RDX s = a2 /\ read R8 s = a3 /\
        read R9 s = a4 /\
        read (memory :> bytes64 (word_add (read RSP s) (word 40))) s = a5) /\
  (WINDOWS_C_ARGUMENTS [a1;a2;a3;a4] s <=>
        read RCX s = a1 /\ read RDX s = a2 /\ read R8 s = a3 /\
        read R9 s = a4) /\
  (WINDOWS_C_ARGUMENTS [a1;a2;a3] s <=>
        read RCX s = a1 /\ read RDX s = a2 /\ read R8 s = a3) /\
  (WINDOWS_C_ARGUMENTS [a1;a2] s <=>
        read RCX s = a1 /\ read RDX s = a2) /\
  (WINDOWS_C_ARGUMENTS [a1] s <=>
        read RCX s = a1) /\
  (WINDOWS_C_ARGUMENTS [] s <=>
        T)`;;

let WINDOWS_C_RETURN = define
 `WINDOWS_C_RETURN = read RAX`;;

let WINDOWS_PRESERVED_GPRS = define
 `WINDOWS_PRESERVED_GPRS = [RSP; RBX; RBP; RSI; RDI; R12; R13; R14; R15]`;;

let WINDOWS_MODIFIABLE_GPRS = define
 `WINDOWS_MODIFIABLE_GPRS = [RAX; RCX; RDX; R8; R9; R10; R11]`;;

let WINDOWS_MODIFIABLE_ZMMS = define
 `WINDOWS_MODIFIABLE_ZMMS =
   [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5;
    ZMM16; ZMM17; ZMM18; ZMM19; ZMM20; ZMM21; ZMM22; ZMM23;
    ZMM24; ZMM25; ZMM26; ZMM27; ZMM28; ZMM29; ZMM30; ZMM31]`;;

let WINDOWS_MODIFIABLE_UPPER_ZMMS = define
 `WINDOWS_MODIFIABLE_UPPER_ZMMS =
   [ZMM6 :> tophalf; ZMM7 :> tophalf; ZMM8 :> tophalf; ZMM9 :> tophalf;
    ZMM10 :> tophalf; ZMM11 :> tophalf; ZMM12 :> tophalf; ZMM13 :> tophalf;
    ZMM14 :> tophalf; ZMM15 :> tophalf]`;;

let WINDOWS_MODIFIABLE_UPPER_YMMS = define
 `WINDOWS_MODIFIABLE_UPPER_YMMS =
   [ZMM6 :> bottomhalf :> tophalf; ZMM7 :> bottomhalf :> tophalf;
    ZMM8 :> bottomhalf :> tophalf; ZMM9 :> bottomhalf :> tophalf;
    ZMM10 :> bottomhalf :> tophalf; ZMM11 :> bottomhalf :> tophalf;
    ZMM12 :> bottomhalf :> tophalf; ZMM13 :> bottomhalf :> tophalf;
    ZMM14 :> bottomhalf :> tophalf; ZMM15 :> bottomhalf :> tophalf]`;;

let WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI = REWRITE_RULE
    [SOME_FLAGS; WINDOWS_MODIFIABLE_GPRS; WINDOWS_MODIFIABLE_ZMMS;
     WINDOWS_MODIFIABLE_UPPER_ZMMS; WINDOWS_MODIFIABLE_UPPER_YMMS]
 (new_definition `WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI =
    MAYCHANGE [RIP] ,, MAYCHANGE WINDOWS_MODIFIABLE_GPRS ,,
    MAYCHANGE WINDOWS_MODIFIABLE_ZMMS ,,
    MAYCHANGE WINDOWS_MODIFIABLE_UPPER_ZMMS ,,
    MAYCHANGE WINDOWS_MODIFIABLE_UPPER_YMMS ,,
    MAYCHANGE SOME_FLAGS`);;

(* ------------------------------------------------------------------------- *)
(* Clausal theorems and other execution assistance.                          *)
(* ------------------------------------------------------------------------- *)

let OPERAND_SIZE_CASES = prove
 (`(match 256 with 256 -> a | 128 -> b) = a /\
   (match 128 with 256 -> a | 128 -> b) = b /\
   (match 64 with 64 -> a | 32 -> b | 16 -> c | 8 -> d) = a /\
   (match 32 with 64 -> a | 32 -> b | 16 -> c | 8 -> d) = b /\
   (match 16 with 64 -> a | 32 -> b | 16 -> c | 8 -> d) = c /\
   (match  8 with 64 -> a | 32 -> b | 16 -> c | 8 -> d) = d /\
   (match 64 with 64 -> a | 32 -> b | 16 -> c) = a /\
   (match 32 with 64 -> a | 32 -> b | 16 -> c) = b /\
   (match 16 with 64 -> a | 32 -> b | 16 -> c) = c /\
   (match 64 with 64 -> a | 32 -> b) = a /\
   (match 32 with 64 -> a | 32 -> b) = b /\
   (match 32 with 32 -> a | 16 -> b) = a /\
   (match 16 with 32 -> a | 16 -> b) = b /\
   (match (64,32) with
      (64,32) -> a  | (64,16) -> b  | (64,8) -> c | (32,32) -> d
    | (32,16) -> e | (32,8) -> f  | (16,8) -> g) = a /\
   (match (64,16) with
      (64,32) -> a  | (64,16) -> b  | (64,8) -> c | (32,32) -> d
    | (32,16) -> e | (32,8) -> f  | (16,8) -> g) = b /\
   (match (64,8) with
      (64,32) -> a  | (64,16) -> b  | (64,8) -> c | (32,32) -> d
    | (32,16) -> e | (32,8) -> f  | (16,8) -> g) = c /\
   (match (32,32) with
      (64,32) -> a  | (64,16) -> b  | (64,8) -> c | (32,32) -> d
    | (32,16) -> e | (32,8) -> f  | (16,8) -> g) = d /\
   (match (32,16) with
      (64,32) -> a  | (64,16) -> b  | (64,8) -> c | (32,32) -> d
    | (32,16) -> e | (32,8) -> f  | (16,8) -> g) = e /\
   (match (32,8) with
      (64,32) -> a  | (64,16) -> b  | (64,8) -> c | (32,32) -> d
    | (32,16) -> e | (32,8) -> f  | (16,8) -> g) = f /\
   (match (16,8) with
      (64,32) -> a  | (64,16) -> b  | (64,8) -> c | (32,32) -> d
    | (32,16) -> e | (32,8) -> f  | (16,8) -> g) = g /\
   (match (64,16) with
      (64,16) -> b  | (64,8) -> c
    | (32,16) -> e | (32,8) -> f  | (16,8) -> g) = b /\
   (match (64,8) with
      (64,16) -> b  | (64,8) -> c
    | (32,16) -> e | (32,8) -> f  | (16,8) -> g) = c /\
   (match (32,16) with
      (64,16) -> b  | (64,8) -> c
    | (32,16) -> e | (32,8) -> f  | (16,8) -> g) = e /\
   (match (32,8) with
      (64,16) -> b  | (64,8) -> c
    | (32,16) -> e | (32,8) -> f  | (16,8) -> g) = f /\
   (match (16,8) with
      (64,16) -> b  | (64,8) -> c
    | (32,16) -> e | (32,8) -> f  | (16,8) -> g) = g`,
  CONV_TAC(TOP_DEPTH_CONV MATCH_CONV) THEN CONV_TAC NUM_REDUCE_CONV);;

let X86_EXECUTE =
  CONV_RULE (TOP_DEPTH_CONV let_CONV)
   (GEN_REWRITE_RULE LAND_CONV [ETA_AX]
     (GEN_REWRITE_RULE I [GSYM FUN_EQ_THM]
        (GEN `s:x86state` x86_execute)));;

let REGISTER_ALIASES =
 [rax;  rcx;  rdx;  rbx;  rsp;  rbp;  rsi;  rdi;
  r8;   r9;  r10;  r11;  r12;  r13;  r14;  r15;
  eax; ecx; edx; ebx; esp; ebp; esi; edi;
  r8d; r9d; r10d; r11d; r12d; r13d; r14d; r15d;
  ax; cx; dx; bx; sp; bp; si; di; ah;
  al; ch; cl; dh; dl; bh; bl; spl; bpl; sil; dil;
  xmm0; xmm1; xmm2; xmm3; xmm4; xmm5; xmm6; xmm7;
  xmm8; xmm9; xmm10; xmm11; xmm12; xmm13; xmm14; xmm15;
  ymm0; ymm1; ymm2; ymm3; ymm4; ymm5; ymm6; ymm7;
  ymm8; ymm9; ymm10; ymm11;ymm12; ymm13; ymm14; ymm15];;

let OPERAND_SIZE_CONV =
  let topconv = GEN_REWRITE_CONV I [operand_size]
  and botconv = GEN_REWRITE_CONV TOP_DEPTH_CONV (QWORD::REGISTER_ALIASES)
  and midconv = GEN_REWRITE_CONV REPEATC
   [simdregister_size; register_size; bytesize; simdregsize; regsize] in
  fun tm ->
    match tm with
      Comb(Const("operand_size",_),_)->
          (botconv THENC topconv THENC midconv) tm
    | _ -> failwith "OPERAND_SIZE_CONV";;

let BSID_CLAUSES_GEN = prove
 (`bsid_semantics (Bsid (SOME(Gpr r1 Full_64)) (SOME(Gpr r2 Full_64)) k d) s =
   word_add (read (registers :> element r1) s)
            (word (2 EXP (val k) * val(read (registers :> element r2) s) +
                   val d)) /\
   bsid_semantics (Bsid NONE (SOME(Gpr r2 Full_64)) k d) s =
   word_add (word 0)
    (word (2 EXP (val k) * val(read (registers :> element r2) s) + val d)) /\
   bsid_semantics (Bsid (SOME(Gpr r1 Full_64)) NONE k d) s =
   word_add (read (registers :> element r1) s) d /\
   bsid_semantics(Riprel off) s = word(val(read RIP s) + val off)`,
  REWRITE_TAC[bsid_semantics; GPR] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES] THEN
  REWRITE_TAC[WORD_ADD; WORD_ADD_0] THEN
  REWRITE_TAC[WORD_ADD_ASSOC; WORD_VAL] THEN
  REPEAT CONJ_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN TRY BINOP_TAC THEN
  REWRITE_TAC[WORD_MUL; WORD_VAL] THEN TRY AP_TERM_TAC THEN
  REWRITE_TAC[COMPONENT_COMPOSE_ASSOC] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [READ_COMPONENT_COMPOSE] THEN
  REWRITE_TAC[read; asnumber; through] THEN REWRITE_TAC[WORD_VAL]);;

let BSID_SEMANTICS_CONV =
  let coreconv =
    GEN_REWRITE_CONV (LAND_CONV o TRY_CONV)
     [base_displacement; base_scaled_index;
      base_scaled_index_displacement] THENC
    GEN_REWRITE_CONV ONCE_DEPTH_CONV
     [rax;  rcx;  rdx;  rbx;  rsp;  rbp;  rsi;  rdi;
      r8;   r9;  r10;  r11;  r12;  r13;  r14;  r15] THENC
    GEN_REWRITE_CONV I [BSID_CLAUSES_GEN] THENC
    GEN_REWRITE_CONV ONCE_DEPTH_CONV
     (map GSYM [RAX;  RCX;  RDX;  RBX;  RSP;  RBP;  RSI;  RDI;
                R8;   R9;  R10;  R11;  R12;  R13;  R14;  R15]) THENC
    ONCE_DEPTH_CONV WORD_VAL_CONV THENC
    ONCE_DEPTH_CONV NUM_REDUCE_CONV THENC
    GEN_REWRITE_CONV ONCE_DEPTH_CONV [ARITH_RULE `n + 0 = n`] in
  fun tm ->
   (match tm with
      Comb(Comb(Const("bsid_semantics",_),_),_) -> coreconv tm
    | _ -> failwith "BSID_SEMANTICS_CONV");;

let BSID_NORMALIZE_TAC =
  let pth_gen = prove
   (`word(8 * i + 0):int64 = word(8 * i) /\
     word(8 * i + 8):int64 = word(8 * (i + 1)) /\
     word(8 * i + 16):int64 = word(8 * (i + 2))`,
    REPEAT STRIP_TAC THEN AP_TERM_TAC THEN ARITH_TAC)
  and pth_spc = prove
   (`0 < i ==> word(8 * i + 18446744073709551608):int64 = word(8 * (i - 1))`,
    SPEC_TAC(`i:num`,`i:num`) THEN INDUCT_TAC THEN
    REWRITE_TAC[LT_REFL; SUC_SUB1] THEN DISCH_THEN(K ALL_TAC) THEN
    REWRITE_TAC[WORD_EQ; CONG; DIMINDEX_64] THEN
    REWRITE_TAC[MOD_MULT_ADD; ARITH_RULE
     `8 * SUC i + 18446744073709551608 =
      1 * 2 EXP 64 + 8 * i`]) in
  let rule_spc = PART_MATCH (lhand o rand) pth_spc in
  let siderule =
    let siderule_1 asl tm = find (fun th -> concl th = tm) asl
    and rules = map (PART_MATCH rand o ARITH_RULE)
     [`1 <= n ==> 0 < n`; `~(n = 0) ==> 0 < n`;  `m < n ==> 0 < n - m`] in
    fun asl tm ->
      tryfind (fun rule ->
            let th = rule tm in
            MP th (siderule_1 asl (lhand(concl th)))) rules in
  let fullconv(asl,w) tm =
    if not(vfree_in tm w) then failwith "rule" else
    let th = rule_spc tm in
    MP th (siderule (map snd asl) (lhand(concl th))) in
  GEN_REWRITE_TAC ONCE_DEPTH_CONV [pth_gen] THEN
  W(fun (asl,w) -> CONV_TAC(ONCE_DEPTH_CONV(fullconv(asl,w))));;

let BSID_CLAUSES = prove
 (`bsid_semantics (%%(rax,d)) s = word_add (read RAX s) (word d) /\
   bsid_semantics (%%(rcx,d)) s = word_add (read RCX s) (word d) /\
   bsid_semantics (%%(rdx,d)) s = word_add (read RDX s) (word d) /\
   bsid_semantics (%%(rbx,d)) s = word_add (read RBX s) (word d) /\
   bsid_semantics (%%(rsp,d)) s = word_add (read RSP s) (word d) /\
   bsid_semantics (%%(rbp,d)) s = word_add (read RBP s) (word d) /\
   bsid_semantics (%%(rsi,d)) s = word_add (read RSI s) (word d) /\
   bsid_semantics (%%(rdi,d)) s = word_add (read RDI s) (word d) /\
   bsid_semantics (%%( r8,d)) s = word_add (read  R8 s) (word d) /\
   bsid_semantics (%%( r9,d)) s = word_add (read  R9 s) (word d) /\
   bsid_semantics (%%(r10,d)) s = word_add (read R10 s) (word d) /\
   bsid_semantics (%%(r11,d)) s = word_add (read R11 s) (word d) /\
   bsid_semantics (%%(r12,d)) s = word_add (read R12 s) (word d) /\
   bsid_semantics (%%(r13,d)) s = word_add (read R13 s) (word d) /\
   bsid_semantics (%%(r14,d)) s = word_add (read R14 s) (word d) /\
   bsid_semantics (%%(r15,d)) s = word_add (read R15 s) (word d)`,
  REWRITE_TAC[rax;  rcx;  rdx;  rbx;  rsp;  rbp;  rsi;  rdi;
              r8;   r9;  r10;  r11;  r12;  r13;  r14;  r15;
              RAX;  RCX;  RDX;  RBX;  RSP;  RBP;  RSI;  RDI;
              R8;   R9;  R10;  R11;  R12;  R13;  R14;  R15] THEN
  REWRITE_TAC[BSID_CLAUSES_GEN; base_displacement]);;

let OPERAND_CLAUSES = prove
 (`OPERAND128(%_% xmm0) s = YMM0 :> zerotop_128  /\
   OPERAND128(%_% xmm1) s = YMM1 :> zerotop_128  /\
   OPERAND128(%_% xmm2) s = YMM2 :> zerotop_128  /\
   OPERAND128(%_% xmm3) s = YMM3 :> zerotop_128  /\
   OPERAND128(%_% xmm4) s = YMM4 :> zerotop_128  /\
   OPERAND128(%_% xmm5) s = YMM5 :> zerotop_128  /\
   OPERAND128(%_% xmm6) s = YMM6 :> zerotop_128  /\
   OPERAND128(%_% xmm7) s = YMM7 :> zerotop_128  /\
   OPERAND128(%_% xmm8) s = YMM8 :> zerotop_128  /\
   OPERAND128(%_% xmm9) s = YMM9 :> zerotop_128  /\
   OPERAND128(%_% xmm10) s = YMM10 :> zerotop_128  /\
   OPERAND128(%_% xmm11) s = YMM11 :> zerotop_128  /\
   OPERAND128(%_% xmm12) s = YMM12 :> zerotop_128  /\
   OPERAND128(%_% xmm13) s = YMM13 :> zerotop_128  /\
   OPERAND128(%_% xmm14) s = YMM14 :> zerotop_128  /\
   OPERAND128(%_% xmm15) s = YMM15 :> zerotop_128  /\
   OPERAND128 (Memop Word128 bsid) s =
    memory :> bytes128 (bsid_semantics bsid s) /\
   OPERAND128_SSE(%_% xmm0) s = YMM0_SSE :> bottom_128  /\
   OPERAND128_SSE(%_% xmm1) s = YMM1_SSE :> bottom_128  /\
   OPERAND128_SSE(%_% xmm2) s = YMM2_SSE :> bottom_128  /\
   OPERAND128_SSE(%_% xmm3) s = YMM3_SSE :> bottom_128  /\
   OPERAND128_SSE(%_% xmm4) s = YMM4_SSE :> bottom_128  /\
   OPERAND128_SSE(%_% xmm5) s = YMM5_SSE :> bottom_128  /\
   OPERAND128_SSE(%_% xmm6) s = YMM6_SSE :> bottom_128  /\
   OPERAND128_SSE(%_% xmm7) s = YMM7_SSE :> bottom_128  /\
   OPERAND128_SSE(%_% xmm8) s = YMM8_SSE :> bottom_128  /\
   OPERAND128_SSE(%_% xmm9) s = YMM9_SSE :> bottom_128  /\
   OPERAND128_SSE(%_% xmm10) s = YMM10_SSE :> bottom_128  /\
   OPERAND128_SSE(%_% xmm11) s = YMM11_SSE :> bottom_128  /\
   OPERAND128_SSE(%_% xmm12) s = YMM12_SSE :> bottom_128  /\
   OPERAND128_SSE(%_% xmm13) s = YMM13_SSE :> bottom_128  /\
   OPERAND128_SSE(%_% xmm14) s = YMM14_SSE :> bottom_128  /\
   OPERAND128_SSE(%_% xmm15) s = YMM15_SSE :> bottom_128  /\
   OPERAND128_SSE (Memop Word128 bsid) s =
    memory :> bytes128 (bsid_semantics bsid s) /\
   OPERAND256(%_% ymm0) s = YMM0  /\
   OPERAND256(%_% ymm1) s = YMM1  /\
   OPERAND256(%_% ymm2) s = YMM2  /\
   OPERAND256(%_% ymm3) s = YMM3  /\
   OPERAND256(%_% ymm4) s = YMM4  /\
   OPERAND256(%_% ymm5) s = YMM5  /\
   OPERAND256(%_% ymm6) s = YMM6  /\
   OPERAND256(%_% ymm7) s = YMM7  /\
   OPERAND256(%_% ymm8) s = YMM8  /\
   OPERAND256(%_% ymm9) s = YMM9  /\
   OPERAND256(%_% ymm10) s = YMM10  /\
   OPERAND256(%_% ymm11) s = YMM11  /\
   OPERAND256(%_% ymm12) s = YMM12  /\
   OPERAND256(%_% ymm13) s = YMM13  /\
   OPERAND256(%_% ymm14) s = YMM14  /\
   OPERAND256(%_% ymm15) s = YMM15  /\
   OPERAND256 (Memop Word256 bsid) s =
    memory :> bytes256 (bsid_semantics bsid s) /\
   OPERAND64 (%rax) s = RAX /\
   OPERAND64 (%rcx) s = RCX /\
   OPERAND64 (%rdx) s = RDX /\
   OPERAND64 (%rbx) s = RBX /\
   OPERAND64 (%rsp) s = RSP /\
   OPERAND64 (%rbp) s = RBP /\
   OPERAND64 (%rsi) s = RSI /\
   OPERAND64 (%rdi) s = RDI /\
   OPERAND64 (% r8) s =  R8 /\
   OPERAND64 (% r9) s =  R9 /\
   OPERAND64 (%r10) s = R10 /\
   OPERAND64 (%r11) s = R11 /\
   OPERAND64 (%r12) s = R12 /\
   OPERAND64 (%r13) s = R13 /\
   OPERAND64 (%r14) s = R14 /\
   OPERAND64 (%r15) s = R15 /\
   OPERAND64 (## n) s = rvalue(word_sx(word n:32 word)) /\
   OPERAND64 (Imm64 w64) s = rvalue w64 /\
   OPERAND64 (Imm32 w32) s = rvalue(word_sx w32) /\
   OPERAND64 (Imm16 w16) s = rvalue(word_sx w16) /\
   OPERAND64 (Imm8 w8) s = rvalue(word_sx w8) /\
   OPERAND64 (QWORD bsid) s = memory :> bytes64 (bsid_semantics bsid s) /\
   OPERAND64 (Memop Quadword bsid) s =
    memory :> bytes64 (bsid_semantics bsid s) /\
   OPERAND32 (%eax) s = RAX :> zerotop_32 /\
   OPERAND32 (%ecx) s = RCX :> zerotop_32 /\
   OPERAND32 (%edx) s = RDX :> zerotop_32 /\
   OPERAND32 (%ebx) s = RBX :> zerotop_32 /\
   OPERAND32 (%esp) s = RSP :> zerotop_32 /\
   OPERAND32 (%ebp) s = RBP :> zerotop_32 /\
   OPERAND32 (%esi) s = RSI :> zerotop_32 /\
   OPERAND32 (%edi) s = RDI :> zerotop_32 /\
   OPERAND32 (%r8d) s =  R8 :> zerotop_32 /\
   OPERAND32 (%r9d) s =  R9 :> zerotop_32 /\
   OPERAND32 (%r10d) s = R10 :> zerotop_32 /\
   OPERAND32 (%r11d) s = R11 :> zerotop_32 /\
   OPERAND32 (%r12d) s = R12 :> zerotop_32 /\
   OPERAND32 (%r13d) s = R13 :> zerotop_32 /\
   OPERAND32 (%r14d) s = R14 :> zerotop_32 /\
   OPERAND32 (%r15d) s = R15 :> zerotop_32 /\
   OPERAND32 (## n) s = rvalue(word n:32 word) /\
   OPERAND32 (Imm32 w32) s = rvalue w32 /\
   OPERAND32 (Imm16 w16) s = rvalue(word_sx w16) /\
   OPERAND32 (Imm8 w8) s = rvalue(word_sx w8) /\
   OPERAND32 (Memop Doubleword bsid) s =
    memory :> bytes32 (bsid_semantics bsid s) /\
   OPERAND16 (%ax) s = RAX :> bottom_32 :> bottom_16 /\
   OPERAND16 (%cx) s = RCX :> bottom_32 :> bottom_16 /\
   OPERAND16 (%dx) s = RDX :> bottom_32 :> bottom_16 /\
   OPERAND16 (%bx) s = RBX :> bottom_32 :> bottom_16 /\
   OPERAND16 (%sp) s = RSP :> bottom_32 :> bottom_16 /\
   OPERAND16 (%bp) s = RBP :> bottom_32 :> bottom_16 /\
   OPERAND16 (%si) s = RSI :> bottom_32 :> bottom_16 /\
   OPERAND16 (%di) s = RDI :> bottom_32 :> bottom_16 /\
   OPERAND16 (Imm16 w16) s = rvalue w16 /\
   OPERAND16 (Imm8 w8) s = rvalue(word_sx w8) /\
   OPERAND16 (Memop Word bsid) s =
    memory :> bytes16 (bsid_semantics bsid s) /\
   OPERAND8 (%al) s = RAX :> bottom_32 :> bottom_16 :> bottom_8 /\
   OPERAND8 (%cl) s = RCX :> bottom_32 :> bottom_16 :> bottom_8 /\
   OPERAND8 (%dl) s = RDX :> bottom_32 :> bottom_16 :> bottom_8 /\
   OPERAND8 (%bl) s = RBX :> bottom_32 :> bottom_16 :> bottom_8 /\
   OPERAND8 (%spl) s = RSP :> bottom_32 :> bottom_16 :> bottom_8 /\
   OPERAND8 (%bpl) s = RBP :> bottom_32 :> bottom_16 :> bottom_8 /\
   OPERAND8 (%sil) s = RSI :> bottom_32 :> bottom_16 :> bottom_8 /\
   OPERAND8 (%dil) s = RDI :> bottom_32 :> bottom_16 :> bottom_8 /\
   OPERAND8 (%ah) s = RAX :> bottom_32 :> bottom_16 :> top_8 /\
   OPERAND8 (%ch) s = RCX :> bottom_32 :> bottom_16 :> top_8 /\
   OPERAND8 (%dh) s = RDX :> bottom_32 :> bottom_16 :> top_8 /\
   OPERAND8 (%bh) s = RBX :> bottom_32 :> bottom_16 :> top_8 /\
   OPERAND8 (Imm8 w8) s = rvalue w8 /\
   OPERAND8 (Memop Byte bsid) s =
    memory :> bytes8 (bsid_semantics bsid s)`,
  REWRITE_TAC[rax;  rcx;  rdx;  rbx;  rsp;  rbp;  rsi;  rdi;
              r8;   r9;  r10;  r11;  r12;  r13;  r14;  r15;
              RAX;  RCX;  RDX;  RBX;  RSP;  RBP;  RSI;  RDI;
              R8;   R9;  R10;  R11;  R12;  R13;  R14;  R15;
              eax; ecx; edx; ebx; esp; ebp; esi; edi;
              r8d; r9d; r10d; r11d; r12d; r13d; r14d; r15d;
              ax; cx; dx; bx; sp; bp; si; di; ah;
              al; ch; cl; dh; dl; bh; bl; spl; bpl; sil; dil;
              EAX; ECX; EDX; EBX; ESP; EBP; ESI; EDI;
              R8D; R9D; R10D; R11D; R12D; R13D; R14D; R15D;
              AX; CX; DX; BX; SP; BP; SI; DI;
              AH; AL; BH; BL; CH; CL; DH; DL;
              SPL; BPL; SIL; DIL;
              xmm0; xmm1; xmm2; xmm3; xmm4; xmm5; xmm6; xmm7;
              xmm8; xmm9; xmm10; xmm11; xmm12; xmm13; xmm14; xmm15;
              XMM0; XMM1; XMM2; XMM3; XMM4; XMM5; XMM6; XMM7; XMM8;
              XMM9; XMM10; XMM11; XMM12; XMM13; XMM14; XMM15;
              XMM0_SSE; XMM1_SSE; XMM2_SSE; XMM3_SSE;
              XMM4_SSE; XMM5_SSE; XMM6_SSE; XMM7_SSE;
              XMM8_SSE; XMM9_SSE; XMM10_SSE; XMM11_SSE;
              XMM12_SSE; XMM13_SSE; XMM14_SSE; XMM15_SSE;
              ymm0; ymm1; ymm2; ymm3; ymm4; ymm5; ymm6; ymm7;
              ymm8; ymm9; ymm10; ymm11; ymm12; ymm13; ymm14; ymm15;
              YMM0; YMM1; YMM2; YMM3; YMM4; YMM5; YMM6; YMM7; YMM8;
              YMM9; YMM10; YMM11; YMM12; YMM13; YMM14; YMM15;
              YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM3_SSE;
              YMM4_SSE; YMM5_SSE; YMM6_SSE; YMM7_SSE;
              YMM8_SSE; YMM9_SSE; YMM10_SSE; YMM11_SSE;
              YMM12_SSE; YMM13_SSE; YMM14_SSE; YMM15_SSE;
              ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7; ZMM8;
              ZMM9; ZMM10; ZMM11; ZMM12; ZMM13; ZMM14; ZMM15] THEN
  REWRITE_TAC[simple_immediate; base_displacement; QWORD] THEN
  REWRITE_TAC[OPERAND256; OPERAND128; OPERAND128_SSE; OPERAND64; OPERAND32; OPERAND16; OPERAND8;
              register_size; regsize; simdregister_size; simdregsize;
              SIMD256; SIMD128; SIMD128_SSE; GPR64; GPR32_Z; GPR32; GPR16; GPR8] THEN
  REWRITE_TAC[COMPONENT_COMPOSE_ASSOC]);;

(* ------------------------------------------------------------------------- *)
(* Some forms with a comprehensible carry flag; currently 64-bit only.       *)
(* Also 64-bit instantiations of PUSH and POP are much simpler to work with. *)
(* ------------------------------------------------------------------------- *)

let x86_ADC_ALT = prove
 (`x86_ADC dest src s =
        let x = read dest s and y = read src s and c = bitval(read CF s) in
        let z = word_add (word_add x y) (word c) in
        (dest := (z:64 word) ,,
         ZF := (val z = 0) ,,
         SF := (ival z < &0) ,,
         PF := word_evenparity(word_zx z:byte) ,,
         CF := (2 EXP 64 <= val x + val y + c) ,,
         OF := ~(ival x + ival y + &c = ival z) ,,
         AF := ~(val(word_zx x:nybble) + val(word_zx y:nybble) + c =
                 val(word_zx z:nybble))) s`,
  REWRITE_TAC[x86_ADC] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[CARRY64_ADC]);;

let x86_ADCX_ALT = prove
 (`x86_ADCX dest src s =
        let x = read dest s and y = read src s and c = bitval(read CF s) in
        let z = word_add (word_add x y) (word c) in
        (dest := (z:64 word) ,,
         CF := (2 EXP 64 <= val x + val y + c)) s`,
  REWRITE_TAC[x86_ADCX] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[CARRY64_ADC]);;

let x86_ADOX_ALT = prove
 (`x86_ADOX dest src s =
        let x = read dest s and y = read src s and c = bitval(read OF s) in
        let z = word_add (word_add x y) (word c) in
        (dest := (z:64 word) ,,
         OF := (2 EXP 64 <= val x + val y + c)) s`,
  REWRITE_TAC[x86_ADOX] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[CARRY64_ADC]);;

let x86_ADD_ALT = prove
 (`x86_ADD dest src s =
        let x = read dest s and y = read src s in
        let z = word_add x y in
        (dest := (z:64 word) ,,
         ZF := (val z = 0) ,,
         SF := (ival z < &0) ,,
         PF := word_evenparity(word_zx z:byte) ,,
         CF := (2 EXP 64 <= val x + val y) ,,
         OF := ~(ival x + ival y = ival z) ,,
         AF := ~(val(word_zx x:nybble) + val(word_zx y:nybble) =
                 val(word_zx z:nybble))) s`,
  REWRITE_TAC[x86_ADD] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[CARRY64_ADD]);;

let x86_SBB_ALT = prove
 (`x86_SBB dest src s =
        let x = read dest s and y = read src s and c = bitval(read CF s) in
        let z = word_sub x (word_add y (word c)) in
        (dest := (z:64 word) ,,
         ZF := (val z = 0) ,,
         SF := (ival z < &0) ,,
         PF := word_evenparity(word_zx z:byte) ,,
         CF := (val x < val y + c) ,,
         OF := ~(ival x - (ival y + &c) = ival z) ,,
         AF := ~(&(val(word_zx x:nybble)) -
                 (&(val(word_zx y:nybble)) + &c):int =
                 &(val(word_zx z:nybble)))) s`,
  REWRITE_TAC[x86_SBB] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[CARRY64_SBB]);;

let x86_SUB_ALT = prove
 (`x86_SUB dest src s =
        let x = read dest s and y = read src s in
        let z = word_sub x y in
        (dest := (z:64 word) ,,
         ZF := (val z = 0) ,,
         SF := (ival z < &0) ,,
         PF := word_evenparity(word_zx z:byte) ,,
         CF := (val x < val y) ,,
         OF := ~(ival x - ival y = ival z) ,,
         AF := ~(&(val(word_zx x:nybble)) - &(val(word_zx y:nybble)):int =
                 &(val(word_zx z:nybble)))) s`,
  REWRITE_TAC[x86_SUB] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[CARRY64_SUB]);;

let x86_CMP_ALT = prove
 (`x86_CMP dest src s =
        let x = read dest s and y = read src s in
        let (z:64 word) = word_sub x y in
        (ZF := (val z = 0) ,,
         SF := (ival z < &0) ,,
         PF := word_evenparity(word_zx z:byte) ,,
         CF := (val x < val y) ,,
         OF := ~(ival x - ival y = ival z) ,,
         AF := ~(&(val(word_zx x:nybble)) - &(val(word_zx y:nybble)):int =
                 &(val(word_zx z:nybble)))) s`,
  REWRITE_TAC[x86_CMP] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[CARRY64_SUB]);;

let x86_POP_ALT = prove
 (`x86_POP dest s =
        let p = read RSP s in
        let x = read (memory :> bytes64 p) s in
        let p' = word_add p (word 8) in
        (RSP := p' ,,
         dest := x) s`,
  REWRITE_TAC[x86_POP; DIMINDEX_64; bytes64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; asword; through; read; write]);;

let x86_PUSH_ALT = prove
 (`x86_PUSH src s =
        let p = read RSP s
        and x = read src s in
        let p' = word_sub p (word 8) in
        (RSP := p' ,,
         memory :> bytes64 p' := x) s`,
  REWRITE_TAC[x86_PUSH; DIMINDEX_64; bytes64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[WRITE_COMPONENT_COMPOSE; asword; through; read; write; seq;
              assign]);;

let x86_CALL_ALT = prove
 (`x86_CALL target s =
        let p = read RSP s
        and x = read RIP s in
        let p' = word_sub p (word 8) in
        (RSP := p' ,,
         memory :> bytes64 p' := x ,,
         RIP := target) s`,
  REWRITE_TAC[x86_CALL] THEN
  GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV o LAND_CONV) [GSYM ETA_AX] THEN
  REWRITE_TAC[x86_PUSH_ALT] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[FUN_EQ_THM; seq; assign] THEN MESON_TAC[]);;

(*** More alternatives that are nicer to work with ***)

let x86_BTC_ALT = prove
 (`x86_BTC dest src s =
        let (x:N word) = read dest s and y = read src s in
        let c = val y MOD dimindex(:N) in
        let b = bit c x in
        (dest := word_xor x (word_shl (word 1) c) ,,
         CF := b ,,
         UNDEFINED_VALUES[SF;PF;OF;AF]) s`,
  REWRITE_TAC[x86_BTC] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[FUN_EQ_THM; seq; assign; UNWIND_THM1] THEN
  X_GEN_TAC `s':x86state` THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[WRITE_COMPONENT_COMPOSE] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC I [WORD_EQ_BITS_ALT] THEN
  REWRITE_TAC[GSYM READ_BITELEMENT; READ_WRITE_BITELEMENT_GEN] THEN
  SIMP_TAC[READ_BITELEMENT; BIT_WORD_XOR; BIT_WORD_SHL; BIT_WORD_1] THEN
  REWRITE_TAC[MOD_LT_EQ; DIMINDEX_NONZERO] THEN
  REWRITE_TAC[ARITH_RULE `j <= i /\ i - j = 0 <=> i = j`] THEN
  MESON_TAC[]);;

let x86_BTR_ALT = prove
 (`x86_BTR dest src s =
        let (x:N word) = read dest s and y = read src s in
        let c = val y MOD dimindex(:N) in
        let b = bit c x in
        (dest := word_and x (word_not(word_shl (word 1) c)) ,,
         CF := b ,,
         UNDEFINED_VALUES[SF;PF;OF;AF]) s`,
  REWRITE_TAC[x86_BTR] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[FUN_EQ_THM; seq; assign; UNWIND_THM1] THEN
  X_GEN_TAC `s':x86state` THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[WRITE_COMPONENT_COMPOSE] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC I [WORD_EQ_BITS_ALT] THEN
  REWRITE_TAC[GSYM READ_BITELEMENT; READ_WRITE_BITELEMENT_GEN] THEN
  SIMP_TAC[READ_BITELEMENT; BIT_WORD_AND; BIT_WORD_NOT;
           BIT_WORD_SHL; BIT_WORD_1] THEN
  REWRITE_TAC[MOD_LT_EQ; DIMINDEX_NONZERO] THEN
  REWRITE_TAC[ARITH_RULE `j <= i /\ i - j = 0 <=> i = j`] THEN
  MESON_TAC[]);;

let x86_BTS_ALT = prove
 (`x86_BTS dest src s =
        let (x:N word) = read dest s and y = read src s in
        let c = val y MOD dimindex(:N) in
        let b = bit c x in
        (dest := word_or x (word_shl (word 1) c) ,,
         CF := b ,,
         UNDEFINED_VALUES[SF;PF;OF;AF]) s`,
  REWRITE_TAC[x86_BTS] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[FUN_EQ_THM; seq; assign; UNWIND_THM1] THEN
  X_GEN_TAC `s':x86state` THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[WRITE_COMPONENT_COMPOSE] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC I [WORD_EQ_BITS_ALT] THEN
  REWRITE_TAC[GSYM READ_BITELEMENT; READ_WRITE_BITELEMENT_GEN] THEN
  SIMP_TAC[READ_BITELEMENT; BIT_WORD_OR; BIT_WORD_SHL; BIT_WORD_1] THEN
  REWRITE_TAC[MOD_LT_EQ; DIMINDEX_NONZERO] THEN
  REWRITE_TAC[ARITH_RULE `j <= i /\ i - j = 0 <=> i = j`] THEN
  MESON_TAC[]);;

(*** Just a conceptual observation, not actually used ***)

let x86_RET_POP_RIP = prove
 (`x86_RET = x86_POP RIP`,
  GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  X_GEN_TAC `s:x86state` THEN
  REWRITE_TAC[x86_POP_ALT; x86_RET] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[]);;

(*** Simplify word operations in SIMD instructions ***)

let all_simd_rules =
   [usimd16;usimd8;usimd4;usimd2;simd16;simd8;simd4;simd2];;

let EXPAND_SIMD_RULE =
  CONV_RULE (TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) o
  CONV_RULE (DEPTH_CONV DIMINDEX_CONV) o REWRITE_RULE all_simd_rules;;

let x86_PADDD_ALT = EXPAND_SIMD_RULE x86_PADDD;;
let x86_PADDQ_ALT = EXPAND_SIMD_RULE x86_PADDQ;;
let x86_PCMPGTD_ALT = EXPAND_SIMD_RULE x86_PCMPGTD;;
let x86_PSHUFD_ALT = EXPAND_SIMD_RULE x86_PSHUFD;;
let x86_PSRAD_ALT = EXPAND_SIMD_RULE x86_PSRAD;;


let X86_OPERATION_CLAUSES =
  map (CONV_RULE(TOP_DEPTH_CONV let_CONV) o SPEC_ALL)
   [x86_ADC_ALT; x86_ADCX_ALT; x86_ADOX_ALT; x86_ADD_ALT;
    x86_AESDEC; x86_AESDECLAST; x86_AESENC; x86_AESENCLAST;
    x86_AESKEYGENASSIST; x86_AND;
    x86_BSF; x86_BSR; x86_BSWAP; x86_BT; x86_BTC_ALT; x86_BTR_ALT; x86_BTS_ALT;
    x86_CALL_ALT; x86_CLC; x86_CMC; x86_CMOV; x86_CMP_ALT; x86_DEC;
    x86_DIV2; x86_ENDBR64; x86_IMUL; x86_IMUL2; x86_IMUL3; x86_INC; x86_LEA; x86_LZCNT;
    x86_MOV; x86_MOVAPS; x86_MOVDQA; x86_MOVDQU; x86_MOVSX; x86_MOVUPS; x86_MOVZX;
    x86_MUL2; x86_MULX4; x86_NEG; x86_NOP; x86_NOP_N; x86_NOT; x86_OR;
    x86_PADDD_ALT; x86_PADDQ_ALT; x86_PAND; x86_PCMPGTD_ALT; x86_POP_ALT;
    x86_PSHUFD_ALT; x86_PSRAD_ALT; x86_PUSH_ALT; x86_PXOR;
    x86_RCL; x86_RCR; x86_RET; x86_ROL; x86_ROR;
    x86_SAR; x86_SBB_ALT; x86_SET; x86_SHL; x86_SHLD; x86_SHR; x86_SHRD;
    x86_STC; x86_SUB_ALT; x86_TEST; x86_TZCNT; x86_XCHG; x86_XOR;
    (*** AVX2 instructions ***)
    x86_VPXOR;
    (*** 32-bit backups since the ALT forms are 64-bit only ***)
    INST_TYPE[`:32`,`:N`] x86_ADC;
    INST_TYPE[`:32`,`:N`] x86_ADCX;
    INST_TYPE[`:32`,`:N`] x86_ADOX;
    INST_TYPE[`:32`,`:N`] x86_ADD;
    INST_TYPE[`:32`,`:N`] x86_CMP;
    INST_TYPE[`:32`,`:N`] x86_SBB;
    INST_TYPE[`:32`,`:N`] x86_SUB];;

(* ------------------------------------------------------------------------- *)
(* Trivial reassociation and reduction of "word((pc + m) + n)"               *)
(* ------------------------------------------------------------------------- *)

let WORD_NUM_ASSOC_AND_ADD_CONV =
  GEN_REWRITE_CONV I
   [MESON[ADD_ASSOC] `word((pc + m) + n) = word(pc + m + n)`] THENC
  RAND_CONV(RAND_CONV NUM_ADD_CONV);;

(* ------------------------------------------------------------------------- *)
(* Perform symbolic execution of one instruction to reach named state.       *)
(* ------------------------------------------------------------------------- *)

let X86_THM =
  let pth = prove
   (`read RIP s = word pc ==> x86_decode s (word pc) (n,instr) ==>
     (x86 s s' <=> (RIP := word (pc + n) ,, x86_execute instr) s s')`,
    REPEAT STRIP_TAC THEN REWRITE_TAC [x86] THEN
    ASM_REWRITE_TAC[GSYM WORD_ADD] THEN
    ASM_MESON_TAC[PAIR_EQ; x86_decode_unique]) in
  fun (execth2:thm option array) loaded_mc_th pc_th ->
    let th = MATCH_MP pth pc_th in
    let pc_ofs:int =
      let pc_expr = snd (dest_comb (snd (dest_eq (concl pc_th)))) in
      if is_var pc_expr then 0
      else try
        let pc_base,ofs = dest_binary "+" pc_expr in
        dest_small_numeral ofs
      with Failure _ ->
        failwith ("X86_THM: Cannot decompose PC expression: " ^
                  string_of_term (concl pc_th)) in
    CONV_RULE
      (ONCE_DEPTH_CONV
        (REWR_CONV (GSYM ADD_ASSOC) THENC RAND_CONV NUM_REDUCE_CONV))
      (MATCH_MP th (MATCH_MP (Option.get execth2.(pc_ofs)) loaded_mc_th));;

let X86_ENSURES_SUBLEMMA_TAC =
  ENSURES_SUBLEMMA_TAC o MATCH_MP bytes_loaded_update o CONJUNCT1;;

let X86_ENSURES_SUBSUBLEMMA_TAC =
  ENSURES_SUBSUBLEMMA_TAC o map (MATCH_MP bytes_loaded_update o CONJUNCT1);;

let X86_UNDEFINED_GEN_TAC =
  (* Globally assign a unique number to the undefined variable.
     If variable names overlap, this can cause a very weird error
     'Exception: Failure "ABS"'.
     Not scanning the assumptions is also beneficial for the speed
     of this tactic. *)
  let undef_n = ref 1 in
  let rec chundef () =
    let v = "undefined_"^string_of_int !undef_n in
    undef_n := 1 + !undef_n;
    v in
  fun (asl,w) ->
    try let ty = snd(dest_var(fst(dest_forall w))) in
        let x' = chundef () in
        X_GEN_TAC (mk_var(x',ty)) (asl,w)
      with Failure _ -> failwith "X86_UNDEFINED_GEN_TAC";;

let X86_UNDEFINED_CHOOSE_TAC =
  GEN_REWRITE_TAC I [LEFT_IMP_EXISTS_THM] THEN X86_UNDEFINED_GEN_TAC;;

(*** This is to force more aggressive use of assumptions and
 *** simplification if we have a conditional indicative of a
 *** possible exception. Currently this only arises in the
 *** division instruction for cases we are verifying and in
 *** if conditions that checks for alignment in
 *** MOVAPS and MOVDQA
 ***)

let X86_FORCE_CONDITIONAL_CONV =
  let trigger t = is_comb t && is_cond(rator t) in
  fun ths ->
     let baseconv =
       GEN_REWRITE_CONV
        (RATOR_CONV o RATOR_CONV o LAND_CONV o TOP_DEPTH_CONV) ths THENC
       RATOR_CONV(RATOR_CONV(LAND_CONV
         (ONCE_DEPTH_CONV DIMINDEX_CONV))) THENC
       RATOR_CONV(RATOR_CONV(LAND_CONV
         (DEPTH_CONV WORD_NUM_RED_CONV))) THENC
       ALIGNED_16_CONV ths THENC
       TRY_CONV (GEN_REWRITE_CONV
        (RATOR_CONV o RATOR_CONV o LAND_CONV o TOP_DEPTH_CONV) ths) THENC
       TRY_CONV (GEN_REWRITE_CONV RATOR_CONV [COND_CLAUSES]) in
     let chconv t = if trigger t then baseconv t else failwith "baseconv" in
     fun tm -> if trigger tm then (REPEATC chconv THENC TRY_CONV BETA_CONV) tm
               else REFL tm;;

let ASSIGNS_PULL_ZEROTOP_THM = prove
 (`(!P c y. (if P then ASSIGNS (c :> zerotop_32) else c := y) =
            (\s s'. ?d:int32. (c := if P then word_zx d else y) s s')) /\
   (!P c y. (if P then ASSIGNS (c :> zerotop_128) else c := y) =
              (\s s'. ?d:int128. (c := if P then word_zx d else y) s s'))`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[ETA_AX] THEN
  REWRITE_TAC[ASSIGNS; ASSIGN_ZEROTOP_32; ASSIGN_ZEROTOP_128; FUN_EQ_THM] THEN
  MESON_TAC[]);;

(* returns true if t is `read RIP <state>`. *)
let is_read_rip t =
  (* do not use term_match because it is slow. *)
  match t with
  | Comb (Comb (Const ("read", _), Const ("RIP", _)), _) -> true
  | _ -> false;;

(* For compatibility with is_read_pc in Arm *)
let is_read_pc = is_read_rip;;

(* returns true if t is `read events <state>`.
   Currently this always returns false because x86 does not have events. *)
let is_read_events (t:term) = false;;

(*** decode_ths is an array from int offset i to
 ***   Some `|- !s pc. bytes_loaded s pc *_mc
 ***            ==> x86_decode s (word (pc+i)) (..inst..)`
 *** .. if it is a valid byte sequence, or None otherwise.
 ***)

let X86_CONV (decode_ths:thm option array) ths tm =
  let pc_th = find
    (fun th ->
      let c = concl th in
      is_eq c && is_read_rip (fst (dest_eq c)))
    ths in
  let eth = tryfind (fun loaded_mc_th ->
      GEN_REWRITE_CONV I [X86_THM decode_ths loaded_mc_th pc_th] tm) ths in
  (K eth THENC
   REWRITE_CONV[X86_EXECUTE] THENC
   ONCE_DEPTH_CONV OPERAND_SIZE_CONV THENC
   REWRITE_CONV[condition_semantics; aligned_OPERAND128] THENC
   REWRITE_CONV[OPERAND_SIZE_CASES] THENC
   REWRITE_CONV[OPERAND_CLAUSES] THENC
   ONCE_DEPTH_CONV BSID_SEMANTICS_CONV THENC
   REWRITE_CONV X86_OPERATION_CLAUSES THENC
   REWRITE_CONV[READ_RVALUE;
                ASSIGN_ZEROTOP_32; READ_ZEROTOP_32; WRITE_ZEROTOP_32;
                ASSIGN_ZEROTOP_128; READ_ZEROTOP_128; WRITE_ZEROTOP_128;
                READ_BOTTOM_128] THENC
   DEPTH_CONV WORD_NUM_RED_CONV THENC
   REWRITE_CONV[SEQ; condition_semantics] THENC
   GEN_REWRITE_CONV TOP_DEPTH_CONV
    [UNDEFINED_VALUE; UNDEFINED_VALUES; SEQ_ID] THENC
   GEN_REWRITE_CONV TOP_DEPTH_CONV
    [ASSIGNS_PULL_ZEROTOP_THM; ASSIGNS_PULL_THM] THENC
   REWRITE_CONV[ASSIGNS_THM] THENC
   GEN_REWRITE_CONV TOP_DEPTH_CONV [SEQ_PULL_THM; BETA_THM] THENC
   GEN_REWRITE_CONV TOP_DEPTH_CONV[assign; seq; UNWIND_THM1; BETA_THM] THENC
   TRY_CONV(REWRITE_CONV[WRITE_BOTTOM_128]) THENC
   TRY_CONV(REWRITE_CONV READ_YMM_SSE_EQUIV) THENC
   REWRITE_CONV[] THENC REWRITE_CONV[WRITE_SHORT; READ_SHORT] THENC
   TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV THENC
   X86_FORCE_CONDITIONAL_CONV ths THENC
   ONCE_DEPTH_CONV
    (GEN_REWRITE_CONV I [GSYM WORD_ADD] THENC
     GEN_REWRITE_CONV (RAND_CONV o TOP_DEPTH_CONV) [GSYM ADD_ASSOC] THENC
     RAND_CONV NUM_REDUCE_CONV) THENC
   TOP_DEPTH_CONV COMPONENT_WRITE_OVER_WRITE_CONV THENC
   GEN_REWRITE_CONV (SUB_COMPONENTS_CONV o TOP_DEPTH_CONV) ths THENC
   GEN_REWRITE_CONV TOP_DEPTH_CONV [WORD_VAL] THENC
   ONCE_DEPTH_CONV WORD_PC_PLUS_CONV THENC
   DEPTH_CONV WORD_NUM_RED_CONV THENC
   ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV
 ) tm;;

let X86_BASIC_STEP_TAC =
  let x86_tm = `x86` and x86_ty = `:x86state` in
  fun (decode_ths: thm option array) sname (asl,w) ->
    let sv = rand w and sv' = mk_var(sname,x86_ty) in
    let atm = mk_comb(mk_comb(x86_tm,sv),sv') in
    let eth = X86_CONV decode_ths (map snd asl) atm in
    (GEN_REWRITE_TAC I [eventually_CASES] THEN DISJ2_TAC THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC BINDER_CONV [eth] THEN CONV_TAC EXISTS_NONTRIVIAL_CONV;
      X_GEN_TAC sv' THEN GEN_REWRITE_TAC LAND_CONV [eth] THEN
      REPEAT X86_UNDEFINED_CHOOSE_TAC]) (asl,w);;

let X86_STEP_TAC (mc_length_th,decode_ths) subths sname =
  (*** This does the basic decoding setup ***)

  X86_BASIC_STEP_TAC decode_ths sname THEN

  (*** This part shows the code isn't self-modifying ***)

  NONSELFMODIFYING_STATE_UPDATE_TAC
    (MATCH_MP bytes_loaded_update mc_length_th) THEN

  (*** Attempt also to show subroutines aren't modified, if applicable ***)

  MAP_EVERY (TRY o NONSELFMODIFYING_STATE_UPDATE_TAC o
    MATCH_MP bytes_loaded_update o CONJUNCT1) subths THEN

  (*** This part produces any updated versions of existing asms ***)

  ASSUMPTION_STATE_UPDATE_TAC THEN

  (*** Produce updated "MAYCHANGE" assumption ***)

  MAYCHANGE_STATE_UPDATE_TAC THEN

  (*** This adds state component theorems for the updates ***)
  (*** Could also assume th itself but I throw it away   ***)

  DISCH_THEN(fun th ->
    let thl = STATE_UPDATE_NEW_RULE th in
    if thl = [] then ALL_TAC else
    MP_TAC(end_itlist CONJ thl) THEN
    ASSEMBLER_SIMPLIFY_TAC THEN
    (* Reduce reads of YMMx_SSE into reads of YMMx *)
    REWRITE_TAC READ_YMM_SSE_EQUIV THEN
    STRIP_TAC);;

let X86_VERBOSE_STEP_TAC (exth1,exth2) sname g =
  Format.print_string("Stepping to state "^sname); Format.print_newline();
  X86_STEP_TAC (exth1,exth2) [] sname g;;

let X86_VERBOSE_SUBSTEP_TAC (exth1,exth2) subths sname g =
  Format.print_string("Stepping to state "^sname); Format.print_newline();
  X86_STEP_TAC (exth1,exth2) subths sname g;;

(* ------------------------------------------------------------------------- *)
(* Throw away assumptions according to patterns.                             *)
(* ------------------------------------------------------------------------- *)

let DISCARD_FLAGS_TAC =
  DISCARD_MATCHING_ASSUMPTIONS
   [`read CF s = y`; `read PF s = y`; `read AF s = y`;
    `read ZF s = y`; `read SF s = y`; `read OF s = y`];;

let DISCARD_STATE_TAC s =
  DISCARD_ASSUMPTIONS_TAC (vfree_in (mk_var(s,`:x86state`)) o concl);;

let DISCARD_OLDSTATE_TAC s =
  let v = mk_var(s,`:x86state`) in
  let rec unbound_statevars_of_read bound_svars tm =
    match tm with
      Comb(Comb(Const("read",_),cmp),s) ->
        if mem s bound_svars then [] else [s]
    | Comb(a,b) -> union (unbound_statevars_of_read bound_svars a)
                         (unbound_statevars_of_read bound_svars b)
    | Abs(v,t) -> unbound_statevars_of_read (v::bound_svars) t
    | _ -> [] in
  DISCARD_ASSUMPTIONS_TAC(
    fun thm ->
      let us = unbound_statevars_of_read [] (concl thm) in
      if us = [] || us = [v] then false
      else if not(mem v us) then true
      else
        if !x86_print_log then
          (Format.print_string
           ("Info: assumption \`"^string_of_term (concl thm)^
            "\` is erased, but it might have contained useful information\n");
           true)
        else true);;

(* ------------------------------------------------------------------------- *)
(* More convenient stepping tactics, optionally with accumulation.           *)
(* ------------------------------------------------------------------------- *)

let X86_SINGLE_STEP_TAC th s =
  time (X86_VERBOSE_STEP_TAC th s) THEN
  DISCARD_OLDSTATE_TAC s THEN
  CLARIFY_TAC;;

let X86_VACCSTEP_TAC th aflag s =
  X86_VERBOSE_STEP_TAC th s THEN
  (if aflag then TRY(ACCUMULATE_ARITH_TAC s THEN CLARIFY_TAC) else ALL_TAC);;

let X86_XACCSTEP_TAC th excs aflag s =
  X86_SINGLE_STEP_TAC th s THEN
  (if aflag then TRY(ACCUMULATEX_ARITH_TAC excs s THEN CLARIFY_TAC)
   else ALL_TAC);;

(* X86_GEN_ACCSTEP_TAC runs acc_preproc before ACCUMULATE_ARITH_TAC. This is
   useful when the output goal of X86_SINGLE_STEP_TAC needs additional rewrites
   for accumulator to recognize it. *)
let X86_GEN_ACCSTEP_TAC acc_preproc th aflag s =
  X86_SINGLE_STEP_TAC th s THEN
  (if aflag then acc_preproc THEN TRY(ACCUMULATE_ARITH_TAC s THEN CLARIFY_TAC)
   else ALL_TAC);;

let X86_ACCSTEP_TAC th aflag s = X86_GEN_ACCSTEP_TAC ALL_TAC th aflag s;;

let X86_VSTEPS_TAC th snums =
  MAP_EVERY (X86_VERBOSE_STEP_TAC th) (statenames "s" snums);;

let X86_STEPS_TAC th snums =
  MAP_EVERY (X86_SINGLE_STEP_TAC th) (statenames "s" snums);;

let X86_VACCSTEPS_TAC th anums snums =
  MAP_EVERY (fun n -> X86_VACCSTEP_TAC th (mem n anums) ("s"^string_of_int n))
            snums;;

let X86_XACCSTEPS_TAC th excs anums snums =
  MAP_EVERY
   (fun n -> X86_XACCSTEP_TAC th excs (mem n anums) ("s"^string_of_int n))
   snums;;

(* X86_GEN_ACCSTEPS_TAC runs acc_preproc before ACCUMULATE_ARITH_TAC.
   acc_preproc is a function from string (which is a state name) to tactic. *)
let X86_GEN_ACCSTEPS_TAC acc_preproc th anums snums =
  MAP_EVERY
    (fun n ->
      let state_name = "s"^string_of_int n in
      X86_GEN_ACCSTEP_TAC (acc_preproc state_name) th (mem n anums) state_name)
    snums;;

let X86_ACCSTEPS_TAC th anums snums =
  X86_GEN_ACCSTEPS_TAC (fun _ -> ALL_TAC) th anums snums;;

let X86_QUICKSTEP_TAC th pats =
  let pats' =
   [`nonoverlapping_modulo a b c`; `bytes_loaded a b c`;
    `MAYCHANGE a b c`; `(a ,, b) c d`; `read RIP s = x`] @ pats in
  fun s -> time (X86_VERBOSE_STEP_TAC th s) THEN
           DISCARD_NONMATCHING_ASSUMPTIONS pats' THEN
           DISCARD_OLDSTATE_TAC s THEN
           CLARIFY_TAC;;

let X86_QUICKSTEPS_TAC th pats snums =
  MAP_EVERY (X86_QUICKSTEP_TAC th pats) (statenames "s" snums);;

let X86_QUICKSIM_TAC execth pats snums =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN X86_QUICKSTEPS_TAC execth pats snums THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN ASM_REWRITE_TAC[];;

(* ------------------------------------------------------------------------- *)
(* More convenient wrappings of basic simulation flow.                       *)
(* ------------------------------------------------------------------------- *)

let X86_SIM_TAC execth snums =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC execth snums THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN ASM_REWRITE_TAC[];;

let X86_ACCSIM_TAC execth anums snums =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN X86_ACCSTEPS_TAC execth anums snums THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN ASM_REWRITE_TAC[];;

(* ------------------------------------------------------------------------- *)
(* Simulate through a lemma in ?- ensures step P Q C ==> eventually R s      *)
(* ------------------------------------------------------------------------- *)

let (X86_BIGSTEP_TAC:(thm*thm option array)->string->tactic) =
  let lemma = prove
   (`P s /\ (!s':S. Q s' /\ C s s' ==> eventually step R s')
     ==> ensures step P Q C ==> eventually step R s`,
    STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [ensures] THEN
    DISCH_THEN(MP_TAC o SPEC `s:S`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(MESON[]
     `(!s:S. eventually step P s ==> eventually step Q s)
      ==> eventually step P s ==> eventually step Q s`) THEN
    GEN_REWRITE_TAC I [EVENTUALLY_IMP_EVENTUALLY] THEN
    ASM_REWRITE_TAC[]) in
  fun (execth1,_) sname (asl,w) ->
    let sv = mk_var(sname,type_of(rand(rand w))) in
    (GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
      (!simulation_precanon_thms) THEN
     MATCH_MP_TAC lemma THEN CONJ_TAC THENL
      [BETA_TAC THEN ASM_REWRITE_TAC[];
       BETA_TAC THEN X_GEN_TAC sv THEN
       REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
       GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [MAYCHANGE; SEQ_ID] THEN
       GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [GSYM SEQ_ASSOC] THEN
       GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [ASSIGNS_SEQ] THEN
       GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [ASSIGNS_THM] THEN
       REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
       NONSELFMODIFYING_STATE_UPDATE_TAC
        (MATCH_MP bytes_loaded_update execth1) THEN
       ASSUMPTION_STATE_UPDATE_TAC THEN
       MAYCHANGE_STATE_UPDATE_TAC THEN
       DISCH_THEN(K ALL_TAC) THEN DISCARD_OLDSTATE_TAC sname])
    (asl,w);;

(* ------------------------------------------------------------------------- *)
(* Simulate a subroutine, instantiating it from the state.                   *)
(* ------------------------------------------------------------------------- *)

let TWEAK_PC_OFFSET =
  let conv =
   GEN_REWRITE_CONV (RAND_CONV o RAND_CONV) [ARITH_RULE `pc = pc + 0`]
  and tweakneeded tm =
    match tm with
      Comb(Comb(Const("bytes_loaded",_),Var(_,_)),
           Comb(Const("word",_),Var("pc",_))) -> true
    | _ -> false in
  CONV_RULE(ONCE_DEPTH_CONV(conv o check tweakneeded));;

let X86_SUBROUTINE_SIM_TAC (machinecode,execth,offset,submachinecode,subth) =
  let subimpth =
    CONV_RULE NUM_REDUCE_CONV (REWRITE_RULE [LENGTH]
      (MATCH_MP bytes_loaded_of_append3
        (TRANS machinecode (N_SUBLIST_CONV (SPEC_ALL submachinecode) offset
           (rhs(concl machinecode)))))) in
  fun ilist0 n ->
    let sname = "s"^string_of_int(n-1)
    and sname' = "s"^string_of_int n in
    let svar = mk_var(sname,`:x86state`)
    and svar0 = mk_var("s",`:x86state`) in
    let ilist = map (vsubst[svar,svar0]) ilist0 in
    MP_TAC(TWEAK_PC_OFFSET(SPECL ilist subth)) THEN
    REWRITE_TAC[COMPUTE_LENGTH_RULE submachinecode] THEN
    ASM_REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS;
                    MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
                    WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    REWRITE_TAC[fst execth] THEN
    REWRITE_TAC[ALLPAIRS; ALL; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
    TRY(ANTS_TAC THENL
     [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
      REPEAT CONJ_TAC THEN
      TRY(CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN NO_TAC) THEN
      (NONOVERLAPPING_TAC ORELSE
       DISJ1_TAC THEN NONOVERLAPPING_TAC ORELSE
       DISJ2_TAC THEN NONOVERLAPPING_TAC);
      ALL_TAC]) THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)) THEN
    ASM_REWRITE_TAC[] THEN
    X86_BIGSTEP_TAC execth sname' THENL
     [MATCH_MP_TAC subimpth THEN FIRST_X_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    RULE_ASSUM_TAC(CONV_RULE(TRY_CONV
   (GEN_REWRITE_CONV I [MESON[ADD_ASSOC]
     `read RIP s = word((pc + m) + n) <=>
      read RIP s = word(pc + m + n)`] THENC
    funpow 3 RAND_CONV NUM_ADD_CONV)));;

let X86_SUBROUTINE_SIM_ABBREV_TAC tupper ilist0 =
  let tac = X86_SUBROUTINE_SIM_TAC tupper ilist0 in
  fun comp0 abn n (asl,w) ->
    let svar0 = mk_var("s",`:x86state`)
    and svar0' = mk_var("s'",`:x86state`)
    and svar = mk_var("s"^string_of_int(n-1),`:x86state`)
    and svar' = mk_var("s"^string_of_int n,`:x86state`) in
    let comp1 =
      rand(concl(PURE_ONCE_REWRITE_CONV (map snd asl)
        (vsubst[svar,svar0;svar',svar0'] comp0))) in
    (tac n THEN
     ABBREV_TAC(mk_eq(mk_var(abn,type_of comp1),comp1))) (asl,w);;

(* ------------------------------------------------------------------------- *)
(* Simulate a macro, generating subgoal from a template                      *)
(* ------------------------------------------------------------------------- *)

let X86_MACRO_SIM_ABBREV_TAC =
  let dest_pc tm =
    match tm with
      Comb(Const("word",_),Var("pc",_)) -> 0
    | Comb(Const("word",_),Comb(Comb(Const("+",_),Var("pc",_)),n)) ->
          dest_small_numeral n
    | _ -> failwith "dest_pc"
  and mk_pc =
    let pat0 = `word pc:int64`
    and patn = `word(pc + n):int64`
    and pan = `n:num` in
    fun n ->  if n = 0 then pat0
              else vsubst[mk_small_numeral n,pan] patn
  and grab_dest =
    let pat = `read (memory :> bytes(p,8 * n))` in
    fun th ->
      let cortm = rand(body(lhand(repeat (snd o dest_imp) (concl th)))) in
      hd(find_terms (can (term_match [] pat)) cortm)
  and extract_offsets =
    let rec exfn p acc l =
      match l with
       [] -> rev (p::acc)
      | (n,_)::t -> exfn (p+n) (p::acc) t in
    fun mc -> exfn 0 [] (decode_all(rand(concl mc))) in
  let rec skip_to_offset p offl =
    match offl with
     [] -> failwith "skip_to_offset"
    | (n::t) -> if n > p then failwith "skip_to_offset"
                else if n = p then offl
                else skip_to_offset p t in
  let get_statenpc =
    let fils = can (term_match [] `read RIP s = word n`) o concl o snd in
    fun asl ->
      let rips = concl(snd(find fils asl)) in
      rand(lhand rips),dest_pc(rand rips) in
  let simprule =
    CONV_RULE (ONCE_DEPTH_CONV NORMALIZE_ADD_SUBTRACT_WORD_CONV) o
    GEN_REWRITE_RULE ONCE_DEPTH_CONV
     [WORD_RULE `word_add z (word 0):int64 = z`] in
  fun mc ->
    let offl = extract_offsets mc in
    let execth = X86_MK_EXEC_RULE mc in
    fun codelen localvars template core_tac prep ilist ->
      let main_tac (asl,w) =
        let svp,pc = get_statenpc asl in
        let gv = genvar(type_of svp) in
        let n = int_of_string(implode(tl(explode(fst(dest_var svp))))) + 1 in
        let svn = mk_var("s"^string_of_int n,`:x86state`) in
        let pc' = hd(snd(chop_list codelen (skip_to_offset pc offl))) in
        let svs = svp::(mk_pc pc)::(mk_pc pc')::
                  end_itlist (@) (map (C assoc localvars) ilist) in
        let rawsg = simprule(SPECL svs (ASSUME template)) in
        let asimprule = PURE_REWRITE_RULE
         (filter (is_eq o concl) (map snd asl)) in
        let insig = (asimprule o simprule o asimprule) rawsg in
        let subg = mk_forall(gv,vsubst[gv,svp] (concl(simprule insig))) in
        let avoids = itlist (union o thm_frees o snd) asl (frees w) in
        let abv = mk_primed_var avoids (mk_var(hd ilist,`:num`)) in
        (SUBGOAL_THEN subg MP_TAC THENL
         [X_GEN_TAC gv THEN POP_ASSUM_LIST(K ALL_TAC) THEN
          REPEAT(GEN_TAC THEN DISCH_THEN(K ALL_TAC o SYM)) THEN
          core_tac THEN NO_TAC;
          ALL_TAC] THEN
         DISCH_THEN(MP_TAC o SPEC svp) THEN
         GEN_REWRITE_TAC (REPEATC o LAND_CONV) [FORALL_UNWIND_THM1] THEN
         DISCH_THEN(fun subth ->
          let dest = grab_dest subth in
          X86_SUBROUTINE_SIM_TAC(mc,execth,0,mc,subth) [] n THEN
          ABBREV_TAC (mk_eq(abv,mk_comb(dest,svn)))))
        (asl,w) in
     fun (asl,w) ->
        let sv,_ = get_statenpc asl in
        let n = int_of_string(implode(tl(explode(fst(dest_var sv))))) in
        (X86_STEPS_TAC execth ((n+1)--(n+prep)) THEN main_tac) (asl,w);;

(* ------------------------------------------------------------------------- *)
(* Fix up call/return boilerplate given core correctness.                    *)
(* ------------------------------------------------------------------------- *)

let X86_ADD_RETURN_NOSTACK_TAC =
  let lemma1 = prove
   (`ensures step P Q R /\
     (!s s'. P s /\ Q s' /\ R s s' ==> Q' s')
     ==> ensures step P (\s. Q s /\ Q' s) R`,
    ONCE_REWRITE_TAC[IMP_CONJ_ALT] THEN DISCH_TAC THEN
    MATCH_MP_TAC ENSURES_SUBLEMMA_THM THEN
    REWRITE_TAC[SUBSUMED_REFL] THEN ASM_MESON_TAC[]) in
  let lemma2 = prove
   (`C' subsumed C /\
     C ,, C = C /\
     (!s s'. progdata s /\ pcdata s /\ stackdata s /\ retdata s /\ P s /\
             Q s' /\ C' s s'
             ==> progdata s' /\ stackdata s' /\ retdata s') /\
     ensures step (\s. progdata s /\ stackdata s /\ retdata s /\ Q s) R C
     ==> ensures step (\s. progdata s /\ pcdata s /\ P s) Q C'
          ==> ensures step
               (\s. progdata s /\ pcdata s /\ stackdata s /\ retdata s /\ P s)
               R C`,
    ONCE_REWRITE_TAC[TAUT
     `a /\ b /\ p /\ q ==> r ==> s <=> a ==> b ==> p ==> r ==> q ==> s`] THEN
    DISCH_TAC THEN DISCH_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC(ONCE_REWRITE_RULE
     [TAUT `p /\ q /\ r ==> s <=> p /\ q ==> r ==> s`]
     ENSURES_TRANS_SIMPLE) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          ENSURES_FRAME_SUBSUMED)) THEN
    GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV)
     [TAUT `p /\ q /\ r /\ s <=> s /\ p /\ q /\ r`] THEN
    MATCH_MP_TAC lemma1 THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
          ENSURES_PRECONDITION_THM)) THEN
    SIMP_TAC[]) in
  fun execth coreth ->
    let coreth =
      REWRITE_RULE[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI]
      coreth in
    REWRITE_TAC [MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    MP_TAC coreth THEN REWRITE_TAC[fst execth] THEN
    REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALLPAIRS; ALL] THEN
    REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
    DISCH_THEN(fun th ->
      REPEAT GEN_TAC THEN
      TRY(DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
      MP_TAC th) THEN
    ASM_REWRITE_TAC[] THEN
    TRY(ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY DISJ2_TAC THEN NONOVERLAPPING_TAC;
      ALL_TAC]) THEN
    MATCH_MP_TAC lemma2 THEN REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [SUBSUMED_MAYCHANGE_TAC;
      MAYCHANGE_IDEMPOT_TAC;
      REPEAT GEN_TAC THEN REWRITE_TAC(!simulation_precanon_thms) THEN
      REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
      REWRITE_TAC[MAYCHANGE; SEQ_ID] THEN
      REWRITE_TAC[GSYM SEQ_ASSOC] THEN
      REWRITE_TAC[ASSIGNS_SEQ] THEN REWRITE_TAC[ASSIGNS_THM] THEN
      REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
      NONSELFMODIFYING_STATE_UPDATE_TAC
       (MATCH_MP bytes_loaded_update (fst execth)) THEN
      ASSUMPTION_STATE_UPDATE_TAC THEN
      DISCH_THEN(K ALL_TAC) THEN ASM_REWRITE_TAC[] THEN NO_TAC;
      REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
      REPEAT(FIRST_X_ASSUM(DISJ_CASES_TAC o check
       (can (term_match [] `read PC s = a \/ Q` o concl)))) THEN
      X86_STEPS_TAC execth [1] THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]];;

(* ------------------------------------------------------------------------- *)
(* Version with register save/restore and stack adjustment.                  *)
(* ------------------------------------------------------------------------- *)

let GEN_X86_ADD_RETURN_STACK_TAC =
  let mono2lemma = MESON[]
   `(!x. (!y. P x y) ==> (!y. Q x y)) ==> (!x y. P x y) ==> (!x y. Q x y)` in
  fun execth coreth reglist stackoff (n,m) ->
    let regs = dest_list reglist in
    MP_TAC coreth THEN REWRITE_TAC[fst execth] THEN
    REWRITE_TAC [MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
                 WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    REPEAT(MATCH_MP_TAC mono2lemma THEN GEN_TAC) THEN
    (if vfree_in `RSP` (concl coreth) then
      DISCH_THEN(fun th -> WORD_FORALL_OFFSET_TAC stackoff THEN MP_TAC th) THEN
      MATCH_MP_TAC MONO_FORALL THEN GEN_TAC
     else
      MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
      DISCH_THEN(fun th ->
        WORD_FORALL_OFFSET_TAC stackoff THEN MP_TAC th)) THEN
    REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALLPAIRS; ALL] THEN
    REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
    REWRITE_TAC[WINDOWS_C_ARGUMENTS; WINDOWS_C_RETURN] THEN
    DISCH_THEN(fun th ->
      REPEAT GEN_TAC THEN
      TRY(DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
      MP_TAC th) THEN
    ASM_REWRITE_TAC[] THEN
    TRY(ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY DISJ2_TAC THEN NONOVERLAPPING_TAC;
      ALL_TAC]) THEN
    DISCH_THEN(fun th ->
      MAP_EVERY (fun c -> ENSURES_PRESERVED_TAC ("init_"^fst(dest_const c)) c)
                regs THEN
      REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
      X86_STEPS_TAC execth (1--n) THEN
      MP_TAC th) THEN
    X86_BIGSTEP_TAC execth ("s"^string_of_int(n+1)) THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    X86_STEPS_TAC execth ((n+2)--(m+n+1)) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

let X86_ADD_RETURN_STACK_TAC execth coreth reglist stackoff =
  let n0 = length(dest_list reglist) in
  let n = if 8 * n0 = stackoff then n0 else n0 + 1 in
  GEN_X86_ADD_RETURN_STACK_TAC execth coreth reglist stackoff (n,n+1);;

(* ------------------------------------------------------------------------- *)
(* Additional tools for refined "bytes_loaded ... (BUTLAST l)" variants.     *)
(* ------------------------------------------------------------------------- *)

let X86_TRIM_EXEC_RULE =
  let trimth = AP_TERM `BUTLAST:byte list->byte list`
  and pushr = GEN_REWRITE_RULE (RAND_CONV o TOP_SWEEP_CONV)
               [BUTLAST_CLAUSES] in
  pushr o trimth;;

let X86_MK_CORE_EXEC_RULE = X86_MK_EXEC_RULE o X86_TRIM_EXEC_RULE;;

let X86_CORE_PROMOTE =
  let lemma = prove
   (`(ensures x86 (\s. bytes_loaded s (word pc) (BUTLAST l) /\ P s) Q C
      ==> ensures x86 (\s. bytes_loaded s (word pc) l /\ P s) Q C) /\
     ((A ==> ensures x86 (\s. bytes_loaded s (word pc) (BUTLAST l) /\ P s) Q C)
      ==> A ==> ensures x86 (\s. bytes_loaded s (word pc) l /\ P s) Q C)`,
    MATCH_MP_TAC(TAUT `(p ==> q) /\ p ==> p /\ q`) THEN
    CONJ_TAC THENL [CONV_TAC TAUT; ALL_TAC] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] ENSURES_PRECONDITION_THM) THEN
    GEN_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC MONO_AND THEN
    REWRITE_TAC[BYTES_LOADED_BUTLAST]) in
  let rule1 = MATCH_MP(CONJUNCT1 lemma)
  and rule2 = MATCH_MP(CONJUNCT2 lemma) in
  fun th -> let avs,bod = strip_forall(concl th) in
            let sth = SPECL avs th in
            let gth = try rule2 sth with Failure _ -> rule1 sth in
            GENL avs gth;;

let X86_PROMOTE_RETURN_NOSTACK_TAC mc core =
  X86_ADD_RETURN_NOSTACK_TAC (X86_MK_EXEC_RULE mc) (X86_CORE_PROMOTE core);;

let X86_PROMOTE_RETURN_STACK_TAC mc core regs off =
  X86_ADD_RETURN_STACK_TAC
    (X86_MK_EXEC_RULE mc) (X86_CORE_PROMOTE core) regs off;;

(* ------------------------------------------------------------------------- *)
(* Wrap up function for the Windows ABI                                      *)
(* ------------------------------------------------------------------------- *)

let WINDOWS_ABI_STACK_THM = prove
 (`(read RSP s = stackpointer /\ P /\
    WINDOWS_C_ARGUMENTS [a1; a2; a3; a4; a5] s /\ Q <=>
    read RSP s = stackpointer /\ P /\
    (WINDOWS_C_ARGUMENTS [a1; a2; a3; a4] s /\
     read (memory :> bytes64 (word_add stackpointer (word 40))) s = a5) /\
    Q) /\
   (read RSP s = stackpointer /\ P /\
    WINDOWS_C_ARGUMENTS [a1; a2; a3; a4; a5; a6] s /\ Q <=>
    read RSP s = stackpointer /\ P /\
    (WINDOWS_C_ARGUMENTS [a1; a2; a3; a4] s /\
     read (memory :> bytes64 (word_add stackpointer (word 40))) s = a5 /\
     read (memory :> bytes64 (word_add stackpointer (word 48))) s = a6) /\
    Q) /\
   (read RSP s = stackpointer /\ P /\
    WINDOWS_C_ARGUMENTS [a1; a2; a3; a4; a5] s <=>
    read RSP s = stackpointer /\ P /\
    (WINDOWS_C_ARGUMENTS [a1; a2; a3; a4] s /\
     read (memory :> bytes64 (word_add stackpointer (word 40))) s = a5)) /\
   (read RSP s = stackpointer /\ P /\
    WINDOWS_C_ARGUMENTS [a1; a2; a3; a4; a5; a6] s <=>
    read RSP s = stackpointer /\ P /\
    (WINDOWS_C_ARGUMENTS [a1; a2; a3; a4] s /\
     read (memory :> bytes64 (word_add stackpointer (word 40))) s = a5 /\
     read (memory :> bytes64 (word_add stackpointer (word 48))) s = a6))`,
  REWRITE_TAC[WINDOWS_C_ARGUMENTS] THEN MESON_TAC[]);;

let WINDOWS_X86_WRAP_NOSTACK_TAC =
  let mono2lemma = MESON[]
     `(!x. (!y. P x y) ==> (!y. Q x y)) ==> (!x y. P x y) ==> (!x y. Q x y)`
  and pcofflemma = MESON[]
    `!n:num. (!x. P(x + n) ==> Q x) ==> (!x. P x) ==> (!x. Q x)`
  and pcplusplus_conv =
    GEN_REWRITE_CONV I
     [MESON[ADD_ASSOC] `word((pc + m) + n) = word(pc + m + n)`] THENC
    RAND_CONV(RAND_CONV NUM_ADD_CONV)
  and count_args =
    let argy = `WINDOWS_C_ARGUMENTS` in
    let is_nargle t = is_comb t && rator t = argy in
    length o dest_list o rand o find_term is_nargle in
  fun winmc stdmc coreth (asl,w) ->
    let nargs = count_args w in
    let prolog_len = 2 + nargs
    and epilog_len = 3
    and stackoff = 16
    and pcoff = match nargs with
      1 -> 5 | 2 -> 8 | 3 -> 11 | 4 -> 14 | 5 -> 19 | 6 -> 24 | _ -> 0 in
    let interstate = "s"^string_of_int(prolog_len+1)
    and subimpth =
      CONV_RULE NUM_REDUCE_CONV (REWRITE_RULE [LENGTH]
        (MATCH_MP bytes_loaded_of_append3
          (TRANS winmc (N_SUBLIST_CONV
             (SPEC_ALL (X86_TRIM_EXEC_RULE stdmc)) pcoff
             (rhs(concl winmc))))))
    and winexecth = X86_MK_EXEC_RULE winmc in
    let coreth = REWRITE_RULE
      [MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] coreth in
   (REWRITE_TAC [WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    PURE_REWRITE_TAC[WINDOWS_ABI_STACK_THM] THEN
    MP_TAC coreth THEN REWRITE_TAC[fst winexecth] THEN
    REPEAT(MATCH_MP_TAC mono2lemma THEN GEN_TAC) THEN
    MATCH_MP_TAC pcofflemma THEN
    EXISTS_TAC (mk_small_numeral pcoff) THEN GEN_TAC THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV pcplusplus_conv)) THEN
    DISCH_THEN(fun th -> WORD_FORALL_OFFSET_TAC stackoff THEN MP_TAC th) THEN
    REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALLPAIRS; ALL] THEN
    REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
    REWRITE_TAC[WINDOWS_C_ARGUMENTS; WINDOWS_C_RETURN; SOME_FLAGS] THEN
    DISCH_THEN(fun th ->
        REPEAT GEN_TAC THEN
        TRY(DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
        MP_TAC th) THEN
    ASM_REWRITE_TAC[] THEN
    TRY(ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY DISJ2_TAC THEN NONOVERLAPPING_TAC;
      ALL_TAC]) THEN
    DISCH_THEN(fun th ->
        ENSURES_PRESERVED_TAC "init_rsi" `RSI` THEN
        ENSURES_PRESERVED_TAC "init_rdi" `RDI` THEN
        REWRITE_TAC(!simulation_precanon_thms) THEN
        ENSURES_INIT_TAC "s0" THEN
        X86_STEPS_TAC winexecth (1--prolog_len) THEN
        MP_TAC th) THEN
    X86_BIGSTEP_TAC winexecth interstate THENL
     [MATCH_MP_TAC subimpth THEN FIRST_X_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    X86_STEPS_TAC winexecth ((prolog_len+2)--(prolog_len+epilog_len+1)) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]) (asl,w);;

let WINDOWS_X86_WRAP_STACK_TAC =
  let monopsrlemma = MESON[]
     `(!x. P x ==> !p s r. Q x p s r)
      ==> (!x. P x) ==> (!x p s r. Q x p s r)`
  and pcofflemma = MESON[]
    `!n:num. (!x. P(x + n) ==> Q x) ==> (!x. P x) ==> (!x. Q x)`
  and pcplusplus_conv =
    GEN_REWRITE_CONV I
     [MESON[ADD_ASSOC] `word((pc + m) + n) = word(pc + m + n)`] THENC
    RAND_CONV(RAND_CONV NUM_ADD_CONV)
  and count_args =
    let argy = `WINDOWS_C_ARGUMENTS` in
    let is_nargle t = is_comb t && rator t = argy in
    length o dest_list o rand o find_term is_nargle in
  fun winmc stdmc coreth reglist stdstackoff (asl,w) ->
    let stdregs = dest_list reglist in
    let n =
      let n0 = length stdregs in if 8 * n0 = stdstackoff then n0 else n0 + 1 in
    let regs = [`RSI`; `RDI`] @ stdregs
    and stackoff = stdstackoff + 16 in
    let nargs = count_args w in
    let prolog_len = 2 + nargs + n
    and epilog_len = 3 + n in
    let pcoff =  match nargs with
      1 -> 5 | 2 -> 8 | 3 -> 11 | 4 -> 14 | 5 -> 19 | 6 -> 24 | _ -> 0 in
    let interstate = "s"^string_of_int(prolog_len+1)
    and subimpth =
      CONV_RULE NUM_REDUCE_CONV (REWRITE_RULE [LENGTH]
        (MATCH_MP bytes_loaded_of_append3
          (TRANS winmc (N_SUBLIST_CONV
             (SPEC_ALL (X86_TRIM_EXEC_RULE stdmc)) pcoff
             (rhs(concl winmc))))))
    and winexecth = X86_MK_EXEC_RULE winmc in
   (REWRITE_TAC [WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    PURE_REWRITE_TAC[WINDOWS_ABI_STACK_THM] THEN
    MP_TAC coreth THEN REWRITE_TAC[fst winexecth] THEN
    REPEAT(MATCH_MP_TAC monopsrlemma THEN GEN_TAC) THEN
    MATCH_MP_TAC pcofflemma THEN
    EXISTS_TAC (mk_small_numeral pcoff) THEN GEN_TAC THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV pcplusplus_conv)) THEN
    (if vfree_in `RSP` (concl coreth) then
     DISCH_THEN(fun th -> WORD_FORALL_OFFSET_TAC stackoff THEN MP_TAC th) THEN
     MATCH_MP_TAC MONO_FORALL THEN GEN_TAC
    else
     DISCH_THEN(fun th ->
       WORD_FORALL_OFFSET_TAC stackoff THEN MP_TAC th)) THEN
    REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALLPAIRS; ALL] THEN
    REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
    REWRITE_TAC[WINDOWS_C_ARGUMENTS; WINDOWS_C_RETURN; SOME_FLAGS] THEN
    DISCH_THEN(fun th ->
        REPEAT GEN_TAC THEN
        TRY(DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
        MP_TAC th) THEN
    ASM_REWRITE_TAC[] THEN
    TRY(ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY DISJ2_TAC THEN NONOVERLAPPING_TAC;
      ALL_TAC]) THEN
     DISCH_THEN(fun th ->
      MAP_EVERY (fun c ->
                    ENSURES_PRESERVED_TAC ("init_"^fst(dest_const c)) c)
                regs THEN
      REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
      X86_STEPS_TAC winexecth (1--prolog_len) THEN
      MP_TAC th) THEN
    X86_BIGSTEP_TAC winexecth interstate THENL
     [MATCH_MP_TAC subimpth THEN FIRST_X_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    X86_STEPS_TAC winexecth ((prolog_len+2)--(prolog_len+epilog_len+1)) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]) (asl,w);;

(* ------------------------------------------------------------------------- *)
(* Generalize MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI where the            *)
(* standard ABI form is used as a Windows subroutine, basically by repeating *)
(* the standard subroutine wrapper process on a modified version.            *)
(* This is useful where the core subroutine does not use SIMD registers      *)
(* since MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI doesn't imply that.       *)
(* ------------------------------------------------------------------------- *)

let X86_SIMD_SHARPEN_RULE =
  let subfn = subst
   [`MAYCHANGE [RIP] ,,
     MAYCHANGE [RAX; RCX; RDX; RSI; RDI; R8; R9; R10; R11] ,,
     MAYCHANGE [CF; PF; AF; ZF; SF; OF]`,
    `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI`] in
  fun stdthm tac ->
    let stdthm' = subfn(concl stdthm) in prove(stdthm',tac);;

(* ------------------------------------------------------------------------- *)
(* Tweak a standard correctness theorem to use the version with an           *)
(* initial ENDBR64 before the same code, assuming they are defined           *)
(* together in the standard way.                                             *)
(* ------------------------------------------------------------------------- *)

let IBT_WRAP_THM = prove
 (`R ,, R = R /\ MAYCHANGE [RIP] subsumed R /\
   (!s y. P(write RIP y s) <=> P s) /\
   ensures x86
    (\s. bytes_loaded s (word (pc + 4)) mc /\
         read RIP s = word (pc + 4) /\
         P s) Q R
   ==> ensures x86
        (\s. bytes_loaded s (word pc)
               (APPEND [word 0xf3; word 0x0f; word 0x1e; word 0xfa] mc) /\
             read RIP s = word pc /\
             P s) Q R`,
  let execlen =
    REWRITE_CONV[LENGTH_APPEND; LENGTH; ARITH]
     `LENGTH(APPEND [word 0xf3:byte; word 0x0f; word 0x1e; word 0xfa] mc)`
  and execstart = prove
   (`!s pc. bytes_loaded s (word pc)
                    (APPEND [word 0xf3; word 0x0f; word 0x1e; word 0xfa] mc)
            ==> x86_decode s (word pc) (4,ENDBR64)`,
    REPEAT GEN_TAC THEN REWRITE_TAC[bytes_loaded_append] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    let Some th = (snd(X86_MK_EXEC_RULE
     (REFL `[word 243; word 15; word 30; word 250]:byte list`))).(0) in
    REWRITE_TAC[th]) in
  let execth = (execlen,[|Some execstart; None; None; None|]) in
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
  EXISTS_TAC `(MAYCHANGE [RIP] ,, R):x86state->x86state->bool` THEN
  ASM_SIMP_TAC[SUBSUMED_FOR_SEQ; SUBSUMED_REFL] THEN
  MATCH_MP_TAC ENSURES_TRANS THEN
  EXISTS_TAC `\s. bytes_loaded s (word (pc + 4)) mc /\
                  read RIP s = word (pc + 4) /\
                  P s` THEN
  ASM_REWRITE_TAC[] THEN X86_SIM_TAC execth [1] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o CONJUNCT2 o REWRITE_RULE[bytes_loaded_append]) THEN
    CONV_TAC(ONCE_DEPTH_CONV LENGTH_CONV) THEN REWRITE_TAC[WORD_ADD];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE
        (RATOR_CONV o RATOR_CONV) [MAYCHANGE_SING]) THEN
    REWRITE_TAC[ASSIGNS; assign] THEN ASM_MESON_TAC[]]);;

let ADD_IBT_TAC =
  let tweak = subst[`pc + 4`,`pc:num`]
  and EXPAND_TRIMMED_RULE =
    let pth = prove
     (`CONS (a:byte) (CONS b (CONS c (CONS d l))) = APPEND [a;b;c;d] l`,
      REWRITE_TAC[APPEND]) in
    fun fullmc trimc ->
     GEN_REWRITE_RULE (RAND_CONV o RAND_CONV) [GSYM trimc]
     (GEN_REWRITE_RULE RAND_CONV [pth] fullmc) in
  fun fullmc trimc th ->
    let expth = EXPAND_TRIMMED_RULE fullmc trimc in
    W(fun (asl,w) ->
          let avs = fst(strip_forall w) in
          MAP_EVERY X_GEN_TAC avs THEN MP_TAC(SPECL (map tweak avs) th)) THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    REWRITE_TAC[C_ARGUMENTS; C_RETURN;
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
                WINDOWS_C_ARGUMENTS; ALL; ALLPAIRS;
                WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    TRY(MATCH_MP_TAC MONO_IMP THEN CONJ_TAC THENL
     [REPEAT(REWRITE_TAC[] THEN
             ((MATCH_MP_TAC MONO_AND THEN CONJ_TAC) ORELSE
              (MATCH_MP_TAC MONO_OR THEN CONJ_TAC))) THEN
      REWRITE_TAC[expth; LENGTH; ARITH; LENGTH_APPEND] THEN
      REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
      MATCH_MP_TAC(ONCE_REWRITE_RULE [IMP_CONJ_ALT]
        NONOVERLAPPING_MODULO_SUBREGIONS) THEN
      REWRITE_TAC[CONTAINED_MODULO_REFL; LE_REFL] THEN
      MATCH_MP_TAC CONTAINED_MODULO_SIMPLE THEN ARITH_TAC;
      ALL_TAC]) THEN
    DISCH_TAC THEN REWRITE_TAC[expth; GSYM APPEND_ASSOC] THEN
    MATCH_MP_TAC IBT_WRAP_THM THEN REPEAT CONJ_TAC THENL
     [MAYCHANGE_IDEMPOT_TAC;
      SUBSUMED_MAYCHANGE_TAC;
      REPEAT GEN_TAC THEN
      CONV_TAC(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
      REFL_TAC;
      FIRST_X_ASSUM ACCEPT_TAC];;

let ADD_IBT_RULE th =
  let bldat =
   rand(lhand(body(lhand(rator
    (repeat (snd o dest_imp) (snd(strip_forall(concl th)))))))) in
  let trimctm = if is_const bldat then bldat else lhand bldat in
  let trimcd = find ((=) trimctm o lhand o concl) (definitions()) in
  let fullmctm = rand(rand(concl trimcd)) in
  let fullmc = find ((=) fullmctm o lhand o concl) (definitions()) in
  let trimc =
    CONV_RULE (RAND_CONV TRIM_LIST_CONV)
     (GEN_REWRITE_RULE (RAND_CONV o RAND_CONV) [fullmc] trimcd) in
  let rec adjust tm =
    match tm with
      Comb(Comb(Const(",",_),Comb(Const("word",_),Var("pc",_))) as rat,off)
          when is_numeral off ->
        mk_comb(rat,mk_numeral(num 4 +/ dest_numeral off))
    | Comb(s,t) -> mk_comb(adjust s,adjust t)
    | Abs(x,t) -> mk_abs(x,adjust t)
    | _ -> if tm = trimctm then  fullmctm else tm in
  prove(adjust (concl th),
        ADD_IBT_TAC fullmc trimc th);;
