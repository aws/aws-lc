(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ------------------------------------------------------------------------- *)
(* Encoding the registers and flags as a 32-element list of numbers.         *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/base.ml";;

let regfile = new_definition
 `regfile s =
   [val(read X0 s); val(read X1 s); val(read X2 s); val(read X3 s);
    val(read X4 s); val(read X5 s); val(read X6 s); val(read X7 s);
    val(read X8 s); val(read X9 s); val(read X10 s); val(read X11 s);
    val(read X12 s); val(read X13 s); val(read X14 s); val(read X15 s);
    val(read X16 s); val(read X17 s); val(read X18 s); val(read X19 s);
    val(read X20 s); val(read X21 s); val(read X22 s); val(read X23 s);
    val(read X24 s); val(read X25 s); val(read X26 s); val(read X27 s);
    val(read X28 s); val(read X29 s); val(read X30 s);
    bitval(read VF s) + 2 * bitval(read CF s) +
    4 * bitval(read ZF s) + 8 * bitval(read NF s);
    val(read Q0 s); val(read Q1 s); val(read Q2 s); val(read Q3 s);
    val(read Q4 s); val(read Q5 s); val(read Q6 s); val(read Q7 s);
    val(read Q8 s); val(read Q9 s); val(read Q10 s); val(read Q11 s);
    val(read Q12 s); val(read Q13 s); val(read Q14 s); val(read Q15 s);
    val(read Q16 s); val(read Q17 s); val(read Q18 s); val(read Q19 s);
    val(read Q20 s); val(read Q21 s); val(read Q22 s); val(read Q23 s);
    val(read Q24 s); val(read Q25 s); val(read Q26 s); val(read Q27 s);
    val(read Q28 s); val(read Q29 s); val(read Q30 s); val(read Q31 s);
    val(read (memory :> bytes128(read SP s)) s);
    val(read (memory :> bytes128(word_add (read SP s) (word 16))) s);
    val(read (memory :> bytes128(word_add (read SP s) (word 32))) s);
    val(read (memory :> bytes128(word_add (read SP s) (word 48))) s);
    val(read (memory :> bytes128(word_add (read SP s) (word 64))) s);
    val(read (memory :> bytes128(word_add (read SP s) (word 80))) s);
    val(read (memory :> bytes128(word_add (read SP s) (word 96))) s);
    val(read (memory :> bytes128(word_add (read SP s) (word 112))) s);
    val(read (memory :> bytes128(word_add (read SP s) (word 128))) s);
    val(read (memory :> bytes128(word_add (read SP s) (word 144))) s);
    val(read (memory :> bytes128(word_add (read SP s) (word 160))) s);
    val(read (memory :> bytes128(word_add (read SP s) (word 176))) s);
    val(read (memory :> bytes128(word_add (read SP s) (word 192))) s);
    val(read (memory :> bytes128(word_add (read SP s) (word 208))) s);
    val(read (memory :> bytes128(word_add (read SP s) (word 224))) s);
    val(read (memory :> bytes128(word_add (read SP s) (word 240))) s)]`;;

let FLAGENCODING_11 = prove
 (`bitval b0 + 2 * bitval b1 + 4 * bitval b2 + 8 * bitval b3 = n <=>
   n < 16 /\
   (b0 <=> ODD n) /\
   (b1 <=> ODD(n DIV 2)) /\
   (b2 <=> ODD(n DIV 4)) /\
   (b3 <=> ODD(n DIV 8))`,
  REWRITE_TAC[bitval] THEN REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  (EQ_TAC THENL
    [DISCH_THEN(SUBST1_TAC o SYM) THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC]) THEN
  REWRITE_TAC[IMP_CONJ] THEN SPEC_TAC(`n:num`,`n:num`) THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* Random numbers with random bit density, random state for simulating.      *)
(* ------------------------------------------------------------------------- *)

let random_boold d = Random.int 64 < d;;

let randomnd n density =
    funpow n (fun n ->
      (if random_boold density then num_1 else num_0) +/ num_2 */ n) num_0;;

let random64() = randomnd 64 (Random.int 65);;

let random_regstate () =
  let d = Random.int 65 in
  map (fun _ -> randomnd 64 d) (0--30) @
  [mod_num (random64()) (num 16)] @
  map (fun _ -> randomnd 128 d) (0--31) @
  map (fun _ -> randomnd 128 d) (0--15);;

(* ------------------------------------------------------------------------- *)
(* Generate random instance of instruction class itself.                     *)
(* ------------------------------------------------------------------------- *)

let classbit s =
  match s with
   "0" -> num_0
  | "1" -> num_1
  | _ -> if Random.bool() then num_1 else num_0;;

let random_iclass s =
  if String.length s <> 32 then failwith "random_iclass: malformed string"
  else itlist (fun c n -> classbit c +/ num 2 */ n) (rev(explode s)) num_0;;

let random_instruction iclasses =
  let iclass = el (Random.int (length iclasses)) iclasses in
  random_iclass iclass;;

(* ------------------------------------------------------------------------- *)
(* Load iclasses.                                                            *)
(* ------------------------------------------------------------------------- *)

loadt "arm/proofs/simulator_iclasses.ml";;

check_insns();;

(* ------------------------------------------------------------------------- *)
(* Run a random example.                                                     *)
(* ------------------------------------------------------------------------- *)

let template =
 `aligned 16 stackpointer /\
  nonoverlapping (word pc,LENGTH ibytes) (stackpointer,256)
  ==> ensures arm
       (\s. aligned_bytes_loaded s (word pc) ibytes /\
            read PC s = word pc /\
            read SP s = stackpointer /\
            regfile s = input_state)
       (\s. read SP s = stackpointer /\
            regfile s = output_state)
       (MAYCHANGE [PC; SP; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                   X10; X11; X12; X13; X14; X15; X16; X17; X18; X19;
                   X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30] ,,
        MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9;
                   Q10; Q11; Q12; Q13; Q14; Q15; Q16; Q17; Q18; Q19;
                   Q20; Q21; Q22; Q23; Q24; Q25; Q26; Q27; Q28; Q29;
                   Q30; Q31] ,,
        MAYCHANGE [memory :> bytes(stackpointer,256)] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`;;

let num_two_to_64 = Num.num_of_string "18446744073709551616";;

(* This makes MESON quiet. *)
verbose := false;;


let READ_MEMORY_MERGE_CONV =
  let baseconv =
    GEN_REWRITE_CONV I [READ_MEMORY_BYTESIZED_SPLIT] THENC
    LAND_CONV(LAND_CONV(RAND_CONV(RAND_CONV
     (TRY_CONV(GEN_REWRITE_CONV I [GSYM WORD_ADD_ASSOC] THENC
               RAND_CONV WORD_ADD_CONV))))) in
  let rec conv tm =
    (baseconv THENC BINOP_CONV(TRY_CONV conv)) tm in
  conv;;

let MEMORY_SPLIT_TAC k =
  let tac =
    STRIP_ASSUME_TAC o
    CONV_RULE (BINOP_CONV(BINOP2_CONV
       (ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) WORD_REDUCE_CONV)) o
    GEN_REWRITE_RULE I [el k (CONJUNCTS READ_MEMORY_BYTESIZED_UNSPLIT)] in
  EVERY_ASSUM (fun th -> try tac th with Failure _ -> ALL_TAC);;

(*** Before and after tactics for goals that either do or don't involve
 *** memory operations (memop = they do). Non-memory ones are simpler and
 *** quicker; the memory ones do some more elaborate fiddling with format
 *** of memory assumptions to maximize their usability.
 ***)

let extra_simp_tac =
  REWRITE_TAC[WORD_RULE `word_sub x (word_add x y):N word = word_neg y`;
              WORD_RULE `word_sub y (word_add x y):N word = word_neg x`;
              WORD_RULE `word_sub (word_add x y) x:N word = y`;
              WORD_RULE `word_sub (word_add x y) y:N word = x`;
              WORD_ADD_0; WORD_SUB_0] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN REWRITE_TAC[];;

let tac_before memop =
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN STRIP_TAC THEN
  REWRITE_TAC[regfile; CONS_11; FLAGENCODING_11; VAL_WORD_GALOIS] THEN
  REWRITE_TAC[DIMINDEX_64; DIMINDEX_128] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[SOME_FLAGS] THEN ONCE_REWRITE_TAC[MESON[]
   `read SP s = stackpointer /\ P (read SP s) s <=>
    read SP s = stackpointer /\ P stackpointer s`] THEN
  ENSURES_INIT_TAC "s0" THEN
  (if memop then
    MAP_EVERY MEMORY_SPLIT_TAC (1--4) THEN
          (* Remove non-"memory :> bytes8" reads because they are not necessary :) *)
    let non_byte_read_list = [
      `read (memory :> bytes16 x) s = y`;
      `read (memory :> bytes32 x) s = y`;
      `read (memory :> bytes64 x) s = y`;
      `read (memory :> bytes128 x) s = y`
    ] in
    DISCARD_MATCHING_ASSUMPTIONS non_byte_read_list
  else ALL_TAC)
and tac_main (memopidx: int option) mc states =
  begin match memopidx with
  | Some idx ->
    let states1, states2 = chop_list idx states in
    (if states1 <> [] then ARM_STEPS_TAC mc states1 else ALL_TAC) THEN
    (if states2 <> [] then ARM_VSTEPS_TAC mc states2 else ALL_TAC)
  | None -> ARM_STEPS_TAC mc states
  end
and tac_after memop =
  (if memop then MAP_EVERY MEMORY_SPLIT_TAC (0--4) else ALL_TAC) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  (if memop then CONV_TAC(ONCE_DEPTH_CONV READ_MEMORY_MERGE_CONV)
   else ALL_TAC) THEN
  ASM_REWRITE_TAC[] THEN extra_simp_tac THEN
  PRINT_GOAL_TAC THEN NO_TAC;;

(*** Cosimulate a list of ARM instruction codes against hardware.
 *** To pass, the formal simulation has to agree with the hardware,
 *** only modify the 256-byte buffer [SP,..,SP+255] and also
 *** leave the final SP value the same as the initial value, though
 *** it can be modified in between.
 ***)

let cosimulate_instructions (memopidx: int option) icodes =
  let icodestring =
    end_itlist (fun s t -> s^","^t) (map string_of_num_hex icodes) in
  let _ =
    (Format.print_string("Cosimulating "^icodestring);
     Format.print_newline()) in

  let ibytes = itlist
    (fun c s ->
     mod_num c (num 256) ::
     mod_num (quo_num c (num 256)) (num 256) ::
     mod_num (quo_num c (num 65536)) (num 256) ::
     quo_num c (num 16777216) :: s) icodes [] in

  let ibyteterm =
    mk_flist(map (curry mk_comb `word:num->byte` o mk_numeral) ibytes) in

  let input_state = random_regstate() in

  let outfile = Filename.temp_file "armsimulator" ".out" in

  let command_arg =
    (* Split q registers that are 128 bits to 64 + 64 bits *)
    let xregs, qmem = chop_list 32 input_state in
    xregs @
    List.concat (map (fun n ->
      [Num.mod_num n num_two_to_64; Num.quo_num n num_two_to_64]) qmem) in

  let command =
    rev_itlist (fun s t -> t ^ " " ^ string_of_num s) command_arg
    ("arm/proofs/armsimulate " ^ icodestring) ^
    " >" ^ outfile in

  let _ = Sys.command command in

  (*** This branch determines whether the actual simulation worked ***)
  (*** In each branch we try to confirm that we likewise do or don't ***)

  if strings_of_file outfile <> [] then
    let resultstring = string_of_file outfile in

    let output_state_raw =
      map (fun (Ident s) -> num_of_string s)
          (lex(explode resultstring)) in

    (* Synthesize q registers from two 64 ints *)
    let output_state =
      let xregs, qmem = chop_list 32 output_state_raw in
      xregs @ snd (List.fold_left (fun (prev_num, ls) n ->
        (* prev_num is None on 0, 2, 4, ..th item
           and Some n' on 1, 3, ..th item *)
        match prev_num with
        | None -> (Some n, ls)
        | Some n' -> (None, ls @ [num_two_to_64 */ n +/ n']))
       (None, []) qmem) in

    let goal = subst
      [ibyteterm,`ibytes:byte list`;
       mk_flist(map mk_numeral input_state),`input_state:num list`;
       mk_flist(map mk_numeral output_state),`output_state:num list`]
      template in

    let execth = ARM_MK_EXEC_RULE(REFL ibyteterm) in

    let decoded = mk_flist
     (map (rand o rand o snd o strip_forall o concl o Option.get)
          (filter Option.is_some (Array.to_list (snd execth))))
    and result =
    can prove
     (goal,
      PURE_REWRITE_TAC [fst execth] THEN
      (tac_before (memopidx <> None) THEN
       tac_main memopidx execth (1--length icodes) THEN
       tac_after (memopidx <> None))) in
    (decoded,result)
  else
    let decoded = mk_flist(map mk_numeral icodes) in
    decoded,not(can ARM_MK_EXEC_RULE(REFL ibyteterm));;

(*** Pick random instances from register-to-register iclasses and run ***)

let run_random_regsimulation () =
  let icode:num = random_instruction iclasses in
  cosimulate_instructions None [icode];;

(* ------------------------------------------------------------------------- *)
(* Setting up safe self-contained tests for load-store instructions.         *)
(* ------------------------------------------------------------------------- *)

let add_Xn_SP_imm rn imm =
  pow2 22 */ num_of_string "0b1001000100" +/
  pow2 10 */ (mod_num (num imm) (pow2 12)) +/
  pow2 5 */ num_of_string "0b11111" +/
  num rn;;

let sub_Xn_SP_imm rn imm =
  pow2 22 */ num_of_string "0b1101000100" +/
  pow2 10 */ (mod_num (num imm) (pow2 12)) +/
  pow2 5 */ num_of_string "0b11111" +/
  num rn;;

let sub_Xn_SP_Xn rn =
  pow2 21 */ num 0b11001011001 +/
  pow2 16 */ num rn +/
  pow2 10 */ num 0b011000 +/
  pow2 5 */ num 0b11111 +/
  num rn;;

let movz_Xn_imm rd imm =
  pow2 21 */ num_of_string "0b11010010100" +/
  pow2 5 */ num(imm mod 65536) +/
  num rd;;

(*** The post-register and no-offset modes are exercised only for LD1/ST1
 *** since they are not currently supported for LD2/ST2.
 ***
 *** The register field is forced to 0 in the no-offset case to unify
 *** the encoding scheme, and is forced to 31 (i.e. post-immediate in
 *** place of post-register) if any of these are true:
 ***
 ***  - it is LD2/ST2 (since post-register is not supported there)
 ***  - the offset register is the same as the base (confuses test harness)
 ***  - the base register is SP (alters final stack pointer in test harness)
 ***  - or just on a 50-50 probability, to avoid biasing to register case
 ***)

let cosimulate_ldst_12() =
  let datasize = Random.int 2
  and isld = Random.int 2
  and esize = Random.int 4
  and rn = Random.int 32
  and rt = Random.int 32 in
  let ldst2 = Random.int 2 in
  let someoffset = if ldst2 = 1 then 1 else Random.int 2 in
  let regoffr = Random.int 32 in
  let regoff =
    if someoffset = 0 then 0
    else if ldst2 = 1 || regoffr = rn || rn = 31 || Random.bool() then 31
    else regoffr in
  let stackoff =
    if rn = 31 then Random.int 14 * 16
    else Random.int 224 in
  let postinc = someoffset * 8 * (datasize + 1) * (ldst2 + 1) in
  let code =
    pow2 30 */ num datasize +/
    pow2 24 */ num 0b001100 +/
    pow2 23 */ num someoffset +/
    pow2 22 */ num isld +/
    pow2 16 */ num regoff +/
    pow2 12 */ num(if ldst2 = 1 then 0b1000 else 0b0111) +/
    pow2 10 */ num esize +/
    pow2 5 */ num rn +/
    num rt in
  if rn = 31 then
    [add_Xn_SP_imm 31 stackoff; code; sub_Xn_SP_imm 31 (stackoff + postinc)]
  else
    [add_Xn_SP_imm rn stackoff; code; sub_Xn_SP_Xn rn];;


(*** This covers LD1 and ST1 with two registers, with the
 *** addressing modes, no-offset and post-immediate offset.
 ***)

let cosimulate_ldst_1_2reg() =
  let someoffset = Random.int 2
  and rn = Random.int 32
  and isld = Random.int 2
  and rt = Random.int 32
  and esize = Random.int 4 in
  let stackoff =
    if rn = 31 then Random.int 14 * 16
    else Random.int 224 in
  let postinc = someoffset * 32 in
  let code =
    pow2 24 */ num 0b01001100 +/
    pow2 23 */ num someoffset +/
    pow2 22 */ num isld +/
    pow2 16 */ num(0b011111 * someoffset) +/
    pow2 12 */ num 0b1010 +/
    pow2 10 */ num esize +/
    pow2 5 */ num rn +/
    num rt in
  if rn = 31 then
    [add_Xn_SP_imm 31 stackoff; code; sub_Xn_SP_imm 31 (stackoff + postinc)]
  else
    [add_Xn_SP_imm rn stackoff; code; sub_Xn_SP_Xn rn];;

(*** This covers LDRB and STRB with unshifted register
 *** There are several more supported addressing modes to cover.
 ***)

let cosimulate_ldstrb() =
  let rn = Random.int 32
  and isld = Random.int 2 in
  let rm = (rn + 1 + Random.int 31) mod 32
  and rt = (rn + 1 + Random.int 31) mod 32 in
  let stackoff =
    if rn = 31 then Random.int 15 * 16
    else Random.int 256 in
  let regoff = Random.int (256-stackoff) in
  let code =
    pow2 23 */ num 0b001110000 +/
    pow2 22 */ num isld +/
    pow2 21 +/
    pow2 16 */ num rm +/
    pow2 10 */ num 0b011010 +/
    pow2 5 */ num rn +/
    num rt in
  if rn = 31 then
    [add_Xn_SP_imm 31 stackoff; movz_Xn_imm rm regoff; code; sub_Xn_SP_imm 31 stackoff]
  else
    [add_Xn_SP_imm rn stackoff; movz_Xn_imm rm regoff; code; sub_Xn_SP_Xn rn];;

(*** This covers LD1R ***)

let cosimulate_ld1r() =
  let q = Random.int 2
  and size = Random.int 4
  and rn = Random.int 32
  and rt = Random.int 32 in
  let stackoff =
    if rn = 31 then Random.int 14 * 16
    else Random.int 224 in
  let stackoff' = (Int.shift_left 8 size)/8 + stackoff in
  let code =
    pow2 30 */ num q +/
    pow2 12 */ num 0b001101110111111100 +/
    pow2 10 */ num size +/
    pow2 5 */ num rn +/
    num rt in
  if rn = 31 then
    [add_Xn_SP_imm 31 stackoff; code; sub_Xn_SP_imm 31 stackoff']
  else
    [add_Xn_SP_imm rn stackoff; code; sub_Xn_SP_Xn rn];;

let memclasses =
   [cosimulate_ldst_12; cosimulate_ldst_1_2reg; cosimulate_ldstrb; cosimulate_ld1r];;

let run_random_memopsimulation() =
  let icodes = el (Random.int (length memclasses)) memclasses () in
  let _ = assert (length icodes >= 2) in
  let memop_index = length icodes - 2 in
  cosimulate_instructions (Some memop_index) icodes;;

(* ------------------------------------------------------------------------- *)
(* Keep running tests till a failure happens then return it.                 *)
(* ------------------------------------------------------------------------- *)

let run_random_simulation() =
  if Random.int 100 < 90 then
    let decoded, result = run_random_regsimulation() in
    decoded,result,true
  else
    let decoded, result = run_random_memopsimulation() in
    decoded,result,false;;

let time_limit_sec = 1800.0;;
let tested_reg_instances = ref 0;;
let tested_mem_instances = ref 0;;

let rec run_random_simulations start_t =
  let decoded,result,isreg = run_random_simulation() in
  if result then begin
    tested_reg_instances := !tested_reg_instances + (if isreg then 1 else 0);
    tested_mem_instances := !tested_mem_instances + (if isreg then 0 else 1);
    let fey = if is_numeral (lhand decoded)
              then " (fails correctly) instruction codes " else " " in
    let _ = Format.print_string("OK:" ^ fey ^ string_of_term decoded);
            Format.print_newline() in
    let now_t = Sys.time() in
    if now_t -. start_t > time_limit_sec then
      let _ = Printf.printf "Finished (time limit: %fs, tested reg instances: %d, tested mem instances: %d, total: %d)\n"
          time_limit_sec !tested_reg_instances !tested_mem_instances
          (!tested_reg_instances + !tested_mem_instances) in
      None
    else run_random_simulations start_t
  end
  else Some (decoded,result);;

Random.self_init();;

let start_t = Sys.time() (* unit is sec *) in
  match run_random_simulations start_t with
  | Some (t,_) -> Printf.printf "Error: term `%s`" (string_of_term t);
                  failwith "simulator"
  | None -> ();;
