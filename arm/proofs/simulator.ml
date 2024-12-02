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
    val(read Q28 s); val(read Q29 s); val(read Q30 s); val(read Q31 s)]`;;

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
  map (fun _ -> randomnd 128 d) (0--31);;

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
 `ensures arm
     (\s. aligned_bytes_loaded s (word pc) ibytes /\
          read PC s = word pc /\
          regfile s = input_state)
     (\s. regfile s = output_state)
     (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                 X10; X11; X12; X13; X14; X15; X16; X17; X18; X19;
                 X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30] ,,
      MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9;
                 Q10; Q11; Q12; Q13; Q14; Q15; Q16; Q17; Q18; Q19;
                 Q20; Q21; Q22; Q23; Q24; Q25; Q26; Q27; Q28; Q29;
                 Q30; Q31] ,,
      MAYCHANGE SOME_FLAGS)`;;

let num_two_to_64 = Num.num_of_string "18446744073709551616";;

let rec split_first_n (ls: 'a list) (n: int) =
  if n = 0 then ([], ls)
  else match ls with
    | h::t -> let l1, l2 = split_first_n t (n-1) in (h::l1, l2)
    | [] -> failwith "n cannot be smaller than the length of ls";;

let run_random_simulation () =
  let icode:num = random_instruction iclasses in
  let _ = printf "random inst: decode %d\n" (Num.int_of_num icode) in

  let ibytes =
    [mod_num icode (num 256);
     mod_num (quo_num icode (num 256)) (num 256);
     mod_num (quo_num icode (num 65536)) (num 256);
     quo_num icode (num 16777216)] in

  let ibyteterm =
    mk_flist(map (curry mk_comb `word:num->byte` o mk_numeral) ibytes) in


  let input_state = random_regstate() in

  let outfile = Filename.temp_file "armsimulator" ".out" in

  let command_arg =
    (* Split q registers that are 128 bits to 64 + 64 bits *)
    let xregs, qregs = split_first_n input_state 32 in
    xregs @ List.concat (map (fun n -> [Num.mod_num n num_two_to_64; Num.quo_num n num_two_to_64]) qregs) in

  let command =
    rev_itlist (fun s t -> t ^ " " ^ string_of_num s) (icode::command_arg)
    "arm/proofs/armsimulate" ^ " >" ^ outfile in

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
      let xregs, qregs = split_first_n (output_state_raw) 32 in
      xregs @ snd (List.fold_left (fun (prev_num, ls) n ->
        (* prev_num is None on 0, 2, 4, ..th item and Some n' on 1, 3, ..th item *)
        match prev_num with
        | None -> (Some n, ls)
        | Some n' -> (None, ls @ [num_two_to_64 */ n +/ n'])) (None, []) qregs) in

    let goal = subst
      [ibyteterm,`ibytes:byte list`;
       mk_flist(map mk_numeral input_state),`input_state:num list`;
       mk_flist(map mk_numeral output_state),`output_state:num list`]
      template in

    let execth = ARM_MK_EXEC_RULE(REFL ibyteterm) in

    let inst_th = Option.get (snd execth).(0) in
    let decoded =
      rand(rand(snd(strip_forall(concl(inst_th)))))
    and result =
    can prove
     (goal,
      REWRITE_TAC[regfile; CONS_11; FLAGENCODING_11; VAL_WORD_GALOIS] THEN
      REWRITE_TAC[DIMINDEX_64; DIMINDEX_128] THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[SOME_FLAGS] THEN
      ARM_SIM_TAC execth [1] THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN REWRITE_TAC[] THEN
      PRINT_GOAL_TAC THEN
      NO_TAC) in
    (decoded,result)
  else
    let decoded = mk_numeral icode in
    decoded,not(can ARM_MK_EXEC_RULE(REFL ibyteterm));;

(* ------------------------------------------------------------------------- *)
(* Keep running tests till a failure happens then return it.                 *)
(* ------------------------------------------------------------------------- *)

let time_limit_sec = 1800.0;;
let tested_instances = ref 0;;

let rec run_random_simulations start_t =
  let decoded,result = run_random_simulation() in
  if result then begin
    tested_instances := !tested_instances + 1;
    let fey = if is_numeral decoded
              then " (fails correctly) instruction code " else " " in
    let _ = Format.print_string("OK:" ^ fey ^ string_of_term decoded);
            Format.print_newline() in
    let now_t = Sys.time() in
    if now_t -. start_t > time_limit_sec then
      let _ = Printf.printf "Finished (time limit: %fs, tested instances: %d)\n"
          time_limit_sec !tested_instances in
      None
    else run_random_simulations start_t
  end
  else Some (decoded,result);;

(*** Depending on the degree of repeatability wanted.
 *** After a few experiments I'm now going full random.
 ***
 *** Random.init(Hashtbl.hash (Sys.getenv "HOST"));;
 ***)

Random.self_init();;

let start_t = Sys.time() (* unit is sec *) in
  match run_random_simulations start_t with
  | Some (t,_) -> Printf.printf "Error: term `%s`" (string_of_term t); failwith "simulator"
  | None -> ();;
