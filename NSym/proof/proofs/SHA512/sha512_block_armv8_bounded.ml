(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
  SPDX-License-Identifier: Apache-2.0 *)

open Air;;
open Arm;;
open State.Assertions;;
module Cryptol = Cryptol;;

let w0 = (sb 64 "w0");;
let w1 = (sb 64 "w1");;
let w2 = (sb 64 "w2");;
let w3 = (sb 64 "w3");;
let w4 = (sb 64 "w4");;
let w5 = (sb 64 "w5");;
let w6 = (sb 64 "w6");;
let w7 = (sb 64 "w7");;
let w8 = (sb 64 "w8");;
let w9 = (sb 64 "w9");;
let w10 = (sb 64 "w10");;
let w11 = (sb 64 "w11");;
let w12 = (sb 64 "w12");;
let w13 = (sb 64 "w13");;
let w14 = (sb 64 "w14");;
let w15 = (sb 64 "w15");;
let input_list = [w0; w1; w2; w3; w4; w5; w6; w7; w8; w9; w10; w11; w12; w13; w14; w15];;

let asm_input_blk = input_list;;

let h0 = (sb 64 "h0");;
let h1 = (sb 64 "h1");;
let h2 = (sb 64 "h2");;
let h3 = (sb 64 "h3");;
let h4 = (sb 64 "h4");;
let h5 = (sb 64 "h5");;
let h6 = (sb 64 "h6");;
let h7 = (sb 64 "h7");;
let ctx = [h0; h1; h2; h3; h4; h5; h6; h7];;

let state =
  Sha512_block_armv8_init.sha512_block_armv8_init_state
    ~num_blocks:(cb 64 1)
    ~ctx_base:(sb 64 "ctx_base")
    ~ctx:(Some ctx)
    ~input_base:(sb 64 "input_base")
    ~input:(Some asm_input_blk)
    "State initialized for sha512_block_armv8.";;

Air.air_fn_set_uninterpreted_status
  true
  [
    (* Implementation functions *)
   "arm.inst_sfp_crypto_two_reg_sha512.sha512su0";
   "arm.inst_sfp_crypto_three_reg_sha512.sha512su1";
   "arm.inst_sfp_crypto_three_reg_sha512.sha512h";
   "arm.inst_sfp_crypto_three_reg_sha512.sha512h2";
   "arm.inst_sfp_adv_simd_two_reg_misc.rev64";
   "arm.inst_sfp_adv_simd_extract.ext128";
   "arm.inst_sfp_adv_simd_three_same.add_sub_2d";
   (* Specification functions *)
   Sha2.air_messageSchedule_Word_name;
   Sha2.air_compress_Common_t1_name;
   Sha2.air_compress_Common_t2_name;
   "specs.common.bv_revbytes64";];;

(* Rewriting LD1 expressions during symbolic simulation:
   interestingly, we don't actually NEED these rewrites for the proof
   to go through. They help in readability though. *)

add_assertion
  ~pc:(cb 64 0x3a3488c)
  (Rewrite "q16_contents")
  (Rewrite((Sfp 16), (bvapp w0 w1)));;
add_assertion
  ~pc:(cb 64 0x3a3488c)
  (Rewrite "q17_contents")
  (Rewrite((Sfp 17), (bvapp w2 w3)));;
add_assertion
  ~pc:(cb 64 0x3a3488c)
  (Rewrite "q18_contents")
  (Rewrite((Sfp 18), (bvapp w4 w5)));;
add_assertion
  ~pc:(cb 64 0x3a3488c)
  (Rewrite "q19_contents")
  (Rewrite((Sfp 19), (bvapp w6 w7)));;

add_assertion
  ~pc:(cb 64 0x3a34890)
  (Rewrite "q20_contents")
  (Rewrite((Sfp 20), (bvapp w8 w9)));;
add_assertion
  ~pc:(cb 64 0x3a34890)
  (Rewrite "q21_contents")
  (Rewrite((Sfp 21), (bvapp w10 w11)));;
add_assertion
  ~pc:(cb 64 0x3a34890)
  (Rewrite "q22_contents")
  (Rewrite((Sfp 22), (bvapp w12 w13)));;
add_assertion
  ~pc:(cb 64 0x3a34890)
  (Rewrite "q23_contents")
  (Rewrite((Sfp 23), (bvapp w14 w15)));;

let final_ss = run ~ignore_assertions:true state;;

let message_digest = read_mem_data 64 (State.make_pointer (sb 64 "ctx_base")) final_ss;;

(* ---------------------------------------------------------------------- *)

Air.air_fn_set_uninterpreted_status
  false
  [
    (* Implementation functions *)
   "arm.inst_sfp_crypto_two_reg_sha512.sha512su0";
   "arm.inst_sfp_crypto_three_reg_sha512.sha512su1";
   "arm.inst_sfp_crypto_three_reg_sha512.sha512h";
   "arm.inst_sfp_crypto_three_reg_sha512.sha512h2";
   "arm.inst_sfp_adv_simd_two_reg_misc.rev64";
   "arm.inst_sfp_adv_simd_extract.ext128";
   "arm.inst_sfp_adv_simd_three_same.add_sub_2d";
    (* Specification functions *)
   Sha2.air_messageSchedule_Word_name;
   Sha2.air_compress_Common_t1_name;
   Sha2.air_compress_Common_t2_name;
   "specs.common.bv_revbytes64";];;

Air.air_fn_set_uninterpreted_status
  true
  [
    (* Implementation functions *)
   "arm.inst_sfp_crypto_two_reg_sha512.sha512su0";
   "arm.inst_sfp_crypto_three_reg_sha512.sha512su1";
   "arm.inst_sfp_crypto_three_reg_sha512.sha512h";
   "arm.inst_sfp_crypto_three_reg_sha512.sha512h2";
   "arm.inst_sfp_adv_simd_two_reg_misc.rev64";
   "arm.inst_sfp_adv_simd_extract.ext128";
   "arm.inst_sfp_adv_simd_three_same.add_sub_2d";

   (* Specification functions *)
   Sha2.air_s0_name;
   Sha2.air_s1_name;
   Sha2.air_S0_name;
   Sha2.air_S1_name;
   Sha2.air_Ch_name;
   Sha2.air_messageSchedule_Word_name;
   "specs.common.bv_revbytes64";
   ];;

(* The order of these rules matter, given how rewrite works. E.g., if
   rev64_of_rev64_rule is listed earlier, then (rev64 (rev64 x)) isn't
   rewritten away. *)

let message_digest' = uncond_rewrite message_digest 
  Sha512_block_armv8_rules.[message_schedule_rule;
                            sha512h2_rule; sha512h_rule_1;
                            rev64_rule;
                            sha512h_rule_2;
                            ext128_rule;
                            add_sub_rule;
                            bv_partsel_of_bvapp_rule_1;
                            bv_partsel_of_bvapp_rule_2;
                            rev64_of_rev64_rule;];;

air_fn_set_uninterpreted_status false [Sha2.air_processBlock_Common_rec_name];
air_fn_set_beta_reduce_status true [Sha2.air_processBlock_Common_rec_name];;
air_fn_set_uninterpreted_status false [Sha2.air_processBlocks_rec_name];
air_fn_set_beta_reduce_status true [Sha2.air_processBlocks_rec_name];;

let expected_message_digest = 
  let n = Cryptol.CryBV(s_cb 64 "0x1") in
  (* Note that we need to reverse the order of the bytes in a 64bit word in the hash.
     The assembly expects the first byte of a word to be on the right side. *)
  let input_message = List.map Specs.Common.bv_revbytes64 input_list in
  let input = Cryptol.array_from_seq "0x40" "0x40"
                (Cryptol.toCry2Dim input_message)
                (Cryptol.symbolic_malloc "input" 64 64) in
  let ctx_flat = Cryptol.join "0x8" "0x40" Cryptol.Bit (Cryptol.toCry2Dim ctx) in
  (* Note that impl_digest are in order h7 h6 h5 ... h0, 
     but spec_digest are in order h0 h1 h2 ... h7. 
     Splitting, reversing and joining spec_digest to get the same order. *)
  let res = (Cryptol.rev_digest_blocks 
              (Sha2.processblocks_rec ctx_flat n input)) in
  uncond_rewrite res Sha512_block_armv8_rules.[rev64_of_rev64_rule];;

Smtverify.air_prove
  ~formula:(bveq 512 message_digest' expected_message_digest)
  ~solver_options:{ Smtverify.all_checks_solver_defaults with
                    main_check =
                      { Smtverify.SmtSolve.solver_defaults with
                        solvers = [Z3] }}
  "sha512_block_armv8_one_block_correct";;
