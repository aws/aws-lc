(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
  SPDX-License-Identifier: Apache-2.0*)

open Air;;
module Cryptol = Cryptol;;

(* ---------------------------------------------------------------------- *)

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
let asm_input = input_list;;

let h0 = (sb 64 "h0");;
let h1 = (sb 64 "h1");;
let h2 = (sb 64 "h2");;
let h3 = (sb 64 "h3");;
let h4 = (sb 64 "h4");;
let h5 = (sb 64 "h5");;
let h6 = (sb 64 "h6");;
let h7 = (sb 64 "h7");;
let ctx = [h0; h1; h2; h3; h4; h5; h6; h7];;

(* Specification *)

air_fn_set_uninterpreted_status
  true
  ["arm.inst_sfp_crypto_two_reg_sha512.sigma_0";
   "arm.inst_sfp_crypto_three_reg_sha512.sigma_1";
   "arm.inst_sfp_crypto_three_reg_sha512.sigma_big_0";
   "arm.inst_sfp_crypto_three_reg_sha512.sigma_big_1";
   "arm.inst_sfp_crypto_three_reg_sha512.ch";
   "arm.inst_sfp_crypto_three_reg_sha512.maj";
   Sha2.air_s0_name;
   Sha2.air_s1_name;
   Sha2.air_S0_name;
   Sha2.air_S1_name;
   Sha2.air_Ch_name;
   "specs.common.bv_revbytes64"];;

let spec_message = 
  let input = List.map Specs.Common.bv_revbytes64 input_list in
  Cryptol.array_from_seq "0x40" "0x40"
    (Cryptol.toCry2Dim input)
    (Cryptol.symbolic_malloc "input" 64 64);;

air_fn_set_beta_reduce_status true
  [Sha2.air_compress_Common_t1_name;
   Sha2.air_compress_Common_t2_name;
   Sha2.air_compress_Common_e_name;
   Sha2.air_compress_Common_a_name;
   Sha2.air_messageSchedule_Word_name;
  ];;


air_fn_set_uninterpreted_status false [Sha2.air_processBlock_Common_rec_name];
air_fn_set_beta_reduce_status true [Sha2.air_processBlock_Common_rec_name];;
air_fn_set_uninterpreted_status false [Sha2.air_processBlocks_rec_name];
air_fn_set_beta_reduce_status true [Sha2.air_processBlocks_rec_name];;

let expected_message_digest =
  let n = Cryptol.CryBV(s_cb 64 "0x1") in
  let ctx_flat = Cryptol.join "0x8" "0x40" Cryptol.Bit (Cryptol.toCry2Dim ctx) in
  (Cryptol.rev_digest_blocks
    (Sha2.processblocks_rec ctx_flat n spec_message));;

air_fn_set_uninterpreted_status
  true
  ["arm.inst_sfp_crypto_two_reg_sha512.sigma_0";
   "arm.inst_sfp_crypto_three_reg_sha512.sigma_1";
   "arm.inst_sfp_crypto_three_reg_sha512.sigma_big_0";
   "arm.inst_sfp_crypto_three_reg_sha512.sigma_big_1";
   "arm.inst_sfp_crypto_three_reg_sha512.ch";
   "arm.inst_sfp_crypto_three_reg_sha512.maj";
   Sha2.air_s0_name;
   Sha2.air_s1_name;
   Sha2.air_S0_name;
   Sha2.air_S1_name;
   Sha2.air_Ch_name;
   "specs.common.bv_revbytes64";

   "arm.inst_dpr_logical_shifted_reg.eor64";
   "arm.inst_dpr_logical_shifted_reg.orr64";
   "arm.inst_dpr_logical_shifted_reg.and64";
   "arm.inst_dpr_logical_shifted_reg.bic64";
   "arm.inst_dpi_extract.ror64";
   "arm.inst_dpr_one_src.rev64";
  ];;

(* ---------------------------------------------------------------------- *)

(* Implementation *)

open Arm;;

let state =
  Sha512_block_data_order_init.sha512_block_data_order_init_state
    ~num_blocks:(cb 64 1)
    ~ctx_base:(sb 64 "ctx_base")
    ~ctx:(Some ctx)
    ~input_base:(sb 64 "input_base")
    ~input:(Some asm_input)
    "State initialized for sha512_block_data_order.";;

let final_ss = run ~ignore_assertions:true state;;

let message_digest = read_mem_data 64 (State.make_pointer (sb 64 "ctx_base")) final_ss;;

let expected_message_digest' =
  uncond_rewrite
  expected_message_digest
    Sha512_block_data_order_rules.[
      rev64_of_rev64_rule;
      (* Note: the following rewrites are necessary for cvc5 only *)
      commutativity_and_associativity_of_bvadd_1;
      commutativity_and_associativity_of_bvadd_2;
      commutativity_and_associativity_of_bvadd_3;
    ];;

let message_digest' =
  uncond_rewrite message_digest Sha512_block_data_order_rules.[
      ch_rule;
      maj_rule;
      sigma_big_1_rule1;
      sigma_big_1_rule2;
      sigma_big_0_rule1;
      sigma_big_0_rule2;
      sigma_0_rule;
      sigma_1_rule;
      rev_rule;
      (* Note: the rewrites bvchop_bvadd_rule and bvchop_bvadd_rule2 are necessary for cvc5 only *)
      bvchop_bvadd_rule;
      bvchop_bvadd_rule2;
      rev64_of_rev64_rule;
      sigma0_equiv_rule;
      sigma1_equiv_rule;
      sigma0_big_equiv_rule;
      sigma1_big_equiv_rule;
      ch_equiv_rule;
      maj_equiv_rule;
    ];;

(* ---------------------------------------------------------------------- *)

Smtverify.air_prove ~lhs:message_digest' ~rhs:expected_message_digest'
  ~solver_options:{ main_check =
                      { Smtverify.SmtSolve.solver_defaults with
                        (* Can be solved by Z3, CVC5, as well as Bitwuzla. *)
                        solvers = [CVC5];};
                    vacuity_check =
                      Prove { Smtverify.SmtSolve.solver_defaults with
                              (* Can be solved by Z3, CVC5, as well as Bitwuzla. *)
                              solvers = [CVC5];}}
  "sha512_block_data_order_one_block_correct";;

(* ---------------------------------------------------------------------- *)
