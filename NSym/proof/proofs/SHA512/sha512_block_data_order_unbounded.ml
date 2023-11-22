(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
  SPDX-License-Identifier: Apache-2.0*)

open Air;;
open Arm;;
open State.Assertions;;

(* ---------------------------------------------------------------------- *)

(* State Initialization *)

let h0 = (sb 64 "h0");;
let h1 = (sb 64 "h1");;
let h2 = (sb 64 "h2");;
let h3 = (sb 64 "h3");;
let h4 = (sb 64 "h4");;
let h5 = (sb 64 "h5");;
let h6 = (sb 64 "h6");;
let h7 = (sb 64 "h7");;
let ctx = [h0; h1; h2; h3; h4; h5; h6; h7];;

let num_blocks = (sb 64 "num_blocks");;
let ctx_base = (sb 64 "ctx_base");;
let input_base = (sb 64 "input_base");;

let state =
  Sha512_block_data_order_init.sha512_block_data_order_init_state
    ~num_blocks:num_blocks
    ~ctx_base:ctx_base
    ~ctx:(Some ctx)
    ~input_base:input_base
    ~input:None
    "State initialized for sha512_block_data_order.";;

let input_region = (State.get_mem_region "input_region" state);;

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

let state =
  State.add_preconditions
    [(bvlt 64 (cb 64 0) num_blocks);
     (bveq 7 (bv_partsel num_blocks 57 7) bv_zero);]
    state;;

(* ---------------------------------------------------------------------- *)

(* Inductive Assertions *)

let spec_digest_rules = Sha512_block_data_order_rules.[
    rev64_of_rev64_rule;
    commutativity_and_associativity_of_bvadd_1;
    commutativity_and_associativity_of_bvadd_2;
    commutativity_and_associativity_of_bvadd_3;
  ];;

let impl_digest_rules = Sha512_block_data_order_rules.[
    ch_rule;
    maj_rule;
    sigma_big_1_rule1;
    sigma_big_1_rule2;
    sigma_big_0_rule1;
    sigma_big_0_rule2;
    sigma_0_rule;
    sigma_1_rule;
    rev_rule;
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

let inductive_invariant =
  let open Sha512_block_data_order_init in
  let open State in
  Assert
    ("sha512_block_data_order_loop_inductive_invariant",
     (fun s ->
        (let input_pointer = (input_ptr s) in
         let num_bytes_hashed = input_pointer.offset in
         let num_blks_hashed = (bvrsh 64 num_bytes_hashed (cb 32 7)) in
         let num_blks_hashed =
           Smtverify.apply_rewrites (path_cond s) num_blks_hashed
             Sha512_block_data_order_rules.[simplify_num_blks_hashed_rule] in
         let num_blks_to_hash = (bvsub 64 num_blocks num_blks_hashed) in

         let n = Cryptol.CryBV(num_blks_hashed) in
         let input = Cryptol.CryMem(input_region.memory) in
         let ctx_flat = Cryptol.join "0x8" "0x40" Cryptol.Bit (Cryptol.toCry2Dim ctx) in
         let spec_digest = (Cryptol.rev_digest_blocks
                             (Sha2.processblocks_rec ctx_flat n input)) in
         let spec_digest = uncond_rewrite spec_digest spec_digest_rules in
         let spec_digest =
           Smtverify.apply_rewrites (path_cond s) spec_digest
             Sha512_block_data_order_rules.[sha512_base_case_rule;
                                            sha512_inductive_case_rule;
                                            bvsub_bvadd_rule;
                                            simplify_input_index_rule;]
         in

         let (_, impl_digest_reg) =
           (encapsulate ~name:"SHA512_BLK_IMPL_REG"
              (uncond_rewrite
                    (bvapp_list [(_x 20 s); (_x 21 s); (_x 22 s); (_x 23 s);
                                 (_x 24 s); (_x 25 s); (_x 26 s); (_x 27 s)])
                    impl_digest_rules))
         in
         let (_, impl_digest) =
           (encapsulate ~name:"SHA512_BLK_IMPL"
              (uncond_rewrite
                    (read_mem_data 64 (make_pointer (sb 64 "ctx_base")) s)
                    impl_digest_rules))
         in

         let sp_pointer = (make_pointer (sb 64 "__sp")) in
         let ctx_base_store_pointer = { sp_pointer with offset = (cb 64 224) } in
         let ctx_base_on_stack = (read_mem 8 ctx_base_store_pointer s) in
         let end_of_input_store_pointer = { sp_pointer with offset = (cb 64 232) } in
         let end_of_input_on_stack = read_mem 8 end_of_input_store_pointer s in

           (band_list
              [(* Ctx *)
                (bveq 64 (Option.get (ctx_ptr s).id) ctx_base);
                (bveq 64 (ctx_ptr s).offset (cb 64 0));

                (* Pointer to current input block *)
                (bveq 64 (Option.get input_pointer.id) input_base);
                (bveq 7 (bvchop 7 input_pointer.offset) (cb 7 0));

                (* End of input *)
                (bveq 64 (Option.get (end_of_input_ptr s).id) input_base);
                (bveq 64 (end_of_input_ptr s).offset (bvlsh 64 num_blocks (cb 32 7)));

                (* Stack contents' properties *)
                (bveq 64 (Option.get end_of_input_on_stack.id) input_base);
                (bveq 64 end_of_input_on_stack.offset (bvlsh 64 num_blocks (cb 32 7)));
                (bvle 64 num_bytes_hashed end_of_input_on_stack.offset);
                (bveq 64 (Option.get ctx_base_on_stack.id) ctx_base);
                (bveq 64 ctx_base_on_stack.offset (cb 64 0));

                (* x29 + <offset>: used to index into the input buffer
                   addresses, etc. stored in the memory *)
                (bveq 64 (_x 29 s) (cb 64 128));
                (* x30: pointer to the ktbl constants. At the beginning
                   of each loop iteration, x30 should always point to the
                   first ktbl constant. *)
                (bveq 64 (_x 30 s) ktbl_pointer.offset);

                (* "Interesting" part of the inductive invariant *)
                (bvlt 64 num_blks_to_hash num_blocks);
                (iff (bveq 1 (z_flag s) bv_one)
                   (bveq 64 (bvsub 64 (end_of_input_ptr s).offset input_pointer.offset) bv_zero));
                (bveq 512 impl_digest spec_digest);
                (bveq 512 impl_digest_reg impl_digest)]))));;

add_assertion ~loop_id:0 inductive_invariant
  ~solver_options:{ Smtverify.all_checks_solver_defaults with
                    main_check =
                      {Smtverify.SmtSolve.solver_defaults with
                       solvers = [Z3]; timeout = 200}}
  LoopInvariant;;

let loop_measure =
  let open Sha512_block_data_order_init in
  (*
    Number of blocks to hash decreases.
   *)
  Measure
    ("sha512_block_data_order_loop_measure",
     (fun s -> (bvsub 64 (end_of_input_ptr s).offset (input_ptr s).offset)));;

add_assertion ~loop_id:0 loop_measure LoopMeasure;;

let loop_postcondition =
  let open State in
  let open Sha512_block_data_order_init in
  Assert
    ("sha512_block_data_order_loop_postcondition",
     (fun s ->
        (let n = Cryptol.CryBV(num_blocks) in 
         let input = Cryptol.CryMem(input_region.memory) in
         let ctx_flat = Cryptol.join "0x8" "0x40" Cryptol.Bit (Cryptol.toCry2Dim ctx) in
         let spec_digest = (Cryptol.rev_digest_blocks 
                             (Sha2.processblocks_rec ctx_flat n input)) in
         let (_, impl_digest) =
           (encapsulate ~name:"SHA512_BLK_IMPL"
              (read_mem_data 64 (State.make_pointer (sb 64 "ctx_base")) s))
         in
         (band_list
            [(bveq 64 (input_ptr s).offset (end_of_input_ptr s).offset);
             (bveq 512 impl_digest spec_digest)]))));;

add_assertion ~loop_id:0 loop_postcondition
  ~solver_options:Smtverify.all_checks_solver_defaults
  LoopPostCondition;;

print_all_assertions true;;

(* ---------------------------------------------------------------------- *)

(* Symbolic Simulation & Proof *)

air_fn_set_uninterpreted_status
  true
  ["arm.inst_sfp_crypto_two_reg_sha512.sigma_0";
   "arm.inst_sfp_crypto_three_reg_sha512.sigma_1";
   "arm.inst_sfp_crypto_three_reg_sha512.sigma_big_0";
   "arm.inst_sfp_crypto_three_reg_sha512.sigma_big_1";
   "arm.inst_sfp_crypto_three_reg_sha512.ch";
   "arm.inst_sfp_crypto_three_reg_sha512.maj";
   "specs.common.bv_revbytes64";

   "arm.inst_dpr_logical_shifted_reg.eor64";
   "arm.inst_dpr_logical_shifted_reg.orr64";
   "arm.inst_dpr_logical_shifted_reg.and64";
   "arm.inst_dpr_logical_shifted_reg.bic64";
   "arm.inst_dpi_extract.ror64";
   "arm.inst_dpr_one_src.rev64";

   Sha2.air_s0_name;
   Sha2.air_s1_name;
   Sha2.air_S0_name;
   Sha2.air_S1_name;
   Sha2.air_Ch_name;
  ];;

air_fn_set_uninterpreted_status false [Sha2.air_processBlock_Common_rec_name];;

let _ = run ~unroll_options:[(1, Full)] state;;

(* ---------------------------------------------------------------------- *)
