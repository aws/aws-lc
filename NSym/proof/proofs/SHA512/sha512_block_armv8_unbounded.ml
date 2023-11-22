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
let ctx_base   = (sb 64 "ctx_base");;
let input_base = (sb 64 "input_base");;

let state =
  Sha512_block_armv8_init.sha512_block_armv8_init_state
    ~num_blocks:num_blocks
    ~ctx_base:ctx_base
    ~ctx:(Some ctx)
    ~input_base:input_base
    ~input:None
    "State initialized for sha512_block_armv8.";;

let input_region = (State.get_mem_region "input_region" state);;

let state =
  State.add_preconditions
    [(bvlt 64 (cb 64 0) num_blocks);
     (bveq 7 (bv_partsel num_blocks 57 7) bv_zero);]
    state;;

(* ---------------------------------------------------------------------- *)

(* Inductive Assertions *)

let inductive_invariant =
  let open State in
  let open Sha512_block_armv8_init in
  Assert
    ("sha512_block_armv8_loop_inductive_invariant",
     (fun s ->
        (let num_blocks_left = (num_blocks_left s) in
         let num_blocks_hashed =
           uncond_rewrite (bvsub 64 num_blocks num_blocks_left)
             Sha512_block_armv8_rules.[simplify_num_blks_encrypted_rule_1;
                                       simplify_num_blks_encrypted_rule_2]
         in
         let num_bytes_hashed = (bvlsh 64 num_blocks_hashed (cb 32 7)) in

         let impl_digest =
           uncond_rewrite
             (bvapp_list [(sfp 128 0 s); (sfp 128 1 s); (sfp 128 2 s); (sfp 128 3 s)])
             Sha512_block_armv8_rules.[message_schedule_rule;
                                       sha512h2_rule; sha512h_rule_1;
                                       rev64_rule;
                                       sha512h_rule_2;
                                       ext128_rule;
                                       add_sub_rule;
                                       bv_partsel_of_bvapp_rule_1;
                                       bv_partsel_of_bvapp_rule_2;
                                       rev64_of_rev64_rule;]
         in
         let (_, impl_digest) = (encapsulate ~name:"SHA512_BLK_IMPL" impl_digest) in
         let n = Cryptol.CryBV(num_blocks_hashed) in 
         let input = Cryptol.CryMem(input_region.memory) in
         let ctx_flat = Cryptol.join "0x8" "0x40" Cryptol.Bit (Cryptol.toCry2Dim ctx) in
         let spec_digest = (Cryptol.rev_digest_blocks 
                             (Sha2.processblocks_rec ctx_flat n input)) in
         let spec_digest =
           uncond_rewrite spec_digest Sha512_block_armv8_rules.[sha512_base_case_rule]
         in
         let spec_digest =
           Smtverify.apply_rewrites (State.path_cond s) spec_digest
             Sha512_block_armv8_rules.[sha512_base_case_rule; sha512_inductive_case_rule] in
         let input_in_regs =
           bvapp_list
             [(sfp 128 16 s); (sfp 128 17 s); (sfp 128 18 s); (sfp 128 19 s);
              (sfp 128 20 s); (sfp 128 21 s); (sfp 128 22 s); (sfp 128 23 s)]
         in
         let input_in_mem =
           bvapp_list
             (List.map
                (fun i -> (apply (get_air_fn "arm.inst_sfp_adv_simd_two_reg_misc.rev64") [i]))
                (List.init 8
                   (fun i ->
                      let curr_input_ptr = (input_ptr s) in
                      (read_mem_data 16
                         { curr_input_ptr with offset = (bvsub 64 curr_input_ptr.offset (cb 64 (128 - 16*i))) }
                         s))))
         in
         (band_list
            [(bvlt 64 num_blocks_left num_blocks);
             (iff (bveq 1 (z_flag s) bv_one) (bveq 64 num_blocks_left bv_zero));
             (bveq 512 impl_digest spec_digest);
             (bveq 64 (ktbl_offset s) ktbl_pointer.offset);
             (* In the loop body, we start loading in the NEXT message
                block into q16-23 iff more blocks remain to be
                hashed. Otherwise, we load in the LAST message block
                (again) into q16-23. *)
             (bveq 64 (input_ptr s).offset
                (ite (bveq 64 num_blocks_left (cb 64 0))
                   num_bytes_hashed
                   (bvadd 64 num_bytes_hashed (cb 64 128))));
             (uncond_rewrite
                (bveq 1024 input_in_regs input_in_mem)
                Sha512_block_armv8_rules.[rev64_rule])
                ]
                ))));;

add_assertion ~loop_id:0 inductive_invariant
  ~solver_options:{ Smtverify.all_checks_solver_defaults with
                    main_check =
                      {Smtverify.SmtSolve.solver_defaults
                       with solvers = [Z3];
                            timeout = 200}}
  LoopInvariant;;

let loop_measure =
  (*
    Value of x2 decreases.
   *)
  Measure
    ("sha512_block_armv8_loop_measure",
     (fun s -> (_x 2 s)));;

add_assertion ~loop_id:0 loop_measure LoopMeasure;;

let loop_postcondition =
  let open State in
  let open Sha512_block_armv8_init in
  Assert
    ("sha512_block_armv8_loop_postcondition",
     (fun s ->
        (let num_blocks_left = (num_blocks_left s) in
         let num_blks_encrypted =
           uncond_rewrite (bvsub 64 num_blocks num_blocks_left)
             Sha512_block_armv8_rules.[simplify_num_blks_encrypted_rule_2]
         in
         let num_bytes_encrypted = (bvlsh 64 num_blks_encrypted (cb 32 7)) in
         let (_, impl_digest) = (encapsulate ~name:"SHA512_BLK_IMPL"
                                   (bvapp_list [(sfp 128 0 s);
                                                (sfp 128 1 s);
                                                (sfp 128 2 s);
                                                (sfp 128 3 s)])) in
         let n = Cryptol.CryBV(num_blocks) in 
         let input = Cryptol.CryMem(input_region.memory) in
         let ctx_flat = Cryptol.join "0x8" "0x40" Cryptol.Bit (Cryptol.toCry2Dim ctx) in
         let spec_digest = (Cryptol.rev_digest_blocks 
                              (Sha2.processblocks_rec ctx_flat n input)) in
         (band_list
            [
             (bveq 64 num_blocks_left (cb 64 0));
             (bveq 64 (input_offset input_base s) num_bytes_encrypted);
             (bveq 512 impl_digest spec_digest)
             ]))));;

add_assertion ~loop_id:0 loop_postcondition
  ~solver_options:Smtverify.all_checks_solver_defaults
  LoopPostCondition;;

print_all_assertions true;;

(* ---------------------------------------------------------------------- *)

(* Symbolic Simulation & Proof *)

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
    Sha2.air_s0_name;
    Sha2.air_s1_name;
    Sha2.air_S0_name;
    Sha2.air_S1_name;
    Sha2.air_Ch_name;
    "specs.common.bv_revbytes64";
  ];;

air_fn_set_uninterpreted_status false [Sha2.air_processBlock_Common_rec_name];;

let _ = run state;;

(* ---------------------------------------------------------------------- *)
