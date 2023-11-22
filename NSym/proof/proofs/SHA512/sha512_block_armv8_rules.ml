(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
  SPDX-License-Identifier: Apache-2.0*)

open Air;;

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
 
 let message_schedule_rule =
   let name = "message_schedule_rule" in
   (* This rule would rewrite sha512su1 and sha512su0 in terms of the spec. functions. *)
   let lhs = (apply (get_air_fn "arm.inst_sfp_crypto_three_reg_sha512.sha512su1")
                [(sb 128 "d"); (sb 128 "c");
                 (apply (get_air_fn "arm.inst_sfp_crypto_two_reg_sha512.sha512su0") [(sb 128 "b"); (sb 128 "a")])])
   in
   let equiv = Equal in
   let a0 = (bv_partsel (sb 128 "a") 0 64) in
   let a1 = (bv_partsel (sb 128 "a") 64 64) in
   let b0 = (bv_partsel (sb 128 "b") 0 64) in
   let c0 = (bv_partsel (sb 128 "c") 0 64) in
   let c1 = (bv_partsel (sb 128 "c") 64 64) in
   let d0 = (bv_partsel (sb 128 "d") 0 64) in
   let d1 = (bv_partsel (sb 128 "d") 64 64) in
   let rhs = (bvapp
                (apply (get_air_fn Sha2.air_messageSchedule_Word_name)  [a0; a1; c0; d0])
                (apply (get_air_fn Sha2.air_messageSchedule_Word_name)  [a1; b0; c1; d1])) in
   (Smtverify.prove_rule ~lhs ~equiv ~rhs name);;
 
 let sha512h2_rule =
   let name = "sha512h2_rule" in
   (* This rule would rewrite sha512h2 in terms of the spec. functions. *)
   let lhs = (apply (get_air_fn "arm.inst_sfp_crypto_three_reg_sha512.sha512h2")
                [(sb 128 "a"); (sb 128 "b"); (sb 128 "c")])
   in
   let equiv = Equal in
   let a0 = (bv_partsel (sb 128 "a") 0 64) in
   let b0 = (bv_partsel (sb 128 "b") 0 64) in
   let b1 = (bv_partsel (sb 128 "b") 64 64) in
   let c0 = (bv_partsel (sb 128 "c") 0 64) in
   let c1 = (bv_partsel (sb 128 "c") 64 64) in
   let rhs = (bvapp
                (bvadd 64
                   (apply (get_air_fn Sha2.air_compress_Common_t2_name)
                      [(bvadd 64 (apply (get_air_fn Sha2.air_compress_Common_t2_name) [b0; a0; b1]) c1); b0; b1])
                   c0)
                (bvadd 64 (apply (get_air_fn Sha2.air_compress_Common_t2_name) [b0; a0; b1]) c1)) in
   (let _ =
      Smtverify.air_prove
        ~lhs:lhs ~rhs:rhs
        ~solver_options:{ Smtverify.all_checks_solver_defaults with
                     main_check =
                       { Smtverify.SmtSolve.solver_defaults with
                         solvers = [Z3] }}
        name in
     make_rule ~lhs ~equiv ~rhs name);;
 
 let sha512h_rule_1 =
   let name = "sha512h1_rule_1" in
   (* This rule would rewrite sha512h in terms of the spec. functions. *)
   let lhs = (apply (get_air_fn "arm.inst_sfp_crypto_three_reg_sha512.sha512h")
                [(sb 128 "a"); (sb 128 "b");
                 (apply (get_air_fn "arm.inst_sfp_adv_simd_three_same.add_sub_2d")
                    [(ct false);
                     (apply (get_air_fn "arm.inst_sfp_adv_simd_three_same.add_sub_2d") [(ct false); (sb 128 "c"); (sb 128 "d")]);
                     (sb 128 "e")])])
   in
   let equiv = Equal in
   let a0 = (bv_partsel (sb 128 "a") 0 64) in
   let a1 = (bv_partsel (sb 128 "a") 64 64) in
   let b0 = (bv_partsel (sb 128 "b") 0 64) in
   let b1 = (bv_partsel (sb 128 "b") 64 64) in
   let c0 = (bv_partsel (sb 128 "c") 0 64) in
   let c1 = (bv_partsel (sb 128 "c") 64 64) in
   let d0 = (bv_partsel (sb 128 "d") 0 64) in
   let d1 = (bv_partsel (sb 128 "d") 64 64) in
   let e0 = (bv_partsel (sb 128 "e") 0 64) in
   let e1 = (bv_partsel (sb 128 "e") 64 64) in
   let hi64_spec = (apply (get_air_fn Sha2.air_compress_Common_t1_name) [b1; a0; a1; c1; d1; e1]) in
   let lo64_spec = (apply (get_air_fn Sha2.air_compress_Common_t1_name)
                      [(* (apply (get_air_fn "spec.SHA512rec.air_compression_Common_e") [b0; hi64_spec]); *)
                        (bvadd 64 b0 hi64_spec);
                        b1; a0; c0; d0; e0]) in
   let rhs = (bvapp lo64_spec hi64_spec) in
   (let _ =
      Smtverify.air_prove
        ~lhs:lhs ~rhs:rhs
        (* If we enabled subexpression elimination, the SMT problem
           becomes much more difficult for Z3/CVC5 to solve. *)
        ~reduce_threshold:None
        ~solver_options:{ Smtverify.no_vacuity_check_solver_defaults with
                          main_check =
                            { Smtverify.SmtSolve.solver_defaults with
                              solvers = [Z3]; timeout = 50 }}
        name in
    make_rule ~lhs ~equiv ~rhs name);;
 
 let rev64_rule =
   let name = "rev64_rule" in
   (* This rule would rewrite rev64 in terms of the spec. functions. *)
   let lhs = (apply (get_air_fn "arm.inst_sfp_adv_simd_two_reg_misc.rev64") [(sb 128 "a")]) in
   let equiv = Equal in
   let a0 = (bv_partsel (sb 128 "a") 0 64) in
   let a1 = (bv_partsel (sb 128 "a") 64 64) in
   let rhs = (bvapp (apply (get_air_fn "specs.common.bv_revbytes64") [a0])
                (apply (get_air_fn "specs.common.bv_revbytes64") [a1])) in
   (Smtverify.prove_rule ~lhs ~equiv ~rhs name);;
 
 let rev64_of_rev64_rule =
   let name = "rev64_of_rev64_rule" in
   let lhs =  (apply (get_air_fn "specs.common.bv_revbytes64")
                 [(apply (get_air_fn "specs.common.bv_revbytes64") [(sb 64 "x")])]) in
   let equiv = Equal in
   let rhs = (sb 64 "x") in
   (Smtverify.prove_rule ~lhs ~equiv ~rhs name);;
 
 let sha512h_rule_2 =
   let name = "sha512h2_rule" in
   (* This rule would rewrite sha512h in terms of the spec. functions. *)
   let lhs = (apply (get_air_fn "arm.inst_sfp_crypto_three_reg_sha512.sha512h")
                [(sb 128 "a"); (sb 128 "b");
                 (apply (get_air_fn "arm.inst_sfp_adv_simd_three_same.add_sub_2d")
                    [(ct false);
                     (sb 128 "c");
                     (apply (get_air_fn "arm.inst_sfp_adv_simd_extract.ext128")
                        [(apply (get_air_fn "arm.inst_sfp_adv_simd_three_same.add_sub_2d") [(ct false); (sb 128 "d"); (sb 128 "e")]);
                         (apply (get_air_fn "arm.inst_sfp_adv_simd_three_same.add_sub_2d") [(ct false); (sb 128 "d"); (sb 128 "e")]);
                         (cb 32 64)])])])
   in
   let equiv = Equal in
   let a0 = (bv_partsel (sb 128 "a") 0 64) in
   let a1 = (bv_partsel (sb 128 "a") 64 64) in
   let b0 = (bv_partsel (sb 128 "b") 0 64) in
   let b1 = (bv_partsel (sb 128 "b") 64 64) in
   let c0 = (bv_partsel (sb 128 "c") 0 64) in
   let c1 = (bv_partsel (sb 128 "c") 64 64) in
   let d0 = (bv_partsel (sb 128 "d") 0 64) in
   let d1 = (bv_partsel (sb 128 "d") 64 64) in
   let e0 = (bv_partsel (sb 128 "e") 0 64) in
   let e1 = (bv_partsel (sb 128 "e") 64 64) in
   let hi64_spec = (apply (get_air_fn Sha2.air_compress_Common_t1_name) [b1; a0; a1; c1; d0; e0]) in
   let lo64_spec = (apply (get_air_fn Sha2.air_compress_Common_t1_name)
                      [(* (apply (get_air_fn "spec.SHA512rec.air_compression_Common_e") [b0; hi64_spec]); *)
                        (bvadd 64 b0 hi64_spec);
                        b1; a0; c0; d1; e1])
   in
   let rhs = (bvapp lo64_spec hi64_spec) in
   (let _ =
      Smtverify.air_prove
        ~lhs:lhs ~rhs:rhs
        ~solver_options:{ Smtverify.no_vacuity_check_solver_defaults with
                          main_check =
                            { Smtverify.SmtSolve.solver_defaults with
                              solvers = [Z3]; timeout = 50 }}
        (* If we enabled subexpression elimination, the SMT problem
           becomes much more difficult for Z3/CVC5 to solve. *)
        ~reduce_threshold:None
        name in
   (make_rule ~lhs ~equiv ~rhs name));;
 
 let ext128_rule =
   let name = "ext128_rule" in
   let lhs = (apply (get_air_fn "arm.inst_sfp_adv_simd_extract.ext128") [(sb 128 "a"); (sb 128 "b"); (cb 32 64)]) in
   let equiv = Equal in
   let rhs = (bvapp (bv_partsel (sb 128 "b") 64 64) (bv_partsel (sb 128 "a") 0 64)) in
   (Smtverify.prove_rule ~lhs ~equiv ~rhs name);;
 
 let add_sub_rule =
   let name = "add_sub_rule" in
   let lhs = (apply (get_air_fn "arm.inst_sfp_adv_simd_three_same.add_sub_2d") [(ct false); (sb 128 "operand1"); (sb 128 "operand2")]) in
   let equiv = Equal in
   let rhs = (bvapp
                (bvadd 64 (bv_partsel (sb 128 "operand1") 0 64)  (bv_partsel (sb 128 "operand2") 0 64))
                (bvadd 64 (bv_partsel (sb 128 "operand1") 64 64) (bv_partsel (sb 128 "operand2") 64 64)))in
   (Smtverify.prove_rule ~lhs ~equiv ~rhs name);;
 
 let bv_partsel_of_bvapp_rule_1 =
   let name = "bv_partsel_of_bvapp_rule_1" in
   let lhs = (bv_partsel (bvapp (sb 64 "lo") (sb 64 "hi")) 0 64) in
   let equiv = Equal in
   let rhs = (sb 64 "lo") in
   (Smtverify.prove_rule ~lhs ~equiv ~rhs name);;
 
 let bv_partsel_of_bvapp_rule_2 =
   let name = "bv_partsel_of_bvapp_rule_2" in
   let lhs = (bv_partsel (bvapp (sb 64 "lo") (sb 64 "hi")) 64 64) in
   let equiv = Equal in
   let rhs = (sb 64 "hi") in
   (Smtverify.prove_rule ~lhs ~equiv ~rhs name);;
 
(* ---------------------------------------------------------------------- *)

(* Rules needed for unbounded proof *)

let simplify_num_blks_encrypted_rule_1 =
  let name = "simplify_num_blks_encrypted_rule_1" in
  let lhs = (bvsub 64 (sb 64 "var_1")
               (bvchop 64
                  (bvadd 65
                     (bvadd 65 (sb 64 "var_1") (s_cb 64 "0xfffffffffffffffe"))
                     (cb 1 1))))
  in
  let equiv = Equal in
  let rhs = (cb 64 1) in
  let _ = Smtverify.air_prove ~lhs:lhs ~rhs:rhs name in
  (make_rule ~lhs ~equiv ~rhs name);;

let simplify_num_blks_encrypted_rule_2 =
  let name = "simplify_num_blks_encrypted_rule_2" in
  let lhs = (bvsub 64 (sb 64 "var_1")
               (bvchop 64
                  (bvadd 65
                     (bvadd 65 (sb 64 "var_2") (s_cb 64 "0xfffffffffffffffe"))
                     (cb 1 1))))
  in
  let equiv = Equal in
  let rhs = (bvsub 64 (sb 64 "var_1") (bvsub 64 (sb 64 "var_2") (cb 64 1))) in
  let _ = Smtverify.air_prove ~lhs:lhs ~rhs:rhs name in
  (make_rule ~lhs ~equiv ~rhs name);;
let sha512_base_case_rule =
  let open Arm in
  let name = "sha512_base_case_rule" in
  let base_idx = (cb 64 1) in
  let ctx = (sb 512 "ctx") in
  let lhs = (apply Sha2.air_processBlocks_rec [ctx; base_idx; (smem "input" 64 64)]) in
  let equiv = Equal in
  let rec_call = ctx in
  let input_block =
    (let i = (cb 64 1) in (* i: Number of blocks *)
     let i_1 = (bvsub 64 i (cb 64 1)) in
     let w0  = (State.read_memory 8 (bvadd 64 (bvlsh 64 i_1 (cb 32 7)) (cb 64 (8 * 0)))  ("input",  (smem "input" 64 64))) in
     let w1  = (State.read_memory 8 (bvadd 64 (bvlsh 64 i_1 (cb 32 7)) (cb 64 (8 * 1)))  ("input",  (smem "input" 64 64))) in
     let w2  = (State.read_memory 8 (bvadd 64 (bvlsh 64 i_1 (cb 32 7)) (cb 64 (8 * 2)))  ("input",  (smem "input" 64 64))) in
     let w3  = (State.read_memory 8 (bvadd 64 (bvlsh 64 i_1 (cb 32 7)) (cb 64 (8 * 3)))  ("input",  (smem "input" 64 64))) in
     let w4  = (State.read_memory 8 (bvadd 64 (bvlsh 64 i_1 (cb 32 7)) (cb 64 (8 * 4)))  ("input",  (smem "input" 64 64))) in
     let w5  = (State.read_memory 8 (bvadd 64 (bvlsh 64 i_1 (cb 32 7)) (cb 64 (8 * 5)))  ("input",  (smem "input" 64 64))) in
     let w6  = (State.read_memory 8 (bvadd 64 (bvlsh 64 i_1 (cb 32 7)) (cb 64 (8 * 6)))  ("input",  (smem "input" 64 64))) in
     let w7  = (State.read_memory 8 (bvadd 64 (bvlsh 64 i_1 (cb 32 7)) (cb 64 (8 * 7)))  ("input",  (smem "input" 64 64))) in
     let w8  = (State.read_memory 8 (bvadd 64 (bvlsh 64 i_1 (cb 32 7)) (cb 64 (8 * 8)))  ("input",  (smem "input" 64 64))) in
     let w9  = (State.read_memory 8 (bvadd 64 (bvlsh 64 i_1 (cb 32 7)) (cb 64 (8 * 9)))  ("input",  (smem "input" 64 64))) in
     let w10 = (State.read_memory 8 (bvadd 64 (bvlsh 64 i_1 (cb 32 7)) (cb 64 (8 * 10))) ("input",  (smem "input" 64 64))) in
     let w11 = (State.read_memory 8 (bvadd 64 (bvlsh 64 i_1 (cb 32 7)) (cb 64 (8 * 11))) ("input",  (smem "input" 64 64))) in
     let w12 = (State.read_memory 8 (bvadd 64 (bvlsh 64 i_1 (cb 32 7)) (cb 64 (8 * 12))) ("input",  (smem "input" 64 64))) in
     let w13 = (State.read_memory 8 (bvadd 64 (bvlsh 64 i_1 (cb 32 7)) (cb 64 (8 * 13))) ("input",  (smem "input" 64 64))) in
     let w14 = (State.read_memory 8 (bvadd 64 (bvlsh 64 i_1 (cb 32 7)) (cb 64 (8 * 14))) ("input",  (smem "input" 64 64))) in
     let w15 = (State.read_memory 8 (bvadd 64 (bvlsh 64 i_1 (cb 32 7)) (cb 64 (8 * 15))) ("input",  (smem "input" 64 64))) in
     (List.map
       (fun x -> (apply (get_air_fn "specs.common.bv_revbytes64") [x]))
       [w0; w1; w2; w3; w4; w5; w6; w7; w8; w9; w10; w11; w12; w13; w14; w15])
     ) in
  let rhs =  (apply Sha2.air_processBlock_Common_rec (rec_call :: input_block)) in
  (let _ = Smtverify.air_prove ~lhs:lhs ~rhs:rhs ~theory:[Sha512rec_theorems.sha512_spec_base_theorem; Sha512rec_theorems.sha512_spec_ind_theorem] name in
   (make_rule ~lhs ~equiv ~rhs name));;

let sha512_inductive_case_rule =
  let open Arm in
  let name = "sha512_inductive_case_rule" in
  let base_idx = (bvsub 64 (sb 64 "var_1") (bvsub 64 (sb 64 "var_2") (cb 64 1))) in
  let ctx = (sb 512 "ctx") in
  let hyp = (bvlt 64 (cb 64 0) base_idx) in
  let lhs = (apply Sha2.air_processBlocks_rec [ctx; base_idx; (smem "input" 64 64)]) in
  let equiv = Equal in
  let rec_call = (apply Sha2.air_processBlocks_rec [ctx; (bvsub 64 base_idx (cb 64 1)); (smem "input" 64 64)]) in
  let input_block =
    (let i = base_idx in (* i: Number of blocks *)
     let i_1 = (bvsub 64 i (cb 64 1)) in
     let w0  = (State.read_memory 8 (bvadd 64 (bvlsh 64 i_1 (cb 32 7)) (cb 64 (8 * 0)))  ("input", (smem "input" 64 64))) in
     let w1  = (State.read_memory 8 (bvadd 64 (bvlsh 64 i_1 (cb 32 7)) (cb 64 (8 * 1)))  ("input", (smem "input" 64 64))) in
     let w2  = (State.read_memory 8 (bvadd 64 (bvlsh 64 i_1 (cb 32 7)) (cb 64 (8 * 2)))  ("input", (smem "input" 64 64))) in
     let w3  = (State.read_memory 8 (bvadd 64 (bvlsh 64 i_1 (cb 32 7)) (cb 64 (8 * 3)))  ("input", (smem "input" 64 64))) in
     let w4  = (State.read_memory 8 (bvadd 64 (bvlsh 64 i_1 (cb 32 7)) (cb 64 (8 * 4)))  ("input", (smem "input" 64 64))) in
     let w5  = (State.read_memory 8 (bvadd 64 (bvlsh 64 i_1 (cb 32 7)) (cb 64 (8 * 5)))  ("input", (smem "input" 64 64))) in
     let w6  = (State.read_memory 8 (bvadd 64 (bvlsh 64 i_1 (cb 32 7)) (cb 64 (8 * 6)))  ("input", (smem "input" 64 64))) in
     let w7  = (State.read_memory 8 (bvadd 64 (bvlsh 64 i_1 (cb 32 7)) (cb 64 (8 * 7)))  ("input", (smem "input" 64 64))) in
     let w8  = (State.read_memory 8 (bvadd 64 (bvlsh 64 i_1 (cb 32 7)) (cb 64 (8 * 8)))  ("input", (smem "input" 64 64))) in
     let w9  = (State.read_memory 8 (bvadd 64 (bvlsh 64 i_1 (cb 32 7)) (cb 64 (8 * 9)))  ("input", (smem "input" 64 64))) in
     let w10 = (State.read_memory 8 (bvadd 64 (bvlsh 64 i_1 (cb 32 7)) (cb 64 (8 * 10))) ("input", (smem "input" 64 64))) in
     let w11 = (State.read_memory 8 (bvadd 64 (bvlsh 64 i_1 (cb 32 7)) (cb 64 (8 * 11))) ("input", (smem "input" 64 64))) in
     let w12 = (State.read_memory 8 (bvadd 64 (bvlsh 64 i_1 (cb 32 7)) (cb 64 (8 * 12))) ("input", (smem "input" 64 64))) in
     let w13 = (State.read_memory 8 (bvadd 64 (bvlsh 64 i_1 (cb 32 7)) (cb 64 (8 * 13))) ("input", (smem "input" 64 64))) in
     let w14 = (State.read_memory 8 (bvadd 64 (bvlsh 64 i_1 (cb 32 7)) (cb 64 (8 * 14))) ("input", (smem "input" 64 64))) in
     let w15 = (State.read_memory 8 (bvadd 64 (bvlsh 64 i_1 (cb 32 7)) (cb 64 (8 * 15))) ("input", (smem "input" 64 64))) in
     (List.map
       (fun x -> (apply (get_air_fn "specs.common.bv_revbytes64") [x]))
       [w0; w1; w2; w3; w4; w5; w6; w7; w8; w9; w10; w11; w12; w13; w14; w15]))
  in
  let rhs =  (apply Sha2.air_processBlock_Common_rec (rec_call :: input_block)) in
  (let _ = Smtverify.air_prove ~hyp:hyp ~lhs:lhs ~rhs:rhs ~theory:[Sha512rec_theorems.sha512_spec_base_theorem; Sha512rec_theorems.sha512_spec_ind_theorem] name in
   (make_rule ~lhs ~equiv ~rhs name));;

(* ---------------------------------------------------------------------- *)
