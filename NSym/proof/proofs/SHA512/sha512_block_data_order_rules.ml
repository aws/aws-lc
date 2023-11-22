(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
  SPDX-License-Identifier: Apache-2.0*)

open Air;;

(* ---------------------------------------------------------------------- *)

let ch_rule =
  let name = "ch_rule" in
  let ch    = (get_air_fn "arm.inst_sfp_crypto_three_reg_sha512.ch") in
  let orr_i = (get_air_fn "arm.inst_dpr_logical_shifted_reg.orr64") in
  let and_i = (get_air_fn "arm.inst_dpr_logical_shifted_reg.and64") in
  let bic_i = (get_air_fn "arm.inst_dpr_logical_shifted_reg.bic64") in
  let (e, f, g) = ((sb 64 "e"), (sb 64 "f"), (sb 64 "g")) in
  let lhs = (apply orr_i [(apply and_i [f; e]); (apply bic_i [g; e])]) in
  let equiv = Equal in
  let rhs = (apply ch [e; f; g]) in
  (let _ = Smtverify.air_prove ~lhs:lhs ~rhs:rhs name in
   (make_rule ~lhs ~equiv ~rhs name));;

let maj_rule =
  let name = "maj_rule" in
  let maj   = (get_air_fn "arm.inst_sfp_crypto_three_reg_sha512.maj") in
  let eor_i = (get_air_fn "arm.inst_dpr_logical_shifted_reg.eor64") in
  let and_i = (get_air_fn "arm.inst_dpr_logical_shifted_reg.and64") in
  let (a, b, c) = ((sb 64 "a"), (sb 64 "b"), (sb 64 "c")) in
  let lhs = (apply eor_i [(apply and_i [(apply eor_i [b; c]); (apply eor_i [a; b])]); b]) in
  let equiv = Equal in
  let rhs = (apply maj [a; b; c]) in
  (let _ = Smtverify.air_prove ~lhs:lhs ~rhs:rhs name in
   (make_rule ~lhs ~equiv ~rhs name));;

let sigma_big_1_rule1 =
  let name = "sigma_big_1_rule1" in
  let sigma_big_1 = (get_air_fn "arm.inst_sfp_crypto_three_reg_sha512.sigma_big_1") in
  let eor_i = (get_air_fn "arm.inst_dpr_logical_shifted_reg.eor64") in
  let ror_i = (get_air_fn "arm.inst_dpi_extract.ror64") in
  let e = (sb 64 "e") in
  let s0 = 14 in
  let s1 = 18 in
  let s2 = 41 in
  let big_t0 = (apply eor_i [e; (bvror (s2 - s1) e)]) in
  let t0 = (apply ror_i [(cb 32 s0); e; e]) in
  let lhs = (apply eor_i [t0; (bvror s1 big_t0)]) in
  let equiv = Equal in
  let rhs = (apply sigma_big_1 [e]) in
  (let _ = Smtverify.air_prove ~lhs:lhs ~rhs:rhs name in
   (make_rule ~lhs ~equiv ~rhs name));;

let sigma_big_1_rule2 =
  let name = "sigma_big_1_rule2" in
  let sigma_big_1 = (get_air_fn "arm.inst_sfp_crypto_three_reg_sha512.sigma_big_1") in
  let eor_i = (get_air_fn "arm.inst_dpr_logical_shifted_reg.eor64") in
  let ror_i = (get_air_fn "arm.inst_dpi_extract.ror64") in
  let e = (sb 64 "e") in
  let s0 = 14 in
  let s1 = 18 in
  let s2 = 41 in
  let lhs = (apply eor_i [(apply eor_i [(apply ror_i [(cb 32 s0); e; e]); (bvror s1 e)]); (bvror s2 e)]) in
  let equiv = Equal in
  let rhs = (apply sigma_big_1 [e]) in
  (let _ = Smtverify.air_prove ~lhs:lhs ~rhs:rhs name in
   (make_rule ~lhs ~equiv ~rhs name));;

let sigma_big_0_rule1 =
  let name = "sigma_big_0_rule1" in
  let sigma_big_0 = (get_air_fn "arm.inst_sfp_crypto_three_reg_sha512.sigma_big_0") in
  let eor_i = (get_air_fn "arm.inst_dpr_logical_shifted_reg.eor64") in
  let ror_i = (get_air_fn "arm.inst_dpi_extract.ror64") in
  let a = (sb 64 "a") in
  let s0 = 28 in
  let s1 = 34 in
  let s2 = 39 in
  let big_t0 = (apply ror_i [(cb 32 s0); a; a]) in
  let t1 = (apply eor_i [a; (bvror (s2 - s1) a)]) in
  let lhs = (apply eor_i [big_t0; (bvror s1 t1)]) in
  let equiv = Equal in
  let rhs = (apply sigma_big_0 [a]) in
  (let _ = Smtverify.air_prove ~lhs:lhs ~rhs:rhs name in
   (make_rule ~lhs ~equiv ~rhs name));;

let sigma_big_0_rule2 =
  let name = "sigma_big_0_rule2" in
  let sigma_big_0 = (get_air_fn "arm.inst_sfp_crypto_three_reg_sha512.sigma_big_0") in
  let eor_i = (get_air_fn "arm.inst_dpr_logical_shifted_reg.eor64") in
  let ror_i = (get_air_fn "arm.inst_dpi_extract.ror64") in
  let a = (sb 64 "a") in
  let s0 = 28 in
  let s1 = 34 in
  let s2 = 39 in
  let lhs = (apply eor_i [(apply eor_i [(apply ror_i [(cb 32 s0); a; a]); (bvror s1 a)]); (bvror s2 a)]) in
  let equiv = Equal in
  let rhs = (apply sigma_big_0 [a]) in
  (let _ = Smtverify.air_prove ~lhs:lhs ~rhs:rhs name in
   (make_rule ~lhs ~equiv ~rhs name));;

let sigma_1_rule =
  let name = "sigma_1_rule" in
  let sigma_1 = (get_air_fn "arm.inst_sfp_crypto_three_reg_sha512.sigma_1") in
  let eor_i = (get_air_fn "arm.inst_dpr_logical_shifted_reg.eor64") in
  let ror_i = (get_air_fn "arm.inst_dpi_extract.ror64") in
  let a = (sb 64 "a") in
  let ror_19 = (apply ror_i [(cb 32 19); a; a]) in
  let ror_61 = (bvror 61 a) in
  let ror_6 = (bvrsh 64 a (cb 32 6)) in
  let lhs = (apply eor_i [(apply eor_i [ror_19; ror_61]); ror_6]) in
  let equiv = Equal in
  let rhs = (apply sigma_1 [a; (bv_partsel a 6 58)]) in
  (let _ = Smtverify.air_prove ~lhs:lhs ~rhs:rhs name in
   (make_rule ~lhs ~equiv ~rhs name));;

let sigma_0_rule =
  let name = "sigma_0_rule" in
  let sigma_0 = (get_air_fn "arm.inst_sfp_crypto_two_reg_sha512.sigma_0") in
  let eor_i = (get_air_fn "arm.inst_dpr_logical_shifted_reg.eor64") in
  let ror_i = (get_air_fn "arm.inst_dpi_extract.ror64") in
  let a = (sb 64 "a") in
  let ror_1 = (apply ror_i [(cb 32 1); a; a]) in
  let ror_8 = (bvror 8 a) in
  let ror_7 = (bvrsh 64 a (cb 32 7)) in
  let lhs = (apply eor_i [(apply eor_i [ror_1; ror_8]); ror_7]) in
  let equiv = Equal in
  let rhs = (apply sigma_0 [a; (bv_partsel a 7 57)]) in
  (let _ = Smtverify.air_prove ~lhs:lhs ~rhs:rhs name in
   (make_rule ~lhs ~equiv ~rhs name));;

let rev_rule =
  let name = "rev_rule" in
  let rev = (get_air_fn "specs.common.bv_revbytes64") in
  let rev_i = (get_air_fn "arm.inst_dpr_one_src.rev64") in
  let a = (sb 64 "a") in
  let lhs = (apply rev_i [a]) in
  let equiv = Equal in
  let rhs = (apply rev [a]) in
  (let _ = Smtverify.air_prove ~lhs:lhs ~rhs:rhs name in
   (make_rule ~lhs ~equiv ~rhs name));;


let bvchop_bvadd_rule =
  let name = "bvchop_bvadd_rule" in
  let a = (sb 65 "a_65") in
  let lhs = (bvchop 64 (bvadd 65 a (cb 1 0))) in
  let equiv = Equal in
  let rhs = (bvchop 64 a) in
  (let _ = Smtverify.air_prove ~lhs:lhs ~rhs:rhs name in
   (make_rule ~lhs ~equiv ~rhs name));;

let bvchop_bvadd_rule2 =
  let name = "bvchop_bvadd_rule2" in
  let a = (sb 64 "a") in
  let b = (sb 64 "b") in
  let lhs = (bvchop 64 (bvadd 65 a b)) in
  let equiv = Equal in
  let rhs = (bvadd 64 a b) in
  (let _ = Smtverify.air_prove ~lhs:lhs ~rhs:rhs name in
   (make_rule ~lhs ~equiv ~rhs name));;

let commutativity_and_associativity_of_bvadd_1 =
  let name = "commutativity_and_associativity_of_bvadd_1" in
  let sigma_big_1 = (get_air_fn Sha2.air_S1_name) in
  let ch    = (get_air_fn Sha2.air_Ch_name) in
  let x0 = (sb 64 "x0") in
  let x1 = (sb 64 "x1") in
  let x2 = (sb 64 "x2") in
  let x3 = (sb 64 "x3") in
  let x4 = (sb 64 "x4") in
  let x5 = (sb 64 "x5") in
  let lhs = (bvadd 64
               (bvadd 64
                  (bvadd 64
                     (bvadd 64 x0
                        (apply sigma_big_1 [x3]))
                     (apply ch [x3; x4; x5])) x1) x2) in
  let equiv = Equal in
  let rhs = (bvadd 64
               (bvadd 64
                  (bvadd 64 (bvadd 64 x0 x1) x2)
                  (apply ch [x3; x4; x5]))
               (apply sigma_big_1 [x3])) in
  (let _ = Smtverify.air_prove ~lhs:lhs ~rhs:rhs name in
   (make_rule ~lhs ~equiv ~rhs name));;

let commutativity_and_associativity_of_bvadd_2 =
  let name = "commutativity_and_associativity_of_bvadd_2" in
  let sigma_big_0 = (get_air_fn Sha2.air_S0_name) in
  let maj   = (get_air_fn Sha2.air_Maj_name) in
  let x0 = (sb 64 "x0") in
  let x1 = (sb 64 "x1") in
  let x2 = (sb 64 "x2") in
  let x3 = (sb 64 "x3") in
  let lhs = (bvadd 64 x0
               (bvadd 64
                  (apply sigma_big_0 [x1])
                  (apply maj [x1; x2; x3]))) in
  let equiv = Equal in
  let rhs = (bvadd 64
               (bvadd 64 x0 (apply maj [x1; x2; x3]))
               (apply sigma_big_0 [x1])) in
  (let _ = Smtverify.air_prove ~lhs:lhs ~rhs:rhs name in
   (make_rule ~lhs ~equiv ~rhs name));;

let commutativity_and_associativity_of_bvadd_3 =
  let name = "commutativity_and_associativity_of_bvadd_3" in
  let sigma_1 = (get_air_fn Sha2.air_s1_name) in
  let sigma_0 = (get_air_fn Sha2.air_s0_name) in
  let x0 = (sb 64 "x0") in
  let x1 = (sb 64 "x1") in
  let x2 = (sb 64 "x2") in
  let x3 = (sb 64 "x3") in
  let lhs = (bvadd 64
               (bvadd 64
                  (bvadd 64 x2
                     (apply sigma_0 [x0])) x3)
                  (apply sigma_1 [x1])) in
  let equiv = Equal in
  let rhs = (bvadd 64
               (bvadd 64
                  (bvadd 64 x2 x3)
                  (apply sigma_0 [x0]))
               (apply sigma_1 [x1])) in
  (let _ = Smtverify.air_prove ~lhs:lhs ~rhs:rhs name in
   (make_rule ~lhs ~equiv ~rhs name));;

   let rev64_of_rev64_rule =
    let name = "rev64_of_rev64_rule" in
    let lhs =  (apply (get_air_fn "specs.common.bv_revbytes64")
                  [(apply (get_air_fn "specs.common.bv_revbytes64") [(sb 64 "x")])]) in
    let equiv = Equal in
    let rhs = (sb 64 "x") in
    (let _ = Smtverify.air_prove ~lhs:lhs ~rhs:rhs name in
     (make_rule ~lhs ~equiv ~rhs name));;
  
  (* Equivalence between spec s0, s1, S0, S1, Maj, Ch and their corresponding impl functions *)
  let sigma0_equiv_rule = 
    let name = "sigma0_equiv_rule" in
    let impl = get_air_fn "arm.inst_sfp_crypto_two_reg_sha512.sigma_0" in
    let spec = get_air_fn Sha2.air_s0_name in
    let a = (sb 64 "a") in
    let lhs = (apply impl [a; (bv_partsel a 7 57)]) in
    let equiv = Equal in
    let rhs = (apply spec [a]) in
    (let _ = Smtverify.air_prove ~lhs:lhs ~rhs:rhs name in
      (make_rule ~lhs ~equiv ~rhs name));;
  
  let sigma1_equiv_rule = 
    let name = "sigma1_equiv_rule" in
    let impl = get_air_fn "arm.inst_sfp_crypto_three_reg_sha512.sigma_1" in
    let spec = get_air_fn Sha2.air_s1_name in
    let a = (sb 64 "a") in
    let lhs = (apply impl [a; (bv_partsel a 6 58)]) in
    let equiv = Equal in
    let rhs = (apply spec [a]) in
    (let _ = Smtverify.air_prove ~lhs:lhs ~rhs:rhs name in
      (make_rule ~lhs ~equiv ~rhs name));;
  
  let sigma0_big_equiv_rule = 
    let name = "sigma0_big_equiv_rule" in
    let impl = get_air_fn "arm.inst_sfp_crypto_three_reg_sha512.sigma_big_0" in
    let spec = get_air_fn Sha2.air_S0_name in
    let a = (sb 64 "a") in
    let lhs = (apply impl [a]) in
    let equiv = Equal in
    let rhs = (apply spec [a]) in
    (let _ = Smtverify.air_prove ~lhs:lhs ~rhs:rhs name in
      (make_rule ~lhs ~equiv ~rhs name));;
  
  let sigma1_big_equiv_rule =
    let name = "sigma1_big_equiv_rule" in
    let impl = get_air_fn "arm.inst_sfp_crypto_three_reg_sha512.sigma_big_1" in
    let spec = get_air_fn Sha2.air_S1_name in
    let a = (sb 64 "a") in
    let lhs = (apply impl [a]) in
    let equiv = Equal in
    let rhs = (apply spec [a]) in
    (let _ = Smtverify.air_prove ~lhs:lhs ~rhs:rhs name in
      (make_rule ~lhs ~equiv ~rhs name));;
  
  let maj_equiv_rule = 
    let name = "maj_equiv_rule" in
    let impl = get_air_fn "arm.inst_sfp_crypto_three_reg_sha512.maj" in
    let spec = get_air_fn Sha2.air_Maj_name in
    let a = (sb 64 "a") in
    let b = (sb 64 "b") in
    let c = (sb 64 "c") in
    let lhs = (apply impl [a;b;c]) in
    let equiv = Equal in
    let rhs = (apply spec [a;b;c]) in
    (let _ = Smtverify.air_prove ~lhs:lhs ~rhs:rhs name in
      (make_rule ~lhs ~equiv ~rhs name));;
  
  let ch_equiv_rule = 
    let name = "ch_equiv_rule" in
    let impl = get_air_fn "arm.inst_sfp_crypto_three_reg_sha512.ch" in
    let spec = get_air_fn Sha2.air_Ch_name in
    let a = (sb 64 "a") in
    let b = (sb 64 "b") in
    let c = (sb 64 "c") in
    let lhs = (apply impl [a;b;c]) in
    let equiv = Equal in
    let rhs = (apply spec [a;b;c]) in
    (let _ = Smtverify.air_prove ~lhs:lhs ~rhs:rhs name in
      (make_rule ~lhs ~equiv ~rhs name));;

(* ---------------------------------------------------------------------- *)
(* Rules needed for unbounded proof *)

let bvsub_bvadd_rule =
  let name = "bvsub_bvadd_rule" in
  let lhs = (bvsub 64
               (bvadd 64 (sb 64 "x") (cb 64 0x1))
               (cb 64 0x1))
  in
  let equiv = Equal in
  let rhs = (sb 64 "x") in
  let _ =
    Smtverify.air_prove
      ~lhs:lhs ~rhs:rhs name in
  (make_rule ~lhs ~equiv ~rhs name);;

let simplify_input_index_rule =
  let name = "simplify_input_index_rule" in
  let hyp = (bveq 7 (bv_partsel (sb 64 "x") 0 7) (cb 7 0)) in
  let lhs =
    (bvlsh 64 (bvrsh 64 (sb 64 "x") (cb 32 0x7)) (cb 32 7))
  in
  let equiv = Equal in
  let rhs = (sb 64 "x") in
  let _ =
    Smtverify.air_prove
      ~hyp:hyp
      ~lhs:lhs ~rhs:rhs name in
  (make_rule ~hyps:[hyp] ~lhs ~equiv ~rhs name);;

let simplify_num_blks_hashed_rule =
  let name = "simplify_num_blks_hashed_rule" in
  (*

   Instead of using the following hypothesis involving num_blocks, we
   pick the one involving a concrete number to avoid free variables.

   (bvlt 64 (sb 64 "__s0_undefhavoc_gpr1_16767")
            (bvlsh 64 (sb 64 "num_blocks") (cb 32 7)))

  *)
  let hyps = [(bvlt 64 (sb 64 "__s0_undefhavoc_gpr1_16767") (s_cb 64 "0xFFFFFFFFFFFFFF80"))]
  in
  let genvar_83467 =
    (bvadd 64 (sb 64 "__s0_undefhavoc_gpr1_16767") (cb 64 16)) in
  let genvar_83468 = (bvchop 64 (bvadd 65 (bvadd 65 (bv_partsel genvar_83467 0 64) (cb 64 112)) (cb 1 0)))
  in
  let lhs = (bvrsh 64 genvar_83468 (cb 32 7)) in
  let equiv = Equal in
  let rhs =  (bvadd 64 (bvrsh 64 (sb 64  "__s0_undefhavoc_gpr1_16767") (cb 32 7)) (cb 64 1)) in
  let _ = Smtverify.air_prove ~hyp:(band_list hyps) ~lhs:lhs ~rhs:rhs name in
  (make_rule ~hyps ~lhs ~equiv ~rhs name);;
(* print_rule simplify_num_blks_hashed_rule;; *)


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
        [w0; w1; w2; w3; w4; w5; w6; w7; w8; w9; w10; w11; w12; w13; w14; w15]))
  in
  let rhs =  (apply Sha2.air_processBlock_Common_rec (rec_call :: input_block)) in
  (let _ = Smtverify.air_prove ~lhs:lhs ~rhs:rhs ~theory:[Sha512rec_theorems.sha512_spec_base_theorem; Sha512rec_theorems.sha512_spec_ind_theorem] name in
   (make_rule ~lhs ~equiv ~rhs name));;

let sha512_inductive_case_rule =
  let open Arm in
  let name = "sha512_inductive_case_rule" in
  let base_idx = (bvadd 64 (sb 64 "var_1") (cb 64 1)) in
  let hyp = (bvlt 64 (cb 64 0) base_idx) in
  let ctx = (sb 512 "ctx") in
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
