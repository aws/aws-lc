(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: Apache-2.0 *)

open Air;;
module Cryptol = Cryptol;;

(* We now prove two theorems about SHA512_SPEC using its definitional
   axiom: sha512_spec_base_theorem and sha512_spec_ind_theorem. These two
   theorems help us in crafting rewrite rules that can simplify the
   unbounded proof obligations of sha512_block_armv8 and
   sha512_block_data_order. *)

air_fn_set_uninterpreted_status false [Sha2.air_processBlocks_rec_name];;
air_fn_set_uninterpreted_status true [Sha2.air_processBlock_Common_rec_name];;

let sha512_spec_base_theorem =
  (let formula =
    (bveq
        512
        (apply Sha2.air_processBlocks_rec [(sb 512 "ctx"); (cb 64 0); (smem "input" 64 64)])
        (sb 512 "ctx"))
    in
    let _ =
      Smtverify.air_prove
        ~formula:formula
        (* By default, OSI will map an Air recursive function to an SMT
           recursive function. To use universal quantifiers to state
           the definitional axiom, use the ~defun_conversion_list
           labeled argument of air_prove. *)
        "sha512_spec_base_theorem"
    in
      formula);;

let sha512_spec_ind_theorem =
  let open Arm in
  let formula =
    (let i = (bound_sb 64 "i") in (* i: Number of blocks *)
     let i_1 = (bvsub 64 i (cb 64 1)) in
     let ctx = (sb 512 "ctx") in
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
     let input_block = (List.map
             (fun x -> (apply (get_air_fn "specs.common.bv_revbytes64") [x]))
             [w0; w1; w2; w3; w4; w5; w6; w7; w8; w9; w10; w11; w12; w13; w14; w15]) in
     let rec_call = (apply Sha2.air_processBlocks_rec [ctx; i_1; (smem "input" 64 64)]) in
     (forall [i]
        (implies (bnot (bveq 64 i (cb 64 0)))
           (bveq
              512
              (apply Sha2.air_processBlocks_rec [ctx; i; (smem "input" 64 64)])
              (apply Sha2.air_processBlock_Common_rec (rec_call :: input_block))))
        "sha512_spec_ind_theorem"))
  in
  let _ =
    Smtverify.air_prove ~formula:formula "sha512_spec_ind_theorem" in
  formula;;

air_fn_set_uninterpreted_status true [Sha2.air_processBlock_Common_rec_name];;
air_fn_set_uninterpreted_status true [Sha2.air_processBlocks_rec_name];;
