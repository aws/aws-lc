(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "Library/words.ml";;

(* EVAL evaluates a HOL-Light term using compute module.
   Adapted from June Lee's initial code. *)
let EVAL thms =
  let rw = Compute.bool_compset () in
  (* avoid folding the branches of conditional expression
     before evaluating its condition *)
  let _ = Compute.set_skip rw `COND: bool -> A -> A -> A` (Some 1) in
  let _ = num_compute_add_convs rw in
  let _ = word_compute_add_convs rw in
  let _ = Compute.add_thms [EL_CONS;LET_END_DEF] rw in
  let _ = Compute.add_thms thms rw in
  Compute.WEAK_CBV_CONV rw;;

(* A pretty printer for printing numbers in hex.
   It can be installed by:
     install_user_printer("pp_print_num",pp_print_num_hex);; *)
let pp_print_num_hex fmt tm =
  let n = dest_numeral tm in
  pp_print_string fmt (string_of_num_hex n);;
