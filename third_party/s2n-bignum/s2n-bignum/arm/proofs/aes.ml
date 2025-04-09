(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)
needs "common/aes.ml";;

let aese = new_definition `aese (d:128 word) (n:128 word) =
  aes_sub_bytes joined_GF2 (aes_shift_rows (word_xor d n)) `;;

let aesmc = new_definition `aesmc (n: 128 word) = aes_mix_columns n`;;

let aesd = new_definition `aesd (d:128 word) (n:128 word) =
  aes_sub_bytes joined_GF2_inv (aes_inv_shift_rows (word_xor d n)) `;;

let aesimc = new_definition `aesimc (n: 128 word) = aes_inv_mix_columns n`;;

(************************************************)
(** CONVERSIONS                                **)
(************************************************)

let AESE_HELPER_CONV =
  REWRITE_CONV [aese] THENC
  AES_SHIFT_ROWS_CONV THENC
  AES_SUB_BYTES_CONV THENC
  DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV);;

let AESMC_HELPER_CONV =
  REWRITE_CONV [aesmc] THENC AES_MIX_COLUMNS_CONV;;

let AESD_HELPER_CONV =
  REWRITE_CONV [aesd] THENC
  AES_INV_SHIFT_ROWS_CONV THENC
  AES_SUB_BYTES_CONV THENC
  DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV);;

let AESIMC_HELPER_CONV =
  REWRITE_CONV [aesimc] THENC AES_INV_MIX_COLUMNS_CONV;;

(* Stop early if unmatched. Conversions will become extremely
  expensive if we don't stop early *)
let AESE_REDUCE_CONV tm =
    match tm with
      Comb(Comb(Const("aese",_),
           Comb(Const("word",_),d)),
           Comb(Const("word",_),n))
    when is_numeral d && is_numeral n -> AESE_HELPER_CONV tm
  | _ -> failwith "AESE_REDUCE_CONV: inapplicable";;
let AESMC_REDUCE_CONV tm =
    match tm with
      Comb(Const("aesmc",_), Comb(Const("word",_),n))
    when is_numeral n -> AESMC_HELPER_CONV tm
  | _ -> failwith "AESMC_REDUCE_CONV: inapplicable";;
let AESD_REDUCE_CONV tm =
    match tm with
      Comb(Comb(Const("aesd",_),
           Comb(Const("word",_),d)),
           Comb(Const("word",_),n))
    when is_numeral d && is_numeral n -> AESD_HELPER_CONV tm
  | _ -> failwith "AESD_REDUCE_CONV: inapplicable";;
let AESIMC_REDUCE_CONV tm =
    match tm with
      Comb(Const("aesimc",_), Comb(Const("word",_),n))
    when is_numeral n -> AESIMC_HELPER_CONV tm
  | _ -> failwith "AESIMC_REDUCE_CONV: inapplicable";;
