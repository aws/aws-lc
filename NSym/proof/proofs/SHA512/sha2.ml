(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: Apache-2.0 *)

(* This file is a way to parameterized the sha512_block_data_order and sha512_block_armv8 proofs *)
(* It reads an environment variable called NSYM_SHA2_VERSION. If the variable is defined as SHA512,
   choose SHA512 functions as the set of functions to be used in verification; otherwise,
   choose SHA384. *)

module Sys = Sys

let version = try Sys.getenv("NSYM_SHA2_VERSION")
              with Not_found -> failwith ("Error: Environment variable NSYM_SHA2_VERSION is not found!")
let choose a b = (if version = "SHA512" then a else b)

let h0 = choose Autospecs.SHA512rec.lowercase_H0 Autospecs.SHA384rec.lowercase_H0
let k = choose Autospecs.SHA512rec.lowercase_K Autospecs.SHA384rec.lowercase_K
let sigma_big_0 = choose Autospecs.SHA512rec.lowercase_S0 Autospecs.SHA384rec.lowercase_S0
let sigma_big_1 = choose Autospecs.SHA512rec.lowercase_S1 Autospecs.SHA384rec.lowercase_S1
let sigma_0 = choose Autospecs.SHA512rec.lowercase_s0 Autospecs.SHA384rec.lowercase_s0
let sigma_1 = choose Autospecs.SHA512rec.lowercase_s1 Autospecs.SHA384rec.lowercase_s1
let ch = choose Autospecs.SHA512rec.lowercase_Ch Autospecs.SHA384rec.lowercase_Ch
let maj = choose Autospecs.SHA512rec.lowercase_Maj Autospecs.SHA384rec.lowercase_Maj
let message_schedule_word = choose Autospecs.SHA512rec.lowercase_messageSchedule_Word
                              Autospecs.SHA384rec.lowercase_messageSchedule_Word
let compress_common_t1 = choose Autospecs.SHA512rec.lowercase_compress_Common_t1
                           Autospecs.SHA384rec.lowercase_compress_Common_t1
let compress_common_t2 = choose Autospecs.SHA512rec.lowercase_compress_Common_t2
                           Autospecs.SHA384rec.lowercase_compress_Common_t2
let compress_common_e = choose Autospecs.SHA512rec.lowercase_compress_Common_e
                          Autospecs.SHA384rec.lowercase_compress_Common_e
let compress_common_a = choose Autospecs.SHA512rec.lowercase_compress_Common_a
                          Autospecs.SHA384rec.lowercase_compress_Common_a
let processblock_common_rec = choose Autospecs.SHA512rec.lowercase_processBlock_Common_rec
                                Autospecs.SHA384rec.lowercase_processBlock_Common_rec
let processblocks_rec = choose Autospecs.SHA512rec.lowercase_processBlocks_rec
                          Autospecs.SHA384rec.lowercase_processBlocks_rec


let air_S0 = choose Autospecs.SHA512rec.air_s0 Autospecs.SHA384rec.air_S0
let air_S1 = choose Autospecs.SHA512rec.air_S1 Autospecs.SHA384rec.air_S1
let air_s0 = choose Autospecs.SHA512rec.air_s0 Autospecs.SHA384rec.air_s0
let air_s1 = choose Autospecs.SHA512rec.air_s1 Autospecs.SHA384rec.air_s1
let air_Ch = choose Autospecs.SHA512rec.air_Ch Autospecs.SHA384rec.air_Ch
let air_Maj = choose Autospecs.SHA512rec.air_Maj Autospecs.SHA384rec.air_Maj
let air_messageSchedule_Word = choose Autospecs.SHA512rec.air_messageSchedule_Word
                                 Autospecs.SHA384rec.air_messageSchedule_Word
let air_compress_Common_t1 = choose Autospecs.SHA512rec.air_compress_Common_t1
                               Autospecs.SHA384rec.air_compress_Common_t1
let air_compress_Common_t2 = choose Autospecs.SHA512rec.air_compress_Common_t2
                               Autospecs.SHA384rec.air_compress_Common_t2
let air_compress_Common_e = choose Autospecs.SHA512rec.air_compress_Common_e
                              Autospecs.SHA384rec.air_compress_Common_e
let air_compress_Common_a = choose Autospecs.SHA512rec.air_compress_Common_a
                              Autospecs.SHA384rec.air_compress_Common_a
let air_processBlock_Common_rec = choose Autospecs.SHA512rec.air_processBlock_Common_rec
                                    Autospecs.SHA384rec.air_processBlock_Common_rec
let air_processBlocks_rec = choose Autospecs.SHA512rec.air_processBlocks_rec
                              Autospecs.SHA384rec.air_processBlocks_rec

let air_S0_name = choose "spec.SHA512rec.air_S0" "spec.SHA384rec.air_S0"
let air_S1_name = choose "spec.SHA512rec.air_S1" "spec.SHA384rec.air_S1"
let air_s0_name = choose "spec.SHA512rec.air_s0" "spec.SHA384rec.air_s0"
let air_s1_name = choose "spec.SHA512rec.air_s1" "spec.SHA384rec.air_s1"
let air_Ch_name = choose "spec.SHA512rec.air_Ch" "spec.SHA384rec.air_Ch"
let air_Maj_name = choose "spec.SHA512rec.air_Maj" "spec.SHA384rec.air_Maj"
let air_messageSchedule_Word_name = choose "spec.SHA512rec.air_messageSchedule_Word"
                                      "spec.SHA384rec.air_messageSchedule_Word"
let air_compress_Common_t1_name = choose "spec.SHA512rec.air_compress_Common_t1"
                                    "spec.SHA384rec.air_compress_Common_t1"
let air_compress_Common_t2_name = choose "spec.SHA512rec.air_compress_Common_t2"
                                    "spec.SHA384rec.air_compress_Common_t2"
let air_compress_Common_e_name = choose "spec.SHA512rec.air_compress_Common_e"
                                   "spec.SHA384rec.air_compress_Common_e"
let air_compress_Common_a_name = choose "spec.SHA512rec.air_compress_Common_a"
                                   "spec.SHA384rec.air_compress_Common_a"
let air_processBlock_Common_rec_name = choose "spec.SHA512rec.air_processBlock_Common_rec"
                                         "spec.SHA384rec.air_processBlock_Common_rec"
let air_processBlocks_rec_name = choose "spec.SHA512rec.air_processBlocks_rec"
                                   "spec.SHA384rec.air_processBlocks_rec"
