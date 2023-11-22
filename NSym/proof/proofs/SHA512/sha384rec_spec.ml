(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: Apache-2.0  *)

(* Check the automatically generated specification satisfies the test vectors *)

module Cryptol = Cryptol
open Air

(* Test vector
   https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/SHA384.pdf
*)

(* Wordsize *)
let wordsize = 64;;

(* Message to be hashed *)
let message = Cryptol.array_from_seq "0x40" "0x40"
              (Cryptol.toCry2Dim [(s_cb wordsize "0x6162638000000000");
                                   (s_cb wordsize "0x0000000000000000");
                                   (s_cb wordsize "0x0000000000000000");
                                   (s_cb wordsize "0x0000000000000000");
                                   (s_cb wordsize "0x0000000000000000");
                                   (s_cb wordsize "0x0000000000000000");
                                   (s_cb wordsize "0x0000000000000000");
                                   (s_cb wordsize "0x0000000000000000");
                                   (s_cb wordsize "0x0000000000000000");
                                   (s_cb wordsize "0x0000000000000000");
                                   (s_cb wordsize "0x0000000000000000");
                                   (s_cb wordsize "0x0000000000000000");
                                   (s_cb wordsize "0x0000000000000000");
                                   (s_cb wordsize "0x0000000000000000");
                                   (s_cb wordsize "0x0000000000000000");
                                   (s_cb wordsize "0x0000000000000018")])
              (Cryptol.symbolic_malloc "message" 64 64);;

(* Expected digest *)
let expected_digest = Cryptol.join "0x6" "0x40" Cryptol.Bit
                        (Cryptol.toCry2Dim [(s_cb wordsize "0xCB00753F45A35E8B");
                                            (s_cb wordsize "0xB5A03D699AC65007");
                                            (s_cb wordsize "0x272C32AB0EDED163");
                                            (s_cb wordsize "0x1A8B605A43FF5BED");
                                            (s_cb wordsize "0x8086072BA1E7CC23");
                                            (s_cb wordsize "0x58BAECA134C825A7")]);;

air_fn_set_beta_reduce_status true ["spec.SHA384rec.air_processBlocks_rec";];;

(* Run SHA384 specification *)
let digest = 
  let n = (s_cb 64 "0x1") in
  let h0 = (Cryptol.join "0x8" "0x40" Cryptol.Bit Autospecs.SHA384rec.lowercase_H0) in
  Autospecs.SHA384rec.lowercase_processBlocks_rec h0 (Cryptol.CryBV(n)) message;;

let flat_digest = digest;;
let cut_digest = Cryptol.take "0x180" "0x80" Cryptol.Bit flat_digest;;

(* Compare digest with expected digest *)
match flat_digest, cut_digest, expected_digest with
| Cryptol.CryBV(fv), Cryptol.CryBV(bv), Cryptol.CryBV(exp) 
  -> let _ = print_airexp fv in 
     let _ = print_airexp bv in 
     let _ = print_airexp exp in 
     assert (cut_digest = expected_digest)
| _ -> assert false

(* ---------------------------------------------------------------------- *)

(* TEST 2: 2 blocks *)

(* Message to be hashed *)
let message2 = Cryptol.array_from_seq "0x40" "0x40"
                 (Cryptol.toCry2Dim [(s_cb wordsize "0x6162636465666768");
                                       (s_cb wordsize "0x6263646566676869");
                                       (s_cb wordsize "0x636465666768696A");
                                       (s_cb wordsize "0x6465666768696A6B");
                                       (s_cb wordsize "0x65666768696A6B6C");
                                       (s_cb wordsize "0x666768696A6B6C6D");
                                       (s_cb wordsize "0x6768696A6B6C6D6E");
                                       (s_cb wordsize "0x68696A6B6C6D6E6F");
                                       (s_cb wordsize "0x696A6B6C6D6E6F70");
                                       (s_cb wordsize "0x6A6B6C6D6E6F7071");
                                       (s_cb wordsize "0x6B6C6D6E6F707172");
                                       (s_cb wordsize "0x6C6D6E6F70717273");
                                       (s_cb wordsize "0x6D6E6F7071727374");
                                       (s_cb wordsize "0x6E6F707172737475");
                                       (s_cb wordsize "0x8000000000000000");
                                       (s_cb wordsize "0x0000000000000000");
                                       (s_cb wordsize "0x0000000000000000");
                                       (s_cb wordsize "0x0000000000000000");
                                       (s_cb wordsize "0x0000000000000000");
                                       (s_cb wordsize "0x0000000000000000");
                                       (s_cb wordsize "0x0000000000000000");
                                       (s_cb wordsize "0x0000000000000000");
                                       (s_cb wordsize "0x0000000000000000");
                                       (s_cb wordsize "0x0000000000000000");
                                       (s_cb wordsize "0x0000000000000000");
                                       (s_cb wordsize "0x0000000000000000");
                                       (s_cb wordsize "0x0000000000000000");
                                       (s_cb wordsize "0x0000000000000000");
                                       (s_cb wordsize "0x0000000000000000");
                                       (s_cb wordsize "0x0000000000000000");
                                       (s_cb wordsize "0x0000000000000000");
                                       (s_cb wordsize "0x0000000000000380");])
                  (Cryptol.symbolic_malloc "message2" 64 64);;

(* Expected digest *)
let expected_digest = Cryptol.join "0x6" "0x40" Cryptol.Bit
                        (Cryptol.toCry2Dim [(s_cb wordsize "0x09330C33F71147E8");
                                            (s_cb wordsize "0x3D192FC782CD1B47");
                                            (s_cb wordsize "0x53111B173B3B05D2");
                                            (s_cb wordsize "0x2FA08086E3B0F712");
                                            (s_cb wordsize "0xFCC7C71A557E2DB9");
                                            (s_cb wordsize "0x66C3E9FA91746039");]);;

(* Run SHA384 specification *)
let digest = 
  let n = (s_cb 64 "0x2") in
  let h0 = (Cryptol.join "0x8" "0x40" Cryptol.Bit Autospecs.SHA384rec.lowercase_H0) in
  Autospecs.SHA384rec.lowercase_processBlocks_rec h0 (Cryptol.CryBV(n)) message2;;

let flat_digest = digest;;
let cut_digest = Cryptol.take "0x180" "0x80" Cryptol.Bit flat_digest;;

(* Compare digest with expected digest *)
match flat_digest, cut_digest, expected_digest with
| Cryptol.CryBV(fv), Cryptol.CryBV(bv), Cryptol.CryBV(exp) 
  -> let _ = print_airexp fv in 
     let _ = print_airexp bv in 
     let _ = print_airexp exp in 
     assert (cut_digest = expected_digest)
| _ -> assert false

(* ---------------------------------------------------------------------- *)
