(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: Apache-2.0*)

(* Check the automatically generated specification satisfies the test vectors *)

module Cryptol = Cryptol
open Air

(* Test vector
   https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/SHA512.pdf
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
                        (Cryptol.toCry2Dim [(s_cb wordsize "0xddaf35a193617aba");
                                            (s_cb wordsize "0xcc417349ae204131");
                                            (s_cb wordsize "0x12e6fa4e89a97ea2");
                                            (s_cb wordsize "0x0a9eeee64b55d39a");
                                            (s_cb wordsize "0x2192992a274fc1a8");
                                            (s_cb wordsize "0x36ba3c23a3feebbd");
                                            (s_cb wordsize "0x454d4423643ce80e");
                                            (s_cb wordsize "0x2a9ac94fa54ca49f")]);;

air_fn_set_beta_reduce_status true ["spec.SHA512rec.air_processBlocks_rec"];;

(* Run SHA512 specification *)
let digest = 
  let n = (s_cb 64 "0x1") in
  let h0 = (Cryptol.join "0x8" "0x40" Cryptol.Bit Autospecs.SHA512rec.lowercase_H0) in
  Autospecs.SHA512rec.lowercase_processBlocks_rec h0 (Cryptol.CryBV(n)) message;;

let flat_digest = digest;;

(* Compare digest with expected digest *)
match flat_digest, expected_digest with
| Cryptol.CryBV(fv), Cryptol.CryBV(exp) 
  -> let _ = print_airexp fv in 
     let _ = print_airexp exp in 
     assert (flat_digest = expected_digest)
| _ -> assert false;;

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
                        (Cryptol.toCry2Dim [(s_cb wordsize "0x8E959B75DAE313DA");
                                            (s_cb wordsize "0x8CF4F72814FC143F");
                                            (s_cb wordsize "0x8F7779C6EB9F7FA1");
                                            (s_cb wordsize "0x7299AEADB6889018");
                                            (s_cb wordsize "0x501D289E4900F7E4");
                                            (s_cb wordsize "0x331B99DEC4B5433A");
                                            (s_cb wordsize "0xC7D329EEB6DD2654");
                                            (s_cb wordsize "0x5E96E55B874BE909")]);;

(* Run SHA512 specification *)
let digest = 
  let n = (s_cb 64 "0x2") in
  let h0 = (Cryptol.join "0x8" "0x40" Cryptol.Bit Autospecs.SHA512rec.lowercase_H0) in
  Autospecs.SHA512rec.lowercase_processBlocks_rec h0 (Cryptol.CryBV(n)) message2;;

let flat_digest = digest;;

(* Compare digest with expected digest *)
match flat_digest, expected_digest with
| Cryptol.CryBV(fv), Cryptol.CryBV(exp) 
  -> let _ = print_airexp fv in 
     let _ = print_airexp exp in 
     assert (flat_digest = expected_digest)
| _ -> assert false

(* ---------------------------------------------------------------------- *)
