(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License").
 * You may not use this file except in compliance with the License.
 * A copy of the License is located at
 *
 *  http://aws.amazon.com/apache2.0
 *
 * or in the "LICENSE" file accompanying this file. This file is distributed
 * on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing
 * permissions and limitations under the License.
 *)

(* ========================================================================= *)
(* Load basic background needed for the ARM bignum proofs.                   *)
(* ========================================================================= *)

loadt "update_database.ml";;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Some background theory from the standard libraries.                       *)
(* ------------------------------------------------------------------------- *)

needs "Library/iter.ml";;
needs "Library/rstc.ml";;
needs "Library/bitsize.ml";;
needs "Library/pocklington.ml";;
needs "Library/integer.ml";;
needs "Library/words.ml";;
needs "Library/bitmatch.ml";;

(* ------------------------------------------------------------------------- *)
(* Common ARM-X86 proof infrastructure.                                      *)
(* ------------------------------------------------------------------------- *)

loadt "Common/overlap.ml";;
loadt "Common/for_hollight.ml";;
loadt "Common/words2.ml";;
loadt "Common/misc.ml";;
loadt "Common/components.ml";;
loadt "Common/records.ml";;
loadt "Common/relational.ml";;
loadt "Common/interval.ml";;
loadt "Common/elf.ml";;

loadt "Arm/instruction.ml";;
loadt "Arm/decode.ml";;
loadt "Arm/arm.ml";;

prioritize_int();;
prioritize_real();;
prioritize_num();;

loadt "Common/bignum.ml";;
