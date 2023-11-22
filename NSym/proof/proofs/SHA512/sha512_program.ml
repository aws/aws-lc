(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
  SPDX-License-Identifier: Apache-2.0*)

open Air
open Elf_loader

(*--------------------------------------------------------------------*)
(*** Read in the entire crypto_test ELF and make sure it is configured
     as expected (i.e., 64-bit little-endian, has the expected
     sections, etc.).

     Note that the binary path below is relative to NSym's root
     because that's what dune/build system prefers. If you are
     executing this script interactively, give the path relative to
     your current working directory. You can use the following to
     check the CWD:

     let _ = Printf.printf "\n\nPWD: %s\n\n" (Unix.getcwd ());;
*)
let elf = Elf.read_elf_file "build/aarch64/crypto/crypto_test";;
let section_names = Elf.section_names elf;;
(* The .text section contains the program. *)
assert (Array.exists (fun e -> e = ".text") section_names);;
(* The .rodata section contains the read-only data. *)
assert (Array.exists (fun e -> e = ".rodata") section_names);;
(* The .symtab section contains, among other things, the function
   names and other identifiers--a.k.a symbols--and the address where
   that symbol is defined. *)
assert (Array.exists (fun e -> e = ".symtab") section_names);;
let machine_width = Elf.ei_elfclass_width elf.hdr.e_ident.ei_class;;
assert (machine_width = W64Bits);;
let ident = Elf.ei_elfdata_endian elf.hdr.e_ident.ei_data;;
assert (ident = Machine.LittleEndian);;

(*--------------------------------------------------------------------*)

(*** Read in both the SHA512 routines and retrieve their addresses
     from the symbol table. *)

let print_hex (intstr : string) : unit =
  let hexstr = Z.format "%#x" (Z.of_string intstr) in
  Format.fprintf Format.std_formatter "@[<1>%s@]@." hexstr;;

let (sha512_block_armv8_start_address, sha512_block_armv8_dump) =
  Elf.symbol_contents ~section_name:".symtab" "sha512_block_armv8" elf;;
let sha512_block_armv8_bytes =
  (Elf.uint32_list_of_data sha512_block_armv8_dump);;

(* Print, in hex, the list of sha512_block_armv8 instructions. *)
let _ = List.iter (fun i -> print_hex (Int.to_string i)) sha512_block_armv8_bytes;;

let (sha512_block_data_order_start_address, sha512_block_data_order_dump) =
  Elf.symbol_contents ~section_name:".symtab" "sha512_block_data_order" elf;;
let sha512_block_data_order_bytes =
  (Elf.uint32_list_of_data sha512_block_data_order_dump);;

(* Print, in hex, the list of sha512_block_data_order instructions. *)
let _ =  List.iter (fun i -> print_hex (Int.to_string i)) sha512_block_data_order_bytes;;

(* ---------------------------------------------------------------------- *)

(*** Read in the K512 constants from the binary. *)

let (k512_start_address, k512_dump) =
  Elf.symbol_contents ~section_name:".symtab" ".LK512" elf;;
(* We only care about the first 81 64-bit values (or first 81*2 32-bit
   values) here.*)
let k512_bytes =
  List.filteri (fun i _ -> i < 81 * 2)
    (Elf.uint32_list_of_data k512_dump);;

(* Print, in hex, the list of K512 bytes. *)
let _ = List.iter (fun i -> print_hex (Int.to_string i)) k512_bytes;;

(*** Check that there are 160 32-bit constants, and they are padded by
     64 zeroes at the end. This padding is needed for the termination
     of the inner loop of sha512_block_data_order). *)
assert (List.length k512_bytes = 81 * 2);;
assert (List.nth k512_bytes 160 = 0);;
assert (List.nth k512_bytes 161 = 0);;

(*** K512 is "more naturally" specified as 80 64-bit constants, given
     that SHA512's wordsize is 64. This function converts a list of
     32-bit values to 64-bit values. *)
let rec make_k512_u64s (k512_u32 : airExp list) : airExp list =
  match k512_u32 with
   | [] -> []
   | k_lo :: k_hi :: rst -> (bvapp k_lo k_hi) :: (make_k512_u64s rst)
   | _ -> failwith "Ill-formed input!"

let k512_rodata =
  let k512_bytes = List.filteri (fun i _ -> i < 80 * 2) k512_bytes in
  let k512_air_u32s = List.map (fun k -> (s_cb 32 (Int.to_string k))) k512_bytes in
  (make_k512_u64s k512_air_u32s);;

(* Check that k512 read from the program matches
   Specs.Sha512.SHA512.k. If so, we can use Specs.Sha512.SHA512.k and
   k512_rodata interchangably in our proofs. *)
assert (Specs.Sha512.SHA512.k = k512_rodata);;

(* ----------------------------------------------------------------------*)

(*** Read in the OPENSSL_armcap_P constant from the binary. *)

let openssl_armcap_p_start_address =
  Elf.symbol_address ~section_name:".symtab" "OPENSSL_armcap_P" elf;;
