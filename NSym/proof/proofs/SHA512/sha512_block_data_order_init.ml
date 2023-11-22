(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
  SPDX-License-Identifier: Apache-2.0*)

open Air;;
open Arm;;

(* ---------------------------------------------------------------------- *)

let print_hex (intstr : string) : unit =
  let hexstr = Z.format "%#x" (Z.of_string intstr) in
  Format.fprintf Format.std_formatter "@[<1>%s@]@." hexstr;;

(* Functions to help in program state initialization *)
let digest_size = 512;;

let adrp_base_int =
  (Int.shift_left (Int.shift_right Sha512_program.sha512_block_data_order_start_address 12) 12);;
print_hex (Int.to_string adrp_base_int);;
let adrp_base = (cb 64 adrp_base_int);;
print_hex (Int.to_string Sha512_program.openssl_armcap_p_start_address);;
let openssl_armcap_p_offset_int = Sha512_program.openssl_armcap_p_start_address - adrp_base_int;;
let openssl_armcap_p_offset_complement = Z.extract (Z.of_int openssl_armcap_p_offset_int) 0 64;;
let openssl_armcap_p_offset = (s_cb 64 (Z.format "%#x" openssl_armcap_p_offset_complement));;
print_airexp openssl_armcap_p_offset;;
let (openssl_armcap_p_pointer : State.mem_tracker) =
  { id = Some adrp_base; offset = openssl_armcap_p_offset };;

print_hex (Int.to_string Sha512_program.k512_start_address);;
let ktbl_offset_int = (Sha512_program.k512_start_address - adrp_base_int);;
print_hex (Int.to_string ktbl_offset_int);;
let ktbl_offset_complement = Z.extract (Z.of_int ktbl_offset_int) 0 64;;
print_hex (Int64.to_string (Z.to_int64_unsigned ktbl_offset_complement));;
let ktbl_offset = (s_cb 64 (Z.format "%#x" ktbl_offset_complement));;
print_airexp ktbl_offset;;
let (ktbl_pointer : State.mem_tracker) =
  { id = Some adrp_base; offset = ktbl_offset };;

let sha512_block_data_order_init_state
    ~(num_blocks : airExp)
    ~(ctx_base : airExp)
    ~(ctx : airExp list option) (* Least significant blocks first. *)
    ~(input_base : airExp)
    ~(input : airExp list option) (* Least significant blocks first. *)
    (message : string) : State.t =

  (assert ((Option.is_none input) || (Air.is_concrete_value num_blocks)));

  let open State in

  (* num_bytes = num_blocks * 128 *)
  let num_bytes = (bvlsh 64 num_blocks (cb 32 7)) in

  let state =
    init
      ~stack_size:(Some (cb 64 1024))
      ~stack_offset:(Some (cb 64 256))
      (* We need the stack data width to be 64 here (which,
         thankfully, works out for this program becfause that's the
         granularity of accesses to the stack). The need part comes in
         because right now NSym cannot deal with 'mixed' accesses
         (i.e., accesses involving some addresses that store regular
         data and some that store pointers). If the stack data width
         isn't 64, then NSym can't infer that no 'mixed' accesses are
         occurring, ugh. *)
      ~stack_data_width:64
      ~program_loc:Sha512_program.sha512_block_data_order_start_address
      ~program:Sha512_program.sha512_block_data_order_bytes
      ~pc:Sha512_program.sha512_block_data_order_start_address
      "State initialized for sha512_block_data_order."
  in
  let ctx_pointer = State.make_pointer ctx_base in
  let input_pointer = State.make_pointer input_base in
  (* ktbl data should eventually be copied over from the .rodata section. *)
  let ktbl = Cryptol.toAir2Dim Sha2.k in
  let state =
    State.add_separate_mem_region
      ~name:"ctx_region" ~aw:64 ~dw:64
      ~base_addr:ctx_base ~size:(cb 64 (digest_size / 8))
      ~alignment:8
      state
  in
  let state =
    State.add_separate_mem_region
      ~name:"input_region" ~aw:64 ~dw:64
      ~base_addr:input_base
      ~size:num_bytes
      ~alignment:8
      state
  in
  let _ = print_hex (Z.to_string ktbl_offset_complement) in
  let ktbl_size = Z.add ktbl_offset_complement (Z.of_int ((1 + (List.length ktbl)) * 8)) in
  let armcap_size = Z.add openssl_armcap_p_offset_complement (Z.of_int 4) in
  let max_size = s_cb 64 (Z.format "%#x" (if (Z.compare ktbl_size armcap_size)>=0 then ktbl_size else armcap_size)) in
  let _ = print_hex (Z.to_string ktbl_size) in
  let _ = print_hex (Z.to_string armcap_size) in
  let _ = print_airexp max_size in
  let state =
    State.add_separate_mem_region
      ~name:"ktbl_region" ~aw:64 ~dw:32
      ~base_addr:adrp_base
      (* Note: both ktbl constants and evp_meth_offset are located in
         the same memory region. *)
      ~size:max_size
      ~alignment:4
      state
  in
  (* Making sure that w16 & 64 != 0 so that we bypass *)
  (* sha512_block_armv8.  See instructions at PC 125680-88.*)
  let w16_source_pointer = State.make_pointer adrp_base in
  let w16_source_pointer = { w16_source_pointer with offset = openssl_armcap_p_offset } in
  let state = State.write_mem_data 4 w16_source_pointer (cb 32 0x3d) state in
  let state =
    upd_gprs
      [
        (* x0: pointer to context *)
        (64, 0, ctx_pointer);
        (* x1: pointer to input *)
        (64, 1, input_pointer);
        (* Number of blocks. *)
        (64, 2, (State.make_gpr_data num_blocks));
      ]
      state
  in
  (* Initial hash value *)
  let state =
    if (Option.is_none ctx) then
      state
    else
      write_mem_data (8 * 8) ctx_pointer (bvapp_list (Option.get ctx)) state in
  (* Input block *)
  let state =
    if (Option.is_none input) then
      state
    else
      let input_length_bytes = (Z.to_int (Sem.Bv.to_z (get_cb_val num_bytes))) in
      write_mem_data input_length_bytes input_pointer (Air.bvapp_list (Option.get input)) state in
  (* 80 SHA512 constants, followed by a 64'0. *)
  let (_, state) =
    List.fold_left
      (fun (i, s) k ->
         (i + 8,
          (write_mem_data
             8
             {ktbl_pointer with offset = (cb 64 (ktbl_offset_int + i))}
             k s)))
      (0, state)
      (ktbl @ [(cb 64 0)])
  in
  (Format.fprintf Format.std_formatter "@[%s@]@.@." message;
   state);;

(* ---------------------------------------------------------------------- *)

(* Some utility functions *)

let ctx_ptr (s : State.t) : State.mem_tracker =
  (State.gpr 64 0 s)

let input_ptr (s : State.t) : State.mem_tracker =
  (State.gpr 64 1 s)

let end_of_input_ptr (s : State.t) : State.mem_tracker =
  (State.gpr 64 2 s)

(* ---------------------------------------------------------------------- *)
