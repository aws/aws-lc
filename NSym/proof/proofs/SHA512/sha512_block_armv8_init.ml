(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
  SPDX-License-Identifier: Apache-2.0*)

open Air;;
open Arm;;

(*

   A note on initializing the Arm memory for SHA512 verification

   Briefly, NSym has a segmented memory model, and the user is
   required to explicitly declare the separate memory regions that
   will be accessed by a program (see
   State.add_separate_mem_region). NSym then keeps track of the memory
   region pointed to by every pointer.

   General-purpose registers and the stack pointer can contain
   addresses that index into a memory region. These registers can be
   conceptually viewed as a pair (tracker, value); the tracker is the
   base address of the memory region that the register indexes
   into. The SP must point to a memory region, and a GPR optionally
   so. When the tracker is present, then the register is a pointer and
   the value is the offset into the memory region. Otherwise, the
   value represents the contents (bitvector) of the register.

   Consider the signature of sha512_block_data_order:

   static void sha512_block_data_order(uint64_t *state, const *uint8_t in, size_t num_blocks);

   The first two arguments are pointers and the third one is
   not. According to the ABI (Application Binary Interface), these
   arguments correspond to Arm registers x0, x1, and x2,
   respectively. The user would need to initialize registers x0 and x1
   such that they point to the SHA512 state and input regions (search
   for "upd_gprs" below) AND define these two two as separate regions
   (search for "State.add_separate_mem_region" below).

   What about the Ktbl constants? ELF loader can tell us,
   programmatically, where they are located: see variable
   Sha512_program.k512_start_address in sha512_program.ml. But this
   address is computed in the SHA512 program, instead of being
   available in the function's signature. This means that the user
   does not need to initialize any register with the Ktbl pointer
   information. But how should the user initialize the Ktbl memory
   region?

   Consider the two instructions where this address computation
   happens; the KTbl values are located at the address in x3 (after
   the add instruction below is executed):

      1264d8: adrp	x3, 1b4000 <ecp_nistz256_precomputed+0x25000>
      1264dc: add	x3, x3, #0x300

   The ADRP instruction forms a PC-relative address to 4KB page, i.e.,
   it adds an immediate value that is shifted left by 12 bits, to the
   PC value to form a PC-relative address, with the bottom 12 bits
   masked out, and writes the result to the destination register.
   (see
   https://developer.arm.com/documentation/ddi0602/2023-09/Base-Instructions/ADRP--Form-PC-relative-address-to-4KB-page-?lang=en
   and NSym/arm/inst_dpi/inst_dpi_pc_rel_addr.ml).

   By the time NSym encounters ADRP, the memory region (corresponding
   to the address ADRP computes) should already be known to NSym. So
   the base address of the memory region should be the PC value with
   the low 12-bits zeroed out. Therefore, the offset for the Ktbl
   region would be (Sha512_program.k512_start_address - base address).

   How do we figure out the PC of ADRP programmatically? We could
   write a static analysis function that does that for us, but
   instead, we're taking a slightly risky but lazy approach. We assume
   that we will get the same value when we zero out the low 12 bits of
   address of the first instruction of the program (which ELF loader
   can determine programmatically) and also of the ADRP instruction.

   This is probably okay, since ADRP is very close to the beginning of
   the program (6th instruction in the stable program), and the
   chances of the first address of the program being located in a
   different 4K page as this instruction is low.

   If it does happen that the program is split across 2 4K pages, then
   the proof should fail and warn us.

*)

let print_hex (intstr : string) : unit =
  let hexstr = Z.format "%#x" (Z.of_string intstr) in
  Format.fprintf Format.std_formatter "@[<1>%s@]@." hexstr;;

assert
  (* Check whether the address of the first instruction of the
     program, with the low 12-bit zeroed out, is the same as that for
     ADRP. We are assuming that ADRP is the 5th instruction in the
     program. *)
  ((Int.shift_left (Int.shift_right Sha512_program.sha512_block_armv8_start_address 12)
      12)
   =
   (Int.shift_left (Int.shift_right
                      (* 5 * 4: 5 is the number of instructions before
                         ADRP, and 4 is the number of
                         bytes/instruction. *)
                      (Sha512_program.sha512_block_armv8_start_address + 5*4)
                      12)
      12));;

let adrp_base_int =
  (Int.shift_left (Int.shift_right Sha512_program.sha512_block_armv8_start_address 12)
     12);;
print_hex (Int.to_string adrp_base_int);;
let adrp_base = (cb 64 adrp_base_int);;
print_hex (Int.to_string Sha512_program.k512_start_address);;
let ktbl_offset_int = (Sha512_program.k512_start_address - adrp_base_int);;
print_hex (Int.to_string ktbl_offset_int);;
let ktbl_offset = (s_cb 64 (Z.format "%#x" (Z.extract (Z.of_int ktbl_offset_int) 0 64)));;
print_airexp ktbl_offset;;
let (ktbl_pointer : State.mem_tracker) =
  { id = Some adrp_base; offset = ktbl_offset };;

let digest_size = 512;;

let sha512_block_armv8_init_state
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
      ~stack_data_width:8
      ~stack_size:(Some (cb 64 32))
      ~stack_offset:(Some (cb 64 16))
      ~program_loc:Sha512_program.sha512_block_armv8_start_address
      ~program:Sha512_program.sha512_block_armv8_bytes
      ~pc:Sha512_program.sha512_block_armv8_start_address
      "Initial State created for sha512_block_armv8." in
  let ctx_pointer = State.make_pointer ctx_base in
  let input_pointer = State.make_pointer input_base in
  (* ktbl data is in the .rodata section. *)
  let ktbl = Cryptol.toAir2Dim Sha2.k in
  let state =
    State.add_separate_mem_region
      ~name:"ctx_region" ~aw:64 ~dw:64
      ~base_addr:ctx_base ~size:(cb 64 (digest_size / 8)) ~alignment:16
      state
  in
  let state =
    State.add_separate_mem_region
      ~name:"input_region" ~aw:64 ~dw:64
      ~base_addr:input_base
      ~size:num_bytes
      ~alignment:16
      state
  in
  let state =
    State.add_separate_mem_region
      ~name:"ktbl_region" ~aw:64 ~dw:64
      ~base_addr:adrp_base
      ~size:(cb 64 (ktbl_offset_int + ((List.length ktbl) * 8)))
      ~alignment:16
      state
  in
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
  (* 80 SHA512 constants *)
  let state = write_mem_data ((List.length ktbl) * 8) ktbl_pointer (bvapp_list ktbl) state in
  (Format.fprintf Format.std_formatter "@[%s@]@.@." message;
   state);;

(* ---------------------------------------------------------------------- *)

(* Some utility functions *)

let num_blocks_left (s : State.t) : airExp =
  let gpr2 = (State.gpr 64 2 s) in
  (assert (Option.is_none gpr2.id));
  gpr2.offset

let input_ptr (s : State.t) : State.mem_tracker =
  (State.gpr 64 1 s)

let input_offset (base_addr : airExp) (s : State.t) : airExp =
  let gpr1 = (input_ptr s) in
  (assert ((Option.get gpr1.id) = base_addr));
  gpr1.offset

let ktbl_offset (s : State.t) : airExp =
  let gpr3 = (State.gpr 64 3 s) in
  (assert (gpr3.id = ktbl_pointer.id));
  gpr3.offset

(* ---------------------------------------------------------------------- *)
