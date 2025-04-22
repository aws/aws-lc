(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ------------------------------------------------------------------------- *)
(* The iclasses to simulate.                                                 *)
(* ------------------------------------------------------------------------- *)

let iclasses =
 [(*** CCMN immediate ***)
  (*** CCMN register ***)
  "x0111010010xxxxxxxxx10xxxxx0xxxx";
  "x0111010010xxxxxxxxx00xxxxx0xxxx";

  (*** CCMP immediate ***)
  (*** CCMP register ***)
  "x1111010010xxxxxxxxx10xxxxx0xxxx";
  "x1111010010xxxxxxxxx00xxxxx0xxxx";

  (*** ADC, ADCS, SBC, SBCS with register-register operands ***)
  "xxx11010000xxxxx000000xxxxxxxxxx";

  (*** ADD, ADDS, SUB, SUBS with immediate operand ***)

  (*** We want to avoid any use of SP since our crude simulation
   *** framework doesn't work in such cases. While it misses a
   *** bit of the state space, we force both registers to have
   *** zero bits in their encoding.
   ***)
  "xx0100010xxxxxxxxxxxxxxxxx0xxxx0";
  "xx0100010xxxxxxxxxxxxxxxx0xxxx0x";
  "xx0100010xxxxxxxxxxxxxxx0xxxx0xx";
  "xx0100010xxxxxxxxxxxxxx0xxxx0xxx";
  "xx0100010xxxxxxxxxxxxx0xxxx0xxxx";
  "10010001000000001000001100110110"; (* unmatched case... *)
  "1001000100xxxxxxxxxxxx1110100010"; (* another: add x2, x29, #xxx *)
  (*** Rd of ADDS/SUBS cannot be SP *)
  "xx1100010xxxxxxxxxxxxxxxxx0xxxxx";
  "xx1100010xxxxxxxxxxxxxxxx0xxxxxx";
  "xx1100010xxxxxxxxxxxxxxx0xxxxxxx";
  "xx1100010xxxxxxxxxxxxxx0xxxxxxxx";
  "xx1100010xxxxxxxxxxxxx0xxxxxxxxx";

  (*** ADD, ADDS, SUB, SUBS, shifted registers ***)
  "xxx01011xx0xxxxxxxxxxxxxxxxxxxxx";

  (*** ADD, extended registers. No SP registers ***)
  "10001011001xxxxx010000xxxx0xxxx0"; (* uxtw *)
  "10001011001xxxxx010000xxx0xxxx0x"; (* uxtw *)
  "10001011001xxxxx010000xx0xxxx0xx"; (* uxtw *)
  "10001011001xxxxx010000x0xxxx0xxx"; (* uxtw *)
  "10001011001xxxxx0100000xxxx0xxxx"; (* uxtw *)

  (*** AND, ANDS, EOR, ORR with immediate operand, no negated forms ***)
  (*** Again we want to avoid using SP except for in ANDS ***)

  "x00100100xxxxxxxxxxxxxxxxxxxxxx0";
  "x00100100xxxxxxxxxxxxxxxxxxxxx0x";
  "x00100100xxxxxxxxxxxxxxxxxxxx0xx";
  "x00100100xxxxxxxxxxxxxxxxxxx0xxx";
  "x00100100xxxxxxxxxxxxxxxxxx0xxxx";

  "x01100100xxxxxxxxxxxxxxxxxxxxxx0";
  "x01100100xxxxxxxxxxxxxxxxxxxxx0x";
  "x01100100xxxxxxxxxxxxxxxxxxxx0xx";
  "x01100100xxxxxxxxxxxxxxxxxxx0xxx";
  "x01100100xxxxxxxxxxxxxxxxxx0xxxx";

  "x10100100xxxxxxxxxxxxxxxxxx0xxxx";
  "x10100100xxxxxxxxxxxxxxxxxxxxxx0";
  "x11100100xxxxxxxxxxxxxxxxxxxxxxx";

  (*** BFM ***)
  "x01100110xxxxxxxxxxxxxxxxxxxxxxx";

  (*** CSEL, CSINC, CSINV, CSNEG register-register ***)
  "xx011010100xxxxxxxxx0xxxxxxxxxxx";

  (*** AND, BIC, ..., ORN, shifted registers ***)
  "xxx01010xxxxxxxxxxxxxxxxxxxxxxxx";

  (*** MOVN, MOVZ, MOVK ***)
  "xxx100101xxxxxxxxxxxxxxxxxxxxxxx";

  (*** Extr ***)
  "x00100111x0xxxxxxxxxxxxxxxxxxxxx";

  (*** LSLV, LSRV ***)
  "x0011010110xxxxx0010xxxxxxxxxxxx";

  (*** UBFM, SBFM ***)
  "xx0100110xxxxxxxxxxxxxxxxxxxxxxx";

  (*** CLZ ***)
  "x101101011000000000100xxxxxxxxxx";

  (*** MADD, MSUB ***)
  "x0011011000xxxxxxxxxxxxxxxxxxxxx";

  (*** UMULH ***)
  "10011011110xxxxx011111xxxxxxxxxx";

  (*** SMULH ***)
  "10011011010xxxxx011111xxxxxxxxxx";

  (*** UMADDL, UMSUBL ***)
  "10011011101xxxxxxxxxxxxxxxxxxxxx";

  (****** NEON INSTRUCTIONS *****)
  (*** ADD ***)
  "0x001110xx1xxxxx100001xxxxxxxxxx";

  (*** AND ***)
  "0x001110001xxxxx000111xxxxxxxxxx";

  (*** BIC (vector registers) ***)
  "0x001110011xxxxx000111xxxxxxxxxx";

  (*** BIC (vector immediate, 8h) ***)
  "0x10111100000xxx10x101xxxxxxxxxx"; (* 8h, cmode=10x1 *)

  (*** BIT ***)
  "0x101110101xxxxx000111xxxxxxxxxx";

  (*** CMHI, vector ***)
  "0x101110xx1xxxxx001101xxxxxxxxxx";

  (*** CNT, bias to defined size = 0 ***)
  "0x00111000100000010110xxxxxxxxxx";
  "0x001110xx100000010110xxxxxxxxxx";

  (*** DUP ***)
  "01001110000x1000000011xxxxxxxxxx"; (* original DUP Vd.2d, xn *)
  "0x001110000xxxxx000011xxxxxxxxxx"; (* other variants too     *)

  (*** EOR ***)
  "0x101110001xxxxx000111xxxxxxxxxx";

  (*** EXT ***)
  "01101110000xxxxx0xxxx0xxxxxxxxxx"; (* 128 bits only *)

  (*** FCSEL, 32 and 64 bits ***)
  "00011110001xxxxxxxxx11xxxxxxxxxx";
  "00011110011xxxxxxxxx11xxxxxxxxxx";

  (*** FMOV, double precision ***)
  "100111101010111x000000xxxxxxxxxx";
  "100111100110011x000000xxxxxxxxxx";

  (*** FMOV to general, single ***)
  "0001111000100110000000xxxxxxxxxx";

  (*** INS, or MOV (element) ***)
  "01101110000xxxx10xxxx1xxxxxxxxxx";
  "01101110000xxx100xxxx1xxxxxxxxxx";
  "01101110000xx1000xxxx1xxxxxxxxxx";
  "01101110000x10000xxxx1xxxxxxxxxx";
  "01101110000x00000xxxx1xxxxxxxxxx";

  (*** INS (general, i.e. GPR -> VEC) ***)
  "01001110000xxxx1000111xxxxxxxxxx";
  "01001110000xxx10000111xxxxxxxxxx";
  "01001110000xx100000111xxxxxxxxxx";
  "01001110000x1000000111xxxxxxxxxx";
  "01001110000x0000000111xxxxxxxxxx";

  (*** MLS (by element; focus on defined sizes) ***)
  "0x10111101xxxxxx0100x0xxxxxxxxxx";
  "0x10111110xxxxxx0100x0xxxxxxxxxx";
  "0x101111xxxxxxxx0100x0xxxxxxxxxx";

  (*** MLS (vector) ***)
  "0x101110xx1xxxxx100101xxxxxxxxxx";

  (*** MOVI ***)
  "0110111100000xxx111001xxxxxxxxxx"; (* q=1, cmode=1110 *)

  (*** MUL (by element; focus on defined sizes) ***)
  "0x00111101xxxxxx1000x0xxxxxxxxxx";
  "0x00111110xxxxxx1000x0xxxxxxxxxx";
  "0x001111xxxxxxxx1000x0xxxxxxxxxx";

  (*** MUL (vector) ***)
  "0x001110xx1xxxxx100111xxxxxxxxxx";

  (*** NOP ***)
  "11010101000000110010000000011111";

  (*** ORR ***)
  "0x001110101xxxxx000111xxxxxxxxxx";

  (*** REV64 ***)
  "01001110xx100000000010xxxxxxxxxx";

  (*** SHA256 Intrinsics ***)
  (*** SHA256H ***)
  "01011110000xxxxx010000xxxxxxxxxx";

  (*** SHA256H2 ***)
  "01011110000xxxxx010100xxxxxxxxxx";

  (*** SHA256SU0 ***)
  "0101111000101000001010xxxxxxxxxx";

  (*** SHA256SU1 ***)
  "01011110000xxxxx011000xxxxxxxxxx";

  (*** SHA512H ***)
  "11001110011xxxxx100000xxxxxxxxxx";

  (*** SHA512H2 ***)
  "11001110011xxxxx100001xxxxxxxxxx";

  (*** SHA512SU0 ***)
  "1100111011000000100000xxxxxxxxxx";

  (*** SHA512SU1 ***)
  "11001110011xxxxx100010xxxxxxxxxx";

  (*** SHL (make sure immh is nonzero) ***)
  "0x00111101xxxxxx010101xxxxxxxxxx";
  "0x001111001xxxxx010101xxxxxxxxxx";
  "0x0011110001xxxx010101xxxxxxxxxx";
  "0x00111100001xxx010101xxxxxxxxxx";

  (*** SHRN ***)
  "00001111001xxxxx100001xxxxxxxxxx"; (* q=0, immh!=0 *)
  "000011110001xxxx100001xxxxxxxxxx"; (* q=0, immh!=0 *)
  "0000111100001xxx100001xxxxxxxxxx"; (* q=0, immh!=0 *)

  (*** SMLAL ***)
  "00001110xx1xxxxx100000xxxxxxxxxx";

  (*** SMLAL2 ***)
  "01001110xx1xxxxx100000xxxxxxxxxx";

  (*** SMLSL ***)
  "00001110xx1xxxxx101000xxxxxxxxxx";

  (*** SMLSL2 ***)
  "01001110xx1xxxxx101000xxxxxxxxxx";

  (*** SMULL ***)
  "00001110xx1xxxxx110000xxxxxxxxxx";

  (*** SMULL2 ***)
  "01001110xx1xxxxx110000xxxxxxxxxx";

  (*** SQDMULH ***)
  "0x001111xxxxxxxx1100x0xxxxxxxxxx";

  (*** SQDMULH (vector) ***)
  "0x001110xx1xxxxx101101xxxxxxxxxx";

  (*** SQRDMULH (by element) ***)
  "0x001111xxxxxxxx1101x0xxxxxxxxxx";

  (*** SQRDMULH (vector) ***)
  "0x101110xx1xxxxx101101xxxxxxxxxx";

  (*** SRSHR (make sure immh is nonzero) ***)
  "0x00111101xxxxxx001001xxxxxxxxxx";
  "0x001111001xxxxx001001xxxxxxxxxx";
  "0x0011110001xxxx001001xxxxxxxxxx";
  "0x00111100001xxx001001xxxxxxxxxx";

  (*** SSHR (make sure immh is nonzero) ***)
  "0x00111101xxxxxx000001xxxxxxxxxx";
  "0x001111001xxxxx000001xxxxxxxxxx";
  "0x0011110001xxxx000001xxxxxxxxxx";
  "0x00111100001xxx000001xxxxxxxxxx";

  (*** SLI (vector) ***)
  "0x10111101xxxxxx010101xxxxxxxxxx"; (* immh!=0 *)
  "0x101111001xxxxx010101xxxxxxxxxx"; (* immh!=0 *)
  "0x1011110001xxxx010101xxxxxxxxxx"; (* immh!=0 *)
  "0x10111100001xxx010101xxxxxxxxxx"; (* immh!=0 *)

  (*** SRI (vector) ***)
  "0x10111101xxxxxx010001xxxxxxxxxx"; (* immh!=0 *)
  "0x101111001xxxxx010001xxxxxxxxxx"; (* immh!=0 *)
  "0x1011110001xxxx010001xxxxxxxxxx"; (* immh!=0 *)
  "0x10111100001xxx010001xxxxxxxxxx"; (* immh!=0 *)

  (*** SUB ***)
  "0x101110xx1xxxxx100001xxxxxxxxxx";

  (*** TBL ***)
  "0x001110000xxxxx000000xxxxxxxxxx";

  (*** TRN1 and TRN2 ***)
  "0x001110xx0xxxxx0x1010xxxxxxxxxx";

  (*** UADDLP ***)
  "01101110xx100000001010xxxxxxxxxx";

  (*** UADDLV ***)
  "0x101110xx110000001110xxxxxxxxxx";

  (*** UMOV (.d, .s) ***)
  "01001110000x1000001111xxxxxxxxxx";
  "00001110000xx100001111xxxxxxxxxx";

  (*** UMADDL, UMSUBL ***)
  "10011011101xxxxxxxxxxxxxxxxxxxxx";

  (*** UMLAL ***)
  "00101110xx1xxxxx100000xxxxxxxxxx";

  (*** UMLAL2 ***)
  "01101110xx1xxxxx100000xxxxxxxxxx";

  (*** UMLSL ***)
  "00101110xx1xxxxx101000xxxxxxxxxx";

  (*** UMLSL2 ***)
  "01101110xx1xxxxx101000xxxxxxxxxx";

  (*** UMULL ***)
  "00101110xx1xxxxx110000xxxxxxxxxx";

  (*** UMULL2 ***)
  "01101110xx1xxxxx110000xxxxxxxxxx";

  (*** USHR (make sure immh is nonzero) ***)
  "0x10111101xxxxxx000001xxxxxxxxxx";
  "0x101111001xxxxx000001xxxxxxxxxx";
  "0x1011110001xxxx000001xxxxxxxxxx";
  "0x10111100001xxx000001xxxxxxxxxx";

  (*** USRA ***)
  "0110111101xxxxxx000101xxxxxxxxxx"; (* q=1 *)
  "01101111001xxxxx000101xxxxxxxxxx"; (* q=1 *)
  "011011110001xxxx000101xxxxxxxxxx"; (* q=1 *)
  "0110111100001xxx000101xxxxxxxxxx"; (* q=1 *)
  "00101111001xxxxx000101xxxxxxxxxx"; (* q=0 *)
  "001011110001xxxx000101xxxxxxxxxx"; (* q=0 *)
  "0010111100001xxx000101xxxxxxxxxx"; (* q=0 *)

  (*** UZP1 ***)
  "01001110xx0xxxxx000110xxxxxxxxxx";

  (*** UZP2 ***)
  "01001110xx0xxxxx010110xxxxxxxxxx";

  (*** XTN ***)
  "00001110xx100001001010xxxxxxxxxx";

  (*** ZIP1 ***)
  "0x001110xx0xxxxx001110xxxxxxxxxx";

  (*** ZIP2 ***)
  "0x001110xx0xxxxx011110xxxxxxxxxx";

  (*** EOR3 ***)
  "11001110000xxxxx0xxxxxxxxxxxxxxx";


  (*** BCAX ***)
  "11001110001xxxxx0xxxxxxxxxxxxxxx";

  (*** RAX1 ***)
  "11001110011xxxxx100011xxxxxxxxxx";

  (*** XAR ***)
  "11001110100xxxxxxxxxxxxxxxxxxxxx";

  (*** AESE ***)
  "0100111000101000010010xxxxxxxxxx";

  (*** AESMC ***)
  "0100111000101000011010xxxxxxxxxx";

  (*** AESD ***)
  "0100111000101000010110xxxxxxxxxx";

  (*** AESIMC ***)
  "0100111000101000011110xxxxxxxxxx";
];;


let match_bitpattern =
  let idxs = List.init 32 (fun x->x) in
  fun (opcode:int) (bitpat:string) ->
    List.for_all (fun i ->
        let bitpat = bitpat.[31 - i] and
            bit = (opcode lsr i) land 1 in
        bitpat = 'x' ||
        (bit = 1 && bitpat = '1') ||
        (bit = 0 && bitpat = '0'))
      idxs;;

(* Check that assembly instructions in s2n-bignum object files appear at
   iclasses. *)

let check_insns () =
  (* These commands are not going to be simulated. *)
  let skipping_iclasses = [
    (*** adr ***)
    "0xx10000xxxxxxxxxxxxxxxxxxxxxxxx";

    (*** b ***)
    "000101xxxxxxxxxxxxxxxxxxxxxxxxxx";

    (*** bl ***)
    "100101xxxxxxxxxxxxxxxxxxxxxxxxxx";

    (*** b.cond ***)
    "01010100xxxxxxxxxxxxxxxxxxx0xxxx";

    (*** cbz, cbnz ***)
    "10110100xxxxxxxxxxxxxxxxxxxxxxxx";
    "10110101xxxxxxxxxxxxxxxxxxxxxxxx";

    (*** ldp ***)
    "x010100x1xxxxxxxxxxxxxxxxxxxxxxx"; (* Preimmediate_Offset or Postimmediate_Offset *)
    "x01010010xxxxxxxxxxxxxxxxxxxxxxx"; (* Immediate_Offset *)

    (*** ldp (SIMD & FP) ***)
    "xx10110011xxxxxxxxxxxxxxxxxxxxxx";
    "xx10110111xxxxxxxxxxxxxxxxxxxxxx";
    "xx10110101xxxxxxxxxxxxxxxxxxxxxx";

    (*** ldr (immediate ofs) ***)
    "1x111000010xxxxxxxxx01xxxxxxxxxx";
    "1x111000010xxxxxxxxx11xxxxxxxxxx";
    "1x11100101xxxxxxxxxxxxxxxxxxxxxx";

    (*** ldr (immediate ofs, SIMD & FP) ***)
    "xx111100x10xxxxxxxxx01xxxxxxxxxx";
    "xx111100x10xxxxxxxxx11xxxxxxxxxx";
    "xx111101x1xxxxxxxxxxxxxxxxxxxxxx";

    (*** ldr (register ofs) ***)
    "1x111000011xxxxxxxxx10xxxxxxxxxx";

    (*** ldrb (immediate ofs) ***)
    "00111000010xxxxxxxxx01xxxxxxxxxx";
    "00111000010xxxxxxxxx11xxxxxxxxxx";
    "0011100101xxxxxxxxxxxxxxxxxxxxxx";

    (*** ld1 (1 register, Post-immediate offset) ***)
    "0x001100110111110111xxxxxxxxxxxx";

    (*** st1 (1 register, Post-immediate offset) ***)
    "0x001100100111110111xxxxxxxxxxxx";

    (*** ld1 (1 register, Post-register offset) ***)
    "0x001100110xxxxx0111xxxxxxxxxxxx";

    (*** st1 (1 register, Post-register offset) ***)
    "0x001100100xxxxx0111xxxxxxxxxxxx";

    (*** ld1 (1 register, no Post-immediate offset) ***)
    "0x001100010000000111xxxxxxxxxxxx";

    (*** st1 (1 register, no Post-immediate offset) ***)
    "0x001100000000000111xxxxxxxxxxxx";

    (*** ld1 (2 registers, Post-immediate offset) 128-bit ***)
    "01001100110111111010xxxxxxxxxxxx";

    (*** st1 (2 registers, Post-immediate offset) 128-bit ***)
    "01001100100111111010xxxxxxxxxxxx";

    (*** ld2 (2 register, Post-immediate offset) ***)
    "0x001100110111111000xxxxxxxxxxxx";

    (*** st2 (2 register, Post-immediate offset) ***)
    "0x001100100111111000xxxxxxxxxxxx";

    (*** ld1r (post immediate ofs) ***)
    "0x001101110111111100xxxxxxxxxxxx";

    (*** stp ***)
    "x010100010xxxxxxxxxxxxxxxxxxxxxx";
    "x010100110xxxxxxxxxxxxxxxxxxxxxx";
    "x010100100xxxxxxxxxxxxxxxxxxxxxx";

    (*** stp (SIMD & FP) ***)
    "xx10110010xxxxxxxxxxxxxxxxxxxxxx";
    "xx10110110xxxxxxxxxxxxxxxxxxxxxx";
    "xx10110100xxxxxxxxxxxxxxxxxxxxxx";

    (*** str (immediate ofs) ***)
    "1x111000000xxxxxxxxx01xxxxxxxxxx";
    "1x111000000xxxxxxxxx11xxxxxxxxxx";
    "1x11100100xxxxxxxxxxxxxxxxxxxxxx";

    (*** str (immediate ofs, SIMD & FP) ***)
    "xx111100x00xxxxxxxxx01xxxxxxxxxx";
    "xx111100x00xxxxxxxxx11xxxxxxxxxx";
    "xx111101x0xxxxxxxxxxxxxxxxxxxxxx";

    (*** str (register) ***)
    "1x111000001xxxxxxxxx10xxxxxxxxxx";

    (*** strb (immediate ofs) ***)
    "00111000000xxxxxxxxx01xxxxxxxxxx";
    "00111000000xxxxxxxxx11xxxxxxxxxx";
    "0011100100xxxxxxxxxxxxxxxxxxxxxx";

    (*** sub/add with sp regs ***)
    "xx0100010xxxxxxxxxxxxxxxxxx11111";
    "xx0100010xxxxxxxxxxxxx11111xxxxx";
    "11001011001xxxxxxxxxxx11111xxxxx";

    (*** ret ***)
    "1101011001011111000000xxxxx00000";
  ] in

  (* Check that iclasses and skipping_iclasses has no overlapping bitpattern. *)
  if let char_overlap c1 c2 = c1 = c2 || c1 = 'x' || c2 = 'x' in
      List.exists (fun bitpat1 ->
        List.exists (fun bitpat2 ->
            let range = List.init 32 (fun x->x) in
            if List.for_all (fun i -> char_overlap bitpat1.[i] bitpat2.[i]) range
            then begin
              Printf.eprintf "iclasses and skipping_iclasses overlap!!\n";
              Printf.eprintf "- iclass entry: %s\n" bitpat1;
              Printf.eprintf "- skipping_iclasses entry: %s\n%!" bitpat2;
              true
            end else false)
          skipping_iclasses)
        iclasses
  then failwith "check_insns" else

  let rec traverse_objs dirpath (checkfn:string->unit):unit =
    let dirs = Sys.readdir dirpath in
    Array.iter (fun p ->
        let p = (Filename.concat dirpath p) in
        if Sys.is_directory p then
          traverse_objs p checkfn
        else if Filename.extension p = ".o" && p <> "arm/proofs/simulator.o" then
          checkfn p
        else ()
      ) dirs in

  (* Check whether l (a line of objdump output) is an assembly instruction
     covered by iclasses. *)
  let check_asmline (l:string):bool =
    match String.index_opt l ':' with
    | None -> true
    | Some idx ->
      let l = String.sub l (idx+1) (String.length l - idx - 1) in
      let l = String.trim l in
      match String.index_opt l ' ' with
      | None -> true (* defines label *)
      | Some idx ->
        let hexcode = "0x" ^ (String.sub l 0 idx) in
        let desc = String.trim (String.sub l (idx+1) (String.length l - idx - 1)) in
        if String.starts_with ~prefix:".word" desc then true (* defines a constant *)
        else
          try
            let opcode = int_of_string hexcode in
            if List.exists (match_bitpattern opcode) skipping_iclasses then
              true (* Check passes *)
            else
              List.exists (match_bitpattern opcode) iclasses
          with _ -> false
    in

  let tmppath = Filename.temp_file "objdump" ".txt" in
  let checkfn objpath =
    let cmd = "objdump -d \"" ^ objpath ^ "\" -j .text >" ^ tmppath in
    let exitcode = Sys.command cmd in
    if exitcode <> 0 then begin
      Printf.eprintf "Cannot objdump %s\n%!" objpath;
      failwith "check_insns"
    end else
      (* Read the lines of objdump *)
      let fin = open_in tmppath in
      try
        (* Pass first 6 lines *)
        let count = ref 0 in
        while true; do
          let l = input_line fin in
          count := !count + 1;
          if !count >= 6 then
            if not (check_asmline l) then begin
              Printf.eprintf "Found an assembly that is not covered by iclasses!\n";
              Printf.eprintf "  File: %s\n" objpath;
              Printf.eprintf "  objdump line: %s\n%!" l;
              failwith "check_insns"
            end
        done;
      with End_of_file -> begin
        Printf.printf "Passed: %s\n%!" objpath;
        close_in fin
      end in
  (* Makefile will run this script from the root dir of s2n-bignum/. *)
  traverse_objs "arm/" checkfn;;
