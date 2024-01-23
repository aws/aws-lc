(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* ELF shared object (.o) file reader (for testing and CI)                   *)
(* ========================================================================= *)

let rec get_int_le bs a n =
  if n = 0 then 0 else
    Char.code (Bytes.get bs a) lor (get_int_le bs (a+1) (n-1) lsl 8);;

let load_elf =
  let load_file f =
    let ic = open_in f in
    let n = in_channel_length ic in
    let s = Bytes.create n in
    really_input ic s 0 n;
    close_in ic;
    s in
  let rec get_list bs a n =
    if n = 0 then [] else Bytes.get bs a :: get_list bs (a+1) (n-1) in
  let get_int_list bs a n = map Char.code (get_list bs a n) in
  let get_string bs a =
    let rec len a n = if Bytes.get bs a = '\x00' then n else len (a+1) (n+1) in
    Bytes.sub_string bs a (len a 0) in
  fun arch reloc_type name ->
    let file = load_file name in
    if get_list file 0x0 4 <> ['\x7f'; 'E'; 'L'; 'F'] then
      failwith "not an ELF file" else
    if get_int_list file 0x4 5 <> [2; 1; 1; 0; 0]
      (* ELFCLASS64, ELFDATA2LSB, version 1, ELFOSABI_NONE *) then
      failwith "not a supported ELF filetype" else
    if get_int_le file 0x12 2 <> arch then
      failwith "unexpected ELF architecture" else
    let sections =
      let shoff = get_int_le file 0x28 8
      and shentsize = get_int_le file 0x3a 2
      and shnum = get_int_le file 0x3c 2 in
      Array.init shnum (fun i ->
        Bytes.sub file (shoff + i * shentsize) shentsize)
    and section_offset sec = get_int_le sec 0x18 8
    and section_len sec = get_int_le sec 0x20 8
    and section_link sec = get_int_le sec 0x28 4
    and check_section_type sec ty =
      if get_int_le sec 0x4 4 = ty then ()
      else failwith "unexpected section type" in
    let section_contents sec =
      Bytes.sub file (section_offset sec) (section_len sec)
    and get_string_from_sec sec_ndx =
      let off = section_offset sections.(sec_ndx) in
      fun i -> get_string file (off + i) in
    let section_name =
      let shstrndx = get_int_le file 0x3e 2 in
      if shstrndx = 0xffff then failwith "no string table" else
      get_string_from_sec shstrndx o fun sec -> get_int_le sec 0 4 in
    let find_section =
      let secs = Array.to_list sections in
      fun name ty ->
        let sec = find (fun sec -> section_name sec = name) secs in
        check_section_type sec ty; sec in
    section_contents (find_section ".text" 1 (* SHT_PROGBITS *)),
    match catch (find_section ".rela.text") 4 (* SHT_RELA *) with
    | None -> []
    | Some rel_sec ->
      let symbol =
        let symtab_sec = sections.(section_link rel_sec) in
        let symtab_off = section_offset symtab_sec in
        get_string_from_sec (section_link symtab_sec) o
        fun i -> get_int_le file (symtab_off + i * 0x18) 4 in
      let rel_pos = section_offset rel_sec in
      let rel_end = rel_pos + section_len rel_sec in
      let rec relocs off =
        if off = rel_end then [] else
        (reloc_type (get_int_le file (off + 0x8) 4),
          (get_int_le file off 8,
           symbol (get_int_le file (off + 0xc) 4),
           get_int_le file (off + 0x10) 8)) ::
        relocs (off + 0x18) in
      relocs rel_pos;;

let load_elf_contents arch = fst o load_elf arch
  (fun _ -> failwith "ELF contains relocations");;
let load_elf_contents_x86 = load_elf_contents 62 (* x86-64 *);;
let load_elf_contents_arm = load_elf_contents 183 (* ARM AARCH64 *);;

let load_elf_x86 = load_elf (62 (* x86-64 *))
  (function
  | 2 (* R_X86_64_PC32 *) -> ()
  | n -> failwith (sprintf "unexpected relocation type: %d" n));;

type arm_reloc = Arm_condbr19 | Arm_call26;;
let load_elf_arm = load_elf (183 (* ARM AARCH64 *))
  (function
  | 280 (* R_AARCH64_CONDBR19 *) -> Arm_condbr19
  | 283 (* R_AARCH64_CALL26 *) -> Arm_call26
  | n -> failwith (sprintf "unexpected relocation type: %d" n));;

let term_of_list_int,app_term_of_int_fun,term_of_int_fun =
  let word = `word:num->byte`
  and nil = `NIL:byte list`
  and cons = `CONS:byte->byte list->byte list` in
  let cons_word n e =
    mk_comb (mk_comb (cons, mk_comb (word, mk_numeral (Int n))), e) in
  let app_term_of_int_fun f start end_ =
    let rec go n e =
      if n = start then e else
      let n' = n - 1 in
      go n' (cons_word (f n') e) in
    go end_ in
  C (itlist cons_word) nil, app_term_of_int_fun,
  fun f start end_ -> app_term_of_int_fun f start end_ nil;;

let term_of_bytes bs =
  term_of_int_fun (Char.code o Bytes.get bs) 0 (Bytes.length bs);;
let term_of_array bs =
  term_of_int_fun (Array.get bs) 0 (Array.length bs);;
let array_of_bytes bs =
  Array.init (Bytes.length bs) (Char.code o Bytes.get bs);;

let term_of_relocs reloc_fn (bs,rels) =
  let rec go = function
  | [], start ->
    [], term_of_int_fun (Char.code o Bytes.get bs) start (Bytes.length bs)
  | (ty,(off,sym,(add:int)))::ls, start ->
    let sym = mk_var(sym,`:num`) in
    let n, app = reloc_fn(bs,ty,off,sym,add) in
    let args, e = go (ls, off+n) in
    insert sym args,
    app_term_of_int_fun (Char.code o Bytes.get bs) start off (app e) in
  let args, e = go (rels, 0) in
  `pc:num` :: args, e;;
