(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* ELF and Mach-O object (.o) file reader                                    *)
(* ========================================================================= *)

(*** get int from bs[a:a+n-1] (little-endian). Fail if the resulting
     integer is too large to fit in OCaml int type (63 bits) ***)
let get_int_le (bs:bytes) a n =
  if n > 8 then failwith "get_int_le: n too big" else
  if n = 8 && Char.code (Bytes.get bs 7) >= 128
  then failwith "get_int_le: does not fit in OCaml int (63 bits)" else
  let rec fn a n =
    if n = 0 then 0 else
    Char.code (Bytes.get bs a) lor (fn (a+1) (n-1) lsl 8)
  in fn a n;;

(*** load the whole file at path f ***)
let load_file (f:string): bytes =
  let ic = open_in f in
  let n = in_channel_length ic in
  let s = Bytes.create n in
  really_input ic s 0 n;
  close_in ic;
  s;;

let rec get_list bs a n: char list =
  if n = 0 then [] else Bytes.get bs a :: get_list bs (a+1) (n-1);;

let get_int_list bs a n: int list = map Char.code (get_list bs a n);;

let get_string bs (a:int): string =
  let rec len a n = if Bytes.get bs a = '\x00' then n else len (a+1) (n+1) in
  Bytes.sub_string bs a (len a 0);;


(*** load_elf reads an object file, and returns
      (the ".text" section bytes, relocations info)
***)
let is_elf (file:bytes) = get_list file 0x0 4 = ['\x7f'; 'E'; 'L'; 'F'];;

let load_elf (arch:int) (reloc_type:int -> 'a) (file:bytes):
      bytes * (* .text *)
      (string * bytes) list * (* read-only data list *)
      ('a * (int * string * int)) list (* relocation info *)
  =

  if not (is_elf file) then failwith "not an ELF file" else

  if get_int_list file 0x4 5 <> [2; 1; 1; 0; 0]
    (* ELFCLASS64, ELFDATA2LSB, version 1, ELFOSABI_NONE *) then
    failwith "not a supported ELF filetype" else
  if get_int_le file 0x12 2 <> arch then
    failwith "unexpected ELF architecture" else

  (* Read the ELF header (first 64 bytes of the file) to get section headers *)
  let section_headers: bytes array =
    (* section header's offset; e_shoff *)
    let shoff = get_int_le file 0x28 8
    (* size of a single section header; e_shentsize*)
    and shentsize = get_int_le file 0x3a 2
    (* count of section headers = e_shnum *)
    and shnum = get_int_le file 0x3c 2 in
    Array.init shnum (fun i ->
      Bytes.sub file (shoff + i * shentsize) shentsize)

  (* Helper fns to read a section header.
     Corresponds to the Elf64_Shdr struct.
     Note that Elf64_Word is a 4-byte int, Elf64_Addr is 8 bytes, and
     Elf64_Xword is also 8 bytes. *)
  and section_offset sec_header = get_int_le sec_header 0x18 8
  and section_len sec_header = get_int_le sec_header 0x20 8
  and section_link sec_header = get_int_le sec_header 0x28 4
  and check_section_type sec_header ty =
    if get_int_le sec_header 0x4 4 = ty then ()
    else failwith "unexpected section type" in
  (* Get the section contents of a section header *)
  let section_contents sec_header =
    Bytes.sub file (section_offset sec_header) (section_len sec_header)
  and get_string_from_table sec_ndx =
    let off = section_offset section_headers.(sec_ndx) in
    fun i -> get_string file (off + i) in
  let from_section_string_table =
    let shstrndx = get_int_le file 0x3e 2 in
    if shstrndx = 0xffff then failwith "no string table" else
    fun entry_idx -> get_string_from_table shstrndx entry_idx in
  let section_name sec_header =
    from_section_string_table (get_int_le sec_header 0 4) in

  (* Find a section header from section header table *)
  let find_section_header =
    let secs = Array.to_list section_headers in
    (* ty stands for the type of a section. Figure 4-9 of
       https://refspecs.linuxbase.org/elf/gabi4+/ch4.sheader.html
       has a table for their integer values, and  Figure 4-14
       has types for special sections such as .text . *)
    fun name ty ->
      let sec = find (fun sec -> section_name sec = name) secs in
      check_section_type sec ty; sec in

  let from_symbol_string_table =
    try let the_table = section_contents
        (find_section_header ".strtab" 3 (* SHT_STRTAB *)) in
      fun stridx -> get_string the_table stridx
    with _ -> fun (stridx:int) -> "" in

  (* The ".text" section contents. *)
  section_contents (find_section_header ".text" 1 (* SHT_PROGBITS *)),

  (* Get the read-only data from ".rodata" section by searching
    the symbol table (".symtab"). *)
  (let find_section_contents (name,ty) =
      section_contents (find_section_header name ty) in
   (* The .rodata section *)
    let rodata = catch find_section_contents (".rodata",1 (* SHT_PROGBITS *))
    (* The symbol table.
       https://refspecs.linuxbase.org/elf/gabi4+/ch4.symtab.html *)
    and symtab = catch find_section_contents (".symtab",2 (* SHT_SYMTAB *)) in
    match (rodata,symtab) with
    | Some rodata, Some symtab -> begin
      let sym_entrysize = 24 (* size of Elf64_Sym struct *) in

      (* Skim through the symbol table entries and collect readonly
         entries *)
      let rodata_entries = ref [] in
      for i = 0 to (Bytes.length symtab) / sym_entrysize - 1 do
        let symtab_entry = Bytes.sub symtab (i * sym_entrysize) sym_entrysize in
        (* The "st_shndx" field *)
        let symbol_sectionidx = get_int_le symtab_entry 6 2 in
        (* Least-significant 4 bits of the "st_info" field *)
        let symbol_type =
          let symbol_info = get_int_le symtab_entry 4 1 in
          symbol_info land 0xf in
        if symbol_type = 1 (* 1 = STT_OBJECT: a data object, such as a variable,
              an array, and so on. *) &&
            section_name (section_headers.(symbol_sectionidx)) = ".rodata"
        then (* Found a .rodata entry *)
          let symbol_name =
            let char_index = get_int_le symtab_entry 0 4 in
            from_symbol_string_table char_index in
          let symbol_size = get_int_le symtab_entry 16 8 in
          let symbol_addr = get_int_le symtab_entry 8 8 in
          let data = Bytes.sub rodata symbol_addr symbol_size in
          rodata_entries := (symbol_name, data)::!rodata_entries
        else
          ()
      done;
      !rodata_entries
      end
    | _ -> []),

  (* Relocation info *)
  match catch (find_section_header ".rela.text") 4 (* SHT_RELA *) with
  | None -> []
  | Some rel_sec ->
    let symbol =
      let symtab_sec = section_headers.(section_link rel_sec) in
      let symtab_off = section_offset symtab_sec in
      get_string_from_table (section_link symtab_sec) o
      fun i -> get_int_le file (symtab_off + i * 0x18) 4 in
    let rel_pos = section_offset rel_sec in
    let rel_end = rel_pos + section_len rel_sec in
    let rec relocs off =
      if off = rel_end then [] else
      ((* The relocation type; ELF64_R_TYPE *)
       reloc_type (get_int_le file (off + 0x8) 4),
        ((* r_offset *)
          get_int_le file off 8,
          (* The symbol name (string) *)
          symbol (get_int_le file (off + 0xc) 4),
          (* r_addend. Assume that this value is *)
          get_int_le file (off + 0x10) 8)) ::
      relocs (off + 0x18) in
    relocs rel_pos;;

let load_elf_code arch file =
  let code,_,_ = load_elf arch
    (fun _ -> failwith "ELF contains relocations") file in
  code;;


(*** load_macho reads an object file, and returns the "__text" section bytes
    Reference: OS X ABI Mach-O File Format Reference
***)

let is_macho (file:bytes) =
  get_list file 0x0 4 = ['\207'; '\250'; '\237'; '\254'];;

let load_macho (cputype:int) (reloc_type:int -> 'a) (file:bytes):
    bytes * (* __text *)
    (string * bytes) list (* read-only data list *) *
    ('a * (int * string * int)) list (* relocation info *) =

  (* The magic number (64-bit). *)
  if not (is_macho file) then failwith "not a Mach-O file" else

  (* CPU type. 0x00000007 for x86, 0x0000000C for ARM. 0x01000000 bit
     set if 64-bit *)
  if get_int_le file 0x4 4 <> cputype then
    failwith "unexpected CPU type" else

  (* Get the Mach-O header. It is 32 bytes. *)
  (* Throw away CPU subtype and flags *)
  let num_load_commands = get_int_le file 16 4 and
      size_load_commands = get_int_le file 20 4 and
      filetype = get_int_le file 12 4 in
  if filetype <> 0x00000001 then failwith "Not a relocatable object file" else

  (* Now, read the following load commands *)
  let curr_file_offset = ref 0x20 in
  let sections = ref [] in (* a list of (section name, begin ofs, len) *)
  (* a list of struct nlist_64:
     (symbol name(string), n_type, n_sect, n_desc) *)
  let raw_symbols = ref [] in
  (* a list of struct relocation_info:
     (section idx, r_address, r_data, r_symbolnum, r_pcrel, r_length, r_extern, r_type) list. *)
  let raw_reloc_entries = ref [] in

  for i = 0 to num_load_commands - 1 do
    let cmd_type = get_int_le file !curr_file_offset 4 and
        cmd_size = get_int_le file (4 + !curr_file_offset) 4 in
    let next_file_offset = cmd_size + !curr_file_offset in

    (begin match cmd_type with
    | 0x00000019 -> begin (* Segment load (64 bit) *)
      (* Command name: LC_SEGMENT_64
         C struct: segment_command_64 *)

      (* Read the following struct section_64[]. *)
      let num_sections = get_int_le file (64 + !curr_file_offset) 4 in
      (* each section info consumes 80 bytes *)

      for j = 0 to num_sections - 1 do
        let ofs = 72(*size of load command *) + 80(*size of section info*) * j +
                  !curr_file_offset in
        let section_name = get_string file ofs in
        let file_offset = get_int_le file (48 + ofs) 4 in
        let section_size = get_int_le file (40 + ofs) 8 in
        sections := !sections @ [(section_name,file_offset,section_size)];

        (* Read struct relocation_info[]. *)
        (* file offset and count of relocation entries *)
        let reloc_ofs = get_int_le file (56 + ofs) 4 in
        let num_reloc_entries = get_int_le file (60 + ofs) 4 in
        for k = 0 to num_reloc_entries - 1 do
          let ofs = reloc_ofs + k * 8 in
          let r_address = get_int_le file (ofs) 4 in
          let r_data = get_int_le file (4 + ofs) 4 in
          let r_symbolnum = r_data land 0xFFFFFF in
          let r_pcrel = (r_data lsr 24) land 1 in
          let r_length = (r_data lsr 25) land 2 in
          let r_extern = (r_data lsr 27) land 1 in
          let r_type = (r_data lsr 28) in

          raw_reloc_entries := !raw_reloc_entries @
              [length !sections - 1, r_address, r_data, r_symbolnum, r_pcrel, r_length, r_extern, r_type]
        done
      done
      end
    | 0x00000032 -> begin (* Minimum OS version *)
      end
    | 0x00000002 -> begin (* __LINKEDIT Symbol table *)
      (* Command name: LC_SYMTAB
         C struct: symtab_command *)
      let nlist_ofs = get_int_le file (8 + !curr_file_offset) 4 in
      let num_symbols = get_int_le file (12 + !curr_file_offset) 4 in
      let string_table_ofs = get_int_le file (16 + !curr_file_offset) 4 in
      let string_table_sz = get_int_le file (20 + !curr_file_offset) 4 in

      (* Iterate each symbol table entry *)
      for j = 0 to num_symbols - 1 do
        (* struct nlist_64 *)
        let nlist_j = nlist_ofs + 16 * j in
        let strtable_idx = get_int_le file nlist_j 4 in
        let symbol_name = get_string file (string_table_ofs + strtable_idx) in
        let n_type = get_int_le file (4 + nlist_j) 1 in
        let n_sect = get_int_le file (5 + nlist_j) 1 in
        let n_desc = get_int_le file (6 + nlist_j) 2 in
        let n_value = get_int_le file (8 + nlist_j) 8 in

        raw_symbols := !raw_symbols @ [symbol_name, n_type, n_sect, n_desc, n_value]
      done
      end
    | 0x0000000b -> begin (* __LINKEDIT Symbol table information *)
      end
    | _ -> failwith ("Unknown load command: " ^ (string_of_int cmd_type) ^
            " (file byte offset: " ^ (string_of_int !curr_file_offset) ^ ")")
    end;
    curr_file_offset := next_file_offset)
  done;

  (* Get the readonly symbols from raw_symbols. *)
  let const_symbols = ref [] (* symbol name, byte offset *) in
  List.iter (fun symbol_name, n_type, n_sect, n_desc, n_value ->
    if n_type = 0xe (* N_SECT: The symbol is defined in a section at n_sect *) &&
      n_sect != 0 && (n_sect - 1) < List.length !sections &&
      (let secname,_,_ = List.nth !sections (n_sect - 1) in secname = "__const") &&
      (* Some symbols starting with "ltmp" are auto-generated. They are ignored by
        tools like:
        https://github.com/microsoft/llvm-mctoll/blob/master/MachODump.cpp#L228 *)
      not (String.starts_with ~prefix:"ltmp" symbol_name)
    then begin
      const_symbols := !const_symbols @ [(symbol_name, n_value(*byte offset *))]
    end) !raw_symbols;

  (* Sort the readonly symbols by their addresses.
     This is to 'infer' the sizes of each symbol. Mach-O symbol table does not
     have symbol sizes. *)
  const_symbols := sort (fun (_,addr1) (_,addr2) -> addr1 < addr2)
      !const_symbols;

  (* Now get the final results *)
  (* Helper functions *)
  let find_section (name:string): int * bytes =
    let res = find (fun section_name,_,_ -> section_name = name) !sections in
    match res with
    | _,beginofs,len -> (beginofs,Bytes.sub file beginofs len)
    | _ -> failwith ("Could not find a unique \"" ^ name ^ "\" section") in
  let rec extract_bytes (start_ofs:int) (end_ofs: int option) sections: bytes =
    match sections with
    | [] -> failwith "no available section"
    | s::sections' ->
      let symname,secofs,seclen = s in
      if start_ofs < seclen then
        let symbol_len = if end_ofs <> None
          then (Option.get end_ofs - start_ofs)
          else seclen - start_ofs in
        Bytes.sub file (secofs + start_ofs) symbol_len
      else
        let end_ofs = Option.map (fun x -> x - seclen) end_ofs in
        extract_bytes (start_ofs - seclen) end_ofs sections' in

  (* 1. The __text section data *)
  snd (find_section "__text"),

  (* 2. The readonly constants *)
  (if length !const_symbols = 0 then [] else begin
    (* collect (symbol name, bytes) list *)
    let res = ref [] in
    for j = 0 to (length !const_symbols - 1) do
      let sname,ofs = List.nth !const_symbols j in
      let ofs_end = if j = length !const_symbols - 1 then None
        else Some (snd (List.nth !const_symbols (j+1))) in
      res := !res @ [sname, extract_bytes ofs ofs_end !sections]
    done;
    !res
    end),

   (* 3. Relocation entries *)
  (let res = ref [] in
    List.iter (fun section_idx, r_address, r_data, r_symbolnum, r_pcrel, r_length, r_extern, r_type ->
      let symbolname,_,_,_,_ = List.nth !raw_symbols r_symbolnum in
      res := !res @ [reloc_type r_type,
        (r_address, symbolname, 0 (* corresponds to "addend" in ELF relocation entry *))]
    ) !raw_reloc_entries;
    (* sort the result *)
    sort (fun (_,(i1,_,_)) (_,(i2,_,_)) -> i1 < i2) !res
  );;

let load_macho_code arch file =
  let code,_,_ = load_macho arch
    (fun _ -> failwith "MachO contains relocations") file in
  code;;

(*** TODO: rename these to "load_obj_contents_*" or something else
     because they can also recognize the Mach-O format ***)
let load_elf_contents_x86 path =
  let file = load_file path in
  if is_macho file then load_macho_code 0x01000007 file (* x86, 64-bit *)
  else if is_elf file then load_elf_code 62 file (* x86-64 *)
  else failwith "Neither ELF nor Mach-O";;

let load_elf_contents_arm path =
  let file = load_file path in
  if is_macho file then load_macho_code 0x0100000C file (* ARM, 64-bit *)
  else if is_elf file then load_elf_code 183 file (* ARM AARCH64 *)
  else failwith "Neither ELF nor Mach-O";;


let load_elf_x86 = load_elf (62 (* x86-64 *))
  (function
  | 2 (* R_X86_64_PC32 *) -> ()
  | n -> failwith (sprintf "unexpected relocation type: %d" n));;

(* s2n-bignum data structure for representing relocations.
  The full list can be found from
  https://github.com/lattera/glibc/blob/master/elf/elf.h#L2731.
  Their meanings can be found from 5.7.3. Relocation types in
  https://github.com/ARM-software/abi-aa/blob/main/aaelf64/aaelf64.rst#5733relocation-operations.

  The naming of these constructors follow those of ELF.
*)
type arm_reloc =
    | Arm_condbr19 (* conditional branches *)
    | Arm_call26 (* BL *)
    | Arm_adr_prel_lo21 (* ADR *)
    | Arm_adr_prel_pg_hi21 (* ADRP; this is ARM64_RELOC_PAGE21 in Mach-O *)
    | Arm_add_abs_lo12_nc (* ADD; this is ARM64_RELOC_PAGEOFF12 in Mach-O  *);;

let load_elf_arm (bs:bytes):
  bytes * (string * bytes) list * (arm_reloc * (int * string * int)) list =
  if is_macho bs then
    load_macho 0x0100000C (function
      (* See the full list from:
         https://github.com/llvm/llvm-project/blob/main/llvm/include/llvm/BinaryFormat/MachO.h *)
      | 3 (* ARM64_RELOC_PAGE21 *) -> Arm_adr_prel_pg_hi21
      | 4 (* ARM64_RELOC_PAGEOFF12 *) -> Arm_add_abs_lo12_nc
      | n -> failwith (sprintf "unexpected relocation type: %d" n))
      bs
  else
    load_elf (183 (* ARM AARCH64 *))
      (function
      (* See the full list from:
          https://github.com/lattera/glibc/blob/master/elf/elf.h#L2731 *)
      | 274 (* R_AARCH64_ADR_PREL_LO21 *) -> Arm_adr_prel_lo21
      | 275 (* R_AARCH64_ADR_PREL_PG_HI21  *) -> Arm_adr_prel_pg_hi21
      | 277 (* R_AARCH64_ADD_ABS_LO12_NC  *) -> Arm_add_abs_lo12_nc
      | 280 (* R_AARCH64_CONDBR19 *) -> Arm_condbr19
      | 283 (* R_AARCH64_CALL26 *) -> Arm_call26
      | n -> failwith (sprintf "unexpected relocation type: %d" n))
      bs;;

let term_of_list_int,app_term_of_int_fun,term_of_int_fun =
  let word = `word:num->byte`
  and nil = `NIL:byte list`
  and cons = `CONS:byte->byte list->byte list` in
  let cons_word n e =
    mk_comb (mk_comb (cons, mk_comb (word, mk_numeral (num n))), e) in
  let app_term_of_int_fun f start end_ =
    let rec go n e =
      if n = start then e else
      let n' = n - 1 in
      go n' (cons_word (f n') e) in
    go end_ in
  C (itlist cons_word) nil, app_term_of_int_fun,
  fun f start end_ -> app_term_of_int_fun f start end_ nil;;

(* # term_of_int_fun (fun i -> i * 2) 10 20;;

  - : term =
  `[word 20; word 22; word 24; word 26; word 28; word 30; word 32; word 34;
    word 36; word 38]` *)

let term_of_bytes bs =
  term_of_int_fun (Char.code o Bytes.get bs) 0 (Bytes.length bs);;
let term_of_array bs =
  term_of_int_fun (Array.get bs) 0 (Array.length bs);;
let array_of_bytes bs =
  Array.init (Bytes.length bs) (Char.code o Bytes.get bs);;

let term_of_relocs reloc_fn (bstext,constants,rels) =
  let rec go = function
  | [], start ->
    [], term_of_int_fun (Char.code o Bytes.get bstext) start (Bytes.length bstext)
  | (ty,(off,sym,(add:int)))::ls, start ->
    let sym = mk_var(sym,`:num`) in
    let n, app = reloc_fn(bstext,ty,off,sym,add) in
    let args, e = go (ls, off+n) in
    insert sym args,
    app_term_of_int_fun (Char.code o Bytes.get bstext) start off (app e) in
  let args, e = go (rels, 0) in
  `pc:num` :: args, e;;
