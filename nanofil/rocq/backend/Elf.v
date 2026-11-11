(** # A shared object from an object

    Encode.v gives the object GNU as would make of the backend's lines;
    this file links it alone into an ELF shared object that glibc's
    dlopen loads, as `ld -shared` does in experiments/regex-nanofil's
    rxc. libnanofil gives a program these bytes, and the program loads
    them from a memfd, so no assembler, linker or file is involved.

    The shared object has three loaded segments, and each starts on a
    page. The first is read-only and holds the headers, the dynamic
    tables and .rodata. The second is executable and holds .text and
    the stubs for imported functions. The third is writable and holds
    the data. Some of the data is written only while the loader
    relocates it: .data.rel.ro, the init and fini arrays, the GOT and
    .dynamic. That part comes first, and PT_GNU_RELRO tells the loader
    to make it read-only once relocation is done. PT_GNU_STACK asks for
    a stack that is not executable.

    Relocations are resolved as the object's own definitions first,
    as `ld -shared -Bsymbolic` resolves them: a call or a reference to
    a symbol the object defines goes to that definition, and only an
    undefined symbol is looked up when the object is loaded. A call to
    one goes through a stub that jumps through its GOT slot. The
    loader fills each slot and each address in the data with
    R_X86_64_GLOB_DAT, R_X86_64_64 or R_X86_64_RELATIVE relocations,
    all at load time: there is no lazy binding.

    | Section | Content |
    | --- | --- |
    | .hash | the SysV hash table of .dynsym, which dlsym searches |
    | .dynsym, .dynstr | the null symbol, the imports, then the exports: defined symbols that are global or weak and not hidden |
    | .rela.dyn | the load-time relocations |
    | .plt | one `jmp *slot(%rip)` per imported function that is called |
    | .got | one slot per symbol a GOTPCREL operand or a stub needs |
    | .dynamic | where the tables are, and the init and fini arrays |

    [so_image] refuses an object that it cannot link, and the caller
    treats the module as outside the compiler:

    | The object has | Why it is refused |
    | --- | --- |
    | thread-local storage | no TLS segment is written |
    | an absolute 32-bit address | a shared object can be loaded anywhere |
    | an address in .text or .rodata | the loader cannot write those pages |
    | a PC-relative reference to an undefined symbol, other than a call | only calls go through stubs |
    | a section other than those above | it is not placed |
*)

From Stdlib Require Import String ZArith List Ascii Bool.
From Nanofil Require Import Maps.
From Backend Require Import Text Encode.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition page : Z := 4096.

Definition align_up (n a : Z) : Z := if a <=? 1 then n else ((n + a - 1) / a) * a.

(** ## What the object needs at load time *)

Definition sym_of (o : obj) (s : string) : option osym :=
  find (fun y => String.eqb (oy_name y) s) (ob_syms o).

(** The object's symbols by name. *)
Definition sym_map (o : obj) : smap osym :=
  fold_left (fun m y => sm_add (oy_name y) y m) (ob_syms o) sm_empty.

Definition defined (syms : smap osym) (s : string) : bool :=
  match sm_find s syms with
  | Some y => match oy_sec y with Some _ => true | None => false end
  | None => false
  end.

Definition is_got_type (t : Z) : bool := (t =? 9) || (t =? 41) || (t =? 42).

(** Adds [s] to a list of names, once. *)
Definition add_name (s : string) (l : list string) : list string :=
  if existsb (String.eqb s) l then l else l ++ [s].

(** The imported symbols, the symbols with GOT slots and those with
    stubs, each in order of first use; or why the object cannot be
    linked. *)
Record needs := mkneeds { n_imports : list string; n_got : list string; n_stubs : list string }.

Fixpoint plan (syms : smap osym) (rs : list oreloc) (n : needs) : needs + string :=
  match rs with
  | [] => inl n
  | r :: rest =>
      let s := or_sym r in
      let t := or_type r in
      let def := or_secsym r || defined syms s in
      if is_got_type t then
        plan syms rest (mkneeds (if def then n_imports n else add_name s (n_imports n))
                                (add_name s (n_got n)) (n_stubs n))
      else if t =? 4 then
        if def then plan syms rest n
        else plan syms rest (mkneeds (add_name s (n_imports n)) (add_name s (n_got n)) (add_name s (n_stubs n)))
      else if t =? 2 then
        if def then plan syms rest n else inr (("a PC-relative reference to the undefined symbol " ++ s)%string)
      else if t =? 1 then
        if String.eqb (or_sec r) ".text" || String.eqb (or_sec r) ".rodata"
        then inr (("an address in the read-only section " ++ or_sec r)%string)
        else if def then plan syms rest n
        else plan syms rest (mkneeds (add_name s (n_imports n)) (n_got n) (n_stubs n))
      else if t =? 22 then inr "thread-local storage"
      else inr (("a relocation of type " ++ decimal t)%string)
  end.

(** The symbols the object defines for others: global or weak, and
    not hidden. *)
Definition exports (o : obj) : list osym :=
  filter_tr (fun y => match oy_sec y with
                   | Some _ => negb (oy_bind y =? 0) && negb (oy_vis y =? 2)
                   | None => false
                   end) (ob_syms o).

(** ## Placing the sections *)

(** A section of the shared object: name, ELF type, flags, alignment,
    entry size, the section its sh_link names, sh_info, the segment it
    is in (0 read, 1 code, 2 relro, 3 data, 4 none), and its bytes, or
    its size for NOBITS. *)
Record outsec := mkout {
  q_name : string; q_type : Z; q_flags : Z; q_align : Z; q_entsize : Z; q_link : string;
  q_info : Z; q_seg : Z; q_bytes : list Z; q_size : Z }.

(** Where a section went: its address, which is also its file offset,
    except past the end of the file for NOBITS. *)
Definition placed := list (string * Z).

Definition q_len (q : outsec) : Z := if q_type q =? 8 then q_size q else zlen (q_bytes q).

(** Places the sections in order from [addr], each segment from a new
    page and the relro part padded to a page. *)
Fixpoint place_secs (qs : list outsec) (seg addr : Z) (acc : placed) : placed * Z :=
  match qs with
  | [] => (acc, addr)
  | q :: r =>
      let start := if q_seg q =? seg then addr else align_up addr page in
      let a := align_up start (q_align q) in
      place_secs r (q_seg q) (a + q_len q) (acc ++ [(q_name q, a)])
  end.

Definition addr_of (p : placed) (s : string) : Z :=
  match find (fun e => String.eqb (fst e) s) p with Some e => snd e | None => 0 end.

(** ## Bytes *)

Definition elf_hash (s : string) : Z :=
  fold_left (fun h c =>
               let h1 := h * 16 + Z.of_nat (nat_of_ascii c) in
               let g := Z.land h1 4026531840 in
               if g =? 0 then h1 else Z.land (Z.lxor h1 (Z.shiftr g 24)) (4294967295 - g))
            (list_ascii_of_string s) 0.

Definition str_bytes (s : string) : list Z := map (fun c => Z.of_nat (nat_of_ascii c)) (list_ascii_of_string s).

(** A string table of [names] after a NUL, with each name's offset;
    [acc] holds the names so far, last first. *)
Fixpoint strtab_rev (names : list string) (off : Z) (acc : list (list Z)) (offs : smap Z) : list (list Z) * smap Z :=
  match names with
  | [] => (acc, offs)
  | n :: r =>
      match sm_find n offs with
      | Some _ => strtab_rev r off acc offs
      | None =>
          let bs := str_bytes n ++ [0] in
          strtab_rev r (off + zlen bs) (bs :: acc) (sm_add n off offs)
      end
  end.

Definition strtab (names : list string) : list Z * smap Z :=
  let (acc, offs) := strtab_rev names 1 [[0]] sm_empty in (join_rev acc, offs).

Definition name_off (offs : smap Z) (s : string) : Z :=
  match sm_find s offs with Some n => n | None => 0 end.

(** Writes [patches], at offsets in increasing order from [pos], into
    [bs]; [acc] holds the pieces so far, last first, and the result is
    in that order too. *)
Fixpoint patch_rev (fuel : nat) (bs : list Z) (pos : Z) (patches : list (Z * list Z))
         (acc : list (list Z)) : list (list Z) :=
  match fuel with
  | O => bs :: acc
  | S fuel' =>
      match patches with
      | [] => bs :: acc
      | (at_, v) :: rest =>
          let skip := Z.to_nat (at_ - pos) in
          let n := length v in
          patch_rev fuel' (skipn (skip + n) bs) (at_ + Z.of_nat n) rest (v :: take skip bs :: acc)
      end
  end.

Definition apply_patches (fuel : nat) (bs : list Z) (pos : Z) (patches : list (Z * list Z)) : list Z :=
  join_rev (patch_rev fuel bs pos patches []).

(** The numbers 0 to [n] - 1, in front of [acc]. *)
Fixpoint upto_onto (n : nat) (acc : list Z) : list Z :=
  match n with
  | O => acc
  | S n' => upto_onto n' (Z.of_nat n' :: acc)
  end.

(** The SysV hash table of the symbols [names], index 1 on. *)
Definition hash_table (names : list string) : list Z :=
  let n := zlen names + 1 in
  let nb := Z.max 1 (zlen names) in
  let '(_, buckets, chains) :=
    fold_left (fun (acc : Z * ZMap.t Z * ZMap.t Z) name =>
                 let '(i, bk, ch) := acc in
                 let b := elf_hash name mod nb in
                 let head := match ZMap.find b bk with Some h => h | None => 0 end in
                 (i + 1, ZMap.add b i bk, ZMap.add i head ch))
              names (1, ZMap.empty _, ZMap.empty _) in
  let get m i := match ZMap.find i m with Some v => v | None => 0 end in
  le4 nb ++ le4 n
    ++ flat_map_tr (fun i => le4 (get buckets i)) (upto_onto (Z.to_nat nb) [])
    ++ flat_map_tr (fun i => le4 (get chains i)) (upto_onto (Z.to_nat n) []).

(** The init or fini arrays in the order the linker puts them: by
    priority, then the one without. *)
Definition prio_of (base name : string) : option Z :=
  if String.eqb name base then None
  else Some (fold_left (fun n c => n * 10 + (Z.of_nat (nat_of_ascii c) - 48))
                       (list_ascii_of_string (substring (String.length base + 1) (String.length name) name)) 0).

Definition array_secs (o : obj) (base : string) : list osec :=
  let mine := filter (fun s => String.prefix base (os_name s)) (ob_secs o) in
  let with_prio := filter (fun s => match prio_of base (os_name s) with Some _ => true | None => false end) mine in
  let sorted := sort (fun a b => match prio_of base (os_name a), prio_of base (os_name b) with
                                 | Some x, Some y => x <=? y
                                 | _, _ => true
                                 end) with_prio in
  sorted ++ filter (fun s => String.eqb (os_name s) base) mine.

Definition known_sec (n : string) : bool :=
  existsb (String.eqb n) [".text"; ".rodata"; ".data.rel.ro"; ".data"; ".bss"; ".note.GNU-stack"]
  || String.prefix ".init_array" n || String.prefix ".fini_array" n.

(** The ELF symbol entry of [y] in the section numbered [shndx]. *)
Definition sym_entry (name : Z) (y : osym) (shndx value : Z) : list Z :=
  le4 name ++ [oy_bind y * 16 + oy_type y; oy_vis y] ++ le2 shndx ++ le8 value ++ le8 (oy_size y).

Definition rela (off typ sym add : Z) : list Z := le8 off ++ le8 (sym * 4294967296 + typ) ++ le8 add.

Definition shdr (name typ flags addr off size link info align entsize : Z) : list Z :=
  le4 name ++ le4 typ ++ le8 flags ++ le8 addr ++ le8 off ++ le8 size ++ le4 link ++ le4 info
    ++ le8 align ++ le8 entsize.

Definition phdr (typ flags off size memsz align : Z) : list Z :=
  le4 typ ++ le4 flags ++ le8 off ++ le8 off ++ le8 off ++ le8 size ++ le8 memsz ++ le8 align.

Fixpoint index_of (s : string) (l : list string) (i : Z) : Z :=
  match l with
  | [] => 0
  | x :: r => if String.eqb x s then i else index_of s r (i + 1)
  end.

Definition concat_bytes (ss : list osec) : list Z * list (string * Z) :=
  fold_left (fun (acc : list Z * list (string * Z)) s =>
               let '(bs, offs) := acc in
               let start := align_up (zlen bs) (os_align s) in
               (bs ++ repeat 0 (Z.to_nat (start - zlen bs)) ++ os_bytes s, offs ++ [(os_name s, start)]))
            ss ([], []).

(** The shared object of [o], or why it cannot be linked. *)
Definition so_image (o : obj) : list Z + string :=
  match find (fun s => negb (known_sec (os_name s))) (ob_secs o) with
  | Some s => inr (("the section " ++ os_name s)%string)
  | None =>
  let syms := sym_map o in
  match plan syms (ob_relocs o) (mkneeds [] [] []) with
  | inr why => inr why
  | inl nd =>
  let exps := exports o in
  let dyn_names := n_imports nd ++ map oy_name exps in
  let '(dynstr, offs) := strtab dyn_names in
  let sec_named n := find (fun s => String.eqb (os_name s) n) (ob_secs o) in
  let sec_bytes n := match sec_named n with Some s => os_bytes s | None => [] end in
  let sec_align n := match sec_named n with Some s => os_align s | None => 1 end in
  let '(init_bytes, init_offs) := concat_bytes (array_secs o ".init_array") in
  let '(fini_bytes, fini_offs) := concat_bytes (array_secs o ".fini_array") in
  let bss_size := match sec_named ".bss" with Some s => os_size s | None => 0 end in
  let nstub := zlen (n_stubs nd) in
  let ngot := zlen (n_got nd) in
  let nrel := zlen (filter_tr (fun r => or_type r =? 1) (ob_relocs o)) + ngot in
  let ndyn := 9 + (if zlen init_bytes =? 0 then 0 else 2) + (if zlen fini_bytes =? 0 then 0 else 2) in
  let nsym := 1 + zlen dyn_names in
  (* The sections, in the order they are placed; the contents of those
     whose bytes depend on addresses are filled once they are placed. *)
  let layout :=
    [mkout ".hash" 5 2 8 4 ".dynsym" 0 0 (hash_table dyn_names) 0;
     mkout ".dynsym" 11 2 8 24 ".dynstr" 1 0 (zeros (24 * nsym)) 0;
     mkout ".dynstr" 3 2 1 0 "" 0 0 dynstr 0;
     mkout ".rela.dyn" 4 2 8 24 ".dynsym" 0 0 (zeros (24 * nrel)) 0;
     mkout ".rodata" 1 2 (sec_align ".rodata") 0 "" 0 0 (sec_bytes ".rodata") 0;
     mkout ".text" 1 6 (sec_align ".text") 0 "" 0 1 (sec_bytes ".text") 0;
     mkout ".plt" 1 6 16 8 "" 0 1 (zeros (8 * nstub)) 0;
     mkout ".data.rel.ro" 1 3 (sec_align ".data.rel.ro") 0 "" 0 2 (sec_bytes ".data.rel.ro") 0;
     mkout ".init_array" 14 3 8 8 "" 0 2 init_bytes 0;
     mkout ".fini_array" 15 3 8 8 "" 0 2 fini_bytes 0;
     mkout ".got" 1 3 8 8 "" 0 2 (zeros (8 * ngot)) 0;
     mkout ".dynamic" 6 3 8 16 ".dynstr" 0 2 (zeros (16 * ndyn)) 0;
     mkout ".data" 1 3 (Z.max 8 (sec_align ".data")) 0 "" 0 3 (sec_bytes ".data") 0;
     mkout ".bss" 8 3 (sec_align ".bss") 0 "" 0 3 [] bss_size] in
  let layout := filter (fun q => negb (q_len q =? 0) || existsb (String.eqb (q_name q))
                                   [".hash"; ".dynsym"; ".dynstr"; ".rela.dyn"; ".got"; ".dynamic"; ".data"]) layout in
  let nph := 6 in
  let headers := 64 + 56 * nph in
  (* The relro part ends on a page: .data starts one. *)
  let '(pl, _) := place_secs layout 0 headers [] in
  let a n := addr_of pl n in
  let sec_addr n :=
    if String.prefix ".init_array" n then a ".init_array" + match find (fun e => String.eqb (fst e) n) init_offs with Some e => snd e | None => 0 end
    else if String.prefix ".fini_array" n then a ".fini_array" + match find (fun e => String.eqb (fst e) n) fini_offs with Some e => snd e | None => 0 end
    else a n in
  let out_of n := if String.prefix ".init_array" n then ".init_array"
                  else if String.prefix ".fini_array" n then ".fini_array" else n in
  let shnames := map q_name layout in
  let shndx n := index_of (out_of n) shnames 1 in
  let sym_value (s : string) : option Z :=
    match sm_find s syms with
    | Some y => match oy_sec y with Some c => Some (sec_addr c + oy_value y) | None => None end
    | None => None
    end in
  let target r := if or_secsym r then Some (sec_addr (or_sym r)) else sym_value (or_sym r) in
  let dynidx s := index_of s dyn_names 1 in
  let got_slot s := a ".got" + 8 * (index_of s (n_got nd) 0) in
  let stub s := a ".plt" + 8 * (index_of s (n_stubs nd) 0) in
  (* The bytes each relocation writes, by section, and the load-time
     relocations. *)
  let fixes :=
    map_tr (fun r =>
           let p := sec_addr (or_sec r) + or_off r in
           let t := or_type r in
           let v := target r in
           let field :=
             if is_got_type t then le4 (got_slot (or_sym r) + or_add r - p)
             else if t =? 4 then
               match v with Some x => le4 (x + or_add r - p) | None => le4 (stub (or_sym r) + or_add r - p) end
             else if t =? 2 then
               match v with Some x => le4 (x + or_add r - p) | None => le4 0 end
             else match v with Some x => le8 (x + or_add r) | None => le8 0 end in
           (or_sec r, (or_off r, field))) (ob_relocs o) in
  let data_rels :=
    flat_map_tr (fun r =>
                if or_type r =? 1 then
                  let p := sec_addr (or_sec r) + or_off r in
                  match target r with
                  | Some x => [rela p 8 0 (x + or_add r)]
                  | None => [rela p 1 (dynidx (or_sym r)) (or_add r)]
                  end
                else []) (ob_relocs o) in
  let got_rels :=
    map_tr (fun s =>
           match sym_value s with
           | Some x => rela (got_slot s) 8 0 x
           | None => rela (got_slot s) 6 (dynidx s) 0
           end) (n_got nd) in
  let patched n :=
    let ps := map_tr snd (filter_tr (fun f => String.eqb (fst f) n) fixes) in
    apply_patches (length ps) (sec_bytes n) 0 ps in
  let array_bytes base offs total :=
    (* the sections at their offsets, with the padding between them *)
    fold_left (fun bs e =>
                 let n := fst e in
                 let ps := map snd (filter (fun f => String.eqb (fst f) n) fixes) in
                 bs ++ repeat 0 (Z.to_nat (snd e - zlen bs)) ++ apply_patches (length ps) (sec_bytes n) 0 ps)
              offs [] in
  let dynsym :=
    repeat 0 24
    ++ flat_map_tr (fun s => sym_entry (name_off offs s)
                            (match sm_find s syms with Some y => mkosym s (oy_bind y) (oy_type y) 0 None 0 0
                                                  | None => mkosym s 1 0 0 None 0 0 end) 0 0) (n_imports nd)
    ++ flat_map_tr (fun y => sym_entry (name_off offs (oy_name y)) y
                            (match oy_sec y with Some c => shndx c | None => 0 end)
                            (match sym_value (oy_name y) with Some v => v | None => 0 end)) exps in
  let stubs :=
    flat_map (fun s => let p := stub s in [255; 37] ++ le4 (got_slot s - (p + 6)) ++ [102; 144]) (n_stubs nd) in
  let dyn_entry tag v := le8 tag ++ le8 v in
  let dynamic :=
    dyn_entry 4 (a ".hash") ++ dyn_entry 5 (a ".dynstr") ++ dyn_entry 6 (a ".dynsym")
    ++ dyn_entry 10 (zlen dynstr) ++ dyn_entry 11 24
    ++ dyn_entry 7 (a ".rela.dyn") ++ dyn_entry 8 (24 * nrel) ++ dyn_entry 9 24
    ++ (if zlen init_bytes =? 0 then [] else dyn_entry 25 (a ".init_array") ++ dyn_entry 27 (zlen init_bytes))
    ++ (if zlen fini_bytes =? 0 then [] else dyn_entry 26 (a ".fini_array") ++ dyn_entry 28 (zlen fini_bytes))
    ++ dyn_entry 0 0 in
  let content (q : outsec) : list Z :=
    let n := q_name q in
    if String.eqb n ".dynsym" then dynsym
    else if String.eqb n ".rela.dyn" then join_rev (rev' (rev_append (rev' data_rels) got_rels))
    else if String.eqb n ".plt" then stubs
    else if String.eqb n ".dynamic" then dynamic
    else if String.eqb n ".init_array" then array_bytes ".init_array" init_offs (zlen init_bytes)
    else if String.eqb n ".fini_array" then array_bytes ".fini_array" fini_offs (zlen fini_bytes)
    else if String.eqb n ".got" then q_bytes q
    else if existsb (String.eqb n) [".rodata"; ".text"; ".data.rel.ro"; ".data"] then patched n
    else q_bytes q in
  (* The file: each section's bytes at its address, then .shstrtab and
     the section headers. *)
  let '(body_rev, file_end) :=
    fold_left (fun (acc : list (list Z) * Z) q =>
                 let '(chunks, len) := acc in
                 if q_type q =? 8 then acc
                 else let c := content q in
                      (c :: zeros (a (q_name q) - len) :: chunks, a (q_name q) + zlen c))
              layout ([], 0) in
  let '(shstr, shoffs) := strtab (shnames ++ [".shstrtab"]) in
  let shstr_off := file_end in
  let shoff := align_up (shstr_off + zlen shstr) 8 in
  let seg_bounds (seg : Z) : Z * Z * Z :=
    let qs := filter (fun q => q_seg q =? seg) layout in
    match qs with
    | [] => (0, 0, 0)
    | q :: _ =>
        let start := a (q_name q) in
        let fend := fold_left (fun e q' => if q_type q' =? 8 then e else Z.max e (a (q_name q') + q_len q')) qs start in
        let mend := fold_left (fun e q' => Z.max e (a (q_name q') + q_len q')) qs start in
        (start, fend, mend)
    end in
  let '(s1, e1f, _) := seg_bounds 1 in
  let '(s2, e2f, _) := seg_bounds 2 in
  let '(s3, e3f, e3m) := seg_bounds 3 in
  let '(_, e0f, _) := seg_bounds 0 in
  let rw_start := s2 in
  let rw_file_end := if e3f =? 0 then e2f else Z.max e2f e3f in
  let rw_mem_end := if e3m =? 0 then e2f else Z.max e2f e3m in
  let dyn_size := 16 * ndyn in
  let phdrs :=
    phdr 1 4 0 e0f e0f page
    ++ phdr 1 5 s1 (e1f - s1) (e1f - s1) page
    ++ phdr 1 6 rw_start (rw_file_end - rw_start) (rw_mem_end - rw_start) page
    ++ phdr 2 6 (a ".dynamic") dyn_size dyn_size 8
    ++ le4 1685382481 ++ le4 6 ++ repeat 0 40 ++ le8 16
    ++ phdr 1685382482 4 s2 (align_up e2f page - s2) (align_up e2f page - s2) 1 in
  let ehdr :=
    [127; 69; 76; 70; 2; 1; 1; 0] ++ repeat 0 8
    ++ le2 3 ++ le2 62 ++ le4 1 ++ le8 0 ++ le8 64 ++ le8 shoff ++ le4 0
    ++ le2 64 ++ le2 56 ++ le2 nph ++ le2 64 ++ le2 (zlen shnames + 2) ++ le2 (zlen shnames + 1) in
  let shdrs :=
    repeat 0 64
    ++ flat_map (fun q =>
                   let n := q_name q in
                   shdr (name_off shoffs n) (q_type q) (q_flags q) (a n) (a n) (q_len q)
                        (if String.eqb (q_link q) "" then 0 else index_of (q_link q) shnames 1)
                        (q_info q) (q_align q) (q_entsize q)) layout
    ++ shdr (name_off shoffs ".shstrtab") 3 0 0 shstr_off (zlen shstr) 0 0 1 0 in
  let head := ehdr ++ phdrs in
  let body := join_rev body_rev in
  inl (join_rev [shdrs; zeros (shoff - (shstr_off + zlen shstr)); shstr;
                 skipn (Z.to_nat (zlen head)) body; head])
  end
  end.
