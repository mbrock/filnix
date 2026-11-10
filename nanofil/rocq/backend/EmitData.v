(** # Data objects, thread-local data, table entries and aliases

    The lines of a module item that is not a function, as
    filc_amd64.pl's `item//2` gives them for `data(Name, Linkage,
    Align, Items)` (`data_object//4`, `thread_local_object//4`,
    `init_entry//4`, a weak declaration) and `alias_getter//4` for
    `alias(Name, Linkage, Target)`.

    Emission is total: where the Prolog compiler's goal would fail or
    throw, the lines hold a [todo] line (Layout.v) in that place. *)

From Stdlib Require Import String ZArith List Bool Ascii.
From Nanofil Require Import Term Syntax Maps.
From Backend Require Import Text Asm Plan Abi Layout EmitObject Emit.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(** ## Lines *)

(** `type(S, Kind)`. *)
Definition type_line (s kind : string) : line := Dir (DType (LSym s) (LSym kind)).

(** `size(S, N)`. *)
Definition size_line (s : string) (n : Z) : line := Dir (DSizeOf (LSym s) (LInt n)).

(** `section(S)`. *)
Definition section_line (s : section) : line := Dir (DSection s).

(** As `linkage_globl//2`, of a linkage kept as its term. Emit.v's
    [linkage_globl] gives no line for a term the Prolog has no clause
    for; this one gives a [todo]. *)
Definition data_linkage_globl (l : term) (s : string) : list line :=
  match linkage_of l with
  | LkExport => [Dir (DGlobl (LSym s))]
  | LkLocal => []
  | LkWeak => [Dir (DWeak (LSym s))]
  | LkOther => todo "linkage"
  end.

(** ## Aux words *)

(** A flag of an object's aux word. *)
Inductive object_flag_name : Type :=
| FlGlobal
| FlReadonly
| FlGlobalAux (* the aux array is static data *)
| FlFunction (* special type 1, function *)
| FlSpecialType. (* the special type field, bits 7-10 *)

(** As `object_flag/2`. *)
Definition object_flag (f : object_flag_name) : Z :=
  match f with
  | FlGlobal => 1
  | FlReadonly => 2
  | FlGlobalAux => 16
  | FlFunction => 128
  | FlSpecialType => 1920
  end.

(** The bit at which an aux word's flags start: its low 48 bits are
    the aux pointer. *)
Definition aux_flags_shift : Z := 48.

(** As `aux_bits/2`: the flags in an aux word. *)
Definition aux_bits (flags : list object_flag_name) : Z :=
  Z.shiftl (fold_left (fun sum f => Z.lor sum (object_flag f)) flags 0) aux_flags_shift.

Example aux_bits_function :
  aux_bits [FlGlobal; FlReadonly; FlFunction] = function_object_flags.
Proof. reflexivity. Qed.

(** As `linkage_flags/3`: a data object's linkage, kept as its term,
    and the flag `readonly` if it is read-only. Nothing for a linkage
    that is not a data object's. *)
Definition linkage_flags (lk : Syntax.linkage) : option (term * list object_flag_name) :=
  match lk with
  | LRo l => Some (l, [FlReadonly])
  | LExport => Some (TAtom "export", [])
  | LLocal => Some (TAtom "local", [])
  | LWeak => Some (TAtom "weak", [])
  | LTls _ | LInit _ _ | LExternWeak | LOther _ => None
  end.

(** As `memberchk(readonly, Flags)`. *)
Definition has_readonly (flags : list object_flag_name) : bool :=
  existsb (fun f => match f with FlReadonly => true | _ => false end) flags.

(** ## The payload *)

(** As `r(Offset, Symbol, Addend)`: the pointer at an offset of a
    payload is the symbol's plus the addend. *)
Record reloc : Type := mkReloc {
  r_off : Z;
  r_sym : name;
  r_addend : Z
}.

(** The byte numbers of an x87 extended float, as `numlist(0, 9, Is)`. *)
Definition extended_bytes : list Z := [0; 1; 2; 3; 4; 5; 6; 7; 8; 9].

Definition byte_mask : Z := 255.
Definition byte_count : Z := 256.

(** Whether a character code is a byte. *)
Definition is_byte (c : Z) : bool := (0 <=? c) && (c <? byte_count).

(** As `payload_item/4` and `value_payload/5`: the payload directive
    of the item at the offset off, the offset after it, and rs with
    a relocation added if the item is a pointer, whose slot stays 0
    until the relocation fills it in. The directive is a [todo]
    where the Prolog fails (an item of no clause) or throws (a
    pointer that is not 8-aligned), and for a string with a
    character that is not a byte, which `.ascii` cannot hold. *)
Definition payload_item (it : data_item) (off : Z) (rs : list reloc)
  : list line * Z * list reloc :=
  match it with
  | Zero n => ([zero n], off + n, rs)
  | Str cs =>
      (if forallb is_byte cs
       then [Dir (DAscii (map (fun c => ascii_of_nat (Z.to_nat c)) cs))]
       else todo "string character is not a byte",
       off + Zlength cs, rs)
  | Sym s addend =>
      (if off mod eight =? 0 then [quad_int 0] else todo "pointer data item is not 8-aligned",
       off + eight, mkReloc off s addend :: rs)
  | Item Wx n =>
      (match map (fun i => LInt (Z.land (Z.shiftr n (eight * i)) byte_mask)) extended_bytes with
       | b :: bs => [Dir (DByte b bs)]
       | [] => todo "extended float bytes"
       end,
       off + 10, rs)
  | Item w n =>
      let bytes := width_bytes w in
      let u := n mod (Z.shiftl 1 (eight * bytes)) in
      (if bytes =? 1 then [Dir (DByte (LInt u) [])]
       else if bytes =? 2 then [Dir (DShort (LInt u))]
       else if bytes =? 4 then [long u]
       else if bytes =? eight then [quad_int u]
       else todo "data item width",
       off + bytes, rs)
  | ItemOther _ => (todo "data item", off, rs)
  end.

(** As `foldl(payload_item, Items, Payload, Off0-Rs0, Off-Rs)`: the
    payload directives of the items from the offset off, the offset
    after them, and their relocations in front of rs, the last
    first. *)
Fixpoint payload_items (its : list data_item) (off : Z) (rs : list reloc)
  : list line * Z * list reloc :=
  match its with
  | [] => ([], off, rs)
  | it :: its' =>
      let '(l, off1, rs1) := payload_item it off rs in
      let '(ls, off2, rs2) := payload_items its' off1 rs1 in
      (l ++ ls, off2, rs2)
  end.

(** As `template_needed/1`: some byte of the items is not zero, so
    the fresh (zeroed) object needs a copy of them. *)
Definition template_needed (items : list data_item) : bool :=
  existsb (fun it => match it with
                     | Item _ n => negb (n =? 0)
                     | Str cs => existsb (fun c => negb (c =? 0)) cs
                     | _ => false
                     end) items.

(** ## Relocations *)

(** As `reloc_node/3`: the label of the constexpr node of relocation
    i of the data object name. *)
Definition reloc_node (name : string) (i : Z) : string :=
  ".Lpizlonated_" ++ name ++ "..node" ++ decimal i.

(** As `reloc_entries//3`: the relocation table, each entry {u64
    offset, u32 kind, pad, target}: kind 0 calls a getter, kind 1 a
    constexpr node. rs are the relocations from the ith. *)
Fixpoint reloc_entries (rs : list reloc) (i : Z) (name : string) : list line :=
  match rs with
  | [] => []
  | r :: rs' =>
      (if r_addend r =? 0
       then [quad_int (r_off r); long 0; zero 4; quad_sym (getter_symbol (name_text (r_sym r)))]
       else [quad_int (r_off r); long 1; zero 4; quad_sym (reloc_node name i)])
      ++ reloc_entries rs' (i + 1) name
  end.

(** As `reloc_nodes//3`: the constexpr node {u32 add-immediate = 0,
    u32 0, getter, u64 addend} of each relocation with an addend. rs
    are the relocations from the ith. *)
Fixpoint reloc_nodes (rs : list reloc) (i : Z) (name : string) : list line :=
  match rs with
  | [] => []
  | r :: rs' =>
      (if r_addend r =? 0
       then []
       else [label (reloc_node name i); long 0; long 0;
             quad_sym (getter_symbol (name_text (r_sym r)));
             quad_int (r_addend r mod two64)])
      ++ reloc_nodes rs' (i + 1) name
  end.

(** As `relocations//2`. *)
Definition relocations (rs : list reloc) (name : string) : list line :=
  reloc_entries rs 0 name ++ reloc_nodes rs 0 name.

(** As `relocs_aux_word/4`: the aux word of a global data object
    with the relocations rs and the other flags: its flags, and its
    static aux array da if it holds pointers. *)
Definition relocs_aux_word (rs : list reloc) (flags : list object_flag_name) (da : string)
  : expr :=
  match rs with
  | [] => ELit (LInt (aux_bits (FlGlobal :: flags)))
  | _ :: _ => EAdd (ELit (LSym da)) (ELit (LInt (aux_bits (FlGlobal :: FlGlobalAux :: flags))))
  end.

(** As `aux_array//5`: the aux array da of size bytes and the
    relocation table relocs, if there are relocations. *)
Definition aux_array (rs : list reloc) (da : string) (size : Z) (relocs name : string)
  : list line :=
  match rs with
  | [] => []
  | _ :: _ =>
      [p2align 4; label da; zero size;
       section_line SDataRelRo; p2align 4; label relocs]
      ++ relocations rs name
  end.

(** As `relocations_call//3`: the getter's call that runs the
    relocations, if there are any, of the data object dobj from the
    table relocs. *)
Definition relocations_call (rs : list reloc) (dobj relocs : string) : list line :=
  match rs with
  | [] => []
  | _ :: _ =>
      [ins "mov" "q" [reg "rbx"; reg "rdi"];
       ins "lea" "q" [rip dobj; reg "rsi"];
       ins "lea" "q" [rip relocs; reg "rdx"];
       ins "mov" "l" [imm (Zlength rs); reg "ecx"];
       ins0 "call" [plt "filc_execute_constant_relocations"]]
  end.

(** ## Data objects *)

(** As `data_object//4`, as clang lays out globals: the object
    {upper, aux} then the payload rounded up to 8 bytes, a 16-byte
    cache, an aux array if the payload holds pointers, and a getter
    whose slow path registers the object and runs the relocations
    that fill in its pointers. A payload aligned to more than 16 has
    align - 16 zero bytes before the object, so that its payload is
    aligned. *)
Definition data_object (n : name) (lk : Syntax.linkage) (align : Z) (items : list data_item)
  : list line :=
  match linkage_flags lk with
  | None => todo "data linkage"
  | Some (linkage, flags) =>
      let name := name_text n in
      let dobj := data_object_symbol name in
      let da := data_aux_symbol name in
      let gp := (".LpizlonatedGP_" ++ name)%string in
      let getter := getter_symbol name in
      let relocs := (".Lpizlonated_" ++ name ++ "..relocs")%string in
      let slow := (".Lpizlonated_" ++ name ++ "..slow")%string in
      let inited := (".Lpizlonated_" ++ name ++ "..inited")%string in
      let '(payload, size0, rs0) := payload_items items 0 [] in
      let rs := rev' rs0 in
      let size := Z.quot (size0 + 7) eight * eight in
      let pad := size - size0 in
      let aux_word := relocs_aux_word rs flags da in
      let total := sixteen + size in
      let payload_align := Z.max align sixteen in
      let front := payload_align - sixteen in
      let log := Z.log2 payload_align in
      let sec := if has_readonly flags && match rs with [] => true | _ => false end
                 then SDataRelRo else SData in
      [section_line sec; p2align log]
      ++ (if front >? 0 then [zero front] else [])
      ++ [type_line dobj "object"; label dobj;
          Dir (DQuad (EAdd (payload_of dobj) (ELit (LInt size)))); Dir (DQuad aux_word)]
      ++ payload
      ++ (if pad >? 0 then [zero pad] else [])
      ++ [size_line dobj total]
      ++ [section_line SBss; p2align 4; label gp; zero sixteen]
      ++ aux_array rs da size relocs name
      ++ [section_line SText; p2align 4]
      ++ data_linkage_globl linkage getter
      ++ [type_line getter "function"; label getter;
          ins "mov" "q" [rip gp; reg "rax"];
          ins "mov" "q" [rip_plus gp eight; reg "rdx"];
          ins "test" "q" [reg "rax"; reg "rax"];
          ins0 "jz" [sym slow];
          ins "test" "q" [reg "rdx"; reg "rdx"];
          ins0 "jz" [sym slow];
          ins0 "ret" [];
          label slow;
          ins "push" "q" [reg "rbx"];
          ins "mov" "q" [reg "rdi"; reg "rbx"];
          ins "lea" "q" [rip gp; reg "rdx"];
          ins "lea" "q" [rip dobj; reg "rcx"];
          ins0 "call" [plt "filc_global_initialization_start"];
          ins "test" "b" [imm 1; reg "al"];
          ins0 "jz" [sym inited]]
      ++ relocations_call rs dobj relocs
      ++ [ins "mov" "q" [reg "rbx"; reg "rdi"];
          ins0 "call" [plt "filc_global_initialization_end"];
          label inited;
          ins "pop" "q" [reg "rbx"];
          ins "lea" "q" [ORip (payload_of dobj); reg "rax"];
          ins "mov" "q" [reg "rax"; reg "rdx"];
          ins0 "ret" []]
  end.

(** ## Thread-local data *)

(** As `thread_local_object//4`, as clang lays it out: a .tbss word
    holding this thread's payload address, null until the thread
    first asks, and a getter that returns it or calls the slow path.
    The slow path allocates the thread's object, copies the
    initializer's bytes from a template and runs its relocations, as
    a global's slow path does, then sets the word.

    The Prolog fails on an item its payload has no directive for
    before it gives any line. Here the payload's [todo] lines stand
    where the template would be when no template is needed, so that
    they are never dropped. *)
Definition thread_local_object (n : name) (linkage : term) (align : Z)
                               (items : list data_item) : list line :=
  let name := name_text n in
  let getter := getter_symbol name in
  let tp := ("pizlonatedTP_" ++ name)%string in
  let slow := (".LpizlonatedGS_" ++ name)%string in
  let template := (".LpizlonatedTI_" ++ name)%string in
  let relocs := (".Lpizlonated_" ++ name ++ "..relocs")%string in
  let ensure := (".Lpizlonated_" ++ name ++ "..ensure")%string in
  let '(payload, size, rs0) := payload_items items 0 [] in
  let rs := rev' rs0 in
  let allocate := match rs with
                  | [] => "filc_allocate_thread_local"
                  | _ :: _ => "filc_allocate_thread_local_with_ptrs"
                  end in
  let needed := template_needed items in
  let copy := if needed
              then [ins "lea" "q" [mem sixteen "r12"; reg "rdi"];
                    ins "lea" "q" [rip template; reg "rsi"];
                    ins "mov" "q" [imm size; reg "rcx"];
                    ins0 "rep movsb" []]
              else [] in
  let relocs_call := match rs with
                     | [] => []
                     | _ :: _ =>
                         [ins "mov" "q" [reg "rbx"; reg "rdi"];
                          ins "mov" "q" [reg "r12"; reg "rsi"];
                          ins "lea" "q" [rip relocs; reg "rdx"];
                          ins "mov" "l" [imm (Zlength rs); reg "ecx"];
                          ins0 "call" [plt "filc_execute_constant_relocations"]]
                     end in
  [section_line STbss; p2align 3]
  ++ data_linkage_globl linkage tp
  ++ [type_line tp "object"; label tp; zero eight; size_line tp eight]
  ++ (if needed
      then [section_line SRodata; p2align 4; label template] ++ payload
      else filter is_todo payload)
  ++ match rs with
     | [] => []
     | _ :: _ => [section_line SDataRelRo; p2align 4; label relocs] ++ relocations rs name
     end
  ++ [section_line SText; p2align 4]
  ++ data_linkage_globl linkage getter
  ++ [type_line getter "function"; label getter;
      ins "mov" "q" [OGottpoff (LSym tp); reg "rax"];
      ins "mov" "q" [OFs (mem 0 "rax"); reg "rax"];
      ins "test" "q" [reg "rax"; reg "rax"];
      ins0 "jz" [sym ensure];
      ins "mov" "q" [reg "rax"; reg "rdx"];
      ins0 "ret" [];
      label ensure;
      ins "sub" "q" [imm eight; reg "rsp"];
      ins0 "call" [sym slow];
      ins "add" "q" [imm eight; reg "rsp"];
      ins "mov" "q" [reg "rax"; reg "rdx"];
      ins0 "ret" [];
      p2align 4; type_line slow "function"; label slow;
      ins "push" "q" [reg "rbx"];
      ins "push" "q" [reg "r12"];
      ins "sub" "q" [imm eight; reg "rsp"];
      ins "mov" "q" [reg "rdi"; reg "rbx"];
      ins "mov" "q" [imm size; reg "rsi"];
      ins "mov" "q" [imm align; reg "rdx"];
      ins0 "call" [plt allocate];
      ins "mov" "q" [reg "rax"; reg "r12"]]
  ++ copy
  ++ relocs_call
  ++ [ins "lea" "q" [mem sixteen "r12"; reg "rax"];
      ins "mov" "q" [OGottpoff (LSym tp); reg "rcx"];
      ins "mov" "q" [reg "rax"; OFs (mem 0 "rcx")];
      ins "add" "q" [imm eight; reg "rsp"];
      ins "pop" "q" [reg "r12"];
      ins "pop" "q" [reg "rbx"];
      ins0 "ret" []].

(** ## Constructor and destructor table entries *)

(** As `init_runtime/2`: the runtime function a table entry of the
    kind hands its function object to, and whether the kind is
    `ctor`. *)
Definition init_runtime (kind : term) : option (bool * string) :=
  if is_atom "ctor" kind then Some (true, "filc_defer_or_run_global_ctor")
  else if is_atom "dtor" kind then Some (false, "filc_run_global_dtor")
  else None.

(** The priority of `section(init(Kind, Prio))`: none for the atom
    `none`, else the integer or atom; nothing for a term asm.pl has
    no text for. *)
Definition init_priority (prio : term) : option (option lit) :=
  match prio with
  | TInt p => Some (Some (LInt p))
  | TAtom a => if String.eqb a "none" then Some None else Some (Some (LSym a))
  | _ => None
  end.

(** As `init_entry//4`: a constructor or destructor table entry, as
    clang's Fil-C emits one: a native forwarder in the .init_array
    or .fini_array section, which hands f's function object to the
    runtime to call. *)
Definition init_entry (n : name) (kind prio : term) (f : name) : list line :=
  let fo := function_object_symbol (name_text f) in
  let forwarder := (".L" ++ name_text n ++ "..forwarder")%string in
  match init_runtime kind with
  | None => todo "init kind"
  | Some (ctor, run) =>
      [section_line SText; p2align 4; type_line forwarder "function"; label forwarder;
       ins "lea" "q" [ORip (payload_of fo); reg "rdi"];
       ins "mov" "q" [reg "rdi"; reg "rsi"];
       ins0 "jmp" [plt run]]
      ++ match init_priority prio with
         | Some p => [section_line (SInit ctor p)]
         | None => todo "init priority"
         end
      ++ [p2align 3; quad_sym forwarder]
  end.

(** ## Items *)

(** As `item//2` on `data(Name, Linkage, Align, Items)`. *)
Definition data_lines (n : name) (lk : Syntax.linkage) (align : Z) (items : list data_item)
  : list line :=
  match lk, items with
  | LTls l, _ => thread_local_object n l align items
  | LInit kind prio, [Sym f 0] => init_entry n kind prio f
  | LExternWeak, [] => [Dir (DWeak (LSym (getter_symbol (name_text n))))]
  | _, _ => data_object n lk align items
  end.

(** Whether the module defines the name target with a linkage that
    keeps its getter local: a `local` function, or `local`,
    `ro(local)` or `tls(local)` data. *)
Definition alias_target_local (sy : symbols) (target : name) : bool :=
  match nm_find target (sy_funcs sy) with
  | Some fe => is_atom "local" (fe_linkage fe)
  | None => false
  end
  || match nm_find target (sy_data sy) with
     | Some LLocal => true
     | Some (LRo l) | Some (LTls l) => is_atom "local" l
     | _ => false
     end.

(** As `alias_getter//4`, with sy the symbols of the module: an
    alias's getter returns its target's getter's result, so the
    alias's function or data object is the target's. It calls the
    target's getter, directly when the target is local, else through
    the PLT, with the stack kept 16-aligned. *)
Definition alias_lines (sy : symbols) (n : name) (lk : term) (target : name) : list line :=
  let getter := getter_symbol (name_text n) in
  let tg := getter_symbol (name_text target) in
  let op := if alias_target_local sy target then sym tg else plt tg in
  [section_line SText]
  ++ data_linkage_globl lk getter
  ++ [type_line getter "function"; label getter;
      ins "push" "q" [reg "rax"];
      ins0 "call" [op];
      ins "pop" "q" [reg "rcx"];
      ins0 "ret" []].

(** ## Examples *)

Example weak_declaration :
  data_lines (TAtom "f") LExternWeak 1 [] = [Dir (DWeak (LSym "pizlonated_f"))].
Proof. reflexivity. Qed.

Example payload_pointer_after_bytes :
  payload_items [Item Ww (-1); Zero 4; Sym (TAtom "g") 8; Item Wb 300] 0 []
  = ([long 4294967295; zero 4; quad_int 0; Dir (DByte (LInt 44) [])], 17,
     [mkReloc 8 (TAtom "g") 8]).
Proof. reflexivity. Qed.

Example payload_unaligned_pointer :
  first_todo (fst (fst (payload_items [Item Wb 1; Sym (TAtom "g") 0] 0 [])))
  = Some "pointer data item is not 8-aligned".
Proof. reflexivity. Qed.

Example payload_other_linkage :
  data_lines (TAtom "d") (LOther (TAtom "common")) 8 [Zero 8] = todo "data linkage".
Proof. reflexivity. Qed.

Example thread_local_other_item :
  first_todo (data_lines (TAtom "d") (LTls (TAtom "local")) 8 [ItemOther (TAtom "x")])
  = Some "data item".
Proof. reflexivity. Qed.

Example relocation_table :
  relocations [mkReloc 0 (TAtom "g") 0; mkReloc 8 (TAtom "h") (-1)] "d"
  = [quad_int 0; long 0; zero 4; quad_sym "pizlonated_g";
     quad_int 8; long 1; zero 4; quad_sym ".Lpizlonated_d..node1";
     label ".Lpizlonated_d..node1"; long 0; long 0; quad_sym "pizlonated_h";
     quad_int 18446744073709551615].
Proof. reflexivity. Qed.
