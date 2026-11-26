(** This module processes top-level module assembly directives and lowers GNU
    inline assembly statements for the Gallina C frontend.

    It ports the top-level `.symver` and `.filc_*` directive handling from
    nanofil/src/c_lower.pl alongside the blank memory barrier, fixed-register
    instruction lowering, and Fil-C runtime refusal checks for unsupported
    inline assembly mnemonics. *)

From Stdlib Require Import String ZArith List Bool Ascii Arith.
From Nanofil Require Import Term Maps.
From Backend Require Import Text Order Pizlonate.
From Frontend Require Import CAst CAttrs CLex CIeee CParse CCanon CPp
  CTypeAst CTypeTables CTypes CLowerState.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(** String equality, matching Prolog's `==`. *)
Local Notation "a == b" := (String.eqb a b) (at level 70).

(** ## Splitting and normalizing assembly lines *)

Definition split_bytes_at (seps : list Z) (bs : list Z) : list (list Z) :=
  let fix go (xs cur : list Z) (acc : list (list Z)) : list (list Z) :=
    match xs with
    | [] => rev (rev cur :: acc)
    | b :: rest =>
        if existsb (Z.eqb b) seps then go rest [] (rev cur :: acc)
        else go rest (b :: cur) acc
    end in
  go bs [] [].

Definition is_ws_byte (b : Z) : bool :=
  Z.eqb b 32 || Z.eqb b 9 || Z.eqb b 10 || Z.eqb b 11 || Z.eqb b 12 || Z.eqb b 13.

Definition normalize_space_bytes (bs : list Z) : string :=
  let fix go (xs : list Z) (in_sp started : bool) (acc : list ascii) : string :=
    match xs with
    | [] => string_of_rev acc
    | b :: rest =>
        if is_ws_byte b then go rest started started acc
        else
          let acc1 := if in_sp then " "%char :: acc else acc in
          go rest false true (byte (Z.to_nat (Z.modulo b 256)) :: acc1)
    end in
  go bs false false [].

Definition split_spaces (s : string) : list string :=
  let fix go (cs cur : list ascii) (acc : list string) : list string :=
    match cs with
    | [] =>
        match cur with
        | [] => rev acc
        | _ => rev (string_of_rev cur :: acc)
        end
    | c :: rest =>
        if Ascii.eqb c " "%char then
          match cur with
          | [] => go rest [] acc
          | _ => go rest [] (string_of_rev cur :: acc)
          end
        else go rest (c :: cur) acc
    end in
  go (list_ascii_of_string s) [] [].

Definition split_on_substr (sep s : string) : list string :=
  let ls := String.length s in
  let lp := String.length sep in
  if Nat.eqb lp 0 then [s]
  else
    let fix go (fuel i cur_start : nat) (acc : list string) : list string :=
      match fuel with
      | O => rev (String.substring cur_start (ls - cur_start) s :: acc)
      | S f =>
          if (ls <? i + lp)%nat then
            rev (String.substring cur_start (ls - cur_start) s :: acc)
          else if String.eqb (String.substring i lp s) sep then
            let part := String.substring cur_start (i - cur_start) s in
            go f (i + lp)%nat (i + lp)%nat (part :: acc)
          else go f (S i) cur_start acc
      end in
    go (S ls) 0%nat 0%nat [].

(** ## Top-level module asm directives

    Top-level assembly lines support `.symver`, `.filc_symver`, `.filc_rename`,
    `.filc_alias`, `.filc_weak_alias`, `.filc_weak`, and `.filc_globl`, matching
    FilPizlonator's MATokenizer and `compileModuleAsm`. *)

Inductive ma_dir : Type :=
| MADNone
| MADSymver (l v : string)
| MADGlobl (n : string)
| MADWeak (n : string)
| MADRename (old_n new_n : string)
| MADAlias (old_n new_n lnk : string).

Definition is_ma_white (c : ascii) : bool :=
  let n := code c in
  Nat.eqb n 32 || Nat.eqb n 9 || Nat.eqb n 11 || Nat.eqb n 12 || Nat.eqb n 13.

Fixpoint drop_ma_blank (cs : list ascii) : list ascii :=
  match cs with
  | c :: rest => if is_ma_white c then drop_ma_blank rest else c :: rest
  | [] => []
  end.

Definition is_ma_id_start (c : ascii) : bool :=
  let n := code c in
  ((65 <=? n)%nat && (n <=? 90)%nat)
  || ((97 <=? n)%nat && (n <=? 122)%nat)
  || Nat.eqb n 95.

Definition is_ma_id_char (c : ascii) : bool :=
  let n := code c in
  is_ma_id_start c || ((48 <=? n)%nat && (n <=? 57)%nat)
  || Nat.eqb n 36 || Nat.eqb n 64 || Nat.eqb n 46.

Definition read_ma_id (cs : list ascii) : option (string * list ascii) :=
  match cs with
  | c :: rest =>
      if is_ma_id_start c then
        let fix go (l acc : list ascii) :=
          match l with
          | x :: xr => if is_ma_id_char x then go xr (x :: acc) else (string_of_rev acc, l)
          | [] => (string_of_rev acc, [])
          end in
        Some (go rest [c])
      else None
  | [] => None
  end.

Definition skip_ma_zero_offset (cs : list ascii) : list ascii :=
  match cs with
  | c :: rest =>
      if Ascii.eqb c "+"%char then
        match drop_ma_blank rest with
        | z :: zr =>
            if Ascii.eqb z "0"%char then
              let fix drop_zeros (l : list ascii) :=
                match l with
                | x :: xr => if Ascii.eqb x "0"%char then drop_zeros xr else l
                | [] => []
                end in
              drop_ma_blank (drop_zeros zr)
            else cs
        | [] => cs
        end
      else cs
  | [] => []
  end.

Definition parse_ma_directive (cs0 : list ascii) : option ma_dir :=
  match drop_ma_blank cs0 with
  | [] => Some MADNone
  | c :: rest =>
      if Ascii.eqb c "."%char then
        match read_ma_id rest with
        | Some (word, w :: rest1) =>
            if is_ma_white w then
              match read_ma_id (drop_ma_blank rest1) with
              | Some (a, rest2) =>
                  let rest3 := skip_ma_zero_offset (drop_ma_blank rest2) in
                  match rest3 with
                  | [] =>
                      if word == "filc_weak" then Some (MADWeak a)
                      else if word == "filc_globl" then Some (MADGlobl a)
                      else None
                  | sep :: rest4 =>
                      if Ascii.eqb sep ","%char then
                        match read_ma_id (drop_ma_blank rest4) with
                        | Some (b, rest5) =>
                            match drop_ma_blank rest5 with
                            | [] =>
                                if (word == "symver") || (word == "filc_symver") then
                                  Some (MADSymver a b)
                                else if word == "filc_rename" then Some (MADRename a b)
                                else if word == "filc_alias" then Some (MADAlias a b "export")
                                else if word == "filc_weak_alias" then Some (MADAlias a b "weak")
                                else None
                            | _ => None
                            end
                        | None => None
                        end
                      else None
                  end
              | None => None
              end
            else None
        | _ => None
        end
      else None
  end.

Definition has_filc_nonzero_offset (cs0 : list ascii) : bool :=
  let s := string_of_rev (rev (drop_ma_blank cs0)) in
  match strip_prefix ".filc_" s with
  | Some rest_s =>
      match read_ma_id (list_ascii_of_string rest_s) with
      | Some (_, rest1) =>
          match read_ma_id (drop_ma_blank rest1) with
          | Some (_, rest2) =>
              match drop_ma_blank rest2 with
              | c :: _ => Ascii.eqb c "+"%char
              | [] => false
              end
          | None => false
          end
      | None => false
      end
  | None => false
  end.

Definition module_asm_directive (loc : c_loc) (line_bs : list Z) : c_tr ma_dir :=
  let s := bytes_to_string line_bs in
  let cs := list_ascii_of_string s in
  match parse_ma_directive cs with
  | Some d => TOk d
  | None =>
      if has_filc_nonzero_offset cs then
        sema_err loc ("top-level asm """ ++ s ++ """: an alias at an offset is not supported")
      else
        sema_err loc ("top-level asm """ ++ s ++
                      """ is not supported; only .symver and .filc_rename, .filc_alias, .filc_weak_alias, .filc_weak and .filc_globl are")
  end.

Definition module_asm_lines (items : list c_item) : list (c_loc * list Z) :=
  flat_map (fun it =>
              match it with
              | IToplevelAsm loc tpl => map (fun l => (loc, l)) (split_bytes_at [10] tpl)
              | _ => []
              end) items.

Definition c_toplevel_asm (items : list c_item) : c_tr (list string) :=
  let fix go (ps : list (c_loc * list Z)) (acc : list string) :=
    match ps with
    | [] => TOk (rev acc)
    | (loc, line_bs) :: rest =>
        match module_asm_directive loc line_bs with
        | TErr err => TErr err
        | TOk (MADSymver la va) =>
            go rest ((".symver pizlonated_" ++ la ++ ", pizlonated_" ++ va) :: acc)
        | TOk (MADGlobl n) =>
            go rest ((".globl pizlonated_" ++ n) :: acc)
        | TOk _ => go rest acc
        end
    end in
  go (module_asm_lines items) [].

Definition symver_default_target (v : string) : option string :=
  match split_on_substr "@@" v with
  | [nm; ver] =>
      if (0 <? String.length nm)%nat && (0 <? String.length ver)%nat
         && negb (contains_substr "@" nm) && negb (contains_substr "@" ver) then
        Some nm
      else None
  | _ => None
  end.

Definition filc_directives (items : list c_item) : c_tr (list (c_loc * ma_dir)) :=
  let fix go (ps : list (c_loc * list Z)) (acc : list (c_loc * ma_dir)) :=
    match ps with
    | [] => TOk (rev acc)
    | (loc, line_bs) :: rest =>
        match module_asm_directive loc line_bs with
        | TErr err => TErr err
        | TOk MADNone => go rest acc
        | TOk (MADSymver l v) =>
            match symver_default_target v with
            | Some nm =>
                if nm == l then go rest acc
                else go rest ((loc, MADAlias l nm "export") :: acc)
            | None => go rest acc
            end
        | TOk d => go rest ((loc, d) :: acc)
        end
    end in
  go (module_asm_lines items) [].

Definition symver_default_names (lines : list string) : list string :=
  flat_map
    (fun line =>
       match strip_prefix ".symver pizlonated_" line with
       | Some rest =>
           match split_on_substr ", pizlonated_" rest with
           | [l_nm; v_nm] =>
               match symver_default_target v_nm with
               | Some nm => if nm == l_nm then [] else [nm]
               | None => []
               end
           | _ => []
           end
       | None => []
       end)
    lines.

Definition without_symver_aliases (asm_lines : list string) (items : list term) : list term :=
  let names := symver_default_names asm_lines in
  match names with
  | [] => items
  | _ =>
      filter (fun it =>
                match it with
                | TApp f [TAtom n; _; _] => negb ((f == "alias") && str_mem n names)
                | _ => true
                end) items
  end.

(** ## Applying module-level symbol directives

    Symbol identities are represented as [term] (`TAtom sym` for original
    symbols and `TApp "alias_symbol" [TAtom new; Term.TInt n]` for directive-created
    aliases) so later renames move alias targets identically to FilPizlonator. *)

Definition ir_item_symbol (it : term) : option term :=
  match it with
  | TApp f (s :: _) =>
      if (f == "func") || (f == "data") || (f == "alias") then Some s else None
  | _ => None
  end.

Fixpoint collect_symbol_refs (t : term) (acc : list term) : list term :=
  match t with
  | TApp f [TAtom s] => if f == "global" then TAtom s :: acc else acc
  | TApp f [TAtom s; _] => if f == "sym" then TAtom s :: acc else acc
  | TApp _ args => fold_left (fun a x => collect_symbol_refs x a) args acc
  | TList xs => fold_left (fun a x => collect_symbol_refs x a) xs acc
  | _ => acc
  end.

Record dir_alias : Type := mkDirAlias {
  da_id : term;
  da_link : string;
  da_target : term;
}.

Definition defined_id_target (items0 : list term) (aliases : list dir_alias)
  (id : term) : option term :=
  match find (fun a => term_eqb (da_id a) id) aliases with
  | Some a => Some (da_target a)
  | None =>
      let fix go (l : list term) : option term :=
        match l with
        | [] => None
        | it :: rest =>
            match it with
            | TApp f [s; _; _; _; _] =>
                if (f == "func") && term_eqb s id then Some id else go rest
            | TApp f [s; lnk; _; _] =>
                if (f == "data") && term_eqb s id
                   && negb (term_eqb lnk (TApp "extern" [TAtom "weak"])) then Some id
                else go rest
            | TApp f [s; _; tgt] =>
                if (f == "alias") && term_eqb s id then Some tgt else go rest
            | _ => go rest
            end
        end in
      go items0
  end.

Definition cur_lookup (cur : list (string * term)) (n : string) : option term :=
  match find (fun p => fst p == n) cur with Some (_, id) => Some id | None => None end.

Definition cur_remove (cur : list (string * term)) (n : string) : list (string * term) :=
  filter (fun p => negb (fst p == n)) cur.

Definition cur_put (cur : list (string * term)) (n : string) (id : term) : list (string * term) :=
  (n, id) :: cur_remove cur n.

Definition final_symbol (fin : nmap string) (s0 : term) : string :=
  match nm_find s0 fin with
  | Some s => s
  | None => match s0 with TAtom a => a | _ => "" end
  end.

Fixpoint rename_refs_term (fin : nmap string) (t : term) : term :=
  match t with
  | TApp f [TAtom s] =>
      if f == "global" then ir_global (final_symbol fin (TAtom s))
      else TApp f [TAtom s]
  | TApp f [TAtom s; o] =>
      if f == "sym" then TApp "sym" [TAtom (final_symbol fin (TAtom s)); o]
      else TApp f [TAtom s; rename_refs_term fin o]
  | TApp f args => TApp f (map (rename_refs_term fin) args)
  | TList xs => TList (map (rename_refs_term fin) xs)
  | _ => t
  end.

Definition rename_item_term (fin : nmap string) (it : term) : term :=
  match it with
  | TApp f [s0; l; r; ps; bs0] =>
      if f == "func" then
        TApp "func" [TAtom (final_symbol fin s0); l; r; ps; rename_refs_term fin bs0]
      else it
  | TApp f [s0; l; a; is0] =>
      if f == "data" then
        TApp "data" [TAtom (final_symbol fin s0); l; a; rename_refs_term fin is0]
      else it
  | TApp f [s0; l; t0] =>
      if f == "alias" then
        TApp "alias" [TAtom (final_symbol fin s0); l; TAtom (final_symbol fin t0)]
      else it
  | TApp f [s0; rs] =>
      if f == "context" then TApp "context" [TAtom (final_symbol fin s0); rs]
      else it
  | _ => it
  end.

Definition apply_item_linkage (lnk : string) (it : term) : c_tr term :=
  match it with
  | TApp f [s; l0; r; ps; bs] =>
      if f == "func" then
        let l1 :=
          if lnk == "weak" then TAtom "weak"
          else if is_atom "local" l0 then TAtom "export"
          else l0 in
        TOk (TApp "func" [s; l1; r; ps; bs])
      else TOk it
  | TApp f [s; l0; a; is0] =>
      if f == "data" then
        if lnk == "weak" then
          if is_atom "export" l0 || is_atom "local" l0 || is_atom "weak" l0 then
            TOk (TApp "data" [s; TAtom "weak"; a; is0])
          else if term_eqb l0 (TApp "ro" [TAtom "export"])
                  || term_eqb l0 (TApp "ro" [TAtom "local"])
                  || term_eqb l0 (TApp "ro" [TAtom "weak"]) then
            TOk (TApp "data" [s; TApp "ro" [TAtom "weak"]; a; is0])
          else TErr (TESema ".filc_weak of data of unsupported linkage")
        else
          let l1 :=
            if is_atom "local" l0 then TAtom "export"
            else if term_eqb l0 (TApp "ro" [TAtom "local"]) then TApp "ro" [TAtom "export"]
            else if term_eqb l0 (TApp "tls" [TAtom "local"]) then TApp "tls" [TAtom "export"]
            else l0 in
          TOk (TApp "data" [s; l1; a; is0])
      else TOk it
  | TApp f [s; _; t] =>
      if f == "alias" then TOk (TApp "alias" [s; TAtom lnk; t]) else TOk it
  | _ => TOk it
  end.

Definition module_asm_symbols (ds : list (c_loc * ma_dir)) (items0 : list term)
  : c_tr (list term * nmap string) :=
  match ds with
  | [] => TOk (items0, nm_empty)
  | _ =>
      let named := flat_map (fun it => match ir_item_symbol it with Some s => [s] | None => [] end) items0 in
      let refs := fold_left (fun a it => collect_symbol_refs it a) items0 [] in
      let sym_names :=
        fold_left (fun acc t =>
                     match t with
                     | TAtom a => if str_mem a acc then acc else a :: acc
                     | _ => acc
                     end) (app named refs) [] in
      let cur0 := map (fun a => (a, TAtom a)) sym_names in
      let fix step_dirs (xs : list (c_loc * ma_dir))
        (cur : list (string * term)) (merged : list (term * term))
        (aliases : list dir_alias) (links : list (term * string)) :=
        match xs with
        | [] => TOk (cur, merged, aliases, links)
        | (loc, MADRename old_n new_n) :: rest =>
            match cur_lookup cur old_n with
            | Some id =>
                match cur_lookup cur new_n with
                | Some _ => sema_err loc ("cannot rename " ++ old_n ++ " to " ++ new_n ++ ", which is taken")
                | None => step_dirs rest (cur_put (cur_remove cur old_n) new_n id) merged aliases links
                end
            | None => step_dirs rest cur merged aliases links
            end
        | (loc, MADAlias old_n new_n lnk) :: rest =>
            match opt_bind (cur_lookup cur old_n) (defined_id_target items0 aliases) with
            | None =>
                sema_err loc ("alias " ++ new_n ++ " must point to a defined variable or function, not " ++ old_n)
            | Some tgt =>
                match cur_lookup cur new_n with
                | Some new_id =>
                    let same_a :=
                      existsb (fun a => term_eqb (da_id a) new_id && (da_link a == lnk) && term_eqb (da_target a) tgt) aliases
                      || existsb (fun it =>
                                    match it with
                                    | TApp f [s; TAtom l1; t] =>
                                        (f == "alias") && term_eqb s new_id && term_eqb t (match cur_lookup cur old_n with Some oi => oi | None => tgt end)
                                        && Bool.eqb (l1 == "weak") (lnk == "weak")
                                    | _ => false
                                    end) items0 in
                    if same_a then step_dirs rest cur merged aliases links
                    else
                      match defined_id_target items0 aliases new_id with
                      | Some _ => sema_err loc ("alias name " ++ new_n ++ " is already taken by a definition")
                      | None =>
                          let aid := TApp "alias_symbol" [TAtom new_n; Term.TInt (Z.of_nat (length aliases))] in
                          step_dirs rest (cur_put cur new_n aid) ((new_id, tgt) :: merged)
                                    (mkDirAlias aid lnk tgt :: aliases) links
                      end
                | None =>
                    let aid := TApp "alias_symbol" [TAtom new_n; Term.TInt (Z.of_nat (length aliases))] in
                    step_dirs rest (cur_put cur new_n aid) merged
                              (mkDirAlias aid lnk tgt :: aliases) links
                end
            end
        | (loc, MADWeak n) :: rest =>
            match cur_lookup cur n with
            | Some id =>
                match defined_id_target items0 aliases id with
                | Some _ =>
                    let aliases1 :=
                      match find (fun a => term_eqb (da_id a) id) aliases with
                      | Some a =>
                          mkDirAlias (da_id a) "weak" (da_target a)
                          :: filter (fun x => negb (term_eqb (da_id x) id)) aliases
                      | None => aliases
                      end in
                    step_dirs rest cur merged aliases1 ((id, "weak") :: links)
                | None => sema_err loc ("cannot do .filc_weak to " ++ n ++ " because it does not exist")
                end
            | None => sema_err loc ("cannot do .filc_weak to " ++ n ++ " because it does not exist")
            end
        | (_, MADGlobl n) :: rest =>
            match cur_lookup cur n with
            | Some id =>
                match defined_id_target items0 aliases id with
                | Some _ => step_dirs rest cur merged aliases ((id, "export") :: links)
                | None => step_dirs rest cur merged aliases links
                end
            | None => step_dirs rest cur merged aliases links
            end
        | (_, _) :: rest => step_dirs rest cur merged aliases links
        end in
      match step_dirs ds cur0 [] [] [] with
      | TErr err => TErr err
      | TOk (cur, merged, aliases, links) =>
          let f0 :=
            fold_left
              (fun m p =>
                 let '(n, id) := p in
                 if term_eqb (TAtom n) id then m else nm_add id n m)
              cur nm_empty in
          let fin :=
            fold_left
              (fun m p =>
                 let '(id, tgt) := p in
                 let n :=
                   match find (fun q => term_eqb (snd q) tgt) cur with
                   | Some (nm, _) => nm
                   | None => match tgt with TAtom a => a | _ => "" end
                   end in
                 nm_add id n m)
              merged f0 in
          let fix map_items (xs : list term) (acc : list term) :=
            match xs with
            | [] => TOk (rev acc)
            | it :: rest =>
                let drop_weak :=
                  match it with
                  | TApp f [s; lnk; _; TList []] =>
                      (f == "data") && term_eqb lnk (TApp "extern" [TAtom "weak"])
                      && existsb (fun p => term_eqb (fst p) s) merged
                  | _ => false
                  end in
                if drop_weak then map_items rest acc
                else
                  let it1 := rename_item_term fin it in
                  let res_it :=
                    match ir_item_symbol it with
                    | Some s =>
                        match find (fun p => term_eqb (fst p) s) links with
                        | Some (_, lnk) => apply_item_linkage lnk it1
                        | None => TOk it1
                        end
                    | None => TOk it1
                    end in
                  match res_it with
                  | TErr err => TErr err
                  | TOk it2 => map_items rest (it2 :: acc)
                  end
            end in
          match map_items items0 [] with
          | TErr err => TErr err
          | TOk items1 =>
              let alias_items :=
                map (fun a => ir_alias (final_symbol fin (da_id a)) (da_link a)
                                       (final_symbol fin (da_target a)))
                    aliases in
              TOk (app items1 alias_items, fin)
          end
      end
  end.

(** ## Inline assembly classification and fixed-register lowering

    Non-empty inline assembly is classified into three outcomes: a Fil-C
    runtime `zsafety_error` trap, a fixed-register instruction (`cpuid`,
    `xgetbv`, `rdtsc`, `rdtscp`, `lfence`, `sfence`, `pause`, or `mfence`),
    or a compile-time error. *)

Definition asm_fixed_regs (m : string) : option (list string * list string) :=
  if m == "cpuid" then Some (["a"; "c"], ["a"; "b"; "c"; "d"])
  else if m == "xgetbv" then Some (["c"], ["a"; "d"])
  else if m == "rdtsc" then Some ([], ["a"; "d"])
  else if m == "rdtscp" then Some ([], ["a"; "c"; "d"])
  else if (m == "lfence") || (m == "sfence") || (m == "pause") then Some ([], [])
  else None.

Definition asm_value_type (t : c_type) : bool :=
  arithmetic_type t && negb (c_type_eqb t TLDouble).

Inductive asm_op_kind : Type :=
| AOKMem | AOKPtr | AOKValue | AOKVector | AOKOther.

Definition asm_op_kind_eqb (a b : asm_op_kind) : bool :=
  match a with
  | AOKMem => match b with AOKMem => true | _ => false end
  | AOKPtr => match b with AOKPtr => true | _ => false end
  | AOKValue => match b with AOKValue => true | _ => false end
  | AOKVector => match b with AOKVector => true | _ => false end
  | AOKOther => match b with AOKOther => true | _ => false end
  end.

Definition asm_operand_kind (is_out : bool) (env : c_type_env) (loc : c_loc)
  (op : c_asm_op) : c_tr (asm_op_kind * string) :=
  let '(AsmOp c e) := op in
  match elaborate_loc e env loc with
  | TErr err => TErr err
  | TOk None => sema_err loc "cannot elaborate expression"
  | TOk (Some x) =>
      let t := unqualified (tree_type x) in
      let cs := list_ascii_of_string c in
      let has_ch (ch : ascii) := existsb (Ascii.eqb ch) cs in
      let k :=
        if is_out && (has_ch "m"%char || has_ch "g"%char) then AOKMem
        else if negb is_out && (c == "m") then AOKMem
        else
          match t with
          | TPtr _ | TArray _ _ | TFunc _ _ _ => AOKPtr
          | TVec _ _ _ => AOKVector
          | _ => if asm_value_type t then AOKValue else AOKOther
          end in
      TOk (k, c)
  end.

Definition asm_letter_family (r : string) : option string :=
  if r == "a" then Some "ax"
  else if r == "b" then Some "bx"
  else if r == "c" then Some "cx"
  else if r == "d" then Some "dx"
  else if r == "S" then Some "si"
  else if r == "D" then Some "di"
  else None.

Definition asm_register_info (r : string) : option (string * Z) :=
  if (r == "rax") then Some ("ax", 64) else if (r == "eax") then Some ("ax", 32)
  else if (r == "ax") then Some ("ax", 16) else if (r == "al") then Some ("ax", 8)
  else if (r == "rbx") then Some ("bx", 64) else if (r == "ebx") then Some ("bx", 32)
  else if (r == "bx") then Some ("bx", 16) else if (r == "bl") then Some ("bx", 8)
  else if (r == "rcx") then Some ("cx", 64) else if (r == "ecx") then Some ("cx", 32)
  else if (r == "cx") then Some ("cx", 16) else if (r == "cl") then Some ("cx", 8)
  else if (r == "rdx") then Some ("dx", 64) else if (r == "edx") then Some ("dx", 32)
  else if (r == "dx") then Some ("dx", 16) else if (r == "dl") then Some ("dx", 8)
  else if (r == "rsi") then Some ("si", 64) else if (r == "esi") then Some ("si", 32)
  else if (r == "si") then Some ("si", 16) else if (r == "sil") then Some ("si", 8)
  else if (r == "rdi") then Some ("di", 64) else if (r == "edi") then Some ("di", 32)
  else if (r == "di") then Some ("di", 16) else if (r == "dil") then Some ("di", 8)
  else if (r == "rsp") then Some ("sp", 64) else if (r == "esp") then Some ("sp", 32)
  else if (r == "sp") then Some ("sp", 16) else if (r == "spl") then Some ("sp", 8)
  else if (r == "rbp") then Some ("bp", 64) else if (r == "ebp") then Some ("bp", 32)
  else if (r == "bp") then Some ("bp", 16) else if (r == "bpl") then Some ("bp", 8)
  else
    let check_rn (n : Z) : option (string * Z) :=
      let base := "r" ++ decimal n in
      if r == base then Some (base, 64)
      else if r == (base ++ "d") then Some (base, 32)
      else if r == (base ++ "w") then Some (base, 16)
      else if r == (base ++ "b") then Some (base, 8)
      else None in
    let fix try_rns (ns : list Z) :=
      match ns with
      | [] => None
      | n :: rest => match check_rn n with Some res => Some res | None => try_rns rest end
      end in
    try_rns [8; 9; 10; 11; 12; 13; 14; 15].

Definition asm_clobber_name (cl : c_asm_clobber) : option string :=
  match cl with ACName s => Some s | ACLabels _ => None end.

Definition asm_clobber_family (c : string) : option (option string) :=
  if (c == "memory") || (c == "cc") then Some None
  else
    let r := match strip_prefix "%" c with Some s => s | None => c end in
    match asm_register_info r with
    | Some (f, _) => if (f == "sp") || (f == "bp") then None else Some (Some f)
    | None => None
    end.

Fixpoint asm_constraint_split (cs : list ascii) (ps : list ascii)
  : list ascii * list ascii :=
  match cs with
  | c :: rest =>
      if Ascii.eqb c "="%char || Ascii.eqb c "+"%char
         || Ascii.eqb c "&"%char || Ascii.eqb c "%"%char then
        asm_constraint_split rest (c :: ps)
      else (rev ps, cs)
  | [] => (rev ps, [])
  end.

Definition asm_is_digit (c : ascii) : bool :=
  let n := code c in (48 <=? n)%nat && (n <=? 57)%nat.

Definition asm_known_constraint (c : string) : bool :=
  let '(_, body) := asm_constraint_split (list_ascii_of_string c) [] in
  match body with
  | [] => false
  | _ =>
      forallb (fun ch =>
                 let s := string_of_rev [ch] in
                 str_mem s ["r";"m";"g";"i";"n";"e";"N";"q";"Q";"x";"y";"v";"a";"b";"c";"d";"S";"D"]
                 || asm_is_digit ch) body
  end.

Definition asm_ir_constraint (c : string) : string :=
  let '(ps0, body) := asm_constraint_split (list_ascii_of_string c) [] in
  let ps := map (fun ch => if Ascii.eqb ch "+"%char then "=" else string_of_rev [ch]) ps0 in
  let bs :=
    map (fun ch =>
           let s := string_of_rev [ch] in
           if s == "g" then "imr"
           else if s == "a" then "{ax}"
           else if s == "b" then "{bx}"
           else if s == "c" then "{cx}"
           else if s == "d" then "{dx}"
           else if s == "S" then "{si}"
           else if s == "D" then "{di}"
           else s) body in
  String.concat "" (app ps bs).

Definition asm_validated_constraint (ir_c : string) : bool :=
  let '(_, rest) := asm_constraint_split (list_ascii_of_string ir_c) [] in
  let r := string_of_rev (rev rest) in
  str_mem r ["r";"q";"Q";"x";"y";"v";"Yk";"{ax}";"{bx}";"{cx}";"{dx}";"{si}";"{di}"]
  || match rest with [] => false | _ => forallb asm_is_digit rest end.

Definition asm_register_output (c : string) : option (option string) :=
  match list_ascii_of_string c with
  | [p; l] =>
      if Ascii.eqb p "="%char || Ascii.eqb p "+"%char then
        let ls := string_of_rev [l] in
        if ls == "r" then Some None
        else match asm_letter_family ls with Some f => Some (Some f) | None => None end
      else None
  | _ => None
  end.

Definition asm_validated_input (c : string) : bool :=
  if c == "r" then true
  else
    match asm_letter_family c with
    | Some _ => true
    | None =>
        match list_ascii_of_string c with
        | [d] => asm_is_digit d
        | _ => false
        end
    end.

Definition asm_alt_replace (s : string) : string :=
  String.concat ""
    (map (fun c =>
            if Ascii.eqb c "{"%char then "$("
            else if Ascii.eqb c "|"%char then "$|"
            else if Ascii.eqb c "}"%char then "$)"
            else string_of_rev [c]) (list_ascii_of_string s)).

Inductive asm_line_verdict : Type :=
| ALVPassed
| ALVRefused (reason : string)
| ALVUnknown.

Definition check_asm_line (a : string) (covered : list string) : asm_line_verdict :=
  match split_spaces a with
  | [] => ALVPassed
  | w0 :: ops0 =>
      let w := lowercase_string w0 in
      let ops := String.concat "" ops0 in
      if contains_substr "{" w then
        ALVRefused ("unsupported mnemonic for safe inline asm: " ++ asm_alt_replace w)
      else if filcc_refused_mnemonic w then
        ALVRefused ("unsupported mnemonic for safe inline asm: " ++ w)
      else if (w == "cpuid") && (ops == "") then
        let fix check_cpuid (ps : list (string * string)) :=
          match ps with
          | [] => ALVPassed
          | (reg, fam) :: rest =>
              if str_mem fam covered then check_cpuid rest
              else ALVRefused ("cpuid output " ++ reg ++ " not covered by output constraint or clobber")
          end in
        check_cpuid [("eax", "ax"); ("ebx", "bx"); ("ecx", "cx"); ("edx", "dx")]
      else if str_mem w ["xor"; "xorl"; "xorq"; "mov"; "movl"; "movq"] then
        match split_on_substr "%%" ops with
        | [p0; s; d] =>
            if (p0 == "") && ends_with "," s then
              let s1 := String.substring 0 (String.length s - 1) s in
              match asm_register_info s1, asm_register_info d with
              | Some (_, w1), Some (fd, w2) =>
                  if Z.eqb w1 w2 && negb ((fd == "sp") || (fd == "bp")) then
                    if str_mem fd covered then ALVPassed
                    else ALVRefused ("literal register %" ++ d ++ " not covered by output constraint or clobber")
                  else ALVUnknown
              | _, _ => ALVUnknown
              end
            else ALVUnknown
        | _ => ALVUnknown
        end
      else ALVUnknown
  end.

Fixpoint asm_lines_reason (lines : list (list Z)) (covered : list string) : option string :=
  match lines with
  | [] => None
  | l :: rest =>
      let a := normalize_space_bytes l in
      if a == "" then asm_lines_reason rest covered
      else
        match check_asm_line a covered with
        | ALVRefused r => Some r
        | ALVPassed => asm_lines_reason rest covered
        | ALVUnknown => None
        end
  end.

Fixpoint map_option {A B : Type} (f : A -> option B) (xs : list A) : option (list B) :=
  match xs with
  | [] => Some []
  | x :: rest =>
      match f x, map_option f rest with
      | Some y, Some ys => Some (y :: ys)
      | _, _ => None
      end
  end.

Definition asm_runtime_reason (is_goto : bool)
  (out_ks in_ks : list (asm_op_kind * string))
  (clobbers : list string) (tpl : list Z) : option string :=
  let all_ks := app out_ks in_ks in
  if is_goto then
    if existsb (fun p => asm_op_kind_eqb (fst p) AOKMem
                         || asm_op_kind_eqb (fst p) AOKPtr
                         || asm_op_kind_eqb (fst p) AOKOther
                         || asm_op_kind_eqb (fst p) AOKVector) all_ks then None
    else Some "asm goto is not supported"
  else if existsb (fun p => asm_op_kind_eqb (fst p) AOKPtr) out_ks then
    if existsb (fun p => asm_op_kind_eqb (fst p) AOKMem) out_ks then None
    else Some "inline assembly with pointer return type is not supported"
  else if existsb (fun p => asm_op_kind_eqb (fst p) AOKMem) out_ks
          || existsb (fun p => asm_op_kind_eqb (fst p) AOKMem || asm_op_kind_eqb (fst p) AOKPtr) in_ks then
    if existsb (fun p => asm_op_kind_eqb (fst p) AOKOther) all_ks then None
    else Some "inline assembly with pointer argument is not supported"
  else if forallb (fun p => asm_op_kind_eqb (fst p) AOKValue) all_ks
          && forallb (fun p => asm_known_constraint (snd p)) all_ks then
    match find (fun p => negb (asm_validated_constraint (asm_ir_constraint (snd p)))) all_ks with
    | Some (_, c) => Some ("unsupported constraint for safe inline asm: " ++ asm_ir_constraint c)
    | None =>
        match map_option (fun p => asm_register_output (snd p)) out_ks,
              map_option asm_clobber_family clobbers with
        | Some out_fs0, Some clob_fs0 =>
            if forallb (fun p => asm_validated_input (snd p)) in_ks then
              let out_fs := flat_map (fun o => match o with Some f => [f] | None => [] end) out_fs0 in
              let clob_fs := flat_map (fun o => match o with Some f => [f] | None => [] end) clob_fs0 in
              asm_lines_reason (split_bytes_at [10; 59] tpl) (app out_fs clob_fs)
            else None
        | _, _ => None
        end
    end
  else None.

Inductive asm_in_reg : Type :=
| AIRReg (r : string)
| AIRTied (idx : Z).

Definition asm_fixed_output_reg (op : c_asm_op) : option string :=
  let '(AsmOp c _) := op in
  match list_ascii_of_string c with
  | p :: cs =>
      if Ascii.eqb p "="%char || Ascii.eqb p "+"%char then
        match filter (fun ch => negb (Ascii.eqb ch "&"%char)) cs with
        | [r] =>
            let rs := string_of_rev [r] in
            match asm_letter_family rs with Some _ => Some rs | None => None end
        | _ => None
        end
      else None
  | [] => None
  end.

Definition asm_fixed_input_reg (outs : list c_asm_op) (op : c_asm_op) : option asm_in_reg :=
  let '(AsmOp c _) := op in
  match parse_dec_Z c with
  | Some n =>
      if (0 <=? n) && (n <? Z.of_nat (length outs)) then
        match nth_error outs (Z.to_nat n) with
        | Some (AsmOp oc _) =>
            if str_starts_with "=" oc then Some (AIRTied n) else None
        | None => None
        end
      else None
  | None =>
      match list_ascii_of_string c with
      | [r] =>
          let rs := string_of_rev [r] in
          match asm_letter_family rs with Some _ => Some (AIRReg rs) | None => None end
      | _ => None
      end
  end.

Fixpoint is_str_set (xs : list string) : bool :=
  match xs with
  | [] => true
  | x :: rest => negb (str_mem x rest) && is_str_set rest
  end.

Definition asm_fixed_form (tpl : list Z) (outs ins : list c_asm_op)
  (out_ks in_ks : list (asm_op_kind * string)) (clobbers : list string)
  (env : c_type_env) : option (string * list string * list asm_in_reg) :=
  let nonblank :=
    flat_map (fun l =>
                let a := normalize_space_bytes l in
                if a == "" then [] else [lowercase_string a])
             (split_bytes_at [10; 59] tpl) in
  match nonblank with
  | [m] =>
      let writes_opt :=
        if m == "mfence" then Some []
        else match asm_fixed_regs m with Some (_, ws) => Some ws | None => None end in
      match writes_opt with
      | None => None
      | Some writes =>
          let all_val :=
            forallb (fun p => asm_op_kind_eqb (fst p) AOKValue) out_ks
            && forallb (fun p => asm_op_kind_eqb (fst p) AOKValue) in_ks in
          let all_int :=
            forallb (fun op =>
                       let '(AsmOp _ e) := op in
                       match expression_type e env with
                       | Some t0 => int_type (unqualified (value_type t0))
                       | None => false
                       end) (app outs ins) in
          if negb (all_val && all_int) then None
          else
            match map_option asm_fixed_output_reg outs,
                  map_option (asm_fixed_input_reg outs) ins,
                  map_option asm_clobber_family clobbers with
            | Some out_regs, Some in_regs, Some clob_fs0 =>
                let indexed_outs := combine (numlist_Z 0 (Z.of_nat (length outs) - 1)) (combine outs out_regs) in
                let plus_regs :=
                  flat_map (fun p =>
                              let '(_, (AsmOp c _, r)) := p in
                              if str_starts_with "+" c then [r] else []) indexed_outs in
                let in_reg_names :=
                  flat_map (fun ir =>
                              match ir with
                              | AIRReg r => [r]
                              | AIRTied idx =>
                                  match nth_error out_regs (Z.to_nat idx) with Some r => [r] | None => [] end
                              end) in_regs in
                let all_ins := app plus_regs in_reg_names in
                if negb (is_str_set out_regs && is_str_set all_ins) then None
                else
                  let clob_fs := flat_map (fun o => match o with Some f => [f] | None => [] end) clob_fs0 in
                  let out_fs := flat_map (fun r => match asm_letter_family r with Some f => [f] | None => [] end) out_regs in
                  let covered := app out_fs clob_fs in
                  let cov_ok :=
                    if m == "xgetbv" then
                      str_mem "c" all_ins && str_mem "a" out_regs && str_mem "d" out_regs
                    else
                      forallb (fun r =>
                                 match asm_letter_family r with
                                 | Some f => str_mem f covered
                                 | None => false
                                 end) writes in
                  let unwritten_ok :=
                    forallb (fun p =>
                               let '(idx, (AsmOp c _, r)) := p in
                               if str_mem r writes then true
                               else str_starts_with "+" c
                                    || existsb (fun ir => match ir with AIRTied j => Z.eqb j idx | _ => false end) in_regs)
                            indexed_outs in
                  if cov_ok && unwritten_ok then Some (m, out_regs, in_regs) else None
            | _, _, _ => None
            end
      end
  | _ => None
  end.

Definition asm_float_reg (c : string) : bool :=
  str_mem c ["=x"; "+x"; "=t"; "+t"; "=f"; "+f"].

Definition asm_output_type_ok (cls c : string) (t : c_type) (env : c_type_env) : bool :=
  if cls == "mem" then
    negb (is_func_type t) && complete_type t env
    && (if str_mem c ["+mr"; "+rm"; "+g"] then asm_value_type t || is_ptr_type t else true)
  else if cls == "reg" then
    asm_value_type t || ((c == "+r") && is_ptr_type t)
  else
    float_type t.

Record asm_eval_cb : Type := mkAsmEvalCb {
  ae_judged_rval : c_expr -> c_lower_ctx -> c_func_st -> l_res c_val;
  ae_place : c_typed_node -> c_lower_ctx -> c_func_st -> l_res c_place;
}.

Definition place_type_of (p : c_place) : c_type :=
  match p with
  | PLv _ t0 => unqualified t0
  | PBits _ t0 _ _ => unqualified t0
  | PFn _ t0 => unqualified t0
  end.

Definition unsigned_of_size (t : c_type) : option c_type :=
  match int_info t with
  | Some (1, _) => Some TUChar
  | Some (2, _) => Some TUShort
  | Some (4, _) => Some TUInt
  | Some (8, _) => Some TULLong
  | _ => None
  end.

Definition asm_fixed_lowered (cb : asm_eval_cb) (m : string)
  (outs : list c_asm_op) (out_regs : list string)
  (ins : list c_asm_op) (in_regs : list asm_in_reg)
  (ctx : c_lower_ctx) (st0 : c_func_st) : l_res unit :=
  let fix eval_outs (os : list c_asm_op) (rs : list string)
    (ps_acc : list c_place) (pv_acc : list (string * c_val)) (st : c_func_st) :=
    match os, rs with
    | AsmOp c e :: or, r :: rr =>
        match elaborate_loc e (fs_env st) (ctx_loc ctx) with
        | TErr err => LErr (l_tr_msg (ctx_loc ctx) err)
        | TOk None => l_err (ctx_loc ctx) "cannot elaborate expression" st
        | TOk (Some x) =>
            match ae_place cb x ctx st with
            | LErr msg => LErr msg
            | LOk p st1 =>
                if str_starts_with "+" c then
                  match place_read p ctx st1 with
                  | LErr msg => LErr msg
                  | LOk v st2 => eval_outs or rr (p :: ps_acc) ((r, v) :: pv_acc) st2
                  end
                else eval_outs or rr (p :: ps_acc) pv_acc st1
            end
        end
    | _, _ => LOk (rev ps_acc, rev pv_acc) st
    end in
  match eval_outs outs out_regs [] [] st0 with
  | LErr msg => LErr msg
  | LOk (places, plus_vals) st1 =>
      let fix eval_ins (is_ : list c_asm_op) (rs : list asm_in_reg)
        (iv_acc : list (string * c_val)) (tie_acc : list (Z * c_val)) (st : c_func_st) :=
        match is_, rs with
        | AsmOp _ e :: ir, reg :: rr =>
            match ae_judged_rval cb e ctx st with
            | LErr msg => LErr msg
            | LOk v0 st2 =>
                match reg with
                | AIRReg r => eval_ins ir rr ((r, v0) :: iv_acc) tie_acc st2
                | AIRTied n =>
                    let r := match nth_error out_regs (Z.to_nat n) with Some x => x | None => "a" end in
                    let p_opt := nth_error places (Z.to_nat n) in
                    let v_res :=
                      match p_opt, v0 with
                      | Some p, CVal _ ti =>
                          let to := place_type_of p in
                          match type_size_align ti (fs_env st2), type_size_align to (fs_env st2), unsigned_of_size ti with
                          | TOk (si, _), TOk (so, _), Some ui =>
                              if si <? so then convert_val v0 ui st2 else LOk v0 st2
                          | _, _, _ => LOk v0 st2
                          end
                      | None, _ => LOk v0 st2
                      end in
                    match v_res with
                    | LErr msg => LErr msg
                    | LOk v st3 => eval_ins ir rr ((r, v) :: iv_acc) ((n, v) :: tie_acc) st3
                    end
                end
            end
        | _, _ => LOk (rev iv_acc, rev tie_acc) st
        end in
      match eval_ins ins in_regs [] [] st1 with
      | LErr msg => LErr msg
      | LOk (in_vals, ties) st2 =>
          let vals0 := app plus_vals in_vals in
          let '(reads, writes) :=
            if m == "mfence" then ([], [])
            else match asm_fixed_regs m with Some rw => rw | None => ([], []) end in
          let fix build_reads (rs : list string) (acc : list term) (st : c_func_st) :=
            match rs with
            | [] => LOk (rev acc) st
            | r :: rr =>
                match find (fun p => fst p == r) vals0 with
                | Some (_, v) =>
                    match convert_val v TUInt st with
                    | LErr msg => LErr msg
                    | LOk (CVal w0 _) st3 =>
                        let '(w, st4) :=
                          match w0 with
                          | TApp fn [_] =>
                              if fn == "const" then (w0, st3)
                              else
                                let '(CVal _ vt) := v in
                                match type_class vt with
                                | Some k => if k == "l" then l_let "w" (TAtom "copy") [w0] st3 else (w0, st3)
                                | None => (w0, st3)
                                end
                          | _ =>
                              let '(CVal _ vt) := v in
                              match type_class vt with
                              | Some k => if k == "l" then l_let "w" (TAtom "copy") [w0] st3 else (w0, st3)
                              | None => (w0, st3)
                              end
                          end in
                        build_reads rr (ir_edge (TAtom r) w :: acc) st4
                    end
                | None => build_reads rr (ir_edge (TAtom r) (ir_const 0) :: acc) st
                end
            end in
          match build_reads reads [] st2 with
          | LErr msg => LErr msg
          | LOk ir_ins st3 =>
              let written := filter (fun r => str_mem r out_regs) writes in
              let '(ir_outs_rev, st4) :=
                fold_left
                  (fun acc r =>
                     let '(os, s) := acc in
                     let '(t, s1) := l_fresh s in
                     ((r, t) :: os, s1))
                  written ([], st3) in
              let ir_outs_pairs := rev ir_outs_rev in
              let ir_outs := map (fun p => ir_edge (TAtom (fst p)) (snd p)) ir_outs_pairs in
              let st5 :=
                if m == "mfence" then l_emit ir_fence st4
                else l_emit (ir_asm_fixed m ir_ins ir_outs) st4 in
              let fix do_stores (idx : Z) (rs : list string) (ps : list c_place) (st : c_func_st) :=
                match rs, ps with
                | r :: rr, p :: pr =>
                    let t := place_type_of p in
                    let v0 :=
                      match find (fun q => fst q == r) ir_outs_pairs with
                      | Some (_, tmp_v) => CVal tmp_v TUInt
                      | None =>
                          match find (fun q => fst q == r) plus_vals with
                          | Some (_, v) => v
                          | None =>
                              match find (fun q => Z.eqb (fst q) idx) ties with
                              | Some (_, v) => v
                              | None => CVal (ir_const 0) TInt
                              end
                          end
                      end in
                    let v_res :=
                      if c_type_eqb t TBool then
                        match binary_op BAnd v0 (CVal (ir_const 1) TInt) ctx st with
                        | LErr msg => LErr msg
                        | LOk v1 s1 => convert_val v1 TBool s1
                        end
                      else convert_val v0 t st in
                    match v_res with
                    | LErr msg => LErr msg
                    | LOk v s2 =>
                        match place_write p v ctx s2 with
                        | LErr msg => LErr msg
                        | LOk _ s3 => do_stores (idx + 1) rr pr s3
                        end
                    end
                | _, _ => LOk tt st
                end in
              do_stores 0 out_regs places st5
          end
      end
  end.

Definition asm_empty_lowered (cb : asm_eval_cb) (outs ins : list c_asm_op)
  (clobbers : list c_asm_clobber) (is_goto : bool) (ctx : c_lower_ctx)
  (st0 : c_func_st) : l_res unit :=
  let loc := ctx_loc ctx in
  if is_goto then l_err loc "asm goto is not supported" st0
  else
    let bad_clob :=
      find (fun cl =>
              match cl with
              | ACName s => negb ((s == "memory") || (s == "cc"))
              | ACLabels _ => true
              end) clobbers in
    match bad_clob with
    | Some (ACName c) =>
        l_err loc ("an asm clobber other than ""memory"" or ""cc"" is not supported (" ++ c ++ ")") st0
    | Some (ACLabels _) => l_err loc "asm goto is not supported" st0
    | None =>
        let fix eval_outs (os : list c_asm_op) (acc : list c_place) (st : c_func_st) :=
          match os with
          | [] => LOk (rev acc) st
          | AsmOp c e :: rest =>
              let ocls :=
                if (c == "+r") || (c == "=r") then Some "reg"
                else if asm_float_reg c then Some "float"
                else if str_mem c ["=m"; "+m"; "=mr"; "+mr"; "=rm"; "+rm"; "=g"; "+g"] then Some "mem"
                else None in
              match ocls with
              | None => l_err loc ("the asm output constraint """ ++ c ++ """ is not supported") st
              | Some cls =>
                  match elaborate_loc e (fs_env st) loc with
                  | TErr err => LErr (l_tr_msg loc err)
                  | TOk None => l_err loc "cannot elaborate expression" st
                  | TOk (Some x) =>
                      match ae_place cb x ctx st with
                      | LErr msg => LErr msg
                      | LOk p st1 =>
                          match p with
                          | PLv _ t0 =>
                              let t := unqualified t0 in
                              if asm_output_type_ok cls c t (fs_env st1) then
                                eval_outs rest (p :: acc) st1
                              else if cls == "mem" then
                                l_err loc "an asm memory operand must have a complete object type" st1
                              else
                                l_err loc "an asm operand must have integer or floating type" st1
                          | _ =>
                              if cls == "mem" then
                                l_err loc "an asm memory operand must have a complete object type" st1
                              else
                                l_err loc "an asm operand must have integer or floating type" st1
                          end
                      end
                  end
              end
          end in
        match eval_outs outs [] st0 with
        | LErr msg => LErr msg
        | LOk places st1 =>
            let fix eval_ins (is_ : list c_asm_op) (ties : list (c_type * term * term)) (st : c_func_st) :=
              match is_ with
              | [] => LOk (rev ties) st
              | AsmOp c e :: rest =>
                  if str_mem c ["r"; "g"; "i"; "n"; "m"; "x"; "t"; "f"] then
                    if (c == "m") || (c == "g") then
                      let ty_res :=
                        if c == "m" then
                          match elaborate_loc e (fs_env st) loc with
                          | TErr err => LErr (l_tr_msg loc err)
                          | TOk None => l_err loc "cannot elaborate expression" st
                          | TOk (Some x) =>
                              match ae_place cb x ctx st with
                              | LErr msg => LErr msg
                              | LOk (PLv _ t0) st2 => LOk t0 st2
                              | LOk _ st2 => l_err loc "an asm ""m"" operand must be an lvalue" st2
                              end
                          end
                        else
                          match ae_judged_rval cb e ctx st with
                          | LErr msg => LErr msg
                          | LOk (CVal _ t0) st2 => LOk t0 st2
                          end in
                      match ty_res with
                      | LErr msg => LErr msg
                      | LOk t0 st2 =>
                          let t := unqualified t0 in
                          if negb (is_func_type t) && complete_type t (fs_env st2) then
                            eval_ins rest ties st2
                          else l_err loc "an asm memory operand must have a complete object type" st2
                      end
                    else
                      let c_ok :=
                        if (c == "i") || (c == "n") then
                          match const_value e (fs_env st) with TOk _ => true | TErr _ => false end
                        else true in
                      if negb c_ok then
                        l_err loc ("the asm """ ++ c ++ """ operand is not an integer constant") st
                      else
                        match ae_judged_rval cb e ctx st with
                        | LErr msg => LErr msg
                        | LOk (CVal _ t0) st2 =>
                            let t := unqualified t0 in
                            if (c == "x") || (c == "t") || (c == "f") then
                              if float_type t then eval_ins rest ties st2
                              else l_err loc ("an asm """ ++ c ++ """ operand must have floating type") st2
                            else if asm_value_type t || ((c == "r") && is_ptr_type t) then
                              eval_ins rest ties st2
                            else l_err loc "an asm operand must have integer or floating type" st2
                        end
                  else
                    match parse_dec_Z c with
                    | Some n =>
                        match nth_error outs (Z.to_nat n), nth_error places (Z.to_nat n) with
                        | Some (AsmOp oc _), Some (PLv addr t) =>
                            if str_mem oc ["=r"; "=x"; "=t"; "=f"] then
                              match ae_judged_rval cb e ctx st with
                              | LErr msg => LErr msg
                              | LOk (CVal v t1) st2 =>
                                  let u := unqualified t1 in
                                  if c_type_eqb u (unqualified t) && (asm_value_type u || c_type_eqb u TLDouble) then
                                    eval_ins rest ((u, v, addr) :: ties) st2
                                  else l_err loc "an asm input tied to an output must have its integer or floating type" st2
                              end
                            else l_err loc ("the asm input constraint """ ++ c ++ """ is not supported") st
                        | _, _ => l_err loc ("the asm input constraint """ ++ c ++ """ is not supported") st
                        end
                    | None => l_err loc ("the asm input constraint """ ++ c ++ """ is not supported") st
                    end
              end in
            match eval_ins ins [] st1 with
            | LErr msg => LErr msg
            | LOk ties st2 =>
                let fix do_ties (ts : list (c_type * term * term)) (st : c_func_st) :=
                  match ts with
                  | [] => LOk tt st
                  | (u, v, addr) :: rest =>
                      match store_typed u v addr st with
                      | LErr msg => LErr msg
                      | LOk _ st3 => do_ties rest st3
                      end
                  end in
                do_ties ties st2
            end
        end
    end.

Definition asm_stmt_lowered (cb : asm_eval_cb) (tpl : list Z)
  (outs ins : list c_asm_op) (clobbers : list c_asm_clobber) (is_goto : bool)
  (ctx : c_lower_ctx) (st0 : c_func_st) : l_res unit :=
  let loc := ctx_loc ctx in
  let env0 := fs_env st0 in
  let fix map_ops (is_out : bool) (os : list c_asm_op) (acc : list (asm_op_kind * string)) :=
    match os with
    | [] => TOk (rev acc)
    | op :: rest =>
        match asm_operand_kind is_out env0 loc op with
        | TErr err => TErr err
        | TOk kc => map_ops is_out rest (kc :: acc)
        end
    end in
  match map_ops true outs [], map_ops false ins [] with
  | TErr err, _ | _, TErr err => LErr (l_tr_msg loc err)
  | TOk out_ks, TOk in_ks =>
      let clob_names := flat_map (fun c => match asm_clobber_name c with Some s => [s] | None => [] end) clobbers in
      let tpl_s := bytes_to_string tpl in
      match asm_runtime_reason is_goto out_ks in_ks clob_names tpl with
      | Some reason =>
          let msg := string_to_bytes ("cannot handle inline asm (" ++ reason ++ "): " ++ tpl_s) in
          let '(sym, st1) := l_new_literal (LitBytes msg) st0 in
          let eval_eff (os : list c_asm_op) (ks : list (asm_op_kind * string)) (st : c_func_st) :=
            let fix go (a : list c_asm_op) (b : list (asm_op_kind * string)) (s : c_func_st) :=
              match a, b with
              | AsmOp c e :: ar, (k, _) :: br =>
                  if asm_op_kind_eqb k AOKMem || str_starts_with "=" c || str_starts_with "+" c then
                    match elaborate_loc e (fs_env s) loc with
                    | TErr err => LErr (l_tr_msg loc err)
                    | TOk None => l_err loc "cannot elaborate expression" s
                    | TOk (Some x) =>
                        match ae_place cb x ctx s with
                        | LErr msg => LErr msg
                        | LOk _ s1 => go ar br s1
                        end
                    end
                  else
                    match ae_judged_rval cb e ctx s with
                    | LErr msg => LErr msg
                    | LOk _ s1 => go ar br s1
                    end
              | _, _ => LOk tt s
              end in
            go os ks st in
          match eval_eff outs out_ks st1 with
          | LErr msg => LErr msg
          | LOk _ st2 =>
              match eval_eff ins in_ks st2 with
              | LErr msg => LErr msg
              | LOk _ st3 =>
                  let '(addr, st4) := l_let "p" (TAtom "copy") [ir_global sym] st3 in
                  LOk tt (l_emit (ir_call (TAtom "void") (ir_global "zsafety_error") [ir_arg "p" addr]) st4)
              end
          end
      | None =>
          if negb is_goto then
            match asm_fixed_form tpl outs ins out_ks in_ks clob_names env0 with
            | Some (m, out_regs, in_regs) =>
                asm_fixed_lowered cb m outs out_regs ins in_regs ctx st0
            | None =>
                l_err loc ("inline asm """ ++ tpl_s ++ """ is not supported: nanofil cannot check its instructions") st0
            end
          else
            l_err loc ("inline asm """ ++ tpl_s ++ """ is not supported: nanofil cannot check its instructions") st0
      end
  end.
