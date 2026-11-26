(** The arena driver for the Gallina C frontend and lowering passes mirrors
    nanofil/anf/backend/Drive.v. It runs CPp, CLex, CParse, CTypes, CLaunder,
    CLower, and CLayouts inside the 32-bit arena, streaming canonical Prolog
    terms, IR clauses, and record layouts via [Chunk] and requesting file reads,
    existence checks, canonical paths, and feature queries via [NeedRead],
    [NeedExists], [NeedReal], and [NeedFeat]. *)

From Stdlib Require Import String List Ascii ZArith Arith Bool.
From Nanofil Require Import Term.
From Frontend Require Import CAst CAttrs CLex CParse CCanon CPp
  CTypeAst CLowerState CLower CLayouts.
Import ListNotations.
Local Open Scope string_scope.

(** Arguments passed from C into [run] or a [Ready] closure. *)
Record args := mkargs {
  arg_cmd : nat;
  arg_filename : string;
  arg_input : list string;
  arg_extra : list string;
}.

(** A streaming and I/O resumption result matching nanofil/anf/frontend/driver.c:
    every constructor has arity at least 1, so constructor ordinals are 0..6. *)
Inductive out : Type :=
| Done (code : nat) (why : string)
| Chunk (ps : list string) (next : unit -> out)
| NeedRead (path : string) (next : nat * list string -> out)
| NeedExists (path : string) (next : nat -> out)
| NeedReal (path : string) (next : string -> out)
| NeedFeat (op name : string) (next : string -> out)
| Ready (k : args -> out).

Definition text_of (l : list string) : list ascii :=
  rev_append (fold_left (fun acc s => rev_append (list_ascii_of_string s) acc) l []) [].

Definition nl_str : string := string_of_rev ["010"%char].

Fixpoint stream_list {A : Type} (f : A -> list string -> list string)
  (first : bool) (xs : list A) : out :=
  match xs with
  | [] => Chunk ["]"; "."; nl_str] (fun _ => Done 0 "")
  | x :: rest =>
      let a0 := if first then ["["] else [","] in
      let ps := rev_append (f x a0) [] in
      Chunk ps (fun _ => stream_list f false rest)
  end.

Definition emit_list_stream {A : Type} (f : A -> list string -> list string)
  (xs : list A) : out :=
  match xs with
  | [] => Chunk ["[]."; nl_str] (fun _ => Done 0 "")
  | _ => stream_list f true xs
  end.

(** Interpret a pure [pp_step] computation into the arena driver's [out]
    resumption protocol. *)
Fixpoint drive_pp_step {A : Type} (s : pp_step A) (k : c_result A -> out) : out :=
  match s with
  | PPDone r => k r
  | PPReadFile path cont =>
      NeedRead path (fun p =>
        let '(found, pieces) := p in
        let ocs := if Nat.eqb found 0 then None else Some (text_of pieces) in
        drive_pp_step (cont ocs) k)
  | PPFileExists path cont =>
      NeedExists path (fun flag =>
        drive_pp_step (cont (negb (Nat.eqb flag 0))) k)
  | PPRealPath path cont =>
      NeedReal path (fun realp =>
        drive_pp_step (cont realp) k)
  | PPQueryFeature op name cont =>
      NeedFeat op name (fun ans =>
        drive_pp_step (cont ans) k)
  end.

(** Split a space-delimited feature triple `"op name val"` into a
    [feature_entry]. *)
Fixpoint split_spaces_acc (cs cur : list ascii) (acc : list string)
  : list string :=
  match cs with
  | [] =>
      match cur with
      | [] => rev_append acc []
      | _ => rev_append (string_of_rev cur :: acc) []
      end
  | c :: rest =>
      if Ascii.eqb c " "%char then
        match cur with
        | [] => split_spaces_acc rest [] acc
        | _ => split_spaces_acc rest [] (string_of_rev cur :: acc)
        end
      else split_spaces_acc rest (c :: cur) acc
  end.

Definition parse_extra_items (extra : list string)
  : list string * list string * list feature_entry :=
  let fix go (xs incs defs : list string) (feats : list feature_entry) :=
    match xs with
    | [] => (rev_append incs [], rev_append defs [], rev_append feats [])
    | s :: rest =>
        match list_ascii_of_string s with
        | tag :: tail_cs =>
            let tail_s := string_of_rev (rev_append tail_cs []) in
            if Ascii.eqb tag "I"%char then
              go rest (tail_s :: incs) defs feats
            else if Ascii.eqb tag "D"%char then
              go rest incs (tail_s :: defs) feats
            else if Ascii.eqb tag "F"%char then
              match split_spaces_acc tail_cs [] [] with
              | [op; nm; v] =>
                  go rest incs defs (mkFeat op nm v :: feats)
              | _ => go rest incs defs feats
              end
            else go rest incs defs feats
        | [] => go rest incs defs feats
        end
    end in
  go extra [] [] [].

Definition build_pp_env (a : args) : pp_env :=
  let defs_cs := text_of (arg_input a) in
  let dirs := parse_include_dirs (list_ascii_of_string (arg_filename a)) in
  let '(incs, cli_defs, feats) := parse_extra_items (arg_extra a) in
  let env0 := make_pp_env defs_cs dirs feats "<input>" in
  let env1 := match incs with [] => env0 | _ => prepend_include_dirs incs env0 end in
  fold_left (fun e spec => add_cli_define spec e) cli_defs env1.

Definition parse_lower_opts (extra : list string) : c_lower_opts :=
  let fix go (xs : list string) (vecs gnu89 comm merr : bool) : c_lower_opts :=
    match xs with
    | [] => mkCLowerOpts vecs gnu89 comm merr
    | s :: rest =>
        if String.eqb s "V0" then go rest false gnu89 comm merr
        else if String.eqb s "G1" then go rest vecs true comm merr
        else if String.eqb s "C1" then go rest vecs gnu89 true merr
        else if String.eqb s "M0" then go rest vecs gnu89 comm false
        else go rest vecs gnu89 comm merr
    end in
  go extra true false false true.

Fixpoint stream_ir_items (items : list term) : out :=
  match items with
  | [] => Done 0 ""
  | it :: rest =>
      Chunk [ir_item_line it] (fun _ => stream_ir_items rest)
  end.

Definition run_lower_items (c : nat) (opts : c_lower_opts) (items : list c_item) : out :=
  match c_module_opts opts items with
  | TErr err => Done 1 ("lower error: " ++ l_tr_msg unknown_loc err)
  | TOk res =>
      if Nat.eqb c 8 || Nat.eqb c 9 then
        Chunk [module_layouts_canon (cm_env res) (cm_items res); nl_str] (fun _ => Done 0 "")
      else if Nat.eqb c 10 then
        let ni := z_to_string (Z.of_nat (List.length (cm_items res))) in
        Chunk ["ok "; ni; nl_str] (fun _ => Done 0 "")
      else
        stream_ir_items (cm_items res)
  end.

(** Run a preprocessor command against a prebuilt [pp_env]:
    `0` pp, `1` pp-c23, `2` pp-parse, `3` pp-parse-c23, `4` pp-count,
    `5` pp-only-count, `6` pp-cc-ir, `7` pp-cc-ir-c23, `8` pp-cc-layouts,
    `9` pp-cc-layouts-c23, `10` pp-cc-ir-count. *)
Definition run_with_env (base_env : pp_env) (a : args) : out :=
  let c := arg_cmd a in
  let fname := arg_filename a in
  let opts := parse_lower_opts (arg_extra a) in
  drive_pp_step (preprocess_file fname base_env) (fun res =>
    match res with
    | CErr msg => Done 1 ("pp error: " ++ msg)
    | COk ts0 =>
        let is_c23 := Nat.eqb c 1 || Nat.eqb c 3 || Nat.eqb c 7 || Nat.eqb c 9 in
        let ts := if is_c23 then c23_tokens ts0 else ts0 in
        if Nat.eqb c 0 || Nat.eqb c 1 then
          emit_list_stream emit_token ts
        else if Nat.eqb c 5 then
          let nt := z_to_string (Z.of_nat (List.length ts)) in
          Chunk ["ok "; nt; " 0"; nl_str] (fun _ => Done 0 "")
        else
          match c_parse ts with
          | CErr msg => Done 1 ("parse error: " ++ msg)
          | COk items =>
              if Nat.eqb c 4 then
                let nt := z_to_string (Z.of_nat (List.length ts)) in
                let ni := z_to_string (Z.of_nat (List.length items)) in
                Chunk ["ok "; nt; " "; ni; nl_str] (fun _ => Done 0 "")
              else if Nat.eqb c 2 || Nat.eqb c 3 then
                emit_list_stream emit_item items
              else
                run_lower_items c opts items
          end
    end).

(** Run the selected frontend command:
    `0` lex, `1` lex-c23, `2` parse, `3` parse-c23, `4` count, `5` build-env,
    `6` cc-ir, `7` cc-ir-c23, `8` cc-layouts, `9` cc-layouts-c23,
    `10` cc-ir-count. *)
Definition run (a : args) : out :=
  let c := arg_cmd a in
  if Nat.eqb c 5 then
    let env := build_pp_env a in
    Ready (run_with_env env)
  else
    let opts := parse_lower_opts (arg_extra a) in
    let cs := text_of (arg_input a) in
    match lex_chars (arg_filename a) cs with
    | CErr msg => Done 1 ("lex error: " ++ msg)
    | COk ts0 =>
        let is_c23 := Nat.eqb c 1 || Nat.eqb c 3 || Nat.eqb c 7 || Nat.eqb c 9 in
        let ts := if is_c23 then c23_tokens ts0 else ts0 in
        if Nat.eqb c 0 || Nat.eqb c 1 then
          emit_list_stream emit_token ts
        else
          match c_parse ts with
          | CErr msg => Done 1 ("parse error: " ++ msg)
          | COk items =>
              if Nat.eqb c 4 then
                let nt := z_to_string (Z.of_nat (List.length ts)) in
                let ni := z_to_string (Z.of_nat (List.length items)) in
                Chunk ["ok "; nt; " "; ni; nl_str] (fun _ => Done 0 "")
              else if Nat.eqb c 2 || Nat.eqb c 3 then
                emit_list_stream emit_item items
              else
                run_lower_items c opts items
          end
    end.
