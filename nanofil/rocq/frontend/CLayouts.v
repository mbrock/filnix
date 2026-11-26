(** This module computes completed C record layouts and per-function record
    reachability tables from the type environment and lowered IR module.

    It ports nanofil/src/c_layouts.pl to pure, zero-axiom Gallina. Given the
    completed type environment and lowered IR items, it emits every completed
    struct or union definition with its flattened field sizes and alignments,
    appends incomplete tagged records, and computes the sorted set of record
    identifiers reachable from each function's provenance context. *)

From Stdlib Require Import String ZArith List Bool Ascii Arith.
From Nanofil Require Import Term.
From Backend Require Import Text Order.
From Frontend Require Import CAst CAttrs CLex CIeee CParse CCanon CPp
  CTypeAst CTypeTables CTypes CLowerState.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Notation "a == b" := (String.eqb a b) (at level 70, no associativity).

(** ## Map enumeration and deterministic ordering

    SWI-Prolog's [gen_assoc/3] enumerates association trees in ascending key
    order. These helpers extract entries from [smap] hash buckets and sort them
    either numerically by record identifier or lexicographically by atom name. *)

Definition smap_entries {A : Type} (m : smap A) : list (string * A) :=
  flat_map snd (CParse.ZMap.elements m).

Fixpoint insert_sorted {A : Type} (cmp : A -> A -> comparison) (x : A) (xs : list A) : list A :=
  match xs with
  | [] => [x]
  | y :: rest =>
      match cmp x y with
      | Gt => y :: insert_sorted cmp x rest
      | _ => x :: xs
      end
  end.

Definition sort_by {A : Type} (cmp : A -> A -> comparison) (xs : list A) : list A :=
  fold_left (fun acc x => insert_sorted cmp x acc) xs [].

Fixpoint dedup_sorted {A : Type} (eqb : A -> A -> bool) (xs : list A) : list A :=
  match xs with
  | [] => []
  | x :: rest =>
      match rest with
      | [] => [x]
      | y :: _ =>
          if eqb x y then dedup_sorted eqb rest else x :: dedup_sorted eqb rest
      end
  end.

Definition sort_Z_uniq (xs : list Z) : list Z :=
  dedup_sorted Z.eqb (sort_by Z.compare xs).

Definition su_kind_atom (k : su_kind) : string :=
  match k with KStruct => "struct" | KUnion => "union" end.

Definition su_kind_eqb_l (a b : su_kind) : bool :=
  match a, b with
  | KStruct, KStruct => true
  | KUnion, KUnion => true
  | _, _ => false
  end.

Definition su_type_of (k : su_kind) (id : su_id) : c_type :=
  match k with KStruct => TStruct id | KUnion => TUnion id end.

(** ## Record names, members, and canonical terms

    Each completed record keeps its original [def/4] layout term alongside
    flattened named fields (direct members first, then fields inside anonymous
    nested structs or unions, matching [c_layouts:member_name/3]). *)

Definition parse_su_int_key (k : string) : option Z :=
  match strip_prefix "#" k with
  | Some rest => parse_dec_Z rest
  | None => None
  end.

Definition record_names_for (env : c_type_env) (kind : su_kind) (id : su_id) : list term :=
  let sc := te_scope env in
  let su := su_type_of kind id in
  let tag_names :=
    sort_by Order.atom_compare
      (flat_map (fun p =>
                   match snd p with
                   | TagSU k' id' =>
                       if su_kind_eqb_l kind k' && su_id_eqb id id' then [fst p] else []
                   | _ => []
                   end) (smap_entries (sc_tags sc))) in
  let typedef_names :=
    sort_by Order.atom_compare
      (flat_map (fun p =>
                   match snd p with
                   | BTypedef ty =>
                       if c_type_eqb ty su then [fst p] else []
                   | _ => []
                   end) (smap_entries (sc_ords sc))) in
  app (map (fun n => TApp "tag" [TAtom (su_kind_atom kind); TAtom n]) tag_names)
      (map (fun n => TApp "typedef" [TAtom n]) typedef_names).

Definition member_layout_to_term (m : c_member_layout) : term :=
  let nm := match ml_name m with Some n => TApp "some" [TAtom n] | None => TAtom "none" end in
  match ml_bits m with
  | MBNone => TApp "m" [nm; c_type_to_term (ml_type m); Term.TInt (ml_off m)]
  | MBBits pos w =>
      TApp "m" [nm; c_type_to_term (ml_type m); Term.TInt (ml_off m);
                TApp "bits" [Term.TInt pos; Term.TInt w]]
  end.

Definition su_def_to_term (d : su_def) : option term :=
  match d with
  | SUDef kind members sz al =>
      Some (TApp "def" [TAtom (su_kind_atom kind);
                        TList (map member_layout_to_term members);
                        Term.TInt sz; Term.TInt al])
  | _ => None
  end.

Fixpoint member_names_f (fuel : nat) (members : list c_member_layout) (defs : smap su_def)
  : list string :=
  match fuel with
  | O => []
  | S f =>
      let direct :=
        flat_map (fun m => match ml_name m with Some n => [n] | None => [] end) members in
      let anon :=
        flat_map (fun m =>
                    match ml_name m, ml_bits m with
                    | None, MBNone =>
                        match ml_type m with
                        | TStruct id | TUnion id =>
                            match smap_find (su_id_key id) defs with
                            | Some (SUDef _ inner _ _) => member_names_f f inner defs
                            | _ => []
                            end
                        | _ => []
                        end
                    | _, _ => []
                    end) members in
      app direct anon
  end.

Definition member_size_align_l (ty : c_type) (env : c_type_env) : option (Z * Z) :=
  match ty with
  | TArray elem ALNone =>
      match type_size_align elem env with
      | TOk (_, al) => Some (0, al)
      | TErr _ => None
      end
  | _ =>
      match type_size_align ty env with
      | TOk p => Some p
      | TErr _ => None
      end
  end.

Definition field_bits_term (b : c_member_bits) : term :=
  match b with
  | MBNone => TAtom "none"
  | MBBits pos w => TApp "bits" [Term.TInt pos; Term.TInt w]
  end.

(** ## Reachable record identifiers

    Reachability walks every [struct(Id)] and [union(Id)] subterm inside a
    function's [context(Sym, Records)] item, then expands each discovered
    record's member types to a fixed point. *)

Fixpoint term_record_ids_acc (t : term) (acc : list Z) : list Z :=
  match t with
  | TApp f [Term.TInt n] =>
      if (f == "struct") || (f == "union") then n :: acc else acc
  | TApp _ args => fold_left (fun a x => term_record_ids_acc x a) args acc
  | TList xs => fold_left (fun a x => term_record_ids_acc x a) xs acc
  | _ => acc
  end.

Fixpoint c_type_record_ids_acc (ty : c_type) (acc : list Z) : list Z :=
  match ty with
  | TStruct (SUInt n) | TUnion (SUInt n) => n :: acc
  | TPtr inner => c_type_record_ids_acc inner acc
  | TArray inner _ => c_type_record_ids_acc inner acc
  | TFunc ret ops _ =>
      let a1 := c_type_record_ids_acc ret acc in
      match ops with
      | None => a1
      | Some ps => fold_left (fun a p => c_type_record_ids_acc p a) ps a1
      end
  | TAtomic su _ => c_type_record_ids_acc su acc
  | TVec el _ _ => c_type_record_ids_acc el acc
  | TQual _ inner => c_type_record_ids_acc inner acc
  | _ => acc
  end.

Definition members_record_ids (ms : list c_member_layout) : list Z :=
  sort_Z_uniq (fold_left (fun a m => c_type_record_ids_acc (ml_type m) a) ms []).

Fixpoint z_in_list (x : Z) (xs : list Z) : bool :=
  match xs with
  | [] => false
  | y :: rest => if Z.eqb x y then true else z_in_list x rest
  end.

Fixpoint reachable_ids_f (fuel : nat) (todo : list Z) (defs : smap su_def)
  (seen : list Z) : list Z :=
  match fuel, todo with
  | O, _ | _, [] => sort_Z_uniq seen
  | S f, id :: rest =>
      if z_in_list id seen then reachable_ids_f f rest defs seen
      else
        let more :=
          match smap_find (su_id_key (SUInt id)) defs with
          | Some (SUDef _ members _ _) => members_record_ids members
          | _ => []
          end in
        reachable_ids_f f (app more rest) defs (id :: seen)
  end.

(** ## Top-level layout table construction and canonical printing

    [module_layouts_term] builds the exact [layouts(Records, Uses)] term, and
    [write_canonical_term] renders it in SWI-Prolog's [write_canonical/1]
    format with no spaces after commas. *)

Definition module_layouts_term (env : c_type_env) (items : list term) : term :=
  let defs := df_su (te_defs env) in
  let int_defs :=
    sort_by (fun a b => Z.compare (fst a) (fst b))
      (flat_map (fun p =>
                   match parse_su_int_key (fst p), snd p with
                   | Some id, SUDef kind members sz al => [(id, (kind, members, sz, al))]
                   | _, _ => []
                   end) (smap_entries defs)) in
  let complete :=
    map (fun entry =>
           let '(id, (kind, members, sz, al)) := entry in
           let su := su_type_of kind (SUInt id) in
           let names := record_names_for env kind (SUInt id) in
           let def_t := TApp "def" [TAtom (su_kind_atom kind);
                                    TList (map member_layout_to_term members);
                                    Term.TInt sz; Term.TInt al] in
           let field_names := member_names_f 64 members defs in
           let fields :=
             flat_map (fun fnm =>
                         match member_layout su fnm env with
                         | Some (mt, moff, mbits) =>
                             match member_size_align_l mt env with
                             | Some (fsz, fal) =>
                                 [TApp "field" [TAtom fnm;
                                                c_type_to_term mt;
                                                Term.TInt moff;
                                                Term.TInt fsz;
                                                Term.TInt fal;
                                                field_bits_term mbits]]
                             | None => []
                             end
                         | None => []
                         end) field_names in
           TApp "record" [Term.TInt id; TList names; def_t; TList fields])
        int_defs in
  let missing_pairs :=
    dedup_sorted (fun a b => Z.eqb (fst a) (fst b))
      (sort_by (fun a b => Z.compare (fst a) (fst b))
        (flat_map (fun p =>
                     match snd p with
                     | TagSU kind (SUInt id) =>
                         match smap_find (su_id_key (SUInt id)) defs with
                         | Some (SUDef _ _ _ _) => []
                         | _ => [(id, kind)]
                         end
                     | _ => []
                     end) (smap_entries (sc_tags (te_scope env))))) in
  let missing :=
    map (fun p =>
           let '(id, kind) := p in
           let names := record_names_for env kind (SUInt id) in
           TApp "record" [Term.TInt id; TList names; TAtom "incomplete"; TList []])
        missing_pairs in
  let records := app complete missing in
  let uses :=
    flat_map (fun it =>
                match it with
                | TApp f [TAtom fnm; rs] =>
                    if f == "context" then
                      let seeds := sort_Z_uniq (term_record_ids_acc rs []) in
                      let ids := reachable_ids_f (Z.to_nat 4096) seeds defs [] in
                      [TApp "uses" [TAtom fnm; TList (map Term.TInt ids)]]
                    else []
                | _ => []
                end) items in
  TApp "layouts" [TList records; TList uses].

Fixpoint canon_emit_term (t : term) (acc : list string) : list string :=
  let fix emit_seq (xs : list term) (a : list string) : list string :=
    match xs with
    | [] => a
    | [x] => canon_emit_term x a
    | x :: rest => emit_seq rest ("," :: canon_emit_term x a)
    end in
  match t with
  | TAtom s => ir_emit_atom s acc
  | Term.TInt n => decimal n :: acc
  | TList xs => "]" :: emit_seq xs ("[" :: acc)
  | TApp f args => ")" :: emit_seq args ("(" :: ir_emit_atom f acc)
  end.

Definition write_canonical_term (t : term) : string :=
  String.concat "" (rev (canon_emit_term t [])).

Definition module_layouts_canon (env : c_type_env) (items : list term) : string :=
  write_canonical_term (module_layouts_term env items) ++ ".".
