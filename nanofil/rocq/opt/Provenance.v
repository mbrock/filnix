(** This module implements explanatory source context transport and validation
    for the middle-end optimizer, matching `provenance.pl`. Every function may
    carry a `context(Name, Records)` item alongside its `func/5` definition so
    downstream proof scripts and source-hint tools can trace lowered and
    optimized operations back to C declarations and statements.

    Context records remain strictly separate from executable IR semantics and
    never influence fresh executable names or safety proofs. Passes transport
    records explicitly by building old-to-new instruction site maps, retiring
    reused temporary spellings into `history/5` records, and converting legacy
    `loc(File, Line)` markers at unchecked transformation boundaries. *)

From Stdlib Require Import String ZArith List Bool.
From Nanofil Require Import Term Maps Ops Semantics.
From Backend Require Import Order Pizlonate Liveness TermCfg.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(** String equality uses [String.eqb] throughout the optimizer. *)
Local Notation "a == b" := (String.eqb a b) (at level 70).

(** ## Map and grouping helpers

    Prolog association trees iterate keys in standard term order, whereas
    [Maps.nmap] stores entries in hash buckets. The helpers below recover
    sorted entries, test emptiness across removed buckets, insert without
    overwriting earlier keys, and group sorted pairs by key. *)

(** Flattening every bucket of the map [m] yields its key-value pairs in
    unspecified bucket order. *)
Definition nm_elements {A : Type} (m : nmap A) : list (name * A) :=
  flat_map snd (ZMap.elements m).

(** Sorting the entries of [m] by standard term order matches Prolog's
    `assoc_to_list/2`. *)
Definition nm_to_sorted_list {A : Type} (m : nmap A) : list (name * A) :=
  msort (fun a b => term_compare (fst a) (fst b)) (nm_elements m).

(** Testing whether [m] holds no live entries checks that every hash bucket in
    its underlying tree is empty. *)
Definition nm_is_empty {A : Type} (m : nmap A) : bool :=
  forallb (fun p => match snd p with [] => true | _ => false end) (ZMap.elements m).

(** Inserting [(k, v)] only when [m] lacks [k] preserves the first binding for
    each key, matching `index_context/3` and `index_func/3`. *)
Definition nm_add_first {A : Type} (k : name) (v : A) (m : nmap A) : nmap A :=
  if nm_mem k m then m else nm_add k v m.

(** Grouping adjacent pairs with equal keys after a stable sort reproduces
    Prolog's `keysort/2` followed by `group_pairs_by_key/2`. *)
Fixpoint group_sorted_pairs {A : Type} (ps : list (term * A)) : list (term * list A) :=
  match ps with
  | [] => []
  | (k, v) :: rest =>
      match group_sorted_pairs rest with
      | [] => [(k, [v])]
      | (k', vs) :: gs =>
          if term_eqb k k' then (k, v :: vs) :: gs
          else (k, [v]) :: (k', vs) :: gs
      end
  end.

(** Sorting [ps] stably by key and grouping equal keys builds an association
    list of values for each distinct key. *)
Definition group_pairs_by_key {A : Type} (ps : list (term * A)) : list (term * list A) :=
  group_sorted_pairs (msort (fun a b => term_compare (fst a) (fst b)) ps).

(** ## Context indexing and assembly

    A module mixes executable items with `context(Name, Records)` items. The
    functions below separate executable items, index contexts by function name,
    and reattach non-empty contexts after a pass rewrites a function. *)

(** Dropping every `context/2` item from [items] leaves the executable module
    items in their original order, matching `code_items/2`. *)
Definition code_items (items : list term) : list term :=
  filter (fun it => negb (is_context it)) items.

(** Indexing [items] maps each function name to the record list of its first
    `context/2` item, matching `context_index/2`. *)
Definition context_index (items : list term) : nmap (list term) :=
  fold_left
    (fun m it =>
       match it with
       | TApp f [n; TList rs] => if f == "context" then nm_add_first n rs m else m
       | _ => m
       end)
    items nm_empty.

(** Looking up the context of function [name] in [contexts] returns its record
    list, or the empty list when the function has no context. *)
Definition context_records (contexts : nmap (list term)) (name : term) : list term :=
  match nm_find name contexts with
  | Some rs => rs
  | None => []
  end.

(** Attaching [rs] to a function item [fn] emits only the function when [rs] is
    empty and pairs it with `context(Name, Rs)` otherwise, matching
    `with_context/3`. *)
Definition with_context (fn : term) (rs : list term) : list term :=
  match rs with
  | [] => [fn]
  | _ =>
      match fn with
      | TApp f [n; _; _; _; _] =>
          if f == "func" then [fn; TApp "context" [n; TList rs]] else [fn]
      | _ => [fn]
      end
  end.

(** ## Sites and origin identities

    Passes look up instruction origins by site and mint fresh derived origin
    identities without colliding with existing records. Tracking the set size
    alongside the map keeps fresh-origin allocation bounded in constant extra
    work per call. *)

(** Indexing the `site(Site, Origins)` records of [rs] builds a map from each
    site term to its origin list, matching `site_index/2`. *)
Definition site_index (rs : list term) : nmap (list term) :=
  fold_left
    (fun m r =>
       match r with
       | TApp f [s; TList os] => if f == "site" then nm_add s os m else m
       | _ => m
       end)
    rs nm_empty.

(** Reading the origins for [site] from [sites] returns an empty list when the
    site has no recorded origins, matching `site_origins/3`. *)
Definition site_origins (sites : nmap (list term)) (site : term) : list term :=
  match nm_find site sites with
  | Some os => os
  | None => []
  end.

(** An origin table pairs a membership map of origin identities with an upper
    bound on its element count so freshness searches always terminate. *)
Definition origin_set : Type := (nmap unit * nat)%type.

(** Collecting every `origin(Id, _, _, _)` identity in [rs] builds an
    [origin_set], matching `origin_ids/2`. *)
Definition origin_ids (rs : list term) : origin_set :=
  fold_left
    (fun st r =>
       match r with
       | TApp f [id; _; _; _] =>
           if f == "origin" then (nm_add id tt (fst st), S (snd st)) else st
       | _ => st
       end)
    rs (nm_empty, O).

(** Searching for the first unused `derived(Base, N)` scans upward from [n]
    using the origin-set size as fuel. *)
Fixpoint unused_origin (fuel : nat) (base : term) (n : Z) (ids : nmap unit) : term :=
  let cand := TApp "derived" [base; TInt n] in
  match fuel with
  | O => cand
  | S fuel' =>
      if nm_mem cand ids then unused_origin fuel' base (n + 1) ids
      else cand
  end.

(** Choosing a fresh origin identity returns [base] when absent from [ids] and
    the first unused `derived(Base, N)` otherwise, without extending [ids],
    matching `fresh_origin/3`. *)
Definition fresh_origin (base : term) (ids : origin_set) : term :=
  if nm_mem base (fst ids) then unused_origin (S (snd ids)) base 0 (fst ids)
  else base.

(** Choosing a fresh origin identity and recording it in [ids] returns both the
    updated [origin_set] and the chosen identity, matching `fresh_origin/4`. *)
Definition fresh_origin_add (base : term) (ids : origin_set) : origin_set * term :=
  let id := fresh_origin base ids in
  ((nm_add id tt (fst ids), S (snd ids)), id).

(** ## Retiring reused temporary spellings

    When a pass introduces new definitions whose names already appear in
    historical `value/3`, `alias/4`, or `history/5` records, `retire_values/5`
    moves each colliding old definition into a `history/5` record and rewrites
    incoming references to `historical(Id)`. *)

(** Extracting temporary names that a record [r] mentions historically lists
    the subject of `value/3` and `alias/4` as well as any `tmp(T)` replacement
    in `alias/4` or `history/5`. *)
Definition historical_temps (r : term) : list term :=
  match r with
  | TApp f xs =>
      if f == "value" then
        match xs with [t; _; _] => [t] | _ => [] end
      else if f == "alias" then
        match xs with
        | [t; v; _; _] => t :: tmp_name v
        | _ => []
        end
      else if f == "history" then
        match xs with
        | [_; _; _; _; TApp g [v]] => if g == "replaced" then tmp_name v else []
        | _ => []
        end
      else []
  | _ => []
  end.

(** Building the pair of records for a retired temporary creates a generated
    retirement origin followed by its `history/5` record. *)
Definition retired_pair (t h os repl id : term) : list term :=
  [TApp "origin" [id; TAtom "none";
                  TApp "generated" [TAtom "context"; TApp "retired" [t]]; os];
   TApp "history" [id; t; h; os; repl]].

(** Rewriting incoming references to retired temporaries turns `tmp(Old)` into
    `historical(Id)` inside `alias/4` and `history/5` replacements. *)
Definition retired_reference (retired : nmap term) (r : term) : term :=
  match r with
  | TApp f [t; TApp g [old]; h; os] =>
      if (f == "alias") && (g == "tmp") then
        match nm_find old retired with
        | Some id => TApp "alias" [t; TApp "historical" [id]; h; os]
        | None => r
        end
      else r
  | TApp f [hid; t; h; os; TApp rpl [TApp g [old]]] =>
      if (f == "history") && (rpl == "replaced") && (g == "tmp") then
        match nm_find old retired with
        | Some id => TApp "history" [hid; t; h; os; TApp "replaced" [TApp "historical" [id]]]
        | None => r
        end
      else r
  | _ => r
  end.

(** Retiring every existing record of [temps] in [rs0] converts matching
    `value/3` and `alias/4` entries into `history/5` entries and rewrites all
    incoming references, matching `retire_values/5`. *)
Definition retire_values (rs0 : list term) (temps : list term) (ids : origin_set)
  : origin_set * list term :=
  let new_set := fold_left (fun m t => nm_add t tt m) temps nm_empty in
  let aliases :=
    fold_left
      (fun m r =>
         match r with
         | TApp f [t; v; _; _] => if f == "alias" then nm_add t v m else m
         | _ => m
         end)
      rs0 nm_empty in
  let values :=
    fold_left
      (fun m r =>
         match r with
         | TApp f [t; _; _] => if f == "value" then nm_add t tt m else m
         | _ => m
         end)
      rs0 nm_empty in
  let ts :=
    nsort (flat_map (fun r => filter (fun t => nm_mem t new_set) (historical_temps r)) rs0) in
  let pairs := map (fun t => (t, fresh_origin (TApp "retired" [t]) ids)) ts in
  let retired := nm_of_list pairs in
  let records :=
    flat_map
      (fun r =>
         match r with
         | TApp f [t; h; os] =>
             if f == "value" then
               match nm_find t retired with
               | Some id =>
                   let repl :=
                     match nm_find t aliases with
                     | Some v => TApp "replaced" [v]
                     | None => TAtom "none"
                     end in
                   retired_pair t h os repl id
               | None => [r]
               end
             else [r]
         | TApp f [t; v; h; os] =>
             if f == "alias" then
               match nm_find t retired with
               | Some id =>
                   if nm_mem t values then []
                   else retired_pair t h os (TApp "replaced" [v]) id
               | None => [r]
               end
             else [r]
         | _ => [r]
         end)
      rs0 in
  let missing :=
    flat_map
      (fun p =>
         let '(t, id) := p in
         if negb (nm_mem t values) && negb (nm_mem t aliases)
         then retired_pair t (TAtom "none") (TList []) (TAtom "none") id
         else [])
      pairs in
  (ids, map (retired_reference retired) (records ++ missing)).

(** ## Site remapping

    Instruction sites address instructions by `(Label, Index)`. Rewriting passes
    produce an old-to-new site map and move every instruction site in one pass,
    leaving phi and jump sites untouched. *)

(** Identifying an instruction site matches `site(inst(_, _), _)`. *)
Definition is_instruction_site (r : term) : bool :=
  match r with
  | TApp f [TApp g [_; _]; _] => (f == "site") && (g == "inst")
  | _ => false
  end.

(** Identifying any site record matches `site(_, _)`. *)
Definition is_site_record (r : term) : bool :=
  match r with
  | TApp f [_; _] => f == "site"
  | _ => false
  end.

(** Moving instruction sites according to [site_map] drops previous instruction
    sites and appends one remapped site per mapped pair whose source existed in
    [rs0], matching `remap_sites/3`. *)
Definition remap_sites (rs0 : list term) (site_map : list (term * term)) : list term :=
  let sites := site_index rs0 in
  let kept := filter (fun r => negb (is_instruction_site r)) rs0 in
  let new_sites :=
    flat_map
      (fun p =>
         match nm_find (fst p) sites with
         | Some os => [TApp "site" [snd p; TList os]]
         | None => []
         end)
      site_map in
  kept ++ new_sites.

(** Recording site pairs for [emitted] produced from instruction [old_idx] in
    block [lbl] starting at [new_idx] returns the reversed pairs prepended to
    [acc] and the next output index, matching `emission_sites/7`. *)
Fixpoint emission_sites_rev (lbl : term) (old_idx new_idx : Z) (emitted : list term)
    (acc : list (term * term)) : list (term * term) * Z :=
  match emitted with
  | [] => (acc, new_idx)
  | _ :: rest =>
      let pair := (TApp "inst" [lbl; TInt old_idx], TApp "inst" [lbl; TInt new_idx]) in
      emission_sites_rev lbl old_idx (new_idx + 1) rest (pair :: acc)
  end.

(** ## Legacy location conversion

    Hand-written unchecked IR may contain `loc(File, Line)` markers instead of
    explicit `context/2` records. Converting them at pass entry produces
    equivalent `origin/4` and `site/2` records while leaving checked modules
    and loc-free modules untouched. *)

(** Scanning the instructions of one block converts `loc(File, Line)` markers
    into fresh `legacy(L, Old)` origins and attaches the active origin to every
    subsequent instruction. *)
Fixpoint legacy_insts (insts : list term) (lbl : term) (old_idx new_idx : Z)
    (cur_loc : option term) (ids : origin_set)
    (out_rev rs_rev : list term) (map_rev : list (term * term))
  : list term * list term * option term * origin_set * list (term * term) :=
  match insts with
  | [] => (rev' out_rev, rev' rs_rev, cur_loc, ids, rev' map_rev)
  | i :: rest =>
      match i with
      | TApp f [file; line] =>
          if f == "loc" then
            let '(ids1, id) := fresh_origin_add (TApp "legacy" [lbl; TInt old_idx]) ids in
            let orig :=
              TApp "origin" [id; TApp "at" [file; line];
                             TApp "statement" [TAtom "legacy"]; TList []] in
            legacy_insts rest lbl (old_idx + 1) new_idx (Some id) ids1
              out_rev (orig :: rs_rev) map_rev
          else
            let rs_rev1 :=
              match cur_loc with
              | Some lid => TApp "site" [TApp "inst" [lbl; TInt new_idx]; TList [lid]] :: rs_rev
              | None => rs_rev
              end in
            let pair := (TApp "inst" [lbl; TInt old_idx], TApp "inst" [lbl; TInt new_idx]) in
            legacy_insts rest lbl (old_idx + 1) (new_idx + 1) cur_loc ids
              (i :: out_rev) rs_rev1 (pair :: map_rev)
      | _ =>
          let rs_rev1 :=
            match cur_loc with
            | Some lid => TApp "site" [TApp "inst" [lbl; TInt new_idx]; TList [lid]] :: rs_rev
            | None => rs_rev
            end in
          let pair := (TApp "inst" [lbl; TInt old_idx], TApp "inst" [lbl; TInt new_idx]) in
          legacy_insts rest lbl (old_idx + 1) (new_idx + 1) cur_loc ids
            (i :: out_rev) rs_rev1 (pair :: map_rev)
      end
  end.

(** Processing every block of a function gathers legacy origins, phi sites,
    instruction sites, jump sites, and the old-to-new instruction map. *)
Fixpoint legacy_blocks (bs : list tblock) (ids : origin_set)
  : list tblock * origin_set * list term * list (term * term) :=
  match bs with
  | [] => ([], ids, [], [])
  | b :: bs0 =>
      let lbl := tb_label b in
      let '(is', irs, last_loc, ids1, m0) :=
        legacy_insts (tb_insts b) lbl 0 0 None ids [] [] [] in
      let prs :=
        match tb_insts b, irs with
        | i0 :: _, TApp f [first; _; _; _] :: _ =>
            if is_loc i0 && (f == "origin") then
              flat_map
                (fun p =>
                   map (fun t => TApp "site" [TApp "phi" [t]; TList [first]]) (phi_def p))
                (tb_phis b)
            else []
        | _, _ => []
        end in
      let jrs :=
        match last_loc with
        | Some lid => [TApp "site" [TApp "jump" [lbl]; TList [lid]]]
        | None => []
        end in
      let '(bs', ids2, rest_rs, m1) := legacy_blocks bs0 ids1 in
      (mkTBlock lbl (tb_phis b) is' (tb_jump b) :: bs',
       ids2, prs ++ irs ++ jrs ++ rest_rs, m0 ++ m1)
  end.

(** Merging one site record into the site table unions its origin lists in
    standard term order, matching `legacy_site/3`. *)
Definition legacy_site (sites : nmap (list term)) (r : term) : nmap (list term) :=
  match r with
  | TApp f [s; TList os] =>
      if f == "site" then
        let before := site_origins sites s in
        nm_add s (nsort (before ++ os)) sites
      else sites
  | _ => sites
  end.

(** Checking whether any function block in [items] contains a `loc/2` marker
    decides whether `legacy_context/2` can return the module unchanged. *)
Definition module_has_loc (items : list term) : bool :=
  existsb
    (fun it =>
       existsb
         (fun b =>
            match block_parts b with
            | Some (_, insts, _) => existsb is_loc insts
            | None => false
            end)
         (func_blocks it))
    items.

(** Converting `loc(File, Line)` markers in an unchecked module [m] produces
    context records for each affected function while leaving checked modules
    and marker-free modules unchanged, matching `legacy_context/2`. *)
Definition legacy_context (m : term) : option term :=
  match m with
  | TApp f [TList items0] =>
      if negb (f == "module") then None
      else if module_checked items0 || negb (module_has_loc items0) then Some m
      else
        let contexts := context_index items0 in
        let* groups :=
          map_option
            (fun it =>
               match it with
               | TApp h xs =>
                   if h == "func" then
                     match xs with
                     | [n; l; r; ps; TList bs_terms] =>
                         let* bs0 := map_option term_block bs_terms in
                         let rs0 := context_records contexts n in
                         let ids0 := origin_ids rs0 in
                         let '(bs, _, added, smap) := legacy_blocks bs0 ids0 in
                         let rs1 := remap_sites rs0 smap in
                         let sites := fold_left legacy_site added (site_index rs1) in
                         let site_records :=
                           map (fun p => TApp "site" [fst p; TList (snd p)])
                               (nm_to_sorted_list sites) in
                         let kept := filter (fun rec => negb (is_site_record rec)) (rs1 ++ added) in
                         let fn := TApp "func" [n; l; r; ps; TList (map block_term bs)] in
                         Some (with_context fn (kept ++ site_records))
                     | _ => None
                     end
                   else if h == "context" then
                     if arity 2 xs then Some [] else None
                   else Some [it]
               | _ => Some [it]
               end)
            items0 in
        Some (TApp "module" [TList (concat groups)])
  | _ => None
  end.

(** ## Context validation

    Checking a module's context items enforces every structural invariant
    checked by `provenance:valid_contexts/1`: unique contexts per defined
    function, unique record keys within each kind, defined origin and binding
    references, and valid instruction, phi, and jump sites. *)

(** Testing whether [t] is any Prolog atom. *)
Definition is_atom_term (t : term) : bool :=
  match t with TAtom _ => true | _ => false end.

(** Checking whether [keys] has no duplicate elements builds a membership set
    and rejects the first repeated key. *)
Fixpoint unique_keys (keys : list term) (seen : nmap unit) : option (nmap unit) :=
  match keys with
  | [] => Some seen
  | k :: rest =>
      if nm_mem k seen then None
      else unique_keys rest (nm_add k tt seen)
  end.

(** Checking a source location accepts `none` or `at(File, Line)` with a
    non-negative integer line number. *)
Definition valid_location (loc : term) : bool :=
  match loc with
  | TAtom a => a == "none"
  | TApp f [file; TInt line] => (f == "at") && is_atom_term file && (0 <=? line)
  | _ => false
  end.

(** Checking an origin description accepts `statement(Kind)`, `typed(C, _, _)`,
    and `generated(Pass, _)`. *)
Definition valid_description (desc : term) : bool :=
  match desc with
  | TApp f [k] => (f == "statement") && is_atom_term k
  | TApp f [c; _; _] =>
      (f == "typed") && (is_atom "val" c || is_atom "obj" c || is_atom "fun" c)
  | TApp f [p; _] => (f == "generated") && is_atom_term p
  | _ => false
  end.

(** Checking a value hint accepts `none` or `named(BindingId, Role)` for a
    declared binding and role. *)
Definition valid_hint (bindings : nmap unit) (h : term) : bool :=
  match h with
  | TAtom a => a == "none"
  | TApp f [b; role] =>
      (f == "named")
      && (is_atom "value" role || is_atom "address" role || is_atom "piece" role)
      && nm_mem b bindings
  | _ => false
  end.

(** Checking an origin reference list verifies that [os] is a list of defined
    origin identities. *)
Definition valid_origins (origins : nmap unit) (os : term) : bool :=
  match os with
  | TList xs => forallb (fun o => nm_mem o origins) xs
  | _ => false
  end.

(** Checking a replacement value accepts `tmp/1`, `const/1`, `global/1`, and
    `historical/1` pointing to a defined history record. *)
Definition valid_replacement (histories : nmap unit) (v : term) : bool :=
  match v with
  | TApp f [x] =>
      if (f == "tmp") || (f == "global") then is_atom_term x
      else if f == "const" then match x with TInt _ => true | _ => false end
      else if f == "historical" then nm_mem x histories
      else false
  | _ => false
  end.

(** Checking a site verifies that an instruction index lies within its block,
    a phi names a block phi, or a jump names an existing block. *)
Definition valid_site (blocks : nmap Z) (phis : nmap unit) (s : term) : bool :=
  match s with
  | TApp f [l; TInt i] =>
      if f == "inst" then
        match nm_find l blocks with
        | Some n => (0 <=? i) && (i <? n)
        | None => false
        end
      else false
  | TApp f [t] =>
      if f == "phi" then nm_mem t phis
      else if f == "jump" then nm_mem t blocks
      else false
  | _ => false
  end.

(** Checking one context record validates its functor, arguments, references,
    and site against the function's index tables. *)
Definition valid_record (origins bindings histories : nmap unit)
    (blocks : nmap Z) (phis : nmap unit) (r : term) : bool :=
  match r with
  | TApp f xs =>
      if f == "binding" then
        match xs with
        | [_; nm; _; loc] => is_atom_term nm && valid_location loc
        | _ => false
        end
      else if f == "origin" then
        match xs with
        | [_; loc; desc; parents] =>
            valid_location loc && valid_description desc && valid_origins origins parents
        | _ => false
        end
      else if f == "value" then
        match xs with
        | [t; hint; os] =>
            is_atom_term t && valid_hint bindings hint && valid_origins origins os
        | _ => false
        end
      else if f == "alias" then
        match xs with
        | [t; v; hint; os] =>
            is_atom_term t && valid_replacement histories v
            && valid_hint bindings hint && valid_origins origins os
        | _ => false
        end
      else if f == "history" then
        match xs with
        | [id; t; hint; os; repl] =>
            nm_mem id origins && is_atom_term t
            && valid_hint bindings hint && valid_origins origins os
            && (is_atom "none" repl
                || match repl with
                   | TApp g [v] => (g == "replaced") && valid_replacement histories v
                   | _ => false
                   end)
        | _ => false
        end
      else if f == "site" then
        match xs with
        | [s; os] => valid_site blocks phis s && valid_origins origins os
        | _ => false
        end
      else false
  | _ => false
  end.

(** Validating one function's context checks key uniqueness for every record
    kind and validates every record against the function's blocks and phis. *)
Definition valid_context (funcs : nmap (list tblock)) (name : term) (rs : list term) : bool :=
  match nm_find name funcs with
  | None => false
  | Some bs =>
      let '(os, bs_k, vs, as_k, hs, ss) :=
        fold_left
          (fun acc r =>
             let '(os, bsk, vs, ask, hs, ss) := acc in
             match r with
             | TApp f xs =>
                 if f == "origin" then
                   match xs with [id; _; _; _] => (id :: os, bsk, vs, ask, hs, ss) | _ => acc end
                 else if f == "binding" then
                   match xs with [b; _; _; _] => (os, b :: bsk, vs, ask, hs, ss) | _ => acc end
                 else if f == "value" then
                   match xs with [t; _; _] => (os, bsk, t :: vs, ask, hs, ss) | _ => acc end
                 else if f == "alias" then
                   match xs with [t; _; _; _] => (os, bsk, vs, t :: ask, hs, ss) | _ => acc end
                 else if f == "history" then
                   match xs with [id; _; _; _; _] => (os, bsk, vs, ask, id :: hs, ss) | _ => acc end
                 else if f == "site" then
                   match xs with [s; _] => (os, bsk, vs, ask, hs, s :: ss) | _ => acc end
                 else acc
             | _ => acc
             end)
          rs ([], [], [], [], [], []) in
      match unique_keys os nm_empty, unique_keys bs_k nm_empty,
            unique_keys vs nm_empty, unique_keys as_k nm_empty,
            unique_keys hs nm_empty, unique_keys ss nm_empty with
      | Some origins, Some bindings, Some _, Some _, Some histories, Some _ =>
          let blocks :=
            nm_of_list (map (fun b => (tb_label b, Z.of_nat (length (tb_insts b)))) bs) in
          let phis :=
            fold_left (fun m t => nm_add t tt m)
                      (flat_map (fun b => flat_map phi_def (tb_phis b)) bs) nm_empty in
          forallb (valid_record origins bindings histories blocks phis) rs
      | _, _, _, _, _, _ => false
      end
  end.

(** Validating all `context/2` items in a module item list checks uniqueness of
    context names and validates each context against its function, matching
    `valid_contexts/1`. *)
Definition valid_contexts (items : list term) : bool :=
  let names :=
    flat_map
      (fun it =>
         match it with
         | TApp f [n; _] => if f == "context" then [n] else []
         | _ => []
         end)
      items in
  match unique_keys names nm_empty with
  | None => false
  | Some _ =>
      let funcs :=
        fold_left
          (fun m it =>
             match it with
             | TApp f [n; _; _; _; TList bs_terms] =>
                 if f == "func" then
                   match map_option term_block bs_terms with
                   | Some bs => nm_add_first n bs m
                   | None => m
                   end
                 else m
             | _ => m
             end)
          items nm_empty in
      forallb
        (fun it =>
           match it with
           | TApp f [n; rs_term] =>
               if f == "context" then
                 match rs_term with
                 | TList rs => valid_context funcs n rs
                 | _ => false
                 end
               else true
           | _ => true
           end)
        items
  end.
