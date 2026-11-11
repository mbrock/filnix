(** A large function can define thousands of temporaries, making
    repeated scans for duplicate definitions an expensive part of validation.
    This module speeds up the [[validator]] by counting names once in
    a [[name-map|name map]], then selecting names that have exactly one definition.
    It proves that this faster computation gives the same answer as
    the simpler specification in [Validate](Validate.v).

    The original [[single-definition|single-definition]] computation
    scans every definition for each name, so its work grows quadratically with the definition count.
    The function [single_definitions_fast] replaces those repeated scans
    with map lookups, preserving the original order of the selected definitions.
    Existing safety proofs continue to use the original specification,
    while the [[extraction|extracted]] program runs the faster validator.

    Speeding up validation must not accidentally accept bad programs,
    reject good ones, or change which modules the model cannot judge.
    The final theorem [valid_fast_eq] proves that every module receives
    exactly the original answer, covering all three possible verdicts. *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Maps Syntax Cfg Validate.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.

(** ## Counting definitions

    A temporary can serve as an unambiguous proof source only when its
    name has exactly one definition in the function.
    The following functions count definitions by name and filter the
    original list, retaining both its entries and their order. *)

(** The original duplicate test counts definitions of one name through
    [def_count], which filters the complete definition list before taking its length. *)
Definition def_count (n : name) (ds : list (name * def)) : nat :=
  length (filter (fun d' => name_eqb n (fst d')) ds).

(** Counting every name in one traversal produces [def_counts], whose
    map entries record positive counts while absent names have no entry. *)
Definition def_counts (ds : list (name * def)) : nmap nat :=
  fold_left (fun m d => nm_add (fst d)
                               (match nm_find (fst d) m with Some c => S c | None => 1%nat end)
                               m) ds nm_empty.

(** Selecting definitions whose recorded count is one gives
    [single_definitions_fast], preserving the same entries and order as the original single-definition computation. *)
Definition single_definitions_fast (f : func) : list (name * def) :=
  let ds := all_defs f in
  let counts := def_counts ds in
  filter (fun d => match nm_find (fst d) counts with
                   | Some c => (c =? 1)%nat
                   | None => false
                   end) ds.

(** Extending an existing count map adds each name's new occurrences
    to its previous count, as [def_counts_fold] proves for the counting traversal.
    A previously absent name remains absent when the new list contains
    no definition of that name, rather than acquiring a zero entry. *)
Lemma def_counts_fold : forall n ds m,
  nm_find n (fold_left (fun m d => nm_add (fst d)
                                          (match nm_find (fst d) m with
                                           | Some c => S c
                                           | None => 1%nat
                                           end) m) ds m)
  = match nm_find n m with
    | Some c => Some (c + def_count n ds)%nat
    | None => if (def_count n ds =? 0)%nat then None else Some (def_count n ds)
    end.
Proof.
  intros n ds. induction ds as [|d ds IH]; intros m.
  - simpl. destruct (nm_find n m); [rewrite Nat.add_0_r|]; reflexivity.
  - cbn [fold_left]. rewrite IH, nm_find_add. unfold def_count. cbn [filter].
    destruct (name_eqb n (fst d)) eqn:E.
    + apply term_eqb_eq in E. subst n. cbn [length].
      destruct (nm_find (fst d) m); simpl; f_equal; lia.
    + reflexivity.
Qed.

(** Looking up a defined name returns its exact occurrence count,
    while [def_counts_find] shows that a name with no definitions has no map entry. *)
Lemma def_counts_find : forall n ds,
  nm_find n (def_counts ds)
  = if (def_count n ds =? 0)%nat then None else Some (def_count n ds).
Proof.
  intros n ds. unfold def_counts. rewrite def_counts_fold, nm_find_empty. reflexivity.
Qed.

(** Replacing repeated counting scans with map lookups leaves the whole
    selected definition list unchanged, as [single_definitions_fast_eq] proves for every function. *)
Theorem single_definitions_fast_eq : forall f,
  single_definitions_fast f = single_definitions f.
Proof.
  intros f. unfold single_definitions_fast, single_definitions.
  apply filter_ext. intros d. rewrite def_counts_find. fold (def_count (fst d) (all_defs f)).
  destruct (def_count (fst d) (all_defs f)) as [|c]; reflexivity.
Qed.

(** ## Checking functions and modules

    Finding unique definitions is only one part of checking whether
    instructions use values and memory proofs correctly throughout a function.
    The following functions keep those other checks unchanged while
    feeding them the faster computation's identical list of unique definitions. *)

(** Collecting reusable proof sources uses [stage_sources_fast] to
    substitute the faster single-definition list while retaining the original scheduled checks and repeated getters. *)
Definition stage_sources_fast (md : module) (f : func) (doms : nmap (Z * Z)) : src :=
  if setjmp_func f then mkSrc [] [] [] [] else
  let once := single_definitions_fast f in
  mkSrc (flat_map (fun b => flat_map (fun i => match renew_source once i with
                                               | Some r => [r]
                                               | None => []
                                               end) (b_insts b)) (fn_blocks f))
        once (ahead_justified f once) (repeated_getters md f doms once).

(** Checking a function's proof evidence uses [stage_func_fast], which
    combines the faster source collection with unchanged limit-use and cycle-poll checks. *)
Definition stage_func_fast (md : module) (f : func) (doms : nmap (Z * Z)) : bool :=
  evidence_pass (stage_sources_fast md f doms) f && limit_reads f && polls_every_cycle f.

(** A valid function must still use correctly typed values, place
    definitions before their uses, and justify memory accesses with suitable checks.
    The function [valid_func_fast] retains all those tests while using
    the faster duplicate count to collect reusable proof sources. *)
Definition valid_func_fast (md : module) (f : func) : bool :=
  let bs := fn_blocks f in
  let defs := temp_defs f in
  match bs, block_intervals bs with
  | [], _ | _, None => false
  | entry :: _, Some doms =>
      match fn_linkage f with TAtom ("export" | "local" | "weak") => true | _ => false end
      && match fn_ret f with
         | RTuple ks =>
             (length ks =? 2)%nat
             && forallb (fun k => existsb (class_eqb k) [L; P; Single; Double]) ks
         | RClass k => any_class k
         | RVoid => true
         end
      && negb (extended_crosses f)
      && no_dups (map b_label bs)
      && temp_classes_ok defs
      && negb (existsb (fun b => mem (b_label entry) (succ_labels (b_jump b))) bs)
      && proof_class_defs f
      && definitions_dominate f doms
      && valid_locals f
      && forallb (valid_block md f defs) bs
      && (negb (module_checked md) || stage_func_fast md f doms)
  end.

(** A module's items pass [valid_items_fast] under the original name,
    data, and alias checks, while functions use the faster validator. *)
Definition valid_items_fast (md : module) : bool :=
  unique_names md &&
  forallb (fun it => match it with
                     | IFunc f => valid_func_fast md f
                     | IData n lk al its => valid_data md n lk al its
                     | IAlias n lk t => valid_alias md n lk t
                     | IOutside _ _ => true
                     end) md.

(** The extracted program calls [valid_fast], which declines unsupported
    modules and otherwise returns the result of checking every supported module item. *)
Definition valid_fast (md : module) : option bool :=
  if existsb (fun it => match it with IOutside _ _ => true | _ => false end) md then None
  else Some (valid_items_fast md).

(** ## Preserving validator verdicts

    A faster implementation must preserve rejection and unsupported
    answers too, not merely accept the programs that previously passed.
    The following equalities connect each copied stage to its original,
    ending with equality of the complete validator functions. *)

Lemma stage_sources_fast_eq : forall md f doms,
  stage_sources_fast md f doms = stage_sources md f doms.
Proof.
  intros md f doms. unfold stage_sources_fast, stage_sources.
  rewrite single_definitions_fast_eq. reflexivity.
Qed.

Lemma stage_func_fast_eq : forall md f doms,
  stage_func_fast md f doms = stage_func md f doms.
Proof.
  intros md f doms. unfold stage_func_fast, stage_func.
  rewrite stage_sources_fast_eq. reflexivity.
Qed.

(** Every function receives the same Boolean verdict under both
    implementations, as [valid_func_fast_eq] proves after replacing the faster evidence stage by its specification. *)
Theorem valid_func_fast_eq : forall md f, valid_func_fast md f = valid_func md f.
Proof.
  intros md f. unfold valid_func_fast, valid_func.
  destruct (fn_blocks f) as [|entry bs]; [reflexivity|].
  destruct (block_intervals (entry :: bs)) as [doms|]; [|reflexivity].
  rewrite stage_func_fast_eq. reflexivity.
Qed.

Lemma valid_items_fast_eq : forall md, valid_items_fast md = valid_items md.
Proof.
  intros md. unfold valid_items_fast, valid_items. f_equal.
  assert (H : forall its,
    forallb (fun it => match it with
                       | IFunc f => valid_func_fast md f
                       | IData n lk al its => valid_data md n lk al its
                       | IAlias n lk t => valid_alias md n lk t
                       | IOutside _ _ => true
                       end) its
    = forallb (fun it => match it with
                         | IFunc f => valid_func md f
                         | IData n lk al its => valid_data md n lk al its
                         | IAlias n lk t => valid_alias md n lk t
                         | IOutside _ _ => true
                         end) its).
  { induction its as [|it its IH]; [reflexivity|]. cbn [forallb]. rewrite IH.
    destruct it; try rewrite valid_func_fast_eq; reflexivity. }
  apply H.
Qed.

(** Every module receives exactly the original verdict, including an
    unsupported answer, as [valid_fast_eq] proves by equating the complete validator functions. *)
Theorem valid_fast_eq : forall md, valid_fast md = valid md.
Proof.
  intros md. unfold valid_fast, valid. rewrite valid_items_fast_eq. reflexivity.
Qed.
