(** The [[validator]] with its [[single-definition|single definitions]]
    found through a [[name-map|name map]], and the proof that it
    answers as Validate.v's [valid] does.

    [single_definitions] asks, for each definition of a function, how
    many definitions share its name, and answers by walking the list
    of all of them: time that grows with the square of their number.
    Three functions of SQLite have 6,000 to 14,800 definitions, and
    that walk was 7 of the 18 seconds [valid] took on its module.
    [single_definitions_fast] counts every name once, in a name map,
    and then keeps the definitions whose name counts one.

    [valid] stays the specification: the proofs of the reuse forms
    read [single_definitions], and nothing in them changes.
    [valid_fast] is what an [[extraction|extracted]] program runs, and
    [valid_fast_eq] says the two are one function. The definitions
    from [stage_sources_fast] down to [valid_fast] repeat Validate.v's
    with the one name replaced; each equality is proved by unfolding
    both sides, so a change to one side that the other lacks stops the
    build here. *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Maps Syntax Cfg Validate.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.

(** ## Counting definitions *)

(** How many of the definitions ds define the name n: the length
    [single_definitions] compares with one. *)
Definition def_count (n : name) (ds : list (name * def)) : nat :=
  length (filter (fun d' => name_eqb n (fst d')) ds).

(** The map from each name the definitions ds define to how many of
    them define it, built in one pass over ds. *)
Definition def_counts (ds : list (name * def)) : nmap nat :=
  fold_left (fun m d => nm_add (fst d)
                               (match nm_find (fst d) m with Some c => S c | None => 1%nat end)
                               m) ds nm_empty.

(** As [single_definitions]: the temporaries of the function f with
    exactly one definition, each with it, in the same order. *)
Definition single_definitions_fast (f : func) : list (name * def) :=
  let ds := all_defs f in
  let counts := def_counts ds in
  filter (fun d => match nm_find (fst d) counts with
                   | Some c => (c =? 1)%nat
                   | None => false
                   end) ds.

(** Counting the definitions ds into a map m adds, to what m held for
    the name n, the number of them that define n. *)
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

(** The map of counts answers, for a name n, the number of definitions
    of n when there is one, and nothing otherwise. *)
Lemma def_counts_find : forall n ds,
  nm_find n (def_counts ds)
  = if (def_count n ds =? 0)%nat then None else Some (def_count n ds).
Proof.
  intros n ds. unfold def_counts. rewrite def_counts_fold, nm_find_empty. reflexivity.
Qed.

(** The single definitions found through the map are those
    [single_definitions] finds, as one list. *)
Theorem single_definitions_fast_eq : forall f,
  single_definitions_fast f = single_definitions f.
Proof.
  intros f. unfold single_definitions_fast, single_definitions.
  apply filter_ext. intros d. rewrite def_counts_find. fold (def_count (fst d) (all_defs f)).
  destruct (def_count (fst d) (all_defs f)) as [|c]; reflexivity.
Qed.

(** ## The validator over them *)

(** As [stage_sources], with [single_definitions_fast]. *)
Definition stage_sources_fast (md : module) (f : func) (doms : nmap (Z * Z)) : src :=
  let once := single_definitions_fast f in
  mkSrc (flat_map (fun b => flat_map (fun i => match renew_source once i with
                                               | Some r => [r]
                                               | None => []
                                               end) (b_insts b)) (fn_blocks f))
        once (ahead_justified f once) (repeated_getters md f doms once).

(** As [stage_func], with [stage_sources_fast]. *)
Definition stage_func_fast (md : module) (f : func) (doms : nmap (Z * Z)) : bool :=
  evidence_pass (stage_sources_fast md f doms) f && limit_reads f && polls_every_cycle f.

(** As [valid_func], with [stage_func_fast]. *)
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

(** As [valid_items], with [valid_func_fast]. *)
Definition valid_items_fast (md : module) : bool :=
  unique_names md &&
  forallb (fun it => match it with
                     | IFunc f => valid_func_fast md f
                     | IData n lk al its => valid_data md n lk al its
                     | IAlias n lk t => valid_alias md n lk t
                     | IOutside _ _ => true
                     end) md.

(** As [valid], with [valid_items_fast]: what an extracted program
    runs. *)
Definition valid_fast (md : module) : option bool :=
  if existsb (fun it => match it with IOutside _ _ => true | _ => false end) md then None
  else Some (valid_items_fast md).

(** ## They are the validator *)

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

(** One function is judged alike. *)
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

(** [valid_fast] accepts, refuses and declines to judge exactly the
    modules [valid] does. *)
Theorem valid_fast_eq : forall md, valid_fast md = valid md.
Proof.
  intros md. unfold valid_fast, valid. rewrite valid_items_fast_eq. reflexivity.
Qed.
