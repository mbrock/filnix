(** Copy propagation follows [[temporary]] definitions to a surviving operand.
    This file relates those substitutions to operand evaluation and proves the
    bounds and storage charge of each allocation selected for local access. *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Maps Syntax Values Semantics Cfg.
From Backend Require Import Text Order Pizlonate Liveness TermCfg Copy Escape.
From Opt Require Import Provenance OptIr OptCopy LocalStorage.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(** ## Operands and copies *)

(** The interpreter reads typed operands while the optimizer reads terms.
    Decoding just the class and operand lets both passes share the same
    arithmetic and [[capability]] semantics. *)

(** Each register class has a single spelling in the term representation. *)
Definition copy_class (k : term) : option class :=
  match k with
  | TAtom "w" => Some W | TAtom "l" => Some L | TAtom "p" => Some P
  | TAtom "a" => Some A | TAtom "f" => Some F | TAtom "s" => Some Single
  | TAtom "d" => Some Double | TAtom "x" => Some Extended
  | _ => None
  end.

(** A decoded operand reads its word from the interpreter at the given class. *)
Definition term_value (ge : genv) (e : env) (k v : term) : option word :=
  let* c := copy_class k in
  match v with
  | TApp "tmp" [n] => value_x ge e c (Tmp n)
  | TApp "const" [TInt n] => value_x ge e c (Const n)
  | TApp "global" [s] => value_x ge e c (Global s)
  | _ => None
  end.

(** A temporary keeps its spelling, and reducing an integer constant twice
    gives the same residue. Both facts hold for every environment. *)
Theorem copy_value_sound : forall ge e classes k src v,
  copy_value classes k src = Some v ->
  term_value ge e k v = term_value ge e k src.
Proof.
  intros ge e classes k src v H. unfold copy_value in H.
  destruct src as [| |f [|x [|y rest]]|]; try discriminate H.
  destruct (String.eqb f "tmp").
  - destruct (nm_find x classes) as [c|]; try discriminate H.
    destruct (term_eqb c k); congruence.
  - destruct (String.eqb f "const") eqn:E; try discriminate H.
    apply String.eqb_eq in E. subst f. destruct x as [n| | |]; try discriminate H.
    destruct k as [|a| |]; try discriminate H. cbn [is_atom] in H.
    destruct (String.eqb "w" a) eqn:Wk.
    + apply String.eqb_eq in Wk. subst a. injection H as <-.
      change (Some (WInt ((n mod 2 ^ 32) mod 2 ^ 32)) = Some (WInt (n mod 2 ^ 32))).
      rewrite Z.mod_mod by discriminate. reflexivity.
    + destruct (String.eqb "l" a) eqn:Lk; try discriminate H.
      apply String.eqb_eq in Lk. subst a. injection H as <-.
      change (Some (WInt ((n mod 2 ^ 64) mod 2 ^ 64)) = Some (WInt (n mod 2 ^ 64))).
      rewrite Z.mod_mod by discriminate. reflexivity.
Qed.

(** The optimizer rejects every pointer-class integer constant as a replacement. *)
Theorem copy_pointer_constant : forall classes n,
  copy_value classes (TAtom "p") (TApp "const" [TInt n]) = None.
Proof. reflexivity. Qed.

(** A singleton temporary-name result identifies the complete source term. *)
Lemma tmp_name_single : forall v t, tmp_name v = [t] -> v = tmp t.
Proof.
  intros v t H. destruct v as [| |f [|x [|y xs]]|]; try discriminate H.
  cbn [tmp_name] in H. destruct (String.eqb f "tmp") eqn:E; try discriminate H.
  apply String.eqb_eq in E. subst f. injection H as <-. reflexivity.
Qed.

(** A table preserves values if every lookup equates the destination and source. *)
Definition valued (val : term -> option word) (m : nmap term) : Prop :=
  forall t v, nm_find t m = Some v -> val (tmp t) = val v.

(** An endpoint is normal in a table when its temporary has no entry there. *)
Definition normal (m : nmap term) (v : term) : Prop :=
  forall u, v = tmp u -> nm_find u m = None.

(** A successful walk either reaches a fresh endpoint or reads one from the
    cache. Each newly visited name has a copy edge and shares the endpoint's value. *)
Theorem copy_chain_sound : forall val fuel copies reps v0 path0 path last,
  valued val copies -> valued val reps ->
  copy_chain fuel copies reps v0 path0 = Some (path, last) ->
  val last = val v0 /\
  (forall t, In t path -> ~ In t path0 ->
     val (tmp t) = val last /\ exists src, nm_find t copies = Some src) /\
  ((normal reps last /\ normal copies last) \/ exists t, nm_find t reps = Some last).
Proof.
  intros val fuel copies reps. induction fuel as [|fuel IH]; intros v0 path0 path last C R H;
    cbn [copy_chain] in H; try discriminate H.
  destruct (tmp_name v0) as [|t [|s ts]] eqn:N.
  all: try (injection H as <- <-; split; [reflexivity|]; split;
    [intros; contradiction|left; split; intros u E; subst v0; discriminate N]).
  apply tmp_name_single in N. subst v0.
  destruct (nm_find t reps) as [v|] eqn:Er.
  - injection H as <- <-. split; [symmetry; eapply R; eauto|].
    split; [intros; contradiction|right; eauto].
  - destruct (nm_find t copies) as [src|] eqn:Ec.
    + destruct (IH _ _ _ _ C R H) as [V [Path End]].
      split; [rewrite V; symmetry; eapply C; eauto|]. split; [|exact End].
      intros x Hin Hout. destruct (term_eqb x t) eqn:Eq.
      * apply term_eqb_eq in Eq. subst x. split; [rewrite V; eapply C; eauto|eauto].
      * apply Path; [exact Hin|]. intros [E|E]; [subst x; rewrite term_eqb_refl in Eq; discriminate|auto].
    + injection H as <- <-. split; [reflexivity|]. split; [intros; contradiction|].
      left. split; intros u E; injection E as <-; assumption.
Qed.

(** A self-mapping cache preserves every valuation and returns a mapped endpoint. *)
Example cached_endpoint_counterexample :
  let d := TInt 0 in let reps := nm_add d (tmp d) nm_empty in
  (forall val, valued val reps) /\
  copy_chain 1 nm_empty reps (tmp d) [] = Some ([], tmp d) /\
  nm_find d reps = Some (tmp d).
Proof.
  cbv zeta. split; [|split; reflexivity].
  intros val t v H. rewrite nm_find_add, nm_find_empty in H.
  destruct (name_eqb t (TInt 0)) eqn:E; try discriminate H.
  apply term_eqb_eq in E. congruence.
Qed.

(** ## Representative tables *)

(** The cache starts empty and receives only names with a copy edge.
    Each insertion records an endpoint outside the fixed copy table, so
    adding later entries preserves every earlier endpoint. *)

(** Folding a list preserves a property that each individual step preserves. *)
Lemma fold_property {X Y : Type} (step : X -> Y -> X) (P : X -> Prop) :
  forall ys x, P x -> (forall y a, In y ys -> P a -> P (step a y)) ->
  P (fold_left step ys x).
Proof.
  induction ys as [|y ys IH]; intros x Start Step; [exact Start|].
  apply IH; [apply Step; [left; reflexivity|exact Start]|].
  intros z a Hz. apply Step. right. exact Hz.
Qed.

(** Every lookup in a map built from pairs returns one of the supplied pairs. *)
Lemma pairs_lookup {X : Type} : forall (ps : list (term * X)) t v,
  nm_find t (nm_of_list ps) = Some v -> In (t,v) ps.
Proof.
  intros ps. unfold nm_of_list.
  apply (fold_property _ (fun m => forall t v, nm_find t m = Some v -> In (t,v) ps)).
  - intros t v H. rewrite nm_find_empty in H. discriminate.
  - intros [d src] m Hin Old t v H. rewrite nm_find_add in H.
    cbn [fst snd] in H. destruct (name_eqb t d) eqn:E.
    + apply term_eqb_eq in E. subst t. injection H as <-. exact Hin.
    + eauto.
Qed.

(** A well-formed cache records only copy destinations, and its stored
    values have no further edge in the original copy table. *)
Definition cache_ok (val : term -> option word) (copies reps : nmap term) : Prop :=
  forall d v, nm_find d reps = Some v ->
    val (tmp d) = val v /\ normal copies v /\ exists src, nm_find d copies = Some src.

(** Copy-chain compression preserves all three properties of the cache. *)
Lemma compress_chain : forall val copies reps fuel d path v,
  valued val copies -> cache_ok val copies reps ->
  copy_chain fuel copies reps (tmp d) [] = Some (path,v) ->
  cache_ok val copies (fold_left (fun m t => nm_add t v m) path reps).
Proof.
  intros val copies reps fuel d path v C Cache Run.
  assert (R : valued val reps) by (intros t x H; exact (proj1 (Cache t x H))).
  destruct (copy_chain_sound val fuel copies reps _ _ _ _ C R Run)
    as [_ [Path [[_ End]|[key Hit]]]].
  all: try (pose proof (proj1 (proj2 (Cache key v Hit))) as End).
  all: apply (fold_property _ (cache_ok val copies)); [exact Cache|].
  all: intros t m Hin Good u x H; rewrite nm_find_add in H;
    destruct (name_eqb u t) eqn:E; [|apply Good; exact H].
  all: apply term_eqb_eq in E; subst u; injection H as <-;
    destruct (Path t Hin) as [V Edge]; [simpl; auto|auto].
Qed.

(** Compressing all input pairs produces a well-formed cache from the empty map. *)
Lemma chain_cache_ok : forall val pairs reps,
  (forall d src, In (d,src) pairs -> val (tmp d) = val src) ->
  chain_reps pairs = Some reps -> cache_ok val (nm_of_list pairs) reps.
Proof.
  intros val pairs reps Cons Run. unfold chain_reps in Run.
  set (copies := nm_of_list pairs) in *.
  assert (C : valued val copies) by (intros d src H; apply Cons; eapply pairs_lookup; eauto).
  revert Run. generalize (S (S (length pairs))) as fuel. intro fuel. revert reps.
  apply (fold_property _ (fun result => forall reps, result = Some reps -> cache_ok val copies reps)).
  - intros r E. injection E as <-. intros d v H. rewrite nm_find_empty in H. discriminate.
  - intros [d src] [r|] Hin Old r' H; cbn in H; try discriminate H.
    destruct (copy_chain fuel copies r (tmp d) []) as [[path v]|] eqn:Walk;
      try discriminate H. injection H as <-. eapply compress_chain; eauto.
Qed.

(** Every stored representative preserves evaluation and is an endpoint
    in both the input copy table and the final representative table. *)
Theorem chain_reps_sound : forall (val : term -> option word) pairs reps,
  (forall d src, In (d,src) pairs -> val (tmp d) = val src) ->
  chain_reps pairs = Some reps ->
  forall t v, nm_find t reps = Some v ->
  val (tmp t) = val v /\ normal (nm_of_list pairs) v /\ normal reps v.
Proof.
  intros val pairs reps Cons Run. pose proof (chain_cache_ok val pairs reps Cons Run) as Good.
  intros t v Hit. destruct (Good t v Hit) as [V [End _]]. split; [exact V|].
  split; [exact End|]. intros u E. specialize (End u E).
  destruct (nm_find u reps) as [x|] eqn:H; [|reflexivity].
  destruct (Good u x H) as [_ [_ [src Edge]]]. congruence.
Qed.

(** A normal cache returns a normal endpoint on every successful walk. *)
Theorem copy_chain_normal : forall val fuel copies reps v0 path0 path last,
  valued val copies -> valued val reps ->
  (forall t v, nm_find t reps = Some v -> normal reps v /\ normal copies v) ->
  copy_chain fuel copies reps v0 path0 = Some (path,last) ->
  normal reps last /\ normal copies last.
Proof.
  intros val fuel copies reps v0 path0 path last C R Cache Run.
  destruct (copy_chain_sound _ _ _ _ _ _ _ _ C R Run) as [_ [_ [End|[t Hit]]]]; eauto.
Qed.

(** Inserting pairs puts every input key in the map even when later pairs
    give that key a different value. *)
Lemma input_key_present {X : Type} : forall (ps : list (term * X)) t,
  In t (map fst ps) -> nm_mem t (nm_of_list ps) = true.
Proof.
  intros ps t Hin. unfold nm_of_list. generalize (@nm_empty X).
  assert (Keep : forall (rest : list (term * X)) m,
    nm_mem t m = true -> nm_mem t (fold_left (fun m p => nm_add (fst p) (snd p) m) rest m) = true).
  { intros rest m H. apply (fold_property _ (fun m => nm_mem t m = true)); [exact H|].
    intros p curr _ Old. rewrite nm_mem_add, Old, orb_true_r. reflexivity. }
  induction ps as [|[d v] ps IH]; [contradiction|]. intros m. destruct Hin as [E|Hin].
  - cbn [fst] in E. subst d. cbn [fold_left fst snd]. apply Keep. rewrite nm_mem_add.
    unfold name_eqb. rewrite term_eqb_refl. reflexivity.
  - apply IH. exact Hin.
Qed.

(** A successful walk retains every name in the path that its caller supplies. *)
Lemma copy_chain_keeps_path : forall fuel copies reps v path path' last,
  copy_chain fuel copies reps v path = Some (path',last) -> incl path path'.
Proof.
  induction fuel as [|fuel IH]; intros copies reps v path path' last H; cbn [copy_chain] in H;
    try discriminate H.
  destruct (tmp_name v) as [|t [|s ts]]; try (injection H as <- <-; apply incl_refl).
  destruct (nm_find t reps); [injection H as <- <-; apply incl_refl|].
  destruct (nm_find t copies); [|injection H as <- <-; apply incl_refl].
  intros x Hin. eapply (IH _ _ _ _ _ _ H). right. exact Hin.
Qed.

(** Installing a compressed path covers each visited name and retains
    every name present before the installation. *)
Lemma installed_path_covers : forall path (m : nmap term) v t,
  In t path \/ nm_mem t m = true ->
  nm_mem t (fold_left (fun m d => nm_add d v m) path m) = true.
Proof.
  induction path as [|d path IH]; intros m v t H; cbn in *; [tauto|].
  apply IH. rewrite nm_mem_add. destruct H as [[E|Hin]|Old]; try tauto.
  - subst d. unfold name_eqb. rewrite term_eqb_refl. auto.
  - rewrite Old, orb_true_r. auto.
Qed.

(** Resolving one input key either finds it in the cache or places it on
    the path that the caller installs. *)
Lemma walked_key_covered : forall fuel copies reps d path v,
  nm_mem d copies = true -> copy_chain fuel copies reps (tmp d) [] = Some (path,v) ->
  nm_mem d (fold_left (fun m t => nm_add t v m) path reps) = true.
Proof.
  intros [|fuel] copies reps d path v Present H; [discriminate|].
  apply installed_path_covers. cbn [copy_chain tmp_name tmp] in H. rewrite String.eqb_refl in H.
  destruct (nm_find d reps) eqn:Hit.
  - right. unfold nm_mem. rewrite Hit. reflexivity.
  - unfold nm_mem in Present. destruct (nm_find d copies) as [src|]; try discriminate Present.
    left. apply (copy_chain_keeps_path fuel copies reps src [d] path v H). left. reflexivity.
Qed.

(** The final cache covers every destination in the input. Its domain
    therefore agrees exactly with the input keys, including repeated names. *)
Theorem chain_reps_domain : forall pairs reps, chain_reps pairs = Some reps ->
  forall d, nm_mem d reps = true <-> In d (map fst pairs).
Proof.
  intros pairs reps Run d. split.
  - unfold nm_mem. destruct (nm_find d reps) as [v|] eqn:Hit; [|discriminate].
    intros _. pose proof (chain_cache_ok (fun _ => None) pairs reps
      (fun _ _ _ => eq_refl) Run d v Hit) as [_ [_ [src Edge]]].
    apply pairs_lookup in Edge. apply in_map_iff. exists (d,src). auto.
  - intro Hin. pose proof (input_key_present pairs d Hin) as Present.
    unfold chain_reps in Run. set (copies := nm_of_list pairs) in *.
    generalize dependent reps. generalize (S (S (length pairs))) as fuel. intro fuel.
    assert (Cover : forall (todo : list (term * term)) r, In d (map fst todo) \/ nm_mem d r = true ->
      forall final, fold_left (fun acc p => let* m := acc in
        let* walk := copy_chain fuel copies m (tmp (fst p)) [] in
        Some (fold_left (fun m t => nm_add t (snd walk) m) (fst walk) m))
        todo (Some r) = Some final -> nm_mem d final = true).
    { intro remaining. induction remaining as [|[k src] rest IH]; intros r Candidates final Step.
      - injection Step as <-. destruct Candidates as [[]|H]; exact H.
      - cbn in Step. destruct (copy_chain fuel copies r (tmp k) []) as [[path last]|] eqn:Walk.
        + eapply IH; [|exact Step]. cbn [map fst In] in Candidates.
          destruct Candidates as [[E|H]|Old]; [subst k; right; eapply walked_key_covered; eauto|
            left; exact H|right; apply installed_path_covers; auto].
        + exfalso. clear IH Candidates. induction rest as [|p rest IH]; cbn in Step; [discriminate|eauto]. }
    intros final H. eapply Cover; [left; exact Hin|exact H].
Qed.

(** ## Witnesses in sorted lists *)

(** Escape classification and phi simplification both sort and coalesce
    observations. A witness survives these operations whenever the comparator
    preserves its property on a pair that compares equal. *)

Section SortWitness.
Context {X : Type} (cmp : X -> X -> comparison) (P : X -> Prop).

(** A list carries a witness when one of its elements satisfies the predicate. *)
Definition carries (xs : list X) := exists x, In x xs /\ P x.

(** A cons cell carries a witness at its head or in its tail. *)
Lemma carries_cons : forall x xs, carries (x :: xs) <-> P x \/ carries xs.
Proof.
  intros x xs. unfold carries. split.
  - intros [y [[E|H] Py]]; [subst; auto|right; eauto].
  - intros [H|[y [Hin Py]]]; [exists x; split; [left|]; auto|exists y; split; [right|]; auto].
Qed.

(** A merge with sufficient fuel retains a witness from either input. *)
Lemma merge_carries : forall n xs ys, (length xs + length ys <= n)%nat ->
  carries xs \/ carries ys -> carries (merge_steps cmp n xs ys).
Proof.
  induction n as [|n IH]; intros [|x xs] [|y ys] Bound H;
    cbn [length] in Bound; try lia; cbn [merge_steps];
    try solve [destruct H as [H|H]; try exact H; destruct H as [z [[] _]]].
  pose proof (IH xs (y :: ys) ltac:(cbn; lia)) as TakeLeft.
  pose proof (IH (x :: xs) ys ltac:(cbn; lia)) as TakeRight.
  rewrite (carries_cons y ys) in TakeLeft. rewrite (carries_cons x xs) in TakeRight.
  repeat rewrite carries_cons in H. destruct (cmp x y); apply carries_cons; tauto.
Qed.

(** A stack carries a witness if some pending merge run contains it. *)
Fixpoint stack_carries (stack : list (option (list X))) : Prop :=
  match stack with
  | [] => False
  | None :: rest => stack_carries rest
  | Some xs :: rest => carries xs \/ stack_carries rest
  end.

(** Pushing a run preserves a witness in that run or elsewhere on the stack. *)
Lemma push_carries : forall stack run, stack_carries stack \/ carries run ->
  stack_carries (push_run cmp stack run).
Proof.
  induction stack as [|[xs|] rest IH]; intros run H; cbn in *; try tauto.
  apply IH. unfold merge. destruct H as [[Xw|St]|Rw]; try tauto;
    right; apply merge_carries; [lia|auto|lia|auto].
Qed.

(** Draining the merge stack emits every property witnessed by a pending run. *)
Lemma drain_carries : forall stack, stack_carries stack -> carries (merge_runs cmp stack).
Proof.
  induction stack as [|[xs|] rest IH]; cbn; try tauto.
  intro H. apply merge_carries; [lia|tauto].
Qed.

(** Merge sorting preserves a witness at every position of the input. *)
Lemma msort_carries : forall xs, carries xs -> carries (msort cmp xs).
Proof.
  intros xs H. unfold msort. apply drain_carries.
  assert (Walk : forall ys st, stack_carries st \/ carries ys ->
    stack_carries (fold_left (fun s x => push_run cmp s [x]) ys st)).
  { induction ys as [|y ys IH]; intros st G; cbn; [destruct G as [G|[x [[] _]]]; exact G|].
    apply IH. rewrite carries_cons in G. destruct G as [G|[Y|Tail]]; try tauto.
    - left. apply push_carries. auto.
    - left. apply push_carries. right. apply carries_cons. auto. }
  apply Walk. auto.
Qed.

(** Coalescing equal neighbors preserves any witness that passes from a
    discarded neighbor to its retained successor. *)
Lemma sort_carries : (forall x y, cmp x y = Datatypes.Eq -> P x -> P y) ->
  forall xs, carries xs -> carries (sort cmp xs).
Proof.
  intros Stable xs H. unfold sort. apply msort_carries in H.
  generalize dependent (msort cmp xs). intros ys.
  induction ys as [|x [|y ys] IH]; intro G; try exact G.
  cbn [dedup]. rewrite carries_cons in G. destruct (cmp x y) eqn:E.
  - apply IH. destruct G as [Px|Tail]; [apply carries_cons; left; eauto|exact Tail].
  - apply carries_cons. tauto.
  - apply carries_cons. tauto.
Qed.
End SortWitness.

(** ## Phi operands and the worklist *)

(** An operand can justify a phi's value if it occurs before the phi in
    a well-founded order. Substituting the operand that justifies an earlier
    phi preserves this order even when two phis refer to one another. *)

(** A consistent phi agrees with any word shared by all its nonself operands. *)
Definition phi_consistent (val : term -> option word) (d : term) (vs : list term) :=
  forall w, (forall x, In x vs -> x <> tmp d -> val x = Some w) -> val (tmp d) = Some w.

(** A single undefined incoming operand makes the word premise vacuous
    even though the worklist emits a substitution for the defined destination. *)
Example undefined_phi_counterexample :
  let d := TInt 0 in let x := TApp "const" [TInt 1] in
  let val := fun v => if term_eqb v (tmp d) then Some (WInt 0) else None in
  phi_consistent val d [x] /\
  phi_worklist 2 [d] (nm_add d [x] nm_empty) nm_empty [] = Some [(d,x)] /\
  val (tmp d) <> val x.
Proof.
  cbv zeta. split; [|split; [reflexivity|discriminate]].
  intros w All. specialize (All (TApp "const" [TInt 1]) (or_introl eq_refl) ltac:(discriminate)).
  discriminate All.
Qed.

(** Two mutually dependent phis can pass the consistency test with defined
    words. Replacing one by the other then exposes a third operand with a
    different word and invalidates the remaining phi. *)
Example circular_phi_counterexample :
  let x := TInt 0 in let y := TInt 1 in let c := TApp "const" [TInt 2] in
  let val := fun v => Some (WInt (if term_eqb v c then 2 else 0)) in
  phi_consistent val y [tmp x] /\ phi_consistent val x [tmp y;c] /\
  phi_worklist 3 [y] (nm_of_list [(x,[tmp y;c]);(y,[tmp x])])
    (nm_add y [x] nm_empty) [] = Some [(x,c);(y,tmp x)] /\
  ~ phi_consistent val x [tmp x;c] /\ val (tmp x) <> val c.
Proof.
  cbv zeta. split.
  - intros w All. exact (All (tmp (TInt 0)) (or_introl eq_refl) ltac:(discriminate)).
  - split.
    + intros w All. exact (All (tmp (TInt 1)) (or_introl eq_refl) ltac:(discriminate)).
    + split; [reflexivity|]. split; [|discriminate]. intro Good.
      specialize (Good (WInt 2)). assert (Bad : Some (WInt 0) = Some (WInt 2)).
      { apply Good. intros v [E|[E|[]]] Diff; subst v; [contradiction|reflexivity]. }
      discriminate.
Qed.

(** A justification names an incoming operand with the destination's value
    and a smaller rank. Its spelling distinguishes it from every unequal
    term during duplicate removal. *)
Definition justifies (val : term -> option word) (rank : term -> nat) (d x : term) :=
  val x = val (tmp d) /\ (rank x < rank (tmp d))%nat /\
  forall y, term_compare x y = Datatypes.Eq -> x = y.

(** Each live phi carries at least one justified incoming operand. *)
Definition phi_table_ok val rank (phis : nmap (list term)) :=
  forall d vs, nm_find d phis = Some vs -> carries (justifies val rank d) vs.

(** A justified table satisfies the word consistency condition for each entry. *)
Lemma justified_consistent : forall val rank phis, phi_table_ok val rank phis ->
  forall d vs, nm_find d phis = Some vs -> phi_consistent val d vs.
Proof.
  intros val rank phis Table d vs Hit w All.
  destruct (Table d vs Hit) as (x & Hin & Same & Before & Unique).
  rewrite <- Same. apply All; [exact Hin|]. intros ->. lia.
Qed.

(** A singleton sorted result identifies the operand that justifies the phi. *)
Lemma singleton_justifies : forall val rank d vs x,
  carries (justifies val rank d) vs ->
  sort term_compare (filter (fun v => negb (term_eqb v (tmp d))) vs) = [x] ->
  justifies val rank d x.
Proof.
  intros val rank d vs x [v [Hin J]] Sorted.
  destruct J as [Same [Before Unique]].
  assert (Filtered : In v (filter (fun z => negb (term_eqb z (tmp d))) vs)).
  { apply filter_In. split; [exact Hin|]. destruct (term_eqb v (tmp d)) eqn:E; [|reflexivity].
    apply term_eqb_eq in E. subst v. lia. }
  assert (Witness : carries (fun z => v = z)
    (sort term_compare (filter (fun z => negb (term_eqb z (tmp d))) vs))).
  { apply sort_carries.
    - intros s t E <-. apply Unique. exact E.
    - exists v. auto. }
  rewrite Sorted in Witness. destruct Witness as [z [[E|[]] <-]]. subst x.
  unfold justifies. auto.
Qed.

(** Substituting a justified operand keeps the user's witness or replaces
    it with one of strictly smaller rank and the same value. *)
Lemma substitute_justification : forall val rank d v u vs,
  justifies val rank d v -> carries (justifies val rank u) vs ->
  carries (justifies val rank u) (map (fun x => if term_eqb x (tmp d) then v else x) vs).
Proof.
  intros val rank d v u vs [Same [Before Unique]] [x [Hin [Xval [Xrank Xunique]]]].
  exists (if term_eqb x (tmp d) then v else x). split.
  - apply in_map_iff. exists x. auto.
  - destruct (term_eqb x (tmp d)) eqn:E; unfold justifies; [|auto].
    apply term_eqb_eq in E. subst x. split; [congruence|]. split; [lia|exact Unique].
Qed.

(** Removing the simplified phi and updating its users preserves each
    remaining phi's justification, including after repeated user visits. *)
Lemma phi_step_preserves : forall val rank phis d v live,
  phi_table_ok val rank phis -> justifies val rank d v ->
  phi_table_ok val rank
    (fold_left (fun m u => match nm_find u m with
      | Some vs => nm_add u (map (fun x => if term_eqb x (tmp d) then v else x) vs) m
      | None => m end) live (nm_remove d phis)).
Proof.
  intros val rank phis d v live Table J. apply (fold_property _ (phi_table_ok val rank)).
  - intros u vs Hit. rewrite nm_find_remove in Hit. destruct (name_eqb u d); [discriminate|eauto].
  - intros u m Hin Old. destruct (nm_find u m) as [vs|] eqn:Get; [|exact Old].
    intros k xs Hit. rewrite nm_find_add in Hit. destruct (name_eqb k u) eqn:E; [|eauto].
    apply term_eqb_eq in E. subst k. injection Hit as <-.
    apply substitute_justification; [exact J|eauto].
Qed.

(** A worklist starting with justified phis extends its accumulator only
    with equal-valued substitutions. The same rank witnesses justify the
    remaining table at every recursive step. *)
Theorem phi_worklist_sound : forall val rank fuel pending phis users found result,
  phi_table_ok val rank phis ->
  (forall d v, In (d,v) found -> val (tmp d) = val v) ->
  phi_worklist fuel pending phis users found = Some result ->
  forall d v, In (d,v) result -> val (tmp d) = val v.
Proof.
  intros val rank fuel. induction fuel as [|fuel IH]; intros pending phis users found result Table Old Run;
    cbn [phi_worklist] in Run; try discriminate Run.
  destruct pending as [|d rest]; [injection Run as <-; exact Old|].
  destruct (nm_find d phis) as [vs|] eqn:Hit; [|exact (IH rest phis users found result Table Old Run)].
  cbn [option_map] in Run.
  destruct (sort term_compare (filter (fun x => negb (term_eqb x (tmp d))) vs))
    as [|v [|x xs]] eqn:Sorted; try solve [eapply IH; eauto].
  pose proof (singleton_justifies _ _ _ _ _ (Table d vs Hit) Sorted) as J.
  eapply IH; [apply phi_step_preserves; eauto| |exact Run].
  intros u x [E|Hin]; [injection E as <- <-; symmetry; exact (proj1 J)|auto].
Qed.

(** ## Block rewriting *)

(** The optimizer carries a site map alongside its reversed instruction list.
    Projecting away the map lets us compare each retained instruction with
    the one emitted by the backend. *)

(** The instruction loop appends its surviving instructions to the prefix
    that the accumulator already holds in reverse order. *)
Lemma insts_reps_projection : forall reps lbl xs old new out sites,
  option_map fst (insts_reps_map reps lbl old new xs out sites) =
  option_map (fun ys => rev out ++ ys)
    (map_option (inst_reps reps) (filter (fun i => negb (replaced reps i)) xs)).
Proof.
  intros reps lbl xs. induction xs as [|i xs IH]; intros old new out sites.
  - cbn [insts_reps_map map_option option_map filter fst]. rewrite app_nil_r.
    f_equal. symmetry. apply rev_alt.
  - cbn [insts_reps_map filter]. destruct (replaced reps i); cbn [negb].
    + apply IH.
    + cbn [map_option]. destruct (inst_reps reps i) as [j|]; [|reflexivity].
      cbn [emission_sites_rev]. rewrite IH.
      destruct (map_option (inst_reps reps) (filter (fun i => negb (replaced reps i)) xs));
        cbn; [rewrite <- app_assoc|]; reflexivity.
Qed.

(** Forgetting the site map yields exactly the backend block, including
    failure on malformed instructions, phis or jumps. *)
Theorem reps_block_map_equiv : forall reps b,
  option_map fst (reps_block_map reps b) = reps_block reps b.
Proof.
  intros reps b. unfold reps_block_map, reps_block.
  destruct (map_option _ (filter _ (tb_phis b))) as [phis|]; [|reflexivity].
  pose proof (insts_reps_projection reps (tb_label b) (tb_insts b) 0 0 [] []) as E.
  destruct (insts_reps_map reps (tb_label b) 0 0 (tb_insts b) [] []) as [[is sites]|];
    destruct (map_option _ (filter _ (tb_insts b))); cbn in E; try discriminate E;
    try reflexivity. injection E as <-. destruct (jump_reps reps (tb_jump b)); reflexivity.
Qed.

(** ## Allocation bounds and charges *)

(** A local object must contain each recorded access. Its charge includes
    both rounded storage areas and the fixed overhead. *)

(** The bounds test accepts exactly the supported widths whose byte interval
    fits between zero and the allocation size. *)
Theorem access_inside_iff : forall size a,
  access_inside size a = true <->
  exists bytes, width_bytes (snd a) = Some bytes /\ 0 <= fst a /\ fst a + bytes <= size.
Proof.
  intros size a. unfold access_inside. destruct (width_bytes (snd a)) as [n|].
  - rewrite andb_true_iff, !Z.leb_le. split; [intros; exists n; auto|].
    intros [b [E H]]. injection E as <-. exact H.
  - split; [discriminate|intros [b [E _]]; discriminate].
Qed.

(** An object's charge includes two sixteen-byte-rounded regions and a header. *)
Definition local_object_cost (size : Z) : Z := 2 * (Z.div (size + 15) 16 * 16) + 32.

(** The function's total charge sums the charges of the admitted objects. *)
Definition total_local_cost (objs : list (term * Z)) : Z :=
  fold_right (fun p acc => local_object_cost (snd p) + acc) 0 objs.

(** A nonnegative size contributes at least the fixed overhead. *)
Lemma local_cost_minimum : forall size, 0 <= size -> 32 <= local_object_cost size.
Proof.
  intros size H. unfold local_object_cost.
  assert (0 <= (size + 15) / 16) by (apply Z.div_pos; lia). lia.
Qed.

(** Greedy selection returns input objects, charges at most the starting
    budget, and reserves the fixed overhead for every admitted object. *)
Theorem within_budget_sound : forall cands budget, 0 <= budget ->
  (forall a sz, In (a,sz) cands -> 0 <= sz) ->
  incl (within_budget cands budget) cands /\
  total_local_cost (within_budget cands budget) <= budget /\
  (forall a sz, In (a,sz) (within_budget cands budget) -> 32 <= local_object_cost sz).
Proof.
  induction cands as [|[a sz] rest IH]; intros budget B Sizes.
  - split; [apply incl_refl|]. split; [exact B|intros x s []].
  - assert (Tail : forall x s, In (x,s) rest -> 0 <= s) by
      (intros; apply (Sizes x); right; assumption).
    cbn [within_budget]. fold (local_object_cost sz).
    destruct (local_object_cost sz <=? budget) eqn:Fit.
    + apply Z.leb_le in Fit.
      destruct (IH (budget - local_object_cost sz) ltac:(lia) Tail) as [Sub [Cost Min]].
      split; [intros p [E|Hin]; [left; exact E|right; apply Sub; exact Hin]|]. split.
      * change (local_object_cost sz + total_local_cost (within_budget rest (budget - local_object_cost sz)) <= budget). lia.
      * intros x s [E|Hin]; [injection E as <- <-; apply local_cost_minimum;
          apply (Sizes a); left; reflexivity|eauto].
    + destruct (IH budget B Tail) as [Sub [Cost Min]].
      split; [intros p Hp; right; apply Sub; exact Hp|auto].
Qed.

(** The selector records the roots of load types that local storage cannot read. *)
Definition unsupported_roots (addrs : addresses) (insts : list term) : nmap unit :=
  fold_left (fun m i =>
    match let_parts i with
    | Some (_, _, TApp g [t], [addr]) =>
        if String.eqb g "load" then
          match load_width t with
          | Some _ => m
          | None => fold_left (fun m' r => nm_add (fst r) tt m') (address_of addrs addr) m
          end
        else m
    | _ => m
    end) insts nm_empty.

(** A candidate carries its allocation record and all four checks performed
    before the greedy budget walk. *)
Definition eligible (entry : list term) (blocked : nmap unit)
    (classes : list (term * term * option (list acc))) (a : term) (size : Z) : Prop :=
  0 <= size /\ nm_mem a blocked = false /\ entry_local_alloc_ok entry a size = true /\
  exists xs, In (a,TApp "const" [TInt size],Some xs) classes /\
             Forall (fun x => access_inside size x = true) xs.

(** Decoding an integer constant identifies its exact term representation. *)
Lemma const_int_term : forall t n, const_int t = Some n -> t = TApp "const" [TInt n].
Proof.
  intros t n H. destruct t as [| |f [|[z| | |] [|y ys]]|]; try discriminate H.
  cbn [const_int] in H. destruct (String.eqb f "const") eqn:E; try discriminate H.
  apply String.eqb_eq in E. subst f. injection H as <-. reflexivity.
Qed.

(** Selection retains the evidence for each admitted object and bounds the
    total charge even when it admits no objects. *)
Lemma selection_evidence : forall params bs addrs counts,
  let selected := select_local_objects params bs addrs counts in
  total_local_cost selected <= 4096 /\
  forall a size, In (a,size) selected ->
    exists entry rest, bs = entry :: rest /\
      eligible (tb_insts entry) (unsupported_roots addrs (flat_map tb_insts bs))
        (alloc_classes addrs counts params bs) a size.
Proof.
  intros params [|entry rest] addrs counts; cbv zeta.
  - split; [change (0 <= 4096); lia|intros a size []].
  - unfold select_local_objects. fold (unsupported_roots addrs (flat_map tb_insts (entry :: rest))).
    set (blocked := unsupported_roots _ _).
    set (classes := alloc_classes _ _ _ _).
    match goal with |- context [within_budget ?xs _] => set (cands := xs) end.
    assert (Evidence : forall a size, In (a,size) cands -> eligible (tb_insts entry) blocked classes a size).
    { intros a size H. unfold cands in H. apply in_flat_map in H.
      destruct H as [[[d sz] [xs|]] [Member Admit]]; [|contradiction].
      destruct (const_int sz) as [s|] eqn:C; [|contradiction].
      destruct ((_ && _ && _ && _)%bool) eqn:Tests; [|contradiction].
      destruct Admit as [E|[]]. injection E as <- <-.
      apply const_int_term in C. subst sz. repeat rewrite andb_true_iff in Tests.
      destruct Tests as [[[Nonneg Safe] Entry] Bounds].
      apply Z.leb_le in Nonneg. apply negb_true_iff in Safe.
      unfold eligible. repeat split; auto. exists xs. split; [exact Member|].
      apply Forall_forall. apply forallb_forall. exact Bounds. }
    destruct (within_budget_sound cands 4096 ltac:(lia)
      (fun a s H => proj1 (Evidence a s H))) as [Sub [Cost _]].
    split; [exact Cost|]. intros a size H. exists entry, rest.
    split; [reflexivity|apply Evidence; apply Sub; exact H].
Qed.

(** Every selected object has an entry allocation, a nonnegative size and a
    nonescaping class whose recorded byte intervals fit. Together the objects
    use at most 4096 bytes. *)
Theorem select_local_objects_sound : forall params bs addrs counts a size,
  In (a,size) (select_local_objects params bs addrs counts) ->
  (exists entry rest, bs = entry :: rest /\ 0 <= size /\
    entry_local_alloc_ok (tb_insts entry) a size = true /\
    exists accesses,
      In (a,TApp "const" [TInt size],Some accesses) (alloc_classes addrs counts params bs) /\
      Forall (fun x => exists bytes, width_bytes (snd x) = Some bytes /\
                    0 <= fst x /\ fst x + bytes <= size) accesses) /\
  total_local_cost (select_local_objects params bs addrs counts) <= 4096.
Proof.
  intros params bs addrs counts a size H.
  destruct (selection_evidence params bs addrs counts) as [Cost Eligible].
  destruct (Eligible a size H) as (entry & rest & E & Nonneg & _ & Alloc & xs & Member & Bounds).
  split; [|exact Cost]. exists entry, rest. repeat split; auto.
  exists xs. split; [exact Member|].
  eapply Forall_impl; [|exact Bounds]. intros x. apply access_inside_iff.
Qed.

(** ## Access events and instruction rewriting *)

(** An instruction names a root and offset through the address table.
    Escape classification collects its access event before selection tests
    the interval, so the proof follows that event through both passes. *)

(** Widths that compare equal have the same byte count. Only atoms have
    a byte count, and the comparator distinguishes atoms by name. *)
Lemma compared_width : forall x y, term_compare x y = Datatypes.Eq ->
  width_bytes x = width_bytes y.
Proof.
  intros [n|a|f xs|[|u us]] [m|b|g ys|[|v vs]] H; try reflexivity; try discriminate H.
  change (String.compare a b = Datatypes.Eq) in H.
  apply String.compare_eq_iff in H. subst. reflexivity.
Qed.

(** Sorting access records retains a record with the same offset and byte count. *)
Lemma sorted_access : forall xs off w, In (off,w) xs ->
  exists x, In x (sort acc_compare xs) /\ fst x = off /\ width_bytes (snd x) = width_bytes w.
Proof.
  intros xs off w H. apply (sort_carries acc_compare
    (fun x => fst x = off /\ width_bytes (snd x) = width_bytes w)).
  - intros [n t] [m u] E [Offset Width]. unfold acc_compare in E. cbn [fst snd] in E.
    destruct (Z.compare n m) eqn:C; try discriminate E.
    apply Z.compare_eq_iff in C. cbn in Offset, Width |- *. subst m.
    split; [exact Offset|]. rewrite <- (compared_width _ _ E). exact Width.
  - exists (off,w). auto.
Qed.

(** Updating the access table with a single event preserves its old records
    and adds the event's record at the named root. *)
Definition record_access (m : nmap (list acc)) (e : event) :=
  match snd e with
  | Some x => nm_add (fst e) (x :: accs_at m (fst e)) m
  | None => m
  end.

(** Reading a root after one update includes both old and newly recorded accesses. *)
Lemma record_access_in : forall m e a x,
  In x (accs_at m a) \/ e = (a,Some x) -> In x (accs_at (record_access m e) a).
Proof.
  intros m [d [y|]] a x H; cbn [record_access snd fst]; unfold accs_at at 1.
  - rewrite nm_find_add. destruct (name_eqb a d) eqn:E.
    + apply term_eqb_eq in E. subst d. destruct H as [H|H]; [right; exact H|].
      injection H as ->. left. reflexivity.
    + destruct H as [H|H]; [exact H|]. injection H as -> ->.
      unfold name_eqb in E. rewrite term_eqb_refl in E. discriminate.
  - destruct H as [H|H]; [exact H|discriminate].
Qed.

(** The completed event fold contains every access in its input stream. *)
Lemma recorded_access : forall events m a x,
  In (a,Some x) events \/ In x (accs_at m a) ->
  In x (accs_at (fold_left record_access events m) a).
Proof.
  induction events as [|e es IH]; intros m a x H; cbn in *; [tauto|].
  apply IH. destruct H as [[E|Hin]|Old]; [right|auto|right]; apply record_access_in; auto.
Qed.

(** A successful allocation classification contains an equivalent interval
    for each instruction event at that root. *)
Lemma classified_access : forall addrs counts params bs a sz xs i off w,
  In (a,sz,Some xs) (alloc_classes addrs counts params bs) ->
  In i (flat_map tb_insts bs) -> In (a,Some (off,w)) (inst_events addrs i) ->
  exists x, In x xs /\ fst x = off /\ width_bytes (snd x) = width_bytes w.
Proof.
  intros addrs counts params bs a sz xs i off w Class Inst Event.
  unfold alloc_classes in Class. fold record_access in Class.
  apply in_flat_map in Class. destruct Class as [alloc [_ Class]].
  destruct (let_parts alloc) as [[[[d k] op] [|s [|s' ss]]]|]; try contradiction.
  destruct (is_alloc op); try contradiction. apply in_map_iff in Class.
  destruct Class as [root [E _]]. injection E as -> -> E.
  destruct (nm_mem a _) eqn:Esc; try discriminate E. injection E as <-.
  apply sorted_access. apply recorded_access. left. apply in_or_app. left.
  apply in_flat_map. exists i. auto.
Qed.

(** A load that local storage cannot represent places every addressed root
    in the selector's exclusion table. *)
Lemma blocked_load : forall addrs insts i d k t p a off,
  In i insts -> let_parts i = Some (d,k,TApp "load" [t],[p]) ->
  load_width t = None -> address_of addrs p = [(a,off)] ->
  nm_mem a (unsupported_roots addrs insts) = true.
Proof.
  intros addrs insts i d k t p a off Hin Parts Width Addr.
  unfold unsupported_roots.
  generalize (@nm_empty unit). induction insts as [|j js IH]; [contradiction|].
  cbn [fold_left]. intro m. destruct Hin as [E|Later]; [subst j|apply IH; exact Later].
  rewrite Parts, Width, Addr. cbn [fold_left fst].
  apply (fold_property _ (fun m => nm_mem a m = true)).
  - change (nm_mem a (nm_add a tt m) = true). rewrite nm_mem_add. unfold name_eqb. rewrite term_eqb_refl. reflexivity.
  - intros j m' _ Old.
    destruct (let_parts j) as [[[[dst cls] [| |g [|ty [|ty' ts]]|]] [|ptr [|q qs]]]|];
      try exact Old.
    destruct (String.eqb g "load"); [|exact Old].
    destruct (load_width ty); [exact Old|].
    apply (fold_property _ (fun m => nm_mem a m = true)); [exact Old|].
    intros r curr _ Keep. rewrite nm_mem_add, Keep, orb_true_r. reflexivity.
Qed.

(** Every supported local load reads the same width that escape analysis records. *)
Lemma load_slot_agrees : forall t w, load_width t = Some w -> slot_load_width t = Some w.
Proof.
  intros [|s| |] w H; try discriminate H. unfold load_width in H. unfold slot_load_width.
  destruct ((String.eqb s "l" || String.eqb s "p")%bool) eqn:E; [exact H|].
  destruct (String.eqb s "s") eqn:Ss; [apply String.eqb_eq in Ss; subst; discriminate H|].
  destruct (String.eqb s "d") eqn:Sd; [apply String.eqb_eq in Sd; subst; discriminate H|exact H].
Qed.

(** A successful instruction decomposition identifies the complete let term. *)
Lemma let_parts_term : forall i d k op args, let_parts i = Some (d,k,op,args) ->
  i = TApp "let" [d;k;op;TList args].
Proof.
  intros i d k op args H. unfold let_parts in H.
  destruct i as [| |f [|x [|y [|z [|[| | |vs] [|q qs]]]]]|]; try discriminate H.
  destruct (String.eqb f "let") eqn:E; try discriminate H.
  apply String.eqb_eq in E. subst f. injection H as -> -> -> ->. reflexivity.
Qed.

(** A selected root's map entry supplies its exact size, its load-type
    check and a bound for every instruction event at that root. *)
Lemma selected_events : forall params bs addrs counts a,
  let objs := nm_of_list (select_local_objects params bs addrs counts) in
  nm_mem a objs = true ->
  exists size, nm_find a objs = Some size /\
    nm_mem a (unsupported_roots addrs (flat_map tb_insts bs)) = false /\
    forall i off w, In i (flat_map tb_insts bs) ->
      In (a,Some (off,w)) (inst_events addrs i) ->
      exists bytes, width_bytes w = Some bytes /\ 0 <= off /\ off + bytes <= size.
Proof.
  intros params bs addrs counts a objs Mem. unfold nm_mem in Mem.
  destruct (nm_find a objs) as [size|] eqn:Find; try discriminate Mem.
  exists size. split; [reflexivity|].
  apply pairs_lookup in Find. destruct (selection_evidence params bs addrs counts) as [_ Select].
  destruct (Select a size Find) as (entry & rest & E & N & Supported & Alloc & xs & Class & Bounds).
  split; [exact Supported|]. intros i off w Hi Ev.
  destruct (classified_access _ _ _ _ _ _ _ _ _ _ Class Hi Ev) as (x & Hx & Offset & Width).
  rewrite Forall_forall in Bounds. pose proof (proj1 (access_inside_iff size x) (Bounds x Hx)) as Bound.
  rewrite Offset, Width in Bound. exact Bound.
Qed.

(** Every rewritten access names a single selected root and preserves its
    offset and operands. When the object map comes from this function's
    selector, its recorded size bounds the whole load or store. *)
Theorem local_access_spec : forall objects addrs i i',
  local_access objects addrs i = Some i' ->
  (exists d k t p a off,
    i = TApp "let" [d;k;TApp "load" [t];TList [p]] /\
    address_of addrs p = [(a,off)] /\ nm_mem a objects = true /\
    i' = TApp "local_load" [d;k;t;a;TInt off] /\
    forall params bs counts, objects = nm_of_list (select_local_objects params bs addrs counts) ->
      In i (flat_map tb_insts bs) ->
      exists size w bytes, nm_find a objects = Some size /\ load_width t = Some w /\
        width_bytes w = Some bytes /\ 0 <= off /\ off + bytes <= size)
  \/ (exists w v p a off, i = TApp "store" [w;v;p] /\
    address_of addrs p = [(a,off)] /\ nm_mem a objects = true /\
    i' = TApp "local_store" [w;v;a;TInt off] /\
    forall params bs counts, objects = nm_of_list (select_local_objects params bs addrs counts) ->
      In i (flat_map tb_insts bs) ->
      exists size bytes, nm_find a objects = Some size /\ width_bytes w = Some bytes /\
        0 <= off /\ off + bytes <= size).
Proof.
  intros objects addrs i i' Run. unfold local_access in Run.
  destruct (let_parts i) as [[[[d k] op] args]|] eqn:Parts.
  - destruct op as [| |g [|t [|q qs]]|]; try discriminate Run.
    destruct args as [|p [|q qs]]; try discriminate Run.
    destruct (String.eqb g "load") eqn:G; try discriminate Run. apply String.eqb_eq in G. subst g.
    destruct (address_of addrs p) as [|[a off] [|r rs]] eqn:Addr; try discriminate Run.
    destruct (nm_mem a objects) eqn:Mem; try discriminate Run. injection Run as <-.
    pose proof (let_parts_term _ _ _ _ _ Parts) as Shape.
    left. exists d,k,t,p,a,off. repeat split; auto. intros params bs counts -> Hi.
    destruct (selected_events params bs addrs counts a Mem) as (size & Find & Safe & Bound).
    destruct (load_width t) as [w|] eqn:Width.
    + assert (Ev : In (a,Some (off,w)) (inst_events addrs i)).
      { rewrite Shape. cbn [inst_events]. change (In (a,Some (off,w))
          (map (fun r => (fst r, option_map (fun w => (snd r,w)) (slot_load_width t)))
            (address_of addrs p))). rewrite Addr, (load_slot_agrees _ _ Width). left. reflexivity. }
      destruct (Bound _ _ _ Hi Ev) as [bytes Hb]. exists size,w,bytes. tauto.
    + pose proof (blocked_load _ _ _ _ _ _ _ _ _ Hi Parts Width Addr) as Block. congruence.
  - destruct i as [| |f [|w [|v [|p [|q qs]]]]|]; try discriminate Run.
    destruct (String.eqb f "store") eqn:G; try discriminate Run. apply String.eqb_eq in G. subst f.
    destruct (address_of addrs p) as [|[a off] [|r rs]] eqn:Addr; try discriminate Run.
    destruct (nm_mem a objects) eqn:Mem; try discriminate Run. injection Run as <-.
    right. exists w,v,p,a,off. repeat split; auto. intros params bs counts -> Hi.
    destruct (selected_events params bs addrs counts a Mem) as (size & Find & Safe & Bound).
    assert (Ev : In (a,Some (off,w)) (inst_events addrs (TApp "store" [w;v;p]))).
    { change (In (a,Some (off,w)) (escapes_of addrs [v] ++
        map (fun r => (fst r,Some (snd r,w))) (address_of addrs p))).
      rewrite Addr. apply in_or_app. right. left. reflexivity. }
    destruct (Bound _ _ _ Hi Ev) as [bytes Hb]. exists size,bytes. tauto.
Qed.
