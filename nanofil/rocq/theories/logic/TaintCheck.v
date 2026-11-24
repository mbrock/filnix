(** Constant-time proofs split cleanly into two independent concerns: ordinary
    memory safety (the machine never traps, panics, or goes stuck) and
    [[poison]] discipline (no secret ever reaches a branch, a memory address,
    or a variable-time instruction). Because [pstep] executes [Semantics.step]
    and [tstep] in lockstep without altering program values, a reflective
    abstract taint checker can verify the entire poison discipline by
    computation (`vm_compute`) without adding any taint state or runtime
    overhead to the value-and-bounds abstract runner in `theories/exec`.

    This module defines that orthogonal taint checker and proves the factoring
    theorem that lifts it to [poison_safe] and two-run constant-time trace
    equivalence. A caller supplies a taint specification [tspec] for each
    function in a call graph, lets the untrusted inference pass [taint_infer]
    compute a fixed-point taint environment for every reachable block, and
    checks the resulting block table with [taint_verify]. Any plain memory
    safety proof ([plain_safe]) then combines with [taint_check_program] to
    establish [poison_safe] and identical plain operational leakage traces
    across all secret inputs. *)

From Stdlib Require Import String ZArith List Bool Lia Relations.
From Nanofil Require Import Term Maps Syntax Values Memory Runtime Ops Semantics
  Run Machine Panics StepRules PoisonModel PoisonLogic.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

(** ## Specifications and taint ordering

    Each function in a verified call graph carries a [tspec] bounding its
    input argument taints, its return taint, and the ceiling on memory byte
    and shadow capability taints that it may read or write. The boolean
    order [tenv_le] checks that one taint environment is pointwise below
    another on every variable the target environment needs. *)

(** A taint specification bounds parameter taints, return taint, the maximum
    byte and capability taint in memory, and whether the function may execute
    memory stores. *)
Record tspec : Type := mkTSpec {
  ts_args : list word_taint;
  ts_ret : option word_taint;
  ts_mem : taint;
  ts_aux : taint;
  ts_writes : bool
}.

(** Checking whether [te1] satisfies all upper bounds recorded in [te2].
    Every temporary named in [te2] must appear in [te1] with a taint at or
    below [te2]'s bound; extra temporaries in [te1] are ignored. *)
Definition tenv_le (te1 te2 : tenv) : bool :=
  forallb (fun '(x, wt2) =>
    match lookup x te1 with
    | Some wt1 => wt_le wt1 wt2
    | None => false
    end) te2.

(** Propositional version of [tenv_le]: every lookup in [te2] succeeds in
    [te1] with a smaller or equal word taint. *)
Definition tenv_le_prop (te1 te2 : tenv) : Prop :=
  forall x wt2, lookup x te2 = Some wt2 ->
    exists wt1, lookup x te1 = Some wt1 /\ wt_le wt1 wt2 = true.

(** Any successful [lookup] returns a pair that belongs to the association list. *)
Lemma lookup_in {A : Type} (x : name) (v : A) (m : list (name * A)) :
  lookup x m = Some v -> In (x, v) m.
Proof.
  induction m as [|[k w] m IH]; cbn [lookup]; [discriminate|].
  destruct (name_eqb x k) eqn:E.
  - intros [= ->]. unfold name_eqb in E. apply term_eqb_eq in E. subst k. left. reflexivity.
  - intros H. right. exact (IH H).
Qed.

(** The executable check [tenv_le] implies [tenv_le_prop] without requiring
    unique keys. *)
Lemma tenv_le_sound te1 te2 :
  tenv_le te1 te2 = true -> tenv_le_prop te1 te2.
Proof.
  intros H x wt2 Hlk. unfold tenv_le in H.
  rewrite forallb_forall in H.
  pose proof (H (x, wt2) (lookup_in x wt2 te2 Hlk)) as Hx.
  cbn in Hx.
  destruct (lookup x te1) as [wt1|]; [|discriminate Hx].
  exists wt1. split; [reflexivity | exact Hx].
Qed.

(** [wt_le] is reflexive. *)
Lemma wt_le_refl wt : wt_le wt wt = true.
Proof. destruct wt; cbn [wt_le]; rewrite !taint_le_refl; reflexivity. Qed.

(** [wt_le] is transitive. *)
Lemma wt_le_trans a b c :
  wt_le a b = true -> wt_le b c = true -> wt_le a c = true.
Proof.
  destruct a, b, c; cbn [wt_le]; try discriminate; intros H1 H2.
  - eapply taint_le_trans; eassumption.
  - apply andb_prop in H1; destruct H1 as [H1a H1c]; apply andb_prop in H2; destruct H2 as [H2a H2c].
    rewrite (taint_le_trans _ _ _ H1a H2a), (taint_le_trans _ _ _ H1c H2c); reflexivity.
  - apply andb_prop in H1; destruct H1 as [H1a H1c]; apply andb_prop in H2; destruct H2 as [H2a H2c].
    rewrite (taint_le_trans _ _ _ H1a H2a), (taint_le_trans _ _ _ H1c H2c); reflexivity.
Qed.

(** [taint_bot] sits below every taint. *)
Lemma taint_le_bot_l t : taint_le taint_bot t = true.
Proof. destruct t; reflexivity. Qed.

(** [taint_all] sits above every taint. *)
Lemma taint_le_all_r t : taint_le t taint_all = true.
Proof. destruct t as [[] [] []]; reflexivity. Qed.

(** Joining two taints respects [taint_le] in both arguments. *)
Lemma taint_le_join_mono a1 a2 b1 b2 :
  taint_le a1 a2 = true -> taint_le b1 b2 = true ->
  taint_le (taint_join a1 b1) (taint_join a2 b2) = true.
Proof.
  destruct a1, a2, b1, b2; unfold taint_le, taint_join; cbn;
    intros H1 H2;
    repeat match goal with
    | H : (_ && _) = true |- _ => apply andb_prop in H; destruct H
    end;
    repeat match goal with
    | b : bool |- _ => destruct b
    end; try discriminate; reflexivity.
Qed.

(** Every scalar taint component of a smaller taint is false whenever the
    larger taint's component is false. *)
Lemma taint_le_branch a b :
  taint_le a b = true -> t_branch b = false -> t_branch a = false.
Proof. destruct a as [[] [] []], b as [[] [] []]; unfold taint_le; cbn; intros H1 H2; try discriminate; reflexivity. Qed.

Lemma taint_le_index a b :
  taint_le a b = true -> t_index b = false -> t_index a = false.
Proof. destruct a as [[] [] []], b as [[] [] []]; unfold taint_le; cbn; intros H1 H2; try discriminate; reflexivity. Qed.

Lemma taint_le_vartime a b :
  taint_le a b = true -> t_vartime b = false -> t_vartime a = false.
Proof. destruct a as [[] [] []], b as [[] [] []]; unfold taint_le; cbn; intros H1 H2; try discriminate; reflexivity. Qed.

(** Joining a list of taints respects pointwise [taint_le]. *)
Lemma join_taints_mono ts1 ts2 :
  Forall2 (fun a b => taint_le a b = true) ts1 ts2 ->
  taint_le (join_taints ts1) (join_taints ts2) = true.
Proof.
  induction 1 as [|a b l1 l2 Hab _ IH]; cbn [join_taints].
  - apply taint_le_refl.
  - apply taint_le_join_mono; assumption.
Qed.

(** [tenv_le_prop] is reflexive and transitive. *)
Lemma tenv_le_prop_refl te : tenv_le_prop te te.
Proof. intros x wt H. exists wt. split; [exact H | apply wt_le_refl]. Qed.

Lemma tenv_le_prop_trans te1 te2 te3 :
  tenv_le_prop te1 te2 -> tenv_le_prop te2 te3 -> tenv_le_prop te1 te3.
Proof.
  intros H12 H23 x wt3 H3.
  destruct (H23 x wt3 H3) as (wt2 & H2 & Hle23).
  destruct (H12 x wt2 H2) as (wt1 & H1 & Hle12).
  exists wt1. split; [exact H1 | eapply wt_le_trans; eassumption].
Qed.

(** Binding a temporary to a smaller taint preserves [tenv_le_prop]. *)
Lemma tenv_le_prop_put d wt1 wt2 te1 te2 :
  wt_le wt1 wt2 = true ->
  tenv_le_prop te1 te2 ->
  tenv_le_prop (put d wt1 te1) (put d wt2 te2).
Proof.
  intros Hw Hte x wt Hlk.
  rewrite lookup_put_name in Hlk. rewrite lookup_put_name.
  destruct (name_eqb x d) eqn:E.
  - injection Hlk as <-. exists wt1. split; [reflexivity | exact Hw].
  - exact (Hte x wt Hlk).
Qed.

(** Reading [wt_at_class] preserves [wt_le]. *)
Lemma wt_at_class_mono k wt1 wt2 wt2' :
  wt_le wt1 wt2 = true ->
  wt_at_class k wt2 = Some wt2' ->
  exists wt1', wt_at_class k wt1 = Some wt1' /\ wt_le wt1' wt2' = true.
Proof.
  intros Hle Hat.
  destruct wt1, wt2; cbn [wt_le] in Hle; try discriminate;
    destruct k; cbn [wt_at_class] in Hat |- *; try discriminate;
    injection Hat as <-; eexists; split; try reflexivity; exact Hle.
Qed.

(** Evaluating an operand taint with [value_t] is monotone in the environment. *)
Lemma value_t_mono te1 te2 k v wt2 :
  tenv_le_prop te1 te2 ->
  value_t te2 k v = Some wt2 ->
  exists wt1, value_t te1 k v = Some wt1 /\ wt_le wt1 wt2 = true.
Proof.
  intros Hte Hv. destruct v as [n | z | g]; cbn [value_t] in Hv |- *.
  - destruct (lookup n te2) as [w2|] eqn:E2; [|discriminate Hv].
    destruct (Hte n w2 E2) as (w1 & E1 & Hle).
    rewrite E1. exact (wt_at_class_mono k w1 w2 wt2 Hle Hv).
  - injection Hv as <-. exists (wt_bot k). split; [reflexivity | apply wt_le_refl].
  - injection Hv as <-. exists (WTPtr taint_bot taint_bot). split; [reflexivity | apply wt_le_refl].
Qed.

(** Reading multiple operand taints is monotone. *)
Lemma map2_value_t_mono te1 te2 cls args wts2 :
  tenv_le_prop te1 te2 ->
  map2_option (value_t te2) cls args = Some wts2 ->
  exists wts1, map2_option (value_t te1) cls args = Some wts1 /\
    Forall2 (fun a b => wt_le a b = true) wts1 wts2.
Proof.
  revert args wts2. induction cls as [|k cls IH]; intros [|v args] wts2 Hte H; cbn in H; try discriminate.
  - injection H as <-. exists []. split; [reflexivity | constructor].
  - destruct (value_t te2 k v) as [w2|] eqn:Ev; [|discriminate].
    destruct (map2_option (value_t te2) cls args) as [ws2|] eqn:Ews; [|discriminate].
    injection H as <-.
    destruct (value_t_mono te1 te2 k v w2 Hte Ev) as (w1 & Ev1 & Hle).
    destruct (IH args ws2 Hte Ews) as (ws1 & Ews1 & Hles).
    exists (w1 :: ws1). cbn. rewrite Ev1, Ews1. split; [reflexivity | constructor; assumption].
Qed.

(** Reading call argument taints is monotone. *)
Lemma map_arg_t_mono te1 te2 args wts2 :
  tenv_le_prop te1 te2 ->
  map_option (arg_t te2) args = Some wts2 ->
  exists wts1, map_option (arg_t te1) args = Some wts1 /\
    Forall2 (fun a b => wt_le a b = true) wts1 wts2.
Proof.
  revert wts2. induction args as [|[k v] args IH]; intros wts2 Hte H; cbn in H.
  - injection H as <-. exists []. split; [reflexivity | constructor].
  - destruct (value_t te2 k v) as [w2|] eqn:Ev; [|discriminate].
    destruct (map_option (arg_t te2) args) as [ws2|] eqn:Ews; [|discriminate].
    injection H as <-.
    destruct (value_t_mono te1 te2 k v w2 Hte Ev) as (w1 & Ev1 & Hle).
    destruct (IH ws2 Hte eq_refl) as (ws1 & Ews1 & Hles).
    exists (w1 :: ws1). cbn. rewrite Ev1, Ews1. split; [reflexivity | constructor; assumption].
Qed.

(** Extracting scalar taints from word taints is monotone. *)
Lemma map_scalar_wt_mono wts1 wts2 ts2 :
  Forall2 (fun a b => wt_le a b = true) wts1 wts2 ->
  map_option scalar_wt wts2 = Some ts2 ->
  exists ts1, map_option scalar_wt wts1 = Some ts1 /\
    Forall2 (fun a b => taint_le a b = true) ts1 ts2.
Proof.
  intros Hfa. revert ts2. induction Hfa as [|w1 w2 ws1 ws2 Hle _ IH]; intros ts2 H; cbn in H.
  - injection H as <-. exists []. split; [reflexivity | constructor].
  - destruct w2 as [t2| |]; cbn [scalar_wt] in H; try discriminate.
    destruct w1 as [t1| |]; cbn [wt_le] in Hle; try discriminate.
    destruct (map_option scalar_wt ws2) as [ts2'|] eqn:E2; [|discriminate].
    injection H as <-.
    destruct (IH ts2' eq_refl) as (ts1' & E1 & Hles).
    exists (t1 :: ts1'). cbn. rewrite E1. split; [reflexivity | constructor; assumption].
Qed.

(** Reading [[flight]] arguments and lower capability donors is monotone. *)
Lemma flight_arg_t_mono te1 te2 a t2 :
  tenv_le_prop te1 te2 ->
  flight_arg_t te2 a = Some t2 ->
  exists t1, flight_arg_t te1 a = Some t1 /\ taint_le t1 t2 = true.
Proof.
  intros Hte H. destruct a as [v | v]; cbn [flight_arg_t] in H |- *.
  - destruct (value_t te2 L v) as [wt2|] eqn:E2; [|discriminate].
    destruct (value_t_mono te1 te2 L v wt2 Hte E2) as (wt1 & E1 & Hle).
    rewrite E1. destruct wt2 as [ta2| |]; try discriminate; injection H as <-;
      destruct wt1 as [ta1| |]; cbn [wt_le] in Hle; try discriminate.
    exists ta1; split; [reflexivity | exact Hle].
  - destruct (value_t te2 P v) as [wt2|] eqn:E2; [|discriminate].
    destruct (value_t_mono te1 te2 P v wt2 Hte E2) as (wt1 & E1 & Hle).
    rewrite E1. destruct wt2 as [ta2|ta2 tc2|]; try discriminate; injection H as <-;
      destruct wt1 as [ta1|ta1 tc1|]; cbn [wt_le] in Hle; try discriminate.
    + exists ta1; split; [reflexivity | exact Hle].
    + apply andb_prop in Hle; destruct Hle as [Hla _]. exists ta1; split; [reflexivity | exact Hla].
Qed.

Lemma map_flight_arg_t_mono te1 te2 args ts2 :
  tenv_le_prop te1 te2 ->
  map_option (flight_arg_t te2) args = Some ts2 ->
  exists ts1, map_option (flight_arg_t te1) args = Some ts1 /\
    Forall2 (fun a b => taint_le a b = true) ts1 ts2.
Proof.
  revert ts2. induction args as [|a args IH]; intros ts2 Hte H; cbn in H.
  - injection H as <-. exists []. split; [reflexivity | constructor].
  - destruct (flight_arg_t te2 a) as [t2|] eqn:Ea; [|discriminate].
    destruct (map_option (flight_arg_t te2) args) as [ts2'|] eqn:E2; [|discriminate].
    injection H as <-.
    destruct (flight_arg_t_mono te1 te2 a t2 Hte Ea) as (t1 & Ea1 & Hle).
    destruct (IH ts2' Hte eq_refl) as (ts1' & E1 & Hles).
    exists (t1 :: ts1'). cbn. rewrite Ea1, E1. split; [reflexivity | constructor; assumption].
Qed.

Lemma flight_cap_t_mono te1 te2 lw t2 :
  tenv_le_prop te1 te2 ->
  flight_cap_t te2 lw = Some t2 ->
  exists t1, flight_cap_t te1 lw = Some t1 /\ taint_le t1 t2 = true.
Proof.
  intros Hte H. destruct lw as [|v]; cbn [flight_cap_t] in H |- *.
  - injection H as <-. exists taint_bot. split; [reflexivity | apply taint_le_refl].
  - destruct (value_t te2 P v) as [wt2|] eqn:E2; [|discriminate].
    destruct (value_t_mono te1 te2 P v wt2 Hte E2) as (wt1 & E1 & Hle).
    rewrite E1. destruct wt2 as [ta2|ta2 tc2|]; try discriminate; injection H as <-;
      destruct wt1 as [ta1|ta1 tc1|]; cbn [wt_le] in Hle; try discriminate.
    + exists taint_bot; split; [reflexivity | apply taint_le_refl].
    + apply andb_prop in Hle; destruct Hle as [_ Hlc]. exists tc1; split; [reflexivity | exact Hlc].
Qed.

(** Checking pointer bounds taint is monotone: if larger taints pass,
    smaller taints pass as well. *)
Lemma check_ptr_bounds_taint_mono pol ta1 ta2 tc1 tc2 :
  taint_le ta1 ta2 = true -> taint_le tc1 tc2 = true ->
  check_ptr_bounds_taint pol ta2 tc2 = None ->
  check_ptr_bounds_taint pol ta1 tc1 = None.
Proof.
  unfold check_ptr_bounds_taint. intros Ha Hc H.
  destruct (pol_check_branches pol); [|reflexivity].
  destruct (t_branch ta2) eqn:Eb2; [discriminate|].
  destruct (t_branch tc2) eqn:Ebc2; [discriminate|].
  destruct (t_index tc2) eqn:Eic2; [discriminate|].
  rewrite (taint_le_branch _ _ Ha Eb2), (taint_le_branch _ _ Hc Ebc2), (taint_le_index _ _ Hc Eic2).
  reflexivity.
Qed.

(** Evaluating [[phi]] nodes is monotone in the taint environment. *)
Lemma phis_tenv_mono phis from te1 te2 te2' :
  tenv_le_prop te1 te2 ->
  phis_tenv phis from te2 = Some te2' ->
  exists te1', phis_tenv phis from te1 = Some te1' /\ tenv_le_prop te1' te2'.
Proof.
  intros Hte H. unfold phis_tenv in *.
  destruct from as [pred|].
  - assert (Hgen : forall acc1 acc2,
      tenv_le_prop acc1 acc2 ->
      fold_left (fun acc ph =>
                   let* te := acc in
                   match ph with
                   | Phi d k pairs =>
                       let* v := lookup pred pairs in
                       let* wt := value_t te2 k v in
                       Some (put d wt te)
                   end) phis (Some acc2) = Some te2' ->
      exists te1',
        fold_left (fun acc ph =>
                     let* te := acc in
                     match ph with
                     | Phi d k pairs =>
                         let* v := lookup pred pairs in
                         let* wt := value_t te1 k v in
                         Some (put d wt te)
                     end) phis (Some acc1) = Some te1' /\
        tenv_le_prop te1' te2').
    { clear H. induction phis as [|[d k pairs] phis IH]; intros acc1 acc2 Hacc Hfold; cbn [fold_left] in *.
      - injection Hfold as <-. exists acc1. split; [reflexivity | exact Hacc].
      - destruct (lookup pred pairs) as [v|] eqn:El;
          [|exfalso; clear -Hfold; induction phis as [|ph' phis' IH']; [discriminate | cbn [fold_left] in Hfold; exact (IH' Hfold)]].
        destruct (value_t te2 k v) as [w2|] eqn:Ev2;
          [|exfalso; clear -Hfold; induction phis as [|ph' phis' IH']; [discriminate | cbn [fold_left] in Hfold; exact (IH' Hfold)]].
        destruct (value_t_mono te1 te2 k v w2 Hte Ev2) as (w1 & Ev1 & Hle).
        rewrite Ev1. apply (IH _ _ (tenv_le_prop_put d w1 w2 acc1 acc2 Hle Hacc) Hfold). }
    exact (Hgen te1 te2 Hte H).
  - destruct phis; [|discriminate]. injection H as <-.
    exists te1. split; [reflexivity | exact Hte].
Qed.

(** Binding call parameters is monotone in the argument taint list. *)
Lemma call_tenv_mono f wts1 wts2 te2 :
  Forall2 (fun a b => wt_le a b = true) wts1 wts2 ->
  call_tenv f wts2 = Some te2 ->
  exists te1, call_tenv f wts1 = Some te1 /\ tenv_le_prop te1 te2.
Proof.
  intros Hall H. unfold call_tenv in *.
  pose proof (Forall2_length Hall) as Hlen.
  rewrite Hlen.
  destruct (length wts2 <? length (fn_params f))%nat; [discriminate|].
  injection H as <-. eexists. split; [reflexivity|].
  assert (Hfirst : Forall2 (fun a b => wt_le a b = true)
                     (firstn (length (fn_params f)) wts1)
                     (firstn (length (fn_params f)) wts2)).
  { clear -Hall. revert wts1 wts2 Hall. generalize (length (fn_params f)).
    intros n. induction n as [|n IH]; intros l1 l2 H; [constructor|].
    destruct H as [|a1 a2 l1 l2 Ha Hl]; cbn; constructor; [exact Ha | apply IH; exact Hl]. }
  assert (Hfold : forall (ps : list (class * name)) l1 l2 acc1 acc2,
    Forall2 (fun a b => wt_le a b = true) l1 l2 ->
    tenv_le_prop acc1 acc2 ->
    tenv_le_prop
      (fold_left (fun te px => put (snd (fst px)) (snd px) te) (combine ps l1) acc1)
      (fold_left (fun te px => put (snd (fst px)) (snd px) te) (combine ps l2) acc2)).
  { induction ps as [|[k d] ps IH]; intros l1 l2 acc1 acc2 Hl Hacc; [exact Hacc|].
    destruct Hl as [|w1 w2 l1 l2 Hw Hl]; cbn [combine fold_left fst snd]; [exact Hacc|].
    apply IH; [exact Hl | apply tenv_le_prop_put; assumption]. }
  apply Hfold; [exact Hfirst | apply tenv_le_prop_refl].
Qed.

(** Binding return taints into a caller environment is monotone. *)
Lemma returned_tenv_mono r ots1 ots2 te1 te2 te2' :
  Forall2 (fun a b => wt_le a b = true) ots1 ots2 ->
  tenv_le_prop te1 te2 ->
  returned_tenv r ots2 te2 = Some te2' ->
  exists te1', returned_tenv r ots1 te1 = Some te1' /\ tenv_le_prop te1' te2'.
Proof.
  intros Hots Hte H. unfold returned_tenv in *.
  destruct r as [| d k | rs].
  - injection H as <-. exists te1. split; [reflexivity | exact Hte].
  - destruct Hots as [|w1 w2 l1 l2 Hw Hl]; [discriminate|].
    destruct l2; [|discriminate].
    inversion Hl; subst.
    destruct (wt_at_class k w2) as [w2'|] eqn:E2; [|discriminate].
    injection H as <-.
    destruct (wt_at_class_mono k w1 w2 w2' Hw E2) as (w1' & E1 & Hle').
    rewrite E1. exists (put d w1' te1).
    split; [reflexivity | apply tenv_le_prop_put; assumption].
  - pose proof (Forall2_length Hots) as Hlen. rewrite Hlen.
    destruct (negb (length ots2 =? length rs)%nat); [discriminate|].
    assert (Hgen : forall rs' l1 l2 acc1 acc2,
      Forall2 (fun a b => wt_le a b = true) l1 l2 ->
      tenv_le_prop acc1 acc2 ->
      fold_left (fun acc rx =>
                   let* te' := acc in
                   let* wt' := wt_at_class (snd (fst rx)) (snd rx) in
                   Some (put (fst (fst rx)) wt' te')) (combine rs' l2) (Some acc2) = Some te2' ->
      exists te1',
        fold_left (fun acc rx =>
                     let* te' := acc in
                     let* wt' := wt_at_class (snd (fst rx)) (snd rx) in
                     Some (put (fst (fst rx)) wt' te')) (combine rs' l1) (Some acc1) = Some te1' /\
        tenv_le_prop te1' te2').
    { clear H Hots Hlen. induction rs' as [|[d k] rs' IH]; intros l1 l2 acc1 acc2 Hl Hacc Hf; cbn [combine fold_left] in *.
      - injection Hf as <-. exists acc1. split; [reflexivity | exact Hacc].
      - destruct Hl as [|w1 w2 l1 l2 Hw Hl]; cbn [combine fold_left fst snd] in *.
        + injection Hf as <-. exists acc1. split; [reflexivity | exact Hacc].
        + destruct (wt_at_class k w2) as [w2'|] eqn:E2;
            [|exfalso; clear -Hf; induction (combine rs' l2) as [|rx' l' IH']; [discriminate | cbn [fold_left] in Hf; exact (IH' Hf)]].
          destruct (wt_at_class_mono k w1 w2 w2' Hw E2) as (w1' & E1 & Hle').
          rewrite E1. apply (IH _ _ _ _ Hl (tenv_le_prop_put d w1' w2' acc1 acc2 Hle' Hacc) Hf). }
    exact (Hgen rs ots1 ots2 te1 te2 Hots Hte H).
Qed.

(** ## Memory poison ceiling

    The checker avoids tracking exact byte offsets by bounding the poison
    state globally: every byte in memory permits loads and stays within
    [t_mem], every shadow slot stays within [t_aux], and if the function
    performs stores then every byte permits stores as well. *)

(** A concrete poison memory and shadow taint map respect the ceiling
    declared by a [tspec]. *)
Definition pm_admissible (t_mem t_aux : taint) (writes : bool)
    (pm : Z -> poison_byte) (paux : Z -> taint) : Prop :=
  (forall a, pb_no_load (pm a) = false /\
             taint_le (pb_taint (pm a)) t_mem = true /\
             (writes = true -> pb_no_store (pm a) = false)) /\
  (forall a, taint_le (paux a) t_aux = true).

(** A smaller specification's ceiling implies admissibility for a larger one. *)
Lemma pm_admissible_weaken t_mem1 t_aux1 w1 t_mem2 t_aux2 w2 pm paux :
  taint_le t_mem1 t_mem2 = true ->
  taint_le t_aux1 t_aux2 = true ->
  implb w2 w1 = true ->
  pm_admissible t_mem1 t_aux1 w1 pm paux ->
  pm_admissible t_mem2 t_aux2 w2 pm paux.
Proof.
  intros Hm Ha Hw [Hpm Hpaux]. split.
  - intros a. destruct (Hpm a) as (Hnl & Hlt & Hns). repeat split.
    + exact Hnl.
    + eapply taint_le_trans; eassumption.
    + intros Hw2. apply Hns. destruct w1, w2; cbn in Hw; try discriminate; reflexivity.
  - intros a. eapply taint_le_trans; [apply Hpaux | exact Ha].
Qed.

(** Loading [sz] bytes from an admissible poison memory never faults with
    [PoisonLoad] and yields a taint bounded by [t_mem]. *)
Lemma mem_no_load_admissible t_mem t_aux w pm paux addr sz :
  pm_admissible t_mem t_aux w pm paux ->
  mem_no_load pm addr sz = false.
Proof.
  intros [Hpm _]. unfold mem_no_load.
  assert (Hgen : forall n a, range_no_load_nat pm a n = false).
  { induction n as [|n IH]; intros a; [reflexivity|].
    cbn [range_no_load_nat]. destruct (Hpm a) as [Hnl _]. rewrite Hnl. exact (IH (a + 1)). }
  exact (Hgen (Z.to_nat sz) addr).
Qed.

Lemma mem_load_taint_admissible t_mem t_aux w pm paux addr sz :
  pm_admissible t_mem t_aux w pm paux ->
  taint_le (mem_load_taint pm addr sz) t_mem = true.
Proof.
  intros [Hpm _]. unfold mem_load_taint.
  assert (Hgen : forall n a, taint_le (range_taint_nat pm a n) t_mem = true).
  { induction n as [|n IH]; intros a; [apply taint_le_bot_l|].
    cbn [range_taint_nat]. rewrite taint_join_lub.
    destruct (Hpm a) as (_ & Hlt & _). rewrite Hlt, (IH (a + 1)). reflexivity. }
  exact (Hgen (Z.to_nat sz) addr).
Qed.

(** Storing [sz] bytes into an admissible writable poison memory never faults
    with [PoisonStore] and preserves [pm_admissible] whenever the stored
    taint stays within [t_mem]. *)
Lemma mem_no_store_admissible t_mem t_aux pm paux addr sz :
  pm_admissible t_mem t_aux true pm paux ->
  mem_no_store pm addr sz = false.
Proof.
  intros [Hpm _]. unfold mem_no_store.
  assert (Hgen : forall n a, range_no_store_nat pm a n = false).
  { induction n as [|n IH]; intros a; [reflexivity|].
    cbn [range_no_store_nat]. destruct (Hpm a) as (_ & _ & Hns). rewrite (Hns eq_refl). exact (IH (a + 1)). }
  exact (Hgen (Z.to_nat sz) addr).
Qed.

Lemma note_store_byte_admissible t_mem t pb :
  pb_no_load pb = false ->
  pb_no_store pb = false ->
  taint_le (pb_taint pb) t_mem = true ->
  taint_le t t_mem = true ->
  pb_no_load (note_store_byte t pb) = false /\
  pb_no_store (note_store_byte t pb) = false /\
  taint_le (pb_taint (note_store_byte t pb)) t_mem = true.
Proof.
  destruct pb as [nl ns cb ci cv [tb ti tv]], t as [sb si sv], t_mem as [mb mi mv].
  unfold note_store_byte, note_dim, taint_le; cbn.
  intros Hnl Hns Hpb Hs.
  destruct sb, si, sv; cbn; repeat split;
    try exact Hnl; try exact Hns;
    destruct mb, mi, mv, tb, ti, tv, cb, ci, cv;
    cbn in *; try discriminate; reflexivity.
Qed.

Lemma mem_store_taint_admissible t_mem t_aux pm paux addr sz t :
  taint_le t t_mem = true ->
  pm_admissible t_mem t_aux true pm paux ->
  pm_admissible t_mem t_aux true (mem_store_taint pm addr sz t) paux.
Proof.
  intros Ht [Hpm Hpaux]. split; [|exact Hpaux].
  intros a. unfold mem_store_taint.
  destruct ((addr <=? a) && (a <? addr + sz)).
  - destruct (Hpm a) as (Hnl & Hlt & Hns).
    destruct (note_store_byte_admissible t_mem t (pm a) Hnl (Hns eq_refl) Hlt Ht) as (H1 & H2 & H3).
    repeat split; auto.
  - exact (Hpm a).
Qed.

Lemma paux_store_admissible t_mem t_aux w pm paux addr tc :
  taint_le tc t_aux = true ->
  pm_admissible t_mem t_aux w pm paux ->
  pm_admissible t_mem t_aux w pm (fun b => if b =? addr then tc else paux b).
Proof.
  intros Htc [Hpm Hpaux]. split; [exact Hpm|].
  intros b. destruct (b =? addr); [exact Htc | apply Hpaux].
Qed.

(** Fresh allocation clears bytes to [pb_clean] and shadow slots to
    [taint_bot], preserving every admissible memory ceiling. *)
Lemma unpoison_admissible t_mem t_aux w pm paux base ext :
  pm_admissible t_mem t_aux w pm paux ->
  pm_admissible t_mem t_aux w (unpoison_range pm base ext) (unpoison_aux paux base ext).
Proof.
  intros [Hpm Hpaux]. split.
  - intros a. unfold unpoison_range.
    destruct ((base <=? a) && (a <? base + ext)).
    + split; [reflexivity | split; [apply taint_le_bot_l | intros _; reflexivity]].
    + exact (Hpm a).
  - intros a. unfold unpoison_aux.
    destruct ((base <=? a) && (a <? base + ext)); [apply taint_le_bot_l | apply Hpaux].
Qed.

(** ## Abstract taint transfer and verifier

    The functions [tlet], [tinst], and [tinsts] mirror [PoisonModel.tstep] on
    an abstract taint environment, using [ts_mem] and [ts_aux] to bound memory
    loads and checking every poison restriction statically. The verifier
    [taint_verify] checks a candidate block table in one linear pass over the
    function's blocks. *)

(** Abstract taint transfer for a single [Let] instruction. *)
Definition tlet (pol : poison_policy) (sp : tspec)
    (d : name) (k : class) (o : op) (args : list value) (te : tenv) : option tenv :=
  if is_zero_idiom o k args then Some (put d (WTInt taint_bot) te) else
  match o with
  | CheckLocal _ _ _ _ _ => Some (put d (WTPtr taint_bot taint_bot) te)
  | CheckFunction =>
      match args with
      | [v] =>
          match value_t te P v with
          | Some (WTPtr ta tc) =>
              if t_branch ta || t_branch tc then None
              else Some (put d (WTPtr ta tc) te)
          | _ => None
          end
      | _ => None
      end
  | Alloc _ =>
      match args with
      | [v] =>
          match value_t te L v with
          | Some (WTInt tsz) =>
              if t_branch tsz || t_index tsz then None
              else Some (put d (WTPtr taint_bot taint_bot) te)
          | _ => None
          end
      | _ => None
      end
  | Check _ _ _ _ =>
      match args with
      | [v] =>
          match value_t te P v with
          | Some (WTPtr ta tc) =>
              match check_ptr_bounds_taint pol ta tc with
              | Some _ => None
              | None => Some (put d (WTPtr ta tc) te)
              end
          | _ => None
          end
      | _ => None
      end
  | HalfCheck _ _ _ _ _ | Renew _ _ _ _ =>
      match args with
      | [q1; v] =>
          match value_t te A q1, value_t te P v with
          | Some (WTPtr qa qc), Some (WTPtr ta tc) =>
              match check_ptr_bounds_taint pol (taint_join qa ta) (taint_join qc tc) with
              | Some _ => None
              | None => Some (put d (WTPtr ta tc) te)
              end
          | _, _ => None
          end
      | _ => None
      end
  | RenewHull _ _ _ _ =>
      match args with
      | [ql; qh; v] =>
          match value_t te A ql, value_t te A qh, value_t te P v with
          | Some (WTPtr al cl), Some (WTPtr ah ch), Some (WTPtr ta tc) =>
              match check_ptr_bounds_taint pol
                      (taint_join al (taint_join ah ta))
                      (taint_join cl (taint_join ch tc)) with
              | Some _ => None
              | None => Some (put d (WTPtr ta tc) te)
              end
          | _, _, _ => None
          end
      | _ => None
      end
  | SpanTest _ _ =>
      match args with
      | [v] =>
          match value_t te P v with
          | Some (WTPtr ta tc) =>
              match check_ptr_bounds_taint pol ta tc with
              | Some _ => None
              | None => Some (put d (WTInt (taint_join ta tc)) te)
              end
          | _ => None
          end
      | _ => None
      end
  | RenewIf _ _ _ _ =>
      match args with
      | [v; gv] =>
          match value_t te P v, value_t te W gv with
          | Some (WTPtr ta tc), Some (WTInt tg) =>
              if pol_check_branches pol && t_branch tg then None
              else match check_ptr_bounds_taint pol ta tc with
                   | Some _ => None
                   | None => Some (put d (WTPtr ta tc) te)
                   end
          | _, _ => None
          end
      | _ => None
      end
  | Limit _ =>
      match args with
      | [v] =>
          match value_t te P v with
          | Some (WTPtr _ tc) =>
              if pol_check_branches pol && (t_branch tc || t_index tc) then None
              else Some (put d (WTLimit tc tc) te)
          | _ => None
          end
      | _ => None
      end
  | CheckLimit _ _ _ _ =>
      match args with
      | [v; uv] =>
          match value_t te P v, value_t te L uv with
          | Some (WTPtr ta tc), Some (WTLimit uc ul) =>
              let tc' := taint_join tc (taint_join uc ul) in
              match check_ptr_bounds_taint pol ta tc' with
              | Some _ => None
              | None => Some (put d (WTPtr ta tc) te)
              end
          | _, _ => None
          end
      | _ => None
      end
  | RawLoad _ _ =>
      match args with
      | [av] =>
          match value_t te A av with
          | Some (WTPtr ta tc) =>
              if t_index ta then None
              else if pol_check_branches pol && (t_branch ta || t_branch tc || t_index tc) then None
              else Some (put d (WTInt (ts_mem sp)) te)
          | _ => None
          end
      | _ => None
      end
  | RawLoadPointer _ _ =>
      match args with
      | [av] =>
          match value_t te A av with
          | Some (WTPtr ta tc) =>
              if t_index ta || t_index tc then None
              else if pol_check_branches pol && (t_branch ta || t_branch tc) then None
              else Some (put d (WTPtr (ts_mem sp) (ts_aux sp)) te)
          | _ => None
          end
      | _ => None
      end
  | Ptoi =>
      match args with
      | [v] =>
          match value_t te P v with
          | Some (WTPtr ta _) | Some (WTInt ta) => Some (put d (WTInt ta) te)
          | _ => None
          end
      | _ => None
      end
  | Itop =>
      match args with
      | [v] =>
          match value_t te L v with
          | Some (WTInt ta) => Some (put d (WTPtr ta taint_bot) te)
          | _ => None
          end
      | _ => None
      end
  | Copy =>
      match args with
      | [v] =>
          let* wt := value_t te k v in
          Some (put d wt te)
      | _ => None
      end
  | Add | Sub =>
      match k with
      | P =>
          match args with
          | [pv; ov] =>
              match value_t te P pv, value_t te L ov with
              | Some (WTPtr ta tc), Some (WTInt toff) => Some (put d (WTPtr (taint_join ta toff) tc) te)
              | _, _ => None
              end
          | _ => None
          end
      | A | F => None
      | _ =>
          let* cls := op_arg_classes o k in
          let* wts := map2_option (value_t te) cls args in
          let* ts := map_option scalar_wt wts in
          let tj := join_taints ts in
          if op_checks_vartime pol o k && t_vartime tj then None
          else Some (put d (WTInt tj) te)
      end
  | _ =>
      if pure_scalar_op o && negb (class_eqb k P || class_eqb k A || class_eqb k F) then
        let* cls := op_arg_classes o k in
        let* wts := map2_option (value_t te) cls args in
        let* ts := map_option scalar_wt wts in
        let tj := join_taints ts in
        if op_checks_vartime pol o k && t_vartime tj then None
        else Some (put d (WTInt tj) te)
      else None
  end.

(** Pairwise boolean [wt_le] check on two equal-length taint lists. *)
Fixpoint wts_le (xs ys : list word_taint) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => wt_le x y && wts_le xs' ys'
  | _, _ => false
  end.

Lemma wts_le_Forall2 xs ys :
  wts_le xs ys = true -> Forall2 (fun a b => wt_le a b = true) xs ys.
Proof.
  revert ys. induction xs as [|x xs IH]; intros [|y ys] H; cbn in H; try discriminate.
  - constructor.
  - apply andb_prop in H; destruct H as [Hxy Hrest]. constructor; [exact Hxy | exact (IH ys Hrest)].
Qed.

(** Abstract taint transfer for one instruction [i]. Direct calls consult
    [tspecs] and verify both argument taints and memory-ceiling compatibility. *)
Definition tinst (pol : poison_policy) (md : module) (tspecs : list (name * tspec))
    (sp : tspec) (i : inst) (te : tenv) : option tenv :=
  match i with
  | Loc _ _ | Touch _ | LocalAlloc _ _ => Some te
  | Flight d o args lw =>
      let* ts := map_option (flight_arg_t te) args in
      let* tc := flight_cap_t te lw in
      let ta := join_taints ts in
      if op_checks_vartime pol o L && t_vartime ta then None
      else Some (put d (WTPtr ta tc) te)
  | Let d k o args => tlet pol sp d k o args te
  | RawStore w _ v av =>
      if negb (ts_writes sp) then None else
      let* vk := width_value_class w in
      match value_t te A av with
      | Some (WTPtr ta tc) =>
          if t_index ta then None
          else if pol_check_branches pol && (t_branch ta || t_branch tc || t_index tc) then None
          else match w, value_t te vk v with
               | Wp, Some (WTPtr tva tvc) =>
                   if taint_le tva (ts_mem sp) && taint_le tvc (ts_aux sp) then Some te else None
               | (Wb | Wh | Ww | Wl | Ws | Wd | Wx), Some (WTInt tv) =>
                   if taint_le tv (ts_mem sp) then Some te else None
               | _, _ => None
               end
      | _ => None
      end
  | RawStorePointer _ v av es =>
      if negb (ts_writes sp) then None else
      if effects_eqb es [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]
         || effects_eqb es [LowerWrite; AddressWrite]
         || effects_eqb es [AtomicWrite] then
        match value_t te A av, value_t te P v with
        | Some (WTPtr ta tca), Some (WTPtr tva tvc) =>
            if t_index ta || t_index tca then None
            else if pol_check_branches pol && (t_branch ta || t_branch tca) then None
            else if taint_le tva (ts_mem sp) && taint_le tvc (ts_aux sp) then Some te else None
        | _, _ => None
        end
      else None
  | Call r (Global g) args =>
      let* wts := map_option (arg_t te) args in
      match lookup g tspecs with
      | Some sp_g =>
          if taint_eqb (ts_mem sp_g) (ts_mem sp)
             && taint_eqb (ts_aux sp_g) (ts_aux sp)
             && implb (ts_writes sp_g) (ts_writes sp)
             && wts_le wts (ts_args sp_g) then
            let ots := match ts_ret sp_g with Some wt => [wt] | None => [] end in
            returned_tenv r ots te
          else None
      | None =>
          match find_fn (mkGenv md [] free_res) g with
          | None =>
              if is_free_name g then
                match r, args, wts with
                | CVoid, [Arg P _], [WTPtr ta tc] =>
                    if t_branch ta || t_branch tc || t_index tc then None else Some te
                | CVoid, [Arg P _], [WTInt ta] =>
                    if t_branch ta then None else Some te
                | _, _, _ => None
                end
              else None
          | Some _ => None
          end
      end
  | Call _ _ _ | RawCall _ _ _ => None
  end.

(** Run [tinst] sequentially across a list of instructions. *)
Fixpoint tinsts (pol : poison_policy) (md : module) (tspecs : list (name * tspec))
    (sp : tspec) (ins : list inst) (te : tenv) : option tenv :=
  match ins with
  | [] => Some te
  | i :: rest =>
      let* te' := tinst pol md tspecs sp i te in
      tinsts pol md tspecs sp rest te'
  end.

(** Check that an outgoing edge from block [from] to block [target] resolves
    every [[phi]] node into an environment bounded by [tbl]'s entry for
    [target]. *)
Definition tedge_ok (f : func) (tbl : list (name * tenv))
    (from target : name) (te : tenv) : bool :=
  match find_block target (fn_blocks f), lookup target tbl with
  | Some b, Some te_t =>
      match phis_tenv (b_phis b) (Some from) te with
      | Some te' => tenv_le te' te_t
      | None => false
      end
  | _, _ => false
  end.

(** Check a block terminator [j] at label [l] in abstract taint environment [te]. *)
Definition tjump_ok (f : func) (sp : tspec) (tbl : list (name * tenv))
    (l : name) (j : jump) (te : tenv) : bool :=
  match j with
  | JGoto t => tedge_ok f tbl l (edge_label t) te
  | JBranch v t1 t2 =>
      match value_t te W v with
      | Some (WTInt tv) =>
          negb (t_branch tv)
          && tedge_ok f tbl l (edge_label t1) te
          && tedge_ok f tbl l (edge_label t2) te
      | _ => false
      end
  | JRet v =>
      match fn_ret f, ts_ret sp with
      | RClass k, Some wt_out =>
          match value_t te k v with
          | Some wt => wt_le wt wt_out
          | None => false
          end
      | _, _ => false
      end
  | JRetVoid =>
      match fn_ret f, ts_ret sp with
      | RVoid, None => true
      | _, _ => false
      end
  | JUnreachable => true
  | JRets _ => false
  end.

(** Check one remaining block tail (`rest` followed by `j`) from [te]. *)
Definition ttail_ok (pol : poison_policy) (md : module) (tspecs : list (name * tspec))
    (f : func) (sp : tspec) (tbl : list (name * tenv))
    (l : name) (rest : list inst) (j : jump) (te : tenv) : bool :=
  match tinsts pol md tspecs sp rest te with
  | Some te1 => tjump_ok f sp tbl l j te1
  | None => false
  end.

(** Check one block entry `(l, te0)` in [tbl]. *)
Definition tblock_ok (pol : poison_policy) (md : module) (tspecs : list (name * tspec))
    (f : func) (sp : tspec) (tbl : list (name * tenv))
    (l : name) (te0 : tenv) : bool :=
  match find_block l (fn_blocks f) with
  | Some b => ttail_ok pol md tspecs f sp tbl l (b_insts b) (b_jump b) te0
  | None => false
  end.

(** The entry label of a function is the label of its first basic block. *)
Definition fn_entry (f : func) : option name :=
  match fn_blocks f with
  | b :: _ => Some (b_label b)
  | [] => None
  end.

(** Verify that [tbl] is a sound inductive taint invariant for function [f]
    under policy [pol], module [md], callee specs [tspecs], and specification
    [sp]. *)
Definition taint_verify (pol : poison_policy) (md : module) (tspecs : list (name * tspec))
    (f : func) (sp : tspec) (tbl : list (name * tenv)) : bool :=
  negb (variadic_func f) &&
  match fn_entry f with
  | Some entry =>
      match find_block entry (fn_blocks f), call_tenv f (ts_args sp), lookup entry tbl with
      | Some b_entry, Some te_init, Some te_entry =>
          match b_phis b_entry with
          | [] => tenv_le te_init te_entry
                  && forallb (fun '(l, te0) => tblock_ok pol md tspecs f sp tbl l te0) tbl
          | _ => false
          end
      | _, _, _ => false
      end
  | None => false
  end.

(** ## Untrusted fixed-point inference

    Because [word_taint] has finite height (at most six boolean dimensions for
    a pointer), fixed-point propagation over the control-flow graph terminates
    in a handful of passes. No soundness theorem trusts [taint_infer]:
    [taint_check_fn] always hands the inferred table to [taint_verify]. *)

(** Two word taints have the same shape when both are integers, pointers, or
    limit snapshots. *)
Definition wt_same_shape (a b : word_taint) : bool :=
  match a, b with
  | WTInt _, WTInt _ | WTPtr _ _, WTPtr _ _ | WTLimit _ _, WTLimit _ _ => true
  | _, _ => false
  end.

(** Join two taint environments on the intersection of their domains,
    combining matching-shape bindings with [wt_join]. *)
Definition tenv_join (te1 te2 : tenv) : tenv :=
  flat_map (fun '(x, w1) =>
    match lookup x te2 with
    | Some w2 => if wt_same_shape w1 w2 then [(x, wt_join w1 w2)] else []
    | None => []
    end) te1.

(** Merge a newly reached environment [te] into block [l]'s entry in [tbl],
    reporting whether [tbl] changed. *)
Definition tmerge_block (tbl : list (name * tenv)) (l : name) (te : tenv)
    : list (name * tenv) * bool :=
  match lookup l tbl with
  | None => (put l te tbl, true)
  | Some old =>
      if tenv_le te old then (tbl, false)
      else (put l (tenv_join old te) tbl, true)
  end.

(** Propagate an outgoing edge from block [from] to [target]. *)
Definition tprop_edge (f : func) (from target : name) (te : tenv)
    (acc : option (list (name * tenv) * bool))
    : option (list (name * tenv) * bool) :=
  let* st := acc in
  let '(tbl, ch) := st in
  let* b := find_block target (fn_blocks f) in
  let* te' := phis_tenv (b_phis b) (Some from) te in
  let '(tbl', ch') := tmerge_block tbl target te' in
  Some (tbl', ch || ch').

(** Run one propagation pass across every block currently in [tbl]. *)
Definition tinfer_round (pol : poison_policy) (md : module) (tspecs : list (name * tspec))
    (f : func) (sp : tspec) (tbl : list (name * tenv))
    : option (list (name * tenv) * bool) :=
  fold_left (fun acc '(l, te0) =>
    let* st := acc in
    let '(tbl', ch) := st in
    let* b := find_block l (fn_blocks f) in
    let* te1 := tinsts pol md tspecs sp (b_insts b) te0 in
    match b_jump b with
    | JGoto t => tprop_edge f l (edge_label t) te1 (Some (tbl', ch))
    | JBranch _ t1 t2 =>
        let r1 := tprop_edge f l (edge_label t1) te1 (Some (tbl', ch)) in
        tprop_edge f l (edge_label t2) te1 r1
    | JRet _ | JRetVoid | JUnreachable => Some (tbl', ch)
    | JRets _ => None
    end) tbl (Some (tbl, false)).

Fixpoint tinfer_loop (fuel : nat) (pol : poison_policy) (md : module)
    (tspecs : list (name * tspec)) (f : func) (sp : tspec)
    (tbl : list (name * tenv)) : option (list (name * tenv)) :=
  match fuel with
  | O => Some tbl
  | S fuel' =>
      let* st := tinfer_round pol md tspecs f sp tbl in
      let '(tbl', ch) := st in
      if ch then tinfer_loop fuel' pol md tspecs f sp tbl' else Some tbl'
  end.

(** Infer a block table for [f] starting from [call_tenv f (ts_args sp)]. *)
Definition taint_infer (pol : poison_policy) (md : module) (tspecs : list (name * tspec))
    (f : func) (sp : tspec) : option (list (name * tenv)) :=
  let* entry := fn_entry f in
  let* te0 := call_tenv f (ts_args sp) in
  tinfer_loop (8 * (length (fn_blocks f) + 1))%nat pol md tspecs f sp [(entry, te0)].

(** Infer and immediately verify a single function against [sp]. *)
Definition taint_check_fn (pol : poison_policy) (md : module) (tspecs : list (name * tspec))
    (f : func) (sp : tspec) : bool :=
  match taint_infer pol md tspecs f sp with
  | Some tbl => taint_verify pol md tspecs f sp tbl
  | None => false
  end.

(** Check every function in a call-graph specification table [entries] against
    module [md]. *)
Definition taint_check_program (pol : poison_policy) (md : module)
    (entries : list (name * tspec)) : bool :=
  forallb (fun '(g, sp) =>
    match find_fn (mkGenv md [] free_res) g with
    | Some (Defined f) => taint_check_fn pol md entries f sp
    | _ => false
    end) entries.

(** ## Step-level soundness of abstract taint transfer

    The lemmas in this section prove that whenever [tlet], [tinst], or
    [tjump_ok] accepts a concrete configuration that does not fail under plain
    [Semantics.step], the lockstep poisoned step [pstep] avoids [PTrap] and
    [PStuck] and preserves the abstract taint bound. *)

(** Helper handling the uniform scalar-op branch of [tlet] and [let_tstep]. *)
Lemma tlet_scalar_branch_sound pol d k o args te te_abs te_abs' cs pm paux :
  tenv_le_prop te te_abs ->
  (let* cls := op_arg_classes o k in
   let* wts := map2_option (value_t te_abs) cls args in
   let* ts := map_option scalar_wt wts in
   if op_checks_vartime pol o k && t_vartime (join_taints ts) then None
   else Some (put d (WTInt (join_taints ts)) te_abs)) = Some te_abs' ->
  exists te',
    (match op_arg_classes o k with
     | Some cls =>
         match map2_option (value_t te) cls args with
         | Some wts =>
             match map_option scalar_wt wts with
             | Some ts =>
                 if op_checks_vartime pol o k && t_vartime (join_taints ts) then TFault CannotVarTimeOp
                 else TNext (mkPState (put d (WTInt (join_taints ts)) te) cs pm paux)
             | None => TStuck "op_scalar"
             end
         | None => TStuck "op_args"
         end
     | None => TStuck "op_cls"
     end) = TNext (mkPState te' cs pm paux) /\
    tenv_le_prop te' te_abs'.
Proof.
  intros Hte Ht.
  destruct (op_arg_classes o k) as [cls|] eqn:Ecls; [|discriminate Ht].
  destruct (map2_option (value_t te_abs) cls args) as [wts2|] eqn:Ew2; [|discriminate Ht].
  destruct (map_option scalar_wt wts2) as [ts2|] eqn:Es2; [|discriminate Ht].
  destruct (op_checks_vartime pol o k && t_vartime (join_taints ts2)) eqn:Evt; [discriminate Ht|].
  injection Ht as <-.
  destruct (map2_value_t_mono te te_abs cls args wts2 Hte Ew2) as (wts1 & Ew1 & Hwle).
  destruct (map_scalar_wt_mono wts1 wts2 ts2 Hwle Es2) as (ts1 & Es1 & Htle).
  rewrite Ew1, Es1.
  pose proof (join_taints_mono ts1 ts2 Htle) as Hjle.
  assert (Evt1 : op_checks_vartime pol o k && t_vartime (join_taints ts1) = false).
  { destruct (op_checks_vartime pol o k); cbn in Evt |- *; [eapply taint_le_vartime; eassumption | reflexivity]. }
  rewrite Evt1. eexists. split; [reflexivity|].
  apply tenv_le_prop_put; [exact Hjle | exact Hte].
Qed.

Lemma tlet_sound pol ge e d k o args te te_abs te_abs' cs pm paux sp wr :
  tenv_le_prop te te_abs ->
  pm_admissible (ts_mem sp) (ts_aux sp) wr pm paux ->
  tlet pol sp d k o args te_abs = Some te_abs' ->
  (match o, args with
   | Alloc _, [v] => exists sz, value_x ge e L v = Some (WInt sz)
   | RawLoad _ _, [av] | RawLoadPointer _ _, [av] => exists p, value_x ge e A av = Some (WPtr p)
   | _, _ => True
   end) ->
  match let_tstep pol ge e (mkPState te cs pm paux) d k o args with
  | TNext (mkPState te' cs' pm' paux') =>
      cs' = cs /\ pm' = pm /\ paux' = paux /\ tenv_le_prop te' te_abs'
  | TDone ots =>
      ots = [] /\ match o with Alloc _ => True | _ => False end
  | TFresh tps =>
      match o with
      | Alloc al =>
          forall base,
            let ps' := tps base in
            ps_callers ps' = cs /\
            tenv_le_prop (ps_tenv ps') te_abs' /\
            pm_admissible (ts_mem sp) (ts_aux sp) wr (ps_mem ps') (ps_aux ps')
      | _ => False
      end
  | TFault _ | TStuck _ => False
  end.
Proof.
  intros Hte Hpm Htlet Hx.
  unfold tlet in Htlet. unfold let_tstep. cbv zeta beta in Htlet |- *.
  cbn [ps_tenv ps_callers ps_mem ps_aux].
  destruct (is_zero_idiom o k args) eqn:Ezero.
  { injection Htlet as <-. repeat split; try reflexivity.
    apply tenv_le_prop_put; [apply wt_le_refl | exact Hte]. }
  destruct o; try (
    (* Fallback pure_scalar_op branch *)
    cbn [pure_scalar_op] in Htlet |- *;
    destruct (negb (class_eqb k P || class_eqb k A || class_eqb k F)) eqn:Ek;
      try discriminate Htlet;
    match goal with
    | |- context [op_arg_classes ?o0 ?k0] =>
        destruct (tlet_scalar_branch_sound pol d k0 o0 args te te_abs te_abs' cs pm paux Hte Htlet) as (te' & -> & Hle');
        repeat split; auto
    end).
  - (* Add *)
    destruct k; try (
      match goal with
      | |- context [op_arg_classes ?o0 ?k0] =>
          destruct (tlet_scalar_branch_sound pol d k0 o0 args te te_abs te_abs' cs pm paux Hte Htlet) as (te' & -> & Hle');
          repeat split; auto
      end).
    + (* Add P *)
      destruct args as [|pv [|ov [|]]]; try discriminate Htlet.
      destruct (value_t te_abs P pv) as [wp2|] eqn:Ep2; try discriminate Htlet.
      destruct wp2 as [|ta2 tc2|]; try discriminate Htlet.
      destruct (value_t te_abs L ov) as [wo2|] eqn:Eo2; try discriminate Htlet.
      destruct wo2 as [toff2| |]; try discriminate Htlet.
      injection Htlet as <-.
      destruct (value_t_mono te te_abs P pv (WTPtr ta2 tc2) Hte Ep2) as (wp1 & Ep1 & Hple).
      destruct (value_t_mono te te_abs L ov (WTInt toff2) Hte Eo2) as (wo1 & Eo1 & Hole).
      destruct wp1 as [|ta1 tc1|]; cbn [wt_le] in Hple; try discriminate.
      destruct wo1 as [toff1| |]; cbn [wt_le] in Hole; try discriminate.
      apply andb_prop in Hple; destruct Hple as [Hla Hlc].
      rewrite Ep1, Eo1. repeat split; try reflexivity.
      apply tenv_le_prop_put; [cbn [wt_le]; rewrite (taint_le_join_mono _ _ _ _ Hla Hole), Hlc; reflexivity | exact Hte].
    + discriminate Htlet.
    + discriminate Htlet.
  - (* Sub *)
    destruct k; try (
      match goal with
      | |- context [op_arg_classes ?o0 ?k0] =>
          destruct (tlet_scalar_branch_sound pol d k0 o0 args te te_abs te_abs' cs pm paux Hte Htlet) as (te' & -> & Hle');
          repeat split; auto
      end).
    + (* Sub P *)
      destruct args as [|pv [|ov [|]]]; try discriminate Htlet.
      destruct (value_t te_abs P pv) as [wp2|] eqn:Ep2; try discriminate Htlet.
      destruct wp2 as [|ta2 tc2|]; try discriminate Htlet.
      destruct (value_t te_abs L ov) as [wo2|] eqn:Eo2; try discriminate Htlet.
      destruct wo2 as [toff2| |]; try discriminate Htlet.
      injection Htlet as <-.
      destruct (value_t_mono te te_abs P pv (WTPtr ta2 tc2) Hte Ep2) as (wp1 & Ep1 & Hple).
      destruct (value_t_mono te te_abs L ov (WTInt toff2) Hte Eo2) as (wo1 & Eo1 & Hole).
      destruct wp1 as [|ta1 tc1|]; cbn [wt_le] in Hple; try discriminate.
      destruct wo1 as [toff1| |]; cbn [wt_le] in Hole; try discriminate.
      apply andb_prop in Hple; destruct Hple as [Hla Hlc].
      rewrite Ep1, Eo1. repeat split; try reflexivity.
      apply tenv_le_prop_put; [cbn [wt_le]; rewrite (taint_le_join_mono _ _ _ _ Hla Hole), Hlc; reflexivity | exact Hte].
    + discriminate Htlet.
    + discriminate Htlet.
  - (* Copy *)
    destruct args as [|v []]; try discriminate Htlet.
    destruct (value_t te_abs k v) as [w2|] eqn:Ev2; try discriminate Htlet.
    injection Htlet as <-.
    destruct (value_t_mono te te_abs k v w2 Hte Ev2) as (w1 & Ev1 & Hle).
    rewrite Ev1. repeat split; try reflexivity.
    apply tenv_le_prop_put; assumption.
  - (* Ptoi *)
    destruct args as [|v []]; try discriminate Htlet.
    destruct (value_t te_abs P v) as [w2|] eqn:Ev2; try discriminate Htlet.
    destruct (value_t_mono te te_abs P v w2 Hte Ev2) as (w1 & Ev1 & Hle).
    rewrite Ev1.
    destruct w2 as [ta2|ta2 tc2|]; try discriminate Htlet; injection Htlet as <-;
      destruct w1 as [ta1|ta1 tc1|]; cbn [wt_le] in Hle; try discriminate.
    + repeat split; try reflexivity. apply tenv_le_prop_put; [exact Hle | exact Hte].
    + apply andb_prop in Hle; destruct Hle as [Hla _].
      repeat split; try reflexivity. apply tenv_le_prop_put; [exact Hla | exact Hte].
  - (* Itop *)
    destruct args as [|v []]; try discriminate Htlet.
    destruct (value_t te_abs L v) as [w2|] eqn:Ev2; try discriminate Htlet.
    destruct w2 as [ta2| |]; try discriminate Htlet; injection Htlet as <-.
    destruct (value_t_mono te te_abs L v (WTInt ta2) Hte Ev2) as (w1 & Ev1 & Hle).
    destruct w1 as [ta1| |]; cbn [wt_le] in Hle; try discriminate.
    rewrite Ev1. repeat split; try reflexivity.
    apply tenv_le_prop_put; [cbn [wt_le]; rewrite Hle, taint_le_refl; reflexivity | exact Hte].
  - (* Alloc *)
    destruct args as [|v []]; try discriminate Htlet.
    destruct (value_t te_abs L v) as [w2|] eqn:Ev2; try discriminate Htlet.
    destruct w2 as [tsz2| |]; try discriminate Htlet.
    destruct (t_branch tsz2 || t_index tsz2) eqn:Eb2; try discriminate Htlet.
    injection Htlet as <-.
    apply orb_false_iff in Eb2; destruct Eb2 as [Hb2 Hi2].
    destruct (value_t_mono te te_abs L v (WTInt tsz2) Hte Ev2) as (w1 & Ev1 & Hle).
    destruct w1 as [tsz1| |]; cbn [wt_le] in Hle; try discriminate.
    destruct Hx as [sz Hsz]. rewrite Hsz, Ev1.
    rewrite (taint_le_branch _ _ Hle Hb2), (taint_le_index _ _ Hle Hi2).
    destruct (max_allocation_size <? sz); [split; auto|].
    intros base. cbn [ps_tenv ps_callers ps_mem ps_aux].
    split; [reflexivity | split].
    + apply tenv_le_prop_put; [apply wt_le_refl | exact Hte].
    + apply unpoison_admissible; exact Hpm.
  - (* Check *)
    destruct args as [|v []]; try discriminate Htlet.
    destruct (value_t te_abs P v) as [w2|] eqn:Ev2; try discriminate Htlet.
    destruct w2 as [|ta2 tc2|]; try discriminate Htlet.
    destruct (check_ptr_bounds_taint pol ta2 tc2) eqn:Echk2; try discriminate Htlet.
    injection Htlet as <-.
    destruct (value_t_mono te te_abs P v (WTPtr ta2 tc2) Hte Ev2) as (w1 & Ev1 & Hle).
    destruct w1 as [|ta1 tc1|]; cbn [wt_le] in Hle; try discriminate.
    apply andb_prop in Hle; destruct Hle as [Hla Hlc].
    rewrite Ev1, (check_ptr_bounds_taint_mono pol ta1 ta2 tc1 tc2 Hla Hlc Echk2).
    repeat split; try reflexivity.
    apply tenv_le_prop_put; [cbn [wt_le]; rewrite Hla, Hlc; reflexivity | exact Hte].
  - (* Renew *)
    destruct args as [|q1 [|v []]]; try discriminate Htlet.
    destruct (value_t te_abs A q1) as [wq2|] eqn:Eq2; try discriminate Htlet.
    destruct wq2 as [|qa2 qc2|]; try discriminate Htlet.
    destruct (value_t te_abs P v) as [wv2|] eqn:Ev2; try discriminate Htlet.
    destruct wv2 as [|ta2 tc2|]; try discriminate Htlet.
    destruct (check_ptr_bounds_taint pol (taint_join qa2 ta2) (taint_join qc2 tc2)) eqn:Echk2; try discriminate Htlet.
    injection Htlet as <-.
    destruct (value_t_mono te te_abs A q1 _ Hte Eq2) as (wq1 & Eq1 & Hqle).
    destruct (value_t_mono te te_abs P v _ Hte Ev2) as (wv1 & Ev1 & Hvle).
    destruct wq1 as [|qa1 qc1|]; cbn [wt_le] in Hqle; try discriminate.
    destruct wv1 as [|ta1 tc1|]; cbn [wt_le] in Hvle; try discriminate.
    apply andb_prop in Hqle; destruct Hqle as [Hqa Hqc]; apply andb_prop in Hvle; destruct Hvle as [Hta Htc].
    rewrite Eq1, Ev1.
    rewrite (check_ptr_bounds_taint_mono pol _ _ _ _
              (taint_le_join_mono _ _ _ _ Hqa Hta) (taint_le_join_mono _ _ _ _ Hqc Htc) Echk2).
    repeat split; try reflexivity.
    apply tenv_le_prop_put; [cbn [wt_le]; rewrite Hta, Htc; reflexivity | exact Hte].
  - (* RenewHull *)
    destruct args as [|ql [|qh [|v []]]]; try discriminate Htlet.
    destruct (value_t te_abs A ql) as [wl2|] eqn:El2; try discriminate Htlet.
    destruct wl2 as [|al2 cl2|]; try discriminate Htlet.
    destruct (value_t te_abs A qh) as [wh2|] eqn:Eh2; try discriminate Htlet.
    destruct wh2 as [|ah2 ch2|]; try discriminate Htlet.
    destruct (value_t te_abs P v) as [wv2|] eqn:Ev2; try discriminate Htlet.
    destruct wv2 as [|ta2 tc2|]; try discriminate Htlet.
    destruct (check_ptr_bounds_taint pol (taint_join al2 (taint_join ah2 ta2)) (taint_join cl2 (taint_join ch2 tc2))) eqn:Echk2; try discriminate Htlet.
    injection Htlet as <-.
    destruct (value_t_mono te te_abs A ql _ Hte El2) as (wl1 & El1 & Hlle).
    destruct (value_t_mono te te_abs A qh _ Hte Eh2) as (wh1 & Eh1 & Hhle).
    destruct (value_t_mono te te_abs P v _ Hte Ev2) as (wv1 & Ev1 & Hvle).
    destruct wl1 as [|al1 cl1|]; cbn [wt_le] in Hlle; try discriminate.
    destruct wh1 as [|ah1 ch1|]; cbn [wt_le] in Hhle; try discriminate.
    destruct wv1 as [|ta1 tc1|]; cbn [wt_le] in Hvle; try discriminate.
    apply andb_prop in Hlle; destruct Hlle as [Hal Hcl]; apply andb_prop in Hhle; destruct Hhle as [Hah Hch]; apply andb_prop in Hvle; destruct Hvle as [Hta Htc].
    rewrite El1, Eh1, Ev1.
    rewrite (check_ptr_bounds_taint_mono pol _ _ _ _
              (taint_le_join_mono _ _ _ _ Hal (taint_le_join_mono _ _ _ _ Hah Hta))
              (taint_le_join_mono _ _ _ _ Hcl (taint_le_join_mono _ _ _ _ Hch Htc)) Echk2).
    repeat split; try reflexivity.
    apply tenv_le_prop_put; [cbn [wt_le]; rewrite Hta, Htc; reflexivity | exact Hte].
  - (* HalfCheck *)
    destruct args as [|q1 [|v []]]; try discriminate Htlet.
    destruct (value_t te_abs A q1) as [wq2|] eqn:Eq2; try discriminate Htlet.
    destruct wq2 as [|qa2 qc2|]; try discriminate Htlet.
    destruct (value_t te_abs P v) as [wv2|] eqn:Ev2; try discriminate Htlet.
    destruct wv2 as [|ta2 tc2|]; try discriminate Htlet.
    destruct (check_ptr_bounds_taint pol (taint_join qa2 ta2) (taint_join qc2 tc2)) eqn:Echk2; try discriminate Htlet.
    injection Htlet as <-.
    destruct (value_t_mono te te_abs A q1 _ Hte Eq2) as (wq1 & Eq1 & Hqle).
    destruct (value_t_mono te te_abs P v _ Hte Ev2) as (wv1 & Ev1 & Hvle).
    destruct wq1 as [|qa1 qc1|]; cbn [wt_le] in Hqle; try discriminate.
    destruct wv1 as [|ta1 tc1|]; cbn [wt_le] in Hvle; try discriminate.
    apply andb_prop in Hqle; destruct Hqle as [Hqa Hqc]; apply andb_prop in Hvle; destruct Hvle as [Hta Htc].
    rewrite Eq1, Ev1.
    rewrite (check_ptr_bounds_taint_mono pol _ _ _ _
              (taint_le_join_mono _ _ _ _ Hqa Hta) (taint_le_join_mono _ _ _ _ Hqc Htc) Echk2).
    repeat split; try reflexivity.
    apply tenv_le_prop_put; [cbn [wt_le]; rewrite Hta, Htc; reflexivity | exact Hte].
  - (* SpanTest *)
    destruct args as [|v []]; try discriminate Htlet.
    destruct (value_t te_abs P v) as [wv2|] eqn:Ev2; try discriminate Htlet.
    destruct wv2 as [|ta2 tc2|]; try discriminate Htlet.
    destruct (check_ptr_bounds_taint pol ta2 tc2) eqn:Echk2; try discriminate Htlet.
    injection Htlet as <-.
    destruct (value_t_mono te te_abs P v _ Hte Ev2) as (wv1 & Ev1 & Hvle).
    destruct wv1 as [|ta1 tc1|]; cbn [wt_le] in Hvle; try discriminate.
    apply andb_prop in Hvle; destruct Hvle as [Hta Htc].
    rewrite Ev1, (check_ptr_bounds_taint_mono pol ta1 ta2 tc1 tc2 Hta Htc Echk2).
    repeat split; try reflexivity.
    apply tenv_le_prop_put; [apply taint_le_join_mono; assumption | exact Hte].
  - (* RenewIf *)
    destruct args as [|v [|gv []]]; try discriminate Htlet.
    destruct (value_t te_abs P v) as [wv2|] eqn:Ev2; try discriminate Htlet.
    destruct wv2 as [|ta2 tc2|]; try discriminate Htlet.
    destruct (value_t te_abs W gv) as [wg2|] eqn:Eg2; try discriminate Htlet.
    destruct wg2 as [tg2| |]; try discriminate Htlet.
    destruct (pol_check_branches pol && t_branch tg2) eqn:Ebg2; try discriminate Htlet.
    destruct (check_ptr_bounds_taint pol ta2 tc2) eqn:Echk2; try discriminate Htlet.
    injection Htlet as <-.
    destruct (value_t_mono te te_abs P v _ Hte Ev2) as (wv1 & Ev1 & Hvle).
    destruct (value_t_mono te te_abs W gv _ Hte Eg2) as (wg1 & Eg1 & Hgle).
    destruct wv1 as [|ta1 tc1|]; cbn [wt_le] in Hvle; try discriminate.
    destruct wg1 as [tg1| |]; cbn [wt_le] in Hgle; try discriminate.
    apply andb_prop in Hvle; destruct Hvle as [Hta Htc].
    rewrite Ev1, Eg1.
    assert (Ebg1 : pol_check_branches pol && t_branch tg1 = false)
      by (destruct (pol_check_branches pol); cbn in Ebg2 |- *; [eapply taint_le_branch; eassumption | reflexivity]).
    rewrite Ebg1, (check_ptr_bounds_taint_mono pol ta1 ta2 tc1 tc2 Hta Htc Echk2).
    repeat split; try reflexivity.
    apply tenv_le_prop_put; [cbn [wt_le]; rewrite Hta, Htc; reflexivity | exact Hte].
  - (* Limit *)
    destruct args as [|v []]; try discriminate Htlet.
    destruct (value_t te_abs P v) as [wv2|] eqn:Ev2; try discriminate Htlet.
    destruct wv2 as [|ta2 tc2|]; try discriminate Htlet.
    destruct (pol_check_branches pol && (t_branch tc2 || t_index tc2)) eqn:E2; try discriminate Htlet.
    injection Htlet as <-.
    destruct (value_t_mono te te_abs P v _ Hte Ev2) as (wv1 & Ev1 & Hvle).
    destruct wv1 as [|ta1 tc1|]; cbn [wt_le] in Hvle; try discriminate.
    apply andb_prop in Hvle; destruct Hvle as [_ Htc].
    rewrite Ev1.
    destruct (pol_check_branches pol) eqn:Epol; cbn in E2 |- *.
    + apply orb_false_iff in E2; destruct E2 as [Hb2 Hi2].
      rewrite (taint_le_branch _ _ Htc Hb2), (taint_le_index _ _ Htc Hi2).
      repeat split; try reflexivity.
      apply tenv_le_prop_put; [cbn [wt_le]; rewrite Htc; reflexivity | exact Hte].
    + repeat split; try reflexivity.
      apply tenv_le_prop_put; [cbn [wt_le]; rewrite Htc; reflexivity | exact Hte].
  - (* CheckLimit *)
    destruct args as [|v [|uv []]]; try discriminate Htlet.
    destruct (value_t te_abs P v) as [wv2|] eqn:Ev2; try discriminate Htlet.
    destruct wv2 as [|ta2 tc2|]; try discriminate Htlet.
    destruct (value_t te_abs L uv) as [wu2|] eqn:Eu2; try discriminate Htlet.
    destruct wu2 as [| |uc2 ul2]; try discriminate Htlet.
    destruct (check_ptr_bounds_taint pol ta2 (taint_join tc2 (taint_join uc2 ul2))) eqn:Echk2; try discriminate Htlet.
    injection Htlet as <-.
    destruct (value_t_mono te te_abs P v _ Hte Ev2) as (wv1 & Ev1 & Hvle).
    destruct (value_t_mono te te_abs L uv _ Hte Eu2) as (wu1 & Eu1 & Hule).
    destruct wv1 as [|ta1 tc1|]; cbn [wt_le] in Hvle; try discriminate.
    destruct wu1 as [| |uc1 ul1]; cbn [wt_le] in Hule; try discriminate.
    apply andb_prop in Hvle; destruct Hvle as [Hta Htc]; apply andb_prop in Hule; destruct Hule as [Huc Hul].
    rewrite Ev1, Eu1.
    rewrite (check_ptr_bounds_taint_mono pol ta1 ta2 _ _ Hta
              (taint_le_join_mono _ _ _ _ Htc (taint_le_join_mono _ _ _ _ Huc Hul)) Echk2).
    repeat split; try reflexivity.
    apply tenv_le_prop_put; [cbn [wt_le]; rewrite Hta, Htc; reflexivity | exact Hte].
  - (* CheckLocal *)
    injection Htlet as <-. repeat split; try reflexivity.
    apply tenv_le_prop_put; [apply wt_le_refl | exact Hte].
  - (* CheckFunction *)
    destruct args as [|v []]; try discriminate Htlet.
    destruct (value_t te_abs P v) as [wv2|] eqn:Ev2; try discriminate Htlet.
    destruct wv2 as [|ta2 tc2|]; try discriminate Htlet.
    destruct (t_branch ta2 || t_branch tc2) eqn:Eb2; try discriminate Htlet.
    injection Htlet as <-.
    apply orb_false_iff in Eb2; destruct Eb2 as [Eba2 Ebc2].
    destruct (value_t_mono te te_abs P v _ Hte Ev2) as (wv1 & Ev1 & Hvle).
    destruct wv1 as [|ta1 tc1|]; cbn [wt_le] in Hvle; try discriminate.
    apply andb_prop in Hvle; destruct Hvle as [Hta Htc].
    rewrite Ev1, (taint_le_branch _ _ Hta Eba2), (taint_le_branch _ _ Htc Ebc2).
    repeat split; try reflexivity.
    apply tenv_le_prop_put; [cbn [wt_le]; rewrite Hta, Htc; reflexivity | exact Hte].
  - (* RawLoad *)
    destruct args as [|av []]; try discriminate Htlet.
    destruct (value_t te_abs A av) as [wv2|] eqn:Ev2; try discriminate Htlet.
    destruct wv2 as [|ta2 tc2|]; try discriminate Htlet.
    destruct (t_index ta2) eqn:Ei2; try discriminate Htlet.
    destruct (pol_check_branches pol && (t_branch ta2 || t_branch tc2 || t_index tc2)) eqn:Eb2; try discriminate Htlet.
    injection Htlet as <-.
    destruct (value_t_mono te te_abs A av _ Hte Ev2) as (wv1 & Ev1 & Hvle).
    destruct wv1 as [|ta1 tc1|]; cbn [wt_le] in Hvle; try discriminate.
    apply andb_prop in Hvle; destruct Hvle as [Hta Htc].
    destruct Hx as [p Hp]. rewrite Hp, Ev1.
    rewrite (taint_le_index _ _ Hta Ei2).
    assert (Eb1 : pol_check_branches pol && (t_branch ta1 || t_branch tc1 || t_index tc1) = false).
    { destruct (pol_check_branches pol); cbn in Eb2 |- *; [|reflexivity].
      apply orb_false_iff in Eb2; destruct Eb2 as [Eb2' Eic2]; apply orb_false_iff in Eb2'; destruct Eb2' as [Eba2 Ebc2].
      rewrite (taint_le_branch _ _ Hta Eba2), (taint_le_branch _ _ Htc Ebc2), (taint_le_index _ _ Htc Eic2). reflexivity. }
    rewrite Eb1, (mem_no_load_admissible _ _ _ _ _ _ _ Hpm).
    repeat split; try reflexivity.
    apply tenv_le_prop_put; [apply (mem_load_taint_admissible _ _ _ _ _ _ _ Hpm) | exact Hte].
  - (* RawLoadPointer *)
    destruct args as [|av []]; try discriminate Htlet.
    destruct (value_t te_abs A av) as [wv2|] eqn:Ev2; try discriminate Htlet.
    destruct wv2 as [|ta2 tc2|]; try discriminate Htlet.
    destruct (t_index ta2 || t_index tc2) eqn:Ei2; try discriminate Htlet.
    destruct (pol_check_branches pol && (t_branch ta2 || t_branch tc2)) eqn:Eb2; try discriminate Htlet.
    injection Htlet as <-.
    apply orb_false_iff in Ei2; destruct Ei2 as [Eia2 Eic2].
    destruct (value_t_mono te te_abs A av _ Hte Ev2) as (wv1 & Ev1 & Hvle).
    destruct wv1 as [|ta1 tc1|]; cbn [wt_le] in Hvle; try discriminate.
    apply andb_prop in Hvle; destruct Hvle as [Hta Htc].
    destruct Hx as [p Hp]. rewrite Hp, Ev1.
    rewrite (taint_le_index _ _ Hta Eia2), (taint_le_index _ _ Htc Eic2).
    assert (Eb1 : pol_check_branches pol && (t_branch ta1 || t_branch tc1) = false).
    { destruct (pol_check_branches pol); cbn in Eb2 |- *; [|reflexivity].
      apply orb_false_iff in Eb2; destruct Eb2 as [Eba2 Ebc2].
      rewrite (taint_le_branch _ _ Hta Eba2), (taint_le_branch _ _ Htc Ebc2). reflexivity. }
    rewrite Eb1, (mem_no_load_admissible _ _ _ _ _ _ _ Hpm).
    repeat split; try reflexivity.
    apply tenv_le_prop_put; [|exact Hte].
    cbn [wt_le]. rewrite (mem_load_taint_admissible _ _ _ _ _ _ _ Hpm).
    destruct Hpm as [_ Hpaux]. rewrite (Hpaux _). reflexivity.
Qed.

(** ## Factoring theorem: plain safety plus taint check yields constant time

    We now lift [taint_check_program] to a runtime-parametric factoring
    theorem. Every function in a verified specification table carries an
    inferred block table satisfying [taint_verify]; combining that invariant
    with plain operational safety [plain_safe] establishes [poison_safe] and
    two-run trace equality under [wp_ct_driver_plain]. *)

Module TaintCheckSound (R : Runtime).
Module PL := PoisonLogic R.
Import PL.

(** Plain operational safety: starting from frame [fr] in memory [m] and
    runtime state [s], no reachable machine state fails. *)
Definition plain_safe (ge : genv) (fr : frame) (m : mem) (s : R.state) (fuel : Z) : Prop :=
  forall st, RM.mreachable ge (mkConfig fr [] m fuel, s) st -> ~ fails ge (fst st).

(** [find_fn] depends only on the module inside [ge]. *)
Lemma find_fn_mod ge g :
  find_fn (mkGenv (ge_module ge) [] free_res) g = find_fn ge g.
Proof. unfold find_fn. reflexivity. Qed.

(** A verified call graph maps each function name in [entries] to its
    compiled body, specification, and verified block table. *)
Definition verified_table (pol : poison_policy) (ge : genv)
    (entries : list (name * tspec)) (g : name) (f : func) (sp : tspec)
    (tbl : list (name * tenv)) : Prop :=
  lookup g entries = Some sp /\
  find_fn ge g = Some (Defined f) /\
  taint_verify pol (ge_module ge) entries f sp tbl = true.

(** Extracting the verified block table for every function in a checked
    program. *)
Lemma taint_check_program_entry pol ge entries g sp :
  taint_check_program pol (ge_module ge) entries = true ->
  lookup g entries = Some sp ->
  exists f tbl, verified_table pol ge entries g f sp tbl.
Proof.
  intros Hprog Hlk. unfold taint_check_program in Hprog.
  rewrite forallb_forall in Hprog.
  pose proof (Hprog (g, sp) (lookup_in g sp entries Hlk)) as Hg.
  cbn in Hg. rewrite find_fn_mod in Hg.
  destruct (find_fn ge g) as [[f|]|] eqn:Ef; try discriminate Hg.
  unfold taint_check_fn in Hg.
  destruct (taint_infer pol (ge_module ge) entries f sp) as [tbl|] eqn:Einf; [|discriminate Hg].
  exists f, tbl. repeat split; assumption.
Qed.

(** A single active frame [(fr, te)] satisfies the verified taint invariant
    for specification [sp] and block table [tbl]. *)
Definition tframe_ok (pol : poison_policy) (md : module) (entries : list (name * tspec))
    (f : func) (sp : tspec) (tbl : list (name * tenv))
    (fr : frame) (te : tenv) : Prop :=
  fr_fn fr = f /\
  fr_doomed fr = None /\
  match fr_at fr with
  | Enter l from =>
      exists b te_b,
        find_block l (fn_blocks f) = Some b /\
        lookup l tbl = Some te_b /\
        exists te', phis_tenv (b_phis b) from te = Some te' /\ tenv_le_prop te' te_b
  | Exec l rest j =>
      exists te_abs,
        tenv_le_prop te te_abs /\
        ttail_ok pol md entries f sp tbl l rest j te_abs = true
  | Snapshot _ _ => False
  end.

(** Caller stack invariant: each waiting caller frame matches its taint stack
    entry and resumes a verified block tail for any return taint allowed by
    the callee's [ts_ret]. *)
Inductive tstack_ok (pol : poison_policy) (ge : genv) (entries : list (name * tspec))
    : option word_taint -> taint -> taint -> bool ->
      list (frame * pending) -> list (tenv * call_result) -> Prop :=
| tstack_nil ret_t tm ta wr_mem :
    tstack_ok pol ge entries ret_t tm ta wr_mem [] []
| tstack_cons ret_callee tm_callee ta_callee wr_mem
    cf pd cs caller_te r pcs g f sp tbl l rest j :
    verified_table pol ge entries g f sp tbl ->
    pd_res pd = r ->
    fr_fn cf = f ->
    fr_doomed cf = None ->
    fr_at cf = Exec l rest j ->
    tm_callee = ts_mem sp ->
    ta_callee = ts_aux sp ->
    implb (ts_writes sp) wr_mem = true ->
    (forall ots,
      (match ret_callee with
       | Some wt_out => exists wt, ots = [wt] /\ wt_le wt wt_out = true
       | None => ots = []
       end) ->
      exists te' te_abs,
        returned_tenv r ots caller_te = Some te' /\
        tenv_le_prop te' te_abs /\
        ttail_ok pol (ge_module ge) entries f sp tbl l rest j te_abs = true) ->
    tstack_ok pol ge entries (ts_ret sp) (ts_mem sp) (ts_aux sp) wr_mem cs pcs ->
    tstack_ok pol ge entries ret_callee tm_callee ta_callee wr_mem
      ((cf, pd) :: cs) ((caller_te, r) :: pcs).

(** Whole-configuration taint invariant pairing the active frame, the caller
    stack, and memory poison admissibility under ambient write flag [wr_mem]. *)
Definition tconfig_ok (pol : poison_policy) (ge : genv) (entries : list (name * tspec))
    (c : config) (ps : pstate) : Prop :=
  exists g f sp tbl wr_mem,
    verified_table pol ge entries g f sp tbl /\
    tframe_ok pol (ge_module ge) entries f sp tbl (c_frame c) (ps_tenv ps) /\
    implb (ts_writes sp) wr_mem = true /\
    pm_admissible (ts_mem sp) (ts_aux sp) wr_mem (ps_mem ps) (ps_aux ps) /\
    tstack_ok pol ge entries (ts_ret sp) (ts_mem sp) (ts_aux sp) wr_mem
      (c_callers c) (ps_callers ps).

(** Helper: when [step ge c] does not fail on a [Let] instruction, its
    address or allocation-size operand evaluates to the required word form. *)
Lemma plain_let_operand_ok ge f e ls l d k o args rest j cs m fuel :
  ~ fails ge (mkConfig (mkFrame f e ls None (Exec l (Let d k o args :: rest) j)) cs m fuel) ->
  match o, args with
  | Alloc _, [v] => exists sz, value_x ge e L v = Some (WInt sz)
  | RawLoad _ _, [av] | RawLoadPointer _ _, [av] => exists p, value_x ge e A av = Some (WPtr p)
  | _, _ => True
  end.
Proof.
  intros Hnf.
  destruct o; try exact I; destruct args as [|v [|]]; try exact I;
    unfold fails, step in Hnf; cbn in Hnf.
  - destruct (value_x ge e L v) as [[sz| |]|] eqn:Ev;
      [exists sz; reflexivity | | |];
      exfalso; apply Hnf; unfold op_res in *; destruct k; exact I.
  - destruct (value_x ge e A v) as [[|p|]|] eqn:Ev;
      [|exists p; reflexivity | |];
      exfalso; apply Hnf; unfold op_res in *; destruct k; exact I.
  - destruct (value_x ge e A v) as [[|p|]|] eqn:Ev;
      [|exists p; reflexivity | |];
      exfalso; apply Hnf; unfold op_res in *; destruct k; exact I.
Qed.

(** Helper: when [step ge c] does not fail on a [RawStore] or
    [RawStorePointer], its address operand evaluates to a pointer. *)
Lemma plain_store_addr_ok ge f e ls l w off v av rest j cs m fuel :
  ~ fails ge (mkConfig (mkFrame f e ls None (Exec l (RawStore w off v av :: rest) j)) cs m fuel) ->
  exists p, value_x ge e A av = Some (WPtr p).
Proof.
  intros Hnf. unfold fails, step in Hnf. cbn in Hnf.
  destruct (width_value_class w); cbn in Hnf; [|exfalso; apply Hnf; exact I].
  destruct (value_x ge e _ v); cbn in Hnf; [|exfalso; apply Hnf; exact I].
  destruct (value_x ge e A av) as [[|p|]|] eqn:Ev; cbn in Hnf;
    try (exfalso; apply Hnf; exact I).
  exists p. reflexivity.
Qed.

Lemma plain_store_ptr_addr_ok ge f e ls l off v av es rest j cs m fuel :
  ~ fails ge (mkConfig (mkFrame f e ls None (Exec l (RawStorePointer off v av es :: rest) j)) cs m fuel) ->
  exists p, value_x ge e A av = Some (WPtr p).
Proof.
  intros Hnf. unfold fails, step in Hnf. cbn in Hnf.
  destruct (value_x ge e A av) as [[|p|]|] eqn:Ev; [|exists p; reflexivity | |];
    exfalso; apply Hnf; destruct (value_x ge e P v) as [[| |]|]; exact I.
Qed.

(** Helper: executing one non-failing instruction (other than [CheckAhead] or
    [RawCall]) keeps [fr_doomed = None] and advances cleanly. *)
Lemma plain_inst_step_shape ge f e ls l i rest j cs m fuel :
  (match i with Let _ _ (CheckAhead _ _ _ _ _) _ | RawCall _ _ _ => False | _ => True end) ->
  ~ fails ge (mkConfig (mkFrame f e ls None (Exec l (i :: rest) j)) cs m fuel) ->
  match step ge (mkConfig (mkFrame f e ls None (Exec l (i :: rest) j)) cs m fuel) with
  | Next c' =>
      match i with
      | Call r (Global g) args =>
          (exists gf xs callee,
             find_fn ge g = Some (Defined gf) /\
             call_frame gf xs = Some callee /\
             c' = mkConfig callee
                    ((mkFrame f e ls None (Exec l rest j), mkPending r None) :: cs)
                    m fuel) \/
          (find_fn ge g = None /\
           exists e' ls' m',
             c' = mkConfig (mkFrame f e' ls' None (Exec l rest j)) cs m' fuel)
      | _ =>
          exists e' ls' m',
            c' = mkConfig (mkFrame f e' ls' None (Exec l rest j)) cs m' fuel
      end
  | Done o => ~ failure o
  | Fresh q k =>
      0 <= req_extent q /\
      forall base,
        exists e' ls' m',
          k base = mkConfig (mkFrame f e' ls' None (Exec l rest j)) cs m' fuel
  | Stuck _ => False
  end.
Proof.
  intros Hnca Hnf.
  unfold fails, step in Hnf |- *. cbn [c_frame c_mem c_callers c_fuel fr_at fr_doomed] in Hnf |- *.
  destruct (inst_step ge (mkFrame f e ls None (Exec l (i :: rest) j)) m i) as [out0|] eqn:Einst;
    [|exfalso; apply Hnf; exact I].
  assert (Hd : doomed_result ge (mkFrame f e ls None (Exec l (i :: rest) j)) m i out0 = Some (out0, None)).
  { unfold doomed_result. cbn [fr_doomed].
    destruct i; try (destruct out0 as [|o0| | |]; try reflexivity; destruct o0; reflexivity).
    destruct k; try (destruct out0 as [|o0| | |]; try reflexivity; destruct o0; reflexivity).
    destruct o; try (destruct out0 as [|o0| | |]; try reflexivity; destruct o0; reflexivity).
    exfalso; exact Hnca. }
  rewrite Hd in Hnf |- *. cbn [or_stuck fst snd] in Hnf |- *.
  destruct out0 as [e' ls' m' | o0 | gf xs pd | q k | g_out]; cbn [inst_next c_frame c_callers c_mem c_fuel fr_fn fr_env fr_locals] in Hnf |- *.
  - destruct i; try (exists e', ls', m'; reflexivity).
    destruct callee as [? | ? | g]; try (exists e', ls', m'; reflexivity).
    cbn [inst_step fr_env fr_locals] in Einst.
    destruct (map_option (arg_x ge e) args); [|discriminate Einst].
    destruct (find_fn ge g) as [[gf'|g']|] eqn:Eg; try discriminate Einst.
    right. split; [reflexivity | exists e', ls', m'; reflexivity].
  - exact Hnf.
  - destruct (call_frame gf xs) as [callee|] eqn:Ecf; [|exfalso; apply Hnf; exact I].
    destruct i as [d k o args | d o args lw | w off v av | off v av es | r cal args | r cal args | ? ? | ? ? | ?];
      cbn [inst_step fr_env fr_locals] in Einst; try discriminate Einst;
      try solve [unfold bind_res, store_out in Einst;
                 repeat (cbv zeta in Einst;
                   match type of Einst with
                   | (match ?x with _ => _ end) = _ => destruct x; try discriminate Einst
                   | Some (match ?x with _ => _ end) = _ => destruct x; try discriminate Einst
                   end)].
    + destruct cal as [? | ? | g]; [discriminate Einst | discriminate Einst |].
      destruct (map_option (arg_x ge e) args) as [xs'|]; [|discriminate Einst].
      destruct (find_fn ge g) as [[gf'|g']|] eqn:Eg.
      * injection Einst as -> -> ->. left. exists gf, xs, callee. repeat split; assumption.
      * discriminate Einst.
      * unfold external_call in Einst.
        repeat (cbv zeta in Einst;
          match type of Einst with
          | (match ?x with _ => _ end) = _ => destruct x; try discriminate Einst
          | Some (match ?x with _ => _ end) = _ => destruct x; try discriminate Einst
          end).
    + exfalso; exact Hnca.
  - split; [lia|].
    intros base. destruct (k base) as [[e' ls'] m']. exists e', ls', m'. reflexivity.
  - exfalso; apply Hnf; exact I.
Qed.

(** Helper: a non-variadic [call_frame] enters [fn_entry] with [fr_doomed = None]. *)
Lemma call_frame_nonvariadic_entry gf xs callee entry :
  variadic_func gf = false ->
  fn_entry gf = Some entry ->
  call_frame gf xs = Some callee ->
  fr_fn callee = gf /\ fr_doomed callee = None /\ fr_at callee = Enter entry None.
Proof.
  intros Hv Hent Hcf. unfold call_frame, fn_entry in *.
  destruct (fn_blocks gf) as [|b bs]; [discriminate Hent|].
  injection Hent as <-.
  destruct (length xs <? length (fn_params gf))%nat; [discriminate Hcf|].
  rewrite Hv in Hcf. injection Hcf as <-. repeat split; reflexivity.
Qed.

(** Extracting the verified invariants from [taint_verify]. *)
Lemma taint_verify_entry pol md entries f sp tbl :
  taint_verify pol md entries f sp tbl = true ->
  variadic_func f = false /\
  exists entry b_entry te_init te_entry,
    fn_entry f = Some entry /\
    find_block entry (fn_blocks f) = Some b_entry /\
    b_phis b_entry = [] /\
    call_tenv f (ts_args sp) = Some te_init /\
    lookup entry tbl = Some te_entry /\
    tenv_le_prop te_init te_entry /\
    (forall l te0, lookup l tbl = Some te0 -> tblock_ok pol md entries f sp tbl l te0 = true).
Proof.
  unfold taint_verify. intros H.
  apply andb_prop in H; destruct H as [Hv H]. apply negb_true_iff in Hv. split; [exact Hv|].
  destruct (fn_entry f) as [entry|] eqn:Eent; [|discriminate].
  destruct (find_block entry (fn_blocks f)) as [be|] eqn:Ebe; [|discriminate].
  destruct (call_tenv f (ts_args sp)) as [ti|] eqn:Eti; [|discriminate].
  destruct (lookup entry tbl) as [te|] eqn:Ete; [|discriminate].
  destruct (b_phis be) eqn:Ephis; [|discriminate].
  apply andb_prop in H; destruct H as [Hle Hall].
  exists entry, be, ti, te. repeat split; try assumption.
  - apply tenv_le_sound; exact Hle.
  - intros l te0 Hlk. rewrite forallb_forall in Hall.
    exact (Hall (l, te0) (lookup_in l te0 tbl Hlk)).
Qed.

Lemma op_res_int_alloc_only o k xs m q kont :
  op_res_int o k xs m = Some (OpAlloc q kont) ->
  exists al, o = Alloc al.
Proof.
  unfold op_res_int. intros H.
  destruct o; try (eexists; reflexivity);
    repeat (cbv zeta beta in H;
      match type of H with
      | (match ?x with _ => _ end) = _ => destruct x; try discriminate H
      end); discriminate H.
Qed.

Lemma op_res_alloc_only o k xs m q kont :
  op_res o k xs m = Some (OpAlloc q kont) ->
  exists al, o = Alloc al.
Proof.
  unfold op_res. intros H.
  destruct o;
    repeat (cbv zeta beta in H;
      match type of H with
      | op_res_int _ _ _ _ = _ => eapply op_res_int_alloc_only; exact H
      | float_integer _ _ _ _ _ = _ => unfold float_integer in H
      | (match ?x with _ => _ end) = _ => destruct x; try discriminate H
      end);
    try (eapply op_res_int_alloc_only; exact H); try discriminate H.
Qed.

Lemma doomed_result_not_fresh ge fr m i out0 q kont d0 :
  doomed_result ge fr m i out0 = Some (IFresh q kont, d0) ->
  out0 = IFresh q kont.
Proof.
  unfold doomed_result. intros H.
  destruct out0;
    repeat match type of H with
    | (match ?x with _ => _ end) = _ => destruct x; try discriminate H
    end;
    try (injection H as -> ->; reflexivity); discriminate H.
Qed.

Lemma let_step_fresh_is_alloc ge f e ls l d k o args rest j cs m fuel q k0 :
  step ge (mkConfig (mkFrame f e ls None (Exec l (Let d k o args :: rest) j)) cs m fuel) = Fresh q k0 ->
  exists al, o = Alloc al.
Proof.
  unfold step. cbn [c_frame fr_at c_mem].
  destruct (inst_step ge (mkFrame f e ls None (Exec l (Let d k o args :: rest) j)) m (Let d k o args))
    as [out0|] eqn:Einst; [|discriminate].
  destruct (doomed_result ge (mkFrame f e ls None (Exec l (Let d k o args :: rest) j)) m (Let d k o args) out0)
    as [[out1 d1]|] eqn:Edoom; [|discriminate].
  cbn [or_stuck fst snd]. intros H.
  destruct out1 as [e' ls' m' | o0 | gf xs pd | q' kont | g_out]; cbn [inst_next] in H; try discriminate H.
  - destruct (call_frame gf xs); discriminate H.
  - apply doomed_result_not_fresh in Edoom. subst out0.
    cbn [inst_step fr_env fr_locals] in Einst. cbv zeta in Einst.
    assert (Hgen :
      (let* classes := op_arg_classes o k in
       let* xs := map2_option (value_x ge e) classes args in
       let* out := op_res o k xs m in
       match out with
       | OpRes r m' => Some (bind_res d r e ls m')
       | OpUB why => Some (IStop (UB why))
       | OpAlloc q1 kont1 =>
           Some (IFresh q1 (fun base => let (x, m') := kont1 base in (put d x e, ls, m')))
       end) = Some (IFresh q' kont) -> exists al, o = Alloc al).
    { intros H0.
      destruct (op_arg_classes o k) as [cls|]; [|discriminate H0].
      destruct (map2_option (value_x ge e) cls args) as [xs|]; [|discriminate H0].
      destruct (op_res o k xs m) as [[r m'|why|q1 kont1]|] eqn:Eop; try discriminate H0.
      - unfold bind_res in H0; destruct r; discriminate H0.
      - eapply op_res_alloc_only; exact Eop. }
    destruct k, o; try (apply Hgen; exact Einst); try discriminate Einst.
    + (* P, VaArgs *)
      destruct args as [|v [|]]; try discriminate Einst;
        destruct v; try discriminate Einst;
        match type of Einst with
        | (match ?x with _ => _ end) = _ => destruct x as [[|p|]|]; discriminate Einst
        end.
    + (* A, CheckLocal *)
      destruct args; [|discriminate Einst].
      match type of Einst with
      | (match ?x with _ => _ end) = _ => destruct x as [[base|]|]; try discriminate Einst
      end.
      unfold bind_res, checked_res in Einst.
      match type of Einst with
      | (match ?x with _ => _ end) = _ => destruct x as [[[]| |]|]; discriminate Einst
      end.
    + (* F, CheckFunction *)
      destruct args as [|v [|]]; try discriminate Einst.
      match type of Einst with
      | (match ?x with _ => _ end) = _ => destruct x as [[|p|]|]; try discriminate Einst
      end.
      unfold bind_res, checked_res in Einst.
      match type of Einst with
      | (match ?x with _ => _ end) = _ => destruct x as [[[]| |]|]; discriminate Einst
      end.
Qed.

Lemma edge_step_not_doomed c from t :
  fr_doomed (c_frame c) = None ->
  edge_step c from t =
    Next (continue_at c (with_point (c_frame c) (Enter (edge_label t) (Some from))) (c_mem c) (c_fuel c)).
Proof. intros Hd. unfold edge_step. rewrite Hd. destruct t; reflexivity. Qed.

Lemma implb_true_r b : implb b true = true.
Proof. destruct b; reflexivity. Qed.

Local Ltac split_tconfig :=
  cbn [c_frame c_callers c_mem c_fuel fr_fn fr_doomed fr_at ps_tenv ps_callers ps_mem ps_aux];
  split;
  [ try assumption
  | split;
    [ split; [ try reflexivity; try assumption | split; [ try reflexivity; try assumption | ] ]
    | split;
      [ try assumption; try apply implb_true_r
      | split; [ try assumption | try assumption ] ] ] ].

(** One-step preservation of [tconfig_ok] and poison-fault freedom whenever
    the underlying plain step does not fail. *)
Lemma tconfig_step_ok pol ge entries c ps :
  taint_check_program pol (ge_module ge) entries = true ->
  tconfig_ok pol ge entries c ps ->
  ~ fails ge c ->
  ~ pfails pol ge c ps /\
  match pstep pol ge c ps with
  | PNext c' ps' => step ge c = Next c' /\ tconfig_ok pol ge entries c' ps'
  | PDone o _ => ~ failure o
  | PFresh q k =>
      exists k0,
        step ge c = Fresh q k0 /\
        0 <= req_extent q /\
        forall base,
          fst (k base) = k0 base /\
          tconfig_ok pol ge entries (fst (k base)) (snd (k base))
  | PTrap _ | PStuck _ => False
  end.
Proof.
  intros Hprog Hok Hnf.
  destruct c as [[f e ls doom pt] cs m fuel].
  destruct ps as [te pcs pm paux].
  destruct Hok as (g & f0 & sp & tbl & wr_mem & Hvt & Hfr & Hwr_mem & Hpm & Hstk).
  destruct Hfr as (Hfn & Hdoom & Hpt).
  cbn [c_frame c_callers c_mem c_fuel ps_tenv ps_callers ps_mem ps_aux fr_fn fr_doomed fr_at] in *.
  subst f0 doom.
  destruct pt as [? ? | l from | l rest j]; [contradiction | |].
  - (* Enter l from *)
    destruct Hpt as (b & te_b & Hb & Htbl & te' & Hphis & Hle').
    pose proof Hvt as (Hent_lk & Hgf & Hver).
    destruct (taint_verify_entry _ _ _ _ _ _ Hver) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hblks).
    pose proof (Hblks l te_b Htbl) as Hbk.
    unfold tblock_ok in Hbk. rewrite Hb in Hbk.
    unfold pstep, tstep. cbn [c_frame fr_doomed fr_at c_fuel fr_fn ps_tenv ps_callers ps_mem ps_aux].
    destruct (Z.eqb_spec fuel 0) as [-> | Hnz].
    + unfold step. cbn. split; [unfold pfails, pstep, tstep; cbn; auto | auto].
    + rewrite Hb, Hphis.
      unfold fails, step in Hnf |- *. cbn [c_frame fr_doomed fr_at c_fuel fr_fn fr_env fr_locals] in Hnf |- *.
      replace (fuel =? 0) with false in * by (symmetry; apply Z.eqb_neq; exact Hnz).
      rewrite Hb in Hnf |- *.
      destruct (phis_env ge (b_phis b) from e) as [e'|] eqn:Epe; [|exfalso; apply Hnf; exact I].
      split.
      * unfold pfails, pstep, tstep. cbn [c_frame fr_doomed fr_at c_fuel fr_fn ps_tenv ps_callers ps_mem ps_aux].
        replace (fuel =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hnz).
        rewrite Hb, Hphis. unfold step. cbn.
        replace (fuel =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hnz).
        rewrite Hb, Epe. auto.
      * split; [reflexivity|].
        exists g, f, sp, tbl, wr_mem. split_tconfig.
        exists te_b. split; [exact Hle' | exact Hbk].
  - (* Exec l rest j *)
    destruct Hpt as (te_abs & Hte_le & Htail).
    destruct rest as [|i rest].
    + (* Jump terminator *)
      unfold ttail_ok in Htail. cbn [tinsts] in Htail.
      unfold pstep, tstep, jump_tstep. cbv zeta.
      cbn [c_frame fr_doomed fr_at fr_fn ps_tenv ps_callers ps_mem ps_aux].
      destruct j as [t | v t1 t2 | v | vs | |].
      * (* JGoto t *)
        cbn [tjump_ok] in Htail. unfold tedge_ok in Htail.
        destruct (find_block (edge_label t) (fn_blocks f)) as [bt|] eqn:Ebt; [|discriminate Htail].
        destruct (lookup (edge_label t) tbl) as [te_t|] eqn:Etbl; [|discriminate Htail].
        destruct (phis_tenv (b_phis bt) (Some l) te_abs) as [te_abs'|] eqn:Ep2; [|discriminate Htail].
        destruct (phis_tenv_mono _ _ te te_abs te_abs' Hte_le Ep2) as (te1' & Ep1 & Hle1).
        unfold step, jump_step. cbn [c_frame fr_at fr_doomed].
        rewrite edge_step_not_doomed; [|reflexivity].
        cbn [c_frame c_callers c_mem c_fuel continue_at with_point].
        split.
        -- unfold pfails, pstep, tstep, jump_tstep, step, jump_step. cbn [c_frame fr_at fr_doomed ps_tenv ps_callers ps_mem ps_aux].
           rewrite edge_step_not_doomed; [|reflexivity]. auto.
        -- split; [reflexivity|].
           exists g, f, sp, tbl, wr_mem. split_tconfig.
           exists bt, te_t. repeat split; try assumption.
           exists te1'. split; [exact Ep1 | eapply tenv_le_prop_trans; [exact Hle1 | apply tenv_le_sound; exact Htail]].
      * (* JBranch v t1 t2 *)
        cbn [tjump_ok] in Htail.
        destruct (value_t te_abs W v) as [wt2|] eqn:Ev2; [|discriminate Htail].
        destruct wt2 as [tv2| |]; [|discriminate Htail | discriminate Htail].
        apply andb_prop in Htail; destruct Htail as [Htail He2].
        apply andb_prop in Htail; destruct Htail as [Hbr He1].
        apply negb_true_iff in Hbr.
        destruct (value_t_mono te te_abs W v (WTInt tv2) Hte_le Ev2) as (wt1 & Ev1 & Hwle).
        destruct wt1 as [tv1| |]; cbn [wt_le] in Hwle; [|discriminate | discriminate].
        rewrite Ev1, (taint_le_branch _ _ Hwle Hbr).
        unfold fails, step, jump_step in Hnf |- *. cbn [c_frame fr_at fr_doomed fr_env] in Hnf |- *.
        destruct (value_x ge e W v) as [[n| |]|] eqn:Exv; try (exfalso; apply Hnf; exact I).
        rewrite edge_step_not_doomed; [|reflexivity].
        cbn [c_frame c_callers c_mem c_fuel continue_at with_point].
        split.
        -- unfold pfails, pstep, tstep, jump_tstep. cbn [c_frame fr_at fr_doomed fr_env ps_tenv ps_callers ps_mem ps_aux].
           rewrite Ev1, (taint_le_branch _ _ Hwle Hbr).
           unfold step, jump_step. cbn [c_frame fr_at fr_doomed fr_env].
           rewrite Exv, edge_step_not_doomed; [|reflexivity]. auto.
        -- split; [reflexivity|].
           destruct (n =? 0) eqn:En.
           ++ unfold tedge_ok in He2.
              destruct (find_block (edge_label t2) (fn_blocks f)) as [bt|] eqn:Ebt; [|discriminate He2].
              destruct (lookup (edge_label t2) tbl) as [te_t|] eqn:Etbl; [|discriminate He2].
              destruct (phis_tenv (b_phis bt) (Some l) te_abs) as [te_abs'|] eqn:Ep2; [|discriminate He2].
              destruct (phis_tenv_mono _ _ te te_abs te_abs' Hte_le Ep2) as (te1' & Ep1 & Hle1).
              exists g, f, sp, tbl, wr_mem. split_tconfig.
              exists bt, te_t. repeat split; try assumption.
              exists te1'. split; [exact Ep1 | eapply tenv_le_prop_trans; [exact Hle1 | apply tenv_le_sound; exact He2]].
           ++ unfold tedge_ok in He1.
              destruct (find_block (edge_label t1) (fn_blocks f)) as [bt|] eqn:Ebt; [|discriminate He1].
              destruct (lookup (edge_label t1) tbl) as [te_t|] eqn:Etbl; [|discriminate He1].
              destruct (phis_tenv (b_phis bt) (Some l) te_abs) as [te_abs'|] eqn:Ep2; [|discriminate He1].
              destruct (phis_tenv_mono _ _ te te_abs te_abs' Hte_le Ep2) as (te1' & Ep1 & Hle1).
              exists g, f, sp, tbl, wr_mem. split_tconfig.
              exists bt, te_t. repeat split; try assumption.
              exists te1'. split; [exact Ep1 | eapply tenv_le_prop_trans; [exact Hle1 | apply tenv_le_sound; exact He1]].
      * (* JRet v *)
        cbn [tjump_ok] in Htail.
        destruct (fn_ret f) as [k| |] eqn:Eret; [|discriminate Htail | discriminate Htail].
        destruct (ts_ret sp) as [wt_out|] eqn:Etsr; [|discriminate Htail].
        destruct (value_t te_abs k v) as [wt2|] eqn:Ev2; [|discriminate Htail].
        destruct (value_t_mono te te_abs k v wt2 Hte_le Ev2) as (wt1 & Ev1 & Hwle).
        rewrite Ev1.
        assert (Hwt1 : wt_le wt1 wt_out = true) by (eapply wt_le_trans; eassumption).
        unfold fails, step, jump_step in Hnf |- *. cbn [c_frame fr_at fr_doomed fr_fn fr_env] in Hnf |- *.
        rewrite Eret in Hnf |- *.
        destruct (value_x ge e k v) as [wv|] eqn:Exv; [|exfalso; apply Hnf; exact I].
        unfold return_step in Hnf |- *. cbn [c_frame fr_locals c_mem c_callers] in Hnf |- *.
        destruct (invalidate_locals ls m) as [m'|] eqn:Einv; [|exfalso; apply Hnf; exact I].
        inversion Hstk as [|ret_c tm_c ta_c wr_c cf pd cs' caller_te r pcs'
            g_c f_c sp_c tbl_c l_c rest_c j_c Hvt_c Hpd Hfn_c Hdoom_c Hat_c Htm_c Hta_c Hwr_c Hret_c Hstk_c];
          subst; cbn [return_tstep ps_callers ps_mem ps_aux].
        -- (* Top-level return *)
           split.
           ++ unfold pfails, pstep, tstep, jump_tstep, return_tstep, step, jump_step, return_step, or_stuck.
              cbn [c_frame fr_doomed fr_at fr_fn fr_env fr_locals c_mem c_callers c_fuel ps_tenv ps_callers ps_mem ps_aux].
              rewrite Eret, Ev1, Exv, Einv. exact Hnf.
           ++ exact Hnf.
        -- (* Return to caller *)
           destruct (Hret_c [wt1] ltac:(exists wt1; split; [reflexivity | exact Hwt1]))
             as (te_c' & te_abs_c & Hrt & Hle_c & Htail_c).
           rewrite Hrt.
           destruct (match pd_conv pd with None => Some (Ret wv) | Some (cw, kw) => converted_outcome cw kw (Ret wv) end)
             as [o'|] eqn:Econv; [|exfalso; apply Hnf; exact I].
           destruct (returned_env (pd_res pd) o' (fr_env cf)) as [ec'|] eqn:Ere; [|exfalso; apply Hnf; exact I].
           split.
           ++ unfold pfails, pstep, tstep, jump_tstep, return_tstep, step, jump_step, return_step, or_stuck.
              cbn [c_frame fr_doomed fr_at fr_fn fr_env fr_locals c_mem c_callers c_fuel ps_tenv ps_callers ps_mem ps_aux].
              rewrite Eret, Ev1, Hrt, Exv, Einv, Econv, Ere. auto.
           ++ split; [reflexivity|].
              exists g_c, (fr_fn cf), sp_c, tbl_c, wr_mem. split_tconfig.
              ** rewrite Hat_c. exists te_abs_c. split; [exact Hle_c | exact Htail_c].
              ** rewrite <- Htm_c, <- Hta_c. exact Hpm.
      * (* JRets *) discriminate Htail.
      * (* JRetVoid *)
        cbn [tjump_ok] in Htail.
        destruct (fn_ret f) eqn:Eret; try discriminate Htail.
        destruct (ts_ret sp) eqn:Etsr; try discriminate Htail.
        unfold fails, step, jump_step in Hnf |- *. cbn [c_frame fr_at fr_doomed fr_fn fr_env] in Hnf |- *.
        unfold return_step in Hnf |- *. cbn [c_frame fr_locals c_mem c_callers] in Hnf |- *.
        destruct (invalidate_locals ls m) as [m'|] eqn:Einv; [|exfalso; apply Hnf; exact I].
        inversion Hstk as [|ret_c tm_c ta_c wr_c cf pd cs' caller_te r pcs'
            g_c f_c sp_c tbl_c l_c rest_c j_c Hvt_c Hpd Hfn_c Hdoom_c Hat_c Htm_c Hta_c Hwr_c Hret_c Hstk_c];
          subst; cbn [return_tstep ps_callers ps_mem ps_aux].
        -- split.
           ++ unfold pfails, pstep, tstep, jump_tstep, return_tstep, step, jump_step, return_step, or_stuck.
              cbn [c_frame fr_doomed fr_at fr_fn fr_env fr_locals c_mem c_callers c_fuel ps_tenv ps_callers ps_mem ps_aux].
              rewrite Eret, Einv. exact Hnf.
           ++ exact Hnf.
        -- destruct (Hret_c [] eq_refl) as (te_c' & te_abs_c & Hrt & Hle_c & Htail_c).
           rewrite Hrt.
           destruct (match pd_conv pd with None => Some RetVoid | Some (cw, kw) => converted_outcome cw kw RetVoid end)
             as [o'|] eqn:Econv; [|exfalso; apply Hnf; exact I].
           destruct (returned_env (pd_res pd) o' (fr_env cf)) as [ec'|] eqn:Ere; [|exfalso; apply Hnf; exact I].
           split.
           ++ unfold pfails, pstep, tstep, jump_tstep, return_tstep, step, jump_step, return_step, or_stuck.
              cbn [c_frame fr_doomed fr_at fr_fn fr_env fr_locals c_mem c_callers c_fuel ps_tenv ps_callers ps_mem ps_aux].
              rewrite Eret, Hrt, Einv, Econv, Ere. auto.
           ++ split; [reflexivity|].
              exists g_c, (fr_fn cf), sp_c, tbl_c, wr_mem. split_tconfig.
              ** rewrite Hat_c. exists te_abs_c. split; [exact Hle_c | exact Htail_c].
              ** rewrite <- Htm_c, <- Hta_c. exact Hpm.
      * (* JUnreachable *)
        exfalso. unfold fails, step, jump_step in Hnf. cbn in Hnf. apply Hnf; exact I.
    + (* Instruction i :: rest *)
      unfold ttail_ok in Htail. cbn [tinsts] in Htail.
      destruct (tinst pol (ge_module ge) entries sp i te_abs) as [te_abs'|] eqn:Etinst; [|discriminate Htail].
      assert (Hnca : match i with Let _ _ (CheckAhead _ _ _ _ _) _ | RawCall _ _ _ => False | _ => True end).
      { destruct i; try exact I; [|discriminate Etinst].
        destruct o; try exact I. unfold tinst, tlet in Etinst. destruct k; cbn in Etinst; discriminate Etinst. }
      pose proof (plain_inst_step_shape ge f e ls l i rest j cs m fuel Hnca Hnf) as Hshape.
      destruct i as [d k o args | d o args lw | w off v av | off v av es | r callee args | r callee args | lx size | lfile lline | tq].
      * (* Let *)
        pose proof (plain_let_operand_ok ge f e ls l d k o args rest j cs m fuel Hnf) as Hx.
        pose proof (tlet_sound pol ge e d k o args te te_abs te_abs' pcs pm paux sp wr_mem Hte_le Hpm Etinst Hx) as Hls.
        unfold pfails, pstep, tstep, inst_tstep.
        cbn [c_frame fr_doomed fr_at fr_env ps_tenv ps_callers ps_mem ps_aux].
        destruct (let_tstep pol ge e (mkPState te pcs pm paux) d k o args)
          as [[te' pcs' pm' paux'] | ots | tps | why | why] eqn:Elts; try contradiction.
        -- destruct Hls as (-> & -> & -> & Hle').
           destruct (step ge (mkConfig (mkFrame f e ls None (Exec l (Let d k o args :: rest) j)) cs m fuel))
             as [c' | o' | q k0 | why] eqn:Est; try contradiction.
           ++ destruct Hshape as (e' & ls' & m' & ->).
              split; [auto|]. split; [reflexivity|].
              exists g, f, sp, tbl, wr_mem. split_tconfig.
              exists te_abs'. split; [exact Hle' | exact Htail].
           ++ split; [exact Hshape | exact Hshape].
           ++ (* Fresh mismatch impossible because let_tstep returned TNext while step returned Fresh *)
              exfalso.
              destruct (let_step_fresh_is_alloc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Est) as [al ->].
              unfold let_tstep, is_zero_idiom in Elts. rewrite andb_false_r in Elts. cbn in Elts.
              destruct args as [|v [|]]; try discriminate Elts.
              destruct (value_x ge e L v) as [[sz| |]|]; try discriminate Elts.
              destruct (value_t te L v) as [[tsz| |]|]; try discriminate Elts.
              destruct (t_branch tsz); [discriminate Elts|].
              destruct (t_index tsz); [discriminate Elts|].
              destruct (max_allocation_size <? sz); discriminate Elts.
        -- (* TDone (Alloc TooBig) *)
           destruct Hls as [-> Halloc].
           destruct o; try contradiction.
           destruct (step ge (mkConfig (mkFrame f e ls None (Exec l (Let d k (Alloc align) args :: rest) j)) cs m fuel))
             as [c' | o' | q k0 | why] eqn:Est; try contradiction.
           ++ exfalso.
              unfold let_tstep, is_zero_idiom in Elts. rewrite andb_false_r in Elts. cbn in Elts.
              destruct args as [|v [|]]; try discriminate Elts.
              destruct (value_x ge e L v) as [[sz| |]|] eqn:Ev; try discriminate Elts.
              destruct (value_t te L v) as [[tsz| |]|]; try discriminate Elts.
              destruct (t_branch tsz); [discriminate Elts|].
              destruct (t_index tsz); [discriminate Elts|].
              destruct (max_allocation_size <? sz) eqn:Ebig; [|discriminate Elts].
              unfold step, inst_step in Est;
                cbn [c_frame c_mem c_callers c_fuel fr_at fr_doomed fr_env fr_locals] in Est;
                destruct k; cbn [op_arg_classes map2_option] in Est; rewrite Ev in Est;
                unfold op_res, op_res_int in Est; cbn [fmt_of] in Est; rewrite Ebig in Est; discriminate Est.
           ++ split; [exact Hshape | exact Hshape].
           ++ exfalso.
              unfold let_tstep, is_zero_idiom in Elts. rewrite andb_false_r in Elts. cbn in Elts.
              destruct args as [|v [|]]; try discriminate Elts.
              destruct (value_x ge e L v) as [[sz| |]|] eqn:Ev; try discriminate Elts.
              destruct (value_t te L v) as [[tsz| |]|]; try discriminate Elts.
              destruct (t_branch tsz); [discriminate Elts|].
              destruct (t_index tsz); [discriminate Elts|].
              destruct (max_allocation_size <? sz) eqn:Ebig; [|discriminate Elts].
              unfold step, inst_step in Est;
                cbn [c_frame c_mem c_callers c_fuel fr_at fr_doomed fr_env fr_locals] in Est;
                destruct k; cbn [op_arg_classes map2_option] in Est; rewrite Ev in Est;
                unfold op_res, op_res_int in Est; cbn [fmt_of] in Est; rewrite Ebig in Est; discriminate Est.
        -- (* TFresh (Alloc) *)
           destruct o; try contradiction.
           destruct (step ge (mkConfig (mkFrame f e ls None (Exec l (Let d k (Alloc align) args :: rest) j)) cs m fuel))
             as [c' | o' | q k0 | why] eqn:Est; try contradiction.
           ++ exfalso.
              unfold let_tstep, is_zero_idiom in Elts. rewrite andb_false_r in Elts. cbn in Elts.
              destruct args as [|v [|]]; try discriminate Elts.
              destruct (value_x ge e L v) as [[sz| |]|] eqn:Ev; try discriminate Elts.
              destruct (value_t te L v) as [[tsz| |]|]; try discriminate Elts.
              destruct (t_branch tsz); [discriminate Elts|].
              destruct (t_index tsz); [discriminate Elts|].
              destruct (max_allocation_size <? sz) eqn:Ebig; [discriminate Elts|].
              unfold step, inst_step in Est;
                cbn [c_frame c_mem c_callers c_fuel fr_at fr_doomed fr_env fr_locals] in Est;
                destruct k; cbn [op_arg_classes map2_option] in Est; rewrite Ev in Est;
                unfold op_res, op_res_int in Est; cbn [fmt_of] in Est; rewrite Ebig in Est; discriminate Est.
           ++ split; [exact Hshape | exact Hshape].
           ++ destruct Hshape as [Hext Hk].
              split; [lia|].
              exists k0. split; [reflexivity | split; [exact Hext |]].
              intros base. cbn [fst snd]. split; [reflexivity|].
              destruct (Hk base) as (e' & ls' & m' & ->).
              destruct (Hls base) as (Hcs' & Hle' & Hpm').
              exists g, f, sp, tbl, wr_mem. split_tconfig.
              ** exists te_abs'. split; [exact Hle' | exact Htail].
              ** rewrite Hcs'. exact Hstk.
      * (* Flight *)
        cbn [tinst] in Etinst.
        destruct (map_option (flight_arg_t te_abs) args) as [ts2|] eqn:Ea2; [|discriminate Etinst].
        destruct (flight_cap_t te_abs lw) as [tc2|] eqn:Ec2; [|discriminate Etinst].
        destruct (op_checks_vartime pol o L && t_vartime (join_taints ts2)) eqn:Evt2; [discriminate Etinst|].
        injection Etinst as <-.
        destruct (map_flight_arg_t_mono te te_abs args ts2 Hte_le Ea2) as (ts1 & Ea1 & Htsle).
        destruct (flight_cap_t_mono te te_abs lw tc2 Hte_le Ec2) as (tc1 & Ec1 & Htcle).
        pose proof (join_taints_mono ts1 ts2 Htsle) as Hjle.
        assert (Evt1 : op_checks_vartime pol o L && t_vartime (join_taints ts1) = false)
          by (destruct (op_checks_vartime pol o L); cbn in Evt2 |- *; [eapply taint_le_vartime; eassumption | reflexivity]).
        unfold pfails, pstep, tstep, inst_tstep.
        cbn [c_frame fr_doomed fr_at fr_env ps_tenv ps_callers ps_mem ps_aux].
        rewrite Ea1, Ec1, Evt1.
        destruct (step ge (mkConfig (mkFrame f e ls None (Exec l (Flight d o args lw :: rest) j)) cs m fuel))
          as [c' | o' | q k0 | why] eqn:Est; try contradiction.
        -- destruct Hshape as (e' & ls' & m' & ->).
           split; [auto|]. split; [reflexivity|].
           exists g, f, sp, tbl, wr_mem. split_tconfig.
           exists (put d (WTPtr (join_taints ts2) tc2) te_abs).
           split; [apply tenv_le_prop_put; [cbn [wt_le]; rewrite Hjle, Htcle; reflexivity | exact Hte_le] | exact Htail].
        -- split; [exact Hshape | exact Hshape].
        -- exfalso. unfold step, inst_step in Est; cbn in Est.
           destruct (map_option (flight_arg_x ge e) args); try discriminate Est;
             destruct (alu o L l0) as [[| |]|]; try discriminate Est;
             destruct (flight_cap ge e lw); discriminate Est.
      * (* RawStore *)
        cbn [tinst] in Etinst.
        destruct (ts_writes sp) eqn:Ewr; [|discriminate Etinst].
        assert (Ewm : wr_mem = true) by (destruct wr_mem; [reflexivity | discriminate]).
        subst wr_mem. rewrite <- Ewr in Hwr_mem.
        cbn [negb] in Etinst.
        destruct (width_value_class w) as [vk|] eqn:Evk; [|discriminate Etinst].
        destruct (value_t te_abs A av) as [wa2|] eqn:Ea2; [|discriminate Etinst].
        destruct wa2 as [|ta2 tc2|]; [discriminate | | discriminate].
        destruct (t_index ta2) eqn:Ei2; [discriminate|].
        destruct (pol_check_branches pol && (t_branch ta2 || t_branch tc2 || t_index tc2)) eqn:Eb2; [discriminate|].
        destruct (value_t_mono te te_abs A av _ Hte_le Ea2) as (wa1 & Ea1 & Hwale).
        destruct wa1 as [|ta1 tc1|]; cbn [wt_le] in Hwale; try discriminate.
        apply andb_prop in Hwale; destruct Hwale as [Hta Htc].
        pose proof (plain_store_addr_ok ge f e ls l w off v av rest j cs m fuel Hnf) as [p Hp].
        assert (Eb1 : pol_check_branches pol && (t_branch ta1 || t_branch tc1 || t_index tc1) = false).
        { destruct (pol_check_branches pol); cbn in Eb2 |- *; [|reflexivity].
          apply orb_false_iff in Eb2; destruct Eb2 as [Eb2' Eic2]; apply orb_false_iff in Eb2'; destruct Eb2' as [Eba2 Ebc2].
          rewrite (taint_le_branch _ _ Hta Eba2), (taint_le_branch _ _ Htc Ebc2), (taint_le_index _ _ Htc Eic2). reflexivity. }
        unfold pfails, pstep, tstep, inst_tstep.
        cbn [c_frame fr_doomed fr_at fr_env ps_tenv ps_callers ps_mem ps_aux].
        rewrite Evk, Hp, Ea1, (taint_le_index _ _ Hta Ei2), Eb1.
        rewrite (mem_no_store_admissible _ _ _ _ _ _ Hpm).
        destruct (value_t te_abs vk v) as [wv2|] eqn:Ev2; [|destruct w; discriminate Etinst].
        destruct (value_t_mono te te_abs vk v wv2 Hte_le Ev2) as (wv1 & Ev1 & Hwvle).
        rewrite Ev1.
        destruct (step ge (mkConfig (mkFrame f e ls None (Exec l (RawStore w off v av :: rest) j)) cs m fuel))
          as [c' | o' | q k0 | why] eqn:Est; try contradiction.
        -- destruct Hshape as (e' & ls' & m' & ->).
           destruct w; try (
             destruct wv2 as [tv2| |]; try discriminate Etinst;
             destruct wv1 as [tv1| |]; cbn [wt_le] in Hwvle; try discriminate;
             destruct (taint_le tv2 (ts_mem sp)) eqn:Htv2; try discriminate Etinst;
             injection Etinst as <-;
             assert (Htv1 : taint_le tv1 (ts_mem sp) = true) by (eapply taint_le_trans; eassumption);
             split; [auto|]; split; [reflexivity|];
             exists g, f, sp, tbl, true; split_tconfig;
             [ exists te_abs; split; [exact Hte_le | exact Htail]
             | apply mem_store_taint_admissible; assumption ]).
           (* Wp *)
           destruct wv2 as [|tva2 tvc2|]; try discriminate Etinst.
           destruct wv1 as [|tva1 tvc1|]; cbn [wt_le] in Hwvle; try discriminate.
           apply andb_prop in Hwvle; destruct Hwvle as [Htva Htvc].
           destruct (taint_le tva2 (ts_mem sp) && taint_le tvc2 (ts_aux sp)) eqn:Hv2; try discriminate Etinst.
           apply andb_prop in Hv2; destruct Hv2 as [Htva2 Htvc2].
           injection Etinst as <-.
           assert (Htva1 : taint_le tva1 (ts_mem sp) = true) by (eapply taint_le_trans; eassumption).
           assert (Htvc1 : taint_le tvc1 (ts_aux sp) = true) by (eapply taint_le_trans; eassumption).
           split; [auto|]. split; [reflexivity|].
           exists g, f, sp, tbl, true. split_tconfig.
           ++ exists te_abs. split; [exact Hte_le | exact Htail].
           ++ apply paux_store_admissible; [exact Htvc1|].
              apply mem_store_taint_admissible; assumption.
        -- destruct w;
             try (destruct wv2 as [tv2| |]; try discriminate Etinst;
                  destruct wv1 as [tv1| |]; cbn [wt_le] in Hwvle; try discriminate;
                  split; [exact Hshape | exact Hshape]);
             try (destruct wv2 as [|tva2 tvc2|]; try discriminate Etinst;
                  destruct wv1 as [|tva1 tvc1|]; cbn [wt_le] in Hwvle; try discriminate;
                  split; [exact Hshape | exact Hshape]).
        -- exfalso. unfold step, inst_step in Est; cbn in Est.
           rewrite Evk in Est.
           destruct (value_x ge e vk v) as [xv|]; [|discriminate Est].
           rewrite Hp in Est.
           destruct (store_res w m (raw_address (ptr_addr p) off) (ptr_cap p) xv) as [[r0 m0]|]; [|discriminate Est].
           unfold store_out, raw_res in Est; destruct r0; discriminate Est.
      * (* RawStorePointer *)
        cbn [tinst] in Etinst.
        destruct (ts_writes sp) eqn:Ewr; [|discriminate Etinst].
        assert (Ewm : wr_mem = true) by (destruct wr_mem; [reflexivity | discriminate]).
        subst wr_mem. rewrite <- Ewr in Hwr_mem.
        cbn [negb] in Etinst.
        destruct (effects_eqb es [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]
                  || effects_eqb es [LowerWrite; AddressWrite]
                  || effects_eqb es [AtomicWrite]) eqn:Eeff; [|discriminate Etinst].
        destruct (value_t te_abs A av) as [wa2|] eqn:Ea2; [|discriminate Etinst].
        destruct wa2 as [|ta2 tca2|]; try discriminate Etinst.
        destruct (value_t te_abs P v) as [wv2|] eqn:Ev2; [|discriminate Etinst].
        destruct wv2 as [|tva2 tvc2|]; try discriminate Etinst.
        destruct (t_index ta2 || t_index tca2) eqn:Ei2; try discriminate Etinst.
        destruct (pol_check_branches pol && (t_branch ta2 || t_branch tca2)) eqn:Eb2; try discriminate Etinst.
        destruct (taint_le tva2 (ts_mem sp) && taint_le tvc2 (ts_aux sp)) eqn:Hv2; try discriminate Etinst.
        injection Etinst as <-.
        apply orb_false_iff in Ei2; destruct Ei2 as [Eia2 Eica2].
        apply andb_prop in Hv2; destruct Hv2 as [Htva2 Htvc2].
        destruct (value_t_mono te te_abs A av _ Hte_le Ea2) as (wa1 & Ea1 & Hwale).
        destruct (value_t_mono te te_abs P v _ Hte_le Ev2) as (wv1 & Ev1 & Hwvle).
        destruct wa1 as [|ta1 tca1|]; cbn [wt_le] in Hwale; try discriminate.
        destruct wv1 as [|tva1 tvc1|]; cbn [wt_le] in Hwvle; try discriminate.
        apply andb_prop in Hwale; destruct Hwale as [Hta Htca].
        apply andb_prop in Hwvle; destruct Hwvle as [Htva Htvc].
        pose proof (plain_store_ptr_addr_ok ge f e ls l off v av es rest j cs m fuel Hnf) as [p Hp].
        assert (Eb1 : pol_check_branches pol && (t_branch ta1 || t_branch tca1) = false).
        { destruct (pol_check_branches pol); cbn in Eb2 |- *; [|reflexivity].
          apply orb_false_iff in Eb2; destruct Eb2 as [Eba2 Ebca2].
          rewrite (taint_le_branch _ _ Hta Eba2), (taint_le_branch _ _ Htca Ebca2). reflexivity. }
        unfold pfails, pstep, tstep, inst_tstep.
        cbn [c_frame fr_doomed fr_at fr_env ps_tenv ps_callers ps_mem ps_aux].
        rewrite Eeff, Hp, Ea1, Ev1, (taint_le_index _ _ Hta Eia2), (taint_le_index _ _ Htca Eica2), Eb1.
        rewrite (mem_no_store_admissible _ _ _ _ _ _ Hpm).
        destruct (step ge (mkConfig (mkFrame f e ls None (Exec l (RawStorePointer off v av es :: rest) j)) cs m fuel))
          as [c' | o' | q k0 | why] eqn:Est; try contradiction.
        -- destruct Hshape as (e' & ls' & m' & ->).
           split; [auto|]. split; [reflexivity|].
           exists g, f, sp, tbl, true. split_tconfig.
           ++ exists te_abs. split; [exact Hte_le | exact Htail].
           ++ apply paux_store_admissible; [eapply taint_le_trans; eassumption|].
              apply mem_store_taint_admissible; [eapply taint_le_trans; eassumption | exact Hpm].
        -- split; [exact Hshape | exact Hshape].
        -- exfalso; unfold step, inst_step in Est;
             cbn [c_frame c_mem c_callers c_fuel fr_at fr_doomed fr_env fr_locals] in Est;
             cbv zeta in Est;
             destruct (value_x ge e P v) as [[|vp|]|]; try discriminate Est; rewrite Hp in Est;
             destruct (access_res m (raw_address (ptr_addr p) off) (ptr_cap p) 8 Write 8) as [[[]| |]|]; try discriminate Est;
             destruct (pointer_store_effects (raw_address (ptr_addr p) off) vp m es); discriminate Est.
      * (* Call *)
        destruct callee as [? | ? | g_cal]; try discriminate Etinst.
        cbn [tinst] in Etinst.
        destruct (map_option (arg_t te_abs) args) as [wts2|] eqn:Eargs2; [|discriminate Etinst].
        destruct (map_arg_t_mono te te_abs args wts2 Hte_le Eargs2) as (wts1 & Eargs1 & Hwtsle).
        destruct (lookup g_cal entries) as [sp_g|] eqn:Elkg.
        -- (* Direct call to verified function in entries *)
           destruct (taint_eqb (ts_mem sp_g) (ts_mem sp)
                     && taint_eqb (ts_aux sp_g) (ts_aux sp)
                     && implb (ts_writes sp_g) (ts_writes sp)
                     && wts_le wts2 (ts_args sp_g)) eqn:Echk; [|discriminate Etinst].
           apply andb_prop in Echk; destruct Echk as [Echk Hwarg2].
           apply andb_prop in Echk; destruct Echk as [Echk Hwrg].
           apply andb_prop in Echk; destruct Echk as [Hmem_eq Haux_eq].
           apply taint_eqb_eq in Hmem_eq; apply taint_eqb_eq in Haux_eq.
           destruct (taint_check_program_entry pol ge entries g_cal sp_g Hprog Elkg)
             as (gf & tbl_g & Hvt_g).
           pose proof Hvt_g as (Hlkg & Hfg & Hver_g).
           destruct (taint_verify_entry _ _ _ _ _ _ Hver_g)
             as (Hnv_g & ent_g & b_ent_g & te_init_g & te_ent_g &
                 Hent_g & Hbent_g & Hphis_g & Hct_g & Htbl_g & Hle_init_g & _).
           pose proof (wts_le_Forall2 _ _ Hwarg2) as Hfa2.
           assert (Hfa1 : Forall2 (fun a b => wt_le a b = true) wts1 (ts_args sp_g)).
           { clear -Hwtsle Hfa2. revert Hfa2. generalize (ts_args sp_g).
             induction Hwtsle; intros ys Hfa2; inversion Hfa2; subst; constructor; [eapply wt_le_trans; eassumption | auto]. }
           destruct (call_tenv_mono gf wts1 (ts_args sp_g) te_init_g Hfa1 Hct_g) as (cte & Hcte & Hle_cte).
           unfold pfails, pstep, tstep, inst_tstep.
           cbn [c_frame fr_doomed fr_at fr_env ps_tenv ps_callers ps_mem ps_aux].
           rewrite Eargs1, Hfg, Hnv_g, Hcte.
           destruct (step ge (mkConfig (mkFrame f e ls None (Exec l (Call r (Global g_cal) args :: rest) j)) cs m fuel))
             as [c' | o' | q k0 | why] eqn:Est; try contradiction.
           ++ destruct Hshape as [(gf' & xs & callee & Hfg' & Hcf & ->) | [Hnone _]].
              ** rewrite Hfg in Hfg'. injection Hfg' as <-.
                 destruct (call_frame_nonvariadic_entry gf xs callee ent_g Hnv_g Hent_g Hcf)
                   as (Hfn_cal & Hdoom_cal & Hat_cal).
                 split; [auto|]. split; [reflexivity|].
                 exists g_cal, gf, sp_g, tbl_g, wr_mem. split_tconfig.
                 --- rewrite Hat_cal. exists b_ent_g, te_ent_g. repeat split; try assumption.
                     exists cte. split; [unfold phis_tenv; rewrite Hphis_g; reflexivity | eapply tenv_le_prop_trans; eassumption].
                 --- destruct (ts_writes sp_g), (ts_writes sp), wr_mem; cbn in Hwrg, Hwr_mem |- *; try discriminate; reflexivity.
                 --- rewrite Hmem_eq, Haux_eq. exact Hpm.
                 --- eapply tstack_cons with (g := g) (f := f) (sp := sp) (tbl := tbl) (l := l) (rest := rest) (j := j);
                       cbn [fr_fn fr_doomed fr_at pd_res]; try reflexivity; try assumption.
                     intros ots Hots.
                     assert (Hots_le : Forall2 (fun a b => wt_le a b = true) ots
                               (match ts_ret sp_g with Some wt => [wt] | None => [] end)).
                     { destruct (ts_ret sp_g) as [wout|].
                       - destruct Hots as (wt & -> & Hw). constructor; [exact Hw | constructor].
                       - subst ots. constructor. }
                     destruct (returned_tenv_mono r ots _ te te_abs te_abs' Hots_le Hte_le Etinst)
                       as (te_r & Hrt & Hler).
                     exists te_r, te_abs'. repeat split; assumption.
              ** rewrite Hfg in Hnone; discriminate.
           ++ split; [exact Hshape | exact Hshape].
           ++ exfalso; unfold step, inst_step in Est; cbn in Est.
              destruct (map_option (arg_x ge e) args); [|discriminate Est].
              rewrite Hfg in Est. cbn in Est.
              destruct (call_frame gf l0); discriminate Est.
        -- (* External call to free *)
           rewrite find_fn_mod in Etinst.
           destruct (find_fn ge g_cal) as [[gf|go]|] eqn:Hfg; try discriminate Etinst.
           destruct (is_free_name g_cal) eqn:Hfrn; [|discriminate Etinst].
           unfold pfails, pstep, tstep, inst_tstep.
           cbn [c_frame fr_doomed fr_at fr_env ps_tenv ps_callers ps_mem ps_aux].
           rewrite Eargs1, Hfg.
           assert (Hng : lookup g_cal (ge_globals ge) = None).
           { unfold fails, step, inst_step in Hnf. cbn in Hnf.
             destruct (map_option (arg_x ge e) args); [|exfalso; apply Hnf; exact I].
             rewrite Hfg in Hnf. unfold external_call in Hnf.
             destruct (lookup g_cal (ge_globals ge));
               [exfalso; apply Hnf; cbn [or_stuck fst snd inst_next]; unfold failure, refusal; intros [? | ?]; discriminate | reflexivity]. }
           rewrite Hng, Hfrn.
           destruct r; try discriminate Etinst.
           destruct args as [|[ka va] []]; try discriminate Etinst.
           destruct ka; try discriminate Etinst.
           destruct wts2 as [|w2 []]; try discriminate Etinst.
           inversion Hwtsle as [|w1 w2' l1 l2 Hw12 Hnil]; subst. inversion Hnil; subst.
           destruct w2 as [ta2 | ta2 tc2 |]; try discriminate Etinst.
           ++ destruct (t_branch ta2) eqn:Eb2; [discriminate Etinst|].
              injection Etinst as <-.
              destruct w1 as [ta1 | |]; cbn [wt_le] in Hw12; try discriminate.
              rewrite (taint_le_branch _ _ Hw12 Eb2).
              destruct (step ge (mkConfig (mkFrame f e ls None (Exec l (Call CVoid (Global g_cal) [Arg P va] :: rest) j)) cs m fuel))
                as [c' | o' | q k0 | why] eqn:Est; try contradiction.
              ** destruct Hshape as [(gf' & _ & _ & Hdef & _) | (_ & e' & ls' & m' & ->)]; [discriminate Hdef|].
                 split; [auto|]. split; [reflexivity|].
                 exists g, f, sp, tbl, wr_mem. split_tconfig.
                 exists te_abs. split; [exact Hte_le | exact Htail].
              ** split; [exact Hshape | exact Hshape].
              ** exfalso; unfold step, inst_step in Est; cbn in Est.
                 destruct (value_x ge e P va) as [w|]; [|discriminate Est].
                 rewrite Hfg in Est. unfold external_call in Est. rewrite Hng, Hfrn in Est.
                 destruct (ge_free ge w m); [|discriminate Est]. destruct p as [r0 m0]; destruct r0; discriminate Est.
           ++ destruct (t_branch ta2 || t_branch tc2 || t_index tc2) eqn:Eb2; [discriminate Etinst|].
              injection Etinst as <-.
              apply orb_false_iff in Eb2; destruct Eb2 as [Eb2' Eic2]; apply orb_false_iff in Eb2'; destruct Eb2' as [Eba2 Ebc2].
              destruct w1 as [|ta1 tc1|]; cbn [wt_le] in Hw12; try discriminate.
              apply andb_prop in Hw12; destruct Hw12 as [Hta Htc].
              rewrite (taint_le_branch _ _ Hta Eba2), (taint_le_branch _ _ Htc Ebc2), (taint_le_index _ _ Htc Eic2).
              destruct (step ge (mkConfig (mkFrame f e ls None (Exec l (Call CVoid (Global g_cal) [Arg P va] :: rest) j)) cs m fuel))
                as [c' | o' | q k0 | why] eqn:Est; try contradiction.
              ** destruct Hshape as [(gf' & _ & _ & Hdef & _) | (_ & e' & ls' & m' & ->)]; [discriminate Hdef|].
                 split; [auto|]. split; [reflexivity|].
                 exists g, f, sp, tbl, wr_mem. split_tconfig.
                 exists te_abs. split; [exact Hte_le | exact Htail].
              ** split; [exact Hshape | exact Hshape].
              ** exfalso; unfold step, inst_step in Est; cbn in Est.
                 destruct (value_x ge e P va) as [w|]; [|discriminate Est].
                 rewrite Hfg in Est. unfold external_call in Est. rewrite Hng, Hfrn in Est.
                 destruct (ge_free ge w m); [|discriminate Est]. destruct p as [r0 m0]; destruct r0; discriminate Est.
           ++ destruct w2; discriminate Etinst.
           ++ destruct ka; discriminate Etinst.
      * (* RawCall *) discriminate Etinst.
      * (* LocalAlloc *)
        injection Etinst as <-.
        unfold pfails, pstep, tstep, inst_tstep.
        cbn [c_frame fr_doomed fr_at fr_env ps_tenv ps_callers ps_mem ps_aux].
        destruct (step ge (mkConfig (mkFrame f e ls None (Exec l (LocalAlloc lx size :: rest) j)) cs m fuel))
          as [c' | o' | q k0 | why] eqn:Est; try contradiction.
        -- exfalso; unfold step, inst_step in Est; cbn in Est;
             destruct (lookup lx ls) as [[|]|]; discriminate Est.
        -- split; [exact Hshape | exact Hshape].
        -- destruct Hshape as [Hext Hk].
           split; [lia|].
           exists k0. split; [reflexivity | split; [exact Hext |]].
           intros base. cbn [fst snd]. split; [reflexivity|].
           destruct (Hk base) as (e' & ls' & m' & ->).
           exists g, f, sp, tbl, wr_mem. split_tconfig.
           ++ exists te_abs. split; [exact Hte_le | exact Htail].
           ++ apply unpoison_admissible; exact Hpm.
      * (* Loc *)
        injection Etinst as <-.
        unfold pfails, pstep, tstep, inst_tstep.
        cbn [c_frame fr_doomed fr_at fr_env ps_tenv ps_callers ps_mem ps_aux].
        destruct (step ge (mkConfig (mkFrame f e ls None (Exec l (Loc lfile lline :: rest) j)) cs m fuel))
          as [c' | o' | q k0 | why] eqn:Est; try contradiction.
        -- destruct Hshape as (e' & ls' & m' & ->).
           split; [auto|]. split; [reflexivity|].
           exists g, f, sp, tbl, wr_mem. split_tconfig.
           exists te_abs. split; [exact Hte_le | exact Htail].
        -- split; [exact Hshape | exact Hshape].
        -- exfalso; unfold step, inst_step in Est; cbn in Est; discriminate Est.
      * (* Touch *)
        injection Etinst as <-.
        unfold pfails, pstep, tstep, inst_tstep.
        cbn [c_frame fr_doomed fr_at fr_env ps_tenv ps_callers ps_mem ps_aux].
        destruct (step ge (mkConfig (mkFrame f e ls None (Exec l (Touch tq :: rest) j)) cs m fuel))
          as [c' | o' | q k0 | why] eqn:Est; try contradiction.
        -- destruct Hshape as (e' & ls' & m' & ->).
           split; [auto|]. split; [reflexivity|].
           exists g, f, sp, tbl, wr_mem. split_tconfig.
           exists te_abs. split; [exact Hte_le | exact Htail].
        -- split; [exact Hshape | exact Hshape].
        -- exfalso; unfold step, inst_step in Est; cbn in Est; discriminate Est.
Qed.

(** Factoring theorem: any plain memory-safety proof [plain_safe] combined
    with a passing reflective [taint_check_program] yields full [poison_safe]
    across all reachable machine states and finite driver runs. *)
Theorem taint_check_poison_safe pol ge entries g f sp fr te m pm paux s fuel :
  taint_check_program pol (ge_module ge) entries = true ->
  lookup g entries = Some sp ->
  find_fn ge g = Some (Defined f) ->
  fr_fn fr = f ->
  fr_doomed fr = None ->
  (exists entry, fn_entry f = Some entry /\ fr_at fr = Enter entry None) ->
  (exists te_call, call_tenv f (ts_args sp) = Some te_call /\ tenv_le te te_call = true) ->
  pm_admissible (ts_mem sp) (ts_aux sp) (ts_writes sp) pm paux ->
  plain_safe ge fr m s fuel ->
  poison_safe pol ge fr te m pm paux s fuel.
Proof.
  intros Hprog Hlk Hfg Hfn Hdoom (entry & Hent & Hat) (te_call & Hct & Hle) Hpm Hplain.
  destruct (taint_check_program_entry pol ge entries g sp Hprog Hlk) as (f' & tbl & Hvt).
  pose proof Hvt as (Hlk' & Hfg' & Hver).
  rewrite Hfg in Hfg'. injection Hfg' as <-.
  destruct (taint_verify_entry _ _ _ _ _ _ Hver)
    as (Hnv & ent' & b_ent & te_init & te_ent & Hent' & Hbent & Hphis & Hct' & Htbl & Hle_init & _).
  rewrite Hent in Hent'. injection Hent' as <-.
  rewrite Hct in Hct'. injection Hct' as <-.
  assert (Hok0 : tconfig_ok pol ge entries (mkConfig fr [] m fuel) (mkPState te [] pm paux)).
  { exists g, f, sp, tbl, (ts_writes sp). split_tconfig.
    - rewrite Hat. exists b_ent, te_ent. repeat split; try assumption.
      exists te. split; [unfold phis_tenv; rewrite Hphis; reflexivity|].
      eapply tenv_le_prop_trans; [apply tenv_le_sound; exact Hle | exact Hle_init].
    - destruct (ts_writes sp); reflexivity.
    - constructor. }
  repeat split.
  - (* Conjunct 1: pmreachable -> ~ pfails *)
    intros c ps s' Hreach.
    assert (Hstep_gen : forall stX stY,
      pmreachable pol ge stX stY ->
      RM.mreachable ge (mkConfig fr [] m fuel, s) (fst (fst stX), snd stX) /\
      tconfig_ok pol ge entries (fst (fst stX)) (snd (fst stX)) ->
      RM.mreachable ge (mkConfig fr [] m fuel, s) (fst (fst stY), snd stY) /\
      tconfig_ok pol ge entries (fst (fst stY)) (snd (fst stY))).
    { clear -Hprog Hplain. intros stX stY Hr.
      induction Hr as [a b Hst | a | a b d _ IHa _ IHd]; intros [Hra Hoka].
      - destruct Hst as [c0 ps0 s0 c' ps' Hp | c0 ps0 s0 q k base s1 Hp Hext Hal | c0 ps0 s0 s1 m1 Hdue Hsp];
          cbn [fst snd] in Hra, Hoka |- *.
        + destruct (tconfig_step_ok pol ge entries c0 ps0 Hprog Hoka (Hplain _ Hra)) as [_ Hs].
          rewrite Hp in Hs. destruct Hs as [Hst Hok'].
          split; [eapply rt_trans; [exact Hra | apply rt_step; apply RM.mstep_next; exact Hst] | exact Hok'].
        + destruct (tconfig_step_ok pol ge entries c0 ps0 Hprog Hoka (Hplain _ Hra)) as [_ Hs].
          rewrite Hp in Hs. destruct Hs as (k0 & Hst & _ & Hk).
          destruct (Hk base) as [Hfst Hok'].
          split; [eapply rt_trans; [exact Hra | apply rt_step; rewrite Hfst; eapply RM.mstep_alloc; eassumption] | exact Hok'].
        + split; [eapply rt_trans; [exact Hra | apply rt_step; eapply RM.mstep_safepoint; eassumption]|].
          destruct Hoka as (g0 & f0 & sp0 & tbl0 & wr0 & H1 & H2 & H3 & H4 & H5).
          exists g0, f0, sp0, tbl0, wr0. split; [exact H1 | split; [exact H2 | split; [exact H3 | split; [exact H4 | exact H5]]]].
      - split; assumption.
      - apply IHd, IHa. split; assumption. }
    destruct (Hstep_gen _ _ Hreach (conj (rt_refl _ _ _) Hok0)) as [Hr Hc].
    exact (proj1 (tconfig_step_ok pol ge entries c ps Hprog Hc (Hplain _ Hr))).
  - (* Conjunct 2: plain mreachable -> ~ fails *)
    exact Hplain.
  - (* Conjunct 3: finite pdriver_run *)
    intros steps.
    assert (Hdrv : forall n c ps rt,
      RM.mreachable ge (mkConfig fr [] m fuel, s) (c, rt) ->
      tconfig_ok pol ge entries c ps ->
      match PD.pdriver_run pol ge n c ps rt with
      | PD.PDriverNext _ _ _ => True
      | PD.PDriverDone o _ => ~ failure o
      | PD.PDriverTrap _ | PD.PDriverBad _ => False
      end).
    { induction n as [|n IH]; intros c ps rt Hr Hc; [exact I|].
      cbn [PD.pdriver_run].
      destruct (tconfig_step_ok pol ge entries c ps Hprog Hc (Hplain _ Hr)) as [_ Hs].
      destruct (pstep pol ge c ps) as [c' ps' | o ots | q k | why | why]; try contradiction.
      - destruct Hs as [Hst Hc'].
        apply IH; [eapply rt_trans; [exact Hr | apply rt_step; apply RM.mstep_next; exact Hst] | exact Hc'].
      - exact Hs.
      - destruct Hs as (k0 & Hst & Hext & Hk).
        replace (req_extent q <? 0) with false by (symmetry; apply Z.ltb_ge; exact Hext).
        destruct (R.alloc rt q) as [[base rt']|] eqn:Hal.
        + destruct (k base) as [c' ps'] eqn:Ekb.
          destruct (Hk base) as [Hfst Hc']. rewrite Ekb in Hfst, Hc'. cbn [fst snd] in Hfst, Hc'.
          apply IH; [eapply rt_trans; [exact Hr | apply rt_step; rewrite Hfst; eapply RM.mstep_alloc; eassumption] | exact Hc'].
        + unfold failure, refusal. intros Href. apply Href. left. reflexivity. }
    exact (Hdrv steps (mkConfig fr [] m fuel) (mkPState te [] pm paux) s (rt_refl _ _ _) Hok0).
Qed.

(** Direct constant-time corollary: plain safety plus [taint_check_program]
    yields identical plain operational leakage traces for every pair of
    secret-related executions. *)
Theorem taint_check_constant_time pol ge entries g f sp fr1 fr2 te m1 m2 pm paux s fuel :
  pol_check_branches pol = true ->
  ge_free ge = free_res ->
  taint_check_program pol (ge_module ge) entries = true ->
  lookup g entries = Some sp ->
  find_fn ge g = Some (Defined f) ->
  fr_fn fr1 = f ->
  fr_doomed fr1 = None ->
  (exists entry, fn_entry f = Some entry /\ fr_at fr1 = Enter entry None) ->
  (exists te_call, call_tenv f (ts_args sp) = Some te_call /\ tenv_le te te_call = true) ->
  pm_admissible (ts_mem sp) (ts_aux sp) (ts_writes sp) pm paux ->
  R.ready s m1 -> R.ready s m2 ->
  ct_rel (mkConfig fr1 [] m1 fuel) (mkConfig fr2 [] m2 fuel) (mkPState te [] pm paux) ->
  plain_safe ge fr1 m1 s fuel ->
  forall steps, exists tr,
    PD.driver_trace pol ge steps (mkConfig fr1 [] m1 fuel) s = Some tr /\
    PD.driver_trace pol ge steps (mkConfig fr2 [] m2 fuel) s = Some tr.
Proof.
  intros Hcb Hfree Hprog Hlk Hfg Hfn Hdoom Hent Hte Hpm Hr1 Hr2 Hrel Hplain steps.
  eapply (wp_ct_driver_plain pol ge fr1 fr2 te m1 m2 pm paux s fuel);
    try assumption.
  eapply (taint_check_poison_safe pol ge entries g f sp); eassumption.
Qed.

(** Region-invariant multi-step safety predicate for non-allocating functions.
    Starting from configuration [c], stepping either finishes with a non-failing
    outcome, re-enters the invariant [I], or continues safely under any
    region-preserving garbage-collector safepoint. *)
Inductive block_safe (ge : genv) (I : config -> Prop) : config -> Prop :=
| bs_done c o :
    step ge c = Done o ->
    ~ failure o ->
    block_safe ge I c
| bs_inv c c' :
    step ge c = Next c' ->
    I c' ->
    block_safe ge I c
| bs_step c c' :
    step ge c = Next c' ->
    (forall m', m_regions m' = m_regions (c_mem c') -> block_safe ge I (RM.with_mem c' m')) ->
    block_safe ge I c.

(** Updating a configuration's memory to its current memory is a no-op. *)
Lemma with_mem_self c : RM.with_mem c (c_mem c) = c.
Proof. destruct c; reflexivity. Qed.

(** Repeated [RM.with_mem] keeps the latest memory state. *)
Lemma with_mem_with_mem c m1 m2 : RM.with_mem (RM.with_mem c m1) m2 = RM.with_mem c m2.
Proof. destruct c; reflexivity. Qed.

(** A region-invariant block invariant [I] whose states satisfy [block_safe]
    establishes [plain_safe] across all reachable machine states and arbitrary
    collector safepoints. *)
Theorem plain_safe_by_block_safe ge (I : config -> Prop) fr m s fuel :
  I (mkConfig fr [] m fuel) ->
  (forall c m', I c -> m_regions m' = m_regions (c_mem c) -> I (RM.with_mem c m')) ->
  (forall c, I c -> block_safe ge I c) ->
  plain_safe ge fr m s fuel.
Proof.
  intros HI0 HI_reg HI_step.
  set (P := fun c => forall m', m_regions m' = m_regions (c_mem c) -> block_safe ge I (RM.with_mem c m')).
  assert (HI_P : forall c, I c -> P c).
  { intros c Hc m' Hm'. apply HI_step. apply HI_reg; assumption. }
  assert (HP_step : forall st1 st2, RM.mstep ge st1 st2 -> P (fst st1) -> P (fst st2)).
  { intros [c1 s1] [c2 s2] Hst HP1. cbn [fst] in HP1 |- *.
    inversion Hst as [c0 c' s0 Hs | c0 q k s0 base s' Hs _ _ | c0 s0 s' m' _ Hsp]; subst.
    - pose proof (HP1 (c_mem c1) eq_refl) as Hbs. rewrite with_mem_self in Hbs.
      inversion Hbs as [c_ o Hs' _ | c_ c'' Hs' HI2 | c_ c'' Hs' HP2]; subst.
      + rewrite Hs in Hs'; discriminate.
      + rewrite Hs in Hs'; injection Hs' as <-. apply HI_P; exact HI2.
      + rewrite Hs in Hs'; injection Hs' as <-. exact HP2.
    - pose proof (HP1 (c_mem c1) eq_refl) as Hbs. rewrite with_mem_self in Hbs.
      inversion Hbs as [c_ o Hs' _ | c_ c'' Hs' _ | c_ c'' Hs' _]; subst; rewrite Hs in Hs'; discriminate.
    - intros m'' Hm''. rewrite with_mem_with_mem. apply HP1.
      cbn [c_mem RM.with_mem] in Hm''. rewrite Hm''.
      exact (R.collector_live _ _ _ _ Hsp). }
  assert (HP_reach : forall st1 st2, RM.mreachable ge st1 st2 -> P (fst st1) -> P (fst st2)).
  { intros st1 st2 Hreach. induction Hreach; eauto using HP_step. }
  intros [c' s'] Hreach.
  pose proof (HP_reach _ _ Hreach (HI_P _ HI0)) as HP'.
  cbn [fst] in HP' |- *.
  pose proof (HP' (c_mem c') eq_refl) as Hbs. rewrite with_mem_self in Hbs.
  inversion Hbs as [c_ o Hs Hnf | c_ c'' Hs _ | c_ c'' Hs _]; subst; unfold fails; rewrite Hs; [exact Hnf | auto | auto].
Qed.

End TaintCheckSound.
