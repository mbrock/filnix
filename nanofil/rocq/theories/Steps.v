(** What one step of Semantics.v's `step` does to the running frame,
    as Campaign 3's run-level invariant (Persistence.v) reads it.

    `step` is one function over every point of a frame; the invariant
    asks, point by point, what the frame looks like after it:

    | Point | Lemma |
    |---|---|
    | a variadic callee's snapshot | `step_snapshot`, `step_snapshot_fresh`: it enters the entry block, nothing else changes |
    | a block's entry | `step_enter`: the phis, then the block's instructions, with the same locals and memory |
    | an instruction | `step_exec_cons`: `inst_step`, `doomed_result/5`, then `inst_next` (`inst_next_next`, `inst_next_fresh`) |
    | a return | `return_step_next`: the caller resumes where it waited |

    An instruction that continues keeps the locals (`inst_step_locals`);
    only `alloc` and a named local allocate (`inst_step_fresh_shape`);
    only a call or raw call calls (`inst_step_call_shape`). A frame that
    is not doomed is doomed afterwards only by a `check_ahead`
    (`doomed_result_fresh`), and a doomed one stays doomed
    (`doomed_result_doomed`). *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Maps Syntax Cfg Values Memory Runtime Ops Semantics Machine Validate
  Coverage Evidence Walk.
Import ListNotations.
Open Scope Z_scope.

(** ## What a step does to the frame *)

Lemma find_direct_in : forall n items g, find_direct n items = Some (Defined g) -> In (IFunc g) items.
Proof.
  induction items as [|it items IH]; simpl; intros g H; [discriminate H|].
  destruct it; try (right; apply IH; exact H);
    match type of H with context [if name_eqb ?x n then _ else _] => destruct (name_eqb x n) end;
    try (right; apply IH; exact H); try discriminate H.
  injection H as <-. left. reflexivity.
Qed.

Lemma find_fn_in : forall ge n g, find_fn ge n = Some (Defined g) -> In (IFunc g) (ge_module ge).
Proof.
  unfold find_fn. intros ge n g H. destruct (find_direct n (ge_module ge)) eqn:E.
  - injection H as ->. eapply find_direct_in; eauto.
  - destruct (find_alias n (ge_module ge)); [eapply find_direct_in; eauto | discriminate H].
Qed.

(** An instruction that continues keeps the invocation's locals. *)
Lemma inst_step_locals : forall ge fr m i e l m',
  inst_step ge fr m i = Some (IContinue e l m') -> l = fr_locals fr.
Proof.
  intros ge fr m i e l m' H. destruct i.
  1: destruct (special_let o) eqn:Es;
       [destruct o; try discriminate Es | rewrite (inst_step_let _ _ _ _ _ _ _ Es) in H].
  all: unfold inst_step, external_call, bind_res, store_out in H; cases H; inversion H; subst;
    reflexivity.
Qed.

(** Only `alloc` and a named local's allocation allocate. *)
Lemma op_res_alloc_op : forall o k xs m q kont,
  op_res o k xs m = Some (OpAlloc q kont) -> exists al, o = Alloc al.
Proof.
  intros o k xs m q kont H.
  destruct o; unfold op_res, op_res_int, float_integer in H; cases H; inversion H; subst; eauto.
Qed.

Lemma inst_step_fresh_shape : forall ge fr m i q k,
  inst_step ge fr m i = Some (IFresh q k) ->
  (exists d c al args, i = Let d c (Alloc al) args /\
     forall base, snd (fst (k base)) = fr_locals fr) \/
  (exists x size, i = LocalAlloc x size /\
     forall base, snd (fst (k base)) = put x (Some base) (fr_locals fr)).
Proof.
  intros ge fr m i q k H. destruct i.
  1: destruct (special_let o) eqn:Es;
       [destruct o; try discriminate Es | rewrite (inst_step_let _ _ _ _ _ _ _ Es) in H].
  all: unfold inst_step, external_call, bind_res, store_out in H; cases H; inversion H; subst.
  - match goal with E : op_res _ _ _ _ = Some (OpAlloc _ _) |- _ =>
      destruct (op_res_alloc_op _ _ _ _ _ _ E) as [al ->] end.
    left. eexists; eexists; eexists; eexists. split; [reflexivity|]. intros base. simpl.
    match goal with |- snd (fst (let (_, _) := ?t in _)) = _ => destruct t end. reflexivity.
  - right. eexists; eexists. split; [reflexivity|]. intros base. reflexivity.
Qed.

(** A call comes only from a call instruction, of a function of the
    module. *)
Lemma inst_step_call_shape : forall ge fr m i g xs pd,
  inst_step ge fr m i = Some (ICall g xs pd) ->
  In (IFunc g) (ge_module ge) /\
  ((exists r callee args, i = Call r callee args) \/ (exists r callee args, i = RawCall r callee args)).
Proof.
  intros ge fr m i g xs pd H. destruct i.
  1: destruct (special_let o) eqn:Es;
       [destruct o; try discriminate Es | rewrite (inst_step_let _ _ _ _ _ _ _ Es) in H].
  all: unfold inst_step, external_call, bind_res, store_out in H; cases H; inversion H; subst.
  all: split; [eapply find_fn_in; eassumption | eauto].
Qed.

Lemma call_relies : forall s r callee args, relies s (Call r callee args) = false.
Proof. reflexivity. Qed.

Lemma raw_call_relies : forall s r callee args, relies s (RawCall r callee args) = false.
Proof. reflexivity. Qed.

Lemma alloc_relies : forall s d c al args, relies s (Let d c (Alloc al) args) = false.
Proof. intros s d c al args. destruct c; reflexivity. Qed.

Lemma local_alloc_relies : forall s x size, relies s (LocalAlloc x size) = false.
Proof. reflexivity. Qed.

Lemma transparent_relies : forall s i, ahead_transparent i = true -> relies s i = true.
Proof.
  unfold ahead_transparent, relies. intros s i H. apply andb_true_iff in H as [H _]. rewrite H. reflexivity.
Qed.

(** `doomed_result/5` in a frame that is not doomed: the instruction's
    result as it is, or a doomed `check_ahead` that goes on with its
    pointer. *)
Lemma doomed_result_fresh : forall ge fr m i out od,
  fr_doomed fr = None -> doomed_result ge fr m i out = Some od ->
  od = (out, None) \/ exists e w, od = (IContinue e (fr_locals fr) m, Some w).
Proof.
  intros ge fr m i out od Hd H. destruct (ahead_inst i) eqn:Ea.
  - destruct i as [d k o args | | | | | | |]; try discriminate Ea. destruct k; try discriminate Ea.
    destruct o; try discriminate Ea. destruct args as [|v [|v' args]]; try discriminate Ea.
    unfold doomed_result in H. rewrite Hd in H. cases H; inversion H; subst; eauto.
  - rewrite (doomed_result_other _ _ _ _ _ Ea) in H. rewrite Hd in H. cases H; inversion H; subst; auto.
Qed.

(** In a doomed frame it stays doomed. *)
Lemma doomed_result_doomed : forall ge fr m i out od,
  fr_doomed fr <> None -> doomed_result ge fr m i out = Some od ->
  snd od <> None /\ (fst od = out \/ (exists e, fst od = IContinue e (fr_locals fr) m) \/
                     exists o, fst od = IStop o).
Proof.
  intros ge fr m i out od Hd H. destruct (fr_doomed fr) as [w0|] eqn:Ew; [|congruence].
  destruct (ahead_inst i) eqn:Ea.
  - destruct i as [d k o args | | | | | | |]; try discriminate Ea. destruct k; try discriminate Ea.
    destruct o; try discriminate Ea. destruct args as [|v [|v' args]]; try discriminate Ea.
    unfold doomed_result in H. rewrite Ew in H. cases H; inversion H; subst; simpl;
      (split; [discriminate | eauto]).
  - rewrite (doomed_result_other _ _ _ _ _ Ea) in H. rewrite Ew in H.
    cases H; inversion H; subst; simpl; (split; [discriminate | eauto]).
Qed.

(** The step after an instruction's result that is not an outcome. *)
Lemma inst_next_next : forall c l rest j out d c',
  inst_next c l rest j out d = Next c' ->
  (exists e1 l1 m1, out = IContinue e1 l1 m1 /\
     c' = mkConfig (mkFrame (fr_fn (c_frame c)) e1 l1 d (Exec l rest j)) (c_callers c) m1 (c_fuel c)) \/
  (exists g xs pd callee, out = ICall g xs pd /\ call_frame g xs = Some callee /\
     c' = mkConfig callee ((mkFrame (fr_fn (c_frame c)) (fr_env (c_frame c)) (fr_locals (c_frame c)) d
                                    (Exec l rest j), pd) :: c_callers c) (c_mem c) (c_fuel c)).
Proof.
  unfold inst_next. intros c l rest j out d c' H.
  destruct out; try discriminate H.
  - injection H as <-. left. eauto.
  - destruct (call_frame f xs) eqn:E; [|discriminate H]. injection H as <-. right. eauto 7.
Qed.

Lemma inst_next_fresh : forall c l rest j out d q k,
  inst_next c l rest j out d = Fresh q k ->
  exists k0, out = IFresh q k0 /\
    forall base, k base = match k0 base with
                          | (e, locals, m') =>
                              mkConfig (mkFrame (fr_fn (c_frame c)) e locals d (Exec l rest j))
                                       (c_callers c) m' (c_fuel c)
                          end.
Proof.
  unfold inst_next. intros c l rest j out d q k H.
  destruct out; try discriminate H;
    [match type of H with context [call_frame ?g ?x] => destruct (call_frame g x) end; discriminate H|].
  injection H as <- <-. eexists. split; [reflexivity|]. intros base. reflexivity.
Qed.

(** A step at an instruction: the instruction, `doomed_result/5`, then
    `inst_next`. *)
Lemma step_exec_cons : forall ge c l i rest j r,
  fr_at (c_frame c) = Exec l (i :: rest) j ->
  step ge c = r -> (forall o, r <> Done o) -> (forall why, r <> Stuck why) ->
  (fr_doomed (c_frame c) = None \/ ahead_transparent i = true) /\
  exists out0 od, inst_step ge (c_frame c) (c_mem c) i = Some out0 /\
    doomed_result ge (c_frame c) (c_mem c) i out0 = Some od /\
    inst_next c l rest j (fst od) (snd od) = r.
Proof.
  intros ge c l i rest j r Ha Hs Hd Hst. unfold step in Hs. rewrite Ha in Hs.
  destruct (fr_doomed (c_frame c)) as [w|] eqn:Ew.
  - destruct (ahead_transparent i) eqn:Et; [|subst r; exfalso; eapply Hd; reflexivity].
    split; [right; reflexivity|].
    destruct (inst_step ge (c_frame c) (c_mem c) i) as [out0|] eqn:Ei;
      [|subst r; exfalso; eapply Hst; reflexivity].
    destruct (doomed_result ge (c_frame c) (c_mem c) i out0) as [od|] eqn:Eo;
      [|subst r; exfalso; eapply Hst; reflexivity].
    exists out0, od. split; [first [exact Ei | reflexivity] | split; [first [exact Eo | reflexivity] | exact Hs]].
  - split; [left; reflexivity|].
    destruct (inst_step ge (c_frame c) (c_mem c) i) as [out0|] eqn:Ei;
      [|subst r; exfalso; eapply Hst; reflexivity].
    destruct (doomed_result ge (c_frame c) (c_mem c) i out0) as [od|] eqn:Eo;
      [|subst r; exfalso; eapply Hst; reflexivity].
    exists out0, od. split; [first [exact Ei | reflexivity] | split; [first [exact Eo | reflexivity] | exact Hs]].
Qed.

(** Entering a block: its phis, then its instructions. *)
Lemma step_enter : forall ge c l from c',
  fr_at (c_frame c) = Enter l from -> step ge c = Next c' ->
  exists b e, find_block l (fn_blocks (fr_fn (c_frame c))) = Some b /\
    phis_env ge (b_phis b) from (fr_env (c_frame c)) = Some e /\
    c' = mkConfig (mkFrame (fr_fn (c_frame c)) e (fr_locals (c_frame c)) (fr_doomed (c_frame c))
                           (Exec l (b_insts b) (b_jump b)))
                  (c_callers c) (c_mem c) (c_fuel c - 1).
Proof.
  intros ge c l from c' Ha H. unfold step in H. rewrite Ha in H.
  destruct (c_fuel c =? 0); [discriminate H|]. apply or_stuck_next in H.
  destruct (find_block _ _) as [b|]; [|discriminate H].
  destruct (phis_env ge (b_phis b) from (fr_env (c_frame c))) as [e|] eqn:Ep; [|discriminate H].
  injection H as <-. eauto.
Qed.

Lemma step_enter_fresh : forall ge c l from q k,
  fr_at (c_frame c) = Enter l from -> step ge c <> Fresh q k.
Proof.
  intros ge c l from q k Ha H. unfold step in H. rewrite Ha in H.
  destruct (c_fuel c =? 0); [discriminate H|]. apply or_stuck_fresh in H.
  destruct (find_block _ _) as [b|]; simpl in H; [|discriminate H].
  unfold phis_env in H. destruct from; [|destruct (b_phis b)]; simpl in H; try discriminate H.
  destruct (fold_left _ _ _); discriminate H.
Qed.

(** A variadic callee's snapshot enters the entry block. *)
Lemma step_snapshot : forall ge c xs l c',
  fr_at (c_frame c) = Snapshot xs l -> step ge c = Next c' ->
  c_callers c' = c_callers c /\ fr_fn (c_frame c') = fr_fn (c_frame c) /\
  fr_locals (c_frame c') = fr_locals (c_frame c) /\ fr_doomed (c_frame c') = fr_doomed (c_frame c) /\
  fr_at (c_frame c') = Enter l None.
Proof.
  intros ge c xs l c' Ha H. unfold step in H. rewrite Ha in H.
  destruct xs; [injection H as <-; simpl; auto|].
  destruct (negb _); discriminate H.
Qed.

Lemma step_snapshot_fresh : forall ge c xs l q k,
  fr_at (c_frame c) = Snapshot xs l -> step ge c = Fresh q k ->
  forall base,
    c_callers (k base) = c_callers c /\ fr_fn (c_frame (k base)) = fr_fn (c_frame c) /\
    fr_locals (c_frame (k base)) = fr_locals (c_frame c) /\
    fr_doomed (c_frame (k base)) = fr_doomed (c_frame c) /\ fr_at (c_frame (k base)) = Enter l None.
Proof.
  intros ge c xs l q k Ha H base. unfold step in H. rewrite Ha in H.
  destruct xs; [discriminate H|]. destruct (negb _); [discriminate H|].
  injection H as _ <-. simpl. auto.
Qed.

(** A return resumes the caller where it was, with the callee's result. *)
Lemma return_step_next : forall c o c',
  return_step c o = Next c' ->
  exists caller pd callers e m',
    c_callers c = (caller, pd) :: callers /\
    c' = mkConfig (mkFrame (fr_fn caller) e (fr_locals caller) (fr_doomed caller) (fr_at caller))
                  callers m' (c_fuel c).
Proof.
  unfold return_step. intros c o c' H. apply or_stuck_next in H.
  destruct (invalidate_locals _ _) as [m|]; [|discriminate H].
  destruct (c_callers c) as [|[caller pd] callers]; [discriminate H|].
  destruct (match pd_conv pd with None => Some o | Some (cw, kw) => converted_outcome cw kw o end);
    [|discriminate H].
  destruct (returned_env _ _ _) as [e|]; [|discriminate H]. injection H as <-. eauto 8.
Qed.

(** A raw call whose function check passed is not unchecked. *)
Lemma raw_call_checked : forall ge fr m r q args p why,
  lookup q (fr_env fr) = Some (WPtr p) -> function_check_res ge p = Some ok ->
  inst_step ge fr m (RawCall r (Tmp q) args) <> Some (IStop (Unchecked why)).
Proof.
  intros ge fr m r q args p why Hq Hc H. unfold inst_step, value_x in H. rewrite Hq in H.
  cbn [word_at_class] in H. destruct (map_option _ args); [|discriminate H]. cbv beta iota zeta in H.
  rewrite Hc in H. cbn [raw_res] in H. cases H.
Qed.
