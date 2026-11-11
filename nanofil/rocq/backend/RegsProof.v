(** # Soundness proofs for Regs.v: validator, parallel moves and frame layout

    Kernel-checked proofs for the executable allocation validator
    ([valid_alloc]), parallel-move compiler ([compile_pmoves]), concrete
    frame/save/root separation ([build_rctx]), interval primitives and
    3-address immediate selection in Regs.v (M7 of
    docs/gallina-backend.md):

    1. **Interval and ordset primitives** ([hreg_eqb_spec],
       [ivals_disjoint_sound], [ivals_hit_points_sound],
       [ivals_union_sound], [nset_union_spec], [nset_sub_spec],
       [nset_of_list_spec]): under [ivals_wf], [pts_wf] and [nset_wf],
       the sorted interval tests and [nat] ordset operations agree with
       set membership.
    2. **Validator forward simulation over multi-block CFGs**
       ([valid_alloc_sound], [valid_alloc_classes_eligible],
       [check_rblocks_trace_sound], [rblock_liveness_sound],
       [check_rinsts_rev_sound], [check_rinst_multi_sound],
       [eblocks_to_r_wf]): [state_agrees] relates live temporaries to
       hardware registers and shared physical frame slots (`Z -> Z`
       indexed by `slot_of`, allowing expired spill-slot reuse as in
       [ex_shared_spill_slot] and [ex_valid_alloc_loop]). Whenever
       [valid_alloc] accepts `(cmap, param_tids, rbs, rm)` on a
       well-formed [rblock] CFG, every mapped temporary has class `W`,
       `L` or `P`, no two mapped parameters share a hardware register,
       every entry-live mapped temporary belongs to `param_tids`, and any
       multi-block execution trace from block `0` (across
       multi-definitions, caller-saved call clobbers, simultaneous
       [[phi]] edge updates and `Poll` back-edge clobbers) reads identical
       operands and jump inputs to abstract temporary execution whenever
       unmapped writes satisfy [cfg_trace_slot_ok].
    3. **3-address `lea` and immediate selection** ([imm32_congruent],
       [imm32_add_mod_sound], [imm32_sub_lea_w_sound],
       [imm32_sub_lea_l_sound]): [integer_immediate] and negated `lea`
       displacements compute the exact modular sum and difference at
       both 32-bit (`w`, including `-2^31`) and 64-bit (`l`) widths.
    4. **Whole-scheduler parallel-move soundness**
       ([compile_pmoves_no_todo], [compile_pmoves_sound],
       [ready_pmove_step_sound]): for any well-formed parallel-move list
       with distinct non-scratch destinations and canonical source
       widths, [compile_pmoves] never exhausts its `2n + 1` fuel or
       emits [todo], keeps `%rcx` unread before every cycle break across
       any number of disjoint cycles, and emits x86-64 instructions
       whose sequential execution produces [simul_pmoves] on every
       allocatable register and frame slot under any global symbol map.
    5. **Concrete [build_rctx] callee-save and root-slot invariants**
       ([build_rctx_save_slots_disjoint],
       [build_rctx_used_callee_saved], [build_rctx_callee_saves_sound],
       [build_rctx_root_lower_slot], [lower_key_never_hreg]):
       callee-save slots in [rc_saves] are disjoint from every plain,
       root and aliased frame slot, cover every callee-saved register in
       `rm`, restore all five callee-saved registers via
       [callee_save_stores] and [callee_save_restores], and keep pointer
       lowers in concrete `lowers[]` GC root slots.
    6. **Scope boundary**: `RegsProof.v` proves the verification,
       scheduling and frame-layout kernels above. It does not prove
       whole-function x86-64 lowering of [function_code_allocated]
       against `Nanofil.Semantics`: extraction of [rblock] metadata from
       fused instructions ([pinst_uses], [pinst_defs], [pinst_call],
       [build_eblock]), discharge of [cfg_trace_slot_ok] from
       `FrameSlots.temp_slots`, and machine semantics for non-move body
       instructions remain outside this file and are checked by the
       differential and FUGC gates (`tests/regs.sh`). *)

From Stdlib Require Import String ZArith List Bool Arith Lia SetoidList.
From Nanofil Require Import Term Syntax Maps.
From Backend Require Import Asm Order Plan PlanTerm Layout Emit Regs.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(** ## 1. Hardware register equality and interval disjointness *)

Lemma hreg_eqb_refl : forall r, hreg_eqb r r = true.
Proof. destruct r; reflexivity. Qed.

Theorem hreg_eqb_spec : forall a b, hreg_eqb a b = true <-> a = b.
Proof.
  intros a b. split; intro H.
  - destruct a, b; simpl in H; try discriminate; reflexivity.
  - subst b. apply hreg_eqb_refl.
Qed.

Lemma nat_ltb_spec : forall a b, nat_ltb a b = true <-> (a < b)%nat.
Proof.
  intros a b. unfold nat_ltb.
  destruct (Nat.compare_spec a b); split; intro Hc; try discriminate; lia.
Qed.

Lemma nat_ltb_false_spec : forall a b, nat_ltb a b = false <-> (b <= a)%nat.
Proof.
  intros a b. unfold nat_ltb.
  destruct (Nat.compare_spec a b); split; intro Hc; try discriminate; lia.
Qed.

Lemma nat_eqb_spec : forall a b, nat_eqb a b = true <-> a = b.
Proof.
  intros a b. unfold nat_eqb.
  destruct (Nat.compare_spec a b); split; intro Hc; try discriminate; lia.
Qed.

(** Whether point `p` lies in some closed interval `[lo, hi]` of `ivs`. *)
Fixpoint in_ivals (p : nat) (ivs : list ival) : Prop :=
  match ivs with
  | [] => False
  | (lo, hi) :: ivs' => ((lo <= p)%nat /\ (p <= hi)%nat) \/ in_ivals p ivs'
  end.

(** Strictly ordered interval list: each interval ends before the next
    begins, and every interval satisfies `lo <= hi`. *)
Fixpoint ivals_wf (bound : nat) (ivs : list ival) : Prop :=
  match ivs with
  | [] => True
  | (lo, hi) :: ivs' =>
      (bound <= lo)%nat /\ (lo <= hi)%nat /\ ivals_wf (S hi) ivs'
  end.

Lemma in_ivals_ge_bound : forall ivs bound p,
  ivals_wf bound ivs -> in_ivals p ivs -> (bound <= p)%nat.
Proof.
  induction ivs as [|[lo hi] ivs' IH]; intros bound p Hwf Hin; simpl in *.
  - contradiction.
  - destruct Hwf as [Hb [Hlh Hwf']].
    destruct Hin as [[H1 _] | Hin'].
    + lia.
    + specialize (IH (S hi) p Hwf' Hin'). lia.
Qed.

Lemma ivals_wf_weaken : forall ivs b1 b2,
  (b1 <= b2)%nat -> ivals_wf b2 ivs -> ivals_wf b1 ivs.
Proof.
  destruct ivs as [|[lo hi] ivs']; intros b1 b2 Hle Hwf; simpl in *; [exact I|].
  destruct Hwf as [H1 H2]. split; [lia | exact H2].
Qed.

Lemma ivals_disjoint_fuel_sound : forall fuel xs ys bx by0 p,
  ivals_wf bx xs -> ivals_wf by0 ys ->
  ivals_disjoint_fuel fuel xs ys = true ->
  in_ivals p xs -> in_ivals p ys -> False.
Proof.
  induction fuel as [|fuel' IH]; intros xs ys bx by0 p Hwx Hwy Hdisj Hx Hy.
  - destruct xs as [|[a1 b1] xs']; [simpl in Hx; exact Hx|].
    destruct ys as [|[a2 b2] ys']; [simpl in Hy; exact Hy|].
    simpl in Hdisj. discriminate.
  - destruct xs as [|[a1 b1] xs']; [simpl in Hx; exact Hx|].
    destruct ys as [|[a2 b2] ys']; [simpl in Hy; exact Hy|].
    simpl in Hdisj.
    destruct Hwx as [Hbx [Hab1 Hwx']].
    destruct Hwy as [Hby [Hab2 Hwy']].
    destruct (nat_ltb b1 a2) eqn:E1.
    + apply nat_ltb_spec in E1.
      simpl in Hx. destruct Hx as [[Hpa1 Hpb1] | Hx'].
      * assert (Hpge : (a2 <= p)%nat).
        { apply (in_ivals_ge_bound ((a2, b2) :: ys') a2 p); [|exact Hy].
          simpl. split; [lia | split; [exact Hab2 | exact Hwy']]. }
        lia.
      * eapply IH; [exact Hwx' | | exact Hdisj | exact Hx' | exact Hy].
        simpl. split; [exact Hby | split; [exact Hab2 | exact Hwy']].
    + destruct (nat_ltb b2 a1) eqn:E2; [|discriminate].
      apply nat_ltb_spec in E2.
      simpl in Hy. destruct Hy as [[Hpa2 Hpb2] | Hy'].
      * assert (Hpge : (a1 <= p)%nat).
        { apply (in_ivals_ge_bound ((a1, b1) :: xs') a1 p); [|exact Hx].
          simpl. split; [lia | split; [exact Hab1 | exact Hwx']]. }
        lia.
      * eapply IH; [| exact Hwy' | exact Hdisj | exact Hx | exact Hy'].
        simpl. split; [exact Hbx | split; [exact Hab1 | exact Hwx']].
Qed.

(** Disjoint well-formed interval lists share no program point. *)
Theorem ivals_disjoint_sound : forall xs ys p,
  ivals_wf O xs -> ivals_wf O ys ->
  ivals_disjoint xs ys = true ->
  in_ivals p xs -> in_ivals p ys -> False.
Proof.
  intros xs ys p Hwx Hwy Hdisj Hx Hy. unfold ivals_disjoint in Hdisj.
  eapply ivals_disjoint_fuel_sound; [exact Hwx | exact Hwy | exact Hdisj | exact Hx | exact Hy].
Qed.

Fixpoint pts_wf (bound : nat) (pts : list nat) : Prop :=
  match pts with
  | [] => True
  | q :: pts' => (bound <= q)%nat /\ pts_wf (S q) pts'
  end.

Lemma in_pts_ge_bound : forall pts bound p,
  pts_wf bound pts -> In p pts -> (bound <= p)%nat.
Proof.
  induction pts as [|q pts' IH]; intros bound p Hwf Hin; simpl in *.
  - contradiction.
  - destruct Hwf as [Hb Hwf']. destruct Hin as [<- | Hin'].
    + exact Hb.
    + specialize (IH (S q) p Hwf' Hin'). lia.
Qed.

Lemma ivals_hit_points_fuel_sound : forall fuel ivs pts bi bp p,
  ivals_wf bi ivs -> pts_wf bp pts ->
  ivals_hit_points_fuel fuel ivs pts = false ->
  in_ivals p ivs -> In p pts -> False.
Proof.
  induction fuel as [|fuel' IH]; intros ivs pts bi bp p Hwi Hwp Hhit Hin Hpt.
  - destruct ivs as [|[a b] ivs']; [simpl in Hin; exact Hin|].
    destruct pts as [|q pts']; [simpl in Hpt; exact Hpt|].
    simpl in Hhit. discriminate.
  - destruct ivs as [|[a b] ivs']; [simpl in Hin; exact Hin|].
    destruct pts as [|q pts']; [simpl in Hpt; exact Hpt|].
    simpl in Hhit.
    destruct Hwi as [Hbi [Hab Hwi']].
    destruct Hwp as [Hbp Hwp'].
    destruct (nat_ltb b q) eqn:E1.
    + apply nat_ltb_spec in E1.
      simpl in Hin. destruct Hin as [[_ Hpb] | Hin'].
      * assert (Hqle : (q <= p)%nat).
        { apply (in_pts_ge_bound (q :: pts') q p); [|exact Hpt].
          simpl. split; [lia | exact Hwp']. }
        lia.
      * eapply IH; [exact Hwi' | | exact Hhit | exact Hin' | exact Hpt].
        simpl. split; [exact Hbp | exact Hwp'].
    + destruct (nat_ltb q a) eqn:E2; [|discriminate].
      apply nat_ltb_spec in E2.
      simpl in Hpt. destruct Hpt as [<- | Hpt'].
      * assert (Hale : (a <= q)%nat).
        { apply (in_ivals_ge_bound ((a, b) :: ivs') a q); [|exact Hin].
          simpl. split; [lia | split; [exact Hab | exact Hwi']]. }
        lia.
      * eapply IH; [| exact Hwp' | exact Hhit | exact Hin | exact Hpt'].
        simpl. split; [exact Hbi | split; [exact Hab | exact Hwi']].
Qed.

(** When [ivals_hit_points] returns `false`, no call point in `pts`
    falls inside `ivs`. *)
Theorem ivals_hit_points_sound : forall ivs pts p,
  ivals_wf O ivs -> pts_wf O pts ->
  ivals_hit_points ivs pts = false ->
  in_ivals p ivs -> In p pts -> False.
Proof.
  intros ivs pts p Hwi Hwp Hhit Hin Hpt. unfold ivals_hit_points in Hhit.
  eapply ivals_hit_points_fuel_sound; [exact Hwi | exact Hwp | exact Hhit | exact Hin | exact Hpt].
Qed.

(** [nat_leb] reflects `<=` on [nat]. *)
Lemma nat_leb_spec : forall a b, nat_leb a b = true <-> (a <= b)%nat.
Proof.
  intros a b. unfold nat_leb.
  destruct (Nat.compare_spec a b); split; intro Hc; try discriminate; lia.
Qed.

(** [nat_leb] returns `false` iff `(b < a)%nat`. *)
Lemma nat_leb_false_spec : forall a b, nat_leb a b = false <-> (b < a)%nat.
Proof.
  intros a b. unfold nat_leb.
  destruct (Nat.compare_spec a b); split; intro Hc; try discriminate; lia.
Qed.

(** [nat_max] equals `Nat.max`. *)
Lemma nat_max_spec : forall a b, nat_max a b = Nat.max a b.
Proof.
  intros a b. unfold nat_max.
  destruct (nat_ltb a b) eqn:E.
  - apply nat_ltb_spec in E. lia.
  - apply nat_ltb_false_spec in E. lia.
Qed.

(** Membership in `in_ivals` distributes over list concatenation. *)
Lemma in_ivals_app : forall p xs ys,
  in_ivals p (xs ++ ys) <-> in_ivals p xs \/ in_ivals p ys.
Proof.
  intros p xs ys. induction xs as [|[a b] xs' IH]; simpl.
  - tauto.
  - rewrite IH. tauto.
Qed.

(** Appending an interval strictly after every element of `xs` preserves [ivals_wf]. *)
Lemma ivals_wf_snoc : forall xs bound a b,
  ivals_wf bound xs ->
  (bound <= a)%nat ->
  (a <= b)%nat ->
  (forall u v, In (u, v) xs -> (S v <= a)%nat) ->
  ivals_wf bound (xs ++ [(a, b)]).
Proof.
  induction xs as [|[u v] xs' IH]; intros bound a b Hwf Hba Hab Hall; simpl in *.
  - split; [exact Hba | split; [exact Hab | exact I]].
  - destruct Hwf as [Hbu [Huv Hwf']].
    pose proof (Hall u v (or_introl eq_refl)) as Hva.
    split; [exact Hbu | split; [exact Huv |]].
    apply IH; [exact Hwf' | exact Hva | exact Hab |].
    intros u' v' Hin'. apply (Hall u' v'). right. exact Hin'.
Qed.

(** Reversed well-formedness invariant on [ivals_union_acc]'s accumulator. *)
Definition ivals_acc_wf (lim : nat) (acc : list ival) : Prop :=
  ivals_wf O (rev acc) /\
  match acc with
  | [] => True
  | (a0, _) :: _ =>
      (a0 <= lim)%nat /\
      (forall u v, In (u, v) (tl acc) -> (S v <= a0)%nat)
  end.

(** Pushing interval `(a, b)` with `lim <= a <= b` onto `acc` preserves
    [ivals_acc_wf] at new limit `a` and adds `[a, b]` to `rev acc`. *)
Lemma ival_push_acc_sound : forall lim a b acc,
  ivals_acc_wf lim acc ->
  (lim <= a)%nat ->
  (a <= b)%nat ->
  ivals_acc_wf a (ival_push_acc (a, b) acc) /\
  (forall p, in_ivals p (rev (ival_push_acc (a, b) acc)) <->
             in_ivals p (rev acc) \/ ((a <= p)%nat /\ (p <= b)%nat)).
Proof.
  intros lim a b [|[a0 b0] acc'] [Hwf Hlim] Hla Hab.
  - simpl. split.
    + split; [split; [lia | split; [exact Hab | exact I]] | split; [lia | intros u v []]].
    + intro p. simpl. tauto.
  - destruct Hlim as [Ha0 Hall]. simpl in Hall.
    cbn [ival_push_acc fst snd].
    destruct (nat_leb a (S b0)) eqn:Ele.
    + apply nat_leb_spec in Ele.
      rewrite nat_max_spec.
      assert (Hwf_tl : ivals_wf O (rev acc')).
      { clear -Hwf. simpl in Hwf. revert Hwf. generalize O.
        induction (rev acc') as [|[u v] l IH]; intros bnd Hwf; simpl in *; [exact I|].
        destruct Hwf as [H1 [H2 H3]]. split; [exact H1 | split; [exact H2 | exact (IH (S v) H3)]]. }
      split.
      * split.
        -- simpl. apply ivals_wf_snoc; [exact Hwf_tl | lia | lia |].
           intros u v Hin. apply (Hall u v). apply in_rev. exact Hin.
        -- split; [lia | exact Hall].
      * intro p. simpl. rewrite !in_ivals_app. simpl.
        assert (Hmerge : ((a0 <= p)%nat /\ (p <= Nat.max b0 b)%nat) <->
                         ((a0 <= p)%nat /\ (p <= b0)%nat) \/ ((a <= p)%nat /\ (p <= b)%nat)) by lia.
        tauto.
    + apply nat_leb_false_spec in Ele.
      assert (Hb0 : (a0 <= b0)%nat).
      { clear -Hwf. simpl in Hwf. revert Hwf. generalize O.
        induction (rev acc') as [|[u v] l IH]; intros bnd Hwf; simpl in *.
        - exact (proj1 (proj2 Hwf)).
        - exact (IH (S v) (proj2 (proj2 Hwf))). }
      split.
      * split.
        -- change (rev ((a, b) :: (a0, b0) :: acc')) with (rev ((a0, b0) :: acc') ++ [(a, b)]).
           apply ivals_wf_snoc; [exact Hwf | lia | exact Hab |].
           intros u v Hin. simpl in Hin.
           apply in_app_or in Hin. destruct Hin as [Hin' | [Heq | []]].
           ++ apply in_rev in Hin'. pose proof (Hall u v Hin'). lia.
           ++ injection Heq as <- <-. lia.
        -- split; [lia |].
           intros u v [Heq | Hin']; [injection Heq as <- <-; lia | pose proof (Hall u v Hin'); lia].
      * intro p. change (rev ((a, b) :: (a0, b0) :: acc')) with (rev ((a0, b0) :: acc') ++ [(a, b)]).
        rewrite in_ivals_app. simpl. tauto.
Qed.

(** Fuel induction for [ivals_union_acc]. *)
Lemma ivals_union_acc_sound : forall fuel xs ys bx by0 lim acc,
  (length xs + length ys <= fuel)%nat ->
  ivals_wf bx xs ->
  ivals_wf by0 ys ->
  (lim <= bx)%nat ->
  (lim <= by0)%nat ->
  ivals_acc_wf lim acc ->
  ivals_wf O (ivals_union_acc fuel xs ys acc) /\
  (forall p, in_ivals p (ivals_union_acc fuel xs ys acc) <->
             in_ivals p (rev acc) \/ in_ivals p xs \/ in_ivals p ys).
Proof.
  induction fuel as [|fuel' IH]; intros xs ys bx by0 lim acc Hfuel Hwx Hwy Hlx Hly Hacc.
  - destruct xs, ys; simpl in Hfuel; try lia.
    simpl. unfold rev'. rewrite <- rev_alt.
    split; [exact (proj1 Hacc) | intro p; simpl; tauto].
  - destruct xs as [|[a1 b1] xs'], ys as [|[a2 b2] ys'].
    + simpl. unfold rev'. rewrite <- rev_alt.
      split; [exact (proj1 Hacc) | intro p; simpl; tauto].
    + cbn [ivals_union_acc]. simpl in Hwx, Hwy, Hfuel.
      destruct Hwy as [Hby [Hab2 Hwy']].
      destruct (ival_push_acc_sound lim a2 b2 acc Hacc ltac:(lia) Hab2) as [Hacc' Hiff'].
      destruct (IH [] ys' a2 (S b2) a2 (ival_push_acc (a2, b2) acc)
                  ltac:(simpl; lia) I Hwy' ltac:(lia) ltac:(lia) Hacc') as [Hwf_end Hiff_end].
      split; [exact Hwf_end|].
      intro p. rewrite Hiff_end, Hiff'. simpl. tauto.
    + cbn [ivals_union_acc]. simpl in Hwx, Hwy, Hfuel.
      destruct Hwx as [Hbx [Hab1 Hwx']].
      destruct (ival_push_acc_sound lim a1 b1 acc Hacc ltac:(lia) Hab1) as [Hacc' Hiff'].
      destruct (IH xs' [] (S b1) a1 a1 (ival_push_acc (a1, b1) acc)
                  ltac:(simpl; lia) Hwx' I ltac:(lia) ltac:(lia) Hacc') as [Hwf_end Hiff_end].
      split; [exact Hwf_end|].
      intro p. rewrite Hiff_end, Hiff'. simpl. tauto.
    + cbn [ivals_union_acc]. simpl in Hwx, Hwy, Hfuel.
      destruct Hwx as [Hbx [Hab1 Hwx']].
      destruct Hwy as [Hby [Hab2 Hwy']].
      destruct (nat_leb a1 a2) eqn:Ele.
      * apply nat_leb_spec in Ele.
        destruct (ival_push_acc_sound lim a1 b1 acc Hacc ltac:(lia) Hab1) as [Hacc' Hiff'].
        destruct (IH xs' ((a2, b2) :: ys') (S b1) a2 a1 (ival_push_acc (a1, b1) acc)
                    ltac:(simpl; lia) Hwx'
                    (conj (Nat.le_refl a2) (conj Hab2 Hwy'))
                    ltac:(lia) Ele Hacc') as [Hwf_end Hiff_end].
        split; [exact Hwf_end|].
        intro p. rewrite Hiff_end, Hiff'. simpl. tauto.
      * apply nat_leb_false_spec in Ele.
        destruct (ival_push_acc_sound lim a2 b2 acc Hacc ltac:(lia) Hab2) as [Hacc' Hiff'].
        destruct (IH ((a1, b1) :: xs') ys' a1 (S b2) a2 (ival_push_acc (a2, b2) acc)
                    ltac:(simpl; lia)
                    (conj (Nat.le_refl a1) (conj Hab1 Hwx'))
                    Hwy' ltac:(lia) ltac:(lia) Hacc') as [Hwf_end Hiff_end].
        split; [exact Hwf_end|].
        intro p. rewrite Hiff_end, Hiff'. simpl. tauto.
Qed.

(** [ivals_union] preserves [ivals_wf] and computes the exact point-set union. *)
Theorem ivals_union_sound : forall xs ys,
  ivals_wf O xs ->
  ivals_wf O ys ->
  ivals_wf O (ivals_union xs ys) /\
  (forall p, in_ivals p (ivals_union xs ys) <-> in_ivals p xs \/ in_ivals p ys).
Proof.
  intros xs ys Hwx Hwy. unfold ivals_union.
  destruct (ivals_union_acc_sound (length xs + length ys) xs ys O O O []
              (Nat.le_refl _) Hwx Hwy (Nat.le_refl O) (Nat.le_refl O) (conj I I))
    as [Hwf Hiff].
  split; [exact Hwf | intro p; rewrite Hiff; simpl; tauto].
Qed.

(** Non-strictly sorted [list nat] predicate for merge sort [Order.msort]. *)
Fixpoint le_wf (bound : nat) (xs : list nat) : Prop :=
  match xs with
  | [] => True
  | x :: xs' => (bound <= x)%nat /\ le_wf x xs'
  end.

(** Weakening the lower bound of [le_wf]. *)
Lemma le_wf_weaken : forall xs b1 b2,
  (b1 <= b2)%nat -> le_wf b2 xs -> le_wf b1 xs.
Proof.
  destruct xs as [|x xs']; intros b1 b2 Hle Hwf; simpl in *; [exact I|].
  destruct Hwf as [H1 H2]. split; [lia | exact H2].
Qed.

(** Weakening the lower bound of [pts_wf]. *)
Lemma pts_wf_weaken : forall xs b1 b2,
  (b1 <= b2)%nat -> pts_wf b2 xs -> pts_wf b1 xs.
Proof.
  destruct xs as [|x xs']; intros b1 b2 Hle Hwf; simpl in *; [exact I|].
  destruct Hwf as [H1 H2]. split; [lia | exact H2].
Qed.

(** [Order.merge_steps] preserves [le_wf] and computes list union when fuel suffices. *)
Lemma merge_steps_nat_spec : forall n xs ys b,
  (length xs + length ys <= n)%nat ->
  le_wf b xs -> le_wf b ys ->
  le_wf b (merge_steps Nat.compare n xs ys) /\
  (forall z, In z (merge_steps Nat.compare n xs ys) <-> In z xs \/ In z ys).
Proof.
  induction n as [|n' IH]; intros xs ys b Hlen Hwx Hwy.
  - destruct xs, ys; simpl in *; try lia.
    split; [exact I | intro z; tauto].
  - destruct xs as [|x xs'], ys as [|y ys']; simpl in *.
    + split; [exact I | intro z; tauto].
    + split; [exact Hwy | intro z; tauto].
    + split; [exact Hwx | intro z; tauto].
    + destruct Hwx as [Hbx Hwx']. destruct Hwy as [Hby Hwy'].
      destruct (Nat.compare_spec x y) as [Heq | Hlt | Hgt].
      * subst y.
        destruct (IH xs' (x :: ys') x ltac:(simpl; lia) Hwx' (conj (Nat.le_refl x) Hwy'))
          as [Hwf Hiff].
        split; [split; [exact Hbx | exact Hwf] | intro z; simpl; rewrite Hiff; simpl; tauto].
      * destruct (IH xs' (y :: ys') x ltac:(simpl; lia) Hwx' (conj (Nat.lt_le_incl x y Hlt) Hwy'))
          as [Hwf Hiff].
        split; [split; [exact Hbx | exact Hwf] | intro z; simpl; rewrite Hiff; simpl; tauto].
      * destruct (IH (x :: xs') ys' y ltac:(simpl; lia) (conj (Nat.lt_le_incl y x Hgt) Hwx') Hwy')
          as [Hwf Hiff].
        split; [split; [exact Hby | exact Hwf] | intro z; simpl; rewrite Hiff; simpl; tauto].
Qed.

(** [Order.merge] preserves [le_wf] and computes list union. *)
Lemma merge_nat_spec : forall xs ys,
  le_wf O xs -> le_wf O ys ->
  le_wf O (merge Nat.compare xs ys) /\
  (forall z, In z (merge Nat.compare xs ys) <-> In z xs \/ In z ys).
Proof.
  intros xs ys Hx Hy. unfold merge.
  exact (merge_steps_nat_spec (length xs + length ys) xs ys O (Nat.le_refl _) Hx Hy).
Qed.

(** Well-formedness of a merge-sort run stack. *)
Fixpoint run_stack_wf (st : list (option (list nat))) : Prop :=
  match st with
  | [] => True
  | None :: st' => run_stack_wf st'
  | Some r :: st' => le_wf O r /\ run_stack_wf st'
  end.

(** Membership across a merge-sort run stack. *)
Fixpoint in_run_stack (z : nat) (st : list (option (list nat))) : Prop :=
  match st with
  | [] => False
  | None :: st' => in_run_stack z st'
  | Some r :: st' => In z r \/ in_run_stack z st'
  end.

(** [Order.push_run] preserves [run_stack_wf] and adds `run`'s elements. *)
Lemma push_run_nat_spec : forall st run,
  run_stack_wf st -> le_wf O run ->
  run_stack_wf (push_run Nat.compare st run) /\
  (forall z, in_run_stack z (push_run Nat.compare st run) <-> in_run_stack z st \/ In z run).
Proof.
  induction st as [|[r'|] st' IH]; intros run Hst Hrun; simpl in *.
  - split; [split; [exact Hrun | exact I] | intro z; tauto].
  - destruct Hst as [Hr' Hst'].
    destruct (merge_nat_spec r' run Hr' Hrun) as [Hm_wf Hm_in].
    destruct (IH (merge Nat.compare r' run) Hst' Hm_wf) as [Hp_wf Hp_in].
    split; [exact Hp_wf | intro z; rewrite Hp_in, Hm_in; tauto].
  - split; [split; [exact Hrun | exact Hst] | intro z; tauto].
Qed.

(** [Order.merge_runs] merges a well-formed stack into a sorted list. *)
Lemma merge_runs_nat_spec : forall st,
  run_stack_wf st ->
  le_wf O (merge_runs Nat.compare st) /\
  (forall z, In z (merge_runs Nat.compare st) <-> in_run_stack z st).
Proof.
  induction st as [|[r|] st' IH]; intro Hst; simpl in *.
  - split; [exact I | intro z; tauto].
  - destruct Hst as [Hr Hst'].
    destruct (IH Hst') as [Hm_wf Hm_in].
    destruct (merge_nat_spec (merge_runs Nat.compare st') r Hm_wf Hr) as [Hwf Hiff].
    split; [exact Hwf | intro z; rewrite Hiff, Hm_in; tauto].
  - exact (IH Hst).
Qed.

(** [Order.dedup] turns [le_wf] into strict [pts_wf] while preserving membership. *)
Lemma dedup_nat_spec : forall xs b,
  le_wf b xs ->
  pts_wf b (dedup Nat.compare xs) /\
  (forall z, In z (dedup Nat.compare xs) <-> In z xs).
Proof.
  induction xs as [|x [|y ys] IH]; intros b Hle; simpl in *.
  - split; [exact I | intro z; tauto].
  - destruct Hle as [Hbx _].
    split; [split; [exact Hbx | exact I] | intro z; tauto].
  - destruct Hle as [Hbx [Hxy Hys]].
    destruct (Nat.compare_spec x y) as [Heq | Hlt | Hgt].
    + subst y.
      destruct (IH b (conj Hbx Hys)) as [Hwf Hiff].
      split; [exact Hwf | intro z; rewrite Hiff; simpl; intuition congruence].
    + destruct (IH (S x) (conj Hlt Hys)) as [Hwf Hiff].
      split; [split; [exact Hbx | exact Hwf] | intro z; simpl; rewrite Hiff; simpl; tauto].
    + lia.
Qed.

(** [nset_of_list] produces a strictly sorted [pts_wf] ordset with identical elements. *)
Theorem nset_of_list_spec : forall xs,
  pts_wf O (nset_of_list xs) /\
  (forall z, In z (nset_of_list xs) <-> In z xs).
Proof.
  intro xs. unfold nset_of_list, sort, msort.
  assert (Hfold : forall l st,
            run_stack_wf st ->
            run_stack_wf (fold_left (fun s x => push_run Nat.compare s [x]) l st) /\
            (forall z, in_run_stack z (fold_left (fun s x => push_run Nat.compare s [x]) l st) <->
                       in_run_stack z st \/ In z l)).
  { induction l as [|x l' IH]; intros st Hst; simpl.
    - split; [exact Hst | intro z; tauto].
    - assert (Hx : le_wf O [x]) by (simpl; split; [lia | exact I]).
      destruct (push_run_nat_spec st [x] Hst Hx) as [Hst1 Hin1].
      destruct (IH _ Hst1) as [Hst2 Hin2].
      split; [exact Hst2 | intro z; rewrite Hin2, Hin1; simpl; tauto]. }
  destruct (Hfold xs [] I) as [Hst Hin_st].
  destruct (merge_runs_nat_spec _ Hst) as [Hm_wf Hm_in].
  destruct (dedup_nat_spec _ O Hm_wf) as [Hd_wf Hd_in].
  split; [exact Hd_wf | intro z; rewrite Hd_in, Hm_in, Hin_st; simpl; tauto].
Qed.

(** [nset_eqb] reflects list equality on [list nat]. *)
Theorem nset_eqb_spec : forall xs ys,
  nset_eqb xs ys = true <-> xs = ys.
Proof.
  induction xs as [|x xs' IH]; intros [|y ys']; simpl;
    try (split; [discriminate | discriminate]).
  - split; reflexivity.
  - destruct (nat_eqb x y) eqn:Exy.
    + apply nat_eqb_spec in Exy. subst y.
      rewrite IH. split; [intro H; subst; reflexivity | intro H; injection H as ->; reflexivity].
    + split; [discriminate | intro H; injection H as -> _; rewrite (proj2 (nat_eqb_spec y y) eq_refl) in Exy; discriminate].
Qed.

(** Appending a strictly greater element to a [pts_wf] list preserves [pts_wf]. *)
Lemma pts_wf_snoc : forall xs b x,
  pts_wf b xs ->
  (b <= x)%nat ->
  (forall y, In y xs -> (S y <= x)%nat) ->
  pts_wf b (xs ++ [x]).
Proof.
  induction xs as [|u xs' IH]; intros b x Hwf Hbx Hall; simpl in *.
  - split; [exact Hbx | exact I].
  - destruct Hwf as [Hbu Hwf'].
    split; [exact Hbu |].
    apply IH; [exact Hwf' | exact (Hall u (or_introl eq_refl)) |].
    intros y Hy. apply Hall. right. exact Hy.
Qed.

(** Accumulator invariant for [nset_union_acc] and [nset_sub_acc]. *)
Definition nset_acc_wf (lim : nat) (acc : list nat) : Prop :=
  pts_wf O (rev acc) /\ (forall y, In y acc -> (S y <= lim)%nat).

(** Extending `acc` with `x >= lim` preserves [nset_acc_wf] at `S x`. *)
Lemma nset_acc_push : forall lim x acc,
  nset_acc_wf lim acc ->
  (lim <= x)%nat ->
  nset_acc_wf (S x) (x :: acc).
Proof.
  intros lim x acc [Hwf Hall] Hlx. split.
  - simpl. apply pts_wf_snoc; [exact Hwf | lia |].
    intros y Hy. apply in_rev in Hy. pose proof (Hall y Hy). lia.
  - intros y [<- | Hy]; [lia | pose proof (Hall y Hy); lia].
Qed.

(** Appending a sorted suffix `ys` with bound `>= lim` onto `rev acc` preserves `pts_wf O`. *)
Lemma nset_acc_finish : forall ys lim acc,
  nset_acc_wf lim acc ->
  pts_wf lim ys ->
  pts_wf O (rev_append acc ys).
Proof.
  induction ys as [|y ys' IH]; intros lim acc Hacc Hwy; simpl in *.
  - rewrite rev_append_rev, app_nil_r. exact (proj1 Hacc).
  - destruct Hwy as [Hly Hwy'].
    change (rev_append acc (y :: ys')) with (rev_append (y :: acc) ys').
    apply (IH (S y) (y :: acc) (nset_acc_push lim y acc Hacc Hly) Hwy').
Qed.

(** Fuel induction for [nset_union_acc]. *)
Lemma nset_union_acc_spec : forall fuel xs ys bx by0 lim acc,
  (length xs + length ys <= fuel)%nat ->
  pts_wf bx xs -> pts_wf by0 ys ->
  (lim <= bx)%nat -> (lim <= by0)%nat ->
  nset_acc_wf lim acc ->
  pts_wf O (nset_union_acc fuel xs ys acc) /\
  (forall z, In z (nset_union_acc fuel xs ys acc) <-> In z acc \/ In z xs \/ In z ys).
Proof.
  induction fuel as [|fuel' IH]; intros xs ys bx by0 lim acc Hfuel Hwx Hwy Hlx Hly Hacc.
  - destruct xs, ys; simpl in Hfuel; try lia.
    simpl. rewrite rev_append_rev, app_nil_r.
    split; [exact (proj1 Hacc) | intro z; rewrite <- in_rev; simpl; tauto].
  - destruct xs as [|x xs'], ys as [|y ys'].
    + simpl. rewrite rev_append_rev, app_nil_r.
      split; [exact (proj1 Hacc) | intro z; rewrite <- in_rev; simpl; tauto].
    + cbn [nset_union_acc].
      split; [exact (nset_acc_finish (y :: ys') lim acc Hacc (pts_wf_weaken _ lim by0 Hly Hwy))|].
      intro z. rewrite rev_append_rev, in_app_iff, <- in_rev. simpl; tauto.
    + cbn [nset_union_acc].
      split; [exact (nset_acc_finish (x :: xs') lim acc Hacc (pts_wf_weaken _ lim bx Hlx Hwx))|].
      intro z. rewrite rev_append_rev, in_app_iff, <- in_rev. simpl; tauto.
    + cbn [nset_union_acc]. simpl in Hwx, Hwy, Hfuel.
      destruct Hwx as [Hbx Hwx']. destruct Hwy as [Hby Hwy'].
      destruct (Nat.compare_spec x y) as [Heq | Hlt | Hgt].
      * subst y.
        destruct (IH xs' ys' (S x) (S x) (S x) (x :: acc)
                    ltac:(lia) Hwx' Hwy' (Nat.le_refl _) (Nat.le_refl _)
                    (nset_acc_push lim x acc Hacc ltac:(lia))) as [Hwf Hiff].
        split; [exact Hwf | intro z; rewrite Hiff; simpl; intuition congruence].
      * destruct (IH xs' (y :: ys') (S x) y (S x) (x :: acc)
                    ltac:(simpl; lia) Hwx' (conj (Nat.le_refl y) Hwy')
                    (Nat.le_refl _) Hlt
                    (nset_acc_push lim x acc Hacc ltac:(lia))) as [Hwf Hiff].
        split; [exact Hwf | intro z; rewrite Hiff; simpl; tauto].
      * destruct (IH (x :: xs') ys' x (S y) (S y) (y :: acc)
                    ltac:(simpl; lia) (conj (Nat.le_refl x) Hwx') Hwy'
                    Hgt (Nat.le_refl _)
                    (nset_acc_push lim y acc Hacc ltac:(lia))) as [Hwf Hiff].
        split; [exact Hwf | intro z; rewrite Hiff; simpl; tauto].
Qed.

(** [nset_union] preserves [pts_wf] and computes exact set union. *)
Theorem nset_union_spec : forall xs ys,
  pts_wf O xs -> pts_wf O ys ->
  pts_wf O (nset_union xs ys) /\
  (forall z, In z (nset_union xs ys) <-> In z xs \/ In z ys).
Proof.
  intros xs ys Hx Hy. unfold nset_union.
  destruct (nset_union_acc_spec (length xs + length ys) xs ys O O O []
              (Nat.le_refl _) Hx Hy (Nat.le_refl O) (Nat.le_refl O)
              (conj I (fun _ H => False_ind _ H))) as [Hwf Hiff].
  split; [exact Hwf | intro z; rewrite Hiff; simpl; tauto].
Qed.

(** Fuel induction for [nset_sub_acc]. *)
Lemma nset_sub_acc_spec : forall fuel xs ys bx by0 lim acc,
  (length xs + length ys <= fuel)%nat ->
  pts_wf bx xs -> pts_wf by0 ys ->
  (lim <= bx)%nat ->
  nset_acc_wf lim acc ->
  pts_wf O (nset_sub_acc fuel xs ys acc) /\
  (forall z, In z (nset_sub_acc fuel xs ys acc) <-> In z acc \/ (In z xs /\ ~ In z ys)).
Proof.
  induction fuel as [|fuel' IH]; intros xs ys bx by0 lim acc Hfuel Hwx Hwy Hlx Hacc.
  - destruct xs, ys; simpl in Hfuel; try lia.
    simpl. unfold rev'. rewrite <- rev_alt.
    split; [exact (proj1 Hacc) | intro z; rewrite <- in_rev; simpl; tauto].
  - destruct xs as [|x xs'], ys as [|y ys'].
    + simpl. unfold rev'. rewrite <- rev_alt.
      split; [exact (proj1 Hacc) | intro z; rewrite <- in_rev; simpl; tauto].
    + simpl. unfold rev'. rewrite <- rev_alt.
      split; [exact (proj1 Hacc) | intro z; rewrite <- in_rev; simpl; tauto].
    + cbn [nset_sub_acc].
      split; [exact (nset_acc_finish (x :: xs') lim acc Hacc (pts_wf_weaken _ lim bx Hlx Hwx))|].
      intro z. rewrite rev_append_rev, in_app_iff, <- in_rev. simpl. tauto.
    + cbn [nset_sub_acc]. simpl in Hwx, Hwy, Hfuel.
      destruct Hwx as [Hbx Hwx']. destruct Hwy as [Hby Hwy'].
      destruct (Nat.compare_spec x y) as [Heq | Hlt | Hgt].
      * subst y.
        destruct (IH xs' ys' (S x) (S x) lim acc ltac:(lia) Hwx' Hwy' ltac:(lia) Hacc)
          as [Hwf Hiff].
        split; [exact Hwf|].
        intro z. rewrite Hiff. split.
        -- intros [Ha | [Hx' Hny]]; [left; exact Ha | right; split; [right; exact Hx'|]].
           intros [<- | Hy']; [pose proof (in_pts_ge_bound xs' (S x) x Hwx' Hx'); lia | contradiction].
        -- intros [Ha | [[<- | Hx'] Hny]]; [left; exact Ha | exfalso; apply Hny; left; reflexivity |].
           right; split; [exact Hx' | intro Hy'; apply Hny; right; exact Hy'].
      * destruct (IH xs' (y :: ys') (S x) y (S x) (x :: acc)
                    ltac:(simpl; lia) Hwx' (conj (Nat.le_refl y) Hwy') (Nat.le_refl _)
                    (nset_acc_push lim x acc Hacc ltac:(lia))) as [Hwf Hiff].
        split; [exact Hwf|].
        intro z. rewrite Hiff. simpl. split.
        -- intros [[<- | Ha] | [Hx' Hny]]; [| left; exact Ha | right; split; [right; exact Hx' | exact Hny]].
           right. split; [left; reflexivity|].
           intros [<- | Hy']; [lia | pose proof (in_pts_ge_bound ys' (S y) x Hwy' Hy'); lia].
        -- intros [Ha | [[<- | Hx'] Hny]]; [left; right; exact Ha | left; left; reflexivity |].
           right; split; [exact Hx' | exact Hny].
      * destruct (IH (x :: xs') ys' x (S y) lim acc
                    ltac:(simpl; lia) (conj (Nat.le_refl x) Hwx') Hwy' ltac:(lia) Hacc)
          as [Hwf Hiff].
        split; [exact Hwf|].
        intro z. rewrite Hiff. simpl. split.
        -- intros [Ha | [Hx Hny]]; [left; exact Ha | right; split; [exact Hx|]].
           intros [<- | Hy']; [|contradiction].
           destruct Hx as [<- | Hx']; [lia | pose proof (in_pts_ge_bound xs' (S x) y Hwx' Hx'); lia].
        -- intros [Ha | [Hx Hny]]; [left; exact Ha | right; split; [exact Hx | intro Hy'; apply Hny; right; exact Hy']].
Qed.

(** [nset_sub] preserves [pts_wf] and computes exact set difference. *)
Theorem nset_sub_spec : forall xs ys,
  pts_wf O xs -> pts_wf O ys ->
  pts_wf O (nset_sub xs ys) /\
  (forall z, In z (nset_sub xs ys) <-> In z xs /\ ~ In z ys).
Proof.
  intros xs ys Hx Hy. unfold nset_sub.
  destruct (nset_sub_acc_spec (length xs + length ys) xs ys O O O []
              (Nat.le_refl _) Hx Hy (Nat.le_refl O)
              (conj I (fun _ H => False_ind _ H))) as [Hwf Hiff].
  split; [exact Hwf | intro z; rewrite Hiff; simpl; tauto].
Qed.

(** ## 2. Live register and shared-slot state preservation *)

(** Register file and physical stack-frame slots (indexed by frame
    offset `Z`, which disjoint lifetimes in FrameSlots.v may share). *)
Record mach_state : Type := mkMach {
  ms_reg : hreg -> Z;
  ms_slot : Z -> Z
}.

(** Read temporary `t` from its assigned [hreg] in `rm` or from its
    physical frame slot `slot_of t`. *)
Definition read_mach (rm : ZMap.t hreg) (slot_of : nat -> Z)
                     (ms : mach_state) (t : nat) : Z :=
  match zmap_find_nat t rm with
  | Some r => ms_reg ms r
  | None => ms_slot ms (slot_of t)
  end.

(** Write value `v` to temporary `t`'s assigned [hreg] in `rm` or to
    its physical frame slot `slot_of t`. *)
Definition write_mach (rm : ZMap.t hreg) (slot_of : nat -> Z)
                      (ms : mach_state) (t : nat) (v : Z) : mach_state :=
  match zmap_find_nat t rm with
  | Some r => mkMach (fun r' => if hreg_eqb r' r then v else ms_reg ms r') (ms_slot ms)
  | None => mkMach (ms_reg ms) (fun off => if Z.eqb off (slot_of t) then v else ms_slot ms off)
  end.

(** Write a list of destinations `ds` and values `vs` sequentially to
    registers and physical frame slots. *)
Fixpoint write_mach_list (rm : ZMap.t hreg) (slot_of : nat -> Z)
                         (ms : mach_state) (ds : list nat) (vs : list Z)
  : mach_state :=
  match ds, vs with
  | d :: ds', v :: vs' => write_mach_list rm slot_of (write_mach rm slot_of ms d v) ds' vs'
  | _, _ => ms
  end.

(** Write a list of destinations `ds` and values `vs` to the abstract
    temporary environment `tenv`. *)
Fixpoint write_abs_list (tenv : nat -> Z) (ds : list nat) (vs : list Z) : nat -> Z :=
  match ds, vs with
  | d :: ds', v :: vs' =>
      write_abs_list (fun t => if Nat.eqb t d then v else tenv t) ds' vs'
  | _, _ => tenv
  end.

(** A call clobbers caller-saved registers (`%r10`, `%r11`) with
    arbitrary values `arb` while preserving callee-saved registers and
    physical stack slots. *)
Definition clobber_call (arb : hreg -> Z) (ms : mach_state) : mach_state :=
  mkMach (fun r => if hreg_callee_saved r then ms_reg ms r else arb r) (ms_slot ms).

(** Live-only state agreement: every temporary `t` in `live` reads as
    `tenv t` in `ms` under `rm` and `slot_of`. Dead temporaries need
    not retain their values in shared physical slots. *)
Definition state_agrees (rm : ZMap.t hreg) (slot_of : nat -> Z) (live : list nat)
                        (tenv : nat -> Z) (ms : mach_state) : Prop :=
  forall t, In t live -> read_mach rm slot_of ms t = tenv t.

(** Witness that dead unmapped `0` (abstract value `1`) and live
    unmapped `1` (abstract value `2`) can share physical frame offset
    `16` while satisfying [state_agrees] on `[1]`. *)
Definition ex_shared_slot_of (_ : nat) : Z := 16.
Definition ex_shared_tenv (t : nat) : Z := if Nat.eqb t 0%nat then 1 else 2.
Definition ex_shared_ms : mach_state :=
  mkMach (fun _ => 0) (fun off => if Z.eqb off 16 then 2 else 0).

(** Shared physical spill slots satisfy [state_agrees] once an earlier
    occupant is dead. *)
Example ex_shared_spill_slot :
  state_agrees (ZMap.empty hreg) ex_shared_slot_of [1%nat] ex_shared_tenv ex_shared_ms.
Proof.
  intros t [<- | []]. reflexivity.
Qed.

(** [hreg_in_list] reflects list membership [In]. *)
Lemma hreg_in_list_spec : forall r rs,
  hreg_in_list r rs = true <-> In r rs.
Proof.
  intros r rs. induction rs as [|r' rs' IH]; simpl.
  - split; intro H; [discriminate | contradiction].
  - destruct (hreg_eqb r r') eqn:E.
    + apply hreg_eqb_spec in E. subst r'. split; auto.
    + rewrite IH. split; [right; exact H | intros [Heq | Hin]; [subst; rewrite hreg_eqb_refl in E; discriminate | exact Hin]].
Qed.

(** No temporary in `ts` maps to a register already present in `seen`
    when [no_dup_hregs_acc] accepts. *)
Lemma no_dup_hregs_acc_disjoint : forall rm ts seen t1 r,
  no_dup_hregs_acc rm ts seen = true ->
  In t1 ts -> In r seen -> zmap_find_nat t1 rm = Some r -> False.
Proof.
  intros rm ts. induction ts as [|t ts' IH]; intros seen t1 r Hnd Hin Hseen Hrm; simpl in *.
  - contradiction.
  - destruct (zmap_find_nat t rm) as [rt|] eqn:Ert.
    + destruct (hreg_in_list rt seen) eqn:Ein; [discriminate|].
      destruct Hin as [<- | Hin'].
      * rewrite Hrm in Ert. injection Ert as <-.
        pose proof (proj2 (hreg_in_list_spec r seen) Hseen) as Ht.
        rewrite Ht in Ein. discriminate.
      * eapply IH; [exact Hnd | exact Hin' | right; exact Hseen | exact Hrm].
    + destruct Hin as [<- | Hin'].
      * rewrite Hrm in Ert. discriminate.
      * eapply IH; [exact Hnd | exact Hin' | exact Hseen | exact Hrm].
Qed.

(** When [no_dup_hregs] accepts `ts`, distinct temporaries in `ts`
    never map to the same [hreg]. *)
Lemma no_dup_hregs_inj : forall rm ts,
  no_dup_hregs rm ts = true ->
  forall t1 t2 r, In t1 ts -> In t2 ts -> t1 <> t2 ->
  zmap_find_nat t1 rm = Some r -> zmap_find_nat t2 rm = Some r -> False.
Proof.
  unfold no_dup_hregs. intros rm ts.
  assert (Hgen : forall seen, no_dup_hregs_acc rm ts seen = true ->
            forall t1 t2 r, In t1 ts -> In t2 ts -> t1 <> t2 ->
            zmap_find_nat t1 rm = Some r -> zmap_find_nat t2 rm = Some r -> False).
  { induction ts as [|t ts' IH]; intros seen Hacc t1 t2 r Hin1 Hin2 Hneq Hr1 Hr2; simpl in *.
    - contradiction.
    - destruct (zmap_find_nat t rm) as [rt|] eqn:Ert.
      + destruct (hreg_in_list rt seen) eqn:Ein; [discriminate|].
        destruct Hin1 as [<- | Hin1']; destruct Hin2 as [<- | Hin2'].
        * congruence.
        * rewrite Hr1 in Ert. injection Ert as <-.
          eapply no_dup_hregs_acc_disjoint; [exact Hacc | exact Hin2' | left; reflexivity | exact Hr2].
        * rewrite Hr2 in Ert. injection Ert as <-.
          eapply no_dup_hregs_acc_disjoint; [exact Hacc | exact Hin1' | left; reflexivity | exact Hr1].
        * eapply IH; [exact Hacc | exact Hin1' | exact Hin2' | exact Hneq | exact Hr1 | exact Hr2].
      + destruct Hin1 as [<- | Hin1']; [rewrite Hr1 in Ert; discriminate|].
        destruct Hin2 as [<- | Hin2']; [rewrite Hr2 in Ert; discriminate|].
        eapply IH; [exact Hacc | exact Hin1' | exact Hin2' | exact Hneq | exact Hr1 | exact Hr2]. }
  intros Hacc. eapply Hgen; exact Hacc.
Qed.

(** Every mapped temporary in a list accepted by [all_callee_saved]
    holds a callee-saved register. *)
Lemma all_callee_saved_spec : forall rm ts t r,
  all_callee_saved rm ts = true ->
  In t ts -> zmap_find_nat t rm = Some r ->
  hreg_callee_saved r = true.
Proof.
  intros rm ts. induction ts as [|x ts' IH]; intros t r Hall Hin Hrm; simpl in *.
  - contradiction.
  - destruct Hin as [<- | Hin'].
    + rewrite Hrm in Hall. destruct (hreg_callee_saved r); [reflexivity | discriminate].
    + destruct (zmap_find_nat x rm) as [rx|].
      * destruct (hreg_callee_saved rx); [|discriminate].
        eapply IH; eauto.
      * eapply IH; eauto.
Qed.

(** Clobbering caller-saved registers preserves [state_agrees] on any
    live list `ts` accepted by [all_callee_saved]. *)
Theorem clobber_preserves_agrees : forall rm slot_of ts tenv ms arb,
  all_callee_saved rm ts = true ->
  state_agrees rm slot_of ts tenv ms ->
  state_agrees rm slot_of ts tenv (clobber_call arb ms).
Proof.
  intros rm slot_of ts tenv ms arb Hcs Hlive t Hin.
  specialize (Hlive t Hin). unfold read_mach in *.
  destruct (zmap_find_nat t rm) as [r|] eqn:Er; simpl.
  - rewrite (all_callee_saved_spec rm ts t r Hcs Hin Er). exact Hlive.
  - exact Hlive.
Qed.

(** Poll-edge corollary: when `header_live` is accepted by
    [all_callee_saved], a slow-path poll clobbering caller-saved
    registers preserves [state_agrees] on `header_live`. *)
Theorem poll_edge_clobber_sound : forall rm slot_of header_live tenv ms arb,
  all_callee_saved rm header_live = true ->
  state_agrees rm slot_of header_live tenv ms ->
  state_agrees rm slot_of header_live tenv (clobber_call arb ms).
Proof.
  intros. apply clobber_preserves_agrees; assumption.
Qed.

(** Temporary `d`'s home (register in `rm`, or physical slot in
    `slot_of` when unmapped) collides with no other temporary `t <> d`
    in `live`. *)
Definition dest_no_collision (rm : ZMap.t hreg) (slot_of : nat -> Z)
                             (d : nat) (live : list nat) : Prop :=
  (forall r t, In t live -> t <> d ->
     zmap_find_nat d rm = Some r -> zmap_find_nat t rm = Some r -> False) /\
  (forall t, In t live -> t <> d ->
     zmap_find_nat d rm = None -> zmap_find_nat t rm = None ->
     slot_of d = slot_of t -> False).

(** Filter `live` down to temporaries distinct from `d`. *)
Definition live_without (d : nat) (live : list nat) : list nat :=
  filter (fun t => negb (Nat.eqb t d)) live.

(** Update `tenv` at temporary `d` to `v`. *)
Definition tenv_set (tenv : nat -> Z) (d : nat) (v : Z) (t : nat) : Z :=
  if Nat.eqb t d then v else tenv t.

(** Writing temporary `d` preserves every other temporary `t <> d` in
    `live` whose home does not collide with `d`'s, and sets `d` to `v`. *)
Theorem write_mach_step_sound : forall rm slot_of live tenv ms d v,
  dest_no_collision rm slot_of d live ->
  state_agrees rm slot_of (live_without d live) tenv ms ->
  state_agrees rm slot_of live (tenv_set tenv d v) (write_mach rm slot_of ms d v).
Proof.
  intros rm slot_of live tenv ms d v [Hreg Hslot] Hlive t Hin.
  unfold read_mach, write_mach, tenv_set.
  destruct (Nat.eqb t d) eqn:Etd.
  - apply Nat.eqb_eq in Etd. subst t.
    destruct (zmap_find_nat d rm) as [rd|]; simpl.
    + rewrite hreg_eqb_refl. reflexivity.
    + rewrite Z.eqb_refl. reflexivity.
  - assert (Hin_filt : In t (live_without d live)).
    { unfold live_without. apply filter_In. split; [exact Hin | rewrite Etd; reflexivity]. }
    specialize (Hlive t Hin_filt). unfold read_mach in Hlive.
    apply Nat.eqb_neq in Etd.
    destruct (zmap_find_nat d rm) as [rd|] eqn:Erd;
    destruct (zmap_find_nat t rm) as [rt|] eqn:Ert; simpl.
    + destruct (hreg_eqb rt rd) eqn:Er; [|exact Hlive].
      apply hreg_eqb_spec in Er. subst rt.
      exfalso. eapply Hreg; [exact Hin | exact Etd | reflexivity | exact Ert].
    + exact Hlive.
    + exact Hlive.
    + destruct (Z.eqb (slot_of t) (slot_of d)) eqn:Es; [|exact Hlive].
      apply Z.eqb_eq in Es.
      exfalso. eapply Hslot; [exact Hin | exact Etd | reflexivity | exact Ert | symmetry; exact Es].
Qed.

(** Filter `live` down to temporaries not in `ds`. *)
Fixpoint live_without_list (ds : list nat) (live : list nat) : list nat :=
  match ds with
  | [] => live
  | d :: ds' => live_without d (live_without_list ds' live)
  end.

(** Pairwise and live non-collision across a multi-definition list `ds`. *)
Fixpoint list_no_collision (rm : ZMap.t hreg) (slot_of : nat -> Z)
                           (ds : list nat) (live : list nat) : Prop :=
  match ds with
  | [] => True
  | d :: ds' =>
      dest_no_collision rm slot_of d (live_without_list ds' live) /\
      list_no_collision rm slot_of ds' live
  end.

(** Simultaneous / sequential multi-destination writes [write_mach_list]
    and [write_abs_list] preserve [state_agrees] on `live` when
    [list_no_collision] holds and `length ds = length vs`. *)
Theorem write_mach_list_sound : forall ds vs rm slot_of live tenv ms,
  length ds = length vs ->
  list_no_collision rm slot_of ds live ->
  state_agrees rm slot_of (live_without_list ds live) tenv ms ->
  state_agrees rm slot_of live (write_abs_list tenv ds vs)
               (write_mach_list rm slot_of ms ds vs).
Proof.
  induction ds as [|d ds' IH]; intros [|v vs'] rm slot_of live tenv ms Hlen Hnc Hagree;
    simpl in *; try discriminate.
  - exact Hagree.
  - injection Hlen as Hlen'. destruct Hnc as [Hd Hds'].
    apply IH; [exact Hlen' | exact Hds' |].
    apply write_mach_step_sound; [exact Hd | exact Hagree].
Qed.

(** Mid-instruction call safety condition for [RCallAfterReads]. *)
Definition call_mid_ok (rm : ZMap.t hreg) (call : rcall) (live_mid : list nat) : Prop :=
  match call with
  | RCallAfterReads => all_callee_saved rm live_mid = true
  | _ => True
  end.

(** Pre-read call safety condition for [RCallDuringReads]. *)
Definition call_pre_ok (rm : ZMap.t hreg) (call : rcall) (live_before : list nat) : Prop :=
  match call with
  | RCallDuringReads => all_callee_saved rm live_before = true
  | _ => True
  end.

(** Machine state after any helper call that precedes operand reads. *)
Definition pre_call_state (call : rcall) (arb : hreg -> Z) (ms : mach_state) : mach_state :=
  match call with
  | RCallDuringReads => clobber_call arb ms
  | _ => ms
  end.

(** Machine state after any call that follows operand reads. *)
Definition post_call_state (call : rcall) (arb : hreg -> Z) (ms : mach_state) : mach_state :=
  match call with
  | RCallNone => ms
  | RCallAfterReads | RCallDuringReads => clobber_call arb ms
  end.

(** Single-destination abstract instruction step: under
    [dest_no_collision], [call_mid_ok] and [call_pre_ok], operand reads
    agree with `tenv` and writing `d` preserves [state_agrees] on
    `live_after`. *)
Theorem check_rinst_step_sound :
  forall rm slot_of live_after d uses call f arb1 arb2 tenv ms,
  dest_no_collision rm slot_of d live_after ->
  call_mid_ok rm call (live_without d live_after) ->
  call_pre_ok rm call (uses ++ live_without d live_after) ->
  state_agrees rm slot_of (uses ++ live_without d live_after) tenv ms ->
  map (read_mach rm slot_of (pre_call_state call arb1 ms)) uses = map tenv uses /\
  state_agrees rm slot_of live_after
    (tenv_set tenv d (f (map tenv uses)))
    (write_mach rm slot_of
      (post_call_state call arb2 (pre_call_state call arb1 ms))
      d (f (map (read_mach rm slot_of (pre_call_state call arb1 ms)) uses))).
Proof.
  intros rm slot_of live_after d uses call f arb1 arb2 tenv ms Hnodup Hca Hcd Hagree.
  set (live_mid := live_without d live_after) in *.
  set (live_before := uses ++ live_mid) in *.
  set (ms_pre := pre_call_state call arb1 ms).
  assert (Hagree_pre : state_agrees rm slot_of live_before tenv ms_pre).
  { unfold ms_pre, pre_call_state. destruct call; try exact Hagree.
    apply clobber_preserves_agrees; [exact Hcd | exact Hagree]. }
  assert (Hargs : map (read_mach rm slot_of ms_pre) uses = map tenv uses).
  { apply map_ext_in. intros u Hu.
    apply Hagree_pre. unfold live_before. apply in_or_app. left. exact Hu. }
  split; [exact Hargs|].
  rewrite Hargs.
  apply write_mach_step_sound; [exact Hnodup|].
  assert (Hagree_mid : state_agrees rm slot_of live_mid tenv ms_pre).
  { intros t Ht. apply Hagree_pre. unfold live_before. apply in_or_app. right. exact Ht. }
  unfold post_call_state. destruct call.
  - exact Hagree_mid.
  - apply clobber_preserves_agrees; [exact Hca | exact Hagree_mid].
  - apply clobber_preserves_agrees.
    + simpl in Hcd. clear -Hcd. unfold live_before in Hcd.
      induction uses as [|u uses' IH]; simpl in *; [exact Hcd|].
      destruct (zmap_find_nat u rm) as [ru|].
      * destruct (hreg_callee_saved ru); [exact (IH Hcd) | discriminate].
      * exact (IH Hcd).
    + exact Hagree_mid.
Qed.

(** Lookup in [ZMap] corresponds to pair membership in [ZMap.elements]. *)
Lemma zmap_find_in_elements : forall (A : Type) (k : Z) (v : A) (m : ZMap.t A),
  ZMap.find k m = Some v <-> In (k, v) (ZMap.elements m).
Proof.
  intros A k v m.
  rewrite <- ZF.find_mapsto_iff, ZF.elements_mapsto_iff, InA_alt.
  split.
  - intros [[k' v'] [[Hk Hv] Hin]]. simpl in Hk, Hv. subst. exact Hin.
  - intros Hin. exists (k, v). split; [split; reflexivity | exact Hin].
Qed.

(** Domain unit map built by [valid_alloc] from `ZMap.elements rm`. *)
Definition rm_dom_map (rm : ZMap.t hreg) : ZMap.t unit :=
  rm_domain_acc (ZMap.elements rm) (ZMap.empty unit).

(** Helper for [rm_domain_acc] lookups. *)
Lemma rm_domain_acc_find : forall els m k,
  ZMap.find k (rm_domain_acc els m) = Some tt <->
  ZMap.find k m = Some tt \/ (exists r, In (k, r) els).
Proof.
  induction els as [|[k0 r0] els' IH]; intros m k; simpl.
  - split; [intro H; left; exact H | intros [H | [r []]]; exact H].
  - rewrite IH.
    destruct (Z.eq_dec k0 k) as [-> | Hneq].
    + rewrite ZF.add_eq_o by reflexivity.
      split; [intros _; right; exists r0; left; reflexivity | intros _; left; reflexivity].
    + rewrite ZF.add_neq_o by exact Hneq.
      split.
      * intros [Hm | [r Hin]]; [left; exact Hm | right; exists r; right; exact Hin].
      * intros [Hm | [r [Heq | Hin]]]; [left; exact Hm | injection Heq as -> _; contradiction | right; exists r; exact Hin].
Qed.

(** `t` is in `rm_dom_map rm` iff `t` is mapped to some register in `rm`. *)
Lemma rm_dom_find : forall rm t,
  zmap_find_nat t (rm_dom_map rm) = Some tt <-> zmap_find_nat t rm <> None.
Proof.
  intros rm t. unfold rm_dom_map, zmap_find_nat.
  rewrite rm_domain_acc_find, ZF.empty_o.
  split.
  - intros [H | [r Hin]]; [discriminate|].
    apply zmap_find_in_elements in Hin. congruence.
  - intro Hnn. destruct (ZMap.find (Z.of_nat t) rm) as [r|] eqn:E; [|contradiction].
    right. exists r. apply zmap_find_in_elements. exact E.
Qed.

(** Predicate tested by [filter_keep_acc]. *)
Definition keep_pred (keep : option (ZMap.t unit)) (x : nat) : bool :=
  match keep with
  | None => true
  | Some km => match zmap_find_nat x km with Some _ => true | None => false end
  end.

(** Characterization of [filter_keep_acc]. *)
Lemma filter_keep_acc_eq : forall keep xs acc,
  filter_keep_acc keep xs acc = rev acc ++ filter (keep_pred keep) xs.
Proof.
  intros keep xs. induction xs as [|x xs' IH]; intro acc; simpl.
  - unfold rev'. rewrite <- rev_alt, app_nil_r. reflexivity.
  - change (match keep with None => true | Some km => match zmap_find_nat x km with Some _ => true | None => false end end)
      with (keep_pred keep x).
    destruct (keep_pred keep x).
    + rewrite IH. simpl. rewrite <- app_assoc. reflexivity.
    + apply IH.
Qed.

(** Filtering by `Some (rm_dom_map rm)` keeps exactly the `rm`-mapped elements of `xs`. *)
Lemma filter_keep_dom_iff : forall rm xs t,
  In t (filter_keep_acc (Some (rm_dom_map rm)) xs []) <->
  In t xs /\ zmap_find_nat t rm <> None.
Proof.
  intros rm xs t. rewrite filter_keep_acc_eq. simpl.
  rewrite filter_In. unfold keep_pred. split.
  - intros [Hin Hk]. split; [exact Hin|].
    destruct (zmap_find_nat t (rm_dom_map rm)) as [[]|] eqn:Ed; [|discriminate].
    apply rm_dom_find. exact Ed.
  - intros [Hin Hnn]. split; [exact Hin|].
    apply rm_dom_find in Hnn. rewrite Hnn. reflexivity.
Qed.

(** Membership in [live_without_list]. *)
Lemma live_without_list_in : forall ds live t,
  In t (live_without_list ds live) <-> In t live /\ ~ In t ds.
Proof.
  induction ds as [|d ds' IH]; intros live t; simpl.
  - tauto.
  - unfold live_without. rewrite filter_In, IH.
    destruct (Nat.eqb_spec t d) as [-> | Hneq]; simpl; intuition congruence.
Qed.

(** Every `rm`-mapped temporary in `need` belongs to `live`. *)
Definition mapped_incl (rm : ZMap.t hreg) (need live : list nat) : Prop :=
  forall t, zmap_find_nat t rm <> None -> In t need -> In t live.

(** No unmapped write `d` in `ds` shares a physical slot with a distinct
    unmapped temporary `t <> d` in `live`. *)
Definition unmapped_slot_ok (rm : ZMap.t hreg) (slot_of : nat -> Z)
                            (ds live : list nat) : Prop :=
  forall d t, In d ds -> In t live -> t <> d ->
    zmap_find_nat d rm = None -> zmap_find_nat t rm = None ->
    slot_of d <> slot_of t.

(** [all_callee_saved] transfers from `live` to `need` under [mapped_incl]. *)
Lemma all_callee_saved_incl : forall rm need live,
  all_callee_saved rm live = true ->
  mapped_incl rm need live ->
  all_callee_saved rm need = true.
Proof.
  intros rm need live Hcs Hincl.
  induction need as [|x need' IH]; simpl; [reflexivity|].
  destruct (zmap_find_nat x rm) as [rx|] eqn:Ex.
  - assert (Hx_live : In x live).
    { apply Hincl; [congruence | left; reflexivity]. }
    rewrite (all_callee_saved_spec rm live x rx Hcs Hx_live Ex).
    apply IH. intros t Hnn Ht. apply Hincl; [exact Hnn | right; exact Ht].
  - apply IH. intros t Hnn Ht. apply Hincl; [exact Hnn | right; exact Ht].
Qed.

(** [no_dup_hregs] on `u` plus [unmapped_slot_ok] establishes [list_no_collision]. *)
Lemma no_dup_plus_slot_no_collision : forall rm slot_of ds live u,
  no_dup_hregs rm u = true ->
  (forall d, In d ds -> zmap_find_nat d rm <> None -> In d u) ->
  mapped_incl rm live u ->
  unmapped_slot_ok rm slot_of ds live ->
  list_no_collision rm slot_of ds live.
Proof.
  intros rm slot_of ds. induction ds as [|d ds' IH]; intros live u Hnd Hds Hlive Hus; simpl.
  - exact I.
  - split.
    + split.
      * intros r t Ht Hneq Hd_r Ht_r.
        apply live_without_list_in in Ht.
        assert (Hd_u : In d u) by (apply Hds; [left; reflexivity | congruence]).
        assert (Ht_u : In t u) by (apply Hlive; [congruence | exact (proj1 Ht)]).
        eapply no_dup_hregs_inj; [exact Hnd | exact Ht_u | exact Hd_u | exact Hneq | exact Ht_r | exact Hd_r].
      * intros t Ht Hneq Hd_n Ht_n Hslot_eq.
        apply live_without_list_in in Ht.
        eapply Hus; [left; reflexivity | exact (proj1 Ht) | exact Hneq | exact Hd_n | exact Ht_n | exact Hslot_eq].
    + apply (IH live u Hnd).
      * intros d' Hd' Hnn. apply Hds; [right; exact Hd' | exact Hnn].
      * exact Hlive.
      * intros d' t Hd' Ht Hneq Hd_n Ht_n.
        apply Hus; [right; exact Hd' | exact Ht | exact Hneq | exact Hd_n | exact Ht_n].
Qed.

(** Decompose [check_rinsts_rev] across `xs ++ ys` when `Some` is returned. *)
Lemma check_rinsts_rev_app_some : forall rm keep xs ys live out,
  check_rinsts_rev rm keep (xs ++ ys) live = Some out ->
  exists mid,
    check_rinsts_rev rm keep xs live = Some mid /\
    check_rinsts_rev rm keep ys mid = Some out.
Proof.
  intros rm keep xs. induction xs as [|ri xs' IH]; intros ys live out H; simpl in *.
  - exists live. split; [reflexivity | exact H].
  - destruct (negb (no_dup_hregs rm _)); [discriminate|].
    destruct (negb match ri_call ri with RCallAfterReads => _ | _ => true end); [discriminate|].
    destruct (negb (_ && no_dup_hregs rm _)); [discriminate|].
    exact (IH ys _ out H).
Qed.

(** Abstract execution parameters for one [rinst] (pure/helper evaluation
    `ie_eval` and caller-saved clobber witnesses `ie_arb1`, `ie_arb2`). *)
Record inst_exec : Type := mkInstExec {
  ie_eval : list Z -> list Z;
  ie_arb1 : hreg -> Z;
  ie_arb2 : hreg -> Z
}.

(** `ie` produces one output word per destination in `ri_defs ri`. *)
Definition inst_exec_wf (ri : rinst) (ie : inst_exec) : Prop :=
  forall xs, length (ie_eval ie xs) = length (ri_defs ri).

(** Abstract temporary-environment transition for `ri` under `ie`. *)
Definition abs_step_rinst (ri : rinst) (ie : inst_exec) (tenv : nat -> Z) : nat -> Z :=
  write_abs_list tenv (ri_defs ri) (ie_eval ie (map tenv (ri_uses ri))).

(** Machine state at the point `ri` reads its operands. *)
Definition mach_pre_rinst (ri : rinst) (ie : inst_exec) (ms : mach_state) : mach_state :=
  pre_call_state (ri_call ri) (ie_arb1 ie) ms.

(** Machine state transition for `ri` under `ie`. *)
Definition mach_step_rinst (rm : ZMap.t hreg) (slot_of : nat -> Z)
                           (ri : rinst) (ie : inst_exec) (ms : mach_state) : mach_state :=
  let ms_pre := mach_pre_rinst ri ie ms in
  write_mach_list rm slot_of
    (post_call_state (ri_call ri) (ie_arb2 ie) ms_pre)
    (ri_defs ri)
    (ie_eval ie (map (read_mach rm slot_of ms_pre) (ri_uses ri))).

(** Single multi-definition instruction step discharged directly from
    [check_rinsts_rev] acceptance on `Some (rm_dom_map rm)`. *)
Theorem check_rinst_multi_sound : forall rm slot_of ri ie live_after live_before need_after tenv ms,
  pts_wf O live_after ->
  check_rinsts_rev rm (Some (rm_dom_map rm)) [ri] live_after = Some live_before ->
  inst_exec_wf ri ie ->
  mapped_incl rm need_after live_after ->
  unmapped_slot_ok rm slot_of (ri_defs ri) need_after ->
  state_agrees rm slot_of (ri_uses ri ++ live_without_list (ri_defs ri) need_after) tenv ms ->
  pts_wf O live_before /\
  mapped_incl rm (ri_uses ri ++ live_without_list (ri_defs ri) need_after) live_before /\
  map (read_mach rm slot_of (mach_pre_rinst ri ie ms)) (ri_uses ri) = map tenv (ri_uses ri) /\
  state_agrees rm slot_of need_after (abs_step_rinst ri ie tenv) (mach_step_rinst rm slot_of ri ie ms).
Proof.
  intros rm slot_of ri ie live_after live_before need_after tenv ms
         Hwf_la Hchk Hiewf Hincl_after Hus Hagree.
  cbn [check_rinsts_rev] in Hchk. cbv zeta in Hchk.
  set (ds := nset_of_list (filter_keep_acc (Some (rm_dom_map rm)) (ri_defs ri) [])) in *.
  set (us := nset_of_list (filter_keep_acc (Some (rm_dom_map rm)) (ri_uses ri) [])) in *.
  destruct (nset_of_list_spec (filter_keep_acc (Some (rm_dom_map rm)) (ri_defs ri) []))
    as [Hwf_ds Hin_ds].
  destruct (nset_of_list_spec (filter_keep_acc (Some (rm_dom_map rm)) (ri_uses ri) []))
    as [Hwf_us Hin_us].
  fold ds in Hwf_ds, Hin_ds. fold us in Hwf_us, Hin_us.
  destruct (no_dup_hregs rm (nset_union live_after ds)) eqn:End1; [|discriminate].
  cbn [negb] in Hchk.
  set (live_mid := nset_sub live_after ds) in *.
  destruct (nset_sub_spec live_after ds Hwf_la Hwf_ds) as [Hwf_mid Hin_mid].
  fold live_mid in Hwf_mid, Hin_mid.
  destruct (match ri_call ri with RCallAfterReads => all_callee_saved rm live_mid | _ => true end)
    eqn:Ecall1; [|discriminate].
  cbn [negb] in Hchk.
  destruct (nset_union_spec live_mid us Hwf_mid Hwf_us) as [Hwf_bef Hin_bef].
  destruct (match ri_call ri with RCallDuringReads => all_callee_saved rm (nset_union live_mid us) | _ => true end
            && no_dup_hregs rm (nset_union live_mid us)) eqn:Ecall2; [|discriminate].
  cbn [negb] in Hchk. injection Hchk as <-.
  apply Bool.andb_true_iff in Ecall2. destruct Ecall2 as [Ecall2 End2].
  set (need_mid := live_without_list (ri_defs ri) need_after).
  set (need_before := ri_uses ri ++ need_mid).
  assert (Hincl_mid : mapped_incl rm need_mid live_mid).
  { intros t Hnn Ht. apply Hin_mid.
    unfold need_mid in Ht. apply live_without_list_in in Ht.
    split; [apply (Hincl_after t Hnn (proj1 Ht))|].
    intro Hds. apply Hin_ds, filter_keep_dom_iff in Hds. exact (proj2 Ht (proj1 Hds)). }
  assert (Hincl_bef : mapped_incl rm need_before (nset_union live_mid us)).
  { intros t Hnn Ht. apply Hin_bef.
    unfold need_before in Ht. apply in_app_or in Ht. destruct Ht as [Hu | Hm].
    - right. apply Hin_us, filter_keep_dom_iff. split; [exact Hu | exact Hnn].
    - left. exact (Hincl_mid t Hnn Hm). }
  split; [exact Hwf_bef | split; [exact Hincl_bef |]].
  assert (Hagree_pre : state_agrees rm slot_of need_before tenv (mach_pre_rinst ri ie ms)).
  { unfold mach_pre_rinst, pre_call_state.
    destruct (ri_call ri) eqn:Erc; try exact Hagree.
    apply clobber_preserves_agrees; [exact (all_callee_saved_incl rm need_before _ Ecall2 Hincl_bef) | exact Hagree]. }
  assert (Hargs : map (read_mach rm slot_of (mach_pre_rinst ri ie ms)) (ri_uses ri) = map tenv (ri_uses ri)).
  { apply map_ext_in. intros u Hu. apply Hagree_pre. unfold need_before. apply in_or_app. left. exact Hu. }
  split; [exact Hargs|].
  unfold abs_step_rinst, mach_step_rinst. cbv zeta. rewrite Hargs.
  destruct (nset_union_spec live_after ds Hwf_la Hwf_ds) as [_ Hin_u1].
  assert (Hnc : list_no_collision rm slot_of (ri_defs ri) need_after).
  { eapply (no_dup_plus_slot_no_collision rm slot_of (ri_defs ri) need_after (nset_union live_after ds) End1).
    - intros d Hd Hnn. apply Hin_u1. right. apply Hin_ds, filter_keep_dom_iff. split; assumption.
    - intros t Hnn Ht. apply Hin_u1. left. exact (Hincl_after t Hnn Ht).
    - exact Hus. }
  apply write_mach_list_sound; [symmetry; apply Hiewf | exact Hnc |].
  assert (Hagree_mid : state_agrees rm slot_of need_mid tenv (mach_pre_rinst ri ie ms)).
  { intros t Ht. apply Hagree_pre. unfold need_before. apply in_or_app. right. exact Ht. }
  unfold post_call_state. destruct (ri_call ri) eqn:Erc.
  - exact Hagree_mid.
  - apply clobber_preserves_agrees; [exact (all_callee_saved_incl rm need_mid live_mid Ecall1 Hincl_mid) | exact Hagree_mid].
  - apply clobber_preserves_agrees; [|exact Hagree_mid].
    apply (all_callee_saved_incl rm need_mid (nset_union live_mid us) Ecall2).
    intros t Hnn Ht. apply Hin_bef. left. exact (Hincl_mid t Hnn Ht).
Qed.

(** Backward semantic liveness across an instruction list `ris`. *)
Fixpoint insts_need (ris : list rinst) (need_end : list nat) : list nat :=
  match ris with
  | [] => need_end
  | ri :: ris' => ri_uses ri ++ live_without_list (ri_defs ri) (insts_need ris' need_end)
  end.

(** Physical frame-slot non-interference across `ris`. *)
Fixpoint insts_slot_ok (rm : ZMap.t hreg) (slot_of : nat -> Z)
                       (ris : list rinst) (need_end : list nat) : Prop :=
  match ris with
  | [] => True
  | ri :: ris' =>
      unmapped_slot_ok rm slot_of (ri_defs ri) (insts_need ris' need_end) /\
      insts_slot_ok rm slot_of ris' need_end
  end.

(** Output-length well-formedness of an instruction trace `ies` for `ris`. *)
Fixpoint insts_exec_wf (ris : list rinst) (ies : list inst_exec) : Prop :=
  match ris, ies with
  | [], [] => True
  | ri :: ris', ie :: ies' => inst_exec_wf ri ie /\ insts_exec_wf ris' ies'
  | _, _ => False
  end.

(** Abstract block-body execution over `ris`. *)
Fixpoint run_insts_abs (ris : list rinst) (ies : list inst_exec) (tenv : nat -> Z) : nat -> Z :=
  match ris, ies with
  | ri :: ris', ie :: ies' => run_insts_abs ris' ies' (abs_step_rinst ri ie tenv)
  | _, _ => tenv
  end.

(** Register-and-shared-slot block-body execution over `ris`. *)
Fixpoint run_insts_mach (rm : ZMap.t hreg) (slot_of : nat -> Z)
                        (ris : list rinst) (ies : list inst_exec) (ms : mach_state) : mach_state :=
  match ris, ies with
  | ri :: ris', ie :: ies' =>
      run_insts_mach rm slot_of ris' ies' (mach_step_rinst rm slot_of ri ie ms)
  | _, _ => ms
  end.

(** Every instruction in `ris` reads identical operand values in
    `mach_state` and `tenv`. *)
Fixpoint insts_reads_agree (rm : ZMap.t hreg) (slot_of : nat -> Z)
                           (ris : list rinst) (ies : list inst_exec)
                           (tenv : nat -> Z) (ms : mach_state) : Prop :=
  match ris, ies with
  | [], [] => True
  | ri :: ris', ie :: ies' =>
      map (read_mach rm slot_of (mach_pre_rinst ri ie ms)) (ri_uses ri) = map tenv (ri_uses ri) /\
      insts_reads_agree rm slot_of ris' ies'
        (abs_step_rinst ri ie tenv) (mach_step_rinst rm slot_of ri ie ms)
  | _, _ => False
  end.

(** Forward simulation of [check_rinsts_rev] across a full block body
    `ris` with simultaneous multi-definitions, caller-saved call clobbers
    and shared physical frame slots. *)
Theorem check_rinsts_rev_sound : forall ris ies rm slot_of live_end live0 need_end tenv0 ms0,
  pts_wf O live_end ->
  check_rinsts_rev rm (Some (rm_dom_map rm)) (rev' ris) live_end = Some live0 ->
  insts_exec_wf ris ies ->
  mapped_incl rm need_end live_end ->
  insts_slot_ok rm slot_of ris need_end ->
  pts_wf O live0 /\
  mapped_incl rm (insts_need ris need_end) live0 /\
  (state_agrees rm slot_of (insts_need ris need_end) tenv0 ms0 ->
   insts_reads_agree rm slot_of ris ies tenv0 ms0 /\
   state_agrees rm slot_of need_end (run_insts_abs ris ies tenv0)
                (run_insts_mach rm slot_of ris ies ms0)).
Proof.
  induction ris as [|ri ris' IH]; intros [|ie ies'] rm slot_of live_end live0 need_end tenv0 ms0
    Hwf_end Hchk Hiewf Hincl Hus; simpl in Hiewf; try contradiction.
  - simpl in Hchk. injection Hchk as <-.
    split; [exact Hwf_end | split; [exact Hincl | intro Hag; split; [exact I | exact Hag]]].
  - destruct Hiewf as [Hie Hies']. destruct Hus as [Hus1 Hus'].
    unfold rev' in Hchk. rewrite <- rev_alt in Hchk. simpl in Hchk.
    destruct (check_rinsts_rev_app_some rm (Some (rm_dom_map rm)) (rev ris') [ri] live_end live0 Hchk)
      as [live_mid [Erest Hchk1]].
    rewrite rev_alt in Erest; fold (rev' ris') in Erest.
    destruct (IH ies' rm slot_of live_end live_mid need_end
                 (abs_step_rinst ri ie tenv0) (mach_step_rinst rm slot_of ri ie ms0)
                 Hwf_end Erest Hies' Hincl Hus')
      as [Hwf_mid [Hincl_mid Hrun_rest]].
    (* Derive pts_wf O live0 and mapped_incl without needing state_agrees yet *)
    destruct (check_rinst_multi_sound rm slot_of ri ie live_mid live0 (insts_need ris' need_end)
                (fun _ => 0) (mkMach (fun _ => 0) (fun _ => 0))
                Hwf_mid Hchk1 Hie Hincl_mid Hus1 (fun _ _ => ltac:(unfold read_mach; destruct (zmap_find_nat _ rm); reflexivity)))
      as [Hwf0 [Hincl0 _]].
    split; [exact Hwf0 | split; [exact Hincl0 |]].
    intro Hag0.
    destruct (check_rinst_multi_sound rm slot_of ri ie live_mid live0 (insts_need ris' need_end)
                tenv0 ms0 Hwf_mid Hchk1 Hie Hincl_mid Hus1 Hag0)
      as [_ [_ [Hargs Hag_mid]]].
    destruct (Hrun_rest Hag_mid) as [Hreads' Hag_end].
    simpl. split; [split; [exact Hargs | exact Hreads'] | exact Hag_end].
Qed.

(** Synchronization invariant between `defs` map and `kill` list in [rblock_gen_kill]. *)
Definition defs_kill_sync (defs : ZMap.t unit) (kill : list nat) : Prop :=
  forall t, zmap_find_nat t defs <> None <-> In t kill.

(** [gk_defs_step] preserves [defs_kill_sync] and appends `ds` to `kill`. *)
Lemma gk_defs_step_spec : forall ds defs kill,
  defs_kill_sync defs kill ->
  defs_kill_sync (fst (gk_defs_step ds defs kill)) (snd (gk_defs_step ds defs kill)) /\
  (forall t, In t (snd (gk_defs_step ds defs kill)) <-> In t kill \/ In t ds).
Proof.
  induction ds as [|d ds' IH]; intros defs kill Hsync; simpl.
  - split; [exact Hsync | intro t; tauto].
  - assert (Hsync1 : defs_kill_sync (zmap_add_nat d tt defs) (d :: kill)).
    { intro t. unfold zmap_find_nat, zmap_add_nat.
      destruct (Nat.eq_dec t d) as [-> | Hneq].
      - rewrite ZF.add_eq_o by reflexivity. split; [intros _; left; reflexivity | intros _; discriminate].
      - rewrite ZF.add_neq_o by lia. rewrite (Hsync t). simpl. intuition congruence. }
    destruct (IH (zmap_add_nat d tt defs) (d :: kill) Hsync1) as [Hs2 Hi2].
    split; [exact Hs2 | intro t; rewrite Hi2; simpl; intuition congruence].
Qed.

(** [gk_uses_step] adds elements of `us` that are absent from `defs`. *)
Lemma gk_uses_step_spec : forall us defs gen t,
  defs_kill_sync defs [] \/ True ->
  (In t (gk_uses_step us defs gen) <->
   In t gen \/ (In t us /\ zmap_find_nat t defs = None)).
Proof.
  induction us as [|u us' IH]; intros defs gen t _; simpl.
  - tauto.
  - destruct (zmap_find_nat u defs) as [[]|] eqn:Eu.
    + rewrite (IH defs gen t (or_intror I)).
      split; [intros [Hg | [Hu Hn]]; [left; exact Hg | right; split; [right; exact Hu | exact Hn]] |].
      intros [Hg | [[<- | Hu] Hn]]; [left; exact Hg | congruence | right; split; assumption].
    + rewrite (IH defs (u :: gen) t (or_intror I)). simpl.
      split.
      * intros [[<- | Hg] | [Hu Hn]];
          [right; split; [left; reflexivity | exact Eu] | left; exact Hg | right; split; [right; exact Hu | exact Hn]].
      * intros [Hg | [[<- | Hu] Hn]]; [left; right; exact Hg | left; left; reflexivity | right; split; assumption].
Qed.

(** Monotonicity of [gk_insts_step] in `gen` and `kill`. *)
Lemma gk_insts_step_mono : forall keep ris defs gen kill,
  defs_kill_sync defs kill ->
  defs_kill_sync (fst (fst (gk_insts_step keep ris defs gen kill)))
                 (snd (gk_insts_step keep ris defs gen kill)) /\
  (forall t, In t gen -> In t (snd (fst (gk_insts_step keep ris defs gen kill)))) /\
  (forall t, In t kill -> In t (snd (gk_insts_step keep ris defs gen kill))).
Proof.
  intros keep ris. induction ris as [|ri ris' IH]; intros defs gen kill Hsync; simpl.
  - split; [exact Hsync | split; auto].
  - set (us := filter_keep_acc keep (ri_uses ri) []).
    set (ds := filter_keep_acc keep (ri_defs ri) []).
    set (gen1 := gk_uses_step us defs gen).
    pose proof (gk_defs_step_spec ds defs kill Hsync) as [Hsync1 Hkill1].
    destruct (gk_defs_step ds defs kill) as [defs1 kill1]; simpl in Hsync1, Hkill1.
    destruct (IH defs1 gen1 kill1 Hsync1) as [Hsync_end [Hgen_m Hkill_m]].
    split; [exact Hsync_end | split].
    + intros t Ht. apply Hgen_m. unfold gen1.
      apply (proj2 (gk_uses_step_spec us defs gen t (or_intror I))). left. exact Ht.
    + intros t Ht. apply Hkill_m. apply Hkill1. left. exact Ht.
Qed.

(** Backward [check_rinsts_rev] output is contained in `kill \/ gen2 \/ (lout \ kill_end)`. *)
Lemma check_rinsts_rev_gk_incl : forall ris rm keep lout juses_raw defs gen kill live_cur,
  pts_wf O lout ->
  defs_kill_sync defs kill ->
  check_rinsts_rev rm keep (rev' ris) (nset_union lout (nset_of_list juses_raw)) = Some live_cur ->
  pts_wf O live_cur /\
  (forall t, In t live_cur ->
     In t kill \/
     In t (gk_uses_step juses_raw
             (fst (fst (gk_insts_step keep ris defs gen kill)))
             (snd (fst (gk_insts_step keep ris defs gen kill)))) \/
     (In t lout /\ ~ In t (snd (gk_insts_step keep ris defs gen kill)))).
Proof.
  induction ris as [|ri ris' IH]; intros rm keep lout juses_raw defs gen kill live_cur Hlout Hsync Hchk.
  - simpl in Hchk |- *. injection Hchk as <-.
    destruct (nset_of_list_spec juses_raw) as [Hwf_j Hin_j].
    destruct (nset_union_spec lout (nset_of_list juses_raw) Hlout Hwf_j) as [Hwf_u Hin_u].
    split; [exact Hwf_u|].
    intros t Ht. apply Hin_u in Ht.
    destruct (zmap_find_nat t defs) as [[]|] eqn:Ed.
    + left. apply (Hsync t). congruence.
    + assert (Hnk : ~ In t kill) by (intro Hk; apply (Hsync t) in Hk; congruence).
      destruct Ht as [Hlo | Hj].
      * right; right; split; [exact Hlo | exact Hnk].
      * right; left. apply Hin_j in Hj.
        apply (proj2 (gk_uses_step_spec juses_raw defs gen t (or_intror I))).
        right; split; [exact Hj | exact Ed].
  - unfold rev' in Hchk; rewrite <- rev_alt in Hchk; simpl in Hchk.
    destruct (check_rinsts_rev_app_some rm keep (rev ris') [ri] (nset_union lout (nset_of_list juses_raw)) live_cur Hchk)
      as [live_after [Erest Hchk1]].
    rewrite rev_alt in Erest; fold (rev' ris') in Erest.
    cbn [gk_insts_step].
    set (us_raw := filter_keep_acc keep (ri_uses ri) []).
    set (ds_raw := filter_keep_acc keep (ri_defs ri) []).
    set (gen1 := gk_uses_step us_raw defs gen).
    pose proof (gk_defs_step_spec ds_raw defs kill Hsync) as [Hsync1 Hkill1].
    destruct (gk_defs_step ds_raw defs kill) as [defs1 kill1] eqn:Edk; simpl in Hsync1, Hkill1.
    destruct (IH rm keep lout juses_raw defs1 gen1 kill1 live_after Hlout Hsync1 Erest)
      as [Hwf_after Hincl_after].
    cbn [check_rinsts_rev] in Hchk1; cbv zeta in Hchk1.
    fold ds_raw us_raw in Hchk1.
    destruct (nset_of_list_spec ds_raw) as [Hwf_ds Hin_ds].
    destruct (nset_of_list_spec us_raw) as [Hwf_us Hin_us].
    destruct (negb (no_dup_hregs rm _)); [discriminate|].
    destruct (negb match ri_call ri with RCallAfterReads => _ | _ => true end); [discriminate|].
    destruct (negb (_ && no_dup_hregs rm _)); [discriminate|].
    injection Hchk1 as <-.
    destruct (nset_sub_spec live_after (nset_of_list ds_raw) Hwf_after Hwf_ds) as [Hwf_mid Hin_mid].
    destruct (nset_union_spec _ (nset_of_list us_raw) Hwf_mid Hwf_us) as [Hwf_cur Hin_cur].
    split; [exact Hwf_cur|].
    intros t Ht.
    destruct (zmap_find_nat t defs) as [[]|] eqn:Ed.
    + left. apply (Hsync t). congruence.
    + assert (Hnk : ~ In t kill) by (intro Hk; apply (Hsync t) in Hk; congruence).
      apply Hin_cur in Ht. destruct Ht as [Hmid | Hus].
      * apply Hin_mid in Hmid. destruct Hmid as [Haft Hnds].
        assert (Hnk1 : ~ In t kill1).
        { intro Hk1. apply Hkill1 in Hk1. destruct Hk1 as [Hk | Hd];
            [contradiction | apply Hnds, Hin_ds; exact Hd]. }
        destruct (Hincl_after t Haft) as [Hk1 | [Hg2 | Hlo]];
          [contradiction | right; left; exact Hg2 | right; right; exact Hlo].
      * apply Hin_us in Hus.
        right; left.
        destruct (gk_insts_step_mono keep ris' defs1 gen1 kill1 Hsync1) as [_ [Hgen_m _]].
        apply (proj2 (gk_uses_step_spec juses_raw _ _ t (or_intror I))).
        left. apply Hgen_m. unfold gen1.
        apply (proj2 (gk_uses_step_spec us_raw defs gen t (or_intror I))).
        right; split; [exact Hus | exact Ed].
Qed.

(** Connecting [check_rinsts_rev] directly to [rblock_gen_kill]. *)
Lemma rblock_gen_kill_live_after_phis : forall rm keep rb lout live_after_phis,
  pts_wf O lout ->
  check_rinsts_rev rm keep (rev' (rb_insts rb))
    (nset_union lout (nset_of_list (filter_keep_acc keep (rb_jump_uses rb) [])))
    = Some live_after_phis ->
  pts_wf O live_after_phis /\
  (forall t, In t live_after_phis ->
     In t (rblock_phi_defs_acc keep (rb_phis rb) []) \/
     In t (nset_union (fst (rblock_gen_kill keep rb))
                      (nset_sub lout (snd (rblock_gen_kill keep rb))))).
Proof.
  intros rm keep rb lout live_after_phis Hlout Hchk.
  unfold rblock_gen_kill.
  set (pdefs := rblock_phi_defs_acc keep (rb_phis rb) []).
  assert (Hempty_sync : defs_kill_sync (ZMap.empty unit) []).
  { intro t. unfold zmap_find_nat. rewrite ZF.empty_o. simpl. split; [congruence | contradiction]. }
  pose proof (gk_defs_step_spec pdefs (ZMap.empty unit) [] Hempty_sync) as [Hsync0 Hkill0].
  destruct (gk_defs_step pdefs (ZMap.empty unit) []) as [defs0 kill0]; simpl in Hsync0, Hkill0.
  set (juses := filter_keep_acc keep (rb_jump_uses rb) []).
  destruct (check_rinsts_rev_gk_incl (rb_insts rb) rm keep lout juses defs0 [] kill0
              live_after_phis Hlout Hsync0 Hchk) as [Hwf Hincl].
  destruct (gk_insts_step keep (rb_insts rb) defs0 [] kill0) as [[defs1 gen1] kill1]; simpl in Hincl |- *.
  set (gen2 := gk_uses_step juses defs1 gen1) in *.
  destruct (nset_of_list_spec gen2) as [Hwf_g Hin_g].
  destruct (nset_of_list_spec kill1) as [Hwf_k Hin_k].
  destruct (nset_sub_spec lout (nset_of_list kill1) Hlout Hwf_k) as [Hwf_sub Hin_sub].
  destruct (nset_union_spec (nset_of_list gen2) (nset_sub lout (nset_of_list kill1)) Hwf_g Hwf_sub)
    as [_ Hin_u].
  split; [exact Hwf|].
  intros t Ht.
  destruct (Hincl t Ht) as [Hk0 | [Hg2 | [Hlo Hnk1]]].
  - left. apply Hkill0 in Hk0. destruct Hk0 as [[] | Hp]; exact Hp.
  - right. apply Hin_u. left. apply Hin_g. exact Hg2.
  - right. apply Hin_u. right. apply Hin_sub.
    split; [exact Hlo | intro Hk; apply Hnk1, Hin_k; exact Hk].
Qed.

(** Every block index in `rbs` equals its sequential position starting at `idx`. *)
Fixpoint rblocks_indexed (idx : nat) (rbs : list rblock) : Prop :=
  match rbs with
  | [] => True
  | rb :: rbs' => rb_idx rb = idx /\ rblocks_indexed (S idx) rbs'
  end.

(** Every successor index of `rb` is `< n`. *)
Definition rblock_succs_in_range (n : nat) (rb : rblock) : Prop :=
  Forall (fun sp => (fst sp < n)%nat) (rb_succs rb).

(** The entry block (if any) has no phi nodes. *)
Definition rblocks_entry_no_phis (rbs : list rblock) : Prop :=
  match rbs with
  | [] => True
  | rb0 :: _ => rb_phis rb0 = []
  end.

(** Structural well-formedness of a numbered CFG `rbs`. *)
Definition rblocks_wf (rbs : list rblock) : Prop :=
  rblocks_indexed O rbs /\
  Forall (rblock_succs_in_range (length rbs)) rbs /\
  rblocks_entry_no_phis rbs.

(** Under [rblocks_indexed], every `rb` in `rbs` has `rb_idx rb >= idx`. *)
Lemma rblocks_indexed_ge : forall rbs idx rb,
  rblocks_indexed idx rbs -> In rb rbs -> (idx <= rb_idx rb)%nat.
Proof.
  induction rbs as [|r0 rbs' IH]; intros idx rb Hind Hin; simpl in *; [contradiction|].
  destruct Hind as [Hidx Hind']. destruct Hin as [<- | Hin'].
  - lia.
  - specialize (IH (S idx) rb Hind' Hin'). lia.
Qed.

(** Under [rblocks_indexed], `nth_error` determines `In` and `rb_idx`. *)
Lemma rblocks_indexed_nth : forall rbs idx k rb,
  rblocks_indexed idx rbs ->
  nth_error rbs k = Some rb ->
  In rb rbs /\ rb_idx rb = (idx + k)%nat.
Proof.
  induction rbs as [|r0 rbs' IH]; intros idx [|k'] rb Hind Hnth; simpl in *; try discriminate.
  - destruct Hind as [Hidx _]. injection Hnth as <-. split; [left; reflexivity | lia].
  - destruct Hind as [_ Hind'].
    destruct (IH (S idx) k' rb Hind' Hnth) as [Hin Hidx].
    split; [right; exact Hin | lia].
Qed.

(** [build_rb_map] leaves keys `< idx` untouched when `rblocks_indexed idx rbs`. *)
Lemma build_rb_map_lt : forall rbs idx k m,
  rblocks_indexed idx rbs ->
  (k < idx)%nat ->
  zmap_find_nat k (build_rb_map rbs m) = zmap_find_nat k m.
Proof.
  induction rbs as [|rb rbs' IH]; intros idx k m Hind Hlt; simpl in *; [reflexivity|].
  destruct Hind as [Hidx Hind'].
  rewrite (IH (S idx) k _ Hind' ltac:(lia)).
  unfold zmap_find_nat, zmap_add_nat. rewrite ZF.add_neq_o by lia. reflexivity.
Qed.

(** [build_rb_map] maps every block in `rbs` at its `rb_idx`. *)
Lemma build_rb_map_in : forall rbs idx m rb,
  rblocks_indexed idx rbs ->
  In rb rbs ->
  zmap_find_nat (rb_idx rb) (build_rb_map rbs m) = Some rb.
Proof.
  induction rbs as [|r0 rbs' IH]; intros idx m rb Hind Hin; simpl in *; [contradiction|].
  destruct Hind as [Hidx Hind']. destruct Hin as [<- | Hin'];
    [|exact (IH (S idx) _ rb Hind' Hin')].
  rewrite (build_rb_map_lt rbs' (S idx) (rb_idx r0) _ Hind' ltac:(lia)).
  unfold zmap_find_nat, zmap_add_nat. rewrite ZF.add_eq_o by reflexivity. reflexivity.
Qed.

(** [build_gk_map] leaves keys `< idx` untouched. *)
Lemma build_gk_map_lt : forall keep rbs idx k m,
  rblocks_indexed idx rbs ->
  (k < idx)%nat ->
  zmap_find_nat k (build_gk_map keep rbs m) = zmap_find_nat k m.
Proof.
  intros keep rbs. induction rbs as [|rb rbs' IH]; intros idx k m Hind Hlt; simpl in *; [reflexivity|].
  destruct Hind as [Hidx Hind'].
  rewrite (IH (S idx) k _ Hind' ltac:(lia)).
  unfold zmap_find_nat, zmap_add_nat. rewrite ZF.add_neq_o by lia. reflexivity.
Qed.

(** [build_gk_map] maps every block in `rbs` to [rblock_gen_kill]. *)
Lemma build_gk_map_in : forall keep rbs idx m rb,
  rblocks_indexed idx rbs ->
  In rb rbs ->
  zmap_find_nat (rb_idx rb) (build_gk_map keep rbs m) = Some (rblock_gen_kill keep rb).
Proof.
  intros keep rbs. induction rbs as [|r0 rbs' IH]; intros idx m rb Hind Hin; simpl in *; [contradiction|].
  destruct Hind as [Hidx Hind']. destruct Hin as [<- | Hin'];
    [|exact (IH (S idx) _ rb Hind' Hin')].
  rewrite (build_gk_map_lt keep rbs' (S idx) (rb_idx r0) _ Hind' ltac:(lia)).
  unfold zmap_find_nat, zmap_add_nat. rewrite ZF.add_eq_o by reflexivity. reflexivity.
Qed.

(** [build_out_across_maps] leaves keys `< idx` untouched. *)
Lemma build_out_across_lt : forall keep rbm live_in rbs idx k outs across,
  rblocks_indexed idx rbs ->
  (k < idx)%nat ->
  zmap_find_nat k (fst (build_out_across_maps keep rbm live_in rbs outs across)) = zmap_find_nat k outs.
Proof.
  intros keep rbm live_in rbs.
  induction rbs as [|rb rbs' IH]; intros idx k outs across Hind Hlt; simpl in *; [reflexivity|].
  destruct Hind as [Hidx Hind'].
  destruct (succs_live_out keep rbm live_in (rb_idx rb) (rb_succs rb) [] []) as [o a].
  rewrite (IH (S idx) k _ _ Hind' ltac:(lia)).
  unfold zmap_find_nat, zmap_add_nat. rewrite ZF.add_neq_o by lia. reflexivity.
Qed.

(** [build_out_across_maps] stores `fst (succs_live_out ...)` at `rb_idx rb`. *)
Lemma build_out_across_in : forall keep rbm live_in rbs idx outs across rb,
  rblocks_indexed idx rbs ->
  In rb rbs ->
  zmap_find_nat (rb_idx rb) (fst (build_out_across_maps keep rbm live_in rbs outs across)) =
  Some (fst (succs_live_out keep rbm live_in (rb_idx rb) (rb_succs rb) [] [])).
Proof.
  intros keep rbm live_in rbs.
  induction rbs as [|r0 rbs' IH]; intros idx outs across rb Hind Hin; simpl in *; [contradiction|].
  destruct Hind as [Hidx Hind']. destruct Hin as [<- | Hin'].
  - destruct (succs_live_out keep rbm live_in (rb_idx r0) (rb_succs r0) [] []) as [o a]; simpl.
    rewrite (build_out_across_lt keep rbm live_in rbs' (S idx) (rb_idx r0) _ _ Hind' ltac:(lia)).
    unfold zmap_find_nat, zmap_add_nat. rewrite ZF.add_eq_o by reflexivity. reflexivity.
  - destruct (succs_live_out keep rbm live_in (rb_idx r0) (rb_succs r0) [] []) as [o a].
    exact (IH (S idx) _ _ rb Hind' Hin').
Qed.

(** Every ordset entry in `m` satisfies `pts_wf O`. *)
Definition zmap_pts_wf (m : ZMap.t (list nat)) : Prop :=
  forall k, pts_wf O (nset_at k m).

(** [rblock_phi_edge_uses_acc] returns a [pts_wf] ordset containing all kept edge sources. *)
Lemma rblock_phi_edge_uses_spec : forall keep bi phis acc,
  pts_wf O (rblock_phi_edge_uses_acc keep bi phis acc) /\
  (forall t,
     In t (rblock_phi_edge_uses_acc keep bi phis acc) <->
     In t acc \/
     (exists d ps, In (d, ps) phis /\ lookup_phi_edge_src bi ps = Some t /\
                   In t (filter_keep_acc keep [t] []))).
Proof.
  intros keep bi phis. induction phis as [|[d ps] phis' IH]; intro acc; simpl.
  - destruct (nset_of_list_spec acc) as [Hwf Hin].
    split; [exact Hwf | intro t; rewrite Hin; split; [left; exact H | intros [Ha | [? [? [[] _]]]]; exact Ha]].
  - destruct (lookup_phi_edge_src bi ps) as [tid|] eqn:El.
    + destruct (IH (rev_append (filter_keep_acc keep [tid] []) acc)) as [Hwf Hin].
      split; [exact Hwf|].
      intro t. rewrite Hin, rev_append_rev, in_app_iff, <- in_rev.
      split.
      * intros [[Hk | Ha] | [d' [ps' [Hp [Hl Hk']]]]].
        -- right. exists d, ps.
           assert (Heqt : t = tid).
           { rewrite filter_keep_acc_eq in Hk; simpl in Hk.
             destruct (keep_pred keep tid); simpl in Hk;
               [destruct Hk as [<- | []]; reflexivity | contradiction]. }
           subst tid. split; [left; reflexivity | split; [exact El | exact Hk]].
        -- left. exact Ha.
        -- right. exists d', ps'. split; [right; exact Hp | split; assumption].
      * intros [Ha | [d' [ps' [[Heq | Hp] [Hl Hk]]]]].
        -- left; right; exact Ha.
        -- injection Heq as <- <-. rewrite El in Hl. injection Hl as ->.
           left; left; exact Hk.
        -- right. exists d', ps'. split; [exact Hp | split; assumption].
    + destruct (IH acc) as [Hwf Hin].
      split; [exact Hwf | intro t; rewrite Hin; split].
      * intros [Ha | [d' [ps' [Hp Hl]]]]; [left; exact Ha | right; exists d', ps'; split; [right; exact Hp | exact Hl]].
      * intros [Ha | [d' [ps' [[Heq | Hp] [Hl Hk]]]]];
          [left; exact Ha | injection Heq as _ <-; congruence | right; exists d', ps'; split; [exact Hp | split; assumption]].
Qed.

(** [rblock_phi_defs_acc] returns a [pts_wf] ordset containing all kept phi destinations. *)
Lemma rblock_phi_defs_spec : forall keep phis acc,
  pts_wf O (rblock_phi_defs_acc keep phis acc) /\
  (forall t,
     In t (rblock_phi_defs_acc keep phis acc) <->
     In t acc \/ (In t (map fst phis) /\ In t (filter_keep_acc keep [t] []))).
Proof.
  intros keep phis. induction phis as [|[d ps] phis' IH]; intro acc; simpl.
  - destruct (nset_of_list_spec acc) as [Hwf Hin].
    split; [exact Hwf | intro t; rewrite Hin; tauto].
  - destruct (IH (rev_append (filter_keep_acc keep [d] []) acc)) as [Hwf Hin].
    split; [exact Hwf|].
    intro t. rewrite Hin, rev_append_rev, in_app_iff, <- in_rev.
    split.
    + intros [[Hk | Ha] | [Hm Hk]].
      * assert (Heqt : t = d).
        { rewrite filter_keep_acc_eq in Hk; simpl in Hk.
          destruct (keep_pred keep d); simpl in Hk;
            [destruct Hk as [<- | []]; reflexivity | contradiction]. }
        subst d. right. split; [left; reflexivity | exact Hk].
      * left; exact Ha.
      * right. split; [right; exact Hm | exact Hk].
    + intros [Ha | [[<- | Hm] Hk]];
        [left; right; exact Ha | left; left; exact Hk | right; split; assumption].
Qed.

(** [succs_live_out] preserves `pts_wf O` and includes every successor's
    `live_in` and phi edge uses. *)
Lemma succs_live_out_spec : forall succs keep rbm live_in bi out across,
  zmap_pts_wf live_in ->
  pts_wf O out ->
  pts_wf O (fst (succs_live_out keep rbm live_in bi succs out across)) /\
  (forall t, In t out -> In t (fst (succs_live_out keep rbm live_in bi succs out across))) /\
  (forall si is_poll t, In (si, is_poll) succs ->
     In t (nset_at si live_in) ->
     In t (fst (succs_live_out keep rbm live_in bi succs out across))) /\
  (forall si is_poll srb t, In (si, is_poll) succs ->
     zmap_find_nat si rbm = Some srb ->
     In t (rblock_phi_edge_uses_acc keep bi (rb_phis srb) []) ->
     In t (fst (succs_live_out keep rbm live_in bi succs out across))).
Proof.
  induction succs as [|[s0 p0] succs' IH]; intros keep rbm live_in bi out across Hlin Hout; simpl.
  - split; [exact Hout | split; [auto | split; intros; contradiction]].
  - set (euses := match zmap_find_nat s0 rbm with
                  | Some srb => rblock_phi_edge_uses_acc keep bi (rb_phis srb) []
                  | None => []
                  end).
    assert (Hwf_eu : pts_wf O euses).
    { unfold euses. destruct (zmap_find_nat s0 rbm) as [srb|];
        [exact (proj1 (rblock_phi_edge_uses_spec keep bi (rb_phis srb) [])) | exact I]. }
    destruct (nset_union_spec out (nset_at s0 live_in) Hout (Hlin s0)) as [Hwf_u1 Hin_u1].
    destruct (nset_union_spec (nset_union out (nset_at s0 live_in)) euses Hwf_u1 Hwf_eu)
      as [Hwf_u2 Hin_u2].
    destruct (IH keep rbm live_in bi _ (nset_union across (nset_at s0 live_in)) Hlin Hwf_u2)
      as [Hwf_f [Hmono [Hsin Heu]]].
    split; [exact Hwf_f | split; [|split]].
    + intros t Ht. apply Hmono, Hin_u2; left; apply Hin_u1; left; exact Ht.
    + intros si is_poll t [Heq | Hin'] Ht.
      * injection Heq as <- _. apply Hmono, Hin_u2; left; apply Hin_u1; right; exact Ht.
      * exact (Hsin si is_poll t Hin' Ht).
    + intros si is_poll srb t [Heq | Hin'] Hrbm Ht.
      * injection Heq as <- _. apply Hmono, Hin_u2; right.
        unfold euses. rewrite Hrbm. exact Ht.
      * exact (Heu si is_poll srb t Hin' Hrbm Ht).
Qed.

(** Once `changed = true`, [rlive_round_blocks] always returns `(_, true)`. *)
Lemma rlive_round_blocks_true : forall rev_rbs keep rbm gkm live_in,
  snd (rlive_round_blocks keep rbm gkm rev_rbs live_in true) = true.
Proof.
  induction rev_rbs as [|rb rest IH]; intros keep rbm gkm live_in; simpl; [reflexivity|].
  destruct (succs_live_out keep rbm live_in (rb_idx rb) (rb_succs rb) [] []) as [out a].
  destruct (zmap_find_nat (rb_idx rb) gkm) as [[gen kill]|]; [|apply IH].
  destruct (nset_eqb _ _); apply IH.
Qed.

(** Every block step of [rlive_round_blocks] preserves [zmap_pts_wf] when
    `gkm` entries are [pts_wf]. *)
Lemma rlive_round_blocks_wf : forall rev_rbs keep rbm gkm live_in changed,
  (forall k gen kill, zmap_find_nat k gkm = Some (gen, kill) -> pts_wf O gen /\ pts_wf O kill) ->
  zmap_pts_wf live_in ->
  zmap_pts_wf (fst (rlive_round_blocks keep rbm gkm rev_rbs live_in changed)).
Proof.
  induction rev_rbs as [|rb rest IH]; intros keep rbm gkm live_in changed Hgkm Hwf; simpl; [exact Hwf|].
  pose proof (proj1 (succs_live_out_spec (rb_succs rb) keep rbm live_in (rb_idx rb) [] [] Hwf I)) as Hout.
  destruct (succs_live_out keep rbm live_in (rb_idx rb) (rb_succs rb) [] []) as [out a]; simpl in Hout.
  destruct (zmap_find_nat (rb_idx rb) gkm) as [[gen kill]|] eqn:Eg; [|exact (IH _ _ _ _ _ Hgkm Hwf)].
  destruct (Hgkm (rb_idx rb) gen kill Eg) as [Hgen Hkill].
  destruct (nset_eqb _ _); [exact (IH _ _ _ _ _ Hgkm Hwf)|].
  apply IH; [exact Hgkm|].
  intro k. unfold nset_at, zmap_find_nat, zmap_add_nat.
  destruct (Nat.eq_dec k (rb_idx rb)) as [-> | Hneq].
  - rewrite ZF.add_eq_o by reflexivity.
    destruct (nset_sub_spec out kill Hout Hkill) as [Hsub _].
    exact (proj1 (nset_union_spec gen (nset_sub out kill) Hgen Hsub)).
  - rewrite ZF.add_neq_o by lia. exact (Hwf k).
Qed.

(** When [rlive_round_blocks] returns `(live_in, false)` from `false`, the map
    was unchanged and every block's equation holds. *)
Lemma rlive_round_blocks_unchanged : forall rev_rbs keep rbm gkm lin0 live_in,
  rlive_round_blocks keep rbm gkm rev_rbs lin0 false = (live_in, false) ->
  lin0 = live_in /\
  (forall rb gen kill, In rb rev_rbs ->
     zmap_find_nat (rb_idx rb) gkm = Some (gen, kill) ->
     nset_at (rb_idx rb) live_in =
     nset_union gen (nset_sub (fst (succs_live_out keep rbm live_in (rb_idx rb) (rb_succs rb) [] [])) kill)).
Proof.
  induction rev_rbs as [|rb rest IH]; intros keep rbm gkm lin0 live_in H; simpl in *.
  - injection H as ->. split; [reflexivity | intros rb gen kill []].
  - pose proof (rlive_round_blocks_true rest keep rbm gkm) as Htrue.
    destruct (succs_live_out keep rbm lin0 (rb_idx rb) (rb_succs rb) [] []) as [out a] eqn:Eout.
    destruct (zmap_find_nat (rb_idx rb) gkm) as [[gen kill]|] eqn:Eg.
    + destruct (nset_eqb (nset_at (rb_idx rb) lin0) (nset_union gen (nset_sub out kill))) eqn:Eeq.
      * destruct (IH keep rbm gkm lin0 live_in H) as [<- Hall].
        apply nset_eqb_spec in Eeq.
        split; [reflexivity|].
        intros rb' g' k' [<- | Hin'] Eg'.
        -- rewrite Eg in Eg'; injection Eg' as <- <-. rewrite Eout; simpl. exact Eeq.
        -- exact (Hall rb' g' k' Hin' Eg').
      * pose proof (Htrue (zmap_add_nat (rb_idx rb) (nset_union gen (nset_sub out kill)) lin0)) as Ht.
        rewrite H in Ht; simpl in Ht; discriminate.
    + destruct (IH keep rbm gkm lin0 live_in H) as [<- Hall].
      split; [reflexivity|].
      intros rb' g' k' [<- | Hin'] Eg'; [congruence | exact (Hall rb' g' k' Hin' Eg')].
Qed.

(** [rlive_rounds] preserves [zmap_pts_wf] and, when `snd = false`, yields a
    fixed point of [rlive_round_blocks]. *)
Lemma rlive_rounds_fixed : forall fuel keep rbm gkm rev_rbs init live_in,
  (forall k gen kill, zmap_find_nat k gkm = Some (gen, kill) -> pts_wf O gen /\ pts_wf O kill) ->
  zmap_pts_wf init ->
  zmap_pts_wf (fst (rlive_rounds fuel keep rbm gkm rev_rbs init)) /\
  (rlive_rounds fuel keep rbm gkm rev_rbs init = (live_in, false) ->
   rlive_round_blocks keep rbm gkm rev_rbs live_in false = (live_in, false)).
Proof.
  induction fuel as [|fuel' IH]; intros keep rbm gkm rev_rbs init live_in Hgkm Hwf; simpl.
  - split.
    + exact (rlive_round_blocks_wf rev_rbs keep rbm gkm init false Hgkm Hwf).
    + intro H.
      destruct (rlive_round_blocks_unchanged rev_rbs keep rbm gkm init live_in H) as [-> _].
      exact H.
  - destruct (IH keep rbm gkm rev_rbs init (fst (rlive_rounds fuel' keep rbm gkm rev_rbs init)) Hgkm Hwf)
      as [Hwf1 Hfix1].
    destruct (rlive_rounds fuel' keep rbm gkm rev_rbs init) as [m1 [|]] eqn:Er1; simpl in *.
    + destruct (IH keep rbm gkm rev_rbs m1 live_in Hgkm Hwf1) as [Hwf2 Hfix2].
      split; [exact Hwf2 | exact Hfix2].
    + split; [exact Hwf1 | intro H; injection H as ->; exact (Hfix1 eq_refl)].
Qed.

Local Opaque rlive_rounds.

(** Soundness of converged [rblock_liveness] over any indexed CFG `rbs`. *)
Theorem rblock_liveness_sound : forall keep rbs live_in live_out across,
  rblocks_indexed O rbs ->
  rblock_liveness keep rbs = Some (live_in, live_out, across) ->
  zmap_pts_wf live_in /\
  zmap_pts_wf live_out /\
  (forall rb si is_poll t,
     In rb rbs -> In (si, is_poll) (rb_succs rb) ->
     In t (nset_at si live_in) -> In t (nset_at (rb_idx rb) live_out)) /\
  (forall rb si is_poll srb t,
     In rb rbs -> In (si, is_poll) (rb_succs rb) ->
     In srb rbs -> rb_idx srb = si ->
     In t (rblock_phi_edge_uses_acc keep (rb_idx rb) (rb_phis srb) []) ->
     In t (nset_at (rb_idx rb) live_out)) /\
  (forall rm rb live_after_phis,
     In rb rbs ->
     check_rinsts_rev rm keep (rev' (rb_insts rb))
       (nset_union (nset_at (rb_idx rb) live_out)
                   (nset_of_list (filter_keep_acc keep (rb_jump_uses rb) [])))
       = Some live_after_phis ->
     pts_wf O live_after_phis /\
     (forall t, In t live_after_phis ->
        In t (rblock_phi_defs_acc keep (rb_phis rb) []) \/
        In t (nset_at (rb_idx rb) live_in))).
Proof.
  intros keep rbs live_in live_out across Hind Hlv.
  unfold rblock_liveness in Hlv.
  set (rbm := build_rb_map rbs (ZMap.empty rblock)) in *.
  set (gkm := build_gk_map keep rbs (ZMap.empty (list nat * list nat))) in *.
  assert (Hgkm_wf : forall k gen kill, zmap_find_nat k gkm = Some (gen, kill) -> pts_wf O gen /\ pts_wf O kill).
  { intros k gen kill Hfind.
    assert (Hgen_gkm : forall bs m,
              (forall k0 g0 k1, zmap_find_nat k0 m = Some (g0, k1) -> pts_wf O g0 /\ pts_wf O k1) ->
              forall k0 g0 k1, zmap_find_nat k0 (build_gk_map keep bs m) = Some (g0, k1) ->
                pts_wf O g0 /\ pts_wf O k1).
    { induction bs as [|b bs' IHb]; intros m Hm k0 g0 k1 Hf; simpl in *; [exact (Hm k0 g0 k1 Hf)|].
      eapply IHb; [|exact Hf].
      intros k' g' kl' Hf'. unfold zmap_find_nat, zmap_add_nat in Hf'.
      destruct (Z.eq_dec (Z.of_nat (rb_idx b)) (Z.of_nat k')) as [Heq | Hneq].
      - rewrite ZF.add_eq_o in Hf' by exact Heq.
        unfold rblock_gen_kill in Hf'.
        destruct (gk_defs_step _ _ _), (gk_insts_step _ _ _ _ _).
        destruct p. injection Hf' as <- <-.
        split; [exact (proj1 (nset_of_list_spec _)) | exact (proj1 (nset_of_list_spec _))].
      - rewrite ZF.add_neq_o in Hf' by exact Hneq. exact (Hm k' g' kl' Hf'). }
    eapply (Hgen_gkm rbs (ZMap.empty _) _ k gen kill Hfind).
    Unshelve. intros k0 g0 k1 Hf0. unfold zmap_find_nat in Hf0; rewrite ZF.empty_o in Hf0; discriminate. }
  assert (Hempty_wf : zmap_pts_wf (ZMap.empty (list nat))).
  { intro k. unfold nset_at, zmap_find_nat. rewrite ZF.empty_o. exact I. }
  pose proof (rlive_rounds_fixed 40 keep rbm gkm (rev' rbs) (ZMap.empty (list nat)) live_in
                Hgkm_wf Hempty_wf) as [Hwf_r Hfix_r].
  destruct (rlive_rounds 40 keep rbm gkm (rev' rbs) (ZMap.empty (list nat)))
    as [lin_res [|]] eqn:Erounds; [discriminate|].
  cbn [fst] in Hwf_r.
  destruct (build_out_across_maps keep rbm lin_res rbs (ZMap.empty (list nat)) (ZMap.empty (list nat)))
    as [outs_res across_res] eqn:Eouts.
  cbv zeta in Hlv; injection Hlv as -> -> ->.
  pose proof (Hfix_r eq_refl) as Hround_ok.
  destruct (rlive_round_blocks_unchanged (rev' rbs) keep rbm gkm live_in live_in Hround_ok)
    as [_ Heq_blocks].
  assert (Hlout_wf : zmap_pts_wf live_out).
  { assert (Hgen_out : forall bs outs acr0,
              zmap_pts_wf outs ->
              zmap_pts_wf (fst (build_out_across_maps keep rbm live_in bs outs acr0))).
    { induction bs as [|b bs' IHb]; intros outs acr0 Ho; simpl; [exact Ho|].
      pose proof (proj1 (succs_live_out_spec (rb_succs b) keep rbm live_in (rb_idx b) [] [] Hwf_r I)) as Hob.
      destruct (succs_live_out keep rbm live_in (rb_idx b) (rb_succs b) [] []) as [o a]; simpl in Hob.
      apply IHb. intro k. unfold nset_at, zmap_find_nat, zmap_add_nat.
      destruct (Z.eq_dec (Z.of_nat (rb_idx b)) (Z.of_nat k)) as [Heq | Hneq].
      - rewrite ZF.add_eq_o by exact Heq. exact Hob.
      - rewrite ZF.add_neq_o by exact Hneq. exact (Ho k). }
    pose proof (Hgen_out rbs (ZMap.empty _) (ZMap.empty _) Hempty_wf) as Hwfo.
    rewrite Eouts in Hwfo; exact Hwfo. }
  assert (Hlout_of : forall rb, In rb rbs ->
            nset_at (rb_idx rb) live_out =
            fst (succs_live_out keep rbm live_in (rb_idx rb) (rb_succs rb) [] [])).
  { intros rb Hrb.
    pose proof (build_out_across_in keep rbm live_in rbs O (ZMap.empty _) (ZMap.empty _) rb Hind Hrb) as Ho.
    rewrite Eouts in Ho; simpl in Ho. unfold nset_at. rewrite Ho. reflexivity. }
  split; [exact Hwf_r | split; [exact Hlout_wf | split; [|split]]].
  - intros rb si is_poll t Hrb Hsucc Ht.
    rewrite (Hlout_of rb Hrb).
    destruct (succs_live_out_spec (rb_succs rb) keep rbm live_in (rb_idx rb) [] [] Hwf_r I)
      as [_ [_ [Hsin _]]].
    exact (Hsin si is_poll t Hsucc Ht).
  - intros rb si is_poll srb t Hrb Hsucc Hsrb <- Ht.
    rewrite (Hlout_of rb Hrb).
    pose proof (build_rb_map_in rbs O (ZMap.empty _) srb Hind Hsrb) as Hrbm_s.
    destruct (succs_live_out_spec (rb_succs rb) keep rbm live_in (rb_idx rb) [] [] Hwf_r I)
      as [_ [_ [_ Heu]]].
    exact (Heu (rb_idx srb) is_poll srb t Hsucc Hrbm_s Ht).
  - intros rm rb live_after_phis Hrb Hchk.
    destruct (rblock_gen_kill_live_after_phis rm keep rb (nset_at (rb_idx rb) live_out)
                live_after_phis (Hlout_wf (rb_idx rb)) Hchk) as [Hwf_lap Hincl_lap].
    split; [exact Hwf_lap|].
    assert (Hin_rev : In rb (rev' rbs)).
    { unfold rev'. rewrite <- rev_alt. apply in_rev. rewrite rev_involutive. exact Hrb. }
    pose proof (build_gk_map_in keep rbs O (ZMap.empty _) rb Hind Hrb) as Hgkm_rb.
    pose proof (Heq_blocks rb (fst (rblock_gen_kill keep rb)) (snd (rblock_gen_kill keep rb))
                  Hin_rev ltac:(rewrite <- surjective_pairing; exact Hgkm_rb)) as Hlin_eq.
    rewrite <- (Hlout_of rb Hrb) in Hlin_eq.
    intros t Ht. rewrite Hlin_eq. exact (Hincl_lap t Ht).
Qed.

Local Opaque rblock_liveness.

(** Entry block of `ebs` (if any) has no phi nodes. *)
Definition eblocks_entry_no_phis (ebs : list eblock) : Prop :=
  match ebs with
  | [] => True
  | eb0 :: _ => eb_phis eb0 = []
  end.

(** [number_eblocks_labels] produces block indices `< idx + length ebs`. *)
Lemma number_eblocks_labels_bound : forall ebs idx m,
  (forall lbl bi, nm_find lbl m = Some bi -> (bi < idx)%nat) ->
  forall lbl bi, nm_find lbl (number_eblocks_labels ebs idx m) = Some bi ->
    (bi < idx + length ebs)%nat.
Proof.
  induction ebs as [|eb ebs' IH]; intros idx m Hm lbl bi Hfind; simpl in *.
  - pose proof (Hm lbl bi Hfind). lia.
  - destruct (nm_mem (eb_label eb) m).
    + pose proof (IH (S idx) m (fun l b H => ltac:(pose proof (Hm l b H); lia)) lbl bi Hfind). lia.
    + assert (Hm' : forall l b, nm_find l (nm_add (eb_label eb) idx m) = Some b -> (b < S idx)%nat).
      { intros l b Hf. rewrite nm_find_add in Hf.
        destruct (name_eqb l (eb_label eb)); [injection Hf as <-; lia | pose proof (Hm l b Hf); lia]. }
      pose proof (IH (S idx) _ Hm' lbl bi Hfind). lia.
Qed.

(** [targets_to_succs_acc] keeps all target indices `< n`. *)
Lemma targets_to_succs_bound : forall ts bmap n acc,
  (forall lbl bi, nm_find lbl bmap = Some bi -> (bi < n)%nat) ->
  Forall (fun sp => (fst sp < n)%nat) acc ->
  Forall (fun sp => (fst sp < n)%nat) (targets_to_succs_acc bmap ts acc).
Proof.
  induction ts as [|t ts' IH]; intros bmap n acc Hbmap Hacc; simpl.
  - unfold rev'. rewrite <- rev_alt. apply Forall_rev. exact Hacc.
  - destruct (nm_find (edge_label t) bmap) as [bi|] eqn:Eb.
    + apply IH; [exact Hbmap | constructor; [simpl; exact (Hbmap (edge_label t) bi Eb) | exact Hacc]].
    + apply IH; assumption.
Qed.

(** Pure recursive specification of [eblocks_to_r_acc]. *)
Fixpoint eblocks_to_r_list (tmap bmap : nmap nat) (idx : nat) (ebs : list eblock) : list rblock :=
  match ebs with
  | [] => []
  | eb :: ebs' =>
      mkRBlock idx
        (targets_to_succs_acc bmap (ejump_targets (eb_jump eb)) [])
        (phis_to_r_acc tmap bmap (eb_phis eb) [])
        (einsts_to_r_acc tmap (eb_insts eb) [])
        (names_to_tids tmap (ejump_uses (eb_jump eb)))
      :: eblocks_to_r_list tmap bmap (S idx) ebs'
  end.

(** [eblocks_to_r_acc] equals `rev acc ++ eblocks_to_r_list`. *)
Lemma eblocks_to_r_acc_eq : forall ebs tmap bmap idx acc,
  eblocks_to_r_acc tmap bmap idx ebs acc = rev acc ++ eblocks_to_r_list tmap bmap idx ebs.
Proof.
  induction ebs as [|eb ebs' IH]; intros tmap bmap idx acc; simpl.
  - unfold rev'. rewrite <- rev_alt, app_nil_r. reflexivity.
  - rewrite IH. simpl. rewrite <- app_assoc. reflexivity.
Qed.

(** Numbering `ebs` via [number_eblocks_labels] and [eblocks_to_r_acc]
    produces a CFG satisfying [rblocks_wf] whenever the entry block has no phis. *)
Theorem eblocks_to_r_wf : forall tmap ebs,
  eblocks_entry_no_phis ebs ->
  rblocks_wf (eblocks_to_r_acc tmap (number_eblocks_labels ebs O nm_empty) O ebs []).
Proof.
  intros tmap ebs Hentry.
  set (bmap := number_eblocks_labels ebs O nm_empty).
  rewrite eblocks_to_r_acc_eq; simpl.
  assert (Hbmap : forall lbl bi, nm_find lbl bmap = Some bi -> (bi < length ebs)%nat).
  { intros lbl bi Hf.
    apply (number_eblocks_labels_bound ebs O nm_empty
             (fun l b H => ltac:(rewrite nm_find_empty in H; discriminate)) lbl bi Hf). }
  assert (Hlen : forall l idx, length (eblocks_to_r_list tmap bmap idx l) = length l).
  { induction l as [|x l' IH]; intro idx; simpl; [reflexivity | f_equal; apply IH]. }
  assert (Hind : forall l idx, rblocks_indexed idx (eblocks_to_r_list tmap bmap idx l)).
  { induction l as [|x l' IH]; intro idx; simpl; [exact I | split; [reflexivity | apply IH]]. }
  assert (Hsuccs : forall l idx,
            Forall (rblock_succs_in_range (length ebs)) (eblocks_to_r_list tmap bmap idx l)).
  { induction l as [|x l' IH]; intro idx; simpl; [constructor|].
    constructor.
    - unfold rblock_succs_in_range; simpl.
      apply (targets_to_succs_bound _ bmap (length ebs) [] Hbmap (Forall_nil _)).
    - apply IH. }
  unfold rblocks_wf. rewrite Hlen.
  split; [apply Hind | split; [apply Hsuccs |]].
  destruct ebs as [|eb0 ebs']; simpl in *; [exact I | rewrite Hentry; reflexivity].
Qed.

(** Extract raw phi destination IDs of a block. *)
Definition phi_defs_raw (phis : list (nat * list (nat * option nat))) : list nat :=
  map fst phis.

(** Extract raw temporary IDs read by `phis` on edge from `bi`. *)
Fixpoint phi_edge_uses_raw (bi : nat) (phis : list (nat * list (nat * option nat))) : list nat :=
  match phis with
  | [] => []
  | (_, ps) :: phis' =>
      match lookup_phi_edge_src bi ps with
      | Some u => u :: phi_edge_uses_raw bi phis'
      | None => phi_edge_uses_raw bi phis'
      end
  end.

(** Evaluate simultaneous phi right-hand sides on edge from `bi`, using
    `cval idx` for non-temporary (constant or global) incoming values. *)
Fixpoint eval_phis_abs (bi : nat) (cval : nat -> Z) (tenv : nat -> Z)
                       (idx : nat) (phis : list (nat * list (nat * option nat))) : list Z :=
  match phis with
  | [] => []
  | (_, ps) :: phis' =>
      let v := match lookup_phi_edge_src bi ps with
               | Some u => tenv u
               | None => cval idx
               end in
      v :: eval_phis_abs bi cval tenv (S idx) phis'
  end.

(** Abstract simultaneous phi update on edge from `bi`. *)
Definition step_phis_abs (bi : nat) (cval : nat -> Z) (tenv : nat -> Z)
                         (phis : list (nat * list (nat * option nat))) : nat -> Z :=
  write_abs_list tenv (phi_defs_raw phis) (eval_phis_abs bi cval tenv O phis).

(** Machine state after simultaneous phi moves and optional slow-path `Poll` clobber. *)
Definition step_edge_mach (rm : ZMap.t hreg) (slot_of : nat -> Z)
                          (bi : nat) (is_poll : bool) (cval : nat -> Z)
                          (poll_arb : hreg -> Z) (ms : mach_state)
                          (phis : list (nat * list (nat * option nat))) : mach_state :=
  let ms_phi :=
    write_mach_list rm slot_of ms (phi_defs_raw phis)
      (eval_phis_abs bi cval (read_mach rm slot_of ms) O phis) in
  if is_poll then clobber_call poll_arb ms_phi else ms_phi.

(** [eval_phis_abs] produces `length phis` values and agrees whenever
    [state_agrees] holds on [phi_edge_uses_raw]. *)
Lemma eval_phis_agree : forall phis rm slot_of bi cval idx tenv ms,
  state_agrees rm slot_of (phi_edge_uses_raw bi phis) tenv ms ->
  length (eval_phis_abs bi cval tenv idx phis) = length (phi_defs_raw phis) /\
  eval_phis_abs bi cval (read_mach rm slot_of ms) idx phis = eval_phis_abs bi cval tenv idx phis.
Proof.
  induction phis as [|[d ps] phis' IH]; intros rm slot_of bi cval idx tenv ms Hag; simpl in *.
  - split; reflexivity.
  - destruct (lookup_phi_edge_src bi ps) as [u|].
    + assert (Hu : read_mach rm slot_of ms u = tenv u) by (apply Hag; left; reflexivity).
      assert (Hag' : state_agrees rm slot_of (phi_edge_uses_raw bi phis') tenv ms)
        by (intros t Ht; apply Hag; right; exact Ht).
      destruct (IH rm slot_of bi cval (S idx) tenv ms Hag') as [Hlen Heq].
      split; [f_equal; exact Hlen | rewrite Hu, Heq; reflexivity].
    + destruct (IH rm slot_of bi cval (S idx) tenv ms Hag) as [Hlen Heq].
      split; [f_equal; exact Hlen | rewrite Heq; reflexivity].
Qed.

(** One block-to-block step in a numbered CFG execution trace. *)
Record cfg_edge_step : Type := mkEdgeStep {
  ces_ies      : list inst_exec;
  ces_succ     : nat;
  ces_poll     : bool;
  ces_phi_cval : nat -> Z;
  ces_poll_arb : hreg -> Z
}.

(** Structural validity of a multi-block execution trace `(tr, exit_ies)`
    starting at block index `bi` in `rbs`. *)
Fixpoint cfg_trace_valid (rbs : list rblock) (bi : nat)
                         (tr : list cfg_edge_step) (exit_ies : list inst_exec) : Prop :=
  match tr with
  | [] =>
      match nth_error rbs bi with
      | Some rb => insts_exec_wf (rb_insts rb) exit_ies
      | None => False
      end
  | es :: tr' =>
      match nth_error rbs bi with
      | Some rb =>
          insts_exec_wf (rb_insts rb) (ces_ies es) /\
          In (ces_succ es, ces_poll es) (rb_succs rb) /\
          cfg_trace_valid rbs (ces_succ es) tr' exit_ies
      | None => False
      end
  end.

(** Exact semantic live-in temporaries needed at block `bi` (after phis)
    along `(tr, exit_ies)`. *)
Fixpoint cfg_trace_need (rbs : list rblock) (bi : nat) (tr : list cfg_edge_step) : list nat :=
  match tr with
  | [] =>
      match nth_error rbs bi with
      | Some rb => insts_need (rb_insts rb) (rb_jump_uses rb)
      | None => []
      end
  | es :: tr' =>
      match nth_error rbs bi, nth_error rbs (ces_succ es) with
      | Some rb, Some srb =>
          let next_need := cfg_trace_need rbs (ces_succ es) tr' in
          let exit_need :=
            rb_jump_uses rb
            ++ phi_edge_uses_raw bi (rb_phis srb)
            ++ live_without_list (phi_defs_raw (rb_phis srb)) next_need in
          insts_need (rb_insts rb) exit_need
      | _, _ => []
      end
  end.

(** Physical frame-slot non-interference for unmapped writes along `(tr, exit_ies)`. *)
Fixpoint cfg_trace_slot_ok (rm : ZMap.t hreg) (slot_of : nat -> Z)
                           (rbs : list rblock) (bi : nat) (tr : list cfg_edge_step) : Prop :=
  match tr with
  | [] =>
      match nth_error rbs bi with
      | Some rb => insts_slot_ok rm slot_of (rb_insts rb) (rb_jump_uses rb)
      | None => True
      end
  | es :: tr' =>
      match nth_error rbs bi, nth_error rbs (ces_succ es) with
      | Some rb, Some srb =>
          let next_need := cfg_trace_need rbs (ces_succ es) tr' in
          let exit_need :=
            rb_jump_uses rb
            ++ phi_edge_uses_raw bi (rb_phis srb)
            ++ live_without_list (phi_defs_raw (rb_phis srb)) next_need in
          insts_slot_ok rm slot_of (rb_insts rb) exit_need /\
          unmapped_slot_ok rm slot_of (phi_defs_raw (rb_phis srb)) next_need /\
          cfg_trace_slot_ok rm slot_of rbs (ces_succ es) tr'
      | _, _ => True
      end
  end.

(** Complete observational agreement along `(tr, exit_ies)`: every
    instruction operand read and every block-exit jump read in `mach_state`
    equals its abstract value in `tenv`. *)
Fixpoint cfg_trace_agrees (rm : ZMap.t hreg) (slot_of : nat -> Z)
                          (rbs : list rblock) (bi : nat)
                          (tr : list cfg_edge_step) (exit_ies : list inst_exec)
                          (tenv : nat -> Z) (ms : mach_state) : Prop :=
  match tr with
  | [] =>
      match nth_error rbs bi with
      | Some rb =>
          let tenv_end := run_insts_abs (rb_insts rb) exit_ies tenv in
          let ms_end := run_insts_mach rm slot_of (rb_insts rb) exit_ies ms in
          insts_reads_agree rm slot_of (rb_insts rb) exit_ies tenv ms /\
          map (read_mach rm slot_of ms_end) (rb_jump_uses rb) = map tenv_end (rb_jump_uses rb)
      | None => False
      end
  | es :: tr' =>
      match nth_error rbs bi, nth_error rbs (ces_succ es) with
      | Some rb, Some srb =>
          let tenv_end := run_insts_abs (rb_insts rb) (ces_ies es) tenv in
          let ms_end := run_insts_mach rm slot_of (rb_insts rb) (ces_ies es) ms in
          let tenv_next := step_phis_abs bi (ces_phi_cval es) tenv_end (rb_phis srb) in
          let ms_next :=
            step_edge_mach rm slot_of bi (ces_poll es) (ces_phi_cval es)
              (ces_poll_arb es) ms_end (rb_phis srb) in
          insts_reads_agree rm slot_of (rb_insts rb) (ces_ies es) tenv ms /\
          map (read_mach rm slot_of ms_end) (rb_jump_uses rb) = map tenv_end (rb_jump_uses rb) /\
          cfg_trace_agrees rm slot_of rbs (ces_succ es) tr' exit_ies tenv_next ms_next
      | _, _ => False
      end
  end.

(** Extract single-block acceptance facts from [check_rblocks]. *)
Lemma check_rblocks_in : forall rbs rm keep rbm live_in live_out rb,
  check_rblocks rm keep rbm live_in live_out rbs = true ->
  In rb rbs ->
  exists live_after_phis,
    check_succs_polls rm keep rbm live_in (rb_succs rb) = true /\
    check_rinsts_rev rm keep (rev' (rb_insts rb))
      (nset_union (nset_at (rb_idx rb) live_out)
                  (nset_of_list (filter_keep_acc keep (rb_jump_uses rb) [])))
      = Some live_after_phis /\
    no_dup_hregs rm (nset_union live_after_phis (rblock_phi_defs_acc keep (rb_phis rb) [])) = true.
Proof.
  induction rbs as [|r0 rbs' IH]; intros rm keep rbm live_in live_out rb Hchk Hin; simpl in *; [contradiction|].
  destruct (negb _) eqn:Ehead; [discriminate|].
  apply Bool.negb_false_iff in Ehead.
  apply Bool.andb_true_iff in Ehead. destruct Ehead as [_ Hpolls].
  destruct (check_rinsts_rev rm keep (rev' (rb_insts r0)) _) as [lap0|] eqn:Erev; [|discriminate].
  destruct (no_dup_hregs rm (nset_union lap0 _)) eqn:Endp; [|discriminate].
  destruct Hin as [<- | Hin'].
  - exists lap0. split; [exact Hpolls | split; [exact Erev | exact Endp]].
  - exact (IH rm keep rbm live_in live_out rb Hchk Hin').
Qed.

(** Extract successor header checks from [check_succs_polls]. *)
Lemma check_succs_polls_in : forall succs rm keep rbm live_in si is_poll srb,
  check_succs_polls rm keep rbm live_in succs = true ->
  In (si, is_poll) succs ->
  zmap_find_nat si rbm = Some srb ->
  no_dup_hregs rm (nset_union (nset_at si live_in) (rblock_phi_defs_acc keep (rb_phis srb) [])) = true /\
  (is_poll = true ->
   all_callee_saved rm (nset_union (nset_at si live_in) (rblock_phi_defs_acc keep (rb_phis srb) [])) = true).
Proof.
  induction succs as [|[s0 p0] succs' IH]; intros rm keep rbm live_in si is_poll srb Hchk Hin Hrbm;
    simpl in *; [contradiction|].
  destruct (no_dup_hregs rm _ && _) eqn:Eok; [|discriminate].
  destruct Hin as [Heq | Hin'].
  - injection Heq as <- <-. rewrite Hrbm in Eok.
    apply Bool.andb_true_iff in Eok. destruct Eok as [Hnd Hp].
    split; [exact Hnd | intros ->; exact Hp].
  - exact (IH rm keep rbm live_in si is_poll srb Hchk Hin' Hrbm).
Qed.

(** Single-block instruction simulation when `rm` is empty. *)
Lemma empty_rm_insts_sound : forall ris ies rm slot_of ne tenv ms,
  (forall t, zmap_find_nat t rm = None) ->
  insts_exec_wf ris ies ->
  insts_slot_ok rm slot_of ris ne ->
  state_agrees rm slot_of (insts_need ris ne) tenv ms ->
  insts_reads_agree rm slot_of ris ies tenv ms /\
  state_agrees rm slot_of ne (run_insts_abs ris ies tenv) (run_insts_mach rm slot_of ris ies ms).
Proof.
  induction ris as [|ri ris' IHr]; intros [|ie ies'] rm slot_of ne t0 m0 Hempty Hwf Hus0 Hag0;
    simpl in *; try contradiction.
  - split; [exact I | exact Hag0].
  - destruct Hwf as [Hie Hies']. destruct Hus0 as [Hus1 Hus'].
    assert (Hag_pre : state_agrees rm slot_of
                        (ri_uses ri ++ live_without_list (ri_defs ri) (insts_need ris' ne))
                        t0 (mach_pre_rinst ri ie m0)).
    { unfold mach_pre_rinst, pre_call_state; destruct (ri_call ri); try exact Hag0.
      apply clobber_preserves_agrees; [|exact Hag0].
      clear -Hempty; induction (ri_uses ri ++ _) as [|x xs IHx]; simpl;
        [reflexivity | rewrite Hempty; exact IHx]. }
    assert (Hargs : map (read_mach rm slot_of (mach_pre_rinst ri ie m0)) (ri_uses ri) = map t0 (ri_uses ri))
      by (apply map_ext_in; intros u Hu; apply Hag_pre, in_or_app; left; exact Hu).
    assert (Hag_step : state_agrees rm slot_of (insts_need ris' ne)
                         (abs_step_rinst ri ie t0)
                         (mach_step_rinst rm slot_of ri ie m0)).
    { unfold abs_step_rinst, mach_step_rinst; cbv zeta; rewrite Hargs.
      apply write_mach_list_sound; [symmetry; apply Hie | |].
      - eapply (no_dup_plus_slot_no_collision rm slot_of (ri_defs ri) _ [] eq_refl);
          [intros d _ Hnn; exfalso; exact (Hnn (Hempty d))
          | intros t Hnn _; exfalso; exact (Hnn (Hempty t))
          | exact Hus1].
      - assert (Hag_mid : state_agrees rm slot_of
                            (live_without_list (ri_defs ri) (insts_need ris' ne))
                            t0 (mach_pre_rinst ri ie m0))
          by (intros t Ht; apply Hag_pre, in_or_app; right; exact Ht).
        unfold post_call_state; destruct (ri_call ri); [exact Hag_mid | |];
          (apply clobber_preserves_agrees; [|exact Hag_mid];
           clear -Hempty; induction (live_without_list _ _) as [|x xs IHx]; simpl;
             [reflexivity | rewrite Hempty; exact IHx]). }
    destruct (IHr ies' rm slot_of ne _ _ Hempty Hies' Hus' Hag_step) as [Hrd' Hag'].
    split; [split; [exact Hargs | exact Hrd'] | exact Hag'].
Qed.

(** Multi-block trace simulation when `rm` is empty (`forall t, zmap_find_nat t rm = None`). *)
Lemma empty_rm_trace_sound : forall tr exit_ies rm slot_of rbs bi tenv ms,
  (forall t, zmap_find_nat t rm = None) ->
  cfg_trace_valid rbs bi tr exit_ies ->
  cfg_trace_slot_ok rm slot_of rbs bi tr ->
  state_agrees rm slot_of (cfg_trace_need rbs bi tr) tenv ms ->
  cfg_trace_agrees rm slot_of rbs bi tr exit_ies tenv ms.
Proof.
  induction tr as [|es tr' IH]; intros exit_ies rm slot_of rbs bi tenv ms Hempty Hval Hus Hag;
    simpl in *.
  - destruct (nth_error rbs bi) as [rb|]; [|contradiction].
    destruct (empty_rm_insts_sound (rb_insts rb) exit_ies rm slot_of (rb_jump_uses rb)
                tenv ms Hempty Hval Hus Hag) as [Hrd Hag_end].
    split; [exact Hrd | apply map_ext_in; intros u Hu; exact (Hag_end u Hu)].
  - destruct (nth_error rbs bi) as [rb|]; [|contradiction].
    destruct Hval as [Hiewf [Hsucc Hval']].
    assert (Hsrb_ex : exists srb, nth_error rbs (ces_succ es) = Some srb).
    { destruct (nth_error rbs (ces_succ es)) as [srb|] eqn:Es; [exists srb; reflexivity|].
      destruct tr'; simpl in Hval'; rewrite Es in Hval'; contradiction. }
    destruct Hsrb_ex as [srb Esrb]; rewrite Esrb in *.
    destruct Hus as [Hus_insts [Hus_phis Hus']].
    set (next_need := cfg_trace_need rbs (ces_succ es) tr') in *.
    set (exit_need := rb_jump_uses rb ++ phi_edge_uses_raw bi (rb_phis srb)
                      ++ live_without_list (phi_defs_raw (rb_phis srb)) next_need) in *.
    destruct (empty_rm_insts_sound (rb_insts rb) (ces_ies es) rm slot_of exit_need
                tenv ms Hempty Hiewf Hus_insts Hag) as [Hrd Hag_end].
    set (tenv_end := run_insts_abs (rb_insts rb) (ces_ies es) tenv) in *.
    set (ms_end := run_insts_mach rm slot_of (rb_insts rb) (ces_ies es) ms) in *.
    split; [exact Hrd | split].
    + apply map_ext_in; intros u Hu; apply Hag_end, in_or_app; left; exact Hu.
    + apply (IH exit_ies rm slot_of rbs (ces_succ es) _ _ Hempty Hval' Hus').
      assert (Hag_peu : state_agrees rm slot_of (phi_edge_uses_raw bi (rb_phis srb)) tenv_end ms_end).
      { intros u Hu; apply Hag_end, in_or_app; right; apply in_or_app; left; exact Hu. }
      destruct (eval_phis_agree (rb_phis srb) rm slot_of bi (ces_phi_cval es) O tenv_end ms_end Hag_peu)
        as [Hplen Hpeq].
      unfold step_phis_abs, step_edge_mach; cbv zeta; rewrite Hpeq.
      assert (Hag_phi : state_agrees rm slot_of next_need
                          (write_abs_list tenv_end (phi_defs_raw (rb_phis srb))
                             (eval_phis_abs bi (ces_phi_cval es) tenv_end O (rb_phis srb)))
                          (write_mach_list rm slot_of ms_end (phi_defs_raw (rb_phis srb))
                             (eval_phis_abs bi (ces_phi_cval es) tenv_end O (rb_phis srb)))).
      { apply write_mach_list_sound; [symmetry; exact Hplen | |].
        - eapply (no_dup_plus_slot_no_collision rm slot_of _ _ [] eq_refl);
            [intros d _ Hnn; exfalso; exact (Hnn (Hempty d)) | intros t Hnn _; exfalso; exact (Hnn (Hempty t)) | exact Hus_phis].
        - intros t Ht; apply Hag_end, in_or_app; right; apply in_or_app; right; exact Ht. }
      destruct (ces_poll es); [|exact Hag_phi].
      apply clobber_preserves_agrees; [|exact Hag_phi].
      clear -Hempty; induction (cfg_trace_need rbs (ces_succ es) tr') as [|x xs IHx];
        simpl; [reflexivity | rewrite Hempty; exact IHx].
Qed.

(** Header live-plus-phi-defs ordset checked at entry to block `bi`. *)
Definition rblock_header_set (rm : ZMap.t hreg) (rbs : list rblock)
                             (live_in : ZMap.t (list nat)) (bi : nat) : list nat :=
  nset_union (nset_at bi live_in)
    (match nth_error rbs bi with
     | Some rb => rblock_phi_defs_acc (Some (rm_dom_map rm)) (rb_phis rb) []
     | None => []
     end).

(** Multi-block CFG + phi + poll trace simulation from [check_rblocks]
    and converged [rblock_liveness]. *)
Theorem check_rblocks_trace_sound :
  forall tr exit_ies rm slot_of rbs live_in live_out across bi,
  rblocks_indexed O rbs ->
  rblock_liveness (Some (rm_dom_map rm)) rbs = Some (live_in, live_out, across) ->
  check_rblocks rm (Some (rm_dom_map rm)) (build_rb_map rbs (ZMap.empty rblock))
    live_in live_out rbs = true ->
  cfg_trace_valid rbs bi tr exit_ies ->
  cfg_trace_slot_ok rm slot_of rbs bi tr ->
  mapped_incl rm (cfg_trace_need rbs bi tr) (rblock_header_set rm rbs live_in bi) /\
  (forall tenv ms,
     state_agrees rm slot_of (cfg_trace_need rbs bi tr) tenv ms ->
     cfg_trace_agrees rm slot_of rbs bi tr exit_ies tenv ms).
Proof.
  induction tr as [|es tr' IH];
    intros exit_ies rm slot_of rbs live_in live_out across bi Hind Hlv Hchk Hval Hus;
    unfold rblock_header_set.
  - set (dom := Some (rm_dom_map rm)) in *.
    set (rbm := build_rb_map rbs (ZMap.empty rblock)) in *.
    destruct (rblock_liveness_sound dom rbs live_in live_out across Hind Hlv)
      as [Hwf_lin [Hwf_lout [_ [_ Hlap_incl]]]].
    simpl in Hval, Hus |- *.
    destruct (nth_error rbs bi) as [rb|] eqn:Erb; [|contradiction].
    destruct (rblocks_indexed_nth rbs O bi rb Hind Erb) as [Hrb_in Hrb_idx]; simpl in Hrb_idx.
    destruct (check_rblocks_in rbs rm dom rbm live_in live_out rb Hchk Hrb_in)
      as [lap [_ [Erev _]]].
    destruct (Hlap_incl rm rb lap Hrb_in Erev) as [Hwf_lap Hlap_hdr].
    set (juses := nset_of_list (filter_keep_acc dom (rb_jump_uses rb) [])) in *.
    destruct (nset_of_list_spec (filter_keep_acc dom (rb_jump_uses rb) [])) as [Hwf_ju Hin_ju].
    destruct (nset_union_spec (nset_at (rb_idx rb) live_out) juses (Hwf_lout _) Hwf_ju)
      as [Hwf_lend Hin_lend].
    assert (Hincl_end : mapped_incl rm (rb_jump_uses rb) (nset_union (nset_at (rb_idx rb) live_out) juses)).
    { intros t Hnn Ht. apply Hin_lend. right. apply Hin_ju, filter_keep_dom_iff. split; assumption. }
    destruct (check_rinsts_rev_sound (rb_insts rb) exit_ies rm slot_of _ lap (rb_jump_uses rb)
                (fun _ => 0) (mkMach (fun _ => 0) (fun _ => 0))
                Hwf_lend Erev Hval Hincl_end Hus)
      as [_ [Hincl0 _]].
    destruct (nset_union_spec (nset_at bi live_in) (rblock_phi_defs_acc dom (rb_phis rb) [])
                (Hwf_lin bi) (proj1 (rblock_phi_defs_spec dom (rb_phis rb) [])))
      as [_ Hin_hdr].
    split.
    + intros t Hnn Ht. apply Hin_hdr. rewrite <- Hrb_idx.
      destruct (Hlap_hdr t (Hincl0 t Hnn Ht)); [right | left]; assumption.
    + intros tenv ms Hag.
      destruct (check_rinsts_rev_sound (rb_insts rb) exit_ies rm slot_of _ lap (rb_jump_uses rb)
                  tenv ms Hwf_lend Erev Hval Hincl_end Hus)
        as [_ [_ Hrun]].
      destruct (Hrun Hag) as [Hrd Hag_end].
      split; [exact Hrd | apply map_ext_in; intros u Hu; exact (Hag_end u Hu)].
  - set (dom := Some (rm_dom_map rm)) in *.
    set (rbm := build_rb_map rbs (ZMap.empty rblock)) in *.
    destruct (rblock_liveness_sound dom rbs live_in live_out across Hind Hlv)
      as [Hwf_lin [Hwf_lout [Hlout_lin [Hlout_peu Hlap_incl]]]].
    simpl in Hval, Hus |- *.
    destruct (nth_error rbs bi) as [rb|] eqn:Erb; [|contradiction].
    destruct Hval as [Hiewf [Hsucc Hval']].
    assert (Hsrb_ex : exists srb, nth_error rbs (ces_succ es) = Some srb).
    { destruct (nth_error rbs (ces_succ es)) as [srb|] eqn:Es; [exists srb; reflexivity|].
      destruct tr'; simpl in Hval'; rewrite Es in Hval'; contradiction. }
    destruct Hsrb_ex as [srb Esrb]; rewrite Esrb in *.
    destruct Hus as [Hus_insts [Hus_phis Hus']].
    destruct (rblocks_indexed_nth rbs O bi rb Hind Erb) as [Hrb_in Hrb_idx]; simpl in Hrb_idx.
    destruct (rblocks_indexed_nth rbs O (ces_succ es) srb Hind Esrb) as [Hsrb_in Hsrb_idx]; simpl in Hsrb_idx.
    destruct (IH exit_ies rm slot_of rbs live_in live_out across (ces_succ es)
                Hind Hlv Hchk Hval' Hus')
      as [Hincl_next Hrun_next].
    unfold rblock_header_set in Hincl_next; rewrite Esrb in Hincl_next.
    set (next_need := cfg_trace_need rbs (ces_succ es) tr') in *.
    set (exit_need := rb_jump_uses rb ++ phi_edge_uses_raw bi (rb_phis srb)
                      ++ live_without_list (phi_defs_raw (rb_phis srb)) next_need) in *.
    destruct (check_rblocks_in rbs rm dom rbm live_in live_out rb Hchk Hrb_in)
      as [lap [Hpolls [Erev _]]].
    destruct (Hlap_incl rm rb lap Hrb_in Erev) as [Hwf_lap Hlap_hdr].
    set (juses := nset_of_list (filter_keep_acc dom (rb_jump_uses rb) [])) in *.
    destruct (nset_of_list_spec (filter_keep_acc dom (rb_jump_uses rb) [])) as [Hwf_ju Hin_ju].
    destruct (nset_union_spec (nset_at (rb_idx rb) live_out) juses (Hwf_lout _) Hwf_ju)
      as [Hwf_lend Hin_lend].
    destruct (nset_union_spec (nset_at (ces_succ es) live_in)
                (rblock_phi_defs_acc dom (rb_phis srb) [])
                (Hwf_lin _) (proj1 (rblock_phi_defs_spec dom (rb_phis srb) [])))
      as [_ Hin_shdr].
    assert (Hincl_exit : mapped_incl rm exit_need (nset_union (nset_at (rb_idx rb) live_out) juses)).
    { intros t Hnn Ht. apply Hin_lend.
      unfold exit_need in Ht. apply in_app_or in Ht; destruct Ht as [Hju | Ht'];
        [right; apply Hin_ju, filter_keep_dom_iff; split; assumption|].
      left. apply in_app_or in Ht'; destruct Ht' as [Hpeu | Hpass].
      - eapply (Hlout_peu rb (ces_succ es) (ces_poll es) srb t Hrb_in Hsucc Hsrb_in Hsrb_idx).
        rewrite Hrb_idx.
        apply (proj2 (rblock_phi_edge_uses_spec dom bi (rb_phis srb) [])).
        right.
        assert (Hex_phi : exists d ps, In (d, ps) (rb_phis srb) /\ lookup_phi_edge_src bi ps = Some t).
        { clear -Hpeu. induction (rb_phis srb) as [|[d ps] phis' IHp]; simpl in *; [contradiction|].
          destruct (lookup_phi_edge_src bi ps) as [u|] eqn:El.
          - destruct Hpeu as [<- | Hp']; [exists d, ps; split; [left; reflexivity | exact El]|].
            destruct (IHp Hp') as [d' [ps' [H1 H2]]]; exists d', ps'; split; [right; exact H1 | exact H2].
          - destruct (IHp Hpeu) as [d' [ps' [H1 H2]]]; exists d', ps'; split; [right; exact H1 | exact H2]. }
        destruct Hex_phi as [d [ps [Hdp Hlk]]].
        exists d, ps. split; [exact Hdp | split; [exact Hlk |]].
        apply filter_keep_dom_iff; split; [left; reflexivity | exact Hnn].
      - apply live_without_list_in in Hpass; destruct Hpass as [Hnn_next Hnot_pdef].
        pose proof (Hincl_next t Hnn Hnn_next) as Hshdr.
        apply Hin_shdr in Hshdr; destruct Hshdr as [Hlin_s | Hpdef_s].
        + exact (Hlout_lin rb (ces_succ es) (ces_poll es) t Hrb_in Hsucc Hlin_s).
        + apply (proj2 (rblock_phi_defs_spec dom (rb_phis srb) [])) in Hpdef_s.
          destruct Hpdef_s as [[] | [Hmp _]]; contradiction. }
    destruct (check_rinsts_rev_sound (rb_insts rb) (ces_ies es) rm slot_of _ lap exit_need
                (fun _ => 0) (mkMach (fun _ => 0) (fun _ => 0))
                Hwf_lend Erev Hiewf Hincl_exit Hus_insts)
      as [_ [Hincl0 _]].
    destruct (nset_union_spec (nset_at bi live_in) (rblock_phi_defs_acc dom (rb_phis rb) [])
                (Hwf_lin bi) (proj1 (rblock_phi_defs_spec dom (rb_phis rb) [])))
      as [_ Hin_hdr].
    split.
    + intros t Hnn Ht. apply Hin_hdr. rewrite <- Hrb_idx.
      destruct (Hlap_hdr t (Hincl0 t Hnn Ht)); [right | left]; assumption.
    + intros tenv ms Hag.
      destruct (check_rinsts_rev_sound (rb_insts rb) (ces_ies es) rm slot_of _ lap exit_need
                  tenv ms Hwf_lend Erev Hiewf Hincl_exit Hus_insts)
        as [_ [_ Hrun]].
      destruct (Hrun Hag) as [Hrd Hag_end].
      set (tenv_end := run_insts_abs (rb_insts rb) (ces_ies es) tenv) in *.
      set (ms_end := run_insts_mach rm slot_of (rb_insts rb) (ces_ies es) ms) in *.
      split; [exact Hrd | split].
      * apply map_ext_in; intros u Hu; apply Hag_end, in_or_app; left; exact Hu.
      * apply Hrun_next.
        pose proof (build_rb_map_in rbs O (ZMap.empty _) srb Hind Hsrb_in) as Hrbm_s.
        rewrite Hsrb_idx in Hrbm_s.
        destruct (check_succs_polls_in (rb_succs rb) rm dom rbm live_in
                    (ces_succ es) (ces_poll es) srb Hpolls Hsucc Hrbm_s)
          as [Hnd_hdr Hcs_hdr].
        assert (Hag_peu : state_agrees rm slot_of (phi_edge_uses_raw bi (rb_phis srb)) tenv_end ms_end).
        { intros u Hu; apply Hag_end, in_or_app; right; apply in_or_app; left; exact Hu. }
        destruct (eval_phis_agree (rb_phis srb) rm slot_of bi (ces_phi_cval es) O tenv_end ms_end Hag_peu)
          as [Hplen Hpeq].
        unfold step_phis_abs, step_edge_mach; cbv zeta; rewrite Hpeq.
        assert (Hag_phi : state_agrees rm slot_of next_need
                            (write_abs_list tenv_end (phi_defs_raw (rb_phis srb))
                               (eval_phis_abs bi (ces_phi_cval es) tenv_end O (rb_phis srb)))
                            (write_mach_list rm slot_of ms_end (phi_defs_raw (rb_phis srb))
                               (eval_phis_abs bi (ces_phi_cval es) tenv_end O (rb_phis srb)))).
        { apply write_mach_list_sound; [symmetry; exact Hplen | |].
          - eapply (no_dup_plus_slot_no_collision rm slot_of _ _ _ Hnd_hdr).
            + intros d Hd Hnn. apply Hin_shdr. right.
              apply (proj2 (rblock_phi_defs_spec dom (rb_phis srb) [])).
              right; split; [exact Hd | apply filter_keep_dom_iff; split; [left; reflexivity | exact Hnn]].
            + exact Hincl_next.
            + exact Hus_phis.
          - intros t Ht; apply Hag_end, in_or_app; right; apply in_or_app; right; exact Ht. }
        destruct (ces_poll es) eqn:Ep; [|exact Hag_phi].
        apply clobber_preserves_agrees; [|exact Hag_phi].
        exact (all_callee_saved_incl rm next_need _ (Hcs_hdr eq_refl) Hincl_next).
Qed.

(** Every temporary mapped by an accepted `rm` has class `W`, `L` or `P` in `cmap`. *)
Theorem valid_alloc_classes_eligible : forall cmap param_tids rbs rm t r,
  valid_alloc cmap param_tids rbs rm = true ->
  zmap_find_nat t rm = Some r ->
  zmap_find_nat t cmap = Some W \/ zmap_find_nat t cmap = Some L \/ zmap_find_nat t cmap = Some P.
Proof.
  intros cmap param_tids rbs rm t r Hval Hrm.
  unfold valid_alloc in Hval.
  apply zmap_find_in_elements in Hrm.
  destruct (ZMap.elements rm) as [|p0 els'] eqn:Eels; [contradiction|].
  destruct (classes_eligible (p0 :: els') cmap) eqn:Eel; [|discriminate].
  clear -Hrm Eel.
  unfold zmap_find_nat.
  induction (p0 :: els') as [|[k0 r0] rest IH]; simpl in *; [contradiction|].
  destruct (ZMap.find k0 cmap) as [[| | | | | | |]|] eqn:Ek; try discriminate;
    (destruct Hrm as [Heq | Hrm']; [injection Heq as <- _; rewrite Ek; auto | exact (IH Eel Hrm')]).
Qed.

(** Top-level validator forward simulation theorem ([valid_alloc]): for
    any well-formed numbered CFG `rbs` and register assignment `rm`
    accepted by [valid_alloc], and any execution trace `(tr, exit_ies)`
    from entry block `0` whose unmapped writes do not share a physical
    frame slot with simultaneously live unmapped temporaries:
    1. no two mapped parameters share a hardware register;
    2. every entry-live temporary needed by the trace (mapped or unmapped)
       belongs to `param_tids` (mapped temporaries discharged by [valid_alloc]);
    3. starting from any `(tenv0, ms0)` agreeing on `param_tids`, every
       instruction operand read and every block-exit jump read along the
       entire multi-block trace (across multi-definitions, call clobbers,
       simultaneous phi moves and `Poll` back-edges) agrees with abstract
       temporary execution. *)
Theorem valid_alloc_sound :
  forall cmap param_tids rbs rm slot_of tr exit_ies,
  rblocks_wf rbs ->
  valid_alloc cmap param_tids rbs rm = true ->
  cfg_trace_valid rbs O tr exit_ies ->
  cfg_trace_slot_ok rm slot_of rbs O tr ->
  (forall t, zmap_find_nat t rm = None -> In t (cfg_trace_need rbs O tr) -> In t param_tids) ->
  no_dup_hregs rm (nset_of_list (filter_keep_acc (Some (rm_dom_map rm)) param_tids [])) = true /\
  (forall t, In t (cfg_trace_need rbs O tr) -> In t param_tids) /\
  (forall tenv0 ms0,
     state_agrees rm slot_of param_tids tenv0 ms0 ->
     cfg_trace_agrees rm slot_of rbs O tr exit_ies tenv0 ms0).
Proof.
  intros cmap param_tids rbs rm slot_of tr exit_ies [Hind [_ Hentry_nophi]] Hval Htr Hus Hunmap_in.
  unfold valid_alloc in Hval.
  destruct (ZMap.elements rm) as [|p0 els'] eqn:Eels.
  - (* Empty `rm`: no temporary is mapped to a register *)
    assert (Hempty : forall t, zmap_find_nat t rm = None).
    { intro t. unfold zmap_find_nat.
      destruct (ZMap.find (Z.of_nat t) rm) as [r|] eqn:Ef; [|reflexivity].
      apply zmap_find_in_elements in Ef. rewrite Eels in Ef; contradiction. }
    assert (Hnd_ps : no_dup_hregs rm (nset_of_list (filter_keep_acc (Some (rm_dom_map rm)) param_tids [])) = true).
    { unfold no_dup_hregs.
      induction (nset_of_list _) as [|x xs IH]; simpl; [reflexivity | rewrite Hempty; exact IH]. }
    assert (Hin_ps : forall t, In t (cfg_trace_need rbs O tr) -> In t param_tids).
    { intros t Ht. exact (Hunmap_in t (Hempty t) Ht). }
    split; [exact Hnd_ps | split; [exact Hin_ps |]].
    intros tenv0 ms0 Hag0.
    apply (empty_rm_trace_sound tr exit_ies rm slot_of rbs O tenv0 ms0 Hempty Htr Hus).
    intros t Ht. exact (Hag0 t (Hin_ps t Ht)).
  - (* Non-empty `rm`: full dataflow liveness and `check_rblocks` verified *)
    cbv zeta in Hval.
    destruct (classes_eligible (p0 :: els') cmap); [|discriminate].
    cbn [negb] in Hval.
    assert (Edom : rm_domain_acc (p0 :: els') (ZMap.empty unit) = rm_dom_map rm).
    { unfold rm_dom_map. rewrite Eels. reflexivity. }
    rewrite Edom in Hval.
    destruct (rblock_liveness (Some (rm_dom_map rm)) rbs) as [[[live_in live_out] across]|] eqn:Elv;
      [|discriminate].
    destruct rbs as [|rb0 rbs'] eqn:Erbs.
    + simpl in Htr; destruct tr; contradiction.
    + simpl in Hind, Hentry_nophi. destruct Hind as [Hidx0 Hind'].
      rewrite Hidx0 in Hval.
      set (ps := nset_of_list (filter_keep_acc (Some (rm_dom_map rm)) param_tids [])) in *.
      destruct (nset_sub (nset_at O live_in) ps) eqn:Esub; [|discriminate].
      apply Bool.andb_true_iff in Hval. destruct Hval as [Hnd_ps Hchk_blocks].
      destruct (check_rblocks_trace_sound tr exit_ies rm slot_of (rb0 :: rbs')
                  live_in live_out across O (conj Hidx0 Hind') Elv Hchk_blocks Htr Hus)
        as [Hincl_entry Hrun].
      unfold rblock_header_set in Hincl_entry; simpl in Hincl_entry.
      rewrite Hentry_nophi in Hincl_entry; simpl in Hincl_entry.
      destruct (rblock_liveness_sound (Some (rm_dom_map rm)) (rb0 :: rbs') live_in live_out across
                  (conj Hidx0 Hind') Elv) as [Hwf_lin _].
      destruct (nset_of_list_spec (filter_keep_acc (Some (rm_dom_map rm)) param_tids []))
        as [Hwf_ps Hin_ps].
      fold ps in Hwf_ps, Hin_ps.
      destruct (nset_sub_spec (nset_at O live_in) ps (Hwf_lin O) Hwf_ps) as [_ Hin_sub].
      destruct (nset_union_spec (nset_at O live_in) (nset_of_list []) (Hwf_lin O) (proj1 (nset_of_list_spec [])))
        as [_ Hin_u0].
      assert (Hall_in_params : forall t, In t (cfg_trace_need (rb0 :: rbs') O tr) -> In t param_tids).
      { intros t Ht.
        destruct (zmap_find_nat t rm) as [r|] eqn:Erm; [|exact (Hunmap_in t Erm Ht)].
        assert (Hnn : zmap_find_nat t rm <> None) by congruence.
        pose proof (Hincl_entry t Hnn Ht) as Hu0.
        apply Hin_u0 in Hu0.
        destruct Hu0 as [Hlin0 | Hnil].
        - destruct (in_dec Nat.eq_dec t ps) as [Hps | Hnps].
          + apply Hin_ps, filter_keep_dom_iff in Hps. exact (proj1 Hps).
          + exfalso. assert (Hin_s : In t (nset_sub (nset_at O live_in) ps))
              by (apply Hin_sub; split; assumption).
            rewrite Esub in Hin_s; exact Hin_s.
        - apply (proj2 (nset_of_list_spec [])) in Hnil; contradiction. }
      split; [exact Hnd_ps | split; [exact Hall_in_params |]].
      intros tenv0 ms0 Hag0.
      apply Hrun. intros t Ht. exact (Hag0 t (Hall_in_params t Ht)).
Qed.

(** ## 3. Soundness of 3-address `lea` and immediate selection *)

(** [integer_immediate] produces a value congruent to `n` modulo
    `2^32` (`half = true`) or `2^64` (`half = false`). *)
Theorem imm32_congruent : forall half n iv,
  integer_immediate half n = Some iv ->
  iv mod (if half then two32 else two64) = n mod (if half then two32 else two64).
Proof.
  intros [|] n iv H; unfold integer_immediate in H.
  - injection H as <-.
    unfold two31, two32.
    rewrite Zminus_mod_idemp_l.
    replace (n + 2147483648 - 2147483648) with n by lia.
    reflexivity.
  - cbv zeta in H.
    destruct ((- two31 <=? _) && (_ <=? two31 - 1)) eqn:E; [|discriminate].
    injection H as <-.
    destruct ((n mod two64) >=? two63) eqn:Ege.
    + rewrite Zminus_mod_idemp_l.
      replace (n - two64) with (n + (-1) * two64) by lia.
      apply Z_mod_plus_full.
    + apply Z.mod_mod. unfold two64. lia.
Qed.

(** Immediate `add` and `lea disp(%rx)` compute `(x + n) mod M` at both
    32-bit and 64-bit widths. *)
Theorem imm32_add_mod_sound : forall half x n iv,
  integer_immediate half n = Some iv ->
  (x + iv) mod (if half then two32 else two64)
  = (x + n) mod (if half then two32 else two64).
Proof.
  intros half x n iv H.
  pose proof (imm32_congruent half n iv H) as Hc.
  pose proof (Z.add_mod x iv (if half then two32 else two64)) as H1.
  pose proof (Z.add_mod x n (if half then two32 else two64)) as H2.
  assert (Hm : (if half then two32 else two64) <> 0) by (destruct half; unfold two32, two64; lia).
  rewrite H1, H2 by exact Hm. rewrite Hc. reflexivity.
Qed.

(** Reducing modulo `2^64` and then `2^32` equals reducing modulo `2^32`. *)
Lemma mod_two64_mod_two32 : forall a,
  (a mod two64) mod two32 = a mod two32.
Proof.
  intro a.
  pose proof (Z_div_mod_eq_full a two64) as Heq.
  replace (a mod two64) with (a + (- (a / two64) * two32) * two32)
    by (unfold two32, two64 in *; lia).
  apply Z_mod_plus_full.
Qed.

(** 32-bit `Sub` via `leal (-n)(%rx), %dst`: x86-64 adds the 64-bit
    sign-extended 32-bit displacement `iv` to the 64-bit base register
    `x` modulo `2^64`, then truncates to 32 bits (`mod 2^32`). Even at
    the boundary `n = -2^31` (where `-n = 2^31` wraps to `iv = -2^31`),
    the result equals `(x - n) mod 2^32`. *)
Theorem imm32_sub_lea_w_sound : forall x n iv,
  integer_immediate true (- n) = Some iv ->
  ((x + iv) mod two64) mod two32 = (x - n) mod two32.
Proof.
  intros x n iv H.
  rewrite mod_two64_mod_two32.
  replace (x - n) with (x + (- n)) by lia.
  exact (imm32_add_mod_sound true x (- n) iv H).
Qed.

(** 64-bit `Sub` via `leaq (-n)(%rx), %dst` computes `(x - n) mod 2^64`. *)
Theorem imm32_sub_lea_l_sound : forall x n iv,
  integer_immediate false (- n) = Some iv ->
  (x + iv) mod two64 = (x - n) mod two64.
Proof.
  intros x n iv H.
  replace (x - n) with (x + (- n)) by lia.
  exact (imm32_add_mod_sound false x (- n) iv H).
Qed.

(** ## 4. Whole-scheduler parallel-move soundness *)

(** Abstract valuation of parallel-move sources under global symbol
    addresses `sym_env` and location state `env`. *)
Definition eval_pm_src (sym_env : string -> Z) (env : pm_loc -> Z)
                       (half : bool) (s : pm_src) : Z :=
  let m := if half then two32 else two64 in
  match s with
  | PsLoc l => env l mod m
  | PsConst n => n mod m
  | PsGlobal g => sym_env g mod m
  end.

(** Execute one abstract parallel move `m` against `sym_env` and `env`. *)
Definition exec_pmove_abs (sym_env : string -> Z) (env : pm_loc -> Z)
                          (m : pmove) : pm_loc -> Z :=
  let v := eval_pm_src sym_env env (pmv_half m) (pmv_src m) in
  fun l => if pm_loc_eqb l (pmv_dst m) then v else env l.

(** Reflexivity of [pm_loc_eqb]. *)
Lemma pm_loc_eqb_refl : forall l, pm_loc_eqb l l = true.
Proof.
  destruct l as [r | off |]; simpl.
  - apply hreg_eqb_refl.
  - apply Z.eqb_refl.
  - reflexivity.
Qed.

(** [pm_loc_eqb] reflects equality on [pm_loc]. *)
Lemma pm_loc_eqb_spec : forall a b, pm_loc_eqb a b = true <-> a = b.
Proof.
  intros a b. destruct a as [r1 | o1 |], b as [r2 | o2 |]; simpl;
    try (split; intro H; [discriminate | congruence]).
  - rewrite hreg_eqb_spec. split; congruence.
  - rewrite Z.eqb_eq. split; congruence.
  - split; reflexivity.
Qed.

(** Symmetry of [pm_loc_eqb]. *)
Lemma pm_loc_eqb_sym : forall a b, pm_loc_eqb a b = pm_loc_eqb b a.
Proof.
  intros a b. destruct (pm_loc_eqb a b) eqn:E1; destruct (pm_loc_eqb b a) eqn:E2; auto.
  - apply pm_loc_eqb_spec in E1. subst b. rewrite pm_loc_eqb_refl in E2. discriminate.
  - apply pm_loc_eqb_spec in E2. subst a. rewrite pm_loc_eqb_refl in E1. discriminate.
Qed.

(** Executing `m` leaves the evaluated source of `m'` unchanged when
    `m'` does not read `pmv_dst m`. *)
Lemma loc_not_read_eval_unchanged : forall sym_env env m m',
  loc_read_in_pmoves (pmv_dst m) [m'] = false ->
  eval_pm_src sym_env (exec_pmove_abs sym_env env m) (pmv_half m') (pmv_src m')
  = eval_pm_src sym_env env (pmv_half m') (pmv_src m').
Proof.
  intros sym_env env m m' Hnr. simpl in Hnr.
  unfold eval_pm_src, exec_pmove_abs.
  destruct (pmv_src m') as [l' | n | g]; try reflexivity.
  destruct (pm_loc_eqb l' (pmv_dst m)) eqn:E.
  - apply pm_loc_eqb_spec in E. subst l'. rewrite pm_loc_eqb_refl in Hnr. discriminate.
  - reflexivity.
Qed.

(** Ready-move peeling step: if `m`'s destination is not read by any
    move `m'` in `rest`, executing `m` establishes `m`'s target value
    and leaves every source in `rest` unchanged. *)
Theorem ready_pmove_step_sound : forall sym_env env m rest,
  loc_read_in_pmoves (pmv_dst m) rest = false ->
  exec_pmove_abs sym_env env m (pmv_dst m)
    = eval_pm_src sym_env env (pmv_half m) (pmv_src m) /\
  (forall m', In m' rest ->
     eval_pm_src sym_env (exec_pmove_abs sym_env env m) (pmv_half m') (pmv_src m')
     = eval_pm_src sym_env env (pmv_half m') (pmv_src m')) /\
  (forall l, l <> pmv_dst m -> exec_pmove_abs sym_env env m l = env l).
Proof.
  intros sym_env env m rest Hnr. split; [|split].
  - unfold exec_pmove_abs. rewrite pm_loc_eqb_refl. reflexivity.
  - intros m' Hin. induction rest as [|r0 rs IH]; simpl in *.
    + contradiction.
    + destruct (match pmv_src r0 with PsLoc l' => pm_loc_eqb (pmv_dst m) l' | _ => false end) eqn:Eh;
        [discriminate|].
      destruct Hin as [<- | Hin'].
      * apply loc_not_read_eval_unchanged. simpl. rewrite Eh. reflexivity.
      * apply IH; assumption.
  - intros l Hneq. unfold exec_pmove_abs.
    destruct (pm_loc_eqb l (pmv_dst m)) eqn:E; [|reflexivity].
    apply pm_loc_eqb_spec in E. contradiction.
Qed.

(** Look up the move in `ms` whose destination is `l`, if any. *)
Fixpoint find_pmove_dst (l : pm_loc) (ms : list pmove) : option pmove :=
  match ms with
  | [] => None
  | m :: ms' => if pm_loc_eqb l (pmv_dst m) then Some m else find_pmove_dst l ms'
  end.

(** Simultaneous specification of a duplicate-free parallel-move list
    `ms`: each destination `pmv_dst m` receives `m`'s source evaluated
    in the initial state `env`, while untouched locations retain `env l`. *)
Definition simul_pmoves (sym_env : string -> Z) (env : pm_loc -> Z)
                        (ms : list pmove) (l : pm_loc) : Z :=
  match find_pmove_dst l ms with
  | Some m => eval_pm_src sym_env env (pmv_half m) (pmv_src m)
  | None => env l
  end.

(** Concrete x86-64 state for the move and prologue/epilogue subset:
    allocatable [hreg]s, cycle-breaker `%rcx`, scratch `%rax`, and
    `%rbp`-relative 8-byte frame slots (`pm_slot off` is `-off(%rbp)`). *)
Record pm_mach : Type := mkPmMach {
  pm_hreg : hreg -> Z;
  pm_rcx  : Z;
  pm_rax  : Z;
  pm_slot : Z -> Z
}.

(** Project [pm_loc] values from [pm_mach]. *)
Definition pm_mach_env (st : pm_mach) (l : pm_loc) : Z :=
  match l with
  | PmReg r => pm_hreg st r
  | PmSlot off => pm_slot st off
  | PmCycleTmp => pm_rcx st
  end.

(** Every register and frame slot holds a canonical unsigned 64-bit word. *)
Definition pm_mach_canonical (st : pm_mach) : Prop :=
  forall l, 0 <= pm_mach_env st l < two64.

(** Register identifiers touched by parallel-move and save/restore emission. *)
Inductive pm_reg_id : Type :=
| PrHReg (r : hreg)
| PrRcx
| PrRax.

(** Parse a 64-bit AT&T register name into [pm_reg_id]. *)
Definition pm_reg64_id (s : string) : option pm_reg_id :=
  if String.eqb s "r10" then Some (PrHReg HR10)
  else if String.eqb s "r11" then Some (PrHReg HR11)
  else if String.eqb s "rbx" then Some (PrHReg HRbx)
  else if String.eqb s "r12" then Some (PrHReg HR12)
  else if String.eqb s "r13" then Some (PrHReg HR13)
  else if String.eqb s "r14" then Some (PrHReg HR14)
  else if String.eqb s "r15" then Some (PrHReg HR15)
  else if String.eqb s "rcx" then Some PrRcx
  else if String.eqb s "rax" then Some PrRax
  else None.

(** Parse a 32-bit AT&T register name into [pm_reg_id]. *)
Definition pm_reg32_id (s : string) : option pm_reg_id :=
  if String.eqb s "r10d" then Some (PrHReg HR10)
  else if String.eqb s "r11d" then Some (PrHReg HR11)
  else if String.eqb s "ebx" then Some (PrHReg HRbx)
  else if String.eqb s "r12d" then Some (PrHReg HR12)
  else if String.eqb s "r13d" then Some (PrHReg HR13)
  else if String.eqb s "r14d" then Some (PrHReg HR14)
  else if String.eqb s "r15d" then Some (PrHReg HR15)
  else if String.eqb s "ecx" then Some PrRcx
  else if String.eqb s "eax" then Some PrRax
  else None.

(** Parse a 32-bit (`half = true`) or 64-bit (`half = false`) register name. *)
Definition pm_reg_id_at (half : bool) (s : string) : option pm_reg_id :=
  if half then pm_reg32_id s else pm_reg64_id s.

(** Read register `id` from `st`. *)
Definition pm_get_reg (st : pm_mach) (id : pm_reg_id) : Z :=
  match id with
  | PrHReg r => pm_hreg st r
  | PrRcx => pm_rcx st
  | PrRax => pm_rax st
  end.

(** Write 64-bit value `v` (already reduced to width) into register `id`. *)
Definition pm_set_reg (st : pm_mach) (id : pm_reg_id) (v : Z) : pm_mach :=
  match id with
  | PrHReg r =>
      mkPmMach (fun r' => if hreg_eqb r' r then v else pm_hreg st r')
               (pm_rcx st) (pm_rax st) (pm_slot st)
  | PrRcx => mkPmMach (pm_hreg st) v (pm_rax st) (pm_slot st)
  | PrRax => mkPmMach (pm_hreg st) (pm_rcx st) v (pm_slot st)
  end.

(** Write 64-bit value `v` into frame slot `off` (`-off(%rbp)`). *)
Definition pm_set_slot (st : pm_mach) (off v : Z) : pm_mach :=
  mkPmMach (pm_hreg st) (pm_rcx st) (pm_rax st)
           (fun off' => if Z.eqb off' off then v else pm_slot st off').

(** Operational semantics of one emitted x86-64 move/lea [line]; returns
    `None` on any unrecognized instruction, directive, label or [todo]. *)
Definition pm_exec_line (sym_env : string -> Z) (st : pm_mach) (ln : line)
  : option pm_mach :=
  match ln with
  | Ins op (Some suf) [src_op; dst_op] =>
      if String.eqb op "mov" then
        let o_half :=
          if String.eqb suf "l" then Some true
          else if String.eqb suf "q" then Some false
          else None in
        match o_half with
        | None => None
        | Some half =>
            let m := if half then two32 else two64 in
            let o_val :=
              match src_op with
              | OImm (ELit (LInt n)) => Some (n mod m)
              | OReg sr =>
                  option_map (fun id => pm_get_reg st id mod m) (pm_reg_id_at half sr)
              | OMem (LInt disp) base =>
                  if String.eqb base "rbp" then Some (pm_slot st (- disp) mod m) else None
              | _ => None
              end in
            match o_val, dst_op with
            | Some v, OReg dr =>
                option_map (fun id => pm_set_reg st id v) (pm_reg_id_at half dr)
            | Some v, OMem (LInt disp) base =>
                if negb half && String.eqb base "rbp"
                then Some (pm_set_slot st (- disp) v)
                else None
            | _, _ => None
            end
        end
      else if String.eqb op "movabs" && String.eqb suf "q" then
        match src_op, dst_op with
        | OImm (ELit (LInt n)), OReg dr =>
            option_map (fun id => pm_set_reg st id (n mod two64)) (pm_reg64_id dr)
        | _, _ => None
        end
      else if String.eqb op "lea" && String.eqb suf "q" then
        match src_op, dst_op with
        | ORip (ELit (LSym g)), OReg dr =>
            option_map (fun id => pm_set_reg st id (sym_env g mod two64)) (pm_reg64_id dr)
        | _, _ => None
        end
      else None
  | _ => None
  end.

(** Execute a sequence of emitted [line]s sequentially. *)
Fixpoint pm_exec_lines (sym_env : string -> Z) (st : pm_mach) (ls : list line)
  : option pm_mach :=
  match ls with
  | [] => Some st
  | ln :: ls' =>
      match pm_exec_line sym_env st ln with
      | Some st' => pm_exec_lines sym_env st' ls'
      | None => None
      end
  end.

(** [pm_reg64_id] recognizes every [hreg64]. *)
Lemma pm_reg64_hreg : forall r, pm_reg64_id (hreg64 r) = Some (PrHReg r).
Proof. destruct r; reflexivity. Qed.

(** [pm_reg32_id] recognizes every [hreg32]. *)
Lemma pm_reg32_hreg : forall r, pm_reg32_id (hreg32 r) = Some (PrHReg r).
Proof. destruct r; reflexivity. Qed.

(** [pm_reg_id_at] recognizes [hreg_at] at both widths. *)
Lemma pm_reg_id_hreg_at : forall half r,
  pm_reg_id_at half (hreg_at r half) = Some (PrHReg r).
Proof. destruct half, r; reflexivity. Qed.

(** [pm_reg_id_at] recognizes `%rcx` / `%ecx`. *)
Lemma pm_reg_id_rcx : forall half,
  pm_reg_id_at half (reg_name "c" half) = Some PrRcx.
Proof. destruct half; reflexivity. Qed.

(** [pm_reg_id_at] recognizes `%rax` / `%eax`. *)
Lemma pm_reg_id_rax : forall half,
  pm_reg_id_at half (reg_name "a" half) = Some PrRax.
Proof. destruct half; reflexivity. Qed.

(** Sequential execution chains across list concatenation. *)
Lemma pm_exec_lines_app : forall sym_env ls1 ls2 st st1,
  pm_exec_lines sym_env st ls1 = Some st1 ->
  pm_exec_lines sym_env st (ls1 ++ ls2) = pm_exec_lines sym_env st1 ls2.
Proof.
  intros sym_env ls1. induction ls1 as [|ln ls1' IH]; intros ls2 st st1 H1; simpl in *.
  - injection H1 as ->. reflexivity.
  - destruct (pm_exec_line sym_env st ln) as [st'|]; [exact (IH ls2 st' st1 H1) | discriminate].
Qed.

(** No [todo] line is ever accepted by [pm_exec_line]. *)
Lemma pm_exec_line_not_todo : forall sym_env st ln st',
  pm_exec_line sym_env st ln = Some st' -> is_todo ln = false.
Proof.
  intros sym_env st ln st' H.
  destruct ln as [| | op [suf|] ops | ]; simpl in *; try discriminate; reflexivity.
Qed.

(** Any line sequence accepted by [pm_exec_lines] has `first_todo ls = None`. *)
Lemma pm_exec_lines_no_todo : forall sym_env ls st st',
  pm_exec_lines sym_env st ls = Some st' -> first_todo ls = None.
Proof.
  intros sym_env ls. induction ls as [|ln ls' IH]; intros st st' H; simpl in *.
  - reflexivity.
  - destruct (pm_exec_line sym_env st ln) as [st1|] eqn:E; [|discriminate].
    rewrite (pm_exec_line_not_todo sym_env st ln st1 E).
    eapply IH; exact H.
Qed.

(** Moduli `two32` and `two64` keep values in `[0, two64)`. *)
Lemma mod_width_in_two64 : forall (half : bool) (x : Z),
  0 <= x mod (if half then two32 else two64) < two64.
Proof.
  intros [|] x; unfold two32, two64.
  - pose proof (Z.mod_pos_bound x 4294967296 ltac:(lia)). lia.
  - apply Z.mod_pos_bound. lia.
Qed.

(** [load_const_reg] loads `n mod (if half then 2^32 else 2^64)` into target `id`. *)
Lemma load_const_reg_sound : forall sym_env st n half dst64 dst32 id,
  pm_reg64_id dst64 = Some id ->
  pm_reg32_id dst32 = Some id ->
  pm_exec_lines sym_env st (load_const_reg n half dst64 dst32) =
  Some (pm_set_reg st id (n mod (if half then two32 else two64))).
Proof.
  intros sym_env st n [|] dst64 dst32 id H64 H32; unfold load_const_reg.
  - simpl. rewrite H32. simpl.
    rewrite Z.mod_mod by (unfold two32; lia). reflexivity.
  - cbv zeta.
    set (u := n mod two64).
    set (s := if u >=? two63 then u - two64 else u).
    assert (Hu : 0 <= u < two64) by (unfold u, two64; apply Z.mod_pos_bound; lia).
    assert (Hs_mod : s mod two64 = u).
    { unfold s. destruct (u >=? two63) eqn:Ege.
      - replace (u - two64) with (u + (-1) * two64) by lia.
        rewrite Z_mod_plus_full. apply Z.mod_small. exact Hu.
      - apply Z.mod_small. exact Hu. }
    destruct ((0 <=? s) && (s <? two31)) eqn:E1.
    + apply Bool.andb_true_iff in E1. destruct E1 as [E1a E1b].
      apply Z.leb_le in E1a. apply Z.ltb_lt in E1b.
      simpl. rewrite H32. simpl.
      assert (Hs_eq : s = u).
      { unfold s in *. destruct (u >=? two63) eqn:Ege; [lia | reflexivity]. }
      rewrite Z.mod_small by (unfold two31, two32 in *; lia).
      rewrite Hs_eq. reflexivity.
    + destruct ((- two31 <=? s) && (s <? 0)) eqn:E2; simpl; rewrite H64; simpl;
        rewrite Hs_mod; reflexivity.
Qed.

(** [emit_save_cycle_tmp] copies `old` (`old <> PmCycleTmp`) into `%rcx`
    while preserving all other locations and [pm_mach_canonical]. *)
Lemma emit_save_cycle_tmp_sound : forall sym_env st old,
  pm_mach_canonical st ->
  old <> PmCycleTmp ->
  exists st1,
    pm_exec_lines sym_env st (emit_save_cycle_tmp old) = Some st1 /\
    pm_mach_canonical st1 /\
    pm_mach_env st1 PmCycleTmp = pm_mach_env st old /\
    (forall l, l <> PmCycleTmp -> pm_mach_env st1 l = pm_mach_env st l).
Proof.
  intros sym_env st [r | off |] Hcan Hneq; [| | contradiction].
  - eexists. split; [|split; [|split]].
    + simpl. rewrite pm_reg64_hreg. simpl. reflexivity.
    + intros [r' | off' |]; simpl.
      * exact (Hcan (PmReg r')).
      * exact (Hcan (PmSlot off')).
      * apply Z.mod_pos_bound. unfold two64; lia.
    + simpl. apply Z.mod_small. exact (Hcan (PmReg r)).
    + intros [r' | off' |] H; [reflexivity | reflexivity | contradiction].
  - eexists. split; [|split; [|split]].
    + simpl. reflexivity.
    + intros [r' | off' |]; simpl.
      * exact (Hcan (PmReg r')).
      * exact (Hcan (PmSlot off')).
      * apply Z.mod_pos_bound. unfold two64; lia.
    + simpl. replace (- - off) with off by lia.
      apply Z.mod_small. exact (Hcan (PmSlot off)).
    + intros [r' | off' |] H; [reflexivity | reflexivity | contradiction].
Qed.

(** Well-formedness of one [pmove] in location state `env`: non-scratch
    destination, 64-bit global addresses, and canonical 32-bit zero
    extension whenever `pmv_src_w m = true`. *)
Definition pmove_wf (env : pm_loc -> Z) (m : pmove) : Prop :=
  pmv_dst m <> PmCycleTmp /\
  match pmv_src m with
  | PsGlobal _ => pmv_half m = false
  | PsLoc l => pmv_src_w m = true -> env l < two32
  | PsConst _ => True
  end.

(** [emit_one_pmove] executes cleanly in [pm_exec_lines], preserves
    [pm_mach_canonical], sets `pmv_dst m` to [eval_pm_src], and preserves
    every other [pm_loc] (including `PmCycleTmp`, using `%rax` only as scratch). *)
Lemma emit_one_pmove_sound : forall sym_env st m,
  pm_mach_canonical st ->
  pmove_wf (pm_mach_env st) m ->
  exists st1,
    pm_exec_lines sym_env st (emit_one_pmove m) = Some st1 /\
    pm_mach_canonical st1 /\
    pm_mach_env st1 (pmv_dst m) = eval_pm_src sym_env (pm_mach_env st) (pmv_half m) (pmv_src m) /\
    (forall l, l <> pmv_dst m -> pm_mach_env st1 l = pm_mach_env st l).
Proof.
  intros sym_env st [half src_w [rd | off |] src] Hcan [Hdst Hsrc]; simpl in *; [| | contradiction].
  - destruct src as [[rs | soff |] | n | g].
    + destruct half; eexists; (split; [|split; [|split]]).
      * unfold emit_one_pmove; simpl. rewrite !pm_reg32_hreg; simpl; reflexivity.
      * intros [r' | off' |]; simpl; [destruct (hreg_eqb r' rd); [apply (mod_width_in_two64 true) | exact (Hcan (PmReg r'))] | exact (Hcan (PmSlot off')) | exact (Hcan PmCycleTmp)].
      * simpl. rewrite hreg_eqb_refl. reflexivity.
      * intros [r' | off' |] Hneq; simpl; [|reflexivity | reflexivity].
        destruct (hreg_eqb r' rd) eqn:E; [apply hreg_eqb_spec in E; subst; contradiction | reflexivity].
      * unfold emit_one_pmove; simpl. rewrite !pm_reg64_hreg; simpl; reflexivity.
      * intros [r' | off' |]; simpl; [destruct (hreg_eqb r' rd); [apply (mod_width_in_two64 false) | exact (Hcan (PmReg r'))] | exact (Hcan (PmSlot off')) | exact (Hcan PmCycleTmp)].
      * simpl. rewrite hreg_eqb_refl. reflexivity.
      * intros [r' | off' |] Hneq; simpl; [|reflexivity | reflexivity].
        destruct (hreg_eqb r' rd) eqn:E; [apply hreg_eqb_spec in E; subst; contradiction | reflexivity].
    + destruct half; eexists; (split; [|split; [|split]]).
      * unfold emit_one_pmove; simpl. rewrite pm_reg32_hreg; simpl; reflexivity.
      * intros [r' | off' |]; simpl; [destruct (hreg_eqb r' rd); [apply (mod_width_in_two64 true) | exact (Hcan (PmReg r'))] | exact (Hcan (PmSlot off')) | exact (Hcan PmCycleTmp)].
      * simpl. rewrite hreg_eqb_refl. replace (- - soff) with soff by lia. reflexivity.
      * intros [r' | off' |] Hneq; simpl; [|reflexivity | reflexivity].
        destruct (hreg_eqb r' rd) eqn:E; [apply hreg_eqb_spec in E; subst; contradiction | reflexivity].
      * unfold emit_one_pmove; simpl. rewrite pm_reg64_hreg; simpl; reflexivity.
      * intros [r' | off' |]; simpl; [destruct (hreg_eqb r' rd); [apply (mod_width_in_two64 false) | exact (Hcan (PmReg r'))] | exact (Hcan (PmSlot off')) | exact (Hcan PmCycleTmp)].
      * simpl. rewrite hreg_eqb_refl. replace (- - soff) with soff by lia. reflexivity.
      * intros [r' | off' |] Hneq; simpl; [|reflexivity | reflexivity].
        destruct (hreg_eqb r' rd) eqn:E; [apply hreg_eqb_spec in E; subst; contradiction | reflexivity].
    + destruct half; eexists; (split; [|split; [|split]]).
      * unfold emit_one_pmove; simpl. rewrite pm_reg32_hreg; simpl; reflexivity.
      * intros [r' | off' |]; simpl; [destruct (hreg_eqb r' rd); [apply (mod_width_in_two64 true) | exact (Hcan (PmReg r'))] | exact (Hcan (PmSlot off')) | exact (Hcan PmCycleTmp)].
      * simpl. rewrite hreg_eqb_refl. reflexivity.
      * intros [r' | off' |] Hneq; simpl; [|reflexivity | reflexivity].
        destruct (hreg_eqb r' rd) eqn:E; [apply hreg_eqb_spec in E; subst; contradiction | reflexivity].
      * unfold emit_one_pmove; simpl. rewrite pm_reg64_hreg; simpl; reflexivity.
      * intros [r' | off' |]; simpl; [destruct (hreg_eqb r' rd); [apply (mod_width_in_two64 false) | exact (Hcan (PmReg r'))] | exact (Hcan (PmSlot off')) | exact (Hcan PmCycleTmp)].
      * simpl. rewrite hreg_eqb_refl. reflexivity.
      * intros [r' | off' |] Hneq; simpl; [|reflexivity | reflexivity].
        destruct (hreg_eqb r' rd) eqn:E; [apply hreg_eqb_spec in E; subst; contradiction | reflexivity].
    + eexists. split; [|split; [|split]].
      * unfold emit_one_pmove; simpl.
        exact (load_const_reg_sound sym_env st n half (hreg64 rd) (hreg32 rd) (PrHReg rd)
                 (pm_reg64_hreg rd) (pm_reg32_hreg rd)).
      * intros [r' | off' |]; simpl.
        -- destruct (hreg_eqb r' rd); [apply mod_width_in_two64 | exact (Hcan (PmReg r'))].
        -- exact (Hcan (PmSlot off')).
        -- exact (Hcan PmCycleTmp).
      * simpl. rewrite hreg_eqb_refl. reflexivity.
      * intros [r' | off' |] Hneq; simpl; [|reflexivity | reflexivity].
        destruct (hreg_eqb r' rd) eqn:E; [|reflexivity].
        apply hreg_eqb_spec in E. subst r'. contradiction.
    + subst half. eexists. split; [|split; [|split]].
      * unfold emit_one_pmove; simpl. rewrite pm_reg64_hreg; simpl; reflexivity.
      * intros [r' | off' |]; simpl.
        -- destruct (hreg_eqb r' rd); [apply Z.mod_pos_bound; unfold two64; lia | exact (Hcan (PmReg r'))].
        -- exact (Hcan (PmSlot off')).
        -- exact (Hcan PmCycleTmp).
      * simpl. rewrite hreg_eqb_refl. reflexivity.
      * intros [r' | off' |] Hneq; simpl; [|reflexivity | reflexivity].
        destruct (hreg_eqb r' rd) eqn:E; [|reflexivity].
        apply hreg_eqb_spec in E. subst r'. contradiction.
  - destruct src as [[rs | soff |] | n | g].
    + destruct half.
      * eexists. split; [|split; [|split]].
        -- unfold emit_one_pmove; simpl. rewrite pm_reg32_hreg; simpl; reflexivity.
        -- intros [r' | off' |]; simpl; [exact (Hcan (PmReg r')) | | exact (Hcan PmCycleTmp)].
           replace (- - off) with off by lia.
           destruct (Z.eqb off' off); [apply Z.mod_pos_bound; unfold two64; lia | exact (Hcan (PmSlot off'))].
        -- simpl. replace (- - off) with off by lia. rewrite Z.eqb_refl.
           apply Z.mod_small. pose proof (Z.mod_pos_bound (pm_hreg st rs) two32 ltac:(unfold two32; lia)).
           unfold two32, two64 in *; lia.
        -- intros [r' | off' |] Hneq; simpl; [reflexivity | | reflexivity].
           replace (- - off) with off by lia.
           destruct (Z.eqb off' off) eqn:E; [apply Z.eqb_eq in E; subst; contradiction | reflexivity].
      * eexists. split; [|split; [|split]].
        -- unfold emit_one_pmove; simpl. rewrite pm_reg64_hreg; simpl; reflexivity.
        -- intros [r' | off' |]; simpl; [exact (Hcan (PmReg r')) | | exact (Hcan PmCycleTmp)].
           replace (- - off) with off by lia.
           destruct (Z.eqb off' off); [apply Z.mod_pos_bound; unfold two64; lia | exact (Hcan (PmSlot off'))].
        -- simpl. replace (- - off) with off by lia. rewrite Z.eqb_refl. reflexivity.
        -- intros [r' | off' |] Hneq; simpl; [reflexivity | | reflexivity].
           replace (- - off) with off by lia.
           destruct (Z.eqb off' off) eqn:E; [apply Z.eqb_eq in E; subst; contradiction | reflexivity].
    + destruct half; eexists; (split; [|split; [|split]]).
      * unfold emit_one_pmove; simpl; reflexivity.
      * intros [r' | off' |]; simpl; [exact (Hcan (PmReg r')) | | exact (Hcan PmCycleTmp)].
        replace (- - off) with off by lia.
        destruct (Z.eqb off' off); [apply Z.mod_pos_bound; unfold two64; lia | exact (Hcan (PmSlot off'))].
      * simpl. replace (- - off) with off by lia; replace (- - soff) with soff by lia; rewrite Z.eqb_refl.
        apply Z.mod_small. pose proof (Z.mod_pos_bound (pm_slot st soff) two32 ltac:(unfold two32; lia)).
        unfold two32, two64 in *; lia.
      * intros [r' | off' |] Hneq; simpl; [reflexivity | | reflexivity].
        replace (- - off) with off by lia.
        destruct (Z.eqb off' off) eqn:E; [apply Z.eqb_eq in E; subst; contradiction | reflexivity].
      * unfold emit_one_pmove; simpl; reflexivity.
      * intros [r' | off' |]; simpl; [exact (Hcan (PmReg r')) | | exact (Hcan PmCycleTmp)].
        replace (- - off) with off by lia.
        destruct (Z.eqb off' off); [apply Z.mod_pos_bound; unfold two64; lia | exact (Hcan (PmSlot off'))].
      * simpl. replace (- - off) with off by lia; replace (- - soff) with soff by lia; rewrite Z.eqb_refl.
        apply Z.mod_mod. unfold two64; lia.
      * intros [r' | off' |] Hneq; simpl; [reflexivity | | reflexivity].
        replace (- - off) with off by lia.
        destruct (Z.eqb off' off) eqn:E; [apply Z.eqb_eq in E; subst; contradiction | reflexivity].
    + destruct half.
      * eexists. split; [|split; [|split]].
        -- unfold emit_one_pmove; simpl. reflexivity.
        -- intros [r' | off' |]; simpl; [exact (Hcan (PmReg r')) | | exact (Hcan PmCycleTmp)].
           replace (- - off) with off by lia.
           destruct (Z.eqb off' off); [apply Z.mod_pos_bound; unfold two64; lia | exact (Hcan (PmSlot off'))].
        -- simpl. replace (- - off) with off by lia. rewrite Z.eqb_refl.
           apply Z.mod_small. pose proof (Z.mod_pos_bound (pm_rcx st) two32 ltac:(unfold two32; lia)).
           unfold two32, two64 in *; lia.
        -- intros [r' | off' |] Hneq; simpl; [reflexivity | | reflexivity].
           replace (- - off) with off by lia.
           destruct (Z.eqb off' off) eqn:E; [apply Z.eqb_eq in E; subst; contradiction | reflexivity].
      * eexists. split; [|split; [|split]].
        -- unfold emit_one_pmove; simpl. reflexivity.
        -- intros [r' | off' |]; simpl; [exact (Hcan (PmReg r')) | | exact (Hcan PmCycleTmp)].
           replace (- - off) with off by lia.
           destruct (Z.eqb off' off); [apply Z.mod_pos_bound; unfold two64; lia | exact (Hcan (PmSlot off'))].
        -- simpl. replace (- - off) with off by lia. rewrite Z.eqb_refl. reflexivity.
        -- intros [r' | off' |] Hneq; simpl; [reflexivity | | reflexivity].
           replace (- - off) with off by lia.
           destruct (Z.eqb off' off) eqn:E; [apply Z.eqb_eq in E; subst; contradiction | reflexivity].
    + destruct half.
      * unfold emit_one_pmove; simpl.
        eexists. split; [|split; [|split]].
        -- reflexivity.
        -- intros [r' | off' |]; simpl; [exact (Hcan (PmReg r')) | | exact (Hcan PmCycleTmp)].
           replace (- - off) with off by lia.
           destruct (Z.eqb off' off); [apply Z.mod_pos_bound; unfold two64; lia | exact (Hcan (PmSlot off'))].
        -- simpl. replace (- - off) with off by lia. rewrite Z.eqb_refl.
           rewrite Z.mod_mod by (unfold two32; lia).
           apply Z.mod_small. pose proof (Z.mod_pos_bound n two32 ltac:(unfold two32; lia)).
           unfold two32, two64 in *; lia.
        -- intros [r' | off' |] Hneq; simpl; [reflexivity | | reflexivity].
           replace (- - off) with off by lia.
           destruct (Z.eqb off' off) eqn:E; [apply Z.eqb_eq in E; subst; contradiction | reflexivity].
      * cbn [emit_one_pmove pmv_half pmv_dst pmv_src negb].
        destruct (integer_immediate false n) as [imm_v|] eqn:Eimm.
        -- eexists. split; [|split; [|split]].
           ++ simpl. reflexivity.
           ++ intros [r' | off' |]; simpl; [exact (Hcan (PmReg r')) | | exact (Hcan PmCycleTmp)].
              replace (- - off) with off by lia.
              destruct (Z.eqb off' off); [apply Z.mod_pos_bound; unfold two64; lia | exact (Hcan (PmSlot off'))].
           ++ simpl. replace (- - off) with off by lia. rewrite Z.eqb_refl.
              exact (imm32_congruent false n imm_v Eimm).
           ++ intros [r' | off' |] Hneq; simpl; [reflexivity | | reflexivity].
              replace (- - off) with off by lia.
              destruct (Z.eqb off' off) eqn:E; [apply Z.eqb_eq in E; subst; contradiction | reflexivity].
        -- pose proof (load_const_reg_sound sym_env st n false "rax" "eax" PrRax eq_refl eq_refl) as Hlc.
           rewrite (pm_exec_lines_app sym_env _ _ st _ Hlc). simpl.
           eexists. split; [reflexivity | split; [|split]].
           ++ intros [r' | off' |]; simpl; [exact (Hcan (PmReg r')) | | exact (Hcan PmCycleTmp)].
              replace (- - off) with off by lia.
              destruct (Z.eqb off' off); [apply Z.mod_pos_bound; unfold two64; lia | exact (Hcan (PmSlot off'))].
           ++ simpl. replace (- - off) with off by lia. rewrite Z.eqb_refl.
              apply Z.mod_mod. unfold two64; lia.
           ++ intros [r' | off' |] Hneq; simpl; [reflexivity | | reflexivity].
              replace (- - off) with off by lia.
              destruct (Z.eqb off' off) eqn:E; [apply Z.eqb_eq in E; subst; contradiction | reflexivity].
    + subst half. eexists. split; [|split; [|split]].
      * unfold emit_one_pmove; simpl. reflexivity.
      * intros [r' | off' |]; simpl; [exact (Hcan (PmReg r')) | | exact (Hcan PmCycleTmp)].
        replace (- - off) with off by lia.
        destruct (Z.eqb off' off); [apply Z.mod_pos_bound; unfold two64; lia | exact (Hcan (PmSlot off'))].
      * simpl. replace (- - off) with off by lia. rewrite Z.eqb_refl.
        apply Z.mod_mod. unfold two64; lia.
      * intros [r' | off' |] Hneq; simpl; [reflexivity | | reflexivity].
        replace (- - off) with off by lia.
        destruct (Z.eqb off' off) eqn:E; [apply Z.eqb_eq in E; subst; contradiction | reflexivity].
Qed.

(** Characterization of [find_pmove_dst] on duplicate-free destination lists. *)
Lemma find_pmove_dst_some : forall ms l m,
  find_pmove_dst l ms = Some m -> In m ms /\ pmv_dst m = l.
Proof.
  induction ms as [|m0 ms' IH]; intros l m H; simpl in *; [discriminate|].
  destruct (pm_loc_eqb l (pmv_dst m0)) eqn:E.
  - injection H as <-. apply pm_loc_eqb_spec in E. split; [left; reflexivity | symmetry; exact E].
  - destruct (IH l m H) as [Hin Hdst]. split; [right; exact Hin | exact Hdst].
Qed.

(** [find_pmove_dst] returns `None` iff `l` is not in `map pmv_dst ms`. *)
Lemma find_pmove_dst_none : forall ms l,
  find_pmove_dst l ms = None <-> ~ In l (map pmv_dst ms).
Proof.
  induction ms as [|m0 ms' IH]; intro l; simpl.
  - split; auto.
  - destruct (pm_loc_eqb l (pmv_dst m0)) eqn:E.
    + apply pm_loc_eqb_spec in E. subst l.
      split; [discriminate | intro H; exfalso; apply H; left; reflexivity].
    + rewrite IH. split.
      * intros Hnot [Heq | Hin]; [subst; rewrite pm_loc_eqb_refl in E; discriminate | contradiction].
      * intros Hnot. intro Hin. apply Hnot. right. exact Hin.
Qed.

(** Under `NoDup (map pmv_dst ms)`, membership determines [find_pmove_dst]. *)
Lemma find_pmove_dst_in : forall ms m,
  NoDup (map pmv_dst ms) ->
  In m ms ->
  find_pmove_dst (pmv_dst m) ms = Some m.
Proof.
  induction ms as [|m0 ms' IH]; intros m Hnd Hin; simpl in *; [contradiction|].
  inversion Hnd as [| ? ? Hnotin Hnd']; subst.
  destruct Hin as [<- | Hin'].
  - rewrite pm_loc_eqb_refl. reflexivity.
  - destruct (pm_loc_eqb (pmv_dst m) (pmv_dst m0)) eqn:E.
    + apply pm_loc_eqb_spec in E. exfalso. apply Hnotin.
      rewrite <- E. apply in_map. exact Hin'.
    + apply IH; assumption.
Qed.

(** A well-formed no-op move evaluates to the destination's existing value. *)
Lemma pmove_nop_eval : forall sym_env st m,
  pm_mach_canonical st ->
  pmove_wf (pm_mach_env st) m ->
  pmove_is_nop m = true ->
  eval_pm_src sym_env (pm_mach_env st) (pmv_half m) (pmv_src m)
  = pm_mach_env st (pmv_dst m).
Proof.
  intros sym_env st [half src_w dst [l | n | g]] Hcan [_ Hsrc] Hnop;
    cbn [pmove_is_nop pmv_src pmv_dst pmv_half pmv_src_w] in Hnop; try discriminate.
  apply Bool.andb_true_iff in Hnop. destruct Hnop as [El Ew].
  apply pm_loc_eqb_spec in El. subst dst.
  pose proof (Hcan l) as Hbound.
  destruct half; simpl in *.
  - specialize (Hsrc Ew). apply Z.mod_small. split; [lia | exact Hsrc].
  - apply Z.mod_small. exact Hbound.
Qed.

(** [loc_read_in_pmoves] distributes over list concatenation. *)
Lemma loc_read_in_pmoves_app : forall l xs ys,
  loc_read_in_pmoves l (xs ++ ys) = loc_read_in_pmoves l xs || loc_read_in_pmoves l ys.
Proof.
  intros l xs ys. induction xs as [|m xs' IH]; simpl; [reflexivity|].
  destruct (match pmv_src m with PsLoc l' => pm_loc_eqb l l' | _ => false end);
    [reflexivity | exact IH].
Qed.

(** [loc_read_in_pmoves] is invariant under list reversal. *)
Lemma loc_read_in_pmoves_rev : forall l xs,
  loc_read_in_pmoves l (rev xs) = loc_read_in_pmoves l xs.
Proof.
  intros l xs. induction xs as [|m xs' IH]; simpl; [reflexivity|].
  rewrite loc_read_in_pmoves_app, IH. simpl.
  destruct (match pmv_src m with PsLoc l' => pm_loc_eqb l l' | _ => false end);
    [apply Bool.orb_true_r | apply Bool.orb_false_r].
Qed.

(** Helper characterization of [drop_nop_pmoves_acc]. *)
Lemma drop_nop_pmoves_acc_eq : forall ms acc,
  drop_nop_pmoves_acc ms acc = rev acc ++ filter (fun m => negb (pmove_is_nop m)) ms.
Proof.
  induction ms as [|m ms' IH]; intro acc; simpl.
  - unfold rev'. rewrite <- rev_alt, app_nil_r. reflexivity.
  - destruct (pmove_is_nop m).
    + apply IH.
    + rewrite IH. simpl. rewrite <- app_assoc. reflexivity.
Qed.

(** Sublist preservation of `NoDup (map f xs)` under `filter`. *)
Lemma nodup_map_filter : forall (A B : Type) (f : A -> B) (p : A -> bool) (xs : list A),
  NoDup (map f xs) -> NoDup (map f (filter p xs)).
Proof.
  intros A B f p xs. induction xs as [|x xs' IH]; intro Hnd; simpl in *; [constructor|].
  inversion Hnd as [| ? ? Hnotin Hnd']; subst.
  destruct (p x).
  - simpl. constructor; [|apply IH; exact Hnd'].
    intro Hin. apply in_map_iff in Hin. destruct Hin as [x' [Heq Hin']].
    apply filter_In in Hin'. apply Hnotin. rewrite <- Heq. apply in_map. exact (proj1 Hin').
  - apply IH. exact Hnd'.
Qed.

(** Dropping well-formed no-op moves preserves `NoDup`, unread locations,
    [pmove_wf], and [simul_pmoves]. *)
Lemma drop_nop_pmoves_sound : forall sym_env st ms,
  pm_mach_canonical st ->
  NoDup (map pmv_dst ms) ->
  loc_read_in_pmoves PmCycleTmp ms = false ->
  Forall (pmove_wf (pm_mach_env st)) ms ->
  NoDup (map pmv_dst (drop_nop_pmoves_acc ms [])) /\
  loc_read_in_pmoves PmCycleTmp (drop_nop_pmoves_acc ms []) = false /\
  Forall (pmove_wf (pm_mach_env st)) (drop_nop_pmoves_acc ms []) /\
  (forall l, simul_pmoves sym_env (pm_mach_env st) (drop_nop_pmoves_acc ms []) l
             = simul_pmoves sym_env (pm_mach_env st) ms l).
Proof.
  intros sym_env st ms Hcan Hnd Hunread Hwf.
  rewrite !drop_nop_pmoves_acc_eq. simpl.
  set (clean := filter (fun m => negb (pmove_is_nop m)) ms).
  split; [apply nodup_map_filter; exact Hnd | split; [|split]].
  - unfold clean. clear -Hunread.
    induction ms as [|m ms' IH]; [reflexivity|].
    cbn [loc_read_in_pmoves] in Hunread; cbv zeta in Hunread.
    destruct (match pmv_src m with PsLoc l' => pm_loc_eqb PmCycleTmp l' | _ => false end) eqn:Eh;
      [discriminate|].
    cbn [filter]. destruct (pmove_is_nop m); cbn [negb loc_read_in_pmoves]; cbv zeta.
    + exact (IH Hunread).
    + rewrite Eh. exact (IH Hunread).
  - apply Forall_forall. intros m Hm. unfold clean in Hm.
    apply filter_In in Hm. rewrite Forall_forall in Hwf. apply Hwf. exact (proj1 Hm).
  - intro l. unfold simul_pmoves.
    destruct (find_pmove_dst l clean) as [mc|] eqn:Ec.
    + destruct (find_pmove_dst_some clean l mc Ec) as [Hinc Hd].
      subst l. unfold clean in Hinc. apply filter_In in Hinc.
      rewrite (find_pmove_dst_in ms mc Hnd (proj1 Hinc)). reflexivity.
    + apply find_pmove_dst_none in Ec.
      destruct (find_pmove_dst l ms) as [mm|] eqn:Em; [|reflexivity].
      destruct (find_pmove_dst_some ms l mm Em) as [Hinm Hd]. subst l.
      destruct (pmove_is_nop mm) eqn:Enop.
      * rewrite Forall_forall in Hwf.
        symmetry. apply (pmove_nop_eval sym_env st mm Hcan (Hwf mm Hinm) Enop).
      * exfalso. apply Ec. apply in_map. unfold clean.
        apply filter_In. split; [exact Hinm | rewrite Enop; reflexivity].
Qed.

(** Helper: `NoDup (map f (xs ++ y :: zs))` implies `NoDup (map f ((y :: xs) ++ zs))`. *)
Lemma nodup_map_move_mid : forall (A B : Type) (f : A -> B) (xs zs : list A) (y : A),
  NoDup (map f (xs ++ y :: zs)) -> NoDup (map f ((y :: xs) ++ zs)).
Proof.
  intros A B f xs zs y Hnd. rewrite map_app in Hnd. simpl in Hnd.
  rewrite map_app. simpl.
  assert (Hy : ~ In (f y) (map f xs) /\ ~ In (f y) (map f zs) /\ NoDup (map f xs ++ map f zs)).
  { clear -Hnd. induction (map f xs) as [|a l IH]; simpl in *.
    - inversion Hnd as [| ? ? Hny Hnd']; subst. split; [auto | split; assumption].
    - inversion Hnd as [| ? ? Hna Hnd']; subst.
      destruct (IH Hnd') as [Hy1 [Hy2 Hnd'']].
      split.
      + intros [Heq | Hin]; [apply Hna; apply in_or_app; right; left; symmetry; exact Heq | contradiction].
      + split; [exact Hy2 |].
        constructor; [|exact Hnd''].
        intro Hin. apply Hna. apply in_or_app.
        apply in_app_or in Hin. destruct Hin as [H1 | H2]; [left; exact H1 | right; right; exact H2]. }
  destruct Hy as [Hy1 [Hy2 Hnd2]].
  constructor; [|exact Hnd2].
  intro Hin. apply in_app_or in Hin. destruct Hin; contradiction.
Qed.

(** When [pick_ready_pmove] returns `Some (m, rest)`, `m :: rest` is a
    permutation of `rev prefix_rev ++ rest0` and `pmv_dst m` is unread in `rest`. *)
Lemma pick_ready_pmove_some : forall rest0 prefix_rev m rest,
  pick_ready_pmove rest0 prefix_rev = Some (m, rest) ->
  loc_read_in_pmoves (pmv_dst m) rest = false /\
  In m rest0 /\
  (forall x, In x (rev prefix_rev ++ rest0) <-> x = m \/ In x rest) /\
  (NoDup (map pmv_dst (rev prefix_rev ++ rest0)) -> NoDup (map pmv_dst (m :: rest))) /\
  (length (rev prefix_rev ++ rest0) = S (length rest))%nat.
Proof.
  induction rest0 as [|r0 rs IH]; intros prefix_rev m rest H; simpl in *; [discriminate|].
  destruct (negb (loc_read_in_pmoves (pmv_dst r0) prefix_rev) &&
            negb (loc_read_in_pmoves (pmv_dst r0) rs)) eqn:Eok.
  - injection H as <- <-.
    apply Bool.andb_true_iff in Eok. destruct Eok as [Ep Er].
    apply Bool.negb_true_iff in Ep. apply Bool.negb_true_iff in Er.
    rewrite rev_append_rev.
    split; [|split; [|split; [|split]]].
    + rewrite loc_read_in_pmoves_app, loc_read_in_pmoves_rev, Ep, Er. reflexivity.
    + left. reflexivity.
    + intro x. rewrite !in_app_iff. simpl. intuition congruence.
    + intro Hnd. exact (nodup_map_move_mid pmove pm_loc pmv_dst (rev prefix_rev) rs r0 Hnd).
    + rewrite !length_app. simpl. lia.
  - assert (Heq_list : rev (r0 :: prefix_rev) ++ rs = rev prefix_rev ++ r0 :: rs).
    { simpl. rewrite <- app_assoc. reflexivity. }
    destruct (IH (r0 :: prefix_rev) m rest H) as [Hnr [Hin [Hiff [Hnd Hlen]]]].
    rewrite Heq_list in Hiff, Hnd, Hlen.
    split; [exact Hnr | split; [right; exact Hin | split; [exact Hiff | split; [exact Hnd | exact Hlen]]]].
Qed.

(** Extract all location operands read by `ms`. *)
Fixpoint pmove_src_locs (ms : list pmove) : list pm_loc :=
  match ms with
  | [] => []
  | m :: ms' =>
      match pmv_src m with
      | PsLoc l => l :: pmove_src_locs ms'
      | _ => pmove_src_locs ms'
      end
  end.

(** [loc_read_in_pmoves] reflects membership in [pmove_src_locs]. *)
Lemma loc_read_in_pmoves_iff : forall l ms,
  loc_read_in_pmoves l ms = true <-> In l (pmove_src_locs ms).
Proof.
  intros l ms. induction ms as [|m ms' IH]; simpl.
  - split; [discriminate | contradiction].
  - destruct (pmv_src m) as [l' | n | g].
    + simpl. destruct (pm_loc_eqb l l') eqn:E.
      * apply pm_loc_eqb_spec in E. subst l'. split; auto.
      * rewrite IH. split; [right; exact H | intros [Heq | Hin]; [subst; rewrite pm_loc_eqb_refl in E; discriminate | exact Hin]].
    + exact IH.
    + exact IH.
Qed.

(** [pmove_src_locs] has at most `length ms` elements. *)
Lemma pmove_src_locs_len : forall ms,
  (length (pmove_src_locs ms) <= length ms)%nat.
Proof.
  induction ms as [|m ms' IH]; simpl; [lia|].
  destruct (pmv_src m); simpl; lia.
Qed.

(** Remove the first occurrence of `x` from `ls`. *)
Fixpoint remove_one_loc (x : pm_loc) (ls : list pm_loc) : list pm_loc :=
  match ls with
  | [] => []
  | y :: ls' => if pm_loc_eqb x y then ls' else y :: remove_one_loc x ls'
  end.

(** Removing a present element strictly decreases length. *)
Lemma remove_one_loc_lt : forall x ls,
  In x ls -> (length (remove_one_loc x ls) < length ls)%nat.
Proof.
  intros x ls. induction ls as [|y ls' IH]; intro Hin; simpl in *; [contradiction|].
  destruct (pm_loc_eqb x y) eqn:E; [lia|].
  destruct Hin as [Heq | Hin']; [subst y; rewrite pm_loc_eqb_refl in E; discriminate|].
  specialize (IH Hin'). simpl. lia.
Qed.

(** Removing `x` preserves every `z <> x`. *)
Lemma remove_one_loc_in : forall x z ls,
  z <> x -> In z ls -> In z (remove_one_loc x ls).
Proof.
  intros x z ls Hneq. induction ls as [|y ls' IH]; intro Hin; simpl in *; [contradiction|].
  destruct (pm_loc_eqb x y) eqn:E.
  - apply pm_loc_eqb_spec in E. subst y.
    destruct Hin as [Heq | Hin']; [symmetry in Heq; contradiction | exact Hin'].
  - destruct Hin as [<- | Hin']; [left; reflexivity | right; apply IH; exact Hin'].
Qed.

(** Finite pigeonhole lemma on `pm_loc`: a duplicate-free list `ds`
    included in `ls` has `length ds <= length ls`. *)
Lemma nodup_locs_incl_le : forall (ds ls : list pm_loc),
  NoDup ds ->
  (forall x, In x ds -> In x ls) ->
  (length ds <= length ls)%nat.
Proof.
  induction ds as [|d ds' IH]; intros ls Hnd Hincl; simpl; [lia|].
  inversion Hnd as [| ? ? Hnotin Hnd']; subst.
  pose proof (remove_one_loc_lt d ls (Hincl d (or_introl eq_refl))) as Hlt.
  assert (Hsub : forall x, In x ds' -> In x (remove_one_loc d ls)).
  { intros x Hx. apply remove_one_loc_in.
    - intro Heq. subst x. contradiction.
    - apply Hincl. right. exact Hx. }
  specialize (IH (remove_one_loc d ls) Hnd' Hsub). lia.
Qed.

(** Helper: extract an explicit move reading `l` when [loc_read_in_pmoves] returns `true`. *)
Lemma loc_read_in_pmoves_exists : forall l xs,
  loc_read_in_pmoves l xs = true ->
  exists q, In q xs /\ pmv_src q = PsLoc l.
Proof.
  intros l xs. induction xs as [|x xs' IH]; intro Hlr; simpl in *; [discriminate|].
  destruct (pmv_src x) as [lx | | ] eqn:Ex.
  - destruct (pm_loc_eqb l lx) eqn:Elx.
    + apply pm_loc_eqb_spec in Elx. subst lx. exists x. split; [left; reflexivity | exact Ex].
    + destruct (IH Hlr) as [q [Hq1 Hq2]]. exists q. split; [right; exact Hq1 | exact Hq2].
  - destruct (IH Hlr) as [q [Hq1 Hq2]]. exists q. split; [right; exact Hq1 | exact Hq2].
  - destruct (IH Hlr) as [q [Hq1 Hq2]]. exists q. split; [right; exact Hq1 | exact Hq2].
Qed.

(** When [pick_ready_pmove] returns `None` on duplicate-free destinations,
    every move `m` in `prefix_rev ++ rest0` has its destination read by
    some move `q` with `pmv_dst q <> pmv_dst m`. *)
Lemma pick_ready_pmove_none : forall rest0 prefix_rev,
  pick_ready_pmove rest0 prefix_rev = None ->
  NoDup (map pmv_dst (prefix_rev ++ rest0)) ->
  (forall p, In p prefix_rev ->
     exists q, In q (prefix_rev ++ rest0) /\ pmv_dst q <> pmv_dst p /\ pmv_src q = PsLoc (pmv_dst p)) ->
  forall m, In m (prefix_rev ++ rest0) ->
    exists q, In q (prefix_rev ++ rest0) /\ pmv_dst q <> pmv_dst m /\ pmv_src q = PsLoc (pmv_dst m).
Proof.
  induction rest0 as [|r0 rs IH]; intros prefix_rev Hnone Hnd Hpref m Hm; simpl in *.
  - rewrite app_nil_r in *. apply Hpref. exact Hm.
  - destruct (negb (loc_read_in_pmoves (pmv_dst r0) prefix_rev) &&
              negb (loc_read_in_pmoves (pmv_dst r0) rs)) eqn:Eok; [discriminate|].
    assert (Hr0_disj : ~ In (pmv_dst r0) (map pmv_dst prefix_rev) /\ ~ In (pmv_dst r0) (map pmv_dst rs)).
    { pose proof (nodup_map_move_mid pmove pm_loc pmv_dst prefix_rev rs r0 Hnd) as Hnd'.
      simpl in Hnd'. inversion Hnd' as [| ? ? Hnot _]; subst.
      rewrite map_app in Hnot. split; intro Hin; apply Hnot; apply in_or_app; [left | right]; exact Hin. }
    assert (Hr0 : exists q, In q ((r0 :: prefix_rev) ++ rs) /\
                            pmv_dst q <> pmv_dst r0 /\ pmv_src q = PsLoc (pmv_dst r0)).
    { apply Bool.andb_false_iff in Eok.
      destruct Eok as [Ep | Er]; apply Bool.negb_false_iff in Ep + apply Bool.negb_false_iff in Er.
      - destruct (loc_read_in_pmoves_exists (pmv_dst r0) prefix_rev Ep) as [q [Hq1 Hq2]].
        exists q. split; [simpl; right; apply in_or_app; left; exact Hq1 | split; [|exact Hq2]].
        intro Heq. apply (proj1 Hr0_disj). rewrite <- Heq. apply in_map. exact Hq1.
      - destruct (loc_read_in_pmoves_exists (pmv_dst r0) rs Er) as [q [Hq1 Hq2]].
        exists q. split; [simpl; right; apply in_or_app; right; exact Hq1 | split; [|exact Hq2]].
        intro Heq. apply (proj2 Hr0_disj). rewrite <- Heq. apply in_map. exact Hq1. }
    assert (Hpref' : forall p, In p (r0 :: prefix_rev) ->
               exists q, In q ((r0 :: prefix_rev) ++ rs) /\
                         pmv_dst q <> pmv_dst p /\ pmv_src q = PsLoc (pmv_dst p)).
    { intros p [<- | Hp]; [exact Hr0|].
      destruct (Hpref p Hp) as [q [Hq_in [Hq_neq Hq_src]]].
      exists q. split; [|split; [exact Hq_neq | exact Hq_src]].
      simpl. apply in_app_or in Hq_in. destruct Hq_in as [H1 | [<- | H2]];
        [right; apply in_or_app; left; exact H1 | left; reflexivity | right; apply in_or_app; right; exact H2]. }
    pose proof (nodup_map_move_mid pmove pm_loc pmv_dst prefix_rev rs r0 Hnd) as Hnd'.
    assert (Hm' : In m ((r0 :: prefix_rev) ++ rs)).
    { simpl. apply in_app_or in Hm. destruct Hm as [H1 | [<- | H2]];
        [right; apply in_or_app; left; exact H1 | left; reflexivity | right; apply in_or_app; right; exact H2]. }
    destruct (IH (r0 :: prefix_rev) Hnone Hnd' Hpref' m Hm') as [q [Hq_in [Hq_neq Hq_src]]].
    exists q. split; [|split; [exact Hq_neq | exact Hq_src]].
    simpl in Hq_in. destruct Hq_in as [<- | Hq_rest].
    + apply in_or_app. right. left. reflexivity.
    + apply in_app_or in Hq_rest. destruct Hq_rest as [H1 | H2];
        apply in_or_app; [left; exact H1 | right; right; exact H2].
Qed.

(** Membership in `ms` with `pmv_src m = PsLoc l` implies membership in [pmove_src_locs]. *)
Lemma in_pmove_src_locs : forall m ms l,
  In m ms -> pmv_src m = PsLoc l -> In l (pmove_src_locs ms).
Proof.
  intros m ms l. induction ms as [|x xs IH]; intros Hm Hsrc; simpl in *; [contradiction|].
  destruct Hm as [<- | Hm']; [rewrite Hsrc; left; reflexivity|].
  destruct (pmv_src x); [right | |]; apply IH; assumption.
Qed.

(** Pigeonhole consequence at a cycle break: when [pick_ready_pmove] returns
    `None` on distinct non-`PmCycleTmp` destinations, `PmCycleTmp` is NOT
    read anywhere in `ms` (even after earlier cycles used `%rcx`), and
    every move in `ms` has its destination read by another move in `ms`. *)
Lemma no_ready_cycle_tmp_unread : forall ms,
  NoDup (map pmv_dst ms) ->
  (forall m, In m ms -> pmv_dst m <> PmCycleTmp) ->
  pick_ready_pmove ms [] = None ->
  loc_read_in_pmoves PmCycleTmp ms = false /\
  (forall m, In m ms ->
     exists q, In q ms /\ pmv_dst q <> pmv_dst m /\ pmv_src q = PsLoc (pmv_dst m)).
Proof.
  intros ms Hnd Hnot_tmp Hnone.
  assert (Hall : forall m, In m ms ->
            exists q, In q ms /\ pmv_dst q <> pmv_dst m /\ pmv_src q = PsLoc (pmv_dst m)).
  { intros m Hm.
    apply (pick_ready_pmove_none ms [] Hnone Hnd (fun p Hp => False_ind _ Hp) m Hm). }
  split; [|exact Hall].
  destruct (loc_read_in_pmoves PmCycleTmp ms) eqn:Etmp; [|reflexivity].
  exfalso.
  apply loc_read_in_pmoves_iff in Etmp.
  assert (Hincl : forall d, In d (map pmv_dst ms) -> In d (remove_one_loc PmCycleTmp (pmove_src_locs ms))).
  { intros d Hd. apply in_map_iff in Hd. destruct Hd as [m [<- Hm]].
    destruct (Hall m Hm) as [q [Hq_in [_ Hq_src]]].
    apply remove_one_loc_in.
    - apply Hnot_tmp. exact Hm.
    - exact (in_pmove_src_locs q ms (pmv_dst m) Hq_in Hq_src). }
  pose proof (nodup_locs_incl_le (map pmv_dst ms)
                (remove_one_loc PmCycleTmp (pmove_src_locs ms)) Hnd Hincl) as Hle.
  pose proof (remove_one_loc_lt PmCycleTmp (pmove_src_locs ms) Etmp) as Hlt.
  pose proof (pmove_src_locs_len ms) as Hlen.
  rewrite length_map in Hle. lia.
Qed.

(** Single-element source substitution used by [subst_pmove_src]. *)
Definition subst_pmove_one (old : pm_loc) (m : pmove) : pmove :=
  let src' :=
    match pmv_src m with
    | PsLoc l => if pm_loc_eqb l old then PsLoc PmCycleTmp else PsLoc l
    | s => s
    end in
  mkPMove (pmv_half m) (pmv_src_w m) (pmv_dst m) src'.

(** Helper characterization of [subst_pmove_src]. *)
Lemma subst_pmove_src_eq : forall old ms acc,
  subst_pmove_src old ms acc =
  rev acc ++ filter (fun m => negb (pmove_is_nop m)) (map (subst_pmove_one old) ms).
Proof.
  intros old ms. induction ms as [|m ms' IH]; intro acc; simpl.
  - unfold rev'. rewrite <- rev_alt, app_nil_r. reflexivity.
  - unfold subst_pmove_one at 1.
    destruct (pmove_is_nop (mkPMove (pmv_half m) (pmv_src_w m) (pmv_dst m)
                (match pmv_src m with
                 | PsLoc l => if pm_loc_eqb l old then PsLoc PmCycleTmp else PsLoc l
                 | s => s
                 end))).
    + apply IH.
    + rewrite IH. simpl. rewrite <- app_assoc. reflexivity.
Qed.

(** Cycle-breaking transformation [subst_pmove_src] after saving `old` into
    `PmCycleTmp`: preserves `NoDup`, [pmove_wf], and [simul_pmoves] on all
    non-scratch locations, does not grow `ms`, and marks `PmCycleTmp` read. *)
Lemma subst_pmove_src_sound : forall sym_env st st1 old ms,
  pm_mach_canonical st ->
  pm_mach_canonical st1 ->
  old <> PmCycleTmp ->
  loc_read_in_pmoves PmCycleTmp ms = false ->
  NoDup (map pmv_dst ms) ->
  Forall (pmove_wf (pm_mach_env st)) ms ->
  pm_mach_env st1 PmCycleTmp = pm_mach_env st old ->
  (forall l, l <> PmCycleTmp -> pm_mach_env st1 l = pm_mach_env st l) ->
  (exists q, In q ms /\ pmv_dst q <> old /\ pmv_src q = PsLoc old) ->
  NoDup (map pmv_dst (subst_pmove_src old ms [])) /\
  Forall (pmove_wf (pm_mach_env st1)) (subst_pmove_src old ms []) /\
  (length (subst_pmove_src old ms []) <= length ms)%nat /\
  loc_read_in_pmoves PmCycleTmp (subst_pmove_src old ms []) = true /\
  (forall l, l <> PmCycleTmp ->
     simul_pmoves sym_env (pm_mach_env st1) (subst_pmove_src old ms []) l
     = simul_pmoves sym_env (pm_mach_env st) ms l).
Proof.
  intros sym_env st st1 old ms Hcan Hcan1 Hold_neq Hunread Hnd Hwf Htmp Hother [q [Hq_in [Hq_dst Hq_src]]].
  rewrite !subst_pmove_src_eq. simpl.
  set (mapped := map (subst_pmove_one old) ms).
  set (ms' := filter (fun m => negb (pmove_is_nop m)) mapped).
  assert (Hmap_dst : map pmv_dst mapped = map pmv_dst ms).
  { unfold mapped. rewrite map_map. reflexivity. }
  assert (Hnd_mapped : NoDup (map pmv_dst mapped)) by (rewrite Hmap_dst; exact Hnd).
  assert (Hnot_tmp_src : forall m, In m ms -> pmv_src m <> PsLoc PmCycleTmp).
  { intros m Hm Heq.
    pose proof (proj2 (loc_read_in_pmoves_iff PmCycleTmp ms)
                  (in_pmove_src_locs m ms PmCycleTmp Hm Heq)) as Hrd.
    rewrite Hunread in Hrd. discriminate. }
  assert (Heval_one : forall m, In m ms ->
            eval_pm_src sym_env (pm_mach_env st1)
              (pmv_half (subst_pmove_one old m)) (pmv_src (subst_pmove_one old m)) =
            eval_pm_src sym_env (pm_mach_env st) (pmv_half m) (pmv_src m)).
  { intros m Hm. pose proof (Hnot_tmp_src m Hm) as Hnt.
    unfold subst_pmove_one, eval_pm_src. simpl.
    destruct (pmv_src m) as [l | n | g]; [|reflexivity | reflexivity].
    destruct (pm_loc_eqb l old) eqn:Elo.
    - apply pm_loc_eqb_spec in Elo. subst l. rewrite Htmp. reflexivity.
    - rewrite Hother; [reflexivity | congruence]. }
  assert (Hwf_mapped : Forall (pmove_wf (pm_mach_env st1)) mapped).
  { apply Forall_forall. intros m' Hm'. unfold mapped in Hm'.
    apply in_map_iff in Hm'. destruct Hm' as [m [<- Hm]].
    rewrite Forall_forall in Hwf.
    pose proof (Hwf m Hm) as [Hdst Hsrc].
    pose proof (Hnot_tmp_src m Hm) as Hnt.
    unfold subst_pmove_one, pmove_wf; simpl. split; [exact Hdst|].
    destruct (pmv_src m) as [l | n | g]; [|exact I | exact Hsrc].
    destruct (pm_loc_eqb l old) eqn:Elo.
    - apply pm_loc_eqb_spec in Elo. subst l. rewrite Htmp. exact Hsrc.
    - rewrite Hother by congruence. exact Hsrc. }
  split; [apply nodup_map_filter; exact Hnd_mapped | split; [|split; [|split]]].
  - apply Forall_forall. intros x Hx. unfold ms' in Hx.
    apply filter_In in Hx. rewrite Forall_forall in Hwf_mapped.
    apply Hwf_mapped. exact (proj1 Hx).
  - transitivity (length mapped).
    + unfold ms'. clear. induction mapped as [|x xs IH]; simpl; [lia|].
      destruct (negb (pmove_is_nop x)); simpl; lia.
    + unfold mapped. rewrite length_map. lia.
  - apply loc_read_in_pmoves_iff.
    assert (Hq'_in : In (subst_pmove_one old q) ms').
    { unfold ms'. apply filter_In. split.
      - unfold mapped. apply in_map. exact Hq_in.
      - unfold subst_pmove_one; rewrite Hq_src, pm_loc_eqb_refl;
          cbn [pmove_is_nop pmv_src pmv_dst pmv_half pmv_src_w negb].
        rewrite Forall_forall in Hwf. pose proof (proj1 (Hwf q Hq_in)) as Hqd.
        destruct (pm_loc_eqb (pmv_dst q) PmCycleTmp) eqn:Eb; [|reflexivity].
        apply pm_loc_eqb_spec in Eb. contradiction. }
    assert (Hq'_src : pmv_src (subst_pmove_one old q) = PsLoc PmCycleTmp).
    { unfold subst_pmove_one. rewrite Hq_src, pm_loc_eqb_refl. reflexivity. }
    exact (in_pmove_src_locs (subst_pmove_one old q) ms' PmCycleTmp Hq'_in Hq'_src).
  - intros l Hl_neq. unfold simul_pmoves.
    destruct (find_pmove_dst l ms') as [mc|] eqn:Ec.
    + destruct (find_pmove_dst_some ms' l mc Ec) as [Hinc Hd]. subst l.
      unfold ms' in Hinc. apply filter_In in Hinc. destruct Hinc as [Hin_map _].
      unfold mapped in Hin_map. apply in_map_iff in Hin_map.
      destruct Hin_map as [m [Heqm Hm_in]]. subst mc.
      change (pmv_dst (subst_pmove_one old m)) with (pmv_dst m) in *.
      rewrite (find_pmove_dst_in ms m Hnd Hm_in).
      exact (Heval_one m Hm_in).
    + apply find_pmove_dst_none in Ec.
      destruct (find_pmove_dst l ms) as [mm|] eqn:Em; [|exact (Hother l Hl_neq)].
      destruct (find_pmove_dst_some ms l mm Em) as [Hinm Hd]. subst l.
      destruct (pmove_is_nop (subst_pmove_one old mm)) eqn:Enop.
      * rewrite <- (Heval_one mm Hinm).
        rewrite Forall_forall in Hwf_mapped.
        assert (Hin_map : In (subst_pmove_one old mm) mapped) by (unfold mapped; apply in_map; exact Hinm).
        pose proof (pmove_nop_eval sym_env st1 (subst_pmove_one old mm) Hcan1 (Hwf_mapped _ Hin_map) Enop) as Hnop1.
        change (pmv_dst (subst_pmove_one old mm)) with (pmv_dst mm) in Hnop1.
        rewrite Hnop1. reflexivity.
      * exfalso. apply Ec.
        change (pmv_dst mm) with (pmv_dst (subst_pmove_one old mm)).
        apply in_map. unfold ms'. apply filter_In.
        split; [unfold mapped; apply in_map; exact Hinm | rewrite Enop; reflexivity].
Qed.

(** Potential measure strictly decreasing on every step of [compile_pmoves_fuel]. *)
Definition pmoves_measure (ms : list pmove) : nat :=
  (2 * length ms - (if loc_read_in_pmoves PmCycleTmp ms then 1 else 0))%nat.

(** Induction over [compile_pmoves_fuel]: whenever `pmoves_measure ms < fuel`,
    the emitted lines execute cleanly from `st` and realize [simul_pmoves]
    on every non-scratch location `l <> PmCycleTmp`. *)
Lemma compile_pmoves_fuel_sound : forall fuel sym_env ms acc st0 st,
  (pmoves_measure ms < fuel)%nat ->
  pm_exec_lines sym_env st0 (rev acc) = Some st ->
  pm_mach_canonical st ->
  NoDup (map pmv_dst ms) ->
  Forall (pmove_wf (pm_mach_env st)) ms ->
  exists st_end,
    pm_exec_lines sym_env st0 (compile_pmoves_fuel fuel ms acc) = Some st_end /\
    pm_mach_canonical st_end /\
    (forall l, l <> PmCycleTmp ->
       pm_mach_env st_end l = simul_pmoves sym_env (pm_mach_env st) ms l).
Proof.
  induction fuel as [|fuel' IH]; intros sym_env ms acc st0 st Hmeas Hacc Hcan Hnd Hwf.
  - lia.
  - destruct ms as [|m0 ms_tl].
    + simpl. unfold rev'. rewrite <- rev_alt.
      exists st. split; [exact Hacc | split; [exact Hcan | intros l _; reflexivity]].
    + cbn [compile_pmoves_fuel].
      set (ms := m0 :: ms_tl) in *.
      destruct (pick_ready_pmove ms []) as [[m rest]|] eqn:Epick.
      * destruct (pick_ready_pmove_some ms [] m rest Epick)
          as [Hnr [Hm_in [Hiff [Hnd_fn Hlen]]]].
        simpl in Hiff, Hnd_fn, Hlen.
        pose proof (Hnd_fn Hnd) as Hnd_mrest.
        inversion Hnd_mrest as [| ? ? Hnot_rest Hnd_rest]; subst.
        rewrite Forall_forall in Hwf.
        destruct (emit_one_pmove_sound sym_env st m Hcan (Hwf m Hm_in))
          as [st1 [Hexec1 [Hcan1 [Hdst1 Hother1]]]].
        assert (Hacc1 : pm_exec_lines sym_env st0 (rev (rev_append (emit_one_pmove m) acc)) = Some st1).
        { rewrite rev_append_rev, rev_app_distr, rev_involutive.
          rewrite (pm_exec_lines_app sym_env _ _ st0 st Hacc). exact Hexec1. }
        assert (Hmeas_rest : (pmoves_measure rest < fuel')%nat).
        { unfold pmoves_measure, ms in *; cbn [length] in *.
          destruct (loc_read_in_pmoves PmCycleTmp (m0 :: ms_tl));
          destruct (loc_read_in_pmoves PmCycleTmp rest); lia. }
        assert (Hnot_dst_src : forall m' l', In m' rest -> pmv_src m' = PsLoc l' -> l' <> pmv_dst m).
        { intros m' l' Hm' Hsrc Heq. subst l'.
          pose proof (proj2 (loc_read_in_pmoves_iff (pmv_dst m) rest)
                       (in_pmove_src_locs m' rest (pmv_dst m) Hm' Hsrc)) as Hrd.
          rewrite Hnr in Hrd. discriminate. }
        assert (Hwf_rest : Forall (pmove_wf (pm_mach_env st1)) rest).
        { apply Forall_forall. intros m' Hm'.
          assert (Hm'_ms : In m' ms) by (apply Hiff; right; exact Hm').
          pose proof (Hwf m' Hm'_ms) as [Hd' Hs'].
          split; [exact Hd'|].
          destruct (pmv_src m') as [l' | n | g] eqn:Es; [|exact I | exact Hs'].
          rewrite Hother1 by (exact (Hnot_dst_src m' l' Hm' Es)).
          exact Hs'. }
        destruct (IH sym_env rest (rev_append (emit_one_pmove m) acc) st0 st1
                    Hmeas_rest Hacc1 Hcan1 Hnd_rest Hwf_rest)
          as [st_end [Hend [Hcan_end Hsim_end]]].
        exists st_end. split; [exact Hend | split; [exact Hcan_end|]].
        intros l Hl_neq. rewrite (Hsim_end l Hl_neq).
        unfold simul_pmoves.
        destruct (pm_loc_eqb l (pmv_dst m)) eqn:Elm.
        -- apply pm_loc_eqb_spec in Elm. subst l.
           pose proof (proj2 (find_pmove_dst_none rest (pmv_dst m)) Hnot_rest) as Hnone_r.
           rewrite Hnone_r, (find_pmove_dst_in ms m Hnd Hm_in), Hdst1. reflexivity.
        -- assert (Hl_not_m : l <> pmv_dst m).
           { intro Heq. subst l. rewrite pm_loc_eqb_refl in Elm. discriminate. }
           destruct (find_pmove_dst l rest) as [mr|] eqn:Er.
           ++ destruct (find_pmove_dst_some rest l mr Er) as [Hmr_in Hmr_dst]. subst l.
              assert (Hmr_ms : In mr ms) by (apply Hiff; right; exact Hmr_in).
              rewrite (find_pmove_dst_in ms mr Hnd Hmr_ms).
              unfold eval_pm_src.
              destruct (pmv_src mr) as [l' | n | g] eqn:Es; [|reflexivity | reflexivity].
              rewrite Hother1 by (exact (Hnot_dst_src mr l' Hmr_in Es)).
              reflexivity.
           ++ apply find_pmove_dst_none in Er.
              destruct (find_pmove_dst l ms) as [mm|] eqn:Em; [|exact (Hother1 l Hl_not_m)].
              destruct (find_pmove_dst_some ms l mm Em) as [Hmm_in Hmm_dst]. subst l.
              apply Hiff in Hmm_in. destruct Hmm_in as [<- | Hmm_r]; [contradiction|].
              exfalso. apply Er. apply in_map. exact Hmm_r.
      * assert (Hnot_tmp : forall m, In m ms -> pmv_dst m <> PmCycleTmp).
        { intros m Hm. rewrite Forall_forall in Hwf. exact (proj1 (Hwf m Hm)). }
        destruct (no_ready_cycle_tmp_unread ms Hnd Hnot_tmp Epick) as [Hunread Hall].
        assert (Hm0_in : In m0 ms) by (unfold ms; left; reflexivity).
        pose proof (Hnot_tmp m0 Hm0_in) as Hm0_neq.
        destruct (emit_save_cycle_tmp_sound sym_env st (pmv_dst m0) Hcan Hm0_neq)
          as [st1 [Hexec1 [Hcan1 [Htmp1 Hother1]]]].
        assert (Hacc1 : pm_exec_lines sym_env st0 (rev (rev_append (emit_save_cycle_tmp (pmv_dst m0)) acc)) = Some st1).
        { rewrite rev_append_rev, rev_app_distr, rev_involutive.
          rewrite (pm_exec_lines_app sym_env _ _ st0 st Hacc). exact Hexec1. }
        destruct (subst_pmove_src_sound sym_env st st1 (pmv_dst m0) ms
                    Hcan Hcan1 Hm0_neq Hunread Hnd Hwf Htmp1 Hother1 (Hall m0 Hm0_in))
          as [Hnd' [Hwf' [Hlen' [Hread' Hsim']]]].
        assert (Hmeas' : (pmoves_measure (subst_pmove_src (pmv_dst m0) ms []) < fuel')%nat).
        { unfold pmoves_measure in *.
          change (loc_read_in_pmoves PmCycleTmp (m0 :: ms_tl)) with (loc_read_in_pmoves PmCycleTmp ms) in Hmeas.
          change (length (m0 :: ms_tl)) with (length ms) in Hmeas.
          rewrite Hunread in Hmeas. rewrite Hread'.
          assert (Hpos : (1 <= length ms)%nat) by (unfold ms; simpl; lia).
          assert (Hq_ex : exists x, In x (subst_pmove_src (pmv_dst m0) ms [])).
          { apply loc_read_in_pmoves_exists in Hread'.
            destruct Hread' as [x [Hx _]]. exists x. exact Hx. }
          destruct Hq_ex as [x Hx].
          assert (Hpos' : (1 <= length (subst_pmove_src (pmv_dst m0) ms []))%nat).
          { destruct (subst_pmove_src (pmv_dst m0) ms []); [contradiction | simpl; lia]. }
          lia. }
        destruct (IH sym_env (subst_pmove_src (pmv_dst m0) ms [])
                    (rev_append (emit_save_cycle_tmp (pmv_dst m0)) acc) st0 st1
                    Hmeas' Hacc1 Hcan1 Hnd' Hwf')
          as [st_end [Hend [Hcan_end Hsim_end]]].
        exists st_end. split; [exact Hend | split; [exact Hcan_end|]].
        intros l Hl_neq. rewrite (Hsim_end l Hl_neq).
        exact (Hsim' l Hl_neq).
Qed.

(** Well-formedness of a complete parallel-move list `ms` in initial state `st0`. *)
Definition pmove_list_wf (st0 : pm_mach) (ms : list pmove) : Prop :=
  pm_mach_canonical st0 /\
  NoDup (map pmv_dst ms) /\
  loc_read_in_pmoves PmCycleTmp ms = false /\
  Forall (pmove_wf (pm_mach_env st0)) ms.

(** Whole-scheduler parallel-move soundness: for any well-formed list
    `ms`, [compile_pmoves] emits x86-64 instructions that execute
    without error or fuel exhaustion in [pm_exec_lines] and establish
    [simul_pmoves] on every allocatable register and frame slot. *)
Theorem compile_pmoves_sound : forall sym_env st0 ms,
  pmove_list_wf st0 ms ->
  exists st_end,
    pm_exec_lines sym_env st0 (compile_pmoves ms) = Some st_end /\
    pm_mach_canonical st_end /\
    (forall l, l <> PmCycleTmp ->
       pm_mach_env st_end l = simul_pmoves sym_env (pm_mach_env st0) ms l).
Proof.
  intros sym_env st0 ms [Hcan [Hnd [Hunread Hwf]]].
  unfold compile_pmoves.
  destruct (drop_nop_pmoves_sound sym_env st0 ms Hcan Hnd Hunread Hwf)
    as [Hnd_c [Hunread_c [Hwf_c Hsim_c]]].
  set (clean := drop_nop_pmoves_acc ms []) in *.
  assert (Hmeas : (pmoves_measure clean < S (2 * length clean))%nat).
  { unfold pmoves_measure. rewrite Hunread_c. lia. }
  destruct (compile_pmoves_fuel_sound (S (2 * length clean)) sym_env clean [] st0 st0
              Hmeas eq_refl Hcan Hnd_c Hwf_c)
    as [st_end [Hexec [Hcan_end Hsim_end]]].
  exists st_end. split; [exact Hexec | split; [exact Hcan_end|]].
  intros l Hl_neq. rewrite (Hsim_end l Hl_neq). exact (Hsim_c l).
Qed.

(** Corollary: [compile_pmoves] never emits a [todo] line (`"parallel move fuel"`
    or `"cycle tmp dst"`) on any well-formed move list. *)
Corollary compile_pmoves_no_todo : forall st0 ms,
  pmove_list_wf st0 ms ->
  first_todo (compile_pmoves ms) = None.
Proof.
  intros st0 ms Hwf.
  destruct (compile_pmoves_sound (fun _ => 0) st0 ms Hwf) as [st_end [Hexec _]].
  exact (pm_exec_lines_no_todo (fun _ => 0) (compile_pmoves ms) st0 st_end Hexec).
Qed.

(** ## 5. Concrete [build_rctx] frame separation, callee-saves and root slots *)

(** [key_term] is injective, so distinct frame [key]s never collide in [nmap]. *)
Lemma key_term_inj : forall k1 k2,
  key_term k1 = key_term k2 -> k1 = k2.
Proof.
  induction k1 as [n1 | n1 | p1 i1 | | | | x1 s1 | k1' IH | x1];
    intros [n2 | n2 | p2 i2 | | | | x2 s2 | k2' | x2] H;
    simpl in H; try discriminate; try reflexivity.
  - injection H as ->. reflexivity.
  - injection H as ->. reflexivity.
  - injection H as Hp ->. destruct p1, p2; simpl in Hp; try discriminate; reflexivity.
  - injection H as -> ->. reflexivity.
  - injection H as H'. f_equal. apply IH. exact H'.
  - injection H as ->. reflexivity.
Qed.

(** [round16] is never less than its input. *)
Lemma round16_ge : forall n, n <= round16 n.
Proof.
  intro n. unfold round16, fifteen, sixteen.
  pose proof (Z_div_mod_eq_full (n + 15) 16) as Hdiv.
  pose proof (Z.mod_pos_bound (n + 15) 16 ltac:(lia)) as Hmod.
  lia.
Qed.

(** Non-negative size predicate on one frame [key]. *)
Definition key_local_nonneg (k : key) : Prop :=
  match k with
  | KLocal _ sz => 0 <= sz
  | _ => True
  end.

(** Every named local in `fr_plain fr` has non-negative byte size. *)
Definition frame_locals_nonneg (fr : frame) : Prop :=
  Forall key_local_nonneg (fr_plain fr).

(** [rplain_keys] keeps a subset of `fr_plain fr`, so its locals too
    have non-negative size. *)
Lemma rplain_keys_nonneg : forall nreg fr,
  frame_locals_nonneg fr -> Forall key_local_nonneg (rplain_keys nreg fr).
Proof.
  intros nreg fr H. unfold rplain_keys, frame_locals_nonneg in *.
  apply Forall_forall. intros k Hk. apply filter_In in Hk.
  exact (proj1 (Forall_forall _ _) H k (proj1 Hk)).
Qed.

(** Folding [plain_slot] keeps all plain-slot offsets in `(0, off1]`. *)
Lemma plain_slot_bounds : forall ks slots0 locals0 off0,
  Forall key_local_nonneg ks ->
  0 <= off0 ->
  (forall t o, nm_find t slots0 = Some o -> 0 < o <= off0) ->
  off0 <= snd (fold_left plain_slot ks (slots0, locals0, off0)) /\
  (forall t o,
     nm_find t (fst (fst (fold_left plain_slot ks (slots0, locals0, off0)))) = Some o ->
     0 < o <= snd (fold_left plain_slot ks (slots0, locals0, off0))).
Proof.
  induction ks as [|k ks' IH]; intros slots0 locals0 off0 Hfa Hoff Hsl; cbn [fold_left].
  - cbn [fst snd]. split; [lia | exact Hsl].
  - inversion Hfa as [| ? ? Hk Hfa']; subst.
    assert (Hstep :
              off0 < snd (plain_slot (slots0, locals0, off0) k) /\
              (forall t o,
                 nm_find t (fst (fst (plain_slot (slots0, locals0, off0) k))) = Some o ->
                 0 < o <= snd (plain_slot (slots0, locals0, off0) k))).
    { unfold key_local_nonneg in Hk.
      destruct k as [n | n | [| |] i | | | | x sz | k' | x]; cbn [plain_slot fst snd];
        try (split; [unfold eight; lia |
                     intros t o Hf; rewrite nm_find_add in Hf;
                     destruct (name_eqb t _);
                       [injection Hf as <-; unfold eight; lia | pose proof (Hsl t o Hf); unfold eight; lia]]).
      - split; [unfold sixteen; lia |].
        intros t o Hf. rewrite nm_find_add in Hf.
        destruct (name_eqb t _); [injection Hf as <-; unfold sixteen; lia | pose proof (Hsl t o Hf); unfold sixteen; lia].
      - pose proof (round16_ge sz) as Hpad.
        pose proof (round16_ge (off0 + round16 sz)) as Hpay.
        split; [unfold eight; lia |].
        intros t o Hf. pose proof (Hsl t o Hf). unfold eight; lia. }
    destruct (plain_slot (slots0, locals0, off0) k) as [[s1 l1] o1]; cbn [fst snd] in Hstep.
    destruct Hstep as [Hlt1 Hsl1].
    destruct (IH s1 l1 o1 Hfa' ltac:(lia) Hsl1) as [Hle2 Hsl2].
    split; [lia | exact Hsl2].
Qed.

(** Pure recursive specification of [place_callee_saves]. *)
Fixpoint saves_from (rs : list hreg) (off : Z) : list (hreg * Z) :=
  match rs with
  | [] => []
  | r :: rs' => (r, off + eight) :: saves_from rs' (off + eight)
  end.

(** [place_callee_saves] produces [saves_from] and `off + 8 * length rs`. *)
Lemma place_callee_saves_spec : forall rs off acc,
  place_callee_saves rs off acc =
  (rev acc ++ saves_from rs off, off + eight * Z.of_nat (length rs)).
Proof.
  induction rs as [|r rs' IH]; intros off acc; cbn [place_callee_saves saves_from length].
  - unfold rev'. rewrite <- rev_alt, app_nil_r. f_equal. unfold eight; lia.
  - rewrite IH; cbn [rev]; rewrite <- app_assoc; cbn [app]. f_equal. unfold eight; lia.
Qed.

(** Every offset in [saves_from] lies strictly above `off` and at most `off + 8 * length rs`. *)
Lemma saves_from_bounds : forall rs off r o,
  In (r, o) (saves_from rs off) ->
  off < o <= off + eight * Z.of_nat (length rs).
Proof.
  induction rs as [|r0 rs' IH]; intros off r o Hin; cbn [saves_from length In] in *; [contradiction|].
  destruct Hin as [Heq | Hin'].
  - injection Heq as <- <-. unfold eight; lia.
  - pose proof (IH (off + eight) r o Hin'). unfold eight in *; lia.
Qed.

(** Distinct offsets in [saves_from]. *)
Lemma saves_from_offs_gt : forall rs off r o,
  In (r, o) (saves_from rs off) -> off < o.
Proof.
  intros rs off r o H. exact (proj1 (saves_from_bounds rs off r o H)).
Qed.

(** Folding [lower_slot] keeps plain slots in `(0, plain_bytes0]` and places
    root slots in `[plain_bytes + 8, base - 16]`. *)
Lemma lower_slot_bounds : forall rks plain_bytes0 plain_bytes base i0 slots0,
  0 <= i0 ->
  plain_bytes0 <= plain_bytes ->
  plain_bytes + sixteen + eight * (i0 + Z.of_nat (length rks)) <= base ->
  (forall t o, nm_find t slots0 = Some o ->
     (0 < o <= plain_bytes0) \/ (plain_bytes + eight <= o <= base - sixteen)) ->
  forall t o,
    nm_find t (fst (fold_left (lower_slot base) rks (slots0, i0))) = Some o ->
    (0 < o <= plain_bytes0) \/ (plain_bytes + eight <= o <= base - sixteen).
Proof.
  induction rks as [|rk rks' IH]; intros plain_bytes0 plain_bytes base i0 slots0 Hi0 Hpb Hbase Hsl.
  - exact Hsl.
  - simpl length in Hbase. rewrite Nat2Z.inj_succ in Hbase.
    pose proof (Nat2Z.is_nonneg (length rks')) as Hlen_nn.
    cbn [fold_left]; unfold lower_slot at 1.
    apply (IH plain_bytes0 plain_bytes base (i0 + 1)
             (nm_add (key_term rk) (base - sixteen - eight * i0) slots0));
      [lia | exact Hpb | unfold eight, sixteen in *; lia |].
    intros t o Hfind. rewrite nm_find_add in Hfind.
    destruct (name_eqb t (key_term rk)).
    + assert (Ho : base - sixteen - eight * i0 = o) by congruence.
      rewrite <- Ho. right. unfold eight, sixteen in *; lia.
    + exact (Hsl t o Hfind).
Qed.

(** Membership of a duplicate-free root key in `fold_left (lower_slot base)`. *)
Lemma lower_slot_lookup : forall rks base i0 slots0 rk,
  NoDup rks ->
  In rk rks ->
  exists j, (j < length rks)%nat /\
    nm_find (key_term rk) (fst (fold_left (lower_slot base) rks (slots0, i0))) =
    Some (base - sixteen - eight * (i0 + Z.of_nat j)).
Proof.
  induction rks as [|r0 rks' IH]; intros base i0 slots0 rk Hnd Hin;
    cbn [fold_left Datatypes.length In] in *; [contradiction|].
  unfold lower_slot at 1.
  inversion Hnd as [| ? ? Hnotin Hnd']; subst.
  destruct Hin as [-> | Hin'].
  - exists O. split; [lia|].
    replace (i0 + Z.of_nat O) with i0 by lia.
    assert (Hpres : forall ks j sm,
              (~ In rk ks) ->
              nm_find (key_term rk) sm = Some (base - sixteen - eight * i0) ->
              nm_find (key_term rk) (fst (fold_left (lower_slot base) ks (sm, j))) =
              Some (base - sixteen - eight * i0)).
    { induction ks as [|k1 ks1 IHk]; intros j sm Hni Hsm; simpl; [exact Hsm|].
      apply IHk.
      - intro Hc. apply Hni. right. exact Hc.
      - rewrite nm_find_add. destruct (name_eqb (key_term rk) (key_term k1)) eqn:Ek; [|exact Hsm].
        apply term_eqb_eq in Ek. apply key_term_inj in Ek. subst k1.
        exfalso. apply Hni. left. reflexivity. }
    apply Hpres; [exact Hnotin|].
    rewrite nm_find_add, term_eqb_refl. reflexivity.
  - destruct (IH base (i0 + 1) (nm_add (key_term r0) (base - sixteen - eight * i0) slots0)
                rk Hnd' Hin') as [j [Hj Hfind]].
    exists (S j). split; [lia|].
    replace (i0 + Z.of_nat (S j)) with (i0 + 1 + Z.of_nat j) by lia.
    exact Hfind.
Qed.

(** [add_alias_slots] introduces no offsets outside `slots2` and `m`. *)
Lemma add_alias_slots_bounds : forall als slots2 m P,
  (forall t o, nm_find t slots2 = Some o -> P o) ->
  (forall t o, nm_find t m = Some o -> P o) ->
  forall t o, nm_find t (add_alias_slots als slots2 m) = Some o -> P o.
Proof.
  induction als as [|[k1 k2] als' IH]; intros slots2 m P Hs2 Hm t o Hfind; simpl in *.
  - exact (Hm t o Hfind).
  - destruct (nm_find (key_term k2) slots2) as [off|] eqn:Ek2.
    + eapply IH; [exact Hs2 | | exact Hfind].
      intros t' o' Hf'. rewrite nm_find_add in Hf'.
      destruct (name_eqb t' (key_term k1)).
      * injection Hf' as <-. exact (Hs2 (key_term k2) off Ek2).
      * exact (Hm t' o' Hf').
    + eapply IH; [exact Hs2 | exact Hm | exact Hfind].
Qed.

(** [add_alias_slots] maps `(k1, k2)` to `k2`'s offset when `map fst als` has `NoDup`. *)
Lemma add_alias_slots_lookup : forall als slots2 m k1 k2 off,
  NoDup (map fst als) ->
  In (k1, k2) als ->
  nm_find (key_term k2) slots2 = Some off ->
  nm_find (key_term k1) (add_alias_slots als slots2 m) = Some off.
Proof.
  induction als as [|[a1 a2] als' IH]; intros slots2 m k1 k2 off Hnd Hin Hk2; simpl in *; [contradiction|].
  inversion Hnd as [| ? ? Hnotin Hnd']; subst.
  destruct Hin as [Heq | Hin'].
  - injection Heq as -> ->. rewrite Hk2.
    assert (Hpres : forall cs m1,
              (~ In k1 (map fst cs)) ->
              nm_find (key_term k1) m1 = Some off ->
              nm_find (key_term k1) (add_alias_slots cs slots2 m1) = Some off).
    { induction cs as [|[c1 c2] cs1 IHc]; intros m1 Hni Hm1; simpl; [exact Hm1|].
      destruct (nm_find (key_term c2) slots2) as [offc|].
      - apply IHc; [intro Hc; apply Hni; right; exact Hc|].
        rewrite nm_find_add. destruct (name_eqb (key_term k1) (key_term c1)) eqn:Ec; [|exact Hm1].
        apply term_eqb_eq in Ec. apply key_term_inj in Ec. subst c1.
        exfalso. apply Hni. left. reflexivity.
      - apply IHc; [intro Hc; apply Hni; right; exact Hc | exact Hm1]. }
    apply Hpres; [exact Hnotin|].
    rewrite nm_find_add, term_eqb_refl. reflexivity.
  - destruct (nm_find (key_term a2) slots2); eapply IH; eauto.
Qed.

(** Concrete save-slot separation: in [build_rctx], every callee-save
    slot `(r, save_off)` in [rc_saves] lies inside `(0, cx_base)` and
    never collides with any plain, root or aliased frame [slot]. *)
Theorem build_rctx_save_slots_disjoint : forall p names cmap rm r save_off,
  frame_locals_nonneg (pl_frame p) ->
  In (r, save_off) (rc_saves (build_rctx p names cmap rm)) ->
  0 < save_off < cx_base (rc_cx (build_rctx p names cmap rm)) /\
  (forall k, slot (rc_cx (build_rctx p names cmap rm)) k <> Some save_off).
Proof.
  intros p names cmap rm r save_off Hloc Hin.
  unfold build_rctx in *.
  set (fr := pl_frame p) in *.
  pose proof (plain_slot_bounds (rplain_keys (build_name_reg_map names O rm nm_empty) fr) nm_empty nm_empty 0
                (rplain_keys_nonneg _ _ Hloc) ltac:(lia)
                (fun t o H => ltac:(rewrite nm_find_empty in H; discriminate))) as Hpl.
  destruct (fold_left plain_slot (rplain_keys (build_name_reg_map names O rm nm_empty) fr) (nm_empty, nm_empty, 0))
    as [[slots1 locals] plain_bytes0] eqn:Epl.
  cbn [fst snd] in Hpl. destruct Hpl as [Hpb0_nonneg Hsl1].
  set (used_cs := collect_used_cs_acc callee_saved_hregs (ZMap.elements rm) []) in *.
  rewrite place_callee_saves_spec in *.
  cbn [rev app] in *.
  set (plain_bytes := plain_bytes0 + eight * Z.of_nat (length used_cs)) in *.
  set (base := plain_bytes + sixteen + eight * Zlength (fr_roots fr)) in *.
  assert (Hzlen : 0 <= Zlength (fr_roots fr)) by (rewrite Zlength_correct; lia).
  pose proof (Nat2Z.is_nonneg (length used_cs)) as Hcs_nn.
  pose proof (lower_slot_bounds (fr_roots fr) plain_bytes0 plain_bytes base 0 slots1
                ltac:(lia) ltac:(unfold plain_bytes, eight; lia)
                ltac:(rewrite <- Zlength_correct; unfold base; lia)
                (fun t o H => or_introl (Hsl1 t o H))) as Hlow.
  destruct (fold_left (lower_slot base) (fr_roots fr) (slots1, 0)) as [slots2 idx2] eqn:Elow.
  cbn [fst rc_saves rc_cx cx_base cx_slots] in *.
  pose proof (saves_from_bounds used_cs plain_bytes0 r save_off Hin) as Hsave_b.
  split; [unfold base, plain_bytes, sixteen, eight in *; lia|].
  intros k Hslot. unfold slot in Hslot; cbn [cx_slots] in Hslot.
  pose proof (add_alias_slots_bounds (fr_aliases fr) slots2 slots2
                (fun o => (0 < o <= plain_bytes0) \/ (plain_bytes + eight <= o <= base - sixteen))
                Hlow Hlow (key_term k) save_off Hslot) as Hbad.
  unfold plain_bytes, eight in *; lia.
Qed.

(** [hreg_in_pairs] detects any register `r` appearing in `els`. *)
Lemma hreg_in_pairs_spec : forall r els,
  hreg_in_pairs r els = true <-> exists k, In (k, r) els.
Proof.
  intros r els. induction els as [|[k r'] els' IH]; simpl.
  - split; [discriminate | intros [? []]].
  - destruct (hreg_eqb r r') eqn:E.
    + apply hreg_eqb_spec in E. subst r'.
      split; [intros _; exists k; left; reflexivity | auto].
    + rewrite IH. split.
      * intros [k' Hk']. exists k'. right. exact Hk'.
      * intros [k' [Heq | Hk']]; [injection Heq as _ ->; rewrite hreg_eqb_refl in E; discriminate | exists k'; exact Hk'].
Qed.

(** Characterization of [collect_used_cs_acc]. *)
Lemma collect_used_cs_acc_eq : forall cs els acc,
  collect_used_cs_acc cs els acc = rev acc ++ filter (fun r => hreg_in_pairs r els) cs.
Proof.
  induction cs as [|r cs' IH]; intros els acc; simpl.
  - unfold rev'. rewrite <- rev_alt, app_nil_r. reflexivity.
  - destruct (hreg_in_pairs r els); [rewrite IH; simpl; rewrite <- app_assoc; reflexivity | apply IH].
Qed.

(** Every callee-saved register assigned anywhere in `rm` has a dedicated
    save slot in `rc_saves (build_rctx p names cmap rm)`. *)
Theorem build_rctx_used_callee_saved : forall p names cmap rm t r,
  zmap_find_nat t rm = Some r ->
  hreg_callee_saved r = true ->
  In r (map fst (rc_saves (build_rctx p names cmap rm))).
Proof.
  intros p names cmap rm t r Hrm Hcs.
  unfold build_rctx.
  destruct (fold_left plain_slot (rplain_keys (build_name_reg_map names O rm nm_empty) (pl_frame p)) (nm_empty, nm_empty, 0))
    as [[slots1 locals] plain_bytes0].
  rewrite place_callee_saves_spec.
  destruct (fold_left (lower_slot _) (fr_roots (pl_frame p)) (slots1, 0)) as [slots2 _].
  cbn [rc_saves rev app].
  assert (Hfst : forall rs off, map fst (saves_from rs off) = rs).
  { induction rs as [|r0 rs' IH]; intro off; simpl; [reflexivity | rewrite IH; reflexivity]. }
  rewrite Hfst, collect_used_cs_acc_eq. cbn [rev app].
  apply filter_In. split.
  - destruct r; simpl in *; try discriminate; auto 6.
  - apply hreg_in_pairs_spec. exists (Z.of_nat t).
    apply zmap_find_in_elements. exact Hrm.
Qed.

(** Executing [callee_save_stores] over `saves_from rs off` stores each
    `r` in `rs` into its dedicated frame slot while leaving registers and
    all slots `<= off` untouched. *)
Lemma callee_save_stores_exec : forall sym_env rs off st,
  pm_mach_canonical st ->
  exists st_saved,
    pm_exec_lines sym_env st (callee_save_stores (saves_from rs off)) = Some st_saved /\
    pm_mach_canonical st_saved /\
    (forall r', pm_hreg st_saved r' = pm_hreg st r') /\
    (forall off', off' <= off -> pm_slot st_saved off' = pm_slot st off') /\
    (NoDup rs -> forall r o, In (r, o) (saves_from rs off) -> pm_slot st_saved o = pm_hreg st r).
Proof.
  induction rs as [|r0 rs' IH]; intros off st Hcan; simpl.
  - exists st. split; [reflexivity | split; [exact Hcan | split; [intro; reflexivity | split; [intros; reflexivity | intros _ r o []]]]].
  - unfold callee_save_stores in *; simpl.
    rewrite pm_reg64_hreg. simpl.
    set (st1 := pm_set_slot st (- - (off + eight)) (pm_hreg st r0 mod two64)).
    assert (Hcan1 : pm_mach_canonical st1).
    { intros [r' | off' |]; simpl; [exact (Hcan (PmReg r')) | | exact (Hcan PmCycleTmp)].
      destruct (Z.eqb off' (- - (off + eight)));
        [apply Z.mod_pos_bound; unfold two64; lia | exact (Hcan (PmSlot off'))]. }
    destruct (IH (off + eight) st1 Hcan1) as [st_saved [Hexec [Hcan_s [Hreg_s [Hlow_s Hmem_s]]]]].
    exists st_saved. split; [exact Hexec | split; [exact Hcan_s | split; [exact Hreg_s | split]]].
    + intros off' Hoff'. rewrite (Hlow_s off' ltac:(unfold eight; lia)).
      unfold st1; simpl. replace (- - (off + eight)) with (off + eight) by lia.
      destruct (Z.eqb off' (off + eight)) eqn:E; [apply Z.eqb_eq in E; unfold eight in *; lia | reflexivity].
    + intros Hnd r o [Heq | Hin'].
      * injection Heq as -> <-.
        rewrite (Hlow_s (off + eight) ltac:(lia)).
        unfold st1; simpl. replace (- - (off + eight)) with (off + eight) by lia.
        rewrite Z.eqb_refl. apply Z.mod_small. exact (Hcan (PmReg r)).
      * inversion Hnd as [| ? ? Hnotin Hnd']; subst.
        exact (Hmem_s Hnd' r o Hin').
Qed.

(** Executing [callee_save_restores] over `saves_from rs off` loads each
    saved register from its slot while leaving registers outside `rs` unchanged. *)
Lemma callee_save_restores_exec : forall sym_env rs off st_body,
  pm_mach_canonical st_body ->
  NoDup rs ->
  exists st_exit,
    pm_exec_lines sym_env st_body (callee_save_restores (saves_from rs off)) = Some st_exit /\
    (forall r o, In (r, o) (saves_from rs off) -> pm_hreg st_exit r = pm_slot st_body o) /\
    (forall r, ~ In r rs -> pm_hreg st_exit r = pm_hreg st_body r).
Proof.
  induction rs as [|r0 rs' IH]; intros off st_body Hcan Hnd; simpl.
  - exists st_body. split; [reflexivity | split; [intros r o [] | auto]].
  - inversion Hnd as [| ? ? Hnotin Hnd']; subst.
    unfold callee_save_restores in *; simpl.
    rewrite pm_reg64_hreg. simpl.
    set (st1 := pm_set_reg st_body (PrHReg r0) (pm_slot st_body (- - (off + eight)) mod two64)).
    assert (Hcan1 : pm_mach_canonical st1).
    { intros [r' | off' |]; simpl; [| exact (Hcan (PmSlot off')) | exact (Hcan PmCycleTmp)].
      destruct (hreg_eqb r' r0); [apply Z.mod_pos_bound; unfold two64; lia | exact (Hcan (PmReg r'))]. }
    destruct (IH (off + eight) st1 Hcan1 Hnd') as [st_exit [Hexec [Hin_s Hout_s]]].
    exists st_exit. split; [exact Hexec | split].
    + intros r o [Heq | Hin'].
      * injection Heq as -> <-.
        rewrite (Hout_s r Hnotin). unfold st1; simpl.
        rewrite hreg_eqb_refl. replace (- - (off + eight)) with (off + eight) by lia.
        apply Z.mod_small. exact (Hcan (PmSlot (off + eight))).
      * rewrite (Hin_s r o Hin'). reflexivity.
    + intros r Hnot. rewrite (Hout_s r ltac:(intro Hc; apply Hnot; right; exact Hc)).
      unfold st1; simpl. destruct (hreg_eqb r r0) eqn:E; [|reflexivity].
      apply hreg_eqb_spec in E. subst r. exfalso; apply Hnot; left; reflexivity.
Qed.

(** Concrete prologue/epilogue callee-save preservation for [build_rctx]:
    executing [callee_save_stores] on `st_entry`, running any body to
    `st_body` that preserves the disjoint save slots in [rc_saves] and
    leaves unused callee-saved registers untouched, and executing
    [callee_save_restores] restores all five callee-saved registers to
    their entry values. *)
Theorem build_rctx_callee_saves_sound : forall sym_env p names cmap rm st_entry,
  pm_mach_canonical st_entry ->
  exists st_saved,
    pm_exec_lines sym_env st_entry (callee_save_stores (rc_saves (build_rctx p names cmap rm)))
      = Some st_saved /\
    forall st_body,
      pm_mach_canonical st_body ->
      (forall r off, In (r, off) (rc_saves (build_rctx p names cmap rm)) ->
         pm_slot st_body off = pm_slot st_saved off) ->
      (forall r, hreg_callee_saved r = true ->
         ~ In r (map fst (rc_saves (build_rctx p names cmap rm))) ->
         pm_hreg st_body r = pm_hreg st_entry r) ->
      exists st_exit,
        pm_exec_lines sym_env st_body (callee_save_restores (rc_saves (build_rctx p names cmap rm)))
          = Some st_exit /\
        forall r, hreg_callee_saved r = true -> pm_hreg st_exit r = pm_hreg st_entry r.
Proof.
  intros sym_env p names cmap rm st_entry Hcan_e.
  unfold build_rctx.
  destruct (fold_left plain_slot (rplain_keys (build_name_reg_map names O rm nm_empty) (pl_frame p)) (nm_empty, nm_empty, 0))
    as [[slots1 locals] plain_bytes0].
  rewrite place_callee_saves_spec.
  destruct (fold_left (lower_slot _) (fr_roots (pl_frame p)) (slots1, 0)) as [slots2 _].
  cbn [rc_saves rev app].
  set (used_cs := collect_used_cs_acc callee_saved_hregs (ZMap.elements rm) []).
  assert (Hnd_cs : NoDup used_cs).
  { unfold used_cs. rewrite collect_used_cs_acc_eq. cbn [rev app].
    assert (Hnd5 : NoDup callee_saved_hregs).
    { unfold callee_saved_hregs.
      repeat (constructor; [simpl; intuition discriminate|]). constructor. }
    pose proof (nodup_map_filter hreg hreg (fun x => x)
                  (fun r => hreg_in_pairs r (ZMap.elements rm)) callee_saved_hregs) as Hmf.
    rewrite !map_id in Hmf. exact (Hmf Hnd5). }
  destruct (callee_save_stores_exec sym_env used_cs plain_bytes0 st_entry Hcan_e)
    as [st_saved [Hexec_s [_ [_ [_ Hmem_s]]]]].
  exists st_saved. split; [exact Hexec_s|].
  intros st_body Hcan_b Hpres_slots Huntouched.
  destruct (callee_save_restores_exec sym_env used_cs plain_bytes0 st_body Hcan_b Hnd_cs)
    as [st_exit [Hexec_r [Hin_r Hout_r]]].
  exists st_exit. split; [exact Hexec_r|].
  assert (Hfst : map fst (saves_from used_cs plain_bytes0) = used_cs).
  { clear. generalize plain_bytes0. induction used_cs as [|r0 rs IH]; intro off; simpl;
      [reflexivity | rewrite IH; reflexivity]. }
  intros r Hcs.
  destruct (hreg_in_list r used_cs) eqn:Ein.
  - apply hreg_in_list_spec in Ein.
    assert (Hex_off : exists off, In (r, off) (saves_from used_cs plain_bytes0)).
    { rewrite <- Hfst in Ein. apply in_map_iff in Ein.
      destruct Ein as [[r' off] [<- Hin']]. exists off. exact Hin'. }
    destruct Hex_off as [off Hoff].
    rewrite (Hin_r r off Hoff), (Hpres_slots r off Hoff), (Hmem_s Hnd_cs r off Hoff).
    reflexivity.
  - assert (Hnin_real : ~ In r used_cs).
    { intro Hc. apply hreg_in_list_spec in Hc. congruence. }
    rewrite (Hout_r r Hnin_real).
    apply (Huntouched r Hcs). rewrite Hfst. exact Hnin_real.
Qed.

(** Idealized register-indexed save map for `used`. *)
Definition exec_saves (used : list hreg) (entry_regs : hreg -> Z) (save_mem : hreg -> Z)
  : hreg -> Z :=
  fun r => if hreg_in_list r used then entry_regs r else save_mem r.

(** Idealized register-indexed restore map for `used`. *)
Definition exec_restores (used : list hreg) (save_mem : hreg -> Z) (body_regs : hreg -> Z)
  : hreg -> Z :=
  fun r => if hreg_in_list r used then save_mem r else body_regs r.

(** Algebraic round-trip identity on register-indexed maps. *)
Theorem callee_saves_restore_sound :
  forall (used : list hreg) (entry_regs body_regs save_mem0 : hreg -> Z) (r : hreg),
  (hreg_in_list r used = false -> body_regs r = entry_regs r) ->
  exec_restores used (exec_saves used entry_regs save_mem0) body_regs r = entry_regs r.
Proof.
  intros used entry_regs body_regs save_mem0 r Huntouched.
  unfold exec_restores, exec_saves.
  destruct (hreg_in_list r used) eqn:Ein; [reflexivity | apply Huntouched; reflexivity].
Qed.

(** Concrete GC root invariant for [build_rctx]: every pointer temporary
    whose lower key `(KLower (KTmp d), rk)` aliases a root `rk` in
    `fr_roots` resolves in [key_pm_loc] to `Some (PmSlot off)` for a
    positive frame offset inside the collector's `lowers[]` root array. *)
Theorem build_rctx_root_lower_slot : forall p names cmap rm d rk,
  frame_locals_nonneg (pl_frame p) ->
  NoDup (fr_roots (pl_frame p)) ->
  NoDup (map fst (fr_aliases (pl_frame p))) ->
  In rk (fr_roots (pl_frame p)) ->
  In (KLower (KTmp d), rk) (fr_aliases (pl_frame p)) ->
  exists off,
    key_pm_loc (build_rctx p names cmap rm) (KLower (KTmp d)) = Some (PmSlot off) /\
    cx_base (rc_cx (build_rctx p names cmap rm)) - sixteen - eight * Zlength (fr_roots (pl_frame p))
      < off <= cx_base (rc_cx (build_rctx p names cmap rm)) - sixteen.
Proof.
  intros p names cmap rm d rk Hloc Hnd_r Hnd_a Hin_r Hin_a.
  unfold build_rctx.
  set (fr := pl_frame p) in *.
  pose proof (plain_slot_bounds (rplain_keys (build_name_reg_map names O rm nm_empty) fr) nm_empty nm_empty 0
                (rplain_keys_nonneg _ _ Hloc) ltac:(lia)
                (fun t o H => ltac:(rewrite nm_find_empty in H; discriminate))) as [Hpb0 _].
  destruct (fold_left plain_slot (rplain_keys (build_name_reg_map names O rm nm_empty) fr) (nm_empty, nm_empty, 0))
    as [[slots1 locals] plain_bytes0].
  set (used_cs := collect_used_cs_acc callee_saved_hregs (ZMap.elements rm) []).
  rewrite place_callee_saves_spec. cbn [rev app].
  set (plain_bytes := plain_bytes0 + eight * Z.of_nat (length used_cs)).
  set (base := plain_bytes + sixteen + eight * Zlength (fr_roots fr)).
  destruct (lower_slot_lookup (fr_roots fr) base 0 slots1 rk Hnd_r Hin_r)
    as [j [Hj Hfind_rk]].
  destruct (fold_left (lower_slot base) (fr_roots fr) (slots1, 0)) as [slots2 idx2].
  cbn [fst rc_cx cx_base] in Hfind_rk |- *.
  pose proof (add_alias_slots_lookup (fr_aliases fr) slots2 slots2
                (KLower (KTmp d)) rk (base - sixteen - eight * (0 + Z.of_nat j))
                Hnd_a Hin_a Hfind_rk) as Halias.
  exists (base - sixteen - eight * (0 + Z.of_nat j)).
  split.
  - unfold key_pm_loc, slot; cbn [rc_cx cx_slots]. rewrite Halias. reflexivity.
  - rewrite Zlength_correct. unfold eight, sixteen; lia.
Qed.

(** Lookup of `KLower k` in [key_pm_loc] never returns a register
    location [PmReg]. *)
Theorem lower_key_never_hreg : forall rc k r,
  key_pm_loc rc (KLower k) <> Some (PmReg r).
Proof.
  intros rc k r. simpl.
  destruct (slot (rc_cx rc) (KLower k)); intro H; discriminate.
Qed.

(** ## 6. Executable rejection examples for [valid_alloc] *)

Definition ex_cmap2 : ZMap.t class :=
  zmap_add_nat 0%nat L (zmap_add_nat 1%nat L (zmap_add_nat 2%nat Double (ZMap.empty class))).

Definition ex_rm1 (t : nat) (r : hreg) : ZMap.t hreg :=
  zmap_add_nat t r (ZMap.empty hreg).

Definition ex_rb_collision : rblock :=
  mkRBlock 0%nat [] [] [mkRInst [0%nat; 1%nat] [] RCallNone] [].

Definition ex_rm_collision : ZMap.t hreg :=
  zmap_add_nat 0%nat HRbx (ex_rm1 1%nat HRbx).

(** Two live parameters mapped to the same register `HRbx` are rejected. *)
Example ex_rejects_collision :
  valid_alloc ex_cmap2 [0%nat; 1%nat] [ex_rb_collision] ex_rm_collision = false.
Proof. reflexivity. Qed.

Definition ex_rb_after_call : rblock :=
  mkRBlock 0%nat [] [] [mkRInst [] [] RCallAfterReads] [0%nat].

(** A caller-saved register `HR10` live across `RCallAfterReads` is rejected,
    while callee-saved `HRbx` is accepted. *)
Example ex_rejects_r10_call :
  valid_alloc ex_cmap2 [0%nat] [ex_rb_after_call] (ex_rm1 0%nat HR10) = false /\
  valid_alloc ex_cmap2 [0%nat] [ex_rb_after_call] (ex_rm1 0%nat HRbx) = true.
Proof. split; reflexivity. Qed.

Definition ex_rb_during_call : rblock :=
  mkRBlock 0%nat [] [] [mkRInst [0%nat] [] RCallDuringReads] [].

(** Input of `RCallDuringReads` (`AStorePointer` / `ADispatch`) in `HR11`
    is rejected even when dead after the instruction. *)
Example ex_rejects_r11_read_call :
  valid_alloc ex_cmap2 [0%nat] [ex_rb_during_call] (ex_rm1 0%nat HR11) = false /\
  valid_alloc ex_cmap2 [0%nat] [ex_rb_during_call] (ex_rm1 0%nat HR12) = true.
Proof. split; reflexivity. Qed.

Definition ex_rb_poll0 : rblock :=
  mkRBlock 0%nat [(1%nat, false)] [] [] [].

Definition ex_rb_poll1 : rblock :=
  mkRBlock 1%nat [(1%nat, true)] [(1%nat, [(0%nat, Some 0%nat); (1%nat, Some 1%nat)])] [] [1%nat].

(** A phi destination in `HR10` on a `Poll` loop back-edge is rejected,
    while `HR13` is accepted. *)
Example ex_rejects_r10_poll :
  valid_alloc ex_cmap2 [0%nat] [ex_rb_poll0; ex_rb_poll1] (ex_rm1 1%nat HR10) = false /\
  valid_alloc ex_cmap2 [0%nat] [ex_rb_poll0; ex_rb_poll1] (ex_rm1 1%nat HR13) = true.
Proof. split; reflexivity. Qed.

Definition ex_rb_float : rblock :=
  mkRBlock 0%nat [] [] [] [2%nat].

(** Assigning a float temporary (`Double`) to a general register is rejected. *)
Example ex_rejects_float :
  valid_alloc ex_cmap2 [2%nat] [ex_rb_float] (ex_rm1 2%nat HRbx) = false.
Proof. reflexivity. Qed.

(** Non-vacuity witness for [valid_alloc_sound]: a 2-block loop CFG with
    mapped parameters/phis (`0 -> HRbx`, `1, 2 -> HR13` reusing `HR13`
    once `1` dies), a call inside the loop (`RCallAfterReads`), a `Poll`
    back-edge (`1 -> 1`), and two unmapped temporaries (`3` and `4`)
    sharing physical frame slot `-8`. *)
Definition ex_loop_cmap : ZMap.t class :=
  zmap_add_nat 0%nat L (zmap_add_nat 1%nat L (zmap_add_nat 2%nat L
    (zmap_add_nat 3%nat L (zmap_add_nat 4%nat L (ZMap.empty class))))).

Definition ex_loop_rm : ZMap.t hreg :=
  zmap_add_nat 0%nat HRbx (zmap_add_nat 1%nat HR13 (zmap_add_nat 2%nat HR13 (ZMap.empty hreg))).

Definition ex_loop_rb0 : rblock :=
  mkRBlock 0%nat [(1%nat, false)] [] [mkRInst [3%nat] [4%nat] RCallNone] [4%nat].

Definition ex_loop_rb1 : rblock :=
  mkRBlock 1%nat [(1%nat, true)]
    [(1%nat, [(0%nat, Some 0%nat); (1%nat, Some 2%nat)])]
    [mkRInst [1%nat; 0%nat] [2%nat] RCallAfterReads]
    [2%nat].

Definition ex_loop_rbs : list rblock := [ex_loop_rb0; ex_loop_rb1].

Definition ex_loop_slot (t : nat) : Z := -8.

Definition ex_add_ie : inst_exec :=
  mkInstExec (fun vs => [fold_left Z.add vs 0]) (fun _ => 99) (fun _ => 77).

Definition ex_loop_trace : list cfg_edge_step :=
  [mkEdgeStep [ex_add_ie] 1%nat false (fun _ => 0) (fun _ => 55);
   mkEdgeStep [ex_add_ie] 1%nat true (fun _ => 0) (fun _ => 55)].

Example ex_valid_alloc_loop : forall tenv0 ms0,
  valid_alloc ex_loop_cmap [0%nat; 3%nat] ex_loop_rbs ex_loop_rm = true /\
  (state_agrees ex_loop_rm ex_loop_slot [0%nat; 3%nat] tenv0 ms0 ->
   cfg_trace_agrees ex_loop_rm ex_loop_slot ex_loop_rbs 0%nat
     ex_loop_trace [ex_add_ie] tenv0 ms0).
Proof.
  intros tenv0 ms0.
  assert (Hval : valid_alloc ex_loop_cmap [0%nat; 3%nat] ex_loop_rbs ex_loop_rm = true)
    by (vm_compute; reflexivity).
  split; [exact Hval|].
  intro Hag0.
  assert (Hwf : rblocks_wf ex_loop_rbs).
  { unfold rblocks_wf, rblock_succs_in_range, ex_loop_rbs, ex_loop_rb0, ex_loop_rb1.
    simpl. split; [auto | split; [|reflexivity]].
    constructor; [constructor; [simpl; lia | constructor] |
                  constructor; [constructor; [simpl; lia | constructor] | constructor]]. }
  assert (Htr : cfg_trace_valid ex_loop_rbs 0%nat ex_loop_trace [ex_add_ie]).
  { unfold ex_loop_rbs, ex_loop_trace, ex_loop_rb0, ex_loop_rb1, ex_add_ie.
    simpl. repeat split; auto. }
  assert (Hus : cfg_trace_slot_ok ex_loop_rm ex_loop_slot ex_loop_rbs 0%nat ex_loop_trace).
  { unfold ex_loop_rbs, ex_loop_trace, ex_loop_rb0, ex_loop_rb1.
    cbn [cfg_trace_slot_ok cfg_trace_need nth_error insts_slot_ok insts_need
         rb_insts rb_phis rb_jump_uses ces_succ ces_ies ri_defs ri_uses
         phi_defs_raw phi_edge_uses_raw lookup_phi_edge_src live_without_list
         live_without app unmapped_slot_ok].
    repeat split; intros d t Hd Ht Hdm Htm Hneq;
      cbn [In] in Hd, Ht;
      destruct Hd as [<- | Hd]; try contradiction;
      repeat (destruct Ht as [<- | Ht];
              [try contradiction; vm_compute in Hdm; try discriminate; vm_compute in Htm; try discriminate
              |]);
      try contradiction. }
  assert (Hunm : forall t, zmap_find_nat t ex_loop_rm = None ->
                   In t (cfg_trace_need ex_loop_rbs 0%nat ex_loop_trace) ->
                   In t [0%nat; 3%nat]).
  { intros t Hrm Hin.
    unfold ex_loop_rbs, ex_loop_trace, ex_loop_rb0, ex_loop_rb1 in Hin.
    cbn [cfg_trace_need nth_error insts_need rb_insts rb_phis rb_jump_uses
         ces_succ ri_defs ri_uses phi_defs_raw phi_edge_uses_raw
         lookup_phi_edge_src live_without_list live_without app In] in Hin.
    repeat (destruct Hin as [<- | Hin];
            [first [left; reflexivity | right; left; reflexivity
                   | vm_compute in Hrm; discriminate]
            |]);
      contradiction. }
  destruct (valid_alloc_sound ex_loop_cmap [0%nat; 3%nat] ex_loop_rbs ex_loop_rm
              ex_loop_slot ex_loop_trace [ex_add_ie] Hwf Hval Htr Hus Hunm)
    as [_ [_ Hsim]].
  exact (Hsim tenv0 ms0 Hag0).
Qed.
