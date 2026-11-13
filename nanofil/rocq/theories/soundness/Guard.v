(** Optimizing compilers can replace repeated bounds checks with a
    lightweight guard or a cached capability limit. In Fil-C, a
    [[renew_if]] instruction renews a pointer's [[capability]] when an
    earlier [[span test]] succeeded, and a `check_limit` instruction
    verifies bounds against a saved [[limit]] value. Both forms avoid
    re-running a full bounds check, so the machine stops with
    [[unchecked]] if the guard or limit disagrees with the pointer's
    actual object.

    This module proves that neither instruction can fail as `unchecked`
    once the [[validator]] accepts it. For `renew_if`, a zero guard
    falls back to a full [[check]] (which never produces `unchecked`),
    while a nonzero guard guarantees that the tested span fits inside
    the object and encloses the renewed range. Because the span test
    changes no memory, the tested object either remains intact or has
    been freed, and the [[validator]] bounds the span's width below 2^64
    so address arithmetic cannot wrap. For `check_limit`, a
    [[lower chain]] connects the pointer to the source whose capability
    and size the limit recorded. *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Maps Syntax Cfg Values Memory Runtime Ops Semantics Machine Validate
  Dominance Interval Sites Identity Coverage Walk Invariant Persistence Single Evidence Chain Renew.
Import ListNotations.
Open Scope Z_scope.

(** ## Span tests

    A span test checks at runtime whether a pointer's byte range lies
    inside a live object and returns a boolean integer. In this section,
    we establish the arithmetic and memory persistence properties that
    make a nonzero span test strong enough to justify a later renewal. *)

(** The [[validator]] requires every [[span test]] in a valid module to
    test a nonempty range with signed 64-bit offsets. Lemma
    [span_test_ok] recovers those bounds from [inst_valid]. *)
Lemma span_test_ok : forall md f b gn glo ghi n0,
  checked_module md -> In (IFunc f) md -> In b (fn_blocks f) ->
  In (Let gn W (SpanTest glo ghi) [Tmp n0]) (b_insts b) ->
  glo < ghi /\ - 2 ^ 63 <= glo /\ ghi <= 2 ^ 63 - 1.
Proof.
  intros md f b gn glo ghi n0 Hmd Hin Hb Hi.
  destruct (inst_valid _ _ _ _ Hmd Hin Hb Hi) as [cls Hv]. simpl in Hv.
  repeat match goal with H : (_ && _) = true |- _ => apply andb_true_iff in H as [? ?] end.
  repeat match goal with
         | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
         | H : (_ <=? _) = true |- _ => apply Z.leb_le in H
         end.
  lia.
Qed.

(** Suppose a span test verified that a range around base address B
    fits inside an object that ends at or below 2^48. If a derived
    pointer A lies at a known offset from B, then any sub-range around
    A that fits inside the tested span also fits inside the object. The
    width bound below 2^64 ensures that the span's endpoints do not wrap
    around the address space. *)
Lemma guard_inside : forall base end_ B x glo ghi A lo hi,
  base <= raw_address B glo -> raw_address B glo < raw_address B ghi -> raw_address B ghi <= end_ ->
  end_ <= 2 ^ 48 -> glo < ghi -> ghi - glo < 2 ^ 64 ->
  A mod 2 ^ 64 = (B + x) mod 2 ^ 64 -> glo <= x + lo -> x + hi <= ghi -> lo < hi ->
  base <= raw_address A lo /\ raw_address A lo + (hi - lo) <= end_.
Proof.
  intros base end_ B x glo ghi A lo hi Hb HLH Hend Hfit Hg Hw HA Hlo Hhi Hl.
  unfold raw_address in *.
  pose proof (Z.div_mod (B + glo) (2 ^ 64) ltac:(lia)) as DL.
  pose proof (Z.div_mod (B + ghi) (2 ^ 64) ltac:(lia)) as DH.
  pose proof (Z.mod_pos_bound (B + glo) (2 ^ 64) ltac:(lia)) as RL.
  pose proof (Z.mod_pos_bound (B + ghi) (2 ^ 64) ltac:(lia)) as RH.
  set (L := (B + glo) mod 2 ^ 64) in *. set (H := (B + ghi) mod 2 ^ 64) in *.
  set (qL := (B + glo) / 2 ^ 64) in *. set (qH := (B + ghi) / 2 ^ 64) in *.
  (* The two reductions take off the same multiple of 2^64. *)
  assert (Eq : qH = qL) by lia.
  assert (EA : (A + lo) mod 2 ^ 64 = L + (x + lo - glo)).
  { rewrite <- Z.add_mod_idemp_l, HA, Z.add_mod_idemp_l by lia.
    symmetry. apply (Z.mod_unique _ _ qL); lia. }
  rewrite EA. lia.
Qed.

(** Suppose an access lies inside an object's bounds as they were in an
    earlier memory. In any later memory that [persists] from it,
    renewing a pointer to that object either succeeds, traps as
    misaligned or read-only, or finds the object freed; it never fails
    as [[unchecked]]. *)
Lemma renew_inside : forall m1 m c base reg a size r al p,
  (c = Obj base \/ c = Ro base) -> object_region base (m_regions m1) = Some reg ->
  base <= a -> a + size <= r_end reg -> 0 < size -> persists m1 m -> ptr_cap p = c ->
  exists chk, access_res m a c size r al = Some chk /\
    (chk = RTrap Misaligned \/ exists rr, renew_res chk p m = Some rr /\ forall why, rr <> RUnchecked why).
Proof.
  intros m1 m c base reg a size r al p Hc E Hb He Hs Hp Hpc.
  pose proof (object_region_base _ _ _ E) as Hrb.
  unfold access_res, cap_access_res, readonly_access_res, aligned_res.
  destruct (Hp _ _ E) as [E' | E']; destruct Hc as [-> | ->]; rewrite E'.
  - (* an object as it was: the access is inside *)
    replace ((base <=? a) && (a + size <=? r_end reg)) with true
      by (symmetry; apply andb_true_iff; split; apply Z.leb_le; lia).
    destruct (a mod al =? 0); eexists; (split; [reflexivity|]); [right | left; reflexivity].
    eexists. split; [reflexivity | discriminate].
  - (* a read-only object as it was *)
    replace ((base <=? a) && (a + size <=? r_end reg)) with true
      by (symmetry; apply andb_true_iff; split; apply Z.leb_le; lia).
    destruct r; [destruct (a mod al =? 0)|]; eexists; (split; [reflexivity|]);
      first [left; reflexivity | right; eexists; split; [reflexivity | discriminate]].
  - (* freed since: out of bounds, on a freed object *)
    simpl. rewrite Hrb.
    replace ((base <=? a) && (a + size <=? base)) with false
      by (symmetry; apply andb_false_iff; destruct (Z.le_gt_cases base a);
          [right; apply Z.leb_gt; lia | left; apply Z.leb_gt; lia]).
    eexists. split; [reflexivity|]. right. unfold renew_res. rewrite Hpc, E'.
    eexists. split; [reflexivity | discriminate].
  - simpl. rewrite Hrb.
    replace ((base <=? a) && (a + size <=? base)) with false
      by (symmetry; apply andb_false_iff; destruct (Z.le_gt_cases base a);
          [right; apply Z.leb_gt; lia | left; apply Z.leb_gt; lia]).
    eexists. split; [reflexivity|]. right. unfold renew_res. rewrite Hpc, E'.
    eexists. split; [reflexivity | discriminate].
Qed.

(** Turning an access check result into a plain check outcome never
    introduces [RUnchecked], because [cap_access_res] itself never
    returns `RUnchecked`. *)
Lemma checked_res_access : forall m a c size r al chk w why,
  access_res m a c size r al = Some chk -> checked_res chk w <> RUnchecked why.
Proof.
  intros m a c size r al chk w why H E. destruct chk; try discriminate E.
  injection E as ->. exact (cap_access_res_checked _ _ _ _ _ _ _ H).
Qed.

(** If a [[lower chain]] links a temporary name to a single-definition
    source, then that temporary also has a [[single definition]]. *)
Lemma lower_chain_once : forall once fuel d n0,
  once_has once n0 = true -> lower_chain once fuel d (Tmp n0) = true ->
  forall y, d = Tmp y -> once_has once y = true.
Proof.
  intros once fuel d n0 Ho H y ->. destruct fuel as [|fuel]; simpl in H.
  - rewrite orb_false_r in H. apply name_eqb_true in H. subst. exact Ho.
  - apply orb_true_iff in H as [H | H]; [apply name_eqb_true in H; subst; exact Ho|].
    unfold once_has. destruct (lookup y once); [reflexivity | discriminate H].
Qed.

(** The section below proves frame-level soundness for `renew_if` and
    `check_limit` at a single program point. We assume a reachable block
    of a valid module where every [[single definition]] in scope
    replays except `check_ahead`. *)
Section Guard.

Variables (ge : genv) (md : module) (fr : frame) (m : Memory.mem) (l : name) (k : Z).
Hypothesis Hmd : checked_module md.
Hypothesis Hin : In (IFunc (fr_fn fr)) md.
Hypothesis Hr : is_reachable (fn_doms (fr_fn fr)) l = true.
Hypothesis Hs : scope_plain ge fr m.
Hypothesis Hpt : point_site (fr_fn fr) (fr_at fr) = Some (l, k).

(** When a [[span test]] dominates the current program point and holds a
    nonzero integer, the tested pointer still points to an object whose
    span lay inside its bounds in a persisting memory. *)
Lemma span_guard_holds : forall gn glo ghi n0,
  lookup gn (single_definitions (fr_fn fr)) = Some (DInst (Let gn W (SpanTest glo ghi) [Tmp n0])) ->
  once_has (single_definitions (fr_fn fr)) n0 = true -> dominating (fr_fn fr) l k gn ->
  exists v, lookup gn (fr_env fr) = Some (WInt v) /\
    (v <> 0 -> exists pb base reg m1,
       lookup n0 (fr_env fr) = Some (WPtr pb) /\ (ptr_cap pb = Obj base \/ ptr_cap pb = Ro base) /\
       object_region base (m_regions m1) = Some reg /\
       base <= raw_address (ptr_addr pb) glo /\ raw_address (ptr_addr pb) glo < raw_address (ptr_addr pb) ghi /\
       raw_address (ptr_addr pb) ghi <= r_end reg /\ persists m1 m /\ objects_fit (m_regions m1)).
Proof.
  intros gn glo ghi n0 Hgn Ho Hdom.
  destruct (plain_replays _ _ _ _ _ _ _ Hs Hpt Hgn eq_refl eq_refl Hdom)
    as (fr0 & m0 & e1 & l1 & m1 & Hst & He1 & Hops & Hp & Hfit).
  pose proof (Hops n0 (or_introl eq_refl) Ho) as En0.
  rewrite inst_step_let in Hst by reflexivity. cbn [op_arg_classes map2_option value_x] in Hst.
  rewrite En0 in Hst.
  destruct (lookup n0 (fr_env fr)) as [w|] eqn:Ew; [|discriminate Hst].
  destruct w as [u | pb | c0 sz]; simpl in Hst; try discriminate Hst.
  unfold op_res, op_res_int in Hst. cbn beta iota zeta in Hst.
  destruct (ptr_cap pb) as [| base | base | fn | x] eqn:Ec.
  (* A capability that is not an object's: the test holds 0. *)
  all: try (injection Hst as <- _ _; rewrite lookup_put, name_eqb_refl in He1;
            exists 0; split; [symmetry; exact He1 | intros []; reflexivity]).
  all: destruct (object_region base (m_regions m0)) as [reg|] eqn:E; [|discriminate Hst].
  all: injection Hst as <- _ <-; rewrite lookup_put, name_eqb_refl in He1.
  all: eexists; split; [symmetry; exact He1|]; intros Hv.
  all: destruct (_ && _) eqn:Eb; [|exfalso; exact (Hv eq_refl)].
  all: repeat rewrite andb_true_iff in Eb; destruct Eb as ((E1 & E2) & E3).
  all: apply Z.leb_le in E1, E3; apply Z.ltb_lt in E2.
  all: exists pb, base, reg, m0; auto 10.
Qed.

(** A [[lower chain]] follows [[flight]] instructions back to a source
    pointer whose [[capability]] matches the derived pointer's
    capability. Because each flight copies its capability from its lower
    donor, the chain guarantees that both pointers share the same
    capability. *)
Lemma lower_chain_sound : forall fuel p pp n0,
  value_x ge (fr_env fr) P p = Some (WPtr pp) ->
  (forall y, p = Tmp y -> once_has (single_definitions (fr_fn fr)) y = true -> dominating (fr_fn fr) l k y) ->
  once_has (single_definitions (fr_fn fr)) n0 = true ->
  lower_chain (single_definitions (fr_fn fr)) fuel p (Tmp n0) = true ->
  exists pn, value_x ge (fr_env fr) P (Tmp n0) = Some (WPtr pn) /\ ptr_cap pn = ptr_cap pp.
Proof.
  induction fuel as [|fuel IH]; intros p pp n0 Hp Hdom Ho H.
  - simpl in H. rewrite orb_false_r in H. apply value_eqb_eq in H. subst. eauto.
  - simpl in H. apply orb_true_iff in H as [H | H]; [apply value_eqb_eq in H; subst; eauto|].
    destruct p as [x | c | g]; try discriminate H.
    destruct (lookup x (single_definitions (fr_fn fr))) as [[| ph | i]|] eqn:Ex; try discriminate H.
    destruct i as [| d o args lw | | | | | | | ]; try discriminate H.
    destruct lw as [| b]; try discriminate H.
    pose proof (flight_def_name _ _ _ _ _ _ Ex) as ->.
    assert (Hox : once_has (single_definitions (fr_fn fr)) x = true) by (unfold once_has; rewrite Ex; reflexivity).
    pose proof (Hdom x eq_refl Hox) as Hdx.
    destruct (plain_replays _ _ _ _ _ _ _ Hs Hpt Ex eq_refl eq_refl Hdx) as (fr0 & m0 & e1 & l1 & m1 & Hst & Hx1 & Hops & _).
    (* The lower donor b reads now what it read then. *)
    assert (Hub : forall y, b = Tmp y -> In y (inst_uses (Flight x o args (LowerOf b))))
      by (intros y ->; simpl; apply value_temps_in, in_or_app; right; left; reflexivity).
    pose proof (lower_chain_once _ _ _ _ Ho H) as Hob.
    assert (Hbe : value_x ge (fr_env fr0) P b = value_x ge (fr_env fr) P b)
      by (apply value_x_agree; intros y E; exact (Hops _ (Hub y E) (Hob y E))).
    simpl in Hst. unfold flight_cap in Hst. rewrite Hbe in Hst.
    destruct (map_option _ args) as [xs|]; [|discriminate Hst]. simpl in Hst.
    destruct (alu o L xs) as [a|]; [|discriminate Hst]. simpl in Hst.
    destruct (value_x ge (fr_env fr) P b) as [[u | pb | c0 s0]|] eqn:Eb; simpl in Hst; try discriminate Hst.
    destruct a as [n | | ]; try discriminate Hst. injection Hst as <- _ _.
    rewrite lookup_put, name_eqb_refl in Hx1. simpl in Hp. rewrite <- Hx1 in Hp. simpl in Hp.
    injection Hp as <-. simpl.
    exact (IH b pb n0 Eb (fun y E Hoy => operand_dominating _ _ _ _ _ _ _ Hmd Hin Hr Ex Hdx (Hub y E) Hoy) Ho H).
Qed.

(** A [[renew_if]] instruction accepted by the pass never steps to
    [[unchecked]]. When the guard is zero, the instruction falls back to
    a full check; when the guard is nonzero, the earlier span test
    justifies the renewal. *)
Theorem renew_if_not_unchecked : forall b kk q lo hi r al p g rest live out why,
  find_block l (fn_blocks (fr_fn fr)) = Some b ->
  nth_error (b_insts b) kk = Some (Let q A (RenewIf lo hi r al) [p; g]) -> k = Z.of_nat kk ->
  checked_inst_rest (fn_src md (fr_fn fr)) (Let q A (RenewIf lo hi r al) [p; g]) rest live = Some out ->
  inst_step ge fr m (Let q A (RenewIf lo hi r al) [p; g]) <> Some (IStop (Unchecked why)).
Proof.
  intros b kk q lo hi r al p g rest live out why Hb Hk Hkk H.
  set (i := Let q A (RenewIf lo hi r al) [p; g]) in Hk.
  (* What the pass checked: a span test of N0 whose span covers P's. *)
  unfold checked_inst_rest in H. cbn beta iota zeta in H.
  destruct (guard_covers _ p g lo hi) eqn:Eg; [clear H | discriminate H].
  unfold guard_covers in Eg.
  destruct g as [gn | | ]; try discriminate Eg.
  destruct (lookup gn (s_once (fn_src md (fr_fn fr)))) as [[| | gi]|] eqn:Egn; try discriminate Eg.
  destruct gi as [gn' gk go gargs | | | | | | | | ]; try discriminate Eg.
  destruct gk; try discriminate Eg. destruct go; try discriminate Eg.
  destruct gargs as [| [n0 | | ] [|]]; try discriminate Eg.
  repeat rewrite andb_true_iff in Eg. destruct Eg as ((Egn' & Ho) & Ech).
  apply name_eqb_true in Egn'. subst gn'. rename lo0 into glo, hi0 into ghi.
  destruct (first_some _ (guard_chain _ p)) as [[olo ohi]|] eqn:Ef; [|discriminate Ech].
  apply andb_true_iff in Ech as [E1 E2]. apply Z.leb_le in E1, E2.
  (* A function with a setjmp has no single definitions. *)
  destruct (fn_src_cases md (fr_fn fr)) as [[_ Es] | [_ Es]];
    rewrite Es in Egn; cbn [s_once] in Egn; [discriminate Egn|].
  try (rewrite Es in Ho; cbn [s_once] in Ho). try (rewrite Es in Ef; cbn [s_once] in Ef).
  (* The step, with the operands it reads. *)
  intros Hst. rewrite inst_step_let in Hst by reflexivity.
  cbn [op_arg_classes map2_option] in Hst.
  destruct (value_x ge (fr_env fr) P p) as [[u | pp | c0 s0]|] eqn:Ep;
    destruct (value_x ge (fr_env fr) W (Tmp gn)) as [[gv | pg | cg sg]|] eqn:Ev;
    simpl in Hst; try discriminate Hst; unfold op_res, op_res_int in Hst; cbn beta iota zeta in Hst;
    try discriminate Hst.
  destruct (access_res m (raw_address (ptr_addr pp) lo) (ptr_cap pp) (hi - lo) r al) as [chk|] eqn:Echk;
    [|discriminate Hst]. cbn beta iota in Hst.
  destruct (gv =? 0) eqn:Eg0.
  { (* a guard of 0: a check *)
    injection Hst as Hst. unfold bind_res in Hst.
    destruct (checked_res chk (WPtr pp)) eqn:Ec; try discriminate Hst. injection Hst as <-.
    exact (checked_res_access _ _ _ _ _ _ _ _ _ Echk Ec). }
  (* The guard is not 0: its span test found N0's span inside its object. *)
  assert (Hdg : dominating (fr_fn fr) l k gn)
    by (apply (operand_at md fr l k Hmd Hin Hr Hpt b kk i gn Hb Hk Hkk);
        [unfold i; simpl; apply in_or_app; right; left; reflexivity | unfold once_has; rewrite Egn; reflexivity]).
  destruct (span_guard_holds gn glo ghi n0 Egn Ho Hdg) as (v & Ev' & Hspan).
  simpl in Ev. rewrite Ev' in Ev. simpl in Ev. injection Ev as <-.
  destruct (Hspan ltac:(intros ->; discriminate Eg0)) as (pb & base & reg & m1 & En0 & Hc & E & Hb1 & HLH & Hend & Hp & Hfit).
  (* P is a known offset from N0, by its guard chain. *)
  destruct (first_some_in _ _ _ _ _ Ef) as ([v0 [olo' ohi']] & Hel & Hf).
  simpl in Hf. destruct (value_eqb v0 (Tmp n0)) eqn:Ev0; [|discriminate Hf].
  apply value_eqb_eq in Ev0. subst v0. injection Hf as -> ->.
  assert (Hdp : forall y, p = Tmp y -> once_has (single_definitions (fr_fn fr)) y = true -> dominating (fr_fn fr) l k y)
    by (intros y -> Hoy; exact (operand_at md fr l k Hmd Hin Hr Hpt b kk i y Hb Hk Hkk ltac:(unfold i; simpl; auto) Hoy)).
  assert (Hst0 : stable (single_definitions (fr_fn fr)) (Tmp n0)) by (intros y E'; injection E' as <-; exact Ho).
  destruct (guard_chain_sound ge md fr m l k Hmd Hin Hr Hs Hpt p pp (Tmp n0) olo ohi Ep Hdp Hel Hst0)
    as (pb' & x & Hpb & Hcap & Hx & Haddr).
  simpl in Hpb. rewrite En0 in Hpb. injection Hpb as <-.
  (* Sizes the validator guarantees. *)
  destruct (find_block_in _ _ _ Hb) as [Hbin _].
  destruct (check_fact_ok _ _ _ _ _ Hmd Hin Hbin (nth_error_In _ _ Hk) eq_refl) as [Hsz _]. simpl in Hsz.
  destruct (once_position _ _ _ Egn) as (sg & Hpos & _).
  destruct (dinst_site _ _ _ _ Hpos) as (d & j & ->).
  destruct (position_inst _ _ _ _ _ Hpos) as (bg & kg & Hbg & _ & Hkg & _ & _).
  destruct (span_test_ok _ _ _ _ _ _ _ Hmd Hin Hbg (nth_error_In _ _ Hkg)) as (Hgw & Hglo & Hghi).
  destruct (guard_inside base (r_end reg) (ptr_addr pb) x glo ghi (ptr_addr pp) lo hi
              Hb1 HLH Hend (proj2 (Hfit _ _ E)) Hgw ltac:(lia) Haddr ltac:(lia) ltac:(lia) Hsz) as [Hi1 Hi2].
  (* The renew of an access inside the object. *)
  rewrite Hcap in Hc.
  destruct (renew_inside m1 m (ptr_cap pp) base reg (raw_address (ptr_addr pp) lo) (hi - lo) r al pp
              Hc E Hi1 Hi2 ltac:(lia) Hp eq_refl) as (chk' & Echk' & Hres).
  rewrite Echk in Echk'. injection Echk' as <-.
  destruct Hres as [-> | (rr & Hrr & Hnot)]; [discriminate Hst|].
  destruct chk as [[] | [] | w]; try (rewrite Hrr in Hst; cbn beta iota in Hst;
                                      injection Hst as Hst; unfold bind_res in Hst;
                                      destruct rr; try discriminate Hst; injection Hst as <-;
                                      exact (Hnot _ eq_refl)); discriminate Hst.
Qed.

(** A `check_limit` instruction accepted by the pass never steps to
    [[unchecked]]. The [[limit]] operand records the source pointer's
    capability and span size, and [lower_chain_sound] ensures that the
    checked pointer carries that same capability. *)
Theorem check_limit_not_unchecked : forall b kk q lo hi r al p u rest live out why,
  find_block l (fn_blocks (fr_fn fr)) = Some b ->
  nth_error (b_insts b) kk = Some (Let q A (CheckLimit lo hi r al) [p; u]) -> k = Z.of_nat kk ->
  checked_inst_rest (fn_src md (fr_fn fr)) (Let q A (CheckLimit lo hi r al) [p; u]) rest live = Some out ->
  inst_step ge fr m (Let q A (CheckLimit lo hi r al) [p; u]) <> Some (IStop (Unchecked why)).
Proof.
  intros b kk q lo hi r al p u rest live out why Hb Hk Hkk H.
  set (i := Let q A (CheckLimit lo hi r al) [p; u]) in Hk.
  (* What the pass checked: a limit of N0 of the check's span, and P's
     lower chain reaches N0. *)
  unfold checked_inst_rest in H. cbn beta iota zeta in H.
  destruct (limit_covers _ p u lo hi) eqn:Eu; [clear H | discriminate H].
  unfold limit_covers in Eu.
  destruct u as [un | | ]; try discriminate Eu.
  destruct (lookup un (s_once (fn_src md (fr_fn fr)))) as [[| | ui]|] eqn:Eun; try discriminate Eu.
  destruct ui as [un' uk uo uargs | | | | | | | | ]; try discriminate Eu.
  destruct uk; try discriminate Eu. destruct uo; try discriminate Eu.
  destruct uargs as [| [n0 | | ] [|]]; try discriminate Eu.
  repeat rewrite andb_true_iff in Eu. destruct Eu as ((((Eun' & Elo) & Ehi) & Ho) & Hlc).
  apply name_eqb_true in Eun'. subst un'. apply Z.eqb_eq in Elo, Ehi. subst lo hi.
  (* A function with a setjmp has no single definitions. *)
  destruct (fn_src_cases md (fr_fn fr)) as [[_ Es] | [_ Es]];
    rewrite Es in Eun; cbn [s_once] in Eun; [discriminate Eun|].
  try (rewrite Es in Ho; cbn [s_once] in Ho). try (rewrite Es in Hlc; cbn [s_once] in Hlc).
  (* The limit holds N0's capability and the size it read. *)
  assert (Hdu : dominating (fr_fn fr) l k un)
    by (apply (operand_at md fr l k Hmd Hin Hr Hpt b kk i un Hb Hk Hkk);
        [unfold i; simpl; apply in_or_app; right; left; reflexivity | unfold once_has; rewrite Eun; reflexivity]).
  destruct (plain_replays _ _ _ _ _ _ _ Hs Hpt Eun eq_refl eq_refl Hdu)
    as (fr0 & m0 & e1 & l1 & m1 & Hst0 & He1 & Hops & _).
  pose proof (Hops n0 (or_introl eq_refl) Ho) as En0.
  rewrite inst_step_let in Hst0 by reflexivity. cbn [op_arg_classes map2_option value_x] in Hst0.
  rewrite En0 in Hst0.
  destruct (lookup n0 (fr_env fr)) as [[w | pn | cn sn]|] eqn:Ew; simpl in Hst0; try discriminate Hst0.
  injection Hst0 as <- _ _. rewrite lookup_put, name_eqb_refl in He1.
  (* The step. *)
  intros Hst. rewrite inst_step_let in Hst by reflexivity. cbn [op_arg_classes map2_option] in Hst.
  replace (value_x ge (fr_env fr) L (Tmp un)) with (Some (WLimit (ptr_cap pn) size)) in Hst
    by (simpl; rewrite <- He1; reflexivity).
  destruct (value_x ge (fr_env fr) P p) as [[x | pp | c0 s0]|] eqn:Ep;
    simpl in Hst; try discriminate Hst; unfold op_res, op_res_int in Hst; cbn beta iota zeta in Hst;
    try discriminate Hst.
  (* P has N0's capability. *)
  assert (Hdp : forall y, p = Tmp y -> once_has (single_definitions (fr_fn fr)) y = true -> dominating (fr_fn fr) l k y)
    by (intros y -> Hoy; exact (operand_at md fr l k Hmd Hin Hr Hpt b kk i y Hb Hk Hkk ltac:(unfold i; simpl; auto) Hoy)).
  destruct (lower_chain_sound 64 p pp n0 Ep Hdp Ho Hlc) as (pn' & Epn & Hcap).
  simpl in Epn. rewrite Ew in Epn. injection Epn as <-.
  rewrite Hcap, cap_eqb_refl, Z.sub_0_r, Z.eqb_refl in Hst. cbn beta iota in Hst.
  destruct (access_res m (raw_address (ptr_addr pp) 0) (ptr_cap pp) size r al) as [chk|] eqn:Echk;
    cbn beta iota in Hst; [|discriminate Hst].
  injection Hst as Hst. unfold bind_res in Hst.
  destruct (checked_res chk (WPtr pp)) eqn:Ec; try discriminate Hst. injection Hst as <-.
  exact (checked_res_access _ _ _ _ _ _ _ _ _ Echk Ec).
Qed.

End Guard.

(** ## Soundness along every run

    A single-step frame proof only covers one instruction in isolation.
    To show that an entire execution stays safe, we lift the frame
    lemmas across arbitrary runs of any [[runtime]] so every reachable,
    non-[[doomed]] frame avoids [[unchecked]] outcomes. *)

(** Predicate [guard_form] matches any `let` binding whose operation is
    `RenewIf` or `CheckLimit`. Neither form is a raw memory access. *)
Definition guard_form (i : inst) : Prop :=
  (exists q kc lo hi r al args, i = Let q kc (RenewIf lo hi r al) args) \/
  (exists q kc lo hi r al args, i = Let q kc (CheckLimit lo hi r al) args).

(** A malformed `renew_if` or `check_limit` instruction cannot even start
    executing, because the machine rejects wrong operand counts or
    classes before checking bounds. Any instruction that reaches
    [Unchecked] therefore has two operands and proof [[class]] A. *)
Lemma guard_shape : forall ge fr m i why,
  guard_form i -> inst_step ge fr m i = Some (IStop (Unchecked why)) ->
  exists q o a1 a2, i = Let q A o [a1; a2] /\
    ((exists lo hi r al, o = RenewIf lo hi r al) \/ (exists lo hi r al, o = CheckLimit lo hi r al)).
Proof.
  intros ge fr m i why [(q & kc & lo & hi & r & al & args & ->) | (q & kc & lo & hi & r & al & args & ->)] H;
    rewrite inst_step_let in H by reflexivity; cbn beta iota zeta delta [op_arg_classes] in H;
    destruct (map2_option _ _ args) as [xs|] eqn:Ex; try discriminate H;
    destruct (map2_option_two _ _ _ _ _ _ _ _ Ex) as (a1 & a2 & ->);
    destruct kc; unfold op_res, op_res_int in H; cbn beta iota zeta delta [fmt_of] in H; try discriminate H;
    eauto 12.
Qed.

(** Different execution backends share the same check-elimination rules
    even though they implement allocation and garbage collection
    differently. Module [Guards] abstracts our soundness theorem over
    any [[runtime]] implementation. *)
Module Guards (R : Runtime).

Module G := Reuse R.

(** Every reachable, non-[[doomed]] frame in a function from a valid
    module avoids [Unchecked] on `renew_if` and `check_limit`
    instructions, provided the run starts in a [[ready]] memory. *)
Theorem run_guard_checked : forall ge md f xs fr m fuel s0 c s l i rest j why,
  checked_module md -> ge_module ge = md -> ge_free ge = R.free ->
  In (IFunc f) md -> call_frame f xs = Some fr -> R.ready s0 m ->
  G.H.P.I.RM.mreachable ge (mkConfig fr [] m fuel, s0) (c, s) ->
  fr_doomed (c_frame c) = None -> fr_at (c_frame c) = Exec l (i :: rest) j -> guard_form i ->
  inst_step ge (c_frame c) (c_mem c) i <> Some (IStop (Unchecked why)).
Proof.
  intros ge md f xs fr m fuel s0 c s l i rest j why Hmd Hge Hfree Hin Hcf H0 Hreach Hd Ha Hi Hst.
  destruct (guard_shape _ _ _ _ _ Hi Hst) as (q & o & a1 & a2 & -> & Ho).
  destruct (G.run_point _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hmd Hge Hfree Hin Hcf H0 Hreach Hd Ha
              ltac:(destruct Ho as [(? & ? & ? & ? & ->) | (? & ? & ? & ? & ->)]; reflexivity)
              ltac:(intros ? ? ? E; discriminate E) ltac:(intros ? E; discriminate E))
    as (b & kk & live & out & Hinf & Hr & Hsc & Hpt & Hb & Hnth & Hc & _ & _).
  destruct Ho as [(lo & hi & r & al & ->) | (lo & hi & r & al & ->)].
  - exact (renew_if_not_unchecked ge md (c_frame c) (c_mem c) l (Z.of_nat kk) Hmd Hinf Hr (scope_plain_of _ _ _ Hsc) Hpt
             b kk q lo hi r al a1 a2 rest live out why Hb Hnth eq_refl Hc Hst).
  - exact (check_limit_not_unchecked ge md (c_frame c) (c_mem c) l (Z.of_nat kk) Hmd Hinf Hr (scope_plain_of _ _ _ Hsc) Hpt
             b kk q lo hi r al a1 a2 rest live out why Hb Hnth eq_refl Hc Hst).
Qed.

End Guards.

(** ## The interpreter's runtime

    The reference [[interpreter]] provides a concrete runtime that
    satisfies our machine axioms. Instantiating [Guards] with
    [InterpRuntime] yields a self-contained soundness theorem for
    interpreted runs. *)

Module InterpGuards := Guards InterpRuntime.

(** Corollary [interp_guard_checked] specializes [run_guard_checked] to
    the reference [[interpreter]], leaving only the ready-start
    assumption. *)
Corollary interp_guard_checked : forall md globals f xs fr m fuel s0 c s l i rest j why,
  let ge := mkGenv md globals InterpRuntime.free in
  checked_module md -> In (IFunc f) md -> call_frame f xs = Some fr -> InterpRuntime.ready s0 m ->
  InterpGuards.G.H.P.I.RM.mreachable ge (mkConfig fr [] m fuel, s0) (c, s) ->
  fr_doomed (c_frame c) = None -> fr_at (c_frame c) = Exec l (i :: rest) j -> guard_form i ->
  inst_step ge (c_frame c) (c_mem c) i <> Some (IStop (Unchecked why)).
Proof.
  intros md globals f xs fr m fuel s0 c s l i rest j why ge Hmd Hin Hcf H0 Hreach Hd Ha Hi.
  exact (InterpGuards.run_guard_checked ge md f xs fr m fuel s0 c s l i rest j why
           Hmd eq_refl eq_refl Hin Hcf H0 Hreach Hd Ha Hi).
Qed.
