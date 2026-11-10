(** Campaign 3's [[reuse|reuse forms]], part three: [[renew_if]] and
    `check_limit`
    ([formal.md, Campaign 3](../../docs/formal.md#campaign-3-the-soundness-theorem);
    [rocq.md, Guards and limits](../../docs/rocq.md#guards-and-limits)).

    Both take their evidence from a [[single definition]] that tested
    the pointer earlier, not from a [[check]]. A `renew_if` of a pointer
    P with guard G trusts G, a [[span test]] of a pointer N0
    (`guard_covers/5`): where G is nonzero, the span from N0+GLo up to
    N0+GHi lay inside its object, and P's span lies inside that one at
    the offset P's [[guard chain]] gives (`guard_chain/3`). The
    interpreter renews then, and a failed access test that is not on a
    freed object is `unchecked(span)` (`renew_res/4`). A `check_limit`
    of P with U trusts U, a [[limit]] of N0 whose size is the check's
    span (`limit_covers/5`), and P has N0's lower (a [[lower chain]],
    `lower_chain/3`). The interpreter checks then, and a limit of
    another capability or another size is `unchecked(limit)`. This file
    proves neither [[unchecked]] outcome happens where the pass accepted
    the instruction.

    ## Decisions

    | Decision | Why |
    |---|---|
    | the span test's memory is the one it read, which persists | a span test changes nothing; the object it found is as it was or freed (Identity.v) |
    | a guard of 0 needs no argument | `kind_res/8` then checks, and a check is never `unchecked` |
    | the span's width is bounded by `valid_op/1`'s span test, not by the object | the span test's two addresses are each reduced modulo 2^64; their difference is the span only because the span is less than 2^64 | *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Maps Syntax Cfg Values Memory Runtime Ops Semantics Machine Validate
  Dominance Interval Sites Identity Coverage Walk Invariant Persistence Single Evidence Chain Renew.
Import ListNotations.
Open Scope Z_scope.

(** ## Span tests *)

(** A [[span test]] gn of the pointer n0, in a block b of a function f
    of a [checked_module] md, tests a nonempty span from offset glo up
    to ghi, both signed 64-bit offsets. The [[validator]] requires this
    of every span test (`valid_op/1`); the lemma reads it back through
    [inst_valid]. *)
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

(** The arithmetic of a guard. Where a span test of a pointer at
    address B found its span, from L = B+GLo up to H = B+GHi modulo
    2^64, inside an object from base up to end_, which ends in the
    address space (at or below 2^48), an access from A+Lo up to A+Hi,
    with A = B+X modulo 2^64 and both X+Lo and X+Hi between GLo and GHi,
    lies inside the object too. H - L is the span's width exactly,
    since the width is below 2^64. *)
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

(** A renew through a pointer p with an object's capability c, of an
    access from a up to a + size inside that object as a memory m1 had
    it, in a memory m that [persists] from m1, traps misaligned, or
    renews (`renew_res/4`): it passes, traps read-only, or finds the
    object freed (`kind_res/8`). It is never [[unchecked]]. *)
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

(** The result a `check` makes of an access test chk ([checked_res])
    is never [[unchecked]], since the access test itself never is. *)
Lemma checked_res_access : forall m a c size r al chk w why,
  access_res m a c size r al = Some chk -> checked_res chk w <> RUnchecked why.
Proof.
  intros m a c size r al chk w why H E. destruct chk; try discriminate E.
  injection E as ->. exact (cap_access_res_checked _ _ _ _ _ _ _ H).
Qed.

(** If the [[lower chain]] of a value d reaches a single-definition
    name n0 (`lower_chain/3`), d is a single-definition name too, or not
    a name at all. *)
Lemma lower_chain_once : forall once fuel d n0,
  once_has once n0 = true -> lower_chain once fuel d (Tmp n0) = true ->
  forall y, d = Tmp y -> once_has once y = true.
Proof.
  intros once fuel d n0 Ho H y ->. destruct fuel as [|fuel]; simpl in H.
  - rewrite orb_false_r in H. apply name_eqb_true in H. subst. exact Ho.
  - apply orb_true_iff in H as [H | H]; [apply name_eqb_true in H; subst; exact Ho|].
    unfold once_has. destruct (lookup y once); [reflexivity | discriminate H].
Qed.

(** The frame lemmas: a frame fr runs a function of a
    [checked_module] md, in memory m, at index k of a reachable block l,
    and every [[single definition]] in scope but a `check_ahead`
    [[replay|replays]] ([scope_plain]). *)
Section Guard.

Variables (ge : genv) (md : module) (fr : frame) (m : Memory.mem) (l : name) (k : Z).
Hypothesis Hmd : checked_module md.
Hypothesis Hin : In (IFunc (fr_fn fr)) md.
Hypothesis Hr : is_reachable (fn_doms (fr_fn fr)) l = true.
Hypothesis Hs : scope_plain ge fr m.
Hypothesis Hpt : point_site (fr_fn fr) (fr_at fr) = Some (l, k).

(** A [[span test]] gn of the pointer n0, both single definitions, whose
    site [[dominance|dominates]] the frame's point, holds an integer v.
    Where v is not 0, n0 holds a pointer pb of an object whose span from
    offset glo up to ghi the test found inside the object, in a memory
    m1 that lay in the address space and that the current memory
    [persists] from. *)
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

(** A pointer value p whose [[lower chain]] reaches the single-definition
    name n0 (`lower_chain/3`), where p's single definition dominates the
    point, has the [[capability]] of the pointer n0 holds. Each step of
    the chain is a [[flight]], whose capability is its lower donor's
    (`flight_cap/4`). *)
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

(** A [[renew_if]] of a pointer p with guard g, the instruction at
    index k of block b, that the pass accepts ([checked_inst_rest],
    which asks `guard_covers/5`) does not step to [[unchecked]]. Either
    its guard is 0 and it checks, which is never unchecked; or its span
    test passed ([span_guard_holds]), the renewed span lies inside the
    tested one ([guard_inside]), and so it renews ([renew_inside]). *)
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
  simpl in Egn.
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

(** A `check_limit` of a pointer p with limit u, the instruction at
    index k of block b, that the pass accepts ([checked_inst_rest],
    which asks `limit_covers/5`) does not step to [[unchecked]]. Its
    [[limit]] u holds the capability of a pointer N0 and the check's
    span as its size, and p has N0's capability ([lower_chain_sound]),
    so the limit matches and the instruction checks. *)
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
  simpl in Eun.
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

(** ## Along every run *)

(** The instructions this file covers: a `let` of a `renew_if` or a
    `check_limit`, of any class and operands. Neither is a raw access. *)
Definition guard_form (i : inst) : Prop :=
  (exists q kc lo hi r al args, i = Let q kc (RenewIf lo hi r al) args) \/
  (exists q kc lo hi r al args, i = Let q kc (CheckLimit lo hi r al) args).

(** A `renew_if` or `check_limit` that steps to [[unchecked]] is of
    the proof [[class]] A with two operands (`op_arg_classes/4`,
    `kind_res/8`); of any other shape it does not step at all. So the
    run theorem covers every such instruction with the frame lemmas,
    which take only that shape. *)
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

(** The frame lemmas carried along every [[run]] of the [[machine]] of a
    [[runtime]] R, as Renew.v's [Reuse] carries its own. *)
Module Guards (R : Runtime).

Module G := Reuse R.

(** In every state a [[run]] reaches from a call of a function f of a
    [checked_module] md, started in a memory where the runtime is
    [[ready]], a frame that is not [[doomed]] runs no `renew_if` and no
    `check_limit` to an [[unchecked]] outcome. Every runtime spares the
    pass's facts at [[poll|safepoints]] ([spares_any]; see
    [The evidence invariant over runs](../../docs/rocq.md#the-evidence-invariant-over-runs)). *)
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

(** ## The interpreter's runtime *)

Module InterpGuards := Guards InterpRuntime.

(** [run_guard_checked] for the [[interpreter]]'s runtime: in every state of a run of
    a checked module's function that starts ready, a frame that is not
    doomed runs no `renew_if` and no `check_limit` to `unchecked`. No
    hypothesis remains but the ready start. *)
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
