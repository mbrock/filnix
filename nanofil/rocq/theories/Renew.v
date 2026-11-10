(** Campaign 3's [[reuse|reuse forms]], part two: [[renew]],
    [[renew_hull|renew over a hull]] and [[half check]]
    ([formal.md, Campaign 3](../../docs/formal.md#campaign-3-the-soundness-theorem);
    [rocq.md, Renew and the half check](../../docs/rocq.md#renew-and-the-half-check)).

    All three reuse a [[check]] that passed earlier. A renew of a
    pointer P trusts Q1, the [[proof]] of a [[single definition|single-definition]]
    check of a pointer P1 (a [[renew source]], `renew_source_op/6`),
    whose span covers P's at the distance `pointer_distance/4` finds. A
    half check of P trusts the same kind of source for the bound it does
    not test (`half_known/6`). A renew over a hull trusts two sources,
    QL and QH, whose spans bound P's from below and above
    (`hull_renewable/8`). The interpreter makes the run [[unchecked]]
    where that trust was false: Q1 of another capability
    (`unchecked(alias)`), a renew whose access test fails but not
    because the object was freed (`unchecked(span)`), or a half check
    whose one-sided native test disagrees with the whole check
    (`unchecked(half)`). This file proves none of them happens where the
    pass accepted the instruction.

    The argument is the same for all three. Q1 is an operand of the
    instruction, so its single definition [[dominance|dominates]] it and
    [[replay|replays]] (Single.v): Q1 holds the pointer P1 held when its
    check passed, and memory [[identity|persists]] from then, so the
    object is as it was or freed. P is a known distance from P1, so it
    has P1's [[capability]] (Chain.v). What is left is arithmetic over
    `cap_access_res/7`.

    ## Decisions

    | Decision | Why |
    |---|---|
    | the source's rights are not used | a renew asks its own rights; on a read-only object a write traps `readonly`, which `renew_res/4` keeps as the program's trap |
    | the persisting object is split by cases, not read through [persists_access] | a renew's trap must be on a freed object, which [persists_access]'s conclusion forgets |
    | the source's memory fit the address space (Single.v's [replays]) | once the object is freed, the current memory no longer says where it ended, and a lower half check's address may wrap |
    | objects start at or above 0 and freed objects are empty ([objects_fit], [freed_bounds]) | a lower half check reads its address signed and fails on any freed object; the whole check agrees only then |
    | a renew over a hull compares its two sources only through the current memory | each source's check passed in its own memory, and both persist into the current one, so the object is as both saw it or freed since |
    | an instruction of another class or arity is not the pass's concern | it does not step ([reuse_shape]) | *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Maps Syntax Cfg Values Memory Runtime Ops Semantics Machine Validate
  Dominance Interval Sites Identity Coverage Walk Invariant Persistence Single Evidence Chain.
Import ListNotations.
Open Scope Z_scope.

(** ## Renew sources *)

(** A [[renew source]] n1 that the pass records for a function f of a
    module md, of a pointer p1 over the span from lo1 up to hi1 at
    alignment al1, is the check-like instruction i that is n1's single
    definition, and p1 is a single-definition name too
    (`stage_sources/4`). [check_fact] reads the span i checks. *)
Lemma renew_source_def : forall md f n1 p1 lo1 hi1 al1,
  lookup n1 (s_renews (fn_src md f)) = Some (p1, lo1, hi1, al1) ->
  exists i r1, lookup n1 (single_definitions f) = Some (DInst i) /\
    check_fact i = Some (mkFact n1 (Tmp p1) lo1 hi1 r1 al1) /\
    once_has (single_definitions f) p1 = true.
Proof.
  intros md f n1 p1 lo1 hi1 al1 H. unfold fn_src, stage_sources in H. simpl in H.
  destruct (lookup_some_in _ _ _ _ H) as (n1' & En & Hin). apply name_eqb_true in En. subst n1'.
  apply in_flat_map in Hin as (b & Hb & Hin). apply in_flat_map in Hin as (i & Hi & Hin).
  destruct (renew_source (single_definitions f) i) as [[q1 v]|] eqn:Er; [|destruct Hin].
  destruct Hin as [E | []]. injection E as -> ->.
  unfold renew_source in Er.
  destruct i as [q k o args | | | | | | | | ]; try discriminate Er.
  destruct k; try (destruct o; discriminate Er).
  (* Each of the five source ops (check, check_ahead, renew_if,
     check_limit, half_check) has the fact its source records, so it is
     enough that the source instruction is n1's single definition. *)
  assert (G : forall p lo hi r al,
             check_fact (Let q A o args) = Some (mkFact q (Tmp p) lo hi r al) ->
             once_has (single_definitions f) q && once_has (single_definitions f) p = true ->
             q = n1 -> p = p1 -> lo = lo1 -> hi = hi1 -> al = al1 ->
             exists i r1, lookup n1 (single_definitions f) = Some (DInst i) /\
               check_fact i = Some (mkFact n1 (Tmp p1) lo1 hi1 r1 al1) /\
               once_has (single_definitions f) p1 = true).
  { intros p lo hi r al Hf Ho -> -> -> -> ->. apply andb_true_iff in Ho as [Hq Hp].
    unfold once_has in Hq. destruct (lookup n1 (single_definitions f)) as [D|] eqn:Ed; [|discriminate Hq].
    destruct (once_position _ _ _ Ed) as (s & _ & Hu).
    destruct (In_nth_error _ _ Hi) as [kk Hk].
    pose proof (inst_position f b kk (Let n1 A o args) (n1, A) Hb Hk (or_introl eq_refl)) as Hpos.
    destruct (Hu _ _ Hpos) as [_ <-]. exists (Let n1 A o args), r. auto. }
  destruct o; cbn -[once_has] in Er; try discriminate Er; cases Er. all: injection Er as -> -> -> -> ->.
  all: match goal with Ho : (match _ with _ => _ end) = Some _ |- _ =>
         cases Ho; injection Ho as -> -> -> -> end.
  all: eapply G; eauto; reflexivity.
Qed.

(** Every instruction i of a block b of a function f of a
    [checked_module] md passes the [[validator]]'s per-instruction test
    `valid_inst/3` at some list of classes cls. *)
Lemma inst_valid : forall md f b i,
  checked_module md -> In (IFunc f) md -> In b (fn_blocks f) -> In i (b_insts b) ->
  exists cls, valid_inst md cls i = true.
Proof.
  unfold checked_module, valid. intros md f b i [Hv _] Hin Hb Hi.
  destruct (existsb _ md); [discriminate Hv|]. injection Hv as Hv.
  unfold valid_items in Hv. apply andb_true_iff in Hv as [_ Hv]. rewrite forallb_forall in Hv.
  specialize (Hv _ Hin). simpl in Hv. unfold valid_func in Hv.
  destruct (fn_blocks f) as [|b0 bs] eqn:Eb; [destruct Hb|].
  destruct (block_intervals (b0 :: bs)); [|discriminate Hv].
  repeat match goal with H : (_ && _) = true |- _ => apply andb_true_iff in H as [? ?] end.
  match goal with H : forallb (valid_block md f _) _ = true |- _ =>
    rewrite forallb_forall in H; specialize (H b Hb); unfold valid_block in H end.
  repeat match goal with H : (_ && _) = true |- _ => apply andb_true_iff in H as [? ?] end.
  match goal with H : forallb (valid_inst md _) (b_insts b) = true |- _ =>
    rewrite forallb_forall in H; exact (ex_intro _ _ (H i Hi)) end.
Qed.

(** A check-like instruction i of a [checked_module] md, whose fact fa
    [check_fact] reads, checks a nonempty span at one of the alignments
    `valid_op/1` allows ([check_align]). *)
Lemma check_fact_ok : forall md f b i fa,
  checked_module md -> In (IFunc f) md -> In b (fn_blocks f) -> In i (b_insts b) -> check_fact i = Some fa ->
  f_lo fa < f_hi fa /\ check_align (f_al fa) = true.
Proof.
  intros md f b i fa Hmd Hin Hb Hi Hf. destruct (inst_valid _ _ _ _ Hmd Hin Hb Hi) as [cls Hvi].
  destruct i as [q k o args | | | | | | | | ]; try discriminate Hf.
  destruct k; try (destruct o; discriminate Hf).
  destruct o; try discriminate Hf; cbn -[valid_op] in Hf; cases Hf; injection Hf as <-;
    unfold valid_inst in Hvi; simpl in Hvi; unfold check_ok in Hvi;
    repeat match goal with H : (_ && _) = true |- _ => apply andb_true_iff in H as [? ?] end;
    repeat match goal with H : (_ <? _) = true |- _ => apply Z.ltb_lt in H end;
    simpl; (split; [lia | assumption]).
Qed.

(** ## Renew, over memory *)

(** The arithmetic of a [[renew]]. Where the span of capability c from
    A+lo1 up to A+hi1 passed its check in a memory m1, a renew through a
    pointer p of c of the part from A+off up to A+off+size, at an
    alignment al that divides the source's al1, in a memory m that
    [persists] from m1 and lies in the address space, passes, traps
    read-only, or traps out of bounds on a freed object
    (`renew_res/4`); never [[unchecked]]. *)
Lemma renew_access : forall m1 m c A lo1 hi1 r1 al1 u off size r al p,
  access_res m1 (raw_address A lo1) c (hi1 - lo1) r1 al1 = Some (RVal u) ->
  persists m1 m -> objects_fit (m_regions m) -> ptr_cap p = c ->
  lo1 <= off -> off + size <= hi1 -> 0 < size -> 0 < al -> al1 mod al = 0 -> (off - lo1) mod al = 0 ->
  exists chk rr, access_res m (raw_address A off) c size r al = Some chk /\ renew_res chk p m = Some rr /\
    forall why, rr <> RUnchecked why.
Proof.
  intros m1 m c A lo1 hi1 r1 al1 [] off size r al p H Hp Hfit Hc Hlo Hhi Hs Hal Hal1 Hoff.
  unfold access_res, cap_access_res in *.
  destruct c as [| base | base | f | n]; try discriminate H;
    destruct (object_region base (m_regions m1)) as [reg|] eqn:E; try discriminate H;
    destruct ((base <=? raw_address A lo1) && (raw_address A lo1 + (hi1 - lo1) <=? r_end reg)) eqn:Eb;
    try discriminate H;
    apply andb_true_iff in Eb as [E1 E2]; apply Z.leb_le in E1; apply Z.leb_le in E2;
    pose proof (object_region_base _ _ _ E) as Hbase.
  all: assert (Haligned : forall x, x mod al1 = 0 -> (x + (off - lo1)) mod al = 0)
         by (intros x Hx; apply aligned_add; [exact Hal | exact (aligned_divisor _ _ _ Hal Hx Hal1) | exact Hoff]).
  all: destruct (Hp _ _ E) as [E' | E'].
  - (* the object as it was *)
    pose proof (Hfit _ _ E') as Hend.
    rewrite E', (raw_address_within A lo1 off Hlo ltac:(lia)).
    replace ((base <=? raw_address A lo1 + (off - lo1)) && (raw_address A lo1 + (off - lo1) + size <=? r_end reg))
      with true by (symmetry; apply andb_true_iff; split; apply Z.leb_le; lia).
    injection H as H. rewrite (aligned_res_ok _ _ (Haligned _ (aligned_res_mod _ _ H))).
    exists ok, (RVal (WPtr p)). split; [reflexivity|]. split; [reflexivity | discriminate].
  - (* freed: the access traps out of bounds, on a freed object *)
    rewrite E'. simpl. rewrite Hbase.
    replace ((base <=? raw_address A off) && (raw_address A off + size <=? base)) with false
      by (symmetry; apply andb_false_iff; destruct (Z.le_gt_cases base (raw_address A off));
          [right; apply Z.leb_gt; lia | left; apply Z.leb_gt; lia]).
    exists (RTrap OutOfBounds), (RTrap OutOfBounds). split; [reflexivity|].
    unfold renew_res. rewrite Hc, E'. split; [reflexivity | discriminate].
  - (* read-only, as it was: a read passes, a write traps read-only *)
    pose proof (Hfit _ _ E') as Hend.
    rewrite E', (raw_address_within A lo1 off Hlo ltac:(lia)).
    replace ((base <=? raw_address A lo1 + (off - lo1)) && (raw_address A lo1 + (off - lo1) + size <=? r_end reg))
      with true by (symmetry; apply andb_true_iff; split; apply Z.leb_le; lia).
    destruct r1; simpl in H; [|discriminate H]. injection H as H.
    pose proof (Haligned _ (aligned_res_mod _ _ H)) as Ha.
    destruct r; simpl; rewrite ?(aligned_res_ok _ _ Ha).
    + exists ok, (RVal (WPtr p)). split; [reflexivity|]. split; [reflexivity | discriminate].
    + exists (RTrap Readonly), (RTrap Readonly). split; [reflexivity|]. split; [reflexivity | discriminate].
  - (* read-only, freed: as an object freed *)
    rewrite E'. simpl. rewrite Hbase.
    replace ((base <=? raw_address A off) && (raw_address A off + size <=? base)) with false
      by (symmetry; apply andb_false_iff; destruct (Z.le_gt_cases base (raw_address A off));
          [right; apply Z.leb_gt; lia | left; apply Z.leb_gt; lia]).
    exists (RTrap OutOfBounds), (RTrap OutOfBounds). split; [reflexivity|].
    unfold renew_res. rewrite Hc, E'. split; [reflexivity | discriminate].
Qed.

(** ## Renew over a hull, over memory *)

(** The address of a [[renew_hull|renew over a hull]]. The renewed
    pointer's address A is Al+dl and Ah+dh modulo 2^64, where Al and Ah
    are the addresses of the low and high sources. The renew starts E
    past the low source's span and ends F before the high source's,
    both near (between 0 and 2^62). Then A+lo is both sums exactly, not
    merely modulo 2^64: both spans lie in the address space (at or
    below 2^48), so neither sum wraps. *)
Lemma hull_address : forall Al Ah A lol loh hih dl dh lo hi,
  A mod 2 ^ 64 = (Al + dl) mod 2 ^ 64 -> A mod 2 ^ 64 = (Ah + dh) mod 2 ^ 64 ->
  raw_address Al lol <= 2 ^ 48 -> raw_address Ah loh + (hih - loh) <= 2 ^ 48 -> loh < hih ->
  0 <= lo + dl - lol <= 2 ^ 62 -> 0 <= hih - hi - dh <= 2 ^ 62 -> 0 < hi - lo <= 2 ^ 62 ->
  raw_address A lo = raw_address Al lol + (lo + dl - lol) /\
  raw_address A lo = raw_address Ah loh + (lo + dh - loh).
Proof.
  intros Al Ah A lol loh hih dl dh lo hi HAl HAh Hl Hh Hs He Hf Hsz.
  assert (Hmod : forall B d o o', A mod 2 ^ 64 = (B + d) mod 2 ^ 64 ->
            raw_address A o = (raw_address B o' + (o + d - o')) mod 2 ^ 64).
  { intros B d o o' HB. unfold raw_address.
    rewrite <- (Z.add_mod_idemp_l A o (2 ^ 64)), HB, !Z.add_mod_idemp_l by lia. f_equal. ring. }
  pose proof (Hmod Al dl lo lol HAl) as Xl. pose proof (Hmod Ah dh lo loh HAh) as Xh.
  pose proof (Z.mod_pos_bound (Al + lol) (2 ^ 64) ltac:(lia)).
  pose proof (Z.mod_pos_bound (Ah + loh) (2 ^ 64) ltac:(lia)).
  unfold raw_address in *.
  rewrite (Z.mod_small ((Al + lol) mod 2 ^ 64 + (lo + dl - lol))) in Xl by lia.
  pose proof (Z.div_mod ((Ah + loh) mod 2 ^ 64 + (lo + dh - loh)) (2 ^ 64) ltac:(lia)).
  split; [exact Xl | lia].
Qed.

(** A renew through a pointer p whose object, at base, is freed in the
    memory m traps out of bounds on a freed object (`renew_res/4`);
    never [[unchecked]]. *)
Lemma renew_freed : forall m base reg A off size r al p,
  object_region base (m_regions m) = Some (freed_region reg) -> r_base reg = base -> 0 < size ->
  ptr_cap p = Obj base \/ ptr_cap p = Ro base ->
  exists chk rr, access_res m (raw_address A off) (ptr_cap p) size r al = Some chk /\
    renew_res chk p m = Some rr /\ forall why, rr <> RUnchecked why.
Proof.
  intros m base reg A off size r al p E Hrb Hs Hc.
  exists (RTrap OutOfBounds), (RTrap OutOfBounds).
  unfold access_res, cap_access_res, renew_res.
  destruct Hc as [Hc | Hc]; rewrite Hc, E; simpl; rewrite Hrb.
  all: replace ((base <=? raw_address A off) && (raw_address A off + size <=? base)) with false
         by (symmetry; apply andb_false_iff; destruct (Z.le_gt_cases base (raw_address A off));
             [right; apply Z.leb_gt; lia | left; apply Z.leb_gt; lia]).
  all: split; [reflexivity | split; [reflexivity | discriminate]].
Qed.

(** The arithmetic of a [[renew_hull|renew over a hull]], as
    [renew_access] is a renew's. Where a low span from Al+lol up to
    Al+hil and a high span from Ah+loh up to Ah+hih, of one capability
    c, passed their checks in memories ml and mh that the current memory
    m [persists] from, a renew from A+lo up to A+hi between them
    (`hull_renewable/8`'s arithmetic), aligned as one of them is,
    passes, traps read-only, or finds the object freed; never
    [[unchecked]]. Both sources meet only in m: the object is as both
    saw it, or freed since. *)
Lemma hull_renew_access : forall ml mh m c Al Ah A lol hil rl all loh hih rh alh lo hi r al p dl dh,
  access_res ml (raw_address Al lol) c (hil - lol) rl all = Some ok ->
  access_res mh (raw_address Ah loh) c (hih - loh) rh alh = Some ok ->
  persists ml m -> persists mh m -> objects_fit (m_regions m) -> ptr_cap p = c ->
  lol < hil -> loh < hih ->
  A mod 2 ^ 64 = (Al + dl) mod 2 ^ 64 -> A mod 2 ^ 64 = (Ah + dh) mod 2 ^ 64 ->
  0 <= lo + dl - lol <= 2 ^ 62 -> 0 <= hih - hi - dh <= 2 ^ 62 -> 0 < hi - lo <= 2 ^ 62 -> 0 < al ->
  (all mod al = 0 /\ (lo + dl - lol) mod al = 0) \/ (alh mod al = 0 /\ (lo + dh - loh) mod al = 0) ->
  exists chk rr, access_res m (raw_address A lo) c (hi - lo) r al = Some chk /\ renew_res chk p m = Some rr /\
    forall why, rr <> RUnchecked why.
Proof.
  intros ml mh m c Al Ah A lol hil rl all loh hih rh alh lo hi r al p dl dh
    H1 H2 Hpl Hph Hfit Hc Hl Hh HAl HAh He Hf Hsz Hal Halign.
  set (Ll := raw_address Al lol) in *. set (Lh := raw_address Ah loh) in *.
  destruct c as [| base | base | fn | n]; try discriminate H1.
  all: unfold access_res, cap_access_res in H1, H2.
  all: destruct (object_region base (m_regions ml)) as [regl|] eqn:El; try discriminate H1;
    destruct (object_region base (m_regions mh)) as [regh|] eqn:Eh; try discriminate H2;
    destruct ((base <=? Ll) && (Ll + (hil - lol) <=? r_end regl)) eqn:Bl; try discriminate H1;
    destruct ((base <=? Lh) && (Lh + (hih - loh) <=? r_end regh)) eqn:Bh; try discriminate H2;
    apply andb_true_iff in Bl as [Bl Bl']; apply andb_true_iff in Bh as [Bh Bh'];
    apply Z.leb_le in Bl, Bl', Bh, Bh';
    pose proof (object_region_base _ _ _ El) as Hrl; pose proof (object_region_base _ _ _ Eh) as Hrh.
  (* The object is as both checks saw it, or freed since. *)
  all: destruct (Hpl _ _ El) as [E | E];
    [destruct (Hph _ _ Eh) as [E' | E']; rewrite E in E'; injection E' as E'
    | rewrite <- Hc; exact (renew_freed m base regl A lo (hi - lo) r al p E Hrl ltac:(lia) ltac:(auto))].
  (* as the low check saw it but freed since the high one: empty, so
     the low check could not have passed *)
  all: try (subst regl; simpl in Bl'; lia).
  (* both as they were: one object, which holds the hull *)
  all: subst regh; destruct (Hfit _ _ E) as [Hb0 Hend].
  all: destruct (hull_address Al Ah A lol loh hih dl dh lo hi HAl HAh ltac:(lia) ltac:(lia) Hh He Hf Hsz)
         as [Xl Xh].
  all: unfold access_res, cap_access_res; rewrite E.
  all: replace ((base <=? raw_address A lo) && (raw_address A lo + (hi - lo) <=? r_end regl)) with true
         by (symmetry; apply andb_true_iff; split; apply Z.leb_le; lia).
  (* aligned as the source it is aligned to *)
  all: assert (Ha : forall (aal aah : Z), Ll mod aal = 0 -> Lh mod aah = 0 ->
                 (aal mod al = 0 /\ (lo + dl - lol) mod al = 0) \/ (aah mod al = 0 /\ (lo + dh - loh) mod al = 0) ->
                 raw_address A lo mod al = 0)
         by (intros aal aah Hl1 Hh1 [[A1 A2] | [A1 A2]];
             [rewrite Xl | rewrite Xh]; apply aligned_add; auto; eapply aligned_divisor; eauto).
  - injection H1 as H1. injection H2 as H2.
    rewrite (aligned_res_ok _ _ (Ha _ _ (aligned_res_mod _ _ H1) (aligned_res_mod _ _ H2) Halign)).
    do 2 eexists. split; [reflexivity|]. split; [reflexivity | discriminate].
  - destruct rl; simpl in H1; [|discriminate H1]. destruct rh; simpl in H2; [|discriminate H2].
    injection H1 as H1. injection H2 as H2.
    pose proof (Ha _ _ (aligned_res_mod _ _ H1) (aligned_res_mod _ _ H2) Halign) as Hx.
    destruct r; simpl; [rewrite (aligned_res_ok _ _ Hx)|].
    all: do 2 eexists; split; [reflexivity|]; split; [unfold renew_res; reflexivity | discriminate].
Qed.

(** ## The half check, over memory *)

(** A [[half check]]'s address A+lo is its source span's start A1+lo1
    plus e = D + lo - lo1, modulo 2^64, where D is the distance d0
    between A and A1 that `half_known/6` reads as a signed 64-bit
    number. *)
Lemma half_address : forall A A1 d0 lo lo1,
  A mod 2 ^ 64 = (A1 + d0) mod 2 ^ 64 ->
  raw_address A lo = (raw_address A1 lo1 + (((d0 + 2 ^ 63) mod 2 ^ 64 - 2 ^ 63) + lo - lo1)) mod 2 ^ 64.
Proof.
  intros A A1 d0 lo lo1 HA. unfold raw_address. rewrite Z.add_mod_idemp_l by lia.
  assert (E : (d0 + 2 ^ 63) mod 2 ^ 64 - 2 ^ 63 = d0 + (- ((d0 + 2 ^ 63) / 2 ^ 64)) * 2 ^ 64)
    by (rewrite Z.mod_eq by lia; lia).
  rewrite E.
  replace (A1 + lo1 + (d0 + - ((d0 + 2 ^ 63) / 2 ^ 64) * 2 ^ 64 + lo - lo1))
    with ((A1 + d0 + lo) + - ((d0 + 2 ^ 63) / 2 ^ 64) * 2 ^ 64) by ring.
  rewrite Z_mod_plus_full, <- (Z.add_mod_idemp_l (A1 + d0)), <- HA, Z.add_mod_idemp_l by lia.
  reflexivity.
Qed.

(** The bound bd that a [[half check]] tests natively (`half_bound/6`)
    says what both bounds of the whole check say. The access is at
    address b, e past the start of a span from U up to U+span that
    passed earlier, and that span proves the other bound (f is how far
    the access ends before the span does). The object, from base, ends
    at end1 as it was, empty if freed, or is freed since. The span lies
    in the address space, so the address wraps only where a lower
    check, read signed, falls below 0, which fails both tests. *)
Lemma half_bound_agrees : forall bd base U span end1 e f size b end' life',
  0 <= base <= U -> U + span <= end1 <= 2 ^ 48 -> 0 < span -> 0 < size <= 2 ^ 62 ->
  - 2 ^ 62 <= f -> e <= 2 ^ 62 -> e - f = span - size ->
  b = (U + e) mod 2 ^ 64 ->
  match bd with Upper => 0 <= e | Lower => f <= 0 end ->
  (end' = end1 /\ (life' = Freed -> end1 = base)) \/ (end' = base /\ life' = Freed) ->
  half_bound bd b size base end' life' = (base <=? b) && (b + size <=? end').
Proof.
  intros bd base U span end1 e f size b end' life' Hb Hend Hspan Hsize Hf He Hef Haddr Hbd Hobj.
  destruct bd; unfold half_bound.
  - (* upper: the address does not wrap, so it lies at or above the base *)
    replace b with (U + e) in * by (rewrite Haddr; apply (Z.mod_unique _ _ 0); lia).
    replace (base <=? U + e) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
  - destruct Hobj as [(-> & Hlife) | (-> & ->)].
    + (* lower, the object as it was: live, since a freed object is empty *)
      destruct life'; [|specialize (Hlife eq_refl); lia].
      destruct (Z.le_gt_cases 0 (U + e)) as [Hw | Hw].
      * replace b with (U + e) in * by (rewrite Haddr; apply (Z.mod_unique _ _ 0); lia).
        replace (2 ^ 63 <=? U + e) with false by (symmetry; apply Z.leb_gt; lia).
        replace (U + e + size <=? end1) with true by (symmetry; apply Z.leb_le; lia).
        rewrite andb_true_r. reflexivity.
      * (* wrapped: read signed it is below 0, and no object reaches it *)
        replace b with (U + e + 2 ^ 64) in * by (rewrite Haddr; apply (Z.mod_unique _ _ (-1)); lia).
        replace (2 ^ 63 <=? U + e + 2 ^ 64) with true by (symmetry; apply Z.leb_le; lia).
        replace (base <=? U + e + 2 ^ 64 - 2 ^ 64) with false by (symmetry; apply Z.leb_gt; lia).
        replace (U + e + 2 ^ 64 + size <=? end1) with false by (symmetry; apply Z.leb_gt; lia).
        rewrite andb_false_r. reflexivity.
    + (* lower, freed since: both fail *)
      symmetry. apply andb_false_iff. destruct (Z.le_gt_cases base b);
        [right; apply Z.leb_gt; lia | left; apply Z.leb_gt; lia].
Qed.

(** Where the native test agrees with the whole check's bounds, the
    half check's result is the check's: `half_res/4` is never
    [[unchecked]]. *)
Lemma half_res_agrees : forall (inb ro : bool) r a al p why,
  half_res (if inb then (if ro then readonly_access_res r a al else aligned_res a al) else RTrap OutOfBounds)
           (inb && negb (rights_eqb r Write && ro) && (a mod al =? 0)) (WPtr p) <> RUnchecked why.
Proof.
  intros inb ro r a al p why. unfold readonly_access_res, aligned_res.
  destruct inb, ro, r, (a mod al =? 0); simpl; discriminate.
Qed.

(** Where the span of capability c from A1+lo1 up to A1+hi1 passed its
    check in a memory m1 that lay in the address space, a [[half check]]
    at address A, d0 past A1, whose known bound that span proves
    (`half_known/6`), in a memory m that [persists] from m1 and whose
    freed objects are empty, tests natively what the whole check tests:
    its result is never [[unchecked]]. *)
Lemma half_access : forall m1 m c A1 A lo1 hi1 r1 al1 u bd lo hi r al d0 p,
  access_res m1 (raw_address A1 lo1) c (hi1 - lo1) r1 al1 = Some (RVal u) ->
  objects_fit (m_regions m1) -> persists m1 m -> freed_empty (m_regions m) ->
  A mod 2 ^ 64 = (A1 + d0) mod 2 ^ 64 -> lo1 < hi1 -> lo < hi ->
  half_known bd lo hi d0 lo1 hi1 = true ->
  exists chk passes,
    access_res m (raw_address A lo) c (hi - lo) r al = Some chk /\
    half_passes bd m (raw_address A lo) (hi - lo) c r al = Some (Some passes) /\
    forall why, half_res chk passes (WPtr p) <> RUnchecked why.
Proof.
  intros m1 m c A1 A lo1 hi1 r1 al1 u bd lo hi r al d0 p H Hfit1 Hp Hfe HA Hl1 Hl Hk.
  pose proof (half_address _ _ _ lo lo1 HA) as Hb.
  unfold half_known, near_offset in Hk. cbv zeta in Hk. repeat rewrite andb_true_iff in Hk.
  destruct Hk as ((((_ & He) & (Hf & _)) & Hsz) & Hbd). apply Z.leb_le in He, Hf, Hsz.
  assert (Hbd' : match bd with
                 | Upper => 0 <= (d0 + 2 ^ 63) mod 2 ^ 64 - 2 ^ 63 + lo - lo1
                 | Lower => (d0 + 2 ^ 63) mod 2 ^ 64 - 2 ^ 63 + hi - hi1 <= 0
                 end) by (destruct bd; apply Z.leb_le; exact Hbd).
  assert (HU : 0 <= raw_address A1 lo1) by (apply Z.mod_pos_bound; lia).
  unfold access_res, cap_access_res, half_passes in *.
  destruct c as [| base | base | fn | n]; try discriminate H;
    destruct (object_region base (m_regions m1)) as [reg|] eqn:E; try discriminate H;
    destruct ((base <=? raw_address A1 lo1) && (raw_address A1 lo1 + (hi1 - lo1) <=? r_end reg)) eqn:Ein;
    try discriminate H;
    apply andb_true_iff in Ein as [Ein1 Ein2]; apply Z.leb_le in Ein1, Ein2;
    destruct (Hfit1 _ _ E) as [Hbase Hend]; pose proof (object_region_base _ _ _ E) as Hrb.
  (* The object is as it was, or freed since; either way the native
     test's bound says what the check's bounds say. *)
  all: destruct (Hp _ _ E) as [E' | E']; rewrite E'.
  all: do 2 eexists; split; [reflexivity|]; split; [reflexivity|]; intros why.
  all: rewrite (half_bound_agrees bd base (raw_address A1 lo1) (hi1 - lo1) (r_end reg) _ _ (hi - lo) _ _ _
                 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hf He ltac:(lia) Hb Hbd');
    [ first [exact (half_res_agrees _ false r _ al p why) | exact (half_res_agrees _ true r _ al p why)] | ].
  - (* an object, as it was: empty if freed *)
    left. split; [reflexivity|]. intros Hlife. exact (Hfe _ _ E' Hlife).
  - (* an object, freed since *)
    right. simpl. rewrite Hrb. auto.
  - (* a read-only object, as it was *)
    left. split; [reflexivity|]. intros Hlife. exact (Hfe _ _ E' Hlife).
  - (* a read-only object, freed since *)
    right. simpl. rewrite Hrb. auto.
Qed.

(** ## What a reuse form reads at its point *)

(** An element el of a [[guard chain]] (`guard_chain/3`) is its start
    p itself, or p is a name whose single definition is a [[flight]]
    with a lower donor. [distance_pointer] uses it to show the chain
    starts at something that holds a pointer. *)
Lemma chain_go_head : forall once fuel p lo hi el,
  In el (guard_chain_go once fuel p lo hi) ->
  el = (p, (lo, hi)) \/ exists y d o args b, p = Tmp y /\ lookup y once = Some (DInst (Flight d o args (LowerOf b))).
Proof.
  intros once fuel p lo hi el H. destruct fuel as [|fuel]; simpl in H.
  - destruct H as [E | []]. left. auto.
  - destruct H as [E | H]; [left; auto | right].
    destruct p as [y | c | g]; [|simpl in H; contradiction | simpl in H; contradiction].
    destruct (lookup y once) as [[| ph | i]|] eqn:Ey; try (simpl in H; contradiction).
    destruct i as [| d o args lw | | | | | | | ]; try (simpl in H; contradiction).
    destruct lw; [simpl in H; contradiction | eauto 8].
Qed.

(** A [[flight]] d that steps and continues binds d to a pointer. *)
Lemma flight_step_ptr : forall ge fr m d o args lw e1 l1 m1,
  inst_step ge fr m (Flight d o args lw) = Some (IContinue e1 l1 m1) -> exists pf, lookup d e1 = Some (WPtr pf).
Proof.
  intros ge fr m d o args lw e1 l1 m1 H. simpl in H. cases H. injection H as <- _ _.
  rewrite lookup_put_same. eauto.
Qed.

(** A check-like instruction (one [check_fact] reads) is [replayable]:
    Single.v's invariant covers it. *)
Lemma check_fact_replayable : forall i fa, check_fact i = Some fa -> replayable i = true.
Proof.
  intros i fa H. destruct i as [q k o args | | | | | | | | ]; try discriminate H.
  destruct o; try reflexivity. destruct k; discriminate H.
Qed.

(** A check-like instruction also has an access fact, the range its
    own access checks ([access_fact]). *)
Lemma access_fact_some : forall i fa, check_fact i = Some fa -> exists fb, access_fact i = Some fb.
Proof.
  intros i fa H. destruct i as [q k o args | | | | | | | | ]; try discriminate H.
  destruct k; try (eexists; exact H). destruct o; try (eexists; exact H).
  destruct args as [|a [|a2 args]]; try (eexists; exact H). eexists. reflexivity.
Qed.

(** Lemmas for a frame fr of a [checked_module] md, in memory m, at
    index k of a reachable block l, where every [[single definition]] in
    scope but a `check_ahead` [[replay|replays]] ([scope_plain]). A
    [[doomed]] frame keeps that much, so Doomed.v uses these too. *)
Section Plain.

Variables (ge : genv) (md : module) (fr : frame) (m : Memory.mem) (l : name) (k : Z).
Hypothesis Hmd : checked_module md.
Hypothesis Hin : In (IFunc (fr_fn fr)) md.
Hypothesis Hr : is_reachable (fn_doms (fr_fn fr)) l = true.
Hypothesis Hs : scope_plain ge fr m.
Hypothesis Hpt : point_site (fr_fn fr) (fr_at fr) = Some (l, k).

(** A value p a known distance d from a value p1 that holds a pointer
    (`pointer_distance/4`) holds a pointer too, where the single
    definitions of both [[dominance|dominate]] the point. p's
    [[guard chain]] starts at a single definition: the exact base
    itself, which p1's chain reads, or a [[flight]], which binds a
    pointer ([chain_go_head]). *)
Lemma distance_pointer : forall p p1 pp1 d,
  value_x ge (fr_env fr) P p1 = Some (WPtr pp1) ->
  (forall y, p = Tmp y -> once_has (single_definitions (fr_fn fr)) y = true -> dominating (fr_fn fr) l k y) ->
  (forall y, p1 = Tmp y -> once_has (single_definitions (fr_fn fr)) y = true -> dominating (fr_fn fr) l k y) ->
  pointer_distance (single_definitions (fr_fn fr)) p p1 = Some d ->
  exists pp, value_x ge (fr_env fr) P p = Some (WPtr pp).
Proof.
  intros p p1 pp1 d Hp1 Hd Hd1 H. rewrite pointer_distance_eq in H.
  destruct (first_some_in _ _ _ _ _ H) as (el & Hel & Hf).
  destruct (exact_base (single_definitions (fr_fn fr)) el) as [[n0 k0]|] eqn:Eb; [|discriminate Hf].
  destruct (first_some_in _ _ _ _ _ Hf) as (el1 & Hel1 & Hf1).
  destruct el1 as [[n1 | c1 | g1] [k1 k1']]; try discriminate Hf1.
  destruct (name_eqb n1 n0 && (k1 =? k1')) eqn:E1; [|discriminate Hf1].
  apply andb_true_iff in E1 as [En _]. apply name_eqb_true in En. subst n1.
  rewrite guard_chain_eq in Hel.
  destruct (chain_go_head _ _ _ _ _ _ Hel) as [-> | (y & d' & o & args & b & -> & Ey)].
  - (* the exact base is p itself, which p1's chain reads *)
    destruct p as [y | c | g]; try discriminate Eb. unfold exact_base in Eb.
    destruct (once_has (single_definitions (fr_fn fr)) y) eqn:Ho; [|discriminate Eb].
    injection Eb as <- _.
    assert (Hst : stable (single_definitions (fr_fn fr)) (Tmp y)) by (intros y' E; injection E as <-; exact Ho).
    destruct (guard_chain_sound ge md fr m l k Hmd Hin Hr Hs Hpt _ _ _ _ _ Hp1 Hd1 Hel1 Hst) as (pb & _ & Hpb & _).
    eauto.
  - (* p is a flight, which binds a pointer *)
    assert (Ho : once_has (single_definitions (fr_fn fr)) y = true) by (unfold once_has; rewrite Ey; reflexivity).
    pose proof (flight_def_name _ _ _ _ _ _ Ey) as ->.
    destruct (plain_replays _ _ _ _ _ _ _ Hs Hpt Ey eq_refl eq_refl (Hd y eq_refl Ho))
      as (fr0 & m0 & e1 & l1 & m1 & Hst & Hy & _).
    destruct (flight_step_ptr _ _ _ _ _ _ _ _ _ _ Hst) as [pf Hpf].
    exists pf. simpl. rewrite <- Hy, Hpf. reflexivity.
Qed.

End Plain.

(** Lemmas for a frame fr as in [Plain], but where every replayable
    single definition in scope replays ([scope_holds]), `check_ahead`
    included, since a renew's source may be one. *)
Section Reuse.

Variables (ge : genv) (md : module) (fr : frame) (m : Memory.mem) (l : name) (k : Z).
Hypothesis Hmd : checked_module md.
Hypothesis Hin : In (IFunc (fr_fn fr)) md.
Hypothesis Hr : is_reachable (fn_doms (fr_fn fr)) l = true.
Hypothesis Hs : scope_holds ge fr m.
Hypothesis Hpt : point_site (fr_fn fr) (fr_at fr) = Some (l, k).

(** A single-definition operand y of the instruction i at the frame's
    point, index kk of block b, has a site that
    [[dominance|dominates]] the point: the [[validator]] requires an
    operand's definition to dominate its use (`definitions_dominate/3`). *)
Lemma operand_at : forall b kk i y,
  find_block l (fn_blocks (fr_fn fr)) = Some b -> nth_error (b_insts b) kk = Some i -> k = Z.of_nat kk ->
  In y (inst_uses i) -> once_has (single_definitions (fr_fn fr)) y = true -> dominating (fr_fn fr) l k y.
Proof.
  intros b kk i y Hb Hk -> Hu Ho.
  destruct (func_facts _ _ Hmd Hin) as (b0 & rest & _ & _ & _ & Hdd).
  destruct (find_block_in _ _ _ Hb) as [Hbin Hl].
  unfold once_has in Ho. destruct (lookup y (single_definitions (fr_fn fr))) as [D|] eqn:Ey; [|discriminate Ho].
  rewrite <- Hl in Hr.
  destruct (use_dominated _ _ _ _ _ _ _ Hdd Hbin Hr Hk Hu Ey) as (s & Hpos & Hsd).
  exists s, D. rewrite <- Hl. auto.
Qed.

(** A [[renew source]] n1 of the pointer p1 that dominates the point
    holds the pointer pp that p1 holds, and the check n1 made of pp
    passed ([check_passes]) in a memory m1 that lay in the address space
    and that the current memory [persists] from. p1 dominates the point
    too, and the checked span is nonempty. *)
Lemma renew_source_holds : forall n1 p1 lo1 hi1 al1,
  lookup n1 (s_renews (fn_src md (fr_fn fr))) = Some (p1, lo1, hi1, al1) -> dominating (fr_fn fr) l k n1 ->
  exists pp m1 r1,
    lookup n1 (fr_env fr) = Some (WPtr pp) /\ value_x ge (fr_env fr) P (Tmp p1) = Some (WPtr pp) /\
    check_passes m1 pp lo1 hi1 r1 al1 /\ persists m1 m /\ objects_fit (m_regions m1) /\
    lo1 < hi1 /\ dominating (fr_fn fr) l k p1.
Proof.
  intros n1 p1 lo1 hi1 al1 Hsrc Hdom.
  destruct (renew_source_def _ _ _ _ _ _ _ Hsrc) as (i1 & r1 & Hn1 & Hcf & Hop1).
  destruct (dominating_replays _ _ _ _ _ _ _ Hs Hpt Hn1 (check_fact_replayable _ _ Hcf) Hdom)
    as (fr0 & m0 & e1 & l1 & m1 & Hst & He1 & Hops & Hp & Hfit).
  destruct (access_fact_some _ _ Hcf) as [fb Hfb].
  destruct (check_like_continue _ _ _ _ _ _ _ _ _ Hcf Hfb Hst) as (-> & _ & _ & pp & -> & Hx & Hc & _).
  cbn [f_q f_p f_lo f_hi f_r f_al] in Hx, Hc, He1.
  assert (Hu1 : In p1 (inst_uses i1)) by exact (check_fact_uses _ _ _ Hcf eq_refl).
  exists pp, m0, r1. split; [rewrite <- He1; apply lookup_put_same|].
  split; [rewrite <- Hx; symmetry; apply value_x_agree; intros y E; injection E as <-; exact (Hops _ Hu1 Hop1)|].
  split; [exact Hc|]. split; [exact Hp|]. split; [exact Hfit|]. split.
  - destruct Hdom as (s & D & Hn & Hpos & _). rewrite Hn1 in Hn. injection Hn as <-.
    destruct (dinst_site _ _ _ _ Hpos) as (d & j & ->).
    destruct (position_inst _ _ _ _ _ Hpos) as (b1 & kk1 & Hb1 & _ & Hk1 & _ & _).
    exact (proj1 (check_fact_ok _ _ _ _ _ Hmd Hin Hb1 (nth_error_In _ _ Hk1) Hcf)).
  - exact (operand_dominating _ _ _ _ _ _ _ Hmd Hin Hr Hn1 Hdom Hu1 Hop1).
Qed.

(** What a renew or half check i the pass accepted reads at the frame's
    point, index kk of block b. Q1, the name n1, holds the pointer PP1
    of a [[renew source]]'s check that passed in m1, a memory in the
    address space that the current one [persists] from; the renewed
    value p holds a pointer PP of PP1's [[capability]], d past it modulo
    2^64 ([renew_source_holds], [pointer_distance_sound]). *)
Lemma reuse_operands : forall b kk i n1 p p1 lo1 hi1 al1 d,
  find_block l (fn_blocks (fr_fn fr)) = Some b -> nth_error (b_insts b) kk = Some i -> k = Z.of_nat kk ->
  In n1 (inst_uses i) -> (forall y, p = Tmp y -> In y (inst_uses i)) ->
  lookup n1 (s_renews (fn_src md (fr_fn fr))) = Some (p1, lo1, hi1, al1) ->
  pointer_distance (single_definitions (fr_fn fr)) p (Tmp p1) = Some d ->
  exists pp1 pp m1 r1,
    lookup n1 (fr_env fr) = Some (WPtr pp1) /\ value_x ge (fr_env fr) P p = Some (WPtr pp) /\
    check_passes m1 pp1 lo1 hi1 r1 al1 /\ persists m1 m /\ objects_fit (m_regions m1) /\ lo1 < hi1 /\
    ptr_cap pp = ptr_cap pp1 /\ ptr_addr pp mod 2 ^ 64 = (ptr_addr pp1 + d) mod 2 ^ 64.
Proof.
  intros b kk i n1 p p1 lo1 hi1 al1 d Hb Hk Hkk Hu1 Hu Esrc Ed.
  destruct (renew_source_def _ _ _ _ _ _ _ Esrc) as (i1 & _ & En1 & _).
  assert (Hdn1 : dominating (fr_fn fr) l k n1)
    by (apply (operand_at b kk i n1 Hb Hk Hkk Hu1); unfold once_has; rewrite En1; reflexivity).
  destruct (renew_source_holds n1 p1 lo1 hi1 al1 Esrc Hdn1)
    as (pp1 & m1 & r1 & Hn1 & Hp1 & Hc1 & Hp & Hfit1 & Hl1 & Hdp1).
  assert (Hdp : forall y, p = Tmp y -> once_has (single_definitions (fr_fn fr)) y = true -> dominating (fr_fn fr) l k y)
    by (intros y E Ho; exact (operand_at b kk i y Hb Hk Hkk (Hu y E) Ho)).
  assert (Hdq : forall y, Tmp p1 = Tmp y -> once_has (single_definitions (fr_fn fr)) y = true -> dominating (fr_fn fr) l k y)
    by (intros y E _; injection E as <-; exact Hdp1).
  destruct (distance_pointer ge md fr m l k Hmd Hin Hr (scope_plain_of _ _ _ Hs) Hpt p (Tmp p1) pp1 d Hp1 Hdp Hdq Ed)
    as [pp Hpp].
  destruct (pointer_distance_sound ge md fr m l k Hmd Hin Hr (scope_plain_of _ _ _ Hs) Hpt p (Tmp p1) pp pp1 d Hpp Hp1 Hdp Hdq Ed)
    as [Hcap Haddr].
  exists pp1, pp, m1, r1. auto 10.
Qed.

(** `check_align/1` allows only positive alignments. *)
Lemma check_align_pos : forall al, check_align al = true -> 0 < al.
Proof.
  unfold check_align. intros al H. simpl in H.
  repeat (apply orb_true_iff in H as [H | H]; [apply Z.eqb_eq in H; lia|]). discriminate H.
Qed.

(** Every [[capability]] equals itself by [cap_eqb]. *)
Lemma cap_eqb_refl : forall c, cap_eqb c c = true.
Proof. intros []; simpl; try apply Z.eqb_refl; try apply name_eqb_refl; reflexivity. Qed.

(** A [[renew]] of the value p from source n1, the instruction at index
    kk of block b, that the pass accepts ([checked_inst_rest],
    `checked_inst_rest/7`) does not step to [[unchecked]], in a memory in
    the address space. Its source holds the pointer whose check passed
    and the renewed pointer has its capability ([reuse_operands]), so
    there is no alias; and its span lies inside the source's
    ([renew_access]). *)
Theorem renew_not_unchecked : forall b kk q lo hi r al n1 p rest live out why,
  objects_fit (m_regions m) ->
  find_block l (fn_blocks (fr_fn fr)) = Some b ->
  nth_error (b_insts b) kk = Some (Let q A (Renew lo hi r al) [Tmp n1; p]) -> k = Z.of_nat kk ->
  checked_inst_rest (fn_src md (fr_fn fr)) (Let q A (Renew lo hi r al) [Tmp n1; p]) rest live = Some out ->
  inst_step ge fr m (Let q A (Renew lo hi r al) [Tmp n1; p]) <> Some (IStop (Unchecked why)).
Proof.
  intros b kk q lo hi r al n1 p rest live out why Hfit Hb Hk Hkk H.
  (* What the pass checked: a source, a distance, and the span inside. *)
  unfold checked_inst_rest in H. cbn beta iota zeta in H.
  destruct (lookup n1 (s_renews (fn_src md (fr_fn fr)))) as [[[[p1 lo1] hi1] al1]|] eqn:Esrc; [|discriminate H].
  destruct (pointer_distance (s_once (fn_src md (fr_fn fr))) p (Tmp p1)) as [d|] eqn:Ed; [|discriminate H].
  cbn beta iota in H.
  destruct (negb _) eqn:Eok; [discriminate H|]. clear H.
  apply negb_false_iff in Eok. repeat rewrite andb_true_iff in Eok.
  destruct Eok as (((Hlo & Hhi) & Hal) & Hoff).
  apply Z.leb_le in Hlo, Hhi. apply Z.eqb_eq in Hal, Hoff.
  (* What the operands hold at the point. *)
  destruct (reuse_operands b kk _ n1 p p1 lo1 hi1 al1 d Hb Hk Hkk ltac:(simpl; auto)
              ltac:(intros y ->; simpl; auto) Esrc Ed)
    as (pp1 & pp & m1 & r1 & Hn1 & Hpp & Hc1 & Hp & _ & _ & Hcap & Haddr).
  (* The step: one capability, so no alias; then the memory's answer. *)
  rewrite inst_step_let by reflexivity. cbn beta iota zeta delta [op_arg_classes map2_option].
  replace (value_x ge (fr_env fr) A (Tmp n1)) with (Some (WPtr pp1)) by (simpl; rewrite Hn1; reflexivity).
  rewrite Hpp. cbn beta iota. unfold op_res, op_res_int. cbn beta iota zeta delta [fmt_of].
  rewrite Hcap, cap_eqb_refl.
  destruct (find_block_in _ _ _ Hb) as [Hbin _].
  destruct (check_fact_ok _ _ _ _ _ Hmd Hin Hbin (nth_error_In _ _ Hk) eq_refl) as [Hsz Hca]. simpl in Hsz, Hca.
  pose proof (check_align_pos _ Hca) as Hal0.
  replace (raw_address (ptr_addr pp) lo) with (raw_address (ptr_addr pp1) (lo + d))
    by (unfold raw_address; symmetry; rewrite <- Z.add_mod_idemp_l, Haddr, Z.add_mod_idemp_l by lia; f_equal; lia).
  destruct (renew_access m1 m (ptr_cap pp1) (ptr_addr pp1) lo1 hi1 r1 al1 tt (lo + d) (hi - lo) r al pp
              Hc1 Hp Hfit Hcap Hlo ltac:(lia) ltac:(lia) Hal0 Hal Hoff) as (chk & rr & Hchk & Hrr & Hnot).
  rewrite Hchk. cbn beta iota. rewrite Hrr. unfold bind_res.
  destruct rr as [x | w | w]; try discriminate. intros E. injection E as <-. exact (Hnot w eq_refl).
Qed.

(** A [[half check]] of the value p from source n1, the instruction at
    index kk of block b, that the pass accepts ([checked_inst_rest])
    does not step to [[unchecked]], in a memory in the address space
    whose freed objects are empty. The bound it does not test is proved
    by the source's span, which passed ([half_access]). *)
Theorem half_not_unchecked : forall b kk q bd lo hi r al n1 p rest live out why,
  objects_fit (m_regions m) -> freed_empty (m_regions m) ->
  find_block l (fn_blocks (fr_fn fr)) = Some b ->
  nth_error (b_insts b) kk = Some (Let q A (HalfCheck bd lo hi r al) [Tmp n1; p]) -> k = Z.of_nat kk ->
  checked_inst_rest (fn_src md (fr_fn fr)) (Let q A (HalfCheck bd lo hi r al) [Tmp n1; p]) rest live = Some out ->
  inst_step ge fr m (Let q A (HalfCheck bd lo hi r al) [Tmp n1; p]) <> Some (IStop (Unchecked why)).
Proof.
  intros b kk q bd lo hi r al n1 p rest live out why Hfit Hfe Hb Hk Hkk H.
  (* What the pass checked: a source, a distance, and the known bound. *)
  unfold checked_inst_rest in H. cbn beta iota zeta in H.
  destruct (lookup n1 (s_renews (fn_src md (fr_fn fr)))) as [[[[p1 lo1] hi1] al1]|] eqn:Esrc;
    [|discriminate H].
  destruct (pointer_distance (s_once (fn_src md (fr_fn fr))) p (Tmp p1)) as [d|] eqn:Ed; [|discriminate H].
  destruct (half_known bd lo hi d lo1 hi1) eqn:Ek; [clear H | discriminate H].
  (* What the operands hold at the point. *)
  destruct (reuse_operands b kk _ n1 p p1 lo1 hi1 al1 d Hb Hk Hkk ltac:(simpl; auto)
              ltac:(intros y ->; simpl; auto) Esrc Ed)
    as (pp1 & pp & m1 & r1 & Hn1 & Hpp & Hc1 & Hp & Hfit1 & Hl1 & Hcap & Haddr).
  (* The step: one capability, so no alias; then the memory's answer. *)
  rewrite inst_step_let by reflexivity. cbn beta iota zeta delta [op_arg_classes map2_option].
  replace (value_x ge (fr_env fr) A (Tmp n1)) with (Some (WPtr pp1)) by (simpl; rewrite Hn1; reflexivity).
  rewrite Hpp. cbn beta iota. unfold op_res, op_res_int. cbn beta iota zeta delta [fmt_of].
  rewrite Hcap, cap_eqb_refl.
  destruct (find_block_in _ _ _ Hb) as [Hbin _].
  destruct (check_fact_ok _ _ _ _ _ Hmd Hin Hbin (nth_error_In _ _ Hk) eq_refl) as [Hsz _]. simpl in Hsz.
  destruct (half_access m1 m (ptr_cap pp1) (ptr_addr pp1) (ptr_addr pp) lo1 hi1 r1 al1 tt bd lo hi r al d pp
              Hc1 Hfit1 Hp Hfe Haddr Hl1 Hsz Ek) as (chk & passes & Hchk & Hpass & Hnot).
  rewrite Hchk. cbn beta iota. rewrite Hpass. cbn beta iota. unfold bind_res.
  destruct (half_res chk passes (WPtr pp)) as [x | w | w] eqn:Eh; try discriminate.
  intros E. injection E as <-. exact (Hnot w eq_refl).
Qed.

(** A [[renew_hull|renew over a hull]] of the value p with low source nl
    and high source nh, the instruction at index kk of block b, that the
    pass accepts ([checked_inst_rest]) does not step to [[unchecked]],
    in a memory in the address space. Each source holds the pointer its
    check passed, a known distance from the renewed pointer
    ([reuse_operands]), so all three share a capability, and the renewed
    span lies between the two spans (`hull_renewable/8`,
    [hull_renew_access]). *)
Theorem hull_renew_not_unchecked : forall b kk q lo hi r al nl nh p rest live out why,
  objects_fit (m_regions m) ->
  find_block l (fn_blocks (fr_fn fr)) = Some b ->
  nth_error (b_insts b) kk = Some (Let q A (RenewHull lo hi r al) [Tmp nl; Tmp nh; p]) -> k = Z.of_nat kk ->
  checked_inst_rest (fn_src md (fr_fn fr)) (Let q A (RenewHull lo hi r al) [Tmp nl; Tmp nh; p]) rest live
    = Some out ->
  inst_step ge fr m (Let q A (RenewHull lo hi r al) [Tmp nl; Tmp nh; p]) <> Some (IStop (Unchecked why)).
Proof.
  intros b kk q lo hi r al nl nh p rest live out why Hfit Hb Hk Hkk H.
  (* What the pass checked: two sources, two distances, and the span
     between them. *)
  unfold checked_inst_rest in H. cbn beta iota zeta in H.
  destruct (hull_renewable _ _ _ _ _ _ _ _) eqn:Ehr; [clear H | discriminate H].
  unfold hull_renewable in Ehr.
  destruct (lookup nl (s_renews (fn_src md (fr_fn fr)))) as [[[[pl lol] hil] all]|] eqn:El;
    [|discriminate Ehr].
  destruct (lookup nh (s_renews (fn_src md (fr_fn fr)))) as [[[[ph loh] hih] alh]|] eqn:Eh;
    [|discriminate Ehr].
  destruct (pointer_distance (s_once (fn_src md (fr_fn fr))) p (Tmp pl)) as [dl|] eqn:Edl; [|discriminate Ehr].
  destruct (pointer_distance (s_once (fn_src md (fr_fn fr))) p (Tmp ph)) as [dh|] eqn:Edh; [|discriminate Ehr].
  cbn beta iota zeta in Ehr.
  repeat match goal with H : (_ && _) = true |- _ => apply andb_true_iff in H as [? ?] end.
  repeat match goal with H : (_ <=? _) = true |- _ => apply Z.leb_le in H end.
  assert (Halign : (all mod al = 0 /\ (lo + dl - lol) mod al = 0) \/ (alh mod al = 0 /\ (lo + dh - loh) mod al = 0))
    by (match goal with H : (_ || _) = true |- _ =>
          apply orb_true_iff in H as [H | H]; apply andb_true_iff in H as [Ha1 Ha2];
          apply Z.eqb_eq in Ha1, Ha2; [left | right]; split; assumption end).
  (* What the operands hold at the point. *)
  destruct (reuse_operands b kk _ nl p pl lol hil all dl Hb Hk Hkk ltac:(simpl; auto)
              ltac:(intros y ->; simpl; auto) El Edl)
    as (ppl & pp & ml & rl & Hnl & Hpp & Hcl & Hpl & _ & Hll & Hcapl & Haddrl).
  destruct (reuse_operands b kk _ nh p ph loh hih alh dh Hb Hk Hkk ltac:(simpl; auto)
              ltac:(intros y ->; simpl; auto) Eh Edh)
    as (pph & pp' & mh & rh & Hnh & Hpp' & Hch & Hph & _ & Hlh & Hcaph & Haddrh).
  rewrite Hpp in Hpp'. injection Hpp' as <-.
  (* The step: one capability, so no alias; then the memory's answer. *)
  rewrite inst_step_let by reflexivity. cbn beta iota zeta delta [op_arg_classes map2_option].
  replace (value_x ge (fr_env fr) A (Tmp nl)) with (Some (WPtr ppl)) by (simpl; rewrite Hnl; reflexivity).
  replace (value_x ge (fr_env fr) A (Tmp nh)) with (Some (WPtr pph)) by (simpl; rewrite Hnh; reflexivity).
  rewrite Hpp. cbn beta iota. unfold op_res, op_res_int. cbn beta iota zeta delta [fmt_of].
  rewrite <- Hcapl, <- Hcaph, cap_eqb_refl. cbn beta iota delta [andb].
  destruct (find_block_in _ _ _ Hb) as [Hbin _].
  destruct (check_fact_ok _ _ _ _ _ Hmd Hin Hbin (nth_error_In _ _ Hk) eq_refl) as [Hsz Hca]. simpl in Hsz, Hca.
  unfold check_passes in Hcl, Hch. rewrite <- Hcapl in Hcl. rewrite <- Hcaph in Hch.
  destruct (hull_renew_access ml mh m (ptr_cap pp) (ptr_addr ppl) (ptr_addr pph) (ptr_addr pp)
              lol hil rl all loh hih rh alh lo hi r al pp dl dh
              Hcl Hch Hpl Hph Hfit eq_refl Hll Hlh Haddrl Haddrh ltac:(lia) ltac:(lia) ltac:(lia)
              (check_align_pos _ Hca) Halign) as (chk & rr & Hchk & Hrr & Hnot).
  rewrite Hchk. cbn beta iota. rewrite Hrr. unfold bind_res.
  destruct rr as [x | w | w]; try discriminate. intros E. injection E as <-. exact (Hnot w eq_refl).
Qed.

End Reuse.

(** ## Along every run *)

(** The instructions this file covers: a `let` of a renew, a renew
    over a hull or a half check, of any class and operands. None is a
    raw access. *)
Definition reuse_form (i : inst) : Prop :=
  (exists q kc lo hi r al args, i = Let q kc (Renew lo hi r al) args) \/
  (exists q kc lo hi r al args, i = Let q kc (RenewHull lo hi r al) args) \/
  (exists q kc bd lo hi r al args, i = Let q kc (HalfCheck bd lo hi r al) args).

(** A list of operands that [map2_option] pairs with two classes has
    two elements. *)
Lemma map2_option_two : forall (X Y Z : Type) (f : X -> Y -> option Z) x y args zs,
  map2_option f [x; y] args = Some zs -> exists a1 a2, args = [a1; a2].
Proof.
  intros X Y Z f x y args zs H. destruct args as [|a1 [|a2 [|a3 args]]]; simpl in H; try discriminate H.
  - destruct (f x a1); discriminate H.
  - eauto.
  - destruct (f x a1), (f y a2); discriminate H.
Qed.

(** A list of operands that [map2_option] pairs with three classes has
    three elements. *)
Lemma map2_option_three : forall (X Y Z : Type) (f : X -> Y -> option Z) x y w args zs,
  map2_option f [x; y; w] args = Some zs -> exists a1 a2 a3, args = [a1; a2; a3].
Proof.
  intros X Y Z f x y w args zs H. destruct args as [|a1 [|a2 [|a3 [|a4 args]]]]; simpl in H;
    repeat match goal with H : context [match f ?u ?v with _ => _ end] |- _ => destruct (f u v) end;
    try discriminate H; eauto.
Qed.

(** A [reuse_form] that steps to [[unchecked]] is of the proof
    [[class]] A, with two operands for a renew or half check and three
    for a renew over a hull (`op_arg_classes/4`, `kind_res/8`); of any
    other shape it does not step. So the run theorem covers every such
    instruction with the frame lemmas, which take only that shape. *)
Lemma reuse_shape : forall ge fr m i why,
  reuse_form i -> inst_step ge fr m i = Some (IStop (Unchecked why)) ->
  exists q o args, i = Let q A o args /\
    ((exists lo hi r al a1 a2, o = Renew lo hi r al /\ args = [a1; a2]) \/
     (exists lo hi r al a1 a2 a3, o = RenewHull lo hi r al /\ args = [a1; a2; a3]) \/
     (exists bd lo hi r al a1 a2, o = HalfCheck bd lo hi r al /\ args = [a1; a2])).
Proof.
  intros ge fr m i why [(q & kc & lo & hi & r & al & args & ->)
                       | [(q & kc & lo & hi & r & al & args & ->) | (q & kc & bd & lo & hi & r & al & args & ->)]] H;
    rewrite inst_step_let in H by reflexivity; cbn beta iota zeta delta [op_arg_classes] in H;
    destruct (map2_option _ _ args) as [xs|] eqn:Ex; try discriminate H.
  - destruct (map2_option_two _ _ _ _ _ _ _ _ Ex) as (a1 & a2 & ->).
    destruct kc; unfold op_res, op_res_int in H; cbn beta iota zeta delta [fmt_of] in H; try discriminate H;
      do 3 eexists; split; [reflexivity | left; eauto 10].
  - destruct (map2_option_three _ _ _ _ _ _ _ _ _ Ex) as (a1 & a2 & a3 & ->).
    destruct kc; unfold op_res, op_res_int in H; cbn beta iota zeta delta [fmt_of] in H; try discriminate H;
      do 3 eexists; split; [reflexivity | right; left; eauto 10].
  - destruct (map2_option_two _ _ _ _ _ _ _ _ Ex) as (a1 & a2 & ->).
    destruct kc; unfold op_res, op_res_int in H; cbn beta iota zeta delta [fmt_of] in H; try discriminate H;
      do 3 eexists; split; [reflexivity | right; right; eauto 10].
Qed.

(** The frame theorems carried along every [[run]] of the [[machine]] of
    a [[runtime]] R, as Chain.v's [Hull] does: Persistence.v's invariant
    says the pass accepted the instruction at the point, Single.v's that
    single definitions [[replay]] there, and the runtime's
    [[ready|readiness]] that memory lies in the address space with freed
    objects empty. *)
Module Reuse (R : Runtime).

Module H := Hull R.

(** What holds at the point of a frame that is not [[doomed]], in every
    state c a run reaches from a call of a function f of a
    [checked_module] md started [[ready]], at an instruction i that is
    not a raw access or raw call: the pass accepted it there
    ([checked_inst_rest], `checked_inst_rest/7`), single definitions
    [[replay]] ([scope_holds]), and memory lies in the address space
    with freed objects empty. Guard.v's run theorem uses it too. *)
Lemma run_point : forall ge md f xs fr m fuel s0 c s l i rest j,
  checked_module md -> ge_module ge = md -> ge_free ge = R.free ->
  In (IFunc f) md -> call_frame f xs = Some fr -> R.ready s0 m ->
  H.P.I.RM.mreachable ge (mkConfig fr [] m fuel, s0) (c, s) ->
  fr_doomed (c_frame c) = None -> fr_at (c_frame c) = Exec l (i :: rest) j ->
  raw_access i = None -> (forall r cl args, i <> RawCall r cl args) -> (forall q, i <> Touch q) ->
  exists b kk live out,
    In (IFunc (fr_fn (c_frame c))) md /\ is_reachable (fn_doms (fr_fn (c_frame c))) l = true /\
    scope_holds ge (c_frame c) (c_mem c) /\
    point_site (fr_fn (c_frame c)) (fr_at (c_frame c)) = Some (l, Z.of_nat kk) /\
    find_block l (fn_blocks (fr_fn (c_frame c))) = Some b /\ nth_error (b_insts b) kk = Some i /\
    checked_inst_rest (fn_src md (fr_fn (c_frame c))) i rest live = Some out /\
    objects_fit (m_regions (c_mem c)) /\ freed_empty (m_regions (c_mem c)).
Proof.
  intros ge md f xs fr m fuel s0 c s l i rest j Hmd Hge Hfree Hin Hcf H0 Hreach Hd Ha Hra Hrc Hrt.
  (* The pass accepted the instruction at the point. *)
  pose proof (H.P.mreachable_inv _ _ _ _ Hge Hmd Hfree Hreach H0 (H.P.start_inv _ _ _ _ _ _ _ s0 Hmd Hin Hcf))
    as [(Hinf & _ & Hpo) _].
  simpl in Hinf, Hpo. destruct Hpo as [Hd0 | Hpo]; [congruence|].
  destruct (H.P.I.point_ok_exec_inv _ _ _ _ _ _ _ Hpo Ha) as (E & b & out & kk & _ & Hb & _ & _ & Hk & Hat).
  destruct Hat as [(live & Hw & _ & _) | (access & rest' & live' & E' & _ & _ & Hpc)].
  2: { (* only a raw access, a touch or a raw call follows a check as its access *)
       injection E' as <- _. exfalso.
       destruct Hpc as [(fb & pre & [Hcov | E''] & _) | (_ & r & q' & args & p & E'' & _)].
       - unfold covered_access in Hcov. rewrite Hra in Hcov. discriminate Hcov.
       - exact (Hrt _ E'').
       - exact (Hrc _ _ _ E''). }
  destruct (walks_cons _ _ _ _ _ Hw) as (rest' & live' & Hc & _).
  (* Single definitions replay there. *)
  pose proof (H.S.run_sinv _ _ _ _ _ _ _ _ _ Hmd Hge Hfree Hin Hcf H0 (H.mreachable_same _ _ _ Hreach))
    as [[Hsh Hsc] _].
  simpl in Hsh, Hsc. destruct Hsc as [Hsc | Hsc]; [congruence|].
  unfold shaped in Hsh. cbv zeta in Hsh. rewrite Ha in Hsh. destruct Hsh as (_ & Hr & _).
  (* Memory lies in the address space, freed objects empty. *)
  pose proof (H.P.I.RM.mreachable_ready _ _ _ Hfree Hreach H0) as Hready.
  destruct (skipn_cons _ _ _ _ _ (eq_sym Hk)) as (Hnth & _ & Hlen).
  exists b, kk, live, (rest', live'). split; [exact Hinf|]. split; [exact Hr|]. split; [exact Hsc|].
  split; [rewrite Ha, Hk; apply point_site_exec; [exact Hb | lia]|].
  split; [exact Hb|]. split; [exact Hnth|]. split; [exact Hc|].
  exact (conj (R.address_space _ _ Hready) (R.freed_bounds _ _ Hready)).
Qed.

(** In every state a [[run]] reaches from a call of a function f of a
    [checked_module] md, started in a memory where the runtime is
    [[ready]], a frame that is not [[doomed]] runs no renew, renew over
    a hull or half check to an [[unchecked]] outcome. Every runtime
    spares the pass's facts at [[poll|safepoints]] ([spares_any]; see
    [The evidence invariant over runs](../../docs/rocq.md#the-evidence-invariant-over-runs)). *)
Theorem run_reuse_checked : forall ge md f xs fr m fuel s0 c s l i rest j why,
  checked_module md -> ge_module ge = md -> ge_free ge = R.free ->
  In (IFunc f) md -> call_frame f xs = Some fr -> R.ready s0 m ->
  H.P.I.RM.mreachable ge (mkConfig fr [] m fuel, s0) (c, s) ->
  fr_doomed (c_frame c) = None -> fr_at (c_frame c) = Exec l (i :: rest) j -> reuse_form i ->
  inst_step ge (c_frame c) (c_mem c) i <> Some (IStop (Unchecked why)).
Proof.
  intros ge md f xs fr m fuel s0 c s l i rest j why Hmd Hge Hfree Hin Hcf H0 Hreach Hd Ha Hi Hst.
  destruct (reuse_shape _ _ _ _ _ Hi Hst) as (q & o & args & -> & Ho).
  destruct (run_point _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hmd Hge Hfree Hin Hcf H0 Hreach Hd Ha
              ltac:(destruct Ho as [(? & ? & ? & ? & ? & ? & -> & ->)
                                   | [(? & ? & ? & ? & ? & ? & ? & -> & ->) | (? & ? & ? & ? & ? & ? & ? & -> & ->)]];
                    reflexivity)
              ltac:(intros ? ? ? E; discriminate E) ltac:(intros ? E; discriminate E))
    as (b & kk & live & out & Hinf & Hr & Hsc & Hpt & Hb & Hnth & Hc & Hfit & Hfe).
  (* The pass accepts a reuse form only where its sources are proofs'
     names. *)
  destruct Ho as [(lo & hi & r & al & a1 & a2 & -> & ->)
                 | [(lo & hi & r & al & a1 & a2 & a3 & -> & ->) | (bd & lo & hi & r & al & a1 & a2 & -> & ->)]].
  - destruct a1 as [n1 | c1 | g1];
      try (unfold checked_inst_rest in Hc; cbn beta iota zeta in Hc; discriminate Hc).
    exact (renew_not_unchecked ge md (c_frame c) (c_mem c) l (Z.of_nat kk) Hmd Hinf Hr Hsc Hpt
             b kk q lo hi r al n1 a2 rest live out why Hfit Hb Hnth eq_refl Hc Hst).
  - destruct a1 as [nl | c1 | g1], a2 as [nh | c2 | g2];
      try (unfold checked_inst_rest, hull_renewable in Hc; cbn beta iota zeta in Hc; discriminate Hc).
    exact (hull_renew_not_unchecked ge md (c_frame c) (c_mem c) l (Z.of_nat kk) Hmd Hinf Hr Hsc Hpt
             b kk q lo hi r al nl nh a3 rest live out why Hfit Hb Hnth eq_refl Hc Hst).
  - destruct a1 as [n1 | c1 | g1];
      try (unfold checked_inst_rest in Hc; cbn beta iota zeta in Hc; discriminate Hc).
    exact (half_not_unchecked ge md (c_frame c) (c_mem c) l (Z.of_nat kk) Hmd Hinf Hr Hsc Hpt
             b kk q bd lo hi r al n1 a2 rest live out why Hfit Hfe Hb Hnth eq_refl Hc Hst).
Qed.

End Reuse.

(** ## The interpreter's runtime *)

Module InterpReuse := Reuse InterpRuntime.

(** [run_reuse_checked] for the [[interpreter]]'s runtime: in every state of
    a run of a checked module's function that starts ready, a frame that
    is not doomed runs no renew, renew over a hull or half check to
    `unchecked`. No hypothesis remains but the ready start. *)
Corollary interp_reuse_checked : forall md globals f xs fr m fuel s0 c s l i rest j why,
  let ge := mkGenv md globals InterpRuntime.free in
  checked_module md -> In (IFunc f) md -> call_frame f xs = Some fr -> InterpRuntime.ready s0 m ->
  InterpReuse.H.P.I.RM.mreachable ge (mkConfig fr [] m fuel, s0) (c, s) ->
  fr_doomed (c_frame c) = None -> fr_at (c_frame c) = Exec l (i :: rest) j -> reuse_form i ->
  inst_step ge (c_frame c) (c_mem c) i <> Some (IStop (Unchecked why)).
Proof.
  intros md globals f xs fr m fuel s0 c s l i rest j why ge Hmd Hin Hcf H0 Hreach Hd Ha Hi.
  exact (InterpReuse.run_reuse_checked ge md f xs fr m fuel s0 c s l i rest j why
           Hmd eq_refl eq_refl Hin Hcf H0 Hreach Hd Ha Hi).
Qed.
