(** Campaign 3's [[reuse|reuse forms]], part one: what a frame may read
    off the [[single definition|single definitions]] that
    [[dominance|dominate]] its point
    ([formal.md, Campaign 3](../../docs/formal.md#campaign-3-the-soundness-theorem);
    [rocq.md, Reading single definitions](../../docs/rocq.md#reading-single-definitions)).

    Single.v proves that every replayable single definition whose site
    dominates a frame's point [[replay|replays]]: the name still holds
    what its instruction made. This file turns that into the facts the
    reuse forms' rules need: [[offset interval|offset intervals]], the
    elements of a [[guard chain]], and the distance between two
    pointers. From them it proves the first reuse form, a raw access
    covered by the hull of two live facts, never [[unchecked]] along
    any run.

    ## Decisions

    | Decision | Why |
    |---|---|
    | "dominates the point" is the predicate Interval.v walks | it is closed under single-definition operands ([use_dominated]), and what dominates replays ([scope_holds]) |
    | Interval.v's hypothesis speaks of [iv_op] lets at an integer class | a check's proof or a float sum does not compute by `alu`; no derivation walks through one |
    | [guard_chain] and [pointer_distance] are rewritten by equations, never unfolded in a hypothesis | unfolding makes the kernel compare two 64-deep unfoldings, and `Qed` takes minutes |
    | a write through the hull needs some write check of the capability, not of the two bounding spans | `hull_covered/7` takes write rights from any span; a passed write check means the capability is not read-only |
    | the facts' pointers dominating the point is Invariant.v's ([live_dom]), not a hypothesis | inside a block it is [use_dominated]; over a block's entry it is [dom_meet] |
    | `Hull R` carries runs between two instances of `Machine R` | Persistence.v and Single.v each instantiate it, and `mstep` is an inductive, new in each instance | *)

From Stdlib Require Import String ZArith List Bool Lia Relations.
From Nanofil Require Import Term Maps Syntax Cfg Values Memory Runtime Ops Semantics Machine Validate
  Dominance Interval Sites Identity Coverage Walk Invariant Persistence Single Evidence.
Import ListNotations.
Open Scope Z_scope.

(** ## A replayed definition holds *)

(** A `let` n of an op o that intervals walk through ([iv_op]), at an
    integer [[class]] k, that steps and continues, computed its result
    from its operands as [let_holds] says, reading them in the frame
    where it ran (`inst_result/5`, `op_res/7`). *)
Lemma step_let_holds : forall ge fr m n k o args e1 l1 m1,
  iv_op o = true -> class_bits k <> None ->
  inst_step ge fr m (Let n k o args) = Some (IContinue e1 l1 m1) ->
  let_holds ge (fr_env fr) e1 n k o args.
Proof.
  intros ge fr m n k o args e1 l1 m1 Ho Hk H.
  assert (Hs : special_let o = false) by (destruct o; try discriminate Ho; reflexivity).
  rewrite (inst_step_let _ _ _ _ _ _ _ Hs) in H. cbv zeta in H.
  destruct (op_arg_classes o k) as [cls|] eqn:Ec; [|discriminate H].
  destruct (map2_option _ cls args) as [xs|] eqn:Ex; [|discriminate H].
  destruct (op_res o k xs m) as [[r m'| why | q kont]|] eqn:Er; try discriminate H.
  destruct r as [x|why|why]; simpl in H; try discriminate H. injection H as <- _ _.
  assert (Hn : lookup n (put n x (fr_env fr)) = Some x) by (rewrite lookup_put, name_eqb_refl; reflexivity).
  destruct k; try (exfalso; apply Hk; reflexivity); destruct o; try discriminate Ho;
    unfold op_res, op_res_int in Er; simpl in Er; cases Er; inversion Er; subst.
  all: unfold let_holds.
  all: first [ exists cls, xs, x; auto | idtac ].
  all: destruct t; try discriminate Ho.
  all: match goal with Hl : int_load_res _ _ _ _ _ = Some _ |- _ =>
         unfold int_load_res in Hl; cases Hl; inversion Hl; subst end.
  all: simpl in *; try discriminate.
  all: match goal with H0 : RVal _ = RVal _ |- _ => injection H0 as <- end; eauto.
Qed.

(** [let_holds] reads the defined name n only in the later environment,
    so it survives a change of environment that keeps n. *)
Lemma let_holds_name : forall ge e0 e e' n k o args,
  lookup n e' = lookup n e -> let_holds ge e0 e n k o args -> let_holds ge e0 e' n k o args.
Proof. intros ge e0 e e' n k o args E H. unfold let_holds in *. rewrite E. exact H. Qed.

(** ## Definitions that dominate a point *)

(** [[dominance|Dominance]] of sites composes: a site s that dominates
    index j of block d, where that site dominates index k of block l,
    dominates index k of block l. *)
Lemma site_dominates_trans : forall b0 rest doms l k d j s,
  block_intervals (b0 :: rest) = Some doms ->
  site_dominates doms l k (SAt d j) = true -> site_dominates doms d j s = true ->
  site_dominates doms l k s = true.
Proof.
  intros b0 rest doms l k d j s Hd H1 H2. destruct s as [| d' j']; [reflexivity|]. simpl in *.
  destruct (name_eqb d l) eqn:Edl; destruct (name_eqb d' d) eqn:Edd.
  - apply name_eqb_true in Edl, Edd. subst. rewrite name_eqb_refl.
    apply Z.ltb_lt in H1, H2. apply Z.ltb_lt. lia.
  - apply name_eqb_true in Edl. subst. rewrite Edd. exact H2.
  - apply name_eqb_true in Edd. subst. rewrite Edl. exact H1.
  - destruct (name_eqb d' l) eqn:Edl'; [exfalso|exact (dominates_trans _ _ _ Hd _ _ _ H2 H1)].
    apply name_eqb_true in Edl'. subst d'.
    rewrite (dom_antisym _ _ _ Hd _ _ H1 H2), name_eqb_refl in Edl. discriminate Edl.
Qed.

(** In a [checked_module] md, a single-definition operand a of the
    instruction i that defines n, where n [[dominance|dominates]] index k
    of a reachable block l, dominates it too: the [[validator]] requires
    an operand's definition to dominate its use. *)
Lemma operand_dominating : forall md f l k n i a,
  checked_module md -> In (IFunc f) md -> is_reachable (fn_doms f) l = true ->
  lookup n (single_definitions f) = Some (DInst i) -> dominating f l k n ->
  In a (inst_uses i) -> once_has (single_definitions f) a = true -> dominating f l k a.
Proof.
  intros md f l k n i a Hmd Hin Hr Hn (s & D & Hn' & Hpos & Hsd) Hu Ho.
  rewrite Hn in Hn'. injection Hn' as <-.
  destruct (func_facts _ _ Hmd Hin) as (b0 & rest & Hf & Hd & _ & Hdd).
  destruct (dinst_site _ _ _ _ Hpos) as (d & j & ->).
  destruct (position_inst _ _ _ _ _ Hpos) as (b & kk & Hb & Hl & Hk & -> & _).
  unfold once_has in Ho. destruct (lookup a (single_definitions f)) as [Da|] eqn:Ea; [|discriminate Ho].
  assert (Hrb : is_reachable (fn_doms f) (b_label b) = true).
  { rewrite Hl. simpl in Hsd. destruct (name_eqb d l) eqn:E; [apply name_eqb_true in E; subst; exact Hr|].
    exact (proj1 (dominates_reachable _ _ _ Hd _ _ Hsd)). }
  destruct (use_dominated _ _ _ _ _ _ _ Hdd Hb Hrb Hk Hu Ea) as (sa & Hsa & Hsda).
  exists sa, Da. split; [exact Ea|]. split; [exact Hsa|].
  rewrite Hl in Hsda. exact (site_dominates_trans _ _ _ _ _ _ _ _ Hd Hsd Hsda).
Qed.

(** Where every replayable single definition in scope replays
    ([scope_holds]), a replayable definition i of n that dominates the
    frame's point replays: [scope_holds] read at one name. *)
Lemma dominating_replays : forall ge fr m l k n i,
  scope_holds ge fr m -> point_site (fr_fn fr) (fr_at fr) = Some (l, k) ->
  lookup n (single_definitions (fr_fn fr)) = Some (DInst i) -> replayable i = true ->
  dominating (fr_fn fr) l k n -> replays ge (single_definitions (fr_fn fr)) (fr_env fr) m n i.
Proof.
  intros ge fr m l k n i Hs Hpt Hn Hrp (s & D & Hn' & Hpos & Hsd). rewrite Hn in Hn'. injection Hn' as <-.
  exact (Hs _ _ _ _ _ Hpt Hn Hrp Hpos Hsd).
Qed.

(** [dominating_replays] where only definitions that are not a
    `check_ahead` need to replay ([scope_plain]), for a definition that
    is not one ([ahead_free]). *)
Lemma plain_replays : forall ge fr m l k n i,
  scope_plain ge fr m -> point_site (fr_fn fr) (fr_at fr) = Some (l, k) ->
  lookup n (single_definitions (fr_fn fr)) = Some (DInst i) -> replayable i = true -> ahead_free i = true ->
  dominating (fr_fn fr) l k n -> replays ge (single_definitions (fr_fn fr)) (fr_env fr) m n i.
Proof.
  intros ge fr m l k n i Hs Hpt Hn Hrp Ha (s & D & Hn' & Hpos & Hsd). rewrite Hn in Hn'. injection Hn' as <-.
  exact (Hs _ _ _ _ _ Hpt Hn Hrp Hpos Hsd Ha).
Qed.

(** ## Offset intervals at a point *)

(** An [[offset interval]] from lo to hi that the [[validator]] derives
    for a value v at class k' ([iv], `offset_interval/8`) holds of the
    value the frame reads ([in_iv]), where v's name dominates the
    frame's point and every single definition in scope but a
    `check_ahead` replays. *)
Theorem interval_at : forall ge md fr m l k v k' lo hi,
  checked_module md -> In (IFunc (fr_fn fr)) md -> is_reachable (fn_doms (fr_fn fr)) l = true ->
  scope_plain ge fr m -> point_site (fr_fn fr) (fr_at fr) = Some (l, k) ->
  iv (single_definitions (fr_fn fr)) v k' lo hi -> (forall n, v = Tmp n -> dominating (fr_fn fr) l k n) ->
  in_iv ge (fr_env fr) k' v lo hi.
Proof.
  intros ge md fr m l k v k' lo hi Hmd Hin Hr Hs Hpt Hiv Hv.
  refine (iv_sound _ ge (fr_env fr) (dominating (fr_fn fr) l k) _ _ _ _ _ Hiv Hv).
  intros n k0 o args (n' & Hn & Ene) Hop Hk Hdom.
  apply name_eqb_true in Ene. subst n'.
  assert (Hrp : replayable (Let n k0 o args) = true) by (destruct o; try discriminate Hop; reflexivity).
  assert (Haf : ahead_free (Let n k0 o args) = true) by (destruct o; try discriminate Hop; reflexivity).
  destruct (plain_replays _ _ _ _ _ _ _ Hs Hpt Hn Hrp Haf Hdom) as (fr0 & m0 & e1 & l1 & m1 & Hst & Hn1 & Ha & _).
  exists (fr_env fr0). split.
  - exact (let_holds_name _ _ _ _ _ _ _ _ (eq_sym Hn1) (step_let_holds _ _ _ _ _ _ _ _ _ _ Hop Hk Hst)).
  - intros a Hin' Ho. split.
    + exact (operand_dominating _ _ _ _ _ _ _ Hmd Hin Hr Hn Hdom (value_temps_in _ _ Hin') Ho).
    + exact (Ha _ (value_temps_in _ _ Hin') Ho).
Qed.

(** ## The hull of two checks *)

(** An access check that passes ([cap_access_res]) is at an address
    aligned to its alignment al. *)
Lemma cap_access_aligned : forall c rs a size r al,
  cap_access_res c rs a size r al = Some ok -> a mod al = 0.
Proof.
  unfold cap_access_res. intros c rs a size r al H.
  destruct c as [| base | base | f | n]; try discriminate H;
    destruct (object_region base rs) as [reg|]; try discriminate H;
    destruct ((base <=? a) && (a + size <=? r_end reg)); try discriminate H;
    injection H as H.
  - exact (aligned_res_mod _ _ H).
  - destruct r; [exact (aligned_res_mod _ _ H) | discriminate H].
Qed.

(** Every [[raw access|raw access's]] alignment divides 2^64, so an
    address modulo 2^64 is aligned as the address is. *)
Lemma access_align_divides : forall x, (snd (access_size_align x) | 2 ^ 64).
Proof.
  intros [[| | | | t] | w |]; try destruct w; simpl;
    first [ exists (2 ^ 64); reflexivity | exists (2 ^ 61); reflexivity ].
Qed.

(** An access between two passed checks of one [[capability]] c, at
    addresses of one pointer A that are near offsets apart, passes too
    (the arithmetic of `hull_covered/7`). The first
    check's span ends at or above -2^62 and starts at or below the
    access; the second's starts at or below 2^62 and ends at or above
    it. A read needs nothing more; a write needs some write check of
    the capability to have passed.

    The two checks compare addresses taken modulo 2^64. They are A+l1
    and A+l2 exactly, not merely congruent to them, only because the
    object ends at or below 2^48 ([objects_fit]): addresses inside it
    that are congruent and less than 2^63 apart are equal. *)
Lemma cap_access_hull : forall c rs A l1 s1 r1 al1 l2 s2 r2 al2 off size need aa,
  objects_fit rs ->
  cap_access_res c rs (raw_address A l1) s1 r1 al1 = Some ok ->
  cap_access_res c rs (raw_address A l2) s2 r2 al2 = Some ok ->
  - 2 ^ 62 <= l1 + s1 -> l2 <= 2 ^ 62 ->
  l1 <= off -> off + size <= l2 + s2 -> 0 < size ->
  raw_address A off mod aa = 0 ->
  (need = Read \/ exists a3 s3 al3, cap_access_res c rs a3 s3 Write al3 = Some ok) ->
  cap_access_res c rs (raw_address A off) size need aa = Some ok.
Proof.
  intros c rs A l1 s1 r1 al1 l2 s2 r2 al2 off size need aa Hfit H1 H2 Hh1 Hl2 Hoff Hend Hs Hal Hr.
  assert (Hpos : forall a, 0 <= raw_address A a < 2 ^ 64) by (intros a; apply Z.mod_pos_bound; lia).
  assert (Hdiv : forall a, A + a = 2 ^ 64 * ((A + a) / 2 ^ 64) + raw_address A a)
    by (intros a; apply Z.div_mod; lia).
  unfold cap_access_res in *.
  destruct c as [| base | base | f | n]; try discriminate H1.
  all: destruct (object_region base rs) as [reg|] eqn:E; try discriminate H1.
  all: pose proof (Hfit _ _ E) as Hend';
    destruct ((base <=? raw_address A l1) && (raw_address A l1 + s1 <=? r_end reg)) eqn:B1; [|discriminate H1];
    destruct ((base <=? raw_address A l2) && (raw_address A l2 + s2 <=? r_end reg)) eqn:B2; [|discriminate H2];
    apply andb_true_iff in B1 as [B1 B1']; apply andb_true_iff in B2 as [B2 B2'];
    apply Z.leb_le in B1, B1', B2, B2'.
  all: pose proof (Hpos l1); pose proof (Hpos l2); pose proof (Hpos off);
    pose proof (Hdiv l1); pose proof (Hdiv l2); pose proof (Hdiv off).
  all: replace ((base <=? raw_address A off) && (raw_address A off + size <=? r_end reg)) with true
         by (symmetry; apply andb_true_iff; split; apply Z.leb_le; lia).
  - f_equal. apply aligned_res_ok. exact Hal.
  - destruct need; simpl; [f_equal; apply aligned_res_ok; exact Hal|].
    exfalso. destruct Hr as [Hr | (a3 & s3 & al3 & Hw)]; [discriminate Hr|].
    destruct (_ && _); discriminate Hw.
Qed.

(** ## Guard chains *)

(** What [first_some] finds is f of some element of the list. *)
Lemma first_some_in : forall (X Y : Type) (f : X -> option Y) xs y,
  first_some f xs = Some y -> exists x, In x xs /\ f x = Some y.
Proof.
  intros X Y f xs y. induction xs as [|x xs IH]; simpl; intros H; [discriminate H|].
  destruct (f x) eqn:E; [injection H as <-; eauto | destruct (IH H) as (x' & Hin & Hx); eauto].
Qed.

(** A [[flight]] that is the single definition of y defines y. *)
Lemma flight_def_name : forall f y d o args lw,
  lookup y (single_definitions f) = Some (DInst (Flight d o args lw)) -> d = y.
Proof.
  intros f y d o args lw H. destruct (once_position _ _ _ H) as (s & Hpos & _).
  destruct (dinst_site _ _ _ _ Hpos) as (dd & j & ->).
  destruct (position_inst _ _ _ _ _ Hpos) as (_ & _ & _ & _ & _ & _ & Hy).
  simpl in Hy. destruct Hy as [-> | []]. reflexivity.
Qed.

(** A value v reads alike ([value_x]) in two environments e0 and e that
    agree on its name. *)
Lemma value_x_agree : forall ge e0 e k v,
  (forall y, v = Tmp y -> lookup y e0 = lookup y e) -> value_x ge e0 k v = value_x ge e k v.
Proof. intros ge e0 e k v H. destruct v as [y | c | g]; simpl; [rewrite (H y eq_refl) | |]; reflexivity. Qed.

(** What a [[guard chain]] element (b, lo, hi) says of a pointer pp0:
    the value b reads in the environment e as a pointer with pp0's
    [[capability]], and pp0's address is b's plus some x between lo and
    hi, modulo 2^64. *)
Definition offset_rel (ge : genv) (e : env) (pp0 : ptr) (b : value) (lo hi : Z) : Prop :=
  exists pb x, value_x ge e P b = Some (WPtr pb) /\ ptr_cap pb = ptr_cap pp0 /\ lo <= x <= hi /\
    ptr_addr pp0 mod 2 ^ 64 = (ptr_addr pb + x) mod 2 ^ 64.

(** A value v is not a name defined more than once: a constant, a
    global, or a [[single definition|single-definition]] name in once. *)
Definition stable (once : list (name * def)) (v : value) : Prop := forall y, v = Tmp y -> once_has once y = true.

(** The address arithmetic of an add [[flight]]: shifting by z and then
    by xo is shifting by xo + z, modulo 2^64. *)
Lemma mod_shift_add : forall a z xo,
  ((a mod 2 ^ 64 + z mod 2 ^ 64) mod 2 ^ 64 + xo) mod 2 ^ 64 = (a + (xo + z)) mod 2 ^ 64.
Proof. intros a z xo. rewrite <- Z.add_mod, Z.add_mod_idemp_l by lia. f_equal. lia. Qed.

(** The same for a sub flight: shifting by -z and then xo. *)
Lemma mod_shift_sub : forall a z xo,
  ((a mod 2 ^ 64 - z mod 2 ^ 64) mod 2 ^ 64 + xo) mod 2 ^ 64 = (a + (xo - z)) mod 2 ^ 64.
Proof. intros a z xo. rewrite <- Zminus_mod, Z.add_mod_idemp_l by lia. f_equal. lia. Qed.

(** The same for a copy flight, whose shift z is 0 modulo 2^64. *)
Lemma mod_shift_zero : forall a z xo, z mod 2 ^ 64 = 0 ->
  (a mod 2 ^ 64 + xo) mod 2 ^ 64 = (a + (xo + z)) mod 2 ^ 64.
Proof.
  intros a z xo Hz. replace (a + (xo + z)) with ((a + xo) + z) by lia.
  rewrite (Z.add_mod (a + xo) z), Hz, Z.add_0_r, Z.mod_mod, Z.add_mod_idemp_l by lia. reflexivity.
Qed.

(** Lemmas for a frame fr of a [checked_module] md, in memory m, at
    index k of a reachable block l, where every
    [[single definition]] in scope but a `check_ahead`
    [[replay|replays]] ([scope_plain]). *)
Section Chain.

Variables (ge : genv) (md : module) (fr : frame) (m : Memory.mem) (l : name) (k : Z).
Hypothesis Hmd : checked_module md.
Hypothesis Hin : In (IFunc (fr_fn fr)) md.
Hypothesis Hr : is_reachable (fn_doms (fr_fn fr)) l = true.
Hypothesis Hs : scope_plain ge fr m.
Hypothesis Hpt : point_site (fr_fn fr) (fr_at fr) = Some (l, k).

(** Every [stable] element of a [[guard chain]] walked from p with fuel
    steps (`guard_chain/3`) holds of the pointer pp0 ([offset_rel]),
    where p's single definition dominates the point and p's own element
    holds. The induction behind [guard_chain_sound]. *)
Lemma chain_go_sound : forall fuel p lo hi pp0,
  (forall y, p = Tmp y -> once_has (single_definitions (fr_fn fr)) y = true -> dominating (fr_fn fr) l k y) ->
  (stable (single_definitions (fr_fn fr)) p -> offset_rel ge (fr_env fr) pp0 p lo hi) ->
  forall b blo bhi, In (b, (blo, bhi)) (guard_chain_go (single_definitions (fr_fn fr)) fuel p lo hi) ->
  stable (single_definitions (fr_fn fr)) b -> offset_rel ge (fr_env fr) pp0 b blo bhi.
Proof.
  induction fuel as [|fuel IH]; intros p lo hi pp0 Hdom Hrel b blo bhi Hb Hst; simpl in Hb.
  - destruct Hb as [E | []]. injection E as -> -> ->. exact (Hrel Hst).
  - destruct Hb as [E | Hb]; [injection E as -> -> ->; exact (Hrel Hst)|].
    destruct p as [x | c | g]; try contradiction.
    destruct (lookup x (single_definitions (fr_fn fr))) as [[| ph | i]|] eqn:Ex; try contradiction.
    destruct i as [ | d o args lw | | | | | | ]; try contradiction.
    destruct lw as [| b']; try contradiction.
    destruct (flight_term o args b') as [[ov sign]|] eqn:Ef; [|contradiction].
    destruct (offset_interval _ ov L) as [[olo ohi]|] eqn:Eo; [|contradiction].
    pose proof (flight_def_name _ _ _ _ _ _ Ex) as ->.
    assert (Hox : once_has (single_definitions (fr_fn fr)) x = true) by (unfold once_has; rewrite Ex; reflexivity).
    pose proof (Hdom x eq_refl Hox) as Hdx.
    destruct (Hrel ltac:(intros y E; injection E as <-; exact Hox)) as (pp & xo & Hpp & Hcap & Hxo & Haddr).
    destruct (plain_replays _ _ _ _ _ _ _ Hs Hpt Ex eq_refl eq_refl Hdx) as (fr0 & m0 & e1 & l1 & m1 & Hst' & Hx1 & Hops & _).
    assert (Hop : forall y, In (Tmp y) (map flight_arg_value args ++ [b']) ->
                   once_has (single_definitions (fr_fn fr)) y = true ->
                   dominating (fr_fn fr) l k y /\ lookup y (fr_env fr0) = lookup y (fr_env fr)).
    { intros y Hy Ho. split.
      - exact (operand_dominating _ _ _ _ _ _ _ Hmd Hin Hr Ex Hdx (value_temps_in _ _ Hy) Ho).
      - exact (Hops _ (value_temps_in _ _ Hy) Ho). }
    assert (Hov : (forall y, ov = Tmp y -> In (Tmp y) (map flight_arg_value args ++ [b'])) ->
                  exists z, olo <= z <= ohi /\ value_x ge (fr_env fr0) L ov = Some (WInt (z mod 2 ^ 64))).
    { intros Hin'. pose proof (offset_interval_iv _ _ _ _ _ Eo) as Hiv.
      assert (Hdv : forall y, ov = Tmp y -> dominating (fr_fn fr) l k y /\ lookup y (fr_env fr0) = lookup y (fr_env fr))
        by (intros y E; exact (Hop y (Hin' y E) (iv_once _ _ _ _ _ Hiv _ E))).
      destruct (interval_at _ _ _ _ _ _ _ _ _ _ Hmd Hin Hr Hs Hpt Hiv (fun y E => proj1 (Hdv y E)))
        as (bits & u' & z & Hbits & Hu & Hz & ->).
      injection Hbits as <-. exists z. split; [exact Hz|]. rewrite <- Hu. apply value_x_agree.
      intros y E. exact (proj2 (Hdv y E)). }
    assert (Hdb : forall y, b' = Tmp y -> once_has (single_definitions (fr_fn fr)) y = true ->
                   dominating (fr_fn fr) l k y /\ lookup y (fr_env fr0) = lookup y (fr_env fr))
      by (intros y E Ho; subst b'; apply Hop; [apply in_or_app; right; left; reflexivity | exact Ho]).
    simpl in Hst'. unfold flight_cap in Hst'.
    unfold flight_term in Ef. cases Ef; injection Ef as <- <-;
      match goal with E : value_eqb _ _ = true |- _ => apply value_eqb_eq in E; subst end.
    all: simpl in Hst'.
    all: destruct (value_x ge (fr_env fr0) P b') as [[u0 | pb0 | c0 s0]|] eqn:Eb; simpl in Hst'; try discriminate Hst'.
    all: try (match type of Hst' with context [value_x _ _ L ?w] =>
                destruct (value_x ge (fr_env fr0) L w) as [[u | | ]|] eqn:Ev end;
              simpl in Hst'; try discriminate Hst').
    all: injection Hst' as <- _ _.
    all: rewrite lookup_put, name_eqb_refl in Hx1.
    all: simpl in Hpp; rewrite <- Hx1 in Hpp; simpl in Hpp; injection Hpp as <-; simpl in Hcap.
    all: change (Z.pow_pos 2 64) with (2 ^ 64) in *.
    all: assert (Hb' : stable (single_definitions (fr_fn fr)) b' -> value_x ge (fr_env fr) P b' = Some (WPtr pb0))
           by (intros Hsb; rewrite <- Eb; symmetry; apply value_x_agree; intros y E;
               exact (proj2 (Hdb y E (Hsb y E)))).
    all: simpl in Hb.
    all: refine (IH b' _ _ pp0 (fun y E Ho => proj1 (Hdb y E Ho)) _ b blo bhi Hb Hst); intros Hsb.
    all: destruct (Hov ltac:(intros y E; first [discriminate E | subst; simpl; auto 10])) as (z & Hz & Ez); injection Ez as Ez.
    + exists pb0, (xo + z). split; [exact (Hb' Hsb)|]. split; [exact Hcap|]. split; [lia|].
      rewrite Haddr. simpl. change (Z.pow_pos 2 64) with (2 ^ 64) in *. rewrite Ez. apply mod_shift_add.
    + exists pb0, (xo - z). split; [exact (Hb' Hsb)|]. split; [exact Hcap|]. split; [lia|].
      rewrite Haddr. simpl. rewrite Ez. apply mod_shift_sub.
    + exists pb0, (xo + z). split; [exact (Hb' Hsb)|]. split; [exact Hcap|]. split; [lia|].
      rewrite Haddr. simpl. apply mod_shift_zero. change (Z.pow_pos 2 64) with (2 ^ 64) in *. rewrite <- Ez. reflexivity.
Qed.

(** [guard_chain] as an equation. Unfolding it in a hypothesis instead
    makes the kernel compare two unfoldings of [guard_chain_go], which
    recurses twice per level, 64 levels deep. *)
Lemma guard_chain_eq : forall once p, guard_chain once p = guard_chain_go once 64 p 0 0.
Proof. intros once p. reflexivity. Qed.

(** Each [stable] element of the [[guard chain]] of a value p
    (`guard_chain/3`) holds of the pointer pp that p reads
    ([offset_rel]), where p's single definition dominates the point. *)
Lemma guard_chain_sound : forall p pp b blo bhi,
  value_x ge (fr_env fr) P p = Some (WPtr pp) ->
  (forall y, p = Tmp y -> once_has (single_definitions (fr_fn fr)) y = true -> dominating (fr_fn fr) l k y) ->
  In (b, (blo, bhi)) (guard_chain (single_definitions (fr_fn fr)) p) ->
  stable (single_definitions (fr_fn fr)) b -> offset_rel ge (fr_env fr) pp b blo bhi.
Proof.
  intros p pp b blo bhi Hp Hdom Hb Hst. rewrite guard_chain_eq in Hb.
  refine (chain_go_sound 64 p 0 0 pp Hdom _ b blo bhi Hb Hst).
  intros _. exists pp, 0. split; [exact Hp|]. split; [reflexivity|]. split; [lia|].
  rewrite Z.add_0_r. reflexivity.
Qed.

(** [pointer_distance] as an equation, for the same reason as
    [guard_chain_eq]. *)
Lemma pointer_distance_eq : forall once p p1,
  pointer_distance once p p1 =
    first_some (fun e =>
                  match exact_base once e with
                  | Some (n, k) =>
                      first_some (fun e1 => match e1 with
                                            | (Tmp n1, (k1, k1')) =>
                                                if name_eqb n1 n && (k1 =? k1') then Some (k - k1) else None
                                            | _ => None
                                            end) (guard_chain once p1)
                  | None => None
                  end) (guard_chain once p).
Proof. intros once p p1. reflexivity. Qed.

(** Two values p and p1 that read as pointers pp and pp1, whose
    [[guard chain|guard chains]] share an exact base d apart
    (`pointer_distance/4`), have one [[capability]], and addresses d
    apart, modulo 2^64, where their single definitions dominate the
    point. The reuse forms use it to give a renewed pointer its
    source's capability. *)
Theorem pointer_distance_sound : forall p p1 pp pp1 d,
  value_x ge (fr_env fr) P p = Some (WPtr pp) -> value_x ge (fr_env fr) P p1 = Some (WPtr pp1) ->
  (forall y, p = Tmp y -> once_has (single_definitions (fr_fn fr)) y = true -> dominating (fr_fn fr) l k y) ->
  (forall y, p1 = Tmp y -> once_has (single_definitions (fr_fn fr)) y = true -> dominating (fr_fn fr) l k y) ->
  pointer_distance (single_definitions (fr_fn fr)) p p1 = Some d ->
  ptr_cap pp = ptr_cap pp1 /\ ptr_addr pp mod 2 ^ 64 = (ptr_addr pp1 + d) mod 2 ^ 64.
Proof.
  intros p p1 pp pp1 d Hp Hp1 Hd Hd1 H. rewrite pointer_distance_eq in H.
  destruct (first_some_in _ _ _ _ _ H) as (el & Hel & Hf).
  destruct el as [[n0 | c0 | g0] [k0 k0']]; unfold exact_base in Hf; try discriminate Hf.
  destruct ((k0 =? k0') && once_has (single_definitions (fr_fn fr)) n0) eqn:E0; [|discriminate Hf].
  apply andb_true_iff in E0 as [Ek0 Ho]. apply Z.eqb_eq in Ek0. subst k0'.
  destruct (first_some_in _ _ _ _ _ Hf) as (el1 & Hel1 & Hf1).
  destruct el1 as [[n1 | c1 | g1] [k1 k1']]; try discriminate Hf1.
  destruct (name_eqb n1 n0 && (k1 =? k1')) eqn:E1; [|discriminate Hf1]. injection Hf1 as <-.
  apply andb_true_iff in E1 as [En Ek]. apply name_eqb_true in En. apply Z.eqb_eq in Ek. subst n1 k1'.
  assert (Hst : stable (single_definitions (fr_fn fr)) (Tmp n0)) by (intros y E; injection E as <-; exact Ho).
  destruct (guard_chain_sound _ _ _ _ _ Hp Hd Hel Hst) as (pb & x & Hpb & Hc & Hx & Ha).
  destruct (guard_chain_sound _ _ _ _ _ Hp1 Hd1 Hel1 Hst) as (pb' & x1 & Hpb' & Hc1 & Hx1 & Ha1).
  rewrite Hpb in Hpb'. injection Hpb' as <-.
  assert (x = k0) by lia. assert (x1 = k1) by lia. subst x x1.
  split; [congruence|].
  rewrite Ha, <- (Z.add_mod_idemp_l (ptr_addr pp1)), Ha1, Z.add_mod_idemp_l by lia. f_equal. lia.
Qed.

(** ## The hull of a pointer's live facts *)

(** Each span from l1 to h1 that `hull_covered/7` reads off a
    [[live fact]] is a check that passed, of the capability of the
    access pointer pp, at its address plus the span's bounds, where the
    live facts hold ([facts_hold]) and their pointers dominate the
    point. The fact's pointer and the access's are a known distance
    apart ([pointer_distance_sound]). *)
Lemma hull_span_passes : forall live p pp l1 h1 r1,
  facts_hold ge m (fr_env fr) live ->
  (forall fb y, In fb live -> f_p fb = Tmp y ->
     once_has (single_definitions (fr_fn fr)) y = true -> dominating (fr_fn fr) l k y) ->
  value_x ge (fr_env fr) P p = Some (WPtr pp) ->
  (forall y, p = Tmp y -> once_has (single_definitions (fr_fn fr)) y = true -> dominating (fr_fn fr) l k y) ->
  In (l1, h1, r1) (flat_map (fun f =>
                               match pointer_distance (single_definitions (fr_fn fr)) (f_p f) p with
                               | Some d =>
                                   let l1 := f_lo f + d in
                                   let h1 := f_hi f + d in
                                   if near_offset d && near_offset l1 && near_offset h1
                                   then [(l1, h1, f_r f)] else []
                               | None => []
                               end) live) ->
  near_offset l1 = true /\ near_offset h1 = true /\
  exists al1, access_res m (raw_address (ptr_addr pp) l1) (ptr_cap pp) (h1 - l1) r1 al1 = Some ok.
Proof.
  intros live p pp l1 h1 r1 Hl Hdom Hp Hdp Hsp.
  apply in_flat_map in Hsp as (f & Hf & Hsp).
  destruct (pointer_distance (single_definitions (fr_fn fr)) (f_p f) p) as [d|] eqn:Ed; [|contradiction].
  cbv zeta in Hsp.
  destruct (near_offset d && near_offset (f_lo f + d) && near_offset (f_hi f + d)) eqn:En; [|contradiction].
  destruct Hsp as [E | []]. injection E as <- <- <-.
  apply andb_true_iff in En as [En Eh]. apply andb_true_iff in En as [_ El].
  split; [exact El|]. split; [exact Eh|].
  destruct (Hl f Hf) as (pf & _ & Hpf & Hc).
  destruct (pointer_distance_sound _ _ _ _ _ Hpf Hp (fun y => Hdom f y Hf) Hdp Ed) as [Hcap Haddr].
  exists (f_al f). unfold check_passes in Hc.
  replace (f_hi f + d - (f_lo f + d)) with (f_hi f - f_lo f) by lia.
  replace (raw_address (ptr_addr pp) (f_lo f + d)) with (raw_address (ptr_addr pf) (f_lo f)).
  - rewrite <- Hcap. exact Hc.
  - unfold raw_address. rewrite <- Z.add_mod_idemp_l, Haddr, Z.add_mod_idemp_l by lia. f_equal. lia.
Qed.

(** A [[raw access]] i through the proof q that the pass accepts by
    `hull_covered/7` does not step to [[unchecked]], where memory lies
    in the address space, the [[live fact|live facts]] hold and their
    pointers' single definitions dominate the point. The span
    starting at or below the access and the span ending at or above it
    are checks of one capability that passed ([hull_span_passes]), so
    the access's own check passes ([cap_access_hull]). *)
Theorem hull_access_not_unchecked : forall i q fa live why,
  objects_fit (m_regions m) ->
  facts_hold ge m (fr_env fr) live ->
  (forall fb y, In fb live -> f_p fb = Tmp y ->
     once_has (single_definitions (fr_fn fr)) y = true -> dominating (fr_fn fr) l k y) ->
  fact_of q live = Some fa ->
  hull_covered i q (f_p fa) (f_lo fa) (f_al fa) live (single_definitions (fr_fn fr)) = true ->
  inst_step ge fr m i <> Some (IStop (Unchecked why)).
Proof.
  intros i q fa live why Hfit Hl Hdom Hf H.
  destruct (fact_of_in _ _ _ Hf) as [Hfa Hq].
  destruct (Hl fa Hfa) as (pp & Eq & Hp & Hc). rewrite Hq in Eq.
  pose proof (fun y => Hdom fa y Hfa) as Hdp.
  unfold hull_covered in H.
  destruct (raw_access i) as [[[[q' x] off] need]|] eqn:Ei; [|discriminate H].
  pose proof (access_size_align_pos x) as [Hsz Haa]. pose proof (access_align_divides x) as Hdv.
  destruct (access_size_align x) as [size aa] eqn:Ex. simpl in Hsz, Haa, Hdv. cbv zeta in H.
  repeat rewrite andb_true_iff in H.
  destruct H as (((((((Hq' & Hal) & Hoa) & _) & _) & H1) & H2) & Hneed).
  apply name_eqb_true in Hq'. subst q'.
  apply Z.eqb_eq in Hal. apply Z.eqb_eq in Hoa.
  apply existsb_exists in H1 as ([[l1 h1] r1] & Hs1 & Hl1). apply Z.leb_le in Hl1.
  apply existsb_exists in H2 as ([[l2 h2] r2] & Hs2 & Hh2). apply Z.leb_le in Hh2.
  destruct (hull_span_passes _ _ _ _ _ _ Hl Hdom Hp Hdp Hs1) as (_ & Hn1 & al1 & Hc1).
  destruct (hull_span_passes _ _ _ _ _ _ Hl Hdom Hp Hdp Hs2) as (Hn2 & _ & al2 & Hc2).
  unfold near_offset in Hn1, Hn2. apply andb_true_iff in Hn1 as [Hn1 _], Hn2 as [_ Hn2].
  apply Z.leb_le in Hn1, Hn2.
  apply (access_ok_not_unchecked ge fr m i q x off need pp why Ei Eq). rewrite Ex. simpl.
  unfold access_res in *.
  refine (cap_access_hull _ _ _ l1 (h1 - l1) r1 al1 l2 (h2 - l2) r2 al2 _ _ _ _
            Hfit Hc1 Hc2 _ Hn2 Hl1 _ Hsz _ _); [lia | lia | |].
  - (* The access is aligned: the fact's check was, at an alignment aa divides. *)
    unfold check_passes, access_res in Hc. apply cap_access_aligned in Hc.
    unfold raw_address in *.
    rewrite <- (Znumtheory.Zmod_div_mod aa (2 ^ 64)) by (auto; lia).
    replace (ptr_addr pp + off) with ((ptr_addr pp + f_lo fa) + (off - f_lo fa)) by lia.
    apply aligned_add; [exact Haa| |exact Hoa].
    rewrite (Znumtheory.Zmod_div_mod aa (2 ^ 64)) by (auto; lia).
    exact (aligned_divisor _ _ _ Haa Hc Hal).
  - (* The rights: a read, or a write some span's write check allows. *)
    destruct need; [left; reflexivity | right].
    apply existsb_exists in Hneed as ([[l3 h3] r3] & Hs3 & Hr3).
    destruct r3; [discriminate Hr3|].
    destruct (hull_span_passes _ _ _ _ _ _ Hl Hdom Hp Hdp Hs3) as (_ & _ & al3 & Hc3).
    eauto.
Qed.

End Chain.



(** ## No unchecked access through the hull, along every run *)

(** The frame lemmas carried along every [[run]] of the [[machine]] of a
    [[runtime]] R. It joins Persistence.v's invariant, which says the
    hull's facts hold and dominate the point, with Single.v's, which
    says the single definitions there replay. Each instantiates `Machine R` on
    its own, and an instance's `mstep` is an inductive of its own, so a
    run of one is carried over to the other ([mreachable_same]). *)
Module Hull (R : Runtime).

Module P := Persistence R.
Module S := Single R.

(** A step of Persistence.v's machine instance is a step of Single.v's. *)
Lemma mstep_same : forall ge st st', P.I.RM.mstep ge st st' -> S.ID.RM.mstep ge st st'.
Proof. intros ge st st' H. destruct H; econstructor; eassumption. Qed.

(** A run of Persistence.v's machine instance is a run of Single.v's,
    so both invariants hold of every state it reaches. *)
Lemma mreachable_same : forall ge st st', P.I.RM.mreachable ge st st' -> S.ID.RM.mreachable ge st st'.
Proof.
  intros ge st st' H. induction H as [st st' H | st | st1 st2 st3 _ IH1 _ IH2].
  - apply rt_step. exact (mstep_same _ _ _ H).
  - apply rt_refl.
  - exact (rt_trans _ _ _ _ _ IH1 IH2).
Qed.

(** In every state c a [[run]] reaches from a call of a function f of a
    [checked_module] md, started in a memory where the runtime is
    [[ready]], a frame that is not [[doomed]] runs no [[raw access]], and
    no raw call, to an [[unchecked]] outcome, `hull_covered/7` included.
    Every runtime spares the pass's facts at [[poll|safepoints]]
    ([spares_any]; see
    [The evidence invariant over runs](../../docs/rocq.md#the-evidence-invariant-over-runs)). *)
Theorem run_access_checked : forall ge md f xs fr m fuel s0 c s l i rest j why,
  checked_module md -> ge_module ge = md -> ge_free ge = R.free ->
  In (IFunc f) md -> call_frame f xs = Some fr -> R.ready s0 m ->
  P.I.RM.mreachable ge (mkConfig fr [] m fuel, s0) (c, s) ->
  fr_doomed (c_frame c) = None -> fr_at (c_frame c) = Exec l (i :: rest) j ->
  (raw_access i <> None \/ exists r cl args, i = RawCall r cl args) ->
  inst_step ge (c_frame c) (c_mem c) i <> Some (IStop (Unchecked why)).
Proof.
  intros ge md f xs fr m fuel s0 c s l i rest j why Hmd Hge Hfree Hin Hcf H0 Hreach Hd Ha Hi.
  destruct (P.run_access_not_unchecked _ _ _ _ _ _ _ _ _ _ _ _ _ _ why Hmd Hge Hfree Hin Hcf H0 Hreach Hd Ha Hi)
    as [Hn | (b & k & live & fa & q & Hb & Hk & Hl & Hdom & Hfa & Hh)]; [exact Hn|].
  pose proof (S.run_sinv _ _ _ _ _ _ _ _ _ Hmd Hge Hfree Hin Hcf H0 (mreachable_same _ _ _ Hreach))
    as [[Hsh Hsc] _].
  simpl in Hsh, Hsc. destruct Hsc as [Hsc | Hsc]; [congruence|].
  destruct Hsh as [Hinf Hsh]. rewrite Ha in Hsh. destruct Hsh as [Hr _].
  pose proof (P.I.RM.mreachable_ready _ _ _ Hfree Hreach H0) as Hready.
  pose proof (R.address_space _ _ Hready) as Hfit.
  destruct (skipn_cons _ _ _ _ _ (eq_sym Hk)) as (_ & _ & Hlen).
  assert (Hpt : point_site (fr_fn (c_frame c)) (fr_at (c_frame c)) = Some (l, Z.of_nat k))
    by (rewrite Ha, Hk; apply point_site_exec; [exact Hb | lia]).
  exact (hull_access_not_unchecked ge md (c_frame c) (c_mem c) l (Z.of_nat k) Hmd Hinf Hr (scope_plain_of _ _ _ Hsc) Hpt
           i q fa live why Hfit Hl (Hdom Hr) Hfa Hh).
Qed.

End Hull.

(** ## The interpreter's runtime *)

Module InterpHull := Hull InterpRuntime.

(** [run_access_checked] for the [[interpreter]]'s runtime: in every state of
    a run of a checked module's function that starts ready, a frame that
    is not doomed runs no raw access or raw call to `unchecked`. No
    hypothesis remains but the ready start. *)
Corollary interp_access_checked : forall md globals f xs fr m fuel s0 c s l i rest j why,
  let ge := mkGenv md globals InterpRuntime.free in
  checked_module md -> In (IFunc f) md -> call_frame f xs = Some fr -> InterpRuntime.ready s0 m ->
  InterpHull.P.I.RM.mreachable ge (mkConfig fr [] m fuel, s0) (c, s) ->
  fr_doomed (c_frame c) = None -> fr_at (c_frame c) = Exec l (i :: rest) j ->
  (raw_access i <> None \/ exists r cl args, i = RawCall r cl args) ->
  inst_step ge (c_frame c) (c_mem c) i <> Some (IStop (Unchecked why)).
Proof.
  intros md globals f xs fr m fuel s0 c s l i rest j why ge Hmd Hin Hcf H0 Hreach Hd Ha Hi.
  exact (InterpHull.run_access_checked ge md f xs fr m fuel s0 c s l i rest j why
           Hmd eq_refl eq_refl Hin Hcf H0 Hreach Hd Ha Hi).
Qed.
