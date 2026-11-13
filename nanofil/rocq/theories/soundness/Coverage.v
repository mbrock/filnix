(** When a compiler hoists or merges bounds checks in C, a later load,
    store, or atomic operation runs as a [[raw access]] without
    repeating the check. In the Fil-C machine model, every raw access
    still performs its own bounds, [[rights]], and alignment check at
    runtime, and stops the machine as [[unchecked]] if that check would
    [[trap]]. This module proves that if an earlier [[check]] already
    verified a byte range enclosing the raw access, with compatible
    rights and alignment, then the raw access cannot produce
    [Unchecked].

    Pointer addresses wrap modulo 2^64 while object bounds are unbounded
    integers. Containment in a checked range therefore guarantees
    containment in the object only when every live object ends below
    2^64, which holds in every run that starts [[ready]]. Proving that an
    earlier check still passes in the later memory where the raw access
    runs belongs to the [[evidence]] invariant. *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Machine Validate.
Import ListNotations.
Open Scope Z_scope.

(** ## The hypotheses

    The coverage lemma assumes that an earlier check on a pointer
    succeeded in memory. We package that assumption as [check_passes]
    so the arithmetic and instruction lemmas can refer to it cleanly. *)

(** A check instruction verifies a byte range around a pointer with the
    given rights and alignment. Predicate [check_passes] states that
    this [[access]] check succeeds in memory m. *)
Definition check_passes (m : Memory.mem) (p : ptr) (lo hi : Z) (r : rights) (al : Z) : Prop :=
  access_res m (raw_address (ptr_addr p) lo) (ptr_cap p) (hi - lo) r al = Some ok.

(** ## Arithmetic

    Before reasoning about capabilities or instructions, we establish
    two facts about address arithmetic and alignment. First, alignment
    is preserved when dividing the alignment requirement or adding an
    aligned offset. Second, address addition does not wrap modulo 2^64
    when the sum stays within the address space. *)

(** An address a aligned to al is aligned to every positive divisor aa
    of al. *)
Lemma aligned_divisor : forall a al aa, 0 < aa -> a mod al = 0 -> al mod aa = 0 -> a mod aa = 0.
Proof.
  intros a al aa Haa Ha Hal. destruct (Z.eq_dec al 0) as [-> | Hne].
  - rewrite Zmod_0_r in Ha. subst. apply Z.mod_0_l. lia.
  - apply Z.mod_divide in Ha; [|exact Hne]. apply Z.mod_divide in Hal; [|lia].
    apply Z.mod_divide; [lia|]. eapply Z.divide_trans; eassumption.
Qed.

(** Adding a multiple d of aa to an address aligned to aa keeps it
    aligned. *)
Lemma aligned_add : forall a d aa, 0 < aa -> a mod aa = 0 -> d mod aa = 0 -> (a + d) mod aa = 0.
Proof.
  intros a d aa Haa Ha Hd. apply Z.mod_divide in Ha; [|lia]. apply Z.mod_divide in Hd; [|lia].
  apply Z.mod_divide; [lia|]. apply Z.divide_add_r; assumption.
Qed.

(** Adding a non-negative delta to a checked offset yields the same
    address as adding the combined offset directly, provided the sum
    does not overflow 2^64. *)
Lemma raw_address_within : forall a lo off,
  lo <= off -> raw_address a lo + (off - lo) < 2 ^ 64 ->
  raw_address a off = raw_address a lo + (off - lo).
Proof.
  unfold raw_address. intros a lo off Hlo Hb.
  replace (a + off) with ((a + lo) + (off - lo)) by lia.
  rewrite <- (Z.add_mod_idemp_l (a + lo) (off - lo) (2 ^ 64)) by lia.
  pose proof (Z.mod_pos_bound (a + lo) (2 ^ 64) ltac:(lia)).
  apply Z.mod_small. lia.
Qed.

(** The alignment check (`aligned_res/3`) passes for an address a that
    is a multiple of al. *)
Lemma aligned_res_ok : forall a al, a mod al = 0 -> aligned_res a al = ok.
Proof. unfold aligned_res. intros a al H. rewrite H. reflexivity. Qed.

(** Conversely, where the alignment check passes, a is a multiple of
    al. *)
Lemma aligned_res_mod : forall a al, aligned_res a al = ok -> a mod al = 0.
Proof.
  unfold aligned_res. intros a al H. destruct (a mod al =? 0) eqn:E; [|discriminate H].
  apply Z.eqb_eq. exact E.
Qed.

(** ## The access check

    To show that a raw access passes, we first prove that capability
    checks are monotonic with respect to sub-ranges, weaker rights, and
    coarser alignments. *)

(** If an [[access]] check through [[capability]] c succeeds over a
    byte range, then checking any non-empty sub-range with allowed
    rights and a compatible divisor alignment also succeeds. Requiring
    all objects in rs to end below 2^64 prevents an out-of-range check
    from wrapping around to address zero. *)
Lemma cap_access_covered : forall c rs a lo hi r al off size need aa,
  objects_fit rs ->
  cap_access_res c rs (raw_address a lo) (hi - lo) r al = Some ok ->
  lo <= off -> off + size <= hi -> 0 < size ->
  0 < aa -> al mod aa = 0 -> (off - lo) mod aa = 0 ->
  rights_allow r need = true ->
  cap_access_res c rs (raw_address a off) size need aa = Some ok.
Proof.
  intros c rs a lo hi r al off size need aa Hfit H Hlo Hhi Hs Haa Hal Hoff Hr.
  unfold cap_access_res in *.
  destruct c as [| base | base | f | n]; try discriminate H;
    destruct (object_region base rs) as [reg|] eqn:E; try discriminate H;
    pose proof (Hfit _ _ E) as Hend;
    destruct ((base <=? raw_address a lo) && (raw_address a lo + (hi - lo) <=? r_end reg)) eqn:Eb;
    try discriminate H;
    apply andb_true_iff in Eb as [E1 E2]; apply Z.leb_le in E1; apply Z.leb_le in E2;
    rewrite (raw_address_within a lo off Hlo ltac:(lia));
    replace ((base <=? raw_address a lo + (off - lo)) &&
             (raw_address a lo + (off - lo) + size <=? r_end reg)) with true
      by (symmetry; apply andb_true_iff; split; apply Z.leb_le; lia).
  - injection H as H. f_equal. apply aligned_res_ok, aligned_add; auto.
    apply (aligned_divisor _ al); auto using aligned_res_mod.
  - destruct r; simpl in H; [|discriminate H]. destruct need; simpl in Hr; [|discriminate Hr].
    injection H as H. simpl. f_equal. apply aligned_res_ok, aligned_add; auto.
    apply (aligned_divisor _ al); auto using aligned_res_mod.
Qed.

(** An access check that passes at some alignment passes at alignment
    1, as an integer load makes it. *)
Lemma cap_access_align_one : forall c rs a size need al,
  cap_access_res c rs a size need al = Some ok -> cap_access_res c rs a size need 1 = Some ok.
Proof.
  unfold cap_access_res. intros c rs a size need al H.
  destruct c as [| base | base | f | n]; try exact H;
    destruct (object_region base rs) as [reg|]; try exact H;
    destruct ((base <=? a) && (a + size <=? r_end reg)); try exact H.
  - f_equal. apply aligned_res_ok, Z.mod_1_r.
  - destruct need; simpl in *; [f_equal; apply aligned_res_ok, Z.mod_1_r | exact H].
Qed.

(** ## Raw accesses

    Every raw access instruction carries an access kind, an offset, and
    required rights. Here we connect the validator's syntactic
    [covered_access] predicate to the semantic [access_res] check. *)

(** Every raw access type x reads or writes some bytes, at a positive
    alignment (`access_size_align/3`). *)
Lemma access_size_align_pos : forall x, 0 < fst (access_size_align x) /\ 0 < snd (access_size_align x).
Proof. intros [[| | | | t] | w | | [| | t]]; try destruct t; try destruct w; simpl; lia. Qed.

(** If the [[validator]] accepts a raw access instruction as covered by a
    check that passes in memory m, and every object fits in the address
    space, then the instruction's own access check passes in m. *)
Lemma covered_access_checked : forall m p i q lo hi r al,
  objects_fit (m_regions m) ->
  covered_access i q lo hi r al = true ->
  check_passes m p lo hi r al ->
  exists x off need,
    raw_access i = Some (q, x, off, need) /\
    access_res m (raw_address (ptr_addr p) off) (ptr_cap p)
               (fst (access_size_align x)) need (snd (access_size_align x)) = Some ok.
Proof.
  unfold covered_access, check_passes, access_res. intros m p i q lo hi r al Hfit Hc Hp.
  destruct (raw_access i) as [[[[q' x] off] need]|] eqn:Ei; [|discriminate Hc].
  pose proof (access_size_align_pos x) as [Hs Ha].
  destruct (access_size_align x) as [size aa] eqn:Ex. simpl in Hs, Ha |- *.
  repeat rewrite andb_true_iff in Hc. destruct Hc as (((((Hq & H1) & H2) & H3) & H4) & H5).
  apply term_eqb_eq in Hq. subst q'.
  apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.eqb_eq in H3. apply Z.eqb_eq in H4.
  exists x, off, need. split; [reflexivity|]. rewrite Ex. simpl.
  eapply cap_access_covered; eauto.
Qed.

(** ## The loads and stores

    Once an access check passes, the underlying memory operation cannot
    trap or fail as unchecked. These helper lemmas lift that guarantee
    to integer loads, stores, and compare-and-swap operations. *)

(** An integer load whose access check passes always returns a value
    rather than trapping or failing as unchecked. *)
Lemma int_load_res_checked : forall t k m a c rr,
  access_res m a c (fst (access_size_align (XLoad t))) Read 1 = Some ok ->
  int_load_res t k m a c = Some rr -> exists x, rr = RVal x.
Proof.
  unfold int_load_res. intros t k m a c rr Ha H.
  destruct t as [| | | | n]; simpl in Ha; rewrite Ha in H; cases H; injection H as <-; eauto.
Qed.

(** A store of width w succeeds without trapping whenever its access
    check passes. *)
Lemma store_res_checked : forall w m a c x rr m',
  access_res m a c (fst (access_size_align (XWidth w))) Write (snd (access_size_align (XWidth w))) = Some ok ->
  store_res w m a c x = Some (rr, m') -> rr = ok.
Proof.
  unfold store_res. intros w m a c x rr m' Ha H.
  destruct w, x; simpl in Ha, H; try discriminate H; rewrite Ha in H; injection H as <- _; reflexivity.
Qed.

(** A [[cas]] whose write access check passes always yields a value
    rather than trapping or failing as unchecked, whether the
    comparison succeeds or not. *)
Lemma cas_res_checked : forall t k m a c e n rr m',
  access_res m a c (fst (access_size_align (XCas t))) Write (snd (access_size_align (XCas t))) = Some ok ->
  cas_res t k m a c e n = Some (rr, m') -> exists x, rr = RVal x.
Proof.
  unfold cas_res. intros t k m a c e n rr m' Ha H. cbn [fst snd access_size_align] in Ha.
  cbv zeta in H. rewrite Ha in H. cbv beta iota in H. cases H; inversion H; subst; eauto.
Qed.

(** A [[cas]] whose access check traps traps with it, leaving memory
    as it was. *)
Lemma cas_res_trap : forall t k m a c e n why,
  access_res m a c (cas_bytes t) Write (cas_bytes t) = Some (RTrap why) ->
  cas_res t k m a c e n = Some (RTrap why, m).
Proof. unfold cas_res. intros t k m a c e n why Ha. cbv zeta. rewrite Ha. reflexivity. Qed.

(** ## The raw access instruction

    Each raw access instruction evaluates its pointer operand, runs an
    access check, and executes the load, store, or atomic update. We now
    connect our operation lemmas to [inst_step] to prove the main
    coverage theorem. *)

(** A raw access instruction whose own access check passes never steps
    to [Unchecked] under [inst_step]. The instruction may still fail for
    other reasons, such as loading a non-pointer word or passing an
    ill-typed operand. *)
Lemma access_ok_not_unchecked : forall ge fr m i q x off need p why,
  raw_access i = Some (q, x, off, need) ->
  lookup q (fr_env fr) = Some (WPtr p) ->
  access_res m (raw_address (ptr_addr p) off) (ptr_cap p)
             (fst (access_size_align x)) need (snd (access_size_align x)) = Some ok ->
  inst_step ge fr m i <> Some (IStop (Unchecked why)).
Proof.
  intros ge fr m i q x off need p why Ei Hq Ha Hst.
  destruct i; simpl in Ei; cases Ei.
  (* No other instruction is a raw access. *)
  all: try discriminate Ei.
  all: injection Ei as <- <- <- <-; subst.
  all: try (rewrite inst_step_let in Hst by reflexivity).
  all: cbn -[int_load_res access_res pointer_load_effects store_res pointer_store_effects raw_address] in Hst.
  all: rewrite Hq in Hst.
  - (* raw_load: the value loaded is a value, not unchecked. *)
    assert (Ha1 := cap_access_align_one _ _ _ _ _ _ Ha).
    destruct (int_load_res _ _ _ _ _) eqn:El; simpl in Hst; [|discriminate Hst].
    destruct (int_load_res_checked _ _ _ _ _ _ Ha1 El) as [x' ->].
    simpl in Hst. discriminate Hst.
  - (* raw_load_pointer: its check is the one that passed. *)
    simpl in Ha; rewrite Ha in Hst.
    destruct k; try discriminate Hst.
    destruct (pointer_load_effects _ _ _); discriminate Hst.
  - (* raw_cas: its check is the one that passed, so the cas gives old. *)
    destruct l as [|v1 [|v2 [|v3 l]]]; cbn -[cas_res raw_address value_x] in Hst;
      try (destruct (value_x ge (fr_env fr) k v1); cbn -[cas_res raw_address value_x] in Hst);
      try (destruct (value_x ge (fr_env fr) k v2); cbn -[cas_res raw_address value_x] in Hst);
      try discriminate Hst.
    destruct (cas_res _ _ _ _ _ _ _) as [[rr m']|] eqn:Ec; [|discriminate Hst].
    destruct (cas_res_checked _ _ _ _ _ _ _ _ _ Ha Ec) as [x' ->]. discriminate Hst.
  - (* raw_store: the store succeeds. *)
    destruct (width_value_class w); simpl in Hst; try discriminate Hst.
    destruct (value_x _ _ _ _); simpl in Hst; try discriminate Hst.
    destruct (store_res _ _ _ _ _) as [[rr m']|] eqn:Es; try discriminate Hst.
    rewrite (store_res_checked _ _ _ _ _ _ _ Ha Es) in Hst. discriminate Hst.
  - (* raw_store_pointer: its check is the one that passed. *)
    simpl in Ha. destruct (value_x _ _ _ _) as [x|]; simpl in Hst; try discriminate Hst.
    rewrite Ha in Hst. destruct x; try discriminate Hst.
    destruct (pointer_store_effects _ _ _ _); discriminate Hst.
Qed.

(** This is the main coverage theorem. If all objects fit in the address
    space, the [[validator]] accepts a raw access instruction as covered
    by an earlier check, and that check passes in the current memory,
    then stepping the instruction never yields [Unchecked]. *)
Lemma covered_access_not_unchecked : forall ge fr m i q lo hi r al p why,
  objects_fit (m_regions m) ->
  covered_access i q lo hi r al = true ->
  lookup q (fr_env fr) = Some (WPtr p) ->
  check_passes m p lo hi r al ->
  inst_step ge fr m i <> Some (IStop (Unchecked why)).
Proof.
  intros ge fr m i q lo hi r al p why Hfit Hc Hq Hp.
  destruct (covered_access_checked _ _ _ _ _ _ _ _ Hfit Hc Hp) as (x & off & need & Ei & Ha).
  exact (access_ok_not_unchecked _ _ _ _ _ _ _ _ _ _ Ei Hq Ha).
Qed.
