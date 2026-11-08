(** Campaign 3's coverage lemma (docs/formal.md, Campaign 3;
    [docs/rocq.md, The coverage lemma](../../docs/rocq.md#the-coverage-lemma)):
    a [[raw access]] that a passed [[check]] covers, as
    ir.pl's `covered_access/6` says, does not give [[unchecked]].

    A check `let(Q, a, check(Lo, Hi, Rights, Align), [P])` is the
    [[access]] check of the bytes from P+Lo up to P+Hi with Rights and
    Align, and when it passes it yields P itself. A raw access that uses
    Q afterwards reads or writes Size bytes at Q+Off with no check of its
    own: the model makes its access check again, and where that would
    trap the run is `unchecked` (`raw_res/2`). `covered_access/6` asks
    that the access lie inside the checked bytes, at an alignment the
    check's implies, with rights the check's allow. This file proves
    that this is enough: the access's own check then passes
    ([covered_access_not_unchecked]). It is arithmetic over
    `cap_access_res/7`.

    An address is a sum modulo 2^64 (`raw_address/3`), while the model's
    bounds are unbounded integers, so the lemma also needs every object
    to end inside the address space ([objects_fit]). The runtime's
    [address_space] axiom gives that in every state of a run that starts
    [[ready]] (Machine.v's [mreachable_objects_fit]; docs/rocq.md, An
    object past 2^64). That the check passes in the memory the access
    runs in, not only when it ran, is the [[evidence]] invariant's to
    show (Evidence.v, Persistence.v). *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Machine Validate.
Import ListNotations.
Open Scope Z_scope.

(** ## The hypotheses *)

(** The check `check(Lo, Hi, Rights, Align)` of the pointer p passes in
    memory m: the [[access]] check of the bytes from p's address plus lo
    up to plus hi, with rights r and alignment al, as `kind_res/8` makes
    it for `check/4`. *)
Definition check_passes (m : Memory.mem) (p : ptr) (lo hi : Z) (r : rights) (al : Z) : Prop :=
  access_res m (raw_address (ptr_addr p) lo) (ptr_cap p) (hi - lo) r al = Some ok.

(** ## Arithmetic *)

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

(** Offset off from a is offset lo plus off - lo bytes, where lo <= off
    and the sum stays below 2^64: inside the address space, address
    arithmetic ([raw_address], `raw_address/3`, modulo 2^64) does not
    wrap. *)
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

(** ## The access check *)

(** Where every object of the region list rs ends in the address space
    ([objects_fit]) and the [[access]] check through the [[capability]]
    c of the bytes from a+lo up to a+hi, with rights r and alignment al,
    passed, the check of any part of them, from a+off up to
    a+off+size, passes too, at an alignment aa that divides both al and
    off - lo, with rights need that r allows. The first hypothesis
    matters: an object ending above 2^64 would let a check from
    2^64-64 up to 2^64+64 pass and the covered access at offset 64 wrap
    to address 0, outside it. *)
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

(** ## Raw accesses *)

(** Every raw access type x reads or writes some bytes, at a positive
    alignment (`access_size_align/3`). *)
Lemma access_size_align_pos : forall x, 0 < fst (access_size_align x) /\ 0 < snd (access_size_align x).
Proof. intros [[| | | | t] | w |]; try destruct t; try destruct w; simpl; lia. Qed.

(** Where objects fit the address space and the [[validator]] accepts
    the instruction i as an access through q covered by the check of p
    from lo up to hi ([covered_access]), and that check passed in m, i
    is a raw access ([raw_access]: through q, of access type x, at
    offset off, with rights need) whose own access check, at its
    address, size, rights and alignment, passes in m. *)
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

(** ## The loads and stores *)

(** An integer load of type t ([int_load_res], `int_load_res/6`) whose
    access check passes gives a value, not a trap or `unchecked`. *)
Lemma int_load_res_checked : forall t k m a c rr,
  access_res m a c (fst (access_size_align (XLoad t))) Read 1 = Some ok ->
  int_load_res t k m a c = Some rr -> exists x, rr = RVal x.
Proof.
  unfold int_load_res. intros t k m a c rr Ha H.
  destruct t as [| | | | n]; simpl in Ha; rewrite Ha in H; cases H; injection H as <-; eauto.
Qed.

(** A store of width w ([store_res], `store_res/7`) whose access check
    passes succeeds. *)
Lemma store_res_checked : forall w m a c x rr m',
  access_res m a c (fst (access_size_align (XWidth w))) Write (snd (access_size_align (XWidth w))) = Some ok ->
  store_res w m a c x = Some (rr, m') -> rr = ok.
Proof.
  unfold store_res. intros w m a c x rr m' Ha H.
  destruct w, x; simpl in Ha, H; try discriminate H; rewrite Ha in H; injection H as <- _; reflexivity.
Qed.

(** ## The raw access instruction *)

(** A raw access instruction i whose own access check passes, at the
    address of the pointer its operand q holds, is not stopped by
    [inst_step] with [[unchecked]]. The access may still fail otherwise
    (a pointer load of a word that is not a pointer, an operand of the
    wrong class); only `unchecked` is ruled out. *)
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

(** The coverage lemma. Where objects fit the address space, the
    [[validator]] says the raw access instruction i is covered by the
    check that yielded q ([covered_access], the check of the pointer p
    from lo up to hi with rights r and alignment al), and that check
    passes in the memory m that i runs in ([check_passes]), i gives no
    [[unchecked]]. *)
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
