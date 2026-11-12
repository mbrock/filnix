(** Buffers contain data bytes and hidden pointer capabilities.
    These ownership assertions track both kinds of storage, and the
    instruction rules cover integer loads, stores, and compare-and-swap.
    The earlier libc calling rules live in
    [LibcMemLogic](../hello_contracts/LibcMemLogic.v). *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import ZArith Lia.
From Stdlib Require String.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine Panics
  StepRules ExternalCalls ExternalMachine Pieces Heap ContractFrame Language Logic StringLogic.
Open Scope Z_scope.
Open Scope list_scope.

(** ## Aux pieces

    Pointer capabilities live in shadow storage rather than in the
    data bytes that an ordinary C buffer exposes.
    The following piece lists track those shadow locations separately,
    while keeping their offsets aligned with the corresponding byte lists. *)

(** A consecutive list of shadow capabilities becomes one owned piece
    per offset through [aux_ps], beginning at offset o in object b. *)
Definition aux_ps (b o : Z) (cs : list cap) : list (piece * pval) :=
  zip_with (fun i c => (PAux b i, VAux c)) (seqZ o (Z.of_nat (length cs))) cs.

(** A nonempty shadow-slot list separates into its first capability
    and the remaining list, whose starting offset advances by one. *)
Lemma aux_ps_cons b o c cs : aux_ps b o (c :: cs) = (PAux b o, VAux c) :: aux_ps b (o + 1) cs.
Proof.
  unfold aux_ps. cbn [length]. rewrite Nat2Z.inj_succ seqZ_cons; [|lia].
  rewrite Z.pred_succ. reflexivity.
Qed.

(** Concatenating capability lists concatenates their piece lists, with
    the second list beginning immediately after the offsets occupied by the first. *)
Lemma aux_ps_app b o cs ds :
  aux_ps b o (cs ++ ds) = aux_ps b o cs ++ aux_ps b (o + Z.of_nat (length cs)) ds.
Proof.
  revert o. induction cs as [|c cs IH]; intros o; [cbn; rewrite Z.add_0_r; reflexivity|].
  cbn [app]. rewrite !aux_ps_cons IH. cbn [app length].
  replace (o + Z.of_nat (S (length cs))) with (o + 1 + Z.of_nat (length cs)) by lia. reflexivity.
Qed.

(** Repeating one capability across n shadow offsets gives the same
    pieces as assigning that capability separately at every offset. *)
Lemma aux_ps_replicate b o n c :
  aux_ps b o (replicate n c) = (fun i => (PAux b i, VAux c)) <$> seqZ o (Z.of_nat n).
Proof.
  revert o. induction n as [|n IH]; intros o; [reflexivity|].
  rewrite replicate_S aux_ps_cons IH Nat2Z.inj_succ (seqZ_cons o); [|lia].
  rewrite Z.pred_succ. reflexivity.
Qed.

(** Repeating one byte across n offsets gives the same pieces as
    assigning that byte separately at every offset in the range. *)
Lemma byte_ps_replicate b o n x :
  byte_ps b o (replicate n x) = (fun i => (PByte b i, VByte x)) <$> seqZ o (Z.of_nat n).
Proof.
  revert o. induction n as [|n IH]; intros o; [reflexivity|].
  rewrite replicate_S byte_ps_cons IH Nat2Z.inj_succ (seqZ_cons o); [|lia].
  rewrite Z.pred_succ. reflexivity.
Qed.

(** The locations in a shadow-slot piece list are consecutive object
    offsets, independent of the capabilities recorded at those locations. *)
Lemma aux_ps_keys b o cs : (aux_ps b o cs).*1 = PAux b <$> seqZ o (Z.of_nat (length cs)).
Proof.
  revert o. induction cs as [|c cs IH]; intros o; [reflexivity|].
  rewrite aux_ps_cons. cbn [fmap list_fmap fst]. rewrite IH.
  cbn [length]. rewrite Nat2Z.inj_succ (seqZ_cons o); [|lia]. rewrite Z.pred_succ. reflexivity.
Qed.

(** Every piece in a byte list identifies some listed byte and its
    consecutive object-relative offset, as [byte_ps_elem] establishes. *)
Lemma byte_ps_elem b o xs l v :
  (l, v) ∈ byte_ps b o xs -> exists i x, xs !! i = Some x /\ l = PByte b (o + Z.of_nat i) /\ v = VByte x.
Proof.
  intros H. apply list_elem_of_lookup in H as [k Hk]. unfold byte_ps in Hk.
  apply lookup_zip_with_Some in Hk as (i & x & E & Hi & Hx). apply lookup_seqZ in Hi as [-> _].
  injection E as -> ->. eauto.
Qed.

(** Every piece in a shadow-slot list identifies some listed capability
    and its consecutive object-relative offset, as [aux_ps_elem] establishes. *)
Lemma aux_ps_elem b o cs l v :
  (l, v) ∈ aux_ps b o cs -> exists i c, cs !! i = Some c /\ l = PAux b (o + Z.of_nat i) /\ v = VAux c.
Proof.
  intros H. apply list_elem_of_lookup in H as [k Hk]. unfold aux_ps in Hk.
  apply lookup_zip_with_Some in Hk as (i & c & E & Hi & Hc). apply lookup_seqZ in Hi as [-> _].
  injection E as -> ->. eauto.
Qed.

(** Every offset within a capability list has a corresponding shadow
    piece key, allowing an ownership proof to locate that slot. *)
Lemma aux_ps_key b o cs i : 0 <= i < Z.of_nat (length cs) -> PAux b (o + i) ∈ (aux_ps b o cs).*1.
Proof.
  intros Hi. rewrite aux_ps_keys. apply list_elem_of_fmap_2. apply elem_of_seqZ. lia.
Qed.

(** Every offset within a byte list has a corresponding byte piece
    key, allowing an ownership proof to locate that byte. *)
Lemma byte_ps_key b o xs i : 0 <= i < Z.of_nat (length xs) -> PByte b (o + i) ∈ (byte_ps b o xs).*1.
Proof.
  intros Hi. rewrite byte_ps_keys. apply list_elem_of_fmap_2. apply elem_of_seqZ. lia.
Qed.

(** ## Integer stores

    An integer store writes its least significant byte first in the
    little-endian memory used by this model.
    The following representation turns that write into an updated byte
    list and proves that pieces outside the written range still agree. *)

(** Storing integer y into n bytes writes its low-order bytes in
    little-endian order, which [le_bytes] constructs as a list. *)
Definition le_bytes (y : Z) (n : nat) : list Z := (fun i => byte_of y (Z.of_nat i)) <$> seq 0 n.

(** The integer's magnitude does not affect the encoded list's length;
    [length_le_bytes] gives exactly the requested number of stored bytes. *)
Lemma length_le_bytes y n : length (le_bytes y n) = n.
Proof. unfold le_bytes. rewrite length_fmap length_seq. reflexivity. Qed.

(** An integer store replaces the owned range with its little-endian
    bytes and preserves agreement for every piece outside that range. *)
Lemma store_after m b reg o xs y :
  live_disjoint m -> live_at m b reg -> all_agree m (byte_ps b o xs) ->
  all_agree (store_bytes m (b + o) (Z.of_nat (length xs)) y) (byte_ps b o (le_bytes y (length xs))) /\
  frame_ok (byte_ps b o xs).*1 m (store_bytes m (b + o) (Z.of_nat (length xs)) y).
Proof.
  intros Hd Hl Hx.
  assert (Hbyte : forall i, (i < length xs)%nat ->
            registered m b /\ 0 <= o + Z.of_nat i /\ b + (o + Z.of_nat i) < r_end reg).
  { intros i Hi. destruct (lookup_lt_is_Some_2 xs i Hi) as [x Hxi].
    destruct (byte_ps_agree _ _ _ _ _ _ _ Hl Hx Hxi) as (_ & H1 & H2).
    split; [destruct Hl as [E _]; unfold registered; congruence | lia]. }
  split.
  - apply all_agree_intro. intros l v Hin. apply byte_ps_elem in Hin as (i & x & Hxi & -> & ->).
    unfold le_bytes in Hxi. apply list_lookup_fmap_Some in Hxi as (k & -> & Hk).
    apply lookup_seq in Hk as [-> Hi]. cbn [Nat.add]. destruct (Hbyte i Hi) as (Hreg & H1 & H2).
    cbn [agree_piece]. split; [exact Hreg|]. intros reg' E L. destruct Hl as [E0 _].
    rewrite regions_store_bytes E0 in E. injection E as <-. split; [exact H1|]. split; [exact H2|].
    replace (b + (o + Z.of_nat i)) with (b + o + Z.of_nat i) by lia. apply stored_byte. lia.
  - apply (frame_within _ _ _ b reg); [reflexivity | exact Hd | exact Hl | |].
    + intros a H. apply store_bytes_other. intros Ha.
      destruct (Hbyte (Z.to_nat (a - b - o)) ltac:(lia)) as (_ & H1 & H2).
      apply H; [lia|]. replace (a - b) with (o + (a - b - o)) by lia. apply byte_ps_key. lia.
    + intros a _. reflexivity.
Qed.

(** ## Integer values

    Reading a byte range as an integer must reverse the little-endian
    decomposition used by stores.
    The following definitions combine the listed bytes and connect that
    arithmetic value to a load from the actual memory. *)

(** A little-endian byte list represents the first byte plus successive
    bytes weighted by powers of 256, which [of_bytes] computes. *)
Definition of_bytes (xs : list Z) : Z := fold_right (fun x acc => x + 256 * acc) 0 xs.

(** Concatenating byte lists places the second list's integer above
    the first list's bytes, shifting its contribution by the first list's length. *)
Lemma of_bytes_app xs ys : of_bytes (xs ++ ys) = of_bytes xs + 256 ^ Z.of_nat (length xs) * of_bytes ys.
Proof.
  unfold of_bytes. induction xs as [|x xs IH]; cbn [app fold_right length]; [rewrite Z.pow_0_r; ring|].
  rewrite IH Nat2Z.inj_succ Z.pow_succ_r; [ring | lia].
Qed.

(** Loading n consecutive bytes from memory equals combining those
    same bytes as a little-endian list, as [load_bytes_of_bytes] establishes. *)
Lemma load_bytes_of_bytes m a n :
  load_bytes m a (Z.of_nat n) = of_bytes ((fun i => m_bytes m (a + Z.of_nat i)) <$> seq 0 n).
Proof.
  unfold load_bytes. rewrite Nat2Z.id.
  replace (of_bytes _) with (0 * 256 ^ Z.of_nat n + of_bytes ((fun i => m_bytes m (a + Z.of_nat i)) <$> seq 0 n))
    by ring.
  generalize 0 as acc. induction n as [|n IH]; intros acc; [change (Z.of_nat 0) with 0; cbn; ring|].
  cbn -[Z.of_nat Z.add Z.mul Z.pow seq]. rewrite IH seq_S fmap_app of_bytes_app length_fmap length_seq.
  cbn [fmap list_fmap Nat.add]. unfold of_bytes at 3. cbn [fold_right].
  rewrite Nat2Z.inj_succ Z.pow_succ_r; [ring | lia].
Qed.

(** When owned bytes agree with a live object's memory, loading their
    range returns exactly the little-endian integer represented by the list. *)
Lemma bytes_load m b reg o xs :
  live_at m b reg -> all_agree m (byte_ps b o xs) ->
  load_bytes m (b + o) (Z.of_nat (length xs)) = of_bytes xs.
Proof.
  intros Hl Hx. rewrite load_bytes_of_bytes. f_equal. apply list_eq. intros i.
  rewrite list_lookup_fmap. destruct (decide (i < length xs)%nat) as [Hi|Hi].
  - rewrite lookup_seq_lt; [|exact Hi]. destruct (lookup_lt_is_Some_2 xs i Hi) as [x Hxi]. rewrite Hxi.
    destruct (byte_ps_agree _ _ _ _ _ _ _ Hl Hx Hxi) as (Hv & _ & _). cbn. f_equal.
    rewrite <- Hv. f_equal. lia.
  - rewrite lookup_seq_ge; [|lia]. rewrite lookup_ge_None_2; [reflexivity|lia].
Qed.

(** ## Blocks

    A block combines the enclosing object's lifetime with ownership of
    its data bytes and the corresponding shadow capability slots.
    The following facts describe filling and copying such blocks while
    preserving every owned piece outside the destination. *)

(** A block's piece list includes its object lifetime followed by its
    byte and shadow-slot lists, which [block_ps] collects at one offset. *)
Definition block_ps (b : Z) (reg : region) (o : Z) (xs : list Z) (cs : list cap) : list (piece * pval) :=
  (PLive b, VLive reg) :: byte_ps b o xs ++ aux_ps b o cs.

(** Changing a block's recorded bytes and capabilities leaves its piece
    locations unchanged when both replacement lists retain their original lengths. *)
Lemma block_ps_keys b reg o xs cs ys ds :
  length ys = length xs -> length ds = length cs ->
  (block_ps b reg o ys ds).*1 = (block_ps b reg o xs cs).*1.
Proof.
  intros Hy Hd. unfold block_ps. cbn [fmap list_fmap fst]. rewrite !fmap_app.
  rewrite !byte_ps_keys !aux_ps_keys Hy Hd. reflexivity.
Qed.

(** Filling bytes clears capabilities at eight-byte-aligned offsets
    and leaves the other shadow entries unchanged, which [clear_slots] records.
    When the object base is also aligned, these offsets identify
    exactly the pointer slots cleared by the contract. *)
Definition clear_slots (o : Z) (cs : list cap) : list cap :=
  zip_with (fun i c => if i mod 8 =? 0 then CNone else c) (seqZ o (Z.of_nat (length cs))) cs.

(** Clearing capabilities changes their values without adding or
    removing entries, so [length_clear_slots] preserves the size of the shadow-slot list. *)
Lemma length_clear_slots o cs : length (clear_slots o cs) = length cs.
Proof. unfold clear_slots. rewrite length_zip_with length_seqZ Nat2Z.id. lia. Qed.

(** Looking up a cleared slot yields an empty capability at an aligned
    offset and the old capability at any other offset. *)
Lemma lookup_clear_slots o cs i c :
  clear_slots o cs !! i = Some c ->
  exists c0, cs !! i = Some c0 /\ c = if (o + Z.of_nat i) mod 8 =? 0 then CNone else c0.
Proof.
  unfold clear_slots. intros H. apply lookup_zip_with_Some in H as (k & c0 & -> & Hk & Hc).
  apply lookup_seqZ in Hk as [-> _]. eauto.
Qed.

(** Writing an aligned block under the contract's destination bounds
    preserves agreement for every owned piece outside its byte and shadow ranges.
    The lemma [block_frame] supplies this preservation fact to both
    memory filling and copying, which share the same write restriction. *)
Lemma block_frame m m' b reg o xs cs :
  live_disjoint m -> live_at m b reg -> b mod 8 = 0 -> o mod 8 = 0 -> length cs = length xs ->
  all_agree m (byte_ps b o xs ++ aux_ps b o cs) ->
  memset_frame m (mkPtr (b + o) (Obj b)) (Z.of_nat (length xs)) m' ->
  frame_ok (byte_ps b o xs ++ aux_ps b o cs).*1 m m'.
Proof.
  intros Hd Hl Hb8 Ho8 Hlen Ha (Hr & Hbytes & Haux). apply all_agree_app in Ha as [Hx Hc].
  assert (Hbyte : forall i, (i < length xs)%nat -> 0 <= o + Z.of_nat i /\ b + (o + Z.of_nat i) < r_end reg).
  { intros i Hi. destruct (lookup_lt_is_Some_2 xs i Hi) as [x Hxi].
    destruct (byte_ps_agree _ _ _ _ _ _ _ Hl Hx Hxi) as (_ & H1 & H2). lia. }
  assert (Hmod : forall i, (b + (o + i)) mod 8 = (o + i) mod 8).
  { intros i. rewrite Z.add_mod; [|lia]. rewrite Hb8 Z.add_0_l Z.mod_mod; [reflexivity|lia]. }
  apply (frame_within _ _ _ b reg); [exact Hr | exact Hd | exact Hl | |].
  - intros a H. apply Hbytes. intros Hs. unfold span_contains in Hs. cbn in Hs.
    destruct (Hbyte (Z.to_nat (a - b - o)) ltac:(lia)) as [H1 H2].
    apply H; [lia|]. rewrite fmap_app. apply elem_of_app. left.
    replace (a - b) with (o + (a - b - o)) by lia. apply byte_ps_key. lia.
  - intros a H. apply Haux. destruct (memset_touched _ _ _) eqn:Ht; [|reflexivity]. exfalso.
    apply memset_touched_spec in Ht as (Hn & Ha8 & Hhi & Hlo). cbn [ptr_addr] in Hhi, Hlo.
    assert (Hab : b + o <= a).
    { pose proof (Z.div_mod a 8 ltac:(lia)). pose proof (Z.div_mod (b + o) 8 ltac:(lia)).
      pose proof (Hmod 0) as Hm0. rewrite Z.add_0_r in Hm0. rewrite Ho8 in Hm0. lia. }
    destruct (Hbyte (Z.to_nat (a - b - o)) ltac:(lia)) as [H1 H2].
    apply H; [lia|]. rewrite fmap_app. apply elem_of_app. right.
    replace (a - b) with (o + (a - b - o)) by lia. apply aux_ps_key. lia.
Qed.

(** Filling an aligned block replaces every byte with the character's
    low byte and clears each touched pointer capability.
    The lemma [fill_after] records those updated pieces and preserves
    agreement for every owned piece outside the block. *)
Lemma fill_after m m' b reg o xs cs c :
  live_disjoint m -> live_at m b reg -> b mod 8 = 0 -> o mod 8 = 0 -> length cs = length xs ->
  all_agree m (byte_ps b o xs ++ aux_ps b o cs) ->
  memset_result m (mkPtr (b + o) (Obj b)) c (Z.of_nat (length xs)) m' ->
  all_agree m' (byte_ps b o (replicate (length xs) (c mod 256)) ++ aux_ps b o (clear_slots o cs)) /\
  frame_ok (byte_ps b o xs ++ aux_ps b o cs).*1 m m'.
Proof.
  intros Hd Hl Hb8 Ho8 Hlen Ha ((Hr & Hbytes & Haux) & Hfill & Hclear).
  apply all_agree_app in Ha as [Hx Hc].
  set (n := Z.of_nat (length xs)).
  assert (Hregs : forall b', registered m b' -> registered m' b') by (unfold registered; rewrite Hr; auto).
  (* The i-th byte and slot lie in b's bounds. *)
  assert (Hbyte : forall i, (i < length xs)%nat -> 0 <= o + Z.of_nat i /\ b + (o + Z.of_nat i) < r_end reg).
  { intros i Hi. destruct (lookup_lt_is_Some_2 xs i Hi) as [x Hxi].
    destruct (byte_ps_agree _ _ _ _ _ _ _ Hl Hx Hxi) as (_ & H1 & H2). lia. }
  assert (Hslot : forall i c0, cs !! i = Some c0 -> registered m b /\ 0 <= o + Z.of_nat i /\
            b + (o + Z.of_nat i) < r_end reg /\ aux_holds m (b + (o + Z.of_nat i)) c0).
  { intros i c0 Hci. destruct Hl as [E L].
    assert (Hin : (aux_ps b o cs) !! i = Some (PAux b (o + Z.of_nat i), VAux c0)).
    { unfold aux_ps. apply lookup_zip_with_Some. exists (o + Z.of_nat i), c0. split; [reflexivity|].
      split; [|exact Hci]. apply lookup_seqZ. split; [reflexivity|]. apply lookup_lt_Some in Hci. lia. }
    destruct (all_agree_elem _ _ _ _ Hc (list_elem_of_lookup_2 _ _ _ Hin)) as [Hreg Hin'].
    destruct (Hin' reg E L) as (Ho & He & Hh). auto. }
  assert (Hmod : forall i, (b + (o + i)) mod 8 = (o + i) mod 8).
  { intros i. rewrite Z.add_mod; [|lia]. rewrite Hb8 Z.add_0_l Z.mod_mod; [reflexivity|lia]. }
  split.
  - apply all_agree_app. split; apply all_agree_intro; intros l v Hin.
    + apply byte_ps_elem in Hin as (i & x & Hxi & -> & ->).
      apply lookup_replicate in Hxi as [-> Hi].
      destruct (lookup_lt_is_Some_2 xs i Hi) as [x0 Hx0].
      pose proof (all_agree_elem _ _ _ _ Hx (list_elem_of_lookup_2 _ _ _ (byte_ps_lookup b o xs i x0 Hx0)))
        as [Hreg _].
      cbn [agree_piece]. split; [exact (Hregs _ Hreg)|]. intros reg' E L.
      destruct Hl as [E0 _]. rewrite Hr E0 in E. injection E as <-.
      destruct (Hbyte i Hi) as [H1 H2]. split; [exact H1|]. split; [exact H2|].
      apply Hfill. unfold span_contains. cbn. lia.
    + apply aux_ps_elem in Hin as (i & c' & Hci & -> & ->).
      destruct (lookup_clear_slots o cs i c' Hci) as (c0 & Hc0 & ->).
      destruct (Hslot i c0 Hc0) as (Hreg & H1 & H2 & Hh).
      cbn [agree_piece]. split; [exact (Hregs _ Hreg)|]. intros reg' E L.
      destruct Hl as [E0 _]. rewrite Hr E0 in E. injection E as <-.
      split; [exact H1|]. split; [exact H2|].
      assert (Hi : (i < length xs)%nat) by (rewrite <- Hlen; exact (lookup_lt_Some _ _ _ Hc0)).
      destruct (Z.eqb_spec ((o + Z.of_nat i) mod 8) 0) as [Hz|Hz].
      * left. apply Hclear. apply memset_touched_spec. cbn [ptr_addr]. rewrite Hmod. lia.
      * unfold aux_holds in *. rewrite Hr. rewrite Haux; [exact Hh|].
        destruct (memset_touched _ _ _) eqn:Ht; [|reflexivity].
        apply memset_touched_spec in Ht as (_ & Ht & _). rewrite Hmod in Ht. contradiction.
  - apply (block_frame _ _ _ reg); [exact Hd | exact Hl | exact Hb8 | exact Ho8 | exact Hlen |
      apply all_agree_app; split; assumption | split; [exact Hr|]; split; assumption].
Qed.

(** Copying aligned buffers transfers a pointer capability only when
    the copy covers all eight bytes of that pointer slot.
    The function [copy_slots] clears a partially copied slot and leaves
    shadow entries at unaligned offsets unchanged. *)
Definition copy_slots (n : Z) (ds cs : list cap) : list cap :=
  zip_with (fun i dc => if i mod 8 =? 0 then (if i + 8 <=? n then fst dc else CNone) else snd dc)
    (seqZ 0 (Z.of_nat (length cs))) (zip ds cs).

(** Copying equally sized shadow lists changes their recorded values
    without changing the number of destination entries, as [length_copy_slots] proves. *)
Lemma length_copy_slots n ds cs : length ds = length cs -> length (copy_slots n ds cs) = length cs.
Proof.
  intros H. unfold copy_slots. rewrite length_zip_with length_seqZ Nat2Z.id length_zip. lia.
Qed.

(** Each copied shadow entry comes from the source, becomes empty,
    or stays unchanged according to its alignment and complete byte coverage. *)
Lemma lookup_copy_slots n ds cs i c :
  copy_slots n ds cs !! i = Some c ->
  exists d0 c0, ds !! i = Some d0 /\ cs !! i = Some c0 /\
    c = if Z.of_nat i mod 8 =? 0 then (if Z.of_nat i + 8 <=? n then d0 else CNone) else c0.
Proof.
  unfold copy_slots. intros H. apply lookup_zip_with_Some in H as (k & [d0 c0] & -> & Hk & Hdc).
  apply lookup_seqZ in Hk as [-> _]. apply lookup_zip_with_Some in Hdc as (x & y & E & Hd & Hc).
  injection E as -> ->. exists x, y. auto.
Qed.

(** At an aligned destination slot, a copy installs the matching source
    capability only when all eight bytes fit within the copied range.
    Otherwise, [copy_slot_at] shows that the resulting capability is
    empty, assuming both buffer addresses and the slot offset are aligned. *)
Lemma copy_slot_at m b o b' o' c' n i :
  b mod 8 = 0 -> o mod 8 = 0 -> b' mod 8 = 0 -> o' mod 8 = 0 -> 0 <= i -> i mod 8 = 0 ->
  copy_slot m (mkPtr (b + o) (Obj b)) (mkPtr (b' + o') c') n (b + (o + i)) =
  if i + 8 <=? n then m_aux m (b' + (o' + i)) else CNone.
Proof.
  intros Hb Ho Hb' Ho' Hi Hi8. unfold copy_slot, copy_full_slot. cbn [ptr_addr].
  replace (b + o <=? b + (o + i)) with true by (symmetry; apply Z.leb_le; lia).
  replace (b + (o + i) + 8 <=? b + o + n) with (i + 8 <=? n)
    by (destruct (Z.leb_spec (i + 8) n), (Z.leb_spec (b + (o + i) + 8) (b + o + n)); lia).
  replace (b' + o' + (b + (o + i) - (b + o))) with (b' + (o' + i)) by lia.
  replace ((b' + (o' + i)) mod 8 =? 0) with true.
  - destruct (i + 8 <=? n); reflexivity.
  - symmetry. apply Z.eqb_eq. pose proof (Z.div_mod b' 8 ltac:(lia)). pose proof (Z.div_mod o' 8 ltac:(lia)).
    pose proof (Z.div_mod i 8 ltac:(lia)). pose proof (Z.div_mod (b' + (o' + i)) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (b' + (o' + i)) 8 ltac:(lia)). lia.
Qed.

(** An aligned block copy installs the source bytes and the shadow
    capabilities permitted by complete pointer-slot coverage.
    The lemma [copy_after] records the new destination pieces and
    preserves agreement for every piece outside that destination. *)
Lemma copy_after m m' b reg o xs cs b' reg' o' ys ds c' :
  live_disjoint m -> live_at m b reg -> live_at m b' reg' -> b mod 8 = 0 -> o mod 8 = 0 -> b' mod 8 = 0 -> o' mod 8 = 0 ->
  length ys = length xs -> length cs = length xs -> length ds = length xs ->
  all_agree m (byte_ps b o xs ++ aux_ps b o cs) -> all_agree m (byte_ps b' o' ys ++ aux_ps b' o' ds) ->
  copy_result m (mkPtr (b + o) (Obj b)) (mkPtr (b' + o') c') (Z.of_nat (length xs)) m' ->
  all_agree m' (byte_ps b o ys ++ aux_ps b o (copy_slots (Z.of_nat (length xs)) ds cs)) /\
  frame_ok (byte_ps b o xs ++ aux_ps b o cs).*1 m m'.
Proof.
  intros Hd Hl Hl' Hb8 Ho8 Hb8' Ho8' Hly Hlc Hld Hdst Hsrc Hres.
  pose proof Hres as (Hfr & Hcb & Hcs). pose proof Hfr as (Hr & _ & Haux).
  split; [|exact (block_frame _ _ _ _ _ _ _ Hd Hl Hb8 Ho8 Hlc Hdst Hfr)].
  pose proof Hdst as Hdst'. apply all_agree_app in Hdst' as [Hx Hc]. apply all_agree_app in Hsrc as [Hy Hds].
  destruct Hl as [E0 L0].
  assert (Hreg : registered m' b) by (unfold registered; rewrite Hr E0; discriminate).
  (* The i-th byte and slot of the destination lie in b's bounds. *)
  assert (Hbyte : forall i, (i < length xs)%nat -> 0 <= o + Z.of_nat i /\ b + (o + Z.of_nat i) < r_end reg).
  { intros i Hi. destruct (lookup_lt_is_Some_2 xs i Hi) as [x Hxi].
    destruct (byte_ps_agree _ _ _ _ _ _ _ (conj E0 L0) Hx Hxi) as (_ & H1 & H2). lia. }
  assert (Hslot : forall b0 o0 cs0 i c0, all_agree m (aux_ps b0 o0 cs0) -> cs0 !! i = Some c0 ->
            forall reg0, live_at m b0 reg0 -> aux_holds m (b0 + (o0 + Z.of_nat i)) c0).
  { intros b0 o0 cs0 i c0 Ha Hci reg0 [E L].
    assert (Hin : (aux_ps b0 o0 cs0) !! i = Some (PAux b0 (o0 + Z.of_nat i), VAux c0)).
    { unfold aux_ps. apply lookup_zip_with_Some. exists (o0 + Z.of_nat i), c0. split; [reflexivity|].
      split; [|exact Hci]. apply lookup_seqZ. split; [reflexivity|]. apply lookup_lt_Some in Hci. lia. }
    destruct (all_agree_elem _ _ _ _ Ha (list_elem_of_lookup_2 _ _ _ Hin)) as [_ Hin'].
    destruct (Hin' reg0 E L) as (_ & _ & Hh). exact Hh. }
  assert (Hmod : forall i, (b + (o + i)) mod 8 = i mod 8).
  { intros i. rewrite Z.add_mod; [|lia]. rewrite Hb8 Z.add_0_l Z.mod_mod; [|lia].
    rewrite Z.add_mod; [|lia]. rewrite Ho8 Z.add_0_l Z.mod_mod; [reflexivity|lia]. }
  apply all_agree_app. split; apply all_agree_intro; intros l v Hin.
  - apply byte_ps_elem in Hin as (i & y & Hyi & -> & ->).
    assert (Hi : (i < length xs)%nat) by (rewrite <- Hly; exact (lookup_lt_Some _ _ _ Hyi)).
    destruct (Hbyte i Hi) as [H1 H2]. cbn [agree_piece]. split; [exact Hreg|].
    intros reg0 E L. rewrite Hr E0 in E. injection E as <-. split; [exact H1|]. split; [exact H2|].
    rewrite Hcb; [|unfold span_contains; cbn; lia]. cbn [ptr_addr].
    replace (b' + o' + (b + (o + Z.of_nat i) - (b + o))) with (b' + (o' + Z.of_nat i)) by lia.
    destruct (byte_ps_agree _ _ _ _ _ _ _ Hl' Hy Hyi) as (Hv & _ & _). exact Hv.
  - apply aux_ps_elem in Hin as (i & c & Hci & -> & ->).
    destruct (lookup_copy_slots _ _ _ _ _ Hci) as (d0 & c0 & Hd0 & Hc0 & ->).
    assert (Hi : (i < length xs)%nat) by (rewrite <- Hlc; exact (lookup_lt_Some _ _ _ Hc0)).
    destruct (Hbyte i Hi) as [H1 H2]. cbn [agree_piece]. split; [exact Hreg|].
    intros reg0 E L. rewrite Hr E0 in E. injection E as <-. split; [exact H1|]. split; [exact H2|].
    unfold aux_holds. rewrite Hr.
    destruct (Z.eqb_spec (Z.of_nat i mod 8) 0) as [Hz|Hz].
    + assert (Ht : memset_touched (mkPtr (b + o) (Obj b)) (Z.of_nat (length xs)) (b + (o + Z.of_nat i)) = true).
      { apply memset_touched_spec. cbn [ptr_addr]. rewrite Hmod. lia. }
      rewrite (Hcs _ Ht) (copy_slot_at _ _ _ _ _ _ _ (Z.of_nat i) Hb8 Ho8 Hb8' Ho8' ltac:(lia) Hz).
      destruct (Z.of_nat i + 8 <=? Z.of_nat (length xs)).
      * exact (Hslot _ _ _ _ _ Hds Hd0 _ Hl').
      * left. reflexivity.
    + rewrite Haux; [exact (Hslot _ _ _ _ _ Hc Hc0 _ (conj E0 L0))|].
      destruct (memset_touched _ _ _) eqn:Ht; [|reflexivity].
      apply memset_touched_spec in Ht as (_ & Ht & _). rewrite Hmod in Ht. contradiction.
Qed.

(** A write confined to one live object leaves every other object's
    owned pieces valid when all object regions remain unchanged.
    The lemma [frame_other] turns that address restriction into the
    agreement needed to preserve unrelated ownership. *)
Lemma frame_other m m' b reg l v :
  m_regions m' = m_regions m -> live_disjoint m -> live_at m b reg ->
  (forall a, ~ (b <= a < r_end reg) -> m_bytes m' a = m_bytes m a /\ m_aux m' a = m_aux m a) ->
  (mem_piece l -> piece_id l <> b) -> agree_piece m l v -> agree_piece m' l v.
Proof.
  intros Hr Hd Hl Hout Hid.
  set (ks := (PByte b <$> seqZ 0 (r_end reg - b)) ++ (PAux b <$> seqZ 0 (r_end reg - b))).
  apply (frame_within ks m m' b reg Hr Hd Hl).
  - intros a H. apply Hout. intros Ha. apply (H Ha). apply elem_of_app. left.
    apply list_elem_of_fmap_2. apply elem_of_seqZ. lia.
  - intros a H. apply Hout. intros Ha. apply (H Ha). apply elem_of_app. right.
    apply list_elem_of_fmap_2. apply elem_of_seqZ. lia.
  - intros Hk. apply elem_of_app in Hk as [Hk|Hk]; apply list_elem_of_fmap in Hk as (o & -> & _);
      exact (Hid I eq_refl).
Qed.

(** Owned bytes inside a live object's bounds form a readable range
    through either its writable or read-only capability.
    The lemma [block_readable] also identifies every byte value when
    the object fits the address space and all listed values are bytes. *)
Lemma block_readable m b reg o xs c :
  live_at m b reg -> all_agree m (byte_ps b o xs) -> objects_fit (m_regions m) ->
  c = Obj b \/ c = Ro b -> 0 <= o -> b + o + Z.of_nat (length xs) <= r_end reg ->
  Forall (fun x => 0 <= x < 256) xs ->
  readable_bytes m (mkPtr (b + o) c) (Z.of_nat (length xs)) /\
  forall i x, xs !! i = Some x -> m_bytes m (b + o + Z.of_nat i) = x.
Proof.
  intros Hl Hx Hfit Hc Ho Hend Hy. destruct (Hfit b reg (proj1 Hl)) as [Hb0 Hfit'].
  assert (Hv : forall i x, xs !! i = Some x -> m_bytes m (b + o + Z.of_nat i) = x).
  { intros i x Hi. destruct (byte_ps_agree _ _ _ _ _ _ _ Hl Hx Hi) as (Hv & _ & _).
    replace (b + o + Z.of_nat i) with (b + (o + Z.of_nat i)) by lia. exact Hv. }
  split; [|exact Hv]. split; [lia|]. split; [exists b, reg; split; [exact Hc | exact Hl]|]. split.
  - apply (access_read _ b reg); [exact Hc | exact (proj1 Hl) | cbn; lia | cbn; lia | apply Z.mod_1_r].
  - intros i Hi. cbn [ptr_addr]. destruct (lookup_lt_is_Some_2 xs (Z.to_nat i) ltac:(lia)) as [x Hxi].
    rewrite <- (Z2Nat.id i) by lia. rewrite (Hv _ _ Hxi). exact (Forall_lookup_1 _ _ _ _ Hy Hxi).
Qed.

(** The module [MemLogicOn] builds buffer ownership and instruction rules
    over an existing program logic for any chosen [[runtime]] R. *)
Module MemLogicOn (R : Runtime) (LG0 : LogicSig R).
Module SL := StringLogicOn R LG0.
Module LG := SL.LG.
Module L := LG.L.
Import L LG SL.

Section mem.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.

(** A caller owns consecutive data bytes through [bytes], which records
    the listed values from offset o within object b. *)
Definition bytes (b o : Z) (xs : list Z) : iProp Σ := pts (byte_ps b o xs).

(** Shared readers use [bytesq] to own a fraction of the same byte
    range, retaining its recorded values without exclusive write permission. *)
Definition bytesq (dq : dfrac) (b o : Z) (xs : list Z) : iProp Σ := ptsq dq (byte_ps b o xs).

(** A buffer needs ownership of its hidden pointer capabilities when
    an operation copies or clears the pointers stored in that buffer.
    The assertion [auxes] records those capabilities in consecutive
    shadow entries, beginning at offset o within object b. *)
Definition auxes (b o : Z) (cs : list cap) : iProp Σ := pts (aux_ps b o cs).

(** Owning a block's complete piece list equals owning its object
    lifetime, its data bytes, and its shadow slots separately. *)
Lemma block_pts b reg o xs cs : pts (block_ps b reg o xs cs) ⊣⊢ live b reg ∗ bytes b o xs ∗ auxes b o cs.
Proof. rewrite /block_ps /live /bytes /auxes /pts big_sepL_cons big_sepL_app big_sepL_singleton. done. Qed.

(** Ownership of concatenated byte lists splits into ownership of the
    first range and the second range immediately following it. *)
Lemma bytes_app b o xs ys : bytes b o (xs ++ ys) ⊣⊢ bytes b o xs ∗ bytes b (o + Z.of_nat (length xs)) ys.
Proof. rewrite /bytes byte_ps_app. apply pts_app. Qed.

(** Ownership of concatenated shadow lists splits into ownership of the
    first range and the second range immediately following it. *)
Lemma auxes_app b o cs ds : auxes b o (cs ++ ds) ⊣⊢ auxes b o cs ∗ auxes b (o + Z.of_nat (length cs)) ds.
Proof. rewrite /auxes aux_ps_app. apply pts_app. Qed.

(** Byte ownership can split at any position within the list,
    separating the first n bytes from the remainder at the advanced offset. *)
Lemma bytes_take_drop b o xs n : (n <= length xs)%nat ->
  bytes b o xs ⊣⊢ bytes b o (take n xs) ∗ bytes b (o + Z.of_nat n) (drop n xs).
Proof.
  intros Hn. assert (E : Z.of_nat n = Z.of_nat (length (take n xs))) by (rewrite length_take; lia).
  rewrite E -bytes_app take_drop. done.
Qed.

(** Shadow-slot ownership can split at any position within the list,
    separating the first n entries from the remainder at the advanced offset. *)
Lemma auxes_take_drop b o cs n : (n <= length cs)%nat ->
  auxes b o cs ⊣⊢ auxes b o (take n cs) ∗ auxes b (o + Z.of_nat n) (drop n cs).
Proof.
  intros Hn. assert (E : Z.of_nat n = Z.of_nat (length (take n cs))) by (rewrite length_take; lia).
  rewrite E -auxes_app take_drop. done.
Qed.

(** A fresh object's ownership supplies its lifetime, zero-valued bytes,
    and empty shadow capabilities across its full extent, as [obj_zero_block] exposes. *)
Lemma obj_zero_block b q :
  0 <= req_extent q ->
  obj b q ⊣⊢ live b (mkRegion b (b + req_extent q) (req_kind q) Live) ∗
    bytes b 0 (replicate (Z.to_nat (req_extent q)) 0) ∗ auxes b 0 (replicate (Z.to_nat (req_extent q)) CNone).
Proof.
  intros H. rewrite /obj /obj_ps /live /bytes /auxes byte_ps_replicate aux_ps_replicate Z2Nat.id; [|exact H].
  rewrite /pts big_sepL_cons big_sepL_app big_sepL_singleton. done.
Qed.

(** Separately owning an object lifetime and a string's lifetime forces
    different objects, because the same lifetime cannot be owned twice. *)
Lemma live_string_ne b reg p b' reg' ys : live b reg -∗ string p b' reg' ys -∗ ⌜b <> b'⌝.
Proof.
  rewrite /live /string /string_ps /pts !big_sepL_cons. iIntros "[Hl _] [_ [Hs _]]".
  iDestruct (pointsto_ne with "Hl Hs") as %Hne. iPureIntro. intros <-. apply Hne. reflexivity.
Qed.

(** An object's lifetime and its terminated byte sequence form string
    ownership once the pointer and contents satisfy the string bounds. *)
Lemma block_string b reg o ys :
  string_ok (mkPtr (b + o) (Obj b)) b reg ys ->
  live b reg -∗ bytes b o (ys ++ [0]) -∗ string (mkPtr (b + o) (Obj b)) b reg ys.
Proof.
  intros Hok. rewrite /string /string_ps /live /bytes /pts !big_sepL_cons big_sepL_nil. cbn [ptr_addr].
  replace (b + o - b) with o by lia. iIntros "[Hl _] Hx". iSplit; [iPureIntro; exact Hok|]. iFrame.
Qed.

(** A string can lend a byte window before its terminator, together
    with its object lifetime, through [string_window].
    The rule restores the original string ownership when the borrower
    returns the lifetime and the same byte window. *)
Lemma string_window p b reg ys k n :
  (k + n <= length ys)%nat ->
  string p b reg ys -∗
  ⌜string_ok p b reg ys⌝ ∗ live b reg ∗ bytes b (ptr_addr p - b + Z.of_nat k) (take n (drop k ys)) ∗
  (live b reg -∗ bytes b (ptr_addr p - b + Z.of_nat k) (take n (drop k ys)) -∗ string p b reg ys).
Proof.
  intros Hk. iIntros "[%Hok Hs]".
  assert (E : ys ++ [0] = take k ys ++ take n (drop k ys) ++ (drop (k + n) ys ++ [0])).
  { rewrite app_assoc app_assoc. f_equal. rewrite -{1}(take_drop k ys). rewrite -app_assoc. f_equal.
    rewrite -{1}(take_drop n (drop k ys)) drop_drop. reflexivity. }
  assert (Lk : length (take k ys) = k) by (rewrite length_take; lia).
  rewrite /string_ps E !byte_ps_app Lk.
  rewrite /live /bytes /pts big_sepL_cons !big_sepL_app big_sepL_singleton.
  iDestruct "Hs" as "(Hl & Hpre & Hw & Hpost)". iSplit; [done|]. iFrame "Hl Hw".
  iIntros "Hl Hw". rewrite /string. iSplit; [done|]. rewrite /string_ps E !byte_ps_app Lk.
  rewrite /pts big_sepL_cons !big_sepL_app. iFrame.
Qed.

Section calls.
Context {world : Type} (registry : name -> option (contract world))
  (wi : mem -> world -> gmap piece pval -> Prop) `{!SafepointStable wi} (ge : genv).

(** The instance [mem_irisGS] equips these memory rules with the chosen
    contract registry and the interpretation of external-library state. *)
Local Instance mem_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry wi ge.

(** The notation [mexpr] names expressions in this language, keeping
    the selected contract registry implicit in the memory rules below. *)
Local Notation mexpr := (language.expr (nanofil_lang registry ge)).

(** A raw 32-bit store replaces four owned bytes with the integer's
    little-endian representation and returns ownership of that updated range.
    The rule [wp_raw_store_w] requires the object's lifetime and a
    proof that updating these bytes preserves the external-world interpretation. *)
Lemma wp_raw_store_w f e ls l off v a rest j p b reg o xs y Φ :
  value_x ge e W v = Some (WInt y) -> value_x ge e A a = Some (WPtr p) ->
  ptr_cap p = Obj b -> raw_address (ptr_addr p) off = b + o -> length xs = 4%nat ->
  (forall m wd h, (forall l v, (l, v) ∈ (PLive b, VLive reg) :: byte_ps b o xs -> h !! l = Some v) ->
     wi m wd h ->
     wi (store_bytes m (b + o) 4 y) wd (overwrite ((PLive b, VLive reg) :: byte_ps b o (le_bytes y 4)) h)) ->
  live b reg -∗ bytes b o xs -∗
  ▷ (live b reg -∗ bytes b o (le_bytes y 4) -∗ WP (ERun (mkFrame f e ls None (Exec l rest j)) : mexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (RawStore Ww off v a :: rest) j)) : mexpr) {{ Φ }}.
Proof.
  intros Hv Ha Hp Hoff Hlen Hwi. iIntros "Hl Hx HK".
  iApply (wp_write _ _ _ ((PLive b, VLive reg) :: byte_ps b o xs) ((PLive b, VLive reg) :: byte_ps b o (le_bytes y 4))
            _ _ [] (fun m => store_bytes m (b + o) 4 y) with "[Hl Hx] [HK]");
    [cbn [fmap list_fmap fst]; rewrite !byte_ps_keys length_le_bytes Hlen; reflexivity | | exact Hwi |
     rewrite /live /bytes /pts !big_sepL_cons big_sepL_nil; iFrame; iDestruct "Hl" as "[$ _]" |].
  - intros m fuel (Hf & Hd & _). cbn [all_agree agree_piece fst snd] in Hf. destruct Hf as [Hlv Hx].
    destruct (store_after m b reg o xs y Hd Hlv Hx) as [Hag Hfr]. rewrite Hlen in Hag Hfr. cbn in Hag, Hfr.
    assert (Hb : forall i, (i < 4)%nat -> 0 <= o + Z.of_nat i /\ b + (o + Z.of_nat i) < r_end reg).
    { intros i Hi. rewrite <- Hlen in Hi. destruct (lookup_lt_is_Some_2 xs i Hi) as [x Hxi].
      destruct (byte_ps_agree _ _ _ _ _ _ _ Hlv Hx Hxi) as (_ & H1 & H2). lia. }
    destruct (Hb 0%nat ltac:(lia)) as [H0 _]. destruct (Hb 3%nat ltac:(lia)) as [_ H3]. cbn in H0, H3.
    split; [|split; [reflexivity|split; [|split]]].
    + apply rule_raw_store with (vk := W) (x := WInt y) (p := p); [reflexivity | exact Hv | exact Ha |].
      rewrite Hoff. cbn - [access_res store_bytes]. rewrite Hp.
      rewrite (access_obj _ _ reg); [reflexivity | exact (proj1 Hlv) | lia | lia | apply Z.mod_1_r].
    + apply store_bytes_kept. intros a' Ha'. exists b, reg. split; [exact (proj1 Hlv)|lia].
    + cbn [all_agree agree_piece fst snd]. split; [exact Hlv | exact Hag].
    + intros l' v' Hn Ha'. apply Hfr; [|exact Ha'].
      intros Hin. apply Hn. cbn [fmap list_fmap fst]. apply elem_of_cons. right.
      rewrite byte_ps_keys length_le_bytes. rewrite byte_ps_keys Hlen in Hin. exact Hin.
  - iNext. iIntros "H".
    iDestruct (pts_app [(PLive b, VLive reg)] (byte_ps b o (le_bytes y 4)) with "H") as "[Hl Hx]".
    iApply ("HK" with "Hl Hx").
Qed.

(** A narrow raw load reads owned bytes as a little-endian integer,
    extends it to the result class, and preserves the byte values.
    The rule [wp_raw_load_sub_bytes_dq] accepts shared ownership of both
    the object lifetime and the bytes, through writable or read-only capabilities. *)
Lemma wp_raw_load_sub_bytes_dq f e ls l d k n off args rest j classes p b reg o bs y dq1 dq2 Φ :
  op_arg_classes (RawLoad (LdNarrow n) off) k = Some classes ->
  map2_option (value_x ge e) classes args = Some [WPtr p] ->
  length bs = Z.to_nat (fst (narrow_type n)) -> extended n k (of_bytes bs) = Some y ->
  ptr_cap p = Obj b \/ ptr_cap p = Ro b -> raw_address (ptr_addr p) off = b + o ->
  liveq dq1 b reg -∗ bytesq dq2 b o bs -∗
  ▷ (liveq dq1 b reg -∗ bytesq dq2 b o bs -∗
     WP (ERun (mkFrame f (put d y e) ls None (Exec l rest j)) : mexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (Let d k (RawLoad (LdNarrow n) off) args :: rest) j)) : mexpr)
    {{ Φ }}.
Proof.
  intros Hc Hx Hlen Hy Hp Ha. iIntros "Hl Hb HK".
  assert (Hn : Z.of_nat (length bs) = fst (narrow_type n)) by (rewrite Hlen; destruct n; reflexivity).
  iApply (wp_read_with _ _ _ (liveq dq1 b reg ∗ bytesq dq2 b o bs)
            (fun m => live_at m b reg /\ all_agree m (byte_ps b o bs)) _ _ [] with "[$Hl $Hb] [HK]").
  - iIntros (σ) "Hσ [Hl Hb]".
    iDestruct (ptsq_facts with "Hσ Hl") as %([Hlv _] & _).
    iDestruct (ptsq_facts with "Hσ Hb") as %(Hbs & _). iPureIntro. auto.
  - intros m fuel (Hlv & Hbs).
    destruct (lookup_lt_is_Some_2 bs 0 ltac:(destruct n; cbn in Hlen; lia)) as [x0 H0].
    destruct (lookup_lt_is_Some_2 bs (length bs - 1) ltac:(destruct n; cbn in Hlen; lia)) as [x1 H1].
    destruct (byte_ps_agree _ _ _ _ _ _ _ Hlv Hbs H0) as (_ & Hlo & _).
    destruct (byte_ps_agree _ _ _ _ _ _ _ Hlv Hbs H1) as (_ & _ & Hhi).
    apply rule_let with (classes := classes) (xs := [WPtr p]); [reflexivity | exact Hc | exact Hx |].
    rewrite (op_raw_load_narrow m k n p off).
    + rewrite Ha -Hn (bytes_load m b reg o bs Hlv Hbs) Hy. reflexivity.
    + rewrite Ha. apply (access_read _ b reg); [exact Hp | exact (proj1 Hlv) | lia | lia | apply Z.mod_1_r].
  - iNext. iIntros "[Hl Hb]". iApply ("HK" with "Hl Hb").
Qed.

(** Integer compare-and-swap returns the old value and writes the new
    integer only when the stored bytes match the width-wrapped expected value.
    The rule [wp_raw_cas_int] requires exclusive byte ownership, an
    address aligned to the access width, and preservation of the world on success.
    A failed comparison returns the same owned bytes unchanged; this
    rule covers long and narrow integer accesses, not pointer compare-and-swap. *)
Lemma wp_raw_cas_int f e ls l d k t off args rest j classes p b reg o bs ev nv old Φ :
  t <> CasP -> length bs = Z.to_nat (cas_bytes t) ->
  op_arg_classes (RawCas t off) k = Some classes ->
  map2_option (value_x ge e) classes args = Some [WPtr p; WInt ev; WInt nv] ->
  ptr_cap p = Obj b -> raw_address (ptr_addr p) off = b + o -> (b + o) mod cas_bytes t = 0 ->
  cas_old t k (of_bytes bs) = Some old ->
  (of_bytes bs = ev mod 2 ^ (8 * cas_bytes t) -> forall m wd h,
     (forall l v, (l, v) ∈ (PLive b, VLive reg) :: byte_ps b o bs -> h !! l = Some v) -> wi m wd h ->
     wi (store_bytes m (b + o) (cas_bytes t) nv) wd
       (overwrite ((PLive b, VLive reg) :: byte_ps b o (le_bytes nv (length bs))) h)) ->
  live b reg -∗ bytes b o bs -∗
  ▷ (live b reg -∗
     bytes b o (if of_bytes bs =? ev mod 2 ^ (8 * cas_bytes t) then le_bytes nv (length bs) else bs) -∗
     WP (ERun (mkFrame f (put d old e) ls None (Exec l rest j)) : mexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (Let d k (RawCas t off) args :: rest) j)) : mexpr) {{ Φ }}.
Proof.
  intros Ht Hlen Hc Hx Hp Ha Hal Hold Hwi. iIntros "Hl Hb HK".
  assert (Hsz : 0 < cas_bytes t) by (destruct t as [| |[]]; cbn; lia).
  assert (Hn : Z.of_nat (length bs) = cas_bytes t) by lia.
  assert (Hop : forall m, live_at m b reg -> all_agree m (byte_ps b o bs) ->
    op_res (RawCas t off) k [WPtr p; WInt ev; WInt nv] m =
    Some (OpRes (RVal old)
      (if of_bytes bs =? ev mod 2 ^ (8 * cas_bytes t) then store_bytes m (b + o) (cas_bytes t) nv else m))).
  { intros m Hlv Hbs.
    assert (Hld : load_bytes m (b + o) (cas_bytes t) = of_bytes bs)
      by (rewrite <- Hn; exact (bytes_load m b reg o bs Hlv Hbs)).
    destruct (lookup_lt_is_Some_2 bs 0 ltac:(lia)) as [x0 H0].
    destruct (lookup_lt_is_Some_2 bs (length bs - 1) ltac:(lia)) as [x1 H1].
    destruct (byte_ps_agree _ _ _ _ _ _ _ Hlv Hbs H0) as (_ & Hlo & _).
    destruct (byte_ps_agree _ _ _ _ _ _ _ Hlv Hbs H1) as (_ & _ & Hhi).
    rewrite (op_raw_cas_int m t k p off ev nv old Ht).
    - rewrite Ha Hld. reflexivity.
    - rewrite Hp Ha. apply (access_obj _ _ reg); [exact (proj1 Hlv) | lia | lia | exact Hal].
    - rewrite Ha Hld. exact Hold. }
  destruct (of_bytes bs =? ev mod 2 ^ (8 * cas_bytes t)) eqn:Eq.
  - iApply (wp_write _ _ _ ((PLive b, VLive reg) :: byte_ps b o bs)
              ((PLive b, VLive reg) :: byte_ps b o (le_bytes nv (length bs)))
              _ _ [] (fun m => store_bytes m (b + o) (cas_bytes t) nv) with "[Hl Hb] [HK]");
      [cbn [fmap list_fmap fst]; rewrite !byte_ps_keys length_le_bytes; reflexivity | |
       exact (Hwi (proj1 (Z.eqb_eq _ _) Eq)) |
       rewrite /live /bytes /pts !big_sepL_cons big_sepL_nil; iFrame; iDestruct "Hl" as "[$ _]" |].
    + intros m fuel (Hf & Hd & _). cbn [all_agree agree_piece fst snd] in Hf. destruct Hf as [Hlv Hbs].
      destruct (store_after m b reg o bs nv Hd Hlv Hbs) as [Hag Hfr]. rewrite Hn in Hag Hfr.
      destruct (lookup_lt_is_Some_2 bs 0 ltac:(lia)) as [x0 H0].
      destruct (lookup_lt_is_Some_2 bs (length bs - 1) ltac:(lia)) as [x1 H1].
      destruct (byte_ps_agree _ _ _ _ _ _ _ Hlv Hbs H0) as (_ & Hlo & _).
      destruct (byte_ps_agree _ _ _ _ _ _ _ Hlv Hbs H1) as (_ & _ & Hhi).
      split; [|split; [reflexivity|split; [|split]]].
      * apply rule_let with (classes := classes) (xs := [WPtr p; WInt ev; WInt nv]);
          [reflexivity | exact Hc | exact Hx |]. rewrite (Hop m Hlv Hbs); rewrite ?Eq; reflexivity.
      * apply store_bytes_kept. intros a' Ha'. exists b, reg. split; [exact (proj1 Hlv)|lia].
      * cbn [all_agree agree_piece fst snd]. split; [exact Hlv | exact Hag].
      * intros l' v' Hn' Ha'. apply Hfr; [|exact Ha'].
        intros Hin. apply Hn'. cbn [fmap list_fmap fst]. apply elem_of_cons. right.
        rewrite byte_ps_keys length_le_bytes. rewrite byte_ps_keys in Hin. exact Hin.
    + iNext. iIntros "H".
      iDestruct (pts_app [(PLive b, VLive reg)] (byte_ps b o (le_bytes nv (length bs))) with "H") as "[Hl Hb]".
      iApply ("HK" with "Hl Hb").
  - iApply (wp_read _ _ _ ((PLive b, VLive reg) :: byte_ps b o bs) _ _ [] with "[Hl Hb] [HK]").
    + intros m fuel (Hf & _). cbn [all_agree agree_piece fst snd] in Hf. destruct Hf as [Hlv Hbs].
      apply rule_let with (classes := classes) (xs := [WPtr p; WInt ev; WInt nv]);
        [reflexivity | exact Hc | exact Hx |]. rewrite (Hop m Hlv Hbs); rewrite ?Eq; reflexivity.
    + rewrite /live /bytes /pts !big_sepL_cons big_sepL_nil. iFrame. iDestruct "Hl" as "[$ _]".
    + iNext. iIntros "H".
      iDestruct (pts_app [(PLive b, VLive reg)] (byte_ps b o bs) with "H") as "[Hl Hb]".
      iApply ("HK" with "Hl Hb").
Qed.

(** Glibc's locks compare and replace a four-byte integer at an address
    divisible by four, returning the previous 32-bit value.
    The rule [wp_raw_cas_w] specializes integer compare-and-swap to that
    case, accepting either signed or unsigned narrow-word operations. *)
Lemma wp_raw_cas_w f e ls l d nt off args rest j classes p b reg o bs ev nv Φ :
  nt = Sw \/ nt = Uw -> length bs = 4%nat ->
  op_arg_classes (RawCas (CasNarrow nt) off) W = Some classes ->
  map2_option (value_x ge e) classes args = Some [WPtr p; WInt ev; WInt nv] ->
  ptr_cap p = Obj b -> raw_address (ptr_addr p) off = b + o -> (b + o) mod 4 = 0 ->
  (of_bytes bs = ev mod 2 ^ 32 -> forall m wd h,
     (forall l v, (l, v) ∈ (PLive b, VLive reg) :: byte_ps b o bs -> h !! l = Some v) -> wi m wd h ->
     wi (store_bytes m (b + o) 4 nv) wd (overwrite ((PLive b, VLive reg) :: byte_ps b o (le_bytes nv 4)) h)) ->
  live b reg -∗ bytes b o bs -∗
  ▷ (live b reg -∗ bytes b o (if of_bytes bs =? ev mod 2 ^ 32 then le_bytes nv 4 else bs) -∗
     WP (ERun (mkFrame f (put d (WInt (of_bytes bs mod 2 ^ 32)) e) ls None (Exec l rest j)) : mexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (Let d W (RawCas (CasNarrow nt) off) args :: rest) j)) : mexpr) {{ Φ }}.
Proof.
  intros Hnt Hlen Hc Hx Hp Ha Hal Hwi. iIntros "Hl Hb HK".
  assert (Hs : cas_bytes (CasNarrow nt) = 4) by (destruct Hnt as [-> | ->]; reflexivity).
  iApply (wp_raw_cas_int _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (WInt (of_bytes bs mod 2 ^ 32))
            with "Hl Hb [HK]"); [discriminate | rewrite Hs; exact Hlen | exact Hc | exact Hx | exact Hp |
                                exact Ha | rewrite Hs; exact Hal | | |].
  - unfold cas_old, extended, extension. cbn [modulus]. destruct Hnt as [-> | ->]; [|by rewrite Z.mod_mod].
    unfold sign_extension. destruct (_ <=? _); [|by rewrite Z.mod_mod]. f_equal. f_equal.
    rewrite Zminus_mod Z_mod_same_full Z.sub_0_r !Z.mod_mod; lia.
  - rewrite Hs Hlen. exact Hwi.
  - iNext. rewrite Hs Hlen. iExact "HK".
Qed.

End calls.
End mem.
End MemLogicOn.

(** The module [MemLogic] creates its own program-logic instance and
    supplies the buffer assertions and instruction rules from [MemLogicOn]. *)
Module MemLogic (R : Runtime).
Module LG0 := Logic R.
Include MemLogicOn R LG0.
End MemLogic.
