(** Filling or copying a C buffer can change both its bytes and the
    hidden capabilities attached to pointers stored there.
    This module describes ownership of both kinds of storage and
    derives calling rules from the earlier libc [[external-call|contracts]].
    It uses [Logic](Logic.v) and the string assertions from
    [StringLogic](StringLogic.v), rather than proving libc's implementations here.

    Copying a stored pointer must transfer its hidden capability as
    well as its address bytes, while clearing memory must remove that capability.
    The assertions [bytes] and [auxes] separately own these data bytes
    and shadow [[aux]] slots, letting the calling rules describe both changes.
    A partially copied pointer slot becomes empty, preventing the copy
    from manufacturing a capability from an incomplete pointer representation.

    The block-copy rules require eight-byte-aligned bases and offsets,
    so every touched pointer slot begins inside the owned block.
    Their contracts also allow unaligned buffers, but these particular
    ownership rules do not cover a slot beginning before the buffer.
    Scalar string copies preserve all shadow slots, so their rules
    require only byte ownership and impose no such alignment condition.

    The remaining rules describe fresh allocation, string duplication,
    bounded searches, integer loads and stores, and integer [[cas|compare-and-swap]].
    Each rule returns the caller's untouched ownership and updates only
    the pieces that the operation is allowed to write.
    In particular, the malloc contract used here never returns null;
    allocation failure ends execution with a permitted resource refusal instead. *)

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

(** A scalar string copy replaces destination bytes through the NUL,
    preserves every shadow slot, and needs no pointer-slot alignment.
    The lemma [copy_string_after] records the copied bytes and keeps
    every owned piece outside the destination byte range valid. *)
Lemma copy_string_after m m' b reg o xs src b' reg' ys :
  live_disjoint m -> live_at m b reg -> all_agree m (byte_ps b o xs) -> length xs = S (length ys) ->
  string_ok src b' reg' ys -> all_agree m (string_ps src b' reg' ys) ->
  string_copy_result m (mkPtr (b + o) (Obj b)) src (Z.of_nat (length ys) + 1) m' ->
  all_agree m' (byte_ps b o (ys ++ [0])) /\ frame_ok (byte_ps b o xs).*1 m m'.
Proof.
  intros Hd Hl Hx Hlen Hok Hs ((Hr & Haux & Hbytes) & Hcopy).
  assert (Hbyte : forall i, (i < length xs)%nat -> 0 <= o + Z.of_nat i /\ b + (o + Z.of_nat i) < r_end reg).
  { intros i Hi. destruct (lookup_lt_is_Some_2 xs i Hi) as [x Hxi].
    destruct (byte_ps_agree _ _ _ _ _ _ _ Hl Hx Hxi) as (_ & H1 & H2). lia. }
  split.
  - apply all_agree_intro. intros l v Hin.
    apply byte_ps_elem in Hin as (i & x & Hxi & -> & ->).
    assert (Hi : (i < length xs)%nat).
    { apply lookup_lt_Some in Hxi. rewrite length_app in Hxi. cbn in Hxi. lia. }
    destruct (lookup_lt_is_Some_2 xs i Hi) as [x0 Hx0].
    pose proof (all_agree_elem _ _ _ _ Hx (list_elem_of_lookup_2 _ _ _ (byte_ps_lookup b o xs i x0 Hx0)))
      as [Hreg _].
    cbn [agree_piece]. split; [unfold registered in *; rewrite Hr; exact Hreg|]. intros reg0 E L.
    destruct Hl as [E0 _]. rewrite Hr E0 in E. injection E as <-.
    destruct (Hbyte i Hi) as [H1 H2]. split; [exact H1|]. split; [exact H2|].
    rewrite Hcopy; [|unfold span_contains; cbn; lia]. cbn [ptr_addr].
    replace (ptr_addr src + (b + (o + Z.of_nat i) - (b + o))) with (ptr_addr src + Z.of_nat i) by lia.
    exact (string_bytes _ _ _ _ _ Hok Hs i x Hxi).
  - apply (frame_within _ _ _ b reg); [exact Hr | exact Hd | exact Hl | | intros a _; apply Haux].
    intros a H. apply Hbytes. intros Hsp. unfold span_contains in Hsp. cbn in Hsp.
    destruct (Hbyte (Z.to_nat (a - b - o)) ltac:(lia)) as [H1 H2].
    apply H; [lia|]. replace (a - b) with (o + (a - b - o)) by lia. apply byte_ps_key. lia.
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

(** ## Searching a string for its NUL

    A search for zero stops at the first NUL and need not read the
    rest of the caller's stated search range.
    The following facts let a caller use string ownership even when
    that range extends beyond the string's enclosing object. *)

(** Searching a bounded string for zero reads through its NUL or the
    bound, whichever comes first, and never requires bytes after a match.
    The lemma [memchr_input_bounded] turns that readable prefix into the
    memory-search contract's precondition for a zero low byte. *)
Lemma memchr_input_bounded m p c n k :
  0 <= c < 2 ^ 32 -> c mod 256 = 0 -> bounded_length m p n k -> memchr_input m p c n.
Proof.
  intros Hc H0 (Hn & Hk & Hlife & Ha & Hpos & Hnul).
  split; [exact Hc|]. split; [exact Hn|]. exists k. split; [exact Hk|]. rewrite H0. split.
  - split; [destruct (k <? n) eqn:E; [apply Z.ltb_lt in E | apply Z.ltb_ge in E]; lia|].
    split; [exact Hlife|]. split; [exact Ha|].
    destruct (k <? n) eqn:E; intros i Hi.
    + apply Z.ltb_lt in E. destruct (Z.lt_ge_cases i k) as [Hik|Hik]; [specialize (Hpos i ltac:(lia)); lia|].
      replace i with k by lia. rewrite (Hnul E). lia.
    + specialize (Hpos i ltac:(lia)). lia.
  - split; [|exact Hnul]. intros i Hi. specialize (Hpos i Hi). lia.
Qed.

(** A bounded zero search returns the terminator with the string's
    capability only when the terminator lies strictly before the bound.
    The function [nul_found] returns null otherwise, including when the
    bound equals the number of nonzero string bytes. *)
Definition nul_found (p : ptr) (bytes : list Z) (n : Z) : ptr :=
  if Z.of_nat (length bytes) <? n then mkPtr (ptr_addr p + Z.of_nat (length bytes)) (ptr_cap p)
  else mkPtr 0 CNone.

(** No byte before a string's terminator matches zero, so any contracted
    zero-search result must equal [nul_found] for the supplied bound. *)
Lemma memchr_result_string m p b reg bytes c n q :
  string_ok p b reg bytes -> all_agree m (string_ps p b reg bytes) -> c mod 256 = 0 ->
  memchr_result m p c n q -> q = nul_found p bytes n.
Proof.
  intros Hok Ha H0 Hq. pose proof (string_bytes m p b reg bytes Hok Ha) as Hb.
  pose proof Hok as (_ & _ & _ & _ & _ & Hf). unfold memchr_result in Hq. rewrite H0 in Hq. unfold nul_found.
  assert (Hnz : forall i, 0 <= i < Z.of_nat (length bytes) -> m_bytes m (ptr_addr p + i) <> 0).
  { intros i Hi. destruct (lookup_lt_is_Some_2 bytes (Z.to_nat i) ltac:(lia)) as [x Hx].
    rewrite <- (Z2Nat.id i) by lia. rewrite (Hb (Z.to_nat i) x); [|by apply lookup_app_l_Some].
    pose proof (Forall_lookup_1 _ _ _ _ Hf Hx) as Hx0. cbv beta in Hx0. lia. }
  assert (Hz : m_bytes m (ptr_addr p + Z.of_nat (length bytes)) = 0).
  { apply (Hb (length bytes) 0). rewrite lookup_app_r; [|lia]. rewrite Nat.sub_diag. reflexivity. }
  destruct Hq as [(k & Hk & Hvk & Hbefore & ->) | (Hmiss & ->)].
  - assert (Hkl : k = Z.of_nat (length bytes)).
    { destruct (Z.lt_trichotomy k (Z.of_nat (length bytes))) as [Hl|[Hl|Hl]].
      - exfalso. apply (Hnz k); [lia | exact Hvk].
      - exact Hl.
      - exfalso. apply (Hbefore (Z.of_nat (length bytes))); [lia | exact Hz]. }
    subst k. rewrite (proj2 (Z.ltb_lt _ _) (proj2 Hk)). reflexivity.
  - destruct (Z.of_nat (length bytes) <? n) eqn:E; [|reflexivity].
    apply Z.ltb_lt in E. exfalso. apply (Hmiss (Z.of_nat (length bytes))); [lia | exact Hz].
Qed.

(** The module [MemLogicOn] builds buffer ownership and memory-call rules
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

(** Calling memset fills an owned block with the character's low byte,
    clears touched pointer capabilities, and returns the destination pointer.
    The rule [wp_memset] requires an eight-byte-aligned base and offset,
    ownership of the bytes and shadow slots, and sufficient object bounds.
    The caller must also show that this fill preserves the chosen
    interpretation of external-library state. *)
Lemma wp_memset f e ls lab d vp vc vn rest j b reg o xs cs c Φ :
  registry (TAtom "memset") = Some (memset_contract world) ->
  find_fn ge (TAtom "memset") = None -> lookup (TAtom "memset") (ge_globals ge) = None ->
  arg_x ge e (Arg P vp) = Some (WPtr (mkPtr (b + o) (Obj b))) -> arg_x ge e (Arg W vc) = Some (WInt c) ->
  arg_x ge e (Arg L vn) = Some (WInt (Z.of_nat (length xs))) ->
  0 <= c < 2 ^ 32 -> b mod 8 = 0 -> o mod 8 = 0 -> 0 <= o -> b + o + Z.of_nat (length xs) <= r_end reg ->
  length cs = length xs ->
  (forall m m' wd h, memset_result m (mkPtr (b + o) (Obj b)) c (Z.of_nat (length xs)) m' ->
     (forall l v, (l, v) ∈ block_ps b reg o xs cs -> h !! l = Some v) -> wi m wd h ->
     wi m' wd (overwrite (block_ps b reg o (replicate (length xs) (c mod 256)) (clear_slots o cs)) h)) ->
  live b reg -∗ bytes b o xs -∗ auxes b o cs -∗
  ▷ (live b reg -∗ bytes b o (replicate (length xs) (c mod 256)) -∗ auxes b o (clear_slots o cs) -∗
     WP (ERun (mkFrame f (put d (WPtr (mkPtr (b + o) (Obj b))) e) ls None (Exec lab rest j)) : mexpr)
       {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
             (Exec lab (Call (CResult d P) (Global (TAtom "memset")) [Arg P vp; Arg W vc; Arg L vn] :: rest) j))
        : mexpr) {{ Φ }}.
Proof.
  intros Hreg Hfn Hdata Hp Hc Hn Hc32 Hb8 Ho8 Ho Hend Hlen Hwi. iIntros "Hl Hx Hcs HK".
  iDestruct (block_pts b reg o xs cs with "[$Hl $Hx $Hcs]") as "Hps".
  iApply (wp_external _ _ _ _ _ _ _ _ _ _ _ _ (memset_contract world)
            [WPtr (mkPtr (b + o) (Obj b)); WInt c; WInt (Z.of_nat (length xs))] (pts (block_ps b reg o xs cs)) with "Hps [HK]");
    [done | done | done | done | cbn [map_option]; rewrite Hp Hc Hn; done | | |].
  - split; [right; eexists; reflexivity | do 3 eexists; reflexivity].
  - iIntros (σ) "Hσ Hps". iDestruct (pts_facts with "Hσ Hps") as %(Ha & _ & Hfit). iPureIntro.
    destruct Ha as [[E L] _]. cbn [fst snd] in E, L.
    destruct (Hfit b reg E) as [Hb0 Hfit'].
    eexists _, c, _. split; [reflexivity|]. split; [exact Hc32|]. split; [lia|]. split.
    + unfold writable_span. cbn [span_ptr span_size ptr_addr ptr_cap].
      split; [lia|]. exists b, reg. split; [reflexivity|]. split; [exact E|]. split; [exact L|].
      apply (access_obj _ _ reg); [exact E | lia | lia | apply Z.mod_1_r].
    + right. exists b. auto.
  - iNext. iIntros (σ trace values s' m' w' Hinv) "(%h & Hh & %Hf) Hps".
    destruct Hf as (Ha & Hd & Hr & Hw).
    destruct (M.E.memset_invocation _ _ _ _ _ _ _ _ _ _ _ _ Hinv)
      as (_ & -> & p' & c' & n' & Hx & _ & Hres & He).
    injection Hx as <- <- <-. injection He as ->.
    iDestruct (pts_lookup with "Hh Hps") as %Hlk.
    assert (Hold : all_agree (ls_mem σ) (block_ps b reg o xs cs)).
    { apply all_agree_intro. intros l v Hin. exact (Ha l v (Hlk l v Hin)). }
    destruct Hold as [Hlv Hold]. cbn [agree_piece fst snd] in Hlv.
    destruct (fill_after (ls_mem σ) m' b reg o xs cs c Hd Hlv Hb8 Ho8 Hlen Hold Hres) as [Hnew Hfr].
    destruct (M.E.invoke_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ Hinv) as (born & Hpre).
    destruct (M.E.prefix_preserve _ _ _ _ _ _ _ _ _ _ _ Hpre Hr) as [Hr' _].
    pose proof Hres as ((Hregs & _) & _).
    iMod (pts_update _ _ (block_ps b reg o (replicate (length xs) (c mod 256)) (clear_slots o cs))
            with "Hh Hps") as "[Hh Hps]".
    { apply block_ps_keys; [apply length_replicate | apply length_clear_slots]. }
    iModIntro. iExists _. iSplit; [iPureIntro; reflexivity|].
    iSplitL "Hh".
    + iExists _. iFrame "Hh". iPureIntro. cbn [ls_mem ls_rt ls_world]. split; [|split; [|split]].
      * intros l v Hl'. destruct (lookup_overwrite _ _ _ _ Hl') as [Hin | [Hnk Hh]].
        -- apply elem_of_cons in Hin as [Hin|Hin].
           ++ injection Hin as -> ->. cbn [agree_piece]. exact (live_at_regions _ _ _ _ Hregs Hlv).
           ++ exact (all_agree_elem _ _ _ _ Hnew Hin).
        -- apply Hfr; [|exact (Ha l v Hh)]. intros Hk. apply Hnk.
           rewrite (block_ps_keys b reg o xs cs) ; [|apply length_replicate | apply length_clear_slots].
           cbn [fmap list_fmap fst block_ps]. right. exact Hk.
      * exact (live_disjoint_regions _ _ Hregs Hd).
      * exact Hr'.
      * exact (Hwi _ _ _ _ Hres Hlk Hw).
    + rewrite block_pts. iDestruct "Hps" as "(Hl & Hx & Hcs)". iApply ("HK" with "Hl Hx Hcs").
Qed.

(** Calling malloc returns ownership of a fresh heap object whose
    requested size is rounded up to a multiple of sixteen bytes.
    The rule [wp_malloc] has no null-return case because this contract
    treats allocation refusal as a resource ending, not a return.
    The caller must show that adding the allocated object's owned
    pieces preserves its interpretation of external-library state. *)
Lemma wp_malloc f e ls lab d v rest j n Φ :
  registry (TAtom "malloc") = Some (malloc_contract world) ->
  find_fn ge (TAtom "malloc") = None -> lookup (TAtom "malloc") (ge_globals ge) = None ->
  arg_x ge e (Arg L v) = Some (WInt n) -> 0 <= n < 2 ^ 64 ->
  (forall m wd h base, fresh m (heap_req 16 n) base -> wi m wd h ->
     wi (allocated m (heap_req 16 n) base) wd (overwrite (obj_ps base (heap_req 16 n)) h)) ->
  ▷ (∀ base, ⌜0 < base /\ base mod 16 = 0 /\ base + req_extent (heap_req 16 n) <= 2 ^ 48 /\
               n <= max_allocation_size⌝ -∗
       obj base (heap_req 16 n) -∗
       WP (ERun (mkFrame f (put d (WPtr (mkPtr base (Obj base))) e) ls None (Exec lab rest j)) : mexpr)
         {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
             (Exec lab (Call (CResult d P) (Global (TAtom "malloc")) [Arg L v] :: rest) j)) : mexpr)
    {{ Φ }}.
Proof.
  intros Hreg Hfn Hdata Hv Hn Hwi. iIntros "HK".
  iApply (wp_external _ _ _ _ _ _ _ _ _ _ _ _ (malloc_contract world) [WInt n] True%I with "[//] [HK]");
    [done | done | done | done | cbn [map_option]; rewrite Hv; done | | |].
  - split; [right; eexists; reflexivity | eexists; reflexivity].
  - iIntros (σ) "_ _". iPureIntro. exists n. auto.
  - iNext. iIntros (σ trace values s' m' w' Hinv) "(%h & Hh & %Hf) _".
    destruct Hf as (Ha & Hd & Hr & Hw).
    destruct (M.E.invoke_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ Hinv) as (born & Hp).
    destruct (M.E.prefix_preserve _ _ _ _ _ _ _ _ _ _ _ Hp Hr) as [Hr' _].
    destruct (M.E.malloc_invocation _ _ _ _ _ _ _ _ _ _ _ _ Hinv)
      as (_ & -> & n' & Hx & _ & [(base & Hres & He) | (why & born' & He & _)]); [|discriminate He].
    injection Hx as <-. injection He as ->. destruct Hres as (Hmax & Hfr & ->).
    assert (Hex : 0 <= req_extent (heap_req 16 n)).
    { cbn. apply Z.mul_nonneg_nonneg; [apply Z.div_pos|]; lia. }
    pose proof Hfr as (Hpos & Hmod & _ & Hnone & _).
    iMod (pts_alloc h (obj_ps base (heap_req 16 n)) with "Hh") as "[Hh Hps]".
    { apply obj_ps_nodup. }
    { intros l' v' Hin. destruct (h !! l') as [v0|] eqn:E; [|reflexivity]. exfalso.
      pose proof (agree_piece_registered _ _ _ (obj_ps_mem _ _ _ _ Hin) (Ha l' v0 E)) as Hreg'.
      rewrite (obj_ps_id _ _ _ _ Hin) in Hreg'. exact (Hreg' Hnone). }
    iModIntro. iExists _. iSplit; [iPureIntro; reflexivity|].
    iSplitL "Hh".
    + iExists _. iFrame "Hh". iPureIntro. cbn [ls_mem ls_rt ls_world]. split; [|split; [|split]].
      * intros l' v' Hl. destruct (lookup_overwrite _ _ _ _ Hl) as [Hin | [_ Hh]].
        -- exact (obj_ps_agree _ _ _ _ _ Hfr Hex Hin).
        -- exact (agree_piece_allocated _ _ _ _ _ Hnone (Ha l' v' Hh)).
      * exact (live_disjoint_allocated _ _ _ Hd Hfr Hex).
      * exact Hr'.
      * exact (Hwi _ _ _ _ Hfr Hw).
    + iApply ("HK" with "[%] Hps"). split; [exact Hpos|]. split; [exact Hmod|]. split; [|exact (proj2 Hmax)].
      destruct (R.address_space _ _ Hr' base
                  (mkRegion base (base + req_extent (heap_req 16 n)) (req_kind (heap_req 16 n)) Live))
        as [_ Hend]; [rewrite object_region_allocated Z.eqb_refl; reflexivity|].
      cbn [r_end] in Hend. exact Hend.
Qed.

(** Calling memcpy copies bytes and complete pointer capabilities into
    an owned destination, returns its pointer, and preserves the source ownership.
    The rule [wp_memcpy] requires distinct objects and equally sized
    blocks, with both bases and offsets aligned to eight bytes.
    Partially copied pointer slots become empty, and the caller must
    show that the destination update preserves the external-world interpretation. *)
Lemma wp_memcpy f e ls lab d vd vs vn rest j b reg o xs cs b' reg' o' c' ys ds Φ :
  registry (TAtom "memcpy") = Some (memcpy_contract world) ->
  find_fn ge (TAtom "memcpy") = None -> lookup (TAtom "memcpy") (ge_globals ge) = None ->
  arg_x ge e (Arg P vd) = Some (WPtr (mkPtr (b + o) (Obj b))) ->
  arg_x ge e (Arg P vs) = Some (WPtr (mkPtr (b' + o') c')) -> c' = Obj b' \/ c' = Ro b' ->
  arg_x ge e (Arg L vn) = Some (WInt (Z.of_nat (length xs))) ->
  b <> b' -> b mod 8 = 0 -> o mod 8 = 0 -> b' mod 8 = 0 -> o' mod 8 = 0 -> 0 <= o -> 0 <= o' ->
  b + o + Z.of_nat (length xs) <= r_end reg -> b' + o' + Z.of_nat (length xs) <= r_end reg' ->
  length ys = length xs -> length cs = length xs -> length ds = length xs ->
  Forall (fun y => 0 <= y < 256) ys ->
  (forall m m' wd h, copy_result m (mkPtr (b + o) (Obj b)) (mkPtr (b' + o') c') (Z.of_nat (length xs)) m' ->
     (forall l v, (l, v) ∈ block_ps b reg o xs cs -> h !! l = Some v) -> wi m wd h ->
     wi m' wd (overwrite (block_ps b reg o ys (copy_slots (Z.of_nat (length xs)) ds cs)) h)) ->
  live b reg -∗ bytes b o xs -∗ auxes b o cs -∗ live b' reg' -∗ bytes b' o' ys -∗ auxes b' o' ds -∗
  ▷ (live b reg -∗ bytes b o ys -∗ auxes b o (copy_slots (Z.of_nat (length xs)) ds cs) -∗
     live b' reg' -∗ bytes b' o' ys -∗ auxes b' o' ds -∗
     WP (ERun (mkFrame f (put d (WPtr (mkPtr (b + o) (Obj b))) e) ls None (Exec lab rest j)) : mexpr)
       {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
             (Exec lab (Call (CResult d P) (Global (TAtom "memcpy")) [Arg P vd; Arg P vs; Arg L vn] :: rest) j))
        : mexpr) {{ Φ }}.
Proof.
  intros Hreg Hfn Hdata Hpd Hps Hc' Hn Hne Hb8 Ho8 Hb8' Ho8' Ho Ho' Hend Hend' Hly Hlc Hld Hy Hwi.
  iIntros "Hl Hx Hcs Hl' Hy Hds HK".
  iDestruct (block_pts b reg o xs cs with "[$Hl $Hx $Hcs]") as "Hdst".
  iDestruct (block_pts b' reg' o' ys ds with "[$Hl' $Hy $Hds]") as "Hsrc".
  iCombine "Hdst Hsrc" as "Hps".
  iApply (wp_external _ _ _ _ _ _ _ _ _ _ _ _ (memcpy_contract world)
            [WPtr (mkPtr (b + o) (Obj b)); WPtr (mkPtr (b' + o') c'); WInt (Z.of_nat (length xs))]
            (pts (block_ps b reg o xs cs) ∗ pts (block_ps b' reg' o' ys ds)) with "Hps [HK]");
    [done | done | done | done | cbn [map_option]; rewrite Hpd Hps Hn; done | | |].
  - split; [right; eexists; reflexivity | exists vd, vs, vn; reflexivity].
  - iIntros (σ) "Hσ [Hdst Hsrc]". iDestruct (pts_facts with "Hσ Hdst") as %(Ha & Hd & Hfit).
    iDestruct (pts_facts with "Hσ Hsrc") as %(Ha' & _ & _). iPureIntro.
    destruct Ha as [[E L] _]. destruct Ha' as [[E' L'] Hsrc]. cbn [fst snd] in E, L, E', L'.
    apply all_agree_app in Hsrc as [Hys _].
    destruct (Hfit b reg E) as [Hb0 Hfit']. destruct (Hfit b' reg' E') as [Hb0' Hfit''].
    eexists _, _, _. split; [reflexivity|]. split; [|split; [|split]].
    + split; [lia|]. split; [lia|]. split.
      * unfold writable_span. cbn [span_ptr span_size ptr_addr ptr_cap].
        split; [lia|]. exists b, reg. split; [reflexivity|]. split; [exact E|]. split; [exact L|].
        apply (access_obj _ _ reg); [exact E | lia | lia | apply Z.mod_1_r].
      * right. exists b. auto.
    + split; [lia|]. split; [exists b', reg'; auto|]. split.
      * apply (access_read _ b' reg'); [exact Hc' | exact E' | cbn; lia | cbn; lia | apply Z.mod_1_r].
      * intros i Hi. cbn [ptr_addr]. destruct (lookup_lt_is_Some_2 ys (Z.to_nat i) ltac:(lia)) as [y Hyi].
        destruct (byte_ps_agree _ _ _ _ _ _ _ (conj E' L') Hys Hyi) as (Hv & _ & _).
        replace (b' + o' + i) with (b' + (o' + Z.of_nat (Z.to_nat i))) by lia. rewrite Hv.
        exact (Forall_lookup_1 _ _ _ _ Hy Hyi).
    + right. exists b'. auto.
    + right. right. cbn [ptr_addr].
      destruct (Hd b reg b' reg' (conj E L) (conj E' L') Hne); [left | right]; lia.
  - iNext. iIntros (σ trace values s' m' w' Hinv) "(%h & Hh & %Hf) [Hdst Hsrc]".
    destruct Hf as (Ha & Hd & Hr & Hw).
    destruct (M.E.copy_invocation _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hinv)
      as (_ & -> & d' & s0 & n' & Hx & _ & Hres & He).
    injection Hx as <- <- <-. injection He as ->.
    iDestruct (pts_lookup with "Hh Hdst") as %Hlk.
    iDestruct (pts_lookup with "Hh Hsrc") as %Hlk'.
    assert (Hold : all_agree (ls_mem σ) (block_ps b reg o xs cs)).
    { apply all_agree_intro. intros l v Hin. exact (Ha l v (Hlk l v Hin)). }
    assert (Hold' : all_agree (ls_mem σ) (block_ps b' reg' o' ys ds)).
    { apply all_agree_intro. intros l v Hin. exact (Ha l v (Hlk' l v Hin)). }
    destruct Hold as [Hlv Hold]. destruct Hold' as [Hlv' Hold']. cbn [agree_piece fst snd] in Hlv, Hlv'.
    destruct (copy_after (ls_mem σ) m' b reg o xs cs b' reg' o' ys ds c' Hd Hlv Hlv' Hb8 Ho8 Hb8' Ho8'
                Hly Hlc Hld Hold Hold' Hres) as [Hnew Hfr].
    destruct (M.E.invoke_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ Hinv) as (born & Hpre).
    destruct (M.E.prefix_preserve _ _ _ _ _ _ _ _ _ _ _ Hpre Hr) as [Hr' _].
    pose proof Hres as ((Hregs & _) & _).
    assert (Hk : (block_ps b reg o ys (copy_slots (Z.of_nat (length xs)) ds cs)).*1 = (block_ps b reg o xs cs).*1).
    { apply block_ps_keys; [exact Hly | rewrite length_copy_slots; lia]. }
    iMod (pts_update _ _ (block_ps b reg o ys (copy_slots (Z.of_nat (length xs)) ds cs)) with "Hh Hdst")
      as "[Hh Hdst]"; [exact Hk|].
    iModIntro. iExists _. iSplit; [iPureIntro; reflexivity|].
    iSplitL "Hh".
    + iExists _. iFrame "Hh". iPureIntro. cbn [ls_mem ls_rt ls_world]. split; [|split; [|split]].
      * intros l v Hl'. destruct (lookup_overwrite _ _ _ _ Hl') as [Hin | [Hnk Hh]].
        -- apply elem_of_cons in Hin as [Hin|Hin].
           ++ injection Hin as -> ->. cbn [agree_piece]. exact (live_at_regions _ _ _ _ Hregs Hlv).
           ++ exact (all_agree_elem _ _ _ _ Hnew Hin).
        -- apply Hfr; [|exact (Ha l v Hh)]. intros Hk'. apply Hnk. rewrite Hk.
           cbn [fmap list_fmap fst block_ps]. right. exact Hk'.
      * exact (live_disjoint_regions _ _ Hregs Hd).
      * exact Hr'.
      * exact (Hwi _ _ _ _ Hres Hlk Hw).
    + rewrite !block_pts. iDestruct "Hdst" as "(Hl & Hx & Hcs)". iDestruct "Hsrc" as "(Hl' & Hy & Hds)".
      iApply ("HK" with "Hl Hx Hcs Hl' Hy Hds").
Qed.

(** Calling strdup returns an owned string in a fresh heap object and
    hands the original string back unchanged; allocation refusal does not return.
    The rule [wp_strdup] requires the source object's base to be
    eight-byte aligned and the allocation to preserve the external-world interpretation.
    Its result owns the copied string and object lifetime, but not
    the fresh object's remaining bytes or shadow slots. *)
Lemma wp_strdup f e ls lab d v rest j p b reg bytes Φ :
  registry (TAtom "strdup") = Some (strdup_contract world) ->
  find_fn ge (TAtom "strdup") = None -> lookup (TAtom "strdup") (ge_globals ge) = None ->
  arg_x ge e (Arg P v) = Some (WPtr p) -> b mod 8 = 0 ->
  (forall m m' wd h base k, strdup_result m p k base m' -> wi m wd h ->
     wi m' wd (overwrite (string_ps (mkPtr base (Obj base)) base
                            (mkRegion base (base + req_extent (heap_req 16 k)) Heap Live) bytes) h)) ->
  string p b reg bytes -∗
  ▷ (∀ base reg', string p b reg bytes -∗ string (mkPtr base (Obj base)) base reg' bytes -∗
       WP (ERun (mkFrame f (put d (WPtr (mkPtr base (Obj base))) e) ls None (Exec lab rest j)) : mexpr)
         {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
             (Exec lab (Call (CResult d P) (Global (TAtom "strdup")) [Arg P v] :: rest) j)) : mexpr)
    {{ Φ }}.
Proof.
  intros Hreg Hfn Hdata Hv Hb8 Hwi. iIntros "Hs HK".
  iApply (wp_external _ _ _ _ _ _ _ _ _ _ _ _ (strdup_contract world) [WPtr p] (string p b reg bytes)
            with "Hs [HK]"); [done | done | done | done | cbn [map_option]; rewrite Hv; done | | |].
  - split; [right; eexists; reflexivity | eexists; reflexivity].
  - iIntros (σ) "Hσ Hs". iDestruct (string_facts with "Hσ Hs") as %[Ht _].
    iDestruct "Hs" as "[%Hok _]". iPureIntro. destruct Hok as (Hc & _).
    exists p, (Z.of_nat (length bytes)). split; [reflexivity|]. split; [exact Ht|]. exists b. auto.
  - iNext. iIntros (σ trace values s' m' w' Hinv) "(%h & Hh & %Hf) [%Hok Hs]".
    destruct Hf as (Ha & Hd & Hr & Hw).
    iDestruct (pts_lookup with "Hh Hs") as %Hlk.
    assert (Hold : all_agree (ls_mem σ) (string_ps p b reg bytes)).
    { apply all_agree_intro. intros l v' Hin. exact (Ha l v' (Hlk l v' Hin)). }
    pose proof (string_terminated _ _ _ _ _ Hok Hold) as Ht.
    pose proof (string_bytes _ _ _ _ _ Hok Hold) as Hbs.
    destruct (M.E.invoke_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ Hinv) as (born & Hp).
    destruct (M.E.prefix_preserve _ _ _ _ _ _ _ _ _ _ _ Hp Hr) as [Hr' _].
    destruct (M.E.strdup_invocation _ _ _ _ _ _ _ _ _ _ _ _ Hinv)
      as (_ & -> & p' & k & Hx & (Hk & _) & [(base & Hres & He) | (why & born' & He & _)]); [|discriminate He].
    injection Hx as <-. injection He as ->. rewrite <- (terminated_length_unique _ _ _ _ Ht Hk) in Hres.
    set (n := Z.of_nat (length bytes)) in *.
    pose proof (malloc_extent (n + 1) ltac:(unfold n; lia)) as Hext.
    assert (Hn0 : 0 <= n) by (unfold n; lia).
    set (q := heap_req 16 (n + 1)) in *.
    set (reg' := mkRegion base (base + req_extent q) Heap Live).
    destruct Hres as [(Hmax & Hfr & _) Hcopy].
    pose proof Hfr as (Hpos & Hmod & _ & Hnone & _).
    pose proof Hcopy as ((Hregs & Hbytes & Haux) & Hcb & _).
    set (m1 := allocated (ls_mem σ) q base) in *.
    assert (Hl1 : live_at m1 base reg').
    { split; [|reflexivity]. unfold m1. rewrite object_region_allocated Z.eqb_refl. reflexivity. }
    assert (Hd1 : live_disjoint m1).
    { apply live_disjoint_allocated; [exact Hd | exact Hfr | lia]. }
    assert (Hout : forall a, ~ (base <= a < r_end reg') ->
              m_bytes m' a = m_bytes m1 a /\ m_aux m' a = m_aux m1 a).
    { intros a Ha'. cbn [r_end reg'] in Ha'. split.
      - apply Hbytes. unfold span_contains. cbn. lia.
      - apply Haux. destruct (memset_touched _ _ a) eqn:Ht'; [|reflexivity]. exfalso.
        apply memset_touched_spec in Ht' as (_ & Ha8 & Hhi & Hlo). cbn [ptr_addr] in Hhi, Hlo.
        assert (Hb16 : base mod 8 = 0) by exact (fresh_heap_aligned8 _ _ _ Hfr).
        pose proof (Z.div_mod a 8 ltac:(lia)). pose proof (Z.div_mod base 8 ltac:(lia)). lia. }
    iMod (pts_alloc h (string_ps (mkPtr base (Obj base)) base reg' bytes) with "Hh") as "[Hh Hnew]".
    { apply string_ps_nodup. }
    { intros l' v' Hin. destruct (h !! l') as [v0|] eqn:E; [|reflexivity]. exfalso.
      pose proof (agree_piece_registered _ _ _ (string_ps_mem _ _ _ _ _ _ Hin) (Ha l' v0 E)) as Hreg'.
      rewrite (string_ps_id _ _ _ _ _ _ Hin) in Hreg'. exact (Hreg' Hnone). }
    iModIntro. iExists _. iSplit; [iPureIntro; reflexivity|].
    iSplitL "Hh".
    + iExists _. iFrame "Hh". iPureIntro. cbn [ls_mem ls_rt ls_world]. split; [|split; [|split]].
      * intros l' v' Hl. destruct (lookup_overwrite _ _ _ _ Hl) as [Hin | [_ Hh]].
        -- apply elem_of_cons in Hin as [Hin|Hin].
           ++ injection Hin as -> ->. cbn [agree_piece]. unfold live_at. rewrite Hregs. exact Hl1.
           ++ cbn [ptr_addr] in Hin. rewrite Z.sub_diag in Hin.
              apply byte_ps_elem in Hin as (i & x & Hxi & -> & ->). cbn [agree_piece].
              assert (Hi : (i <= length bytes)%nat).
              { apply lookup_lt_Some in Hxi. rewrite length_app in Hxi. cbn in Hxi. lia. }
              split; [unfold registered; rewrite Hregs; destruct Hl1 as [E _]; rewrite E; discriminate|].
              intros reg0 E L. rewrite Hregs in E. destruct Hl1 as [E1 _]. rewrite E1 in E.
              injection E as <-. cbn [r_end reg']. split; [lia|]. split; [lia|].
              rewrite Hcb; [|unfold span_contains; cbn; lia]. cbn [ptr_addr].
              replace (base + (0 + Z.of_nat i) - base) with (Z.of_nat i) by lia.
              exact (Hbs i x Hxi).
        -- apply (frame_other m1 m' base reg'); [exact Hregs | exact Hd1 | exact Hl1 | exact Hout | |].
           ++ intros Hm Hid. pose proof (agree_piece_registered _ _ _ Hm (Ha l' v' Hh)) as Hreg'.
              rewrite Hid in Hreg'. exact (Hreg' Hnone).
           ++ exact (agree_piece_allocated _ _ _ _ _ Hnone (Ha l' v' Hh)).
      * exact (live_disjoint_regions _ _ Hregs Hd1).
      * exact Hr'.
      * exact (Hwi _ _ _ _ _ _ (conj (conj Hmax (conj Hfr eq_refl)) Hcopy) Hw).
    + iApply ("HK" with "[Hs] [Hnew]").
      * iSplit; [iPureIntro; exact Hok | iExact "Hs"].
      * iSplit; [|iExact "Hnew"]. iPureIntro. unfold string_ok. cbn [ptr_cap ptr_addr r_end reg'].
        destruct Hok as (_ & _ & _ & _ & _ & Hf).
        destruct (R.address_space _ _ Hr' base reg') as [_ Hend];
          [rewrite Hregs; exact (proj1 Hl1)|].
        cbn [r_end reg'] in Hend. split; [left; reflexivity|]. repeat split; try lia. exact Hf.
Qed.

(** A scalar string copy turns destination byte ownership into an
    owned string, including its terminator, and preserves the source string.
    The rule [wp_string_copy] returns either the destination pointer or
    its terminating NUL pointer, according to the selected copy contract.
    Owning both object lifetimes forces distinct objects, while preserving
    every shadow slot removes the need for shadow ownership or alignment.
    The caller supplies enough destination bytes and proves that the
    copy preserves its interpretation of external-library state. *)
Lemma wp_string_copy end_return g f e ls lab d vd vs rest j b reg o xs src b' reg' ys Φ :
  registry g = Some (string_copy_contract end_return world) ->
  find_fn ge g = None -> lookup g (ge_globals ge) = None -> is_free_name g = false ->
  arg_x ge e (Arg P vd) = Some (WPtr (mkPtr (b + o) (Obj b))) -> arg_x ge e (Arg P vs) = Some (WPtr src) ->
  0 < b -> 0 <= o -> b + o + Z.of_nat (length xs) <= r_end reg -> length xs = S (length ys) ->
  (forall m m' wd h, string_copy_result m (mkPtr (b + o) (Obj b)) src (Z.of_nat (length ys) + 1) m' ->
     (forall l v, (l, v) ∈ byte_ps b o xs -> h !! l = Some v) -> wi m wd h ->
     wi m' wd (overwrite (byte_ps b o (ys ++ [0])) h)) ->
  live b reg -∗ bytes b o xs -∗ string src b' reg' ys -∗
  ▷ (string (mkPtr (b + o) (Obj b)) b reg ys -∗ string src b' reg' ys -∗
     WP (ERun (mkFrame f (put d (WPtr (copy_return end_return (mkPtr (b + o) (Obj b))
                                         (Z.of_nat (length ys)))) e) ls None (Exec lab rest j)) : mexpr)
       {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
             (Exec lab (Call (CResult d P) (Global g) [Arg P vd; Arg P vs] :: rest) j)) : mexpr) {{ Φ }}.
Proof.
  intros Hreg Hfn Hdata Hfree Hpd Hps Hb0 Ho Hend Hlen Hwi. iIntros "Hl Hx Hs HK".
  iDestruct (live_string_ne with "Hl Hs") as %Hne.
  iApply (wp_external _ _ _ _ _ _ _ _ _ _ _ _ (string_copy_contract end_return world)
            [WPtr (mkPtr (b + o) (Obj b)); WPtr src] (live b reg ∗ bytes b o xs ∗ string src b' reg' ys)
            with "[$Hl $Hx $Hs] [HK]");
    [done | done | done | done | cbn [map_option]; rewrite Hpd Hps; done | | |].
  - split; [right; eexists; reflexivity | exists vd, vs; reflexivity].
  - iIntros (σ) "Hσ (Hl & _ & [%Hok Hs])".
    iDestruct (pts_facts with "Hσ Hl") as %(Hal & Hd & _).
    iDestruct (pts_facts with "Hσ Hs") as %(Has & _ & _). iPureIntro.
    pose proof (string_terminated _ _ _ _ _ Hok Has) as Ht.
    destruct Hal as [[E L] _]. destruct Has as [[E' L'] _]. cbn [fst snd] in E, L, E', L'.
    exists (mkPtr (b + o) (Obj b)), src, (Z.of_nat (length ys)). split; [reflexivity|].
    split; [exact Ht|]. split.
    + unfold writable_span. cbn [span_ptr span_size ptr_addr ptr_cap].
      split; [lia|]. exists b, reg. split; [reflexivity|]. split; [exact E|]. split; [exact L|].
      apply (access_obj _ _ reg); [exact E | lia | lia | apply Z.mod_1_r].
    + cbn [ptr_addr]. destruct Hok as (_ & _ & Hs1 & Hs2 & _).
      destruct (Hd b reg b' reg' (conj E L) (conj E' L') Hne); [left | right]; lia.
  - iNext. iIntros (σ trace values s' m' w' Hinv) "(%h & Hh & %Hf) (Hl & Hx & [%Hok Hs])".
    destruct Hf as (Ha & Hd & Hr & Hw).
    destruct (M.E.string_copy_invocation _ _ _ _ _ _ _ _ _ _ _ _ _ Hinv)
      as (_ & -> & d' & src' & k & Hx' & Hdom & Hres & He).
    injection Hx' as <- <-.
    iDestruct (pts_lookup with "Hh Hl") as %Hll.
    iDestruct (pts_lookup with "Hh Hx") as %Hlx.
    iDestruct (pts_lookup with "Hh Hs") as %Hls.
    assert (Hlv : live_at (ls_mem σ) b reg).
    { apply (Ha (PLive b) (VLive reg)). apply Hll. apply elem_of_cons. left. reflexivity. }
    assert (Hx0 : all_agree (ls_mem σ) (byte_ps b o xs)).
    { apply all_agree_intro. intros l v Hin. exact (Ha l v (Hlx l v Hin)). }
    assert (Hs0 : all_agree (ls_mem σ) (string_ps src b' reg' ys)).
    { apply all_agree_intro. intros l v Hin. exact (Ha l v (Hls l v Hin)). }
    pose proof (string_terminated _ _ _ _ _ Hok Hs0) as Ht.
    assert (k = Z.of_nat (length ys)) as ->.
    { exact (terminated_length_unique _ _ _ _ (proj1 Hdom) Ht). }
    injection He as ->.
    destruct (copy_string_after (ls_mem σ) m' b reg o xs src b' reg' ys Hd Hlv Hx0 Hlen Hok Hs0 Hres)
      as [Hnew Hfr].
    destruct (M.E.invoke_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ Hinv) as (born & Hpre).
    destruct (M.E.prefix_preserve _ _ _ _ _ _ _ _ _ _ _ Hpre Hr) as [Hr' _].
    pose proof Hres as ((Hregs & _) & _).
    destruct (R.address_space _ _ Hr b reg (proj1 Hlv)) as [_ Hfit].
    assert (Hok' : string_ok (mkPtr (b + o) (Obj b)) b reg ys).
    { unfold string_ok. cbn [ptr_cap ptr_addr]. destruct Hok as (_ & _ & _ & _ & _ & Hf).
      split; [left; reflexivity|]. repeat split; try lia. exact Hf. }
    assert (Hk : (byte_ps b o (ys ++ [0])).*1 = (byte_ps b o xs).*1).
    { rewrite !byte_ps_keys length_app Hlen. cbn [length]. rewrite Nat.add_1_r. reflexivity. }
    iMod (pts_update _ (byte_ps b o xs) (byte_ps b o (ys ++ [0])) Hk with "Hh Hx") as "[Hh Hx]".
    iModIntro. iExists _. iSplit; [iPureIntro; reflexivity|].
    iSplitL "Hh".
    + iExists _. iFrame "Hh". iPureIntro. cbn [ls_mem ls_rt ls_world]. split; [|split; [|split]].
      * intros l v Hl'. destruct (lookup_overwrite _ _ _ _ Hl') as [Hin | [Hnk Hh']].
        -- exact (all_agree_elem _ _ _ _ Hnew Hin).
        -- apply Hfr; [|exact (Ha l v Hh')]. rewrite <- Hk. exact Hnk.
      * exact (live_disjoint_regions _ _ Hregs Hd).
      * exact Hr'.
      * exact (Hwi _ _ _ _ Hres Hlx Hw).
    + iApply ("HK" with "[Hl Hx] [Hs]").
      * iApply (block_string _ _ _ _ Hok' with "Hl Hx").
      * iSplit; [iPureIntro; exact Hok | iExact "Hs"].
Qed.

(** Calling strcpy uses the scalar string-copy rule and binds the
    result to the destination pointer, as [wp_strcpy] specializes the general contract. *)
Lemma wp_strcpy f e ls lab d vd vs rest j b reg o xs src b' reg' ys Φ :
  registry (TAtom "strcpy") = Some (strcpy_contract world) ->
  find_fn ge (TAtom "strcpy") = None -> lookup (TAtom "strcpy") (ge_globals ge) = None ->
  arg_x ge e (Arg P vd) = Some (WPtr (mkPtr (b + o) (Obj b))) -> arg_x ge e (Arg P vs) = Some (WPtr src) ->
  0 < b -> 0 <= o -> b + o + Z.of_nat (length xs) <= r_end reg -> length xs = S (length ys) ->
  (forall m m' wd h, string_copy_result m (mkPtr (b + o) (Obj b)) src (Z.of_nat (length ys) + 1) m' ->
     (forall l v, (l, v) ∈ byte_ps b o xs -> h !! l = Some v) -> wi m wd h ->
     wi m' wd (overwrite (byte_ps b o (ys ++ [0])) h)) ->
  live b reg -∗ bytes b o xs -∗ string src b' reg' ys -∗
  ▷ (string (mkPtr (b + o) (Obj b)) b reg ys -∗ string src b' reg' ys -∗
     WP (ERun (mkFrame f (put d (WPtr (mkPtr (b + o) (Obj b))) e) ls None (Exec lab rest j)) : mexpr)
       {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
             (Exec lab (Call (CResult d P) (Global (TAtom "strcpy")) [Arg P vd; Arg P vs] :: rest) j))
        : mexpr) {{ Φ }}.
Proof.
  intros Hreg Hfn Hdata Hpd Hps Hb0 Ho Hend Hlen Hwi. iIntros "Hl Hx Hs HK".
  iApply (wp_string_copy false (TAtom "strcpy") with "Hl Hx Hs HK"); done.
Qed.

(** Calling stpcpy uses the scalar string-copy rule but returns the
    copied terminator's pointer, as [wp_stpcpy] specializes the general contract. *)
Lemma wp_stpcpy f e ls lab d vd vs rest j b reg o xs src b' reg' ys Φ :
  registry (TAtom "stpcpy") = Some (stpcpy_contract world) ->
  find_fn ge (TAtom "stpcpy") = None -> lookup (TAtom "stpcpy") (ge_globals ge) = None ->
  arg_x ge e (Arg P vd) = Some (WPtr (mkPtr (b + o) (Obj b))) -> arg_x ge e (Arg P vs) = Some (WPtr src) ->
  0 < b -> 0 <= o -> b + o + Z.of_nat (length xs) <= r_end reg -> length xs = S (length ys) ->
  (forall m m' wd h, string_copy_result m (mkPtr (b + o) (Obj b)) src (Z.of_nat (length ys) + 1) m' ->
     (forall l v, (l, v) ∈ byte_ps b o xs -> h !! l = Some v) -> wi m wd h ->
     wi m' wd (overwrite (byte_ps b o (ys ++ [0])) h)) ->
  live b reg -∗ bytes b o xs -∗ string src b' reg' ys -∗
  ▷ (string (mkPtr (b + o) (Obj b)) b reg ys -∗ string src b' reg' ys -∗
     WP (ERun (mkFrame f (put d (WPtr (mkPtr (b + o + Z.of_nat (length ys)) (Obj b))) e) ls None
                 (Exec lab rest j)) : mexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
             (Exec lab (Call (CResult d P) (Global (TAtom "stpcpy")) [Arg P vd; Arg P vs] :: rest) j))
        : mexpr) {{ Φ }}.
Proof.
  intros Hreg Hfn Hdata Hpd Hps Hb0 Ho Hend Hlen Hwi. iIntros "Hl Hx Hs HK".
  iApply (wp_string_copy true (TAtom "stpcpy") with "Hl Hx Hs HK"); done.
Qed.

(** Calling memcmp preserves both owned byte ranges and returns an
    integer, but [wp_memcmp] does not specify that integer's sign or value.
    This rule requires equally sized readable ranges and supports
    safety proofs that handle every comparison result without assuming an ordering. *)
Lemma wp_memcmp f e ls lab d vp vq vn rest j b reg o xs c b' reg' o' ys c' Φ :
  registry (TAtom "memcmp") = Some (memcmp_contract world) ->
  find_fn ge (TAtom "memcmp") = None -> lookup (TAtom "memcmp") (ge_globals ge) = None ->
  arg_x ge e (Arg P vp) = Some (WPtr (mkPtr (b + o) c)) -> c = Obj b \/ c = Ro b ->
  arg_x ge e (Arg P vq) = Some (WPtr (mkPtr (b' + o') c')) -> c' = Obj b' \/ c' = Ro b' ->
  arg_x ge e (Arg L vn) = Some (WInt (Z.of_nat (length xs))) -> length ys = length xs ->
  0 <= o -> 0 <= o' -> b + o + Z.of_nat (length xs) <= r_end reg ->
  b' + o' + Z.of_nat (length xs) <= r_end reg' ->
  Forall (fun x => 0 <= x < 256) xs -> Forall (fun x => 0 <= x < 256) ys ->
  live b reg -∗ bytes b o xs -∗ live b' reg' -∗ bytes b' o' ys -∗
  ▷ (∀ bits, live b reg -∗ bytes b o xs -∗ live b' reg' -∗ bytes b' o' ys -∗
     WP (ERun (mkFrame f (put d (WInt bits) e) ls None (Exec lab rest j)) : mexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
             (Exec lab (Call (CResult d W) (Global (TAtom "memcmp")) [Arg P vp; Arg P vq; Arg L vn] :: rest) j))
        : mexpr) {{ Φ }}.
Proof.
  intros Hreg Hfn Hdata Hp Hc Hq Hc' Hn Hlen Ho Ho' Hend Hend' Hx Hy.
  iIntros "Hl Hx Hl' Hy HK".
  iApply (wp_external _ _ _ _ _ _ _ _ _ _ _ _ (memcmp_contract world)
            [WPtr (mkPtr (b + o) c); WPtr (mkPtr (b' + o') c'); WInt (Z.of_nat (length xs))]
            (live b reg ∗ bytes b o xs ∗ live b' reg' ∗ bytes b' o' ys) with "[$Hl $Hx $Hl' $Hy] [HK]");
    [done | done | done | done | cbn [map_option]; rewrite Hp Hq Hn; done | | |].
  - split; [right; eexists; reflexivity | do 3 eexists; reflexivity].
  - iIntros (σ) "Hσ (Hl & Hx & Hl' & Hy)".
    iDestruct (pts_facts with "Hσ Hl") as %([Hlv _] & _ & Hfit).
    iDestruct (pts_facts with "Hσ Hx") as %(Hxa & _).
    iDestruct (pts_facts with "Hσ Hl'") as %([Hlv' _] & _ & _).
    iDestruct (pts_facts with "Hσ Hy") as %(Hya & _). iPureIntro. cbn [fst snd agree_piece] in Hlv, Hlv'.
    exists (mkPtr (b + o) c), (mkPtr (b' + o') c'), (Z.of_nat (length xs)). split; [reflexivity|].
    split; [exact (proj1 (block_readable _ _ _ _ _ _ Hlv Hxa Hfit Hc Ho Hend Hx))|].
    rewrite <- Hlen. rewrite <- Hlen in Hend'.
    exact (proj1 (block_readable _ _ _ _ _ _ Hlv' Hya Hfit Hc' Ho' Hend' Hy)).
  - iNext. iIntros (σ trace values s' m' w' Hinv) "Hσ (Hl & Hx & Hl' & Hy)".
    destruct (M.E.memcmp_invocation _ _ _ _ _ _ _ _ _ _ _ _ Hinv)
      as (_ & -> & -> & p' & q' & n' & bits & Hxs & _ & He). injection He as ->.
    iDestruct (pure_return with "Hσ") as "Hσ"; [exact Hinv|]. destruct σ as [m s fuel w0]. iModIntro.
    iExists _. iSplit; [iPureIntro; reflexivity|]. iFrame "Hσ". iApply ("HK" with "Hl Hx Hl' Hy").
Qed.

(** Calling memchr preserves the owned byte range and returns its first
    match for the argument's low byte, or null when no match exists.
    The rule [wp_memchr] retains the input capability in a matching
    pointer and accepts either writable or read-only access to the range. *)
Lemma wp_memchr f e ls lab d vp vk vn rest j b reg o xs c k Φ :
  registry (TAtom "memchr") = Some (memchr_contract world) ->
  find_fn ge (TAtom "memchr") = None -> lookup (TAtom "memchr") (ge_globals ge) = None ->
  arg_x ge e (Arg P vp) = Some (WPtr (mkPtr (b + o) c)) -> c = Obj b \/ c = Ro b ->
  arg_x ge e (Arg W vk) = Some (WInt k) -> 0 <= k < 2 ^ 32 ->
  arg_x ge e (Arg L vn) = Some (WInt (Z.of_nat (length xs))) ->
  0 <= o -> b + o + Z.of_nat (length xs) <= r_end reg -> Forall (fun x => 0 <= x < 256) xs ->
  live b reg -∗ bytes b o xs -∗
  ▷ (∀ q, ⌜strchr_found (mkPtr (b + o) c) xs k q⌝ -∗ live b reg -∗ bytes b o xs -∗
     WP (ERun (mkFrame f (put d (WPtr q) e) ls None (Exec lab rest j)) : mexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
             (Exec lab (Call (CResult d P) (Global (TAtom "memchr")) [Arg P vp; Arg W vk; Arg L vn] :: rest) j))
        : mexpr) {{ Φ }}.
Proof.
  intros Hreg Hfn Hdata Hp Hc Hk Hk32 Hn Ho Hend Hx. iIntros "Hl Hx HK".
  iApply (wp_external _ _ _ _ _ _ _ _ _ _ _ _ (memchr_contract world)
            [WPtr (mkPtr (b + o) c); WInt k; WInt (Z.of_nat (length xs))]
            (live b reg ∗ bytes b o xs) with "[$Hl $Hx] [HK]");
    [done | done | done | done | cbn [map_option]; rewrite Hp Hk Hn; done | | |].
  - split; [right; eexists; reflexivity | do 3 eexists; reflexivity].
  - iIntros (σ) "Hσ (Hl & Hx)".
    iDestruct (pts_facts with "Hσ Hl") as %([Hlv _] & _ & Hfit).
    iDestruct (pts_facts with "Hσ Hx") as %(Hxa & _). iPureIntro. cbn [fst snd agree_piece] in Hlv.
    do 3 eexists. split; [reflexivity|]. apply memchr_input_full; [exact Hk32|].
    exact (proj1 (block_readable _ _ _ _ _ _ Hlv Hxa Hfit Hc Ho Hend Hx)).
  - iNext. iIntros (σ trace values s' m' w' Hinv) "Hσ (Hl & Hx)".
    iDestruct (pts_facts with "Hσ Hl") as %([Hlv _] & _ & Hfit).
    iDestruct (pts_facts with "Hσ Hx") as %(Hxa & _). cbn [fst snd agree_piece] in Hlv.
    destruct (block_readable _ _ _ _ _ _ Hlv Hxa Hfit Hc Ho Hend Hx) as [_ Hv].
    destruct (M.E.memchr_invocation _ _ _ _ _ _ _ _ _ _ _ _ Hinv)
      as (_ & -> & -> & p' & k' & n' & q & Hxs & Hq & He). injection Hxs as <- <- <-. injection He as ->.
    iDestruct (pure_return with "Hσ") as "Hσ"; [exact Hinv|]. destruct σ as [m s fuel w0]. iModIntro.
    iExists _. iSplit; [iPureIntro; reflexivity|]. iFrame "Hσ".
    iApply ("HK" with "[%] Hl Hx"). cbn [ptr_addr ls_mem] in Hq, Hv.
    destruct Hq as [(i & Hi & Hvi & Hbefore & ->) | (Hnone & ->)].
    + left. destruct (lookup_lt_is_Some_2 xs (Z.to_nat i) ltac:(lia)) as [x Hxi].
      exists (Z.to_nat i), x. split; [exact Hxi|]. split.
      * rewrite <- Hvi. rewrite <- (Hv _ _ Hxi). rewrite Z2Nat.id; [reflexivity|lia].
      * split; [|cbn [ptr_addr ptr_cap]; rewrite Z2Nat.id; [reflexivity|lia]].
        intros i' x' Hlt Hx'. rewrite <- (Hv _ _ Hx'). apply Hbefore. lia.
    + right. split; [|reflexivity]. intros i' x' Hx'. rewrite <- (Hv _ _ Hx').
      apply Hnone. split; [lia|]. apply lookup_lt_Some in Hx'. lia.
Qed.

(** Searching an owned string for zero returns its NUL before the
    bound, or null when the bound excludes that byte.
    The rule [wp_memchr_string] preserves string ownership and permits
    a bound beyond the enclosing object because no read follows the first match. *)
Lemma wp_memchr_string f e ls lab d vp vk vn rest j p b reg bytes k n Φ :
  registry (TAtom "memchr") = Some (memchr_contract world) ->
  find_fn ge (TAtom "memchr") = None -> lookup (TAtom "memchr") (ge_globals ge) = None ->
  arg_x ge e (Arg P vp) = Some (WPtr p) ->
  arg_x ge e (Arg W vk) = Some (WInt k) -> 0 <= k < 2 ^ 32 -> k mod 256 = 0 ->
  arg_x ge e (Arg L vn) = Some (WInt n) -> 0 <= n < 2 ^ 64 ->
  string p b reg bytes -∗
  ▷ (string p b reg bytes -∗
     WP (ERun (mkFrame f (put d (WPtr (nul_found p bytes n)) e) ls None (Exec lab rest j)) : mexpr)
       {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
             (Exec lab (Call (CResult d P) (Global (TAtom "memchr")) [Arg P vp; Arg W vk; Arg L vn] :: rest) j))
        : mexpr) {{ Φ }}.
Proof.
  intros Hreg Hfn Hdata Hp Hk Hk32 H0 Hn Hn64. iIntros "Hs HK".
  iApply (wp_external _ _ _ _ _ _ _ _ _ _ _ _ (memchr_contract world)
            [WPtr p; WInt k; WInt n] (string p b reg bytes) with "Hs [HK]");
    [done | done | done | done | cbn [map_option]; rewrite Hp Hk Hn; done | | |].
  - split; [right; eexists; reflexivity | do 3 eexists; reflexivity].
  - iIntros (σ) "Hσ [%Hok Hs]". iDestruct (pts_facts with "Hσ Hs") as %(Ha & _). iPureIntro.
    do 3 eexists. split; [reflexivity|].
    exact (memchr_input_bounded _ _ _ _ _ Hk32 H0 (string_bounded _ _ _ _ _ n Hok Ha Hn64)).
  - iNext. iIntros (σ trace values s' m' w' Hinv) "Hσ [%Hok Hs]".
    iDestruct (pts_facts with "Hσ Hs") as %(Ha & _).
    destruct (M.E.memchr_invocation _ _ _ _ _ _ _ _ _ _ _ _ Hinv)
      as (_ & -> & -> & p' & k' & n' & q & Hxs & Hq & He). injection Hxs as <- <- <-. injection He as ->.
    rewrite (memchr_result_string _ _ _ _ _ _ _ _ Hok Ha H0 Hq).
    iDestruct (pure_return with "Hσ") as "Hσ"; [exact Hinv|]. destruct σ as [m s fuel w0]. iModIntro.
    iExists _. iSplit; [iPureIntro; reflexivity|]. iFrame "Hσ". iApply "HK". by iSplit.
Qed.

End calls.
End mem.
End MemLogicOn.

(** The module [MemLogic] creates its own program-logic instance and
    supplies the buffer assertions and memory-call rules from [MemLogicOn]. *)
Module MemLogic (R : Runtime).
Module LG0 := Logic R.
Include MemLogicOn R LG0.
End MemLogic.
