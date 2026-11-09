(** Blocks of memory in the program logic of Logic.v, and the triples
    of libc's memory calls derived from [[campaign|Campaign]] 4's
    contracts.

    A block is owned piece by piece: [bytes] b o xs, the bytes xs from
    offset o of the object b, and [auxes] b o cs, the capabilities cs
    in its [[aux]] slots from the same offset. A write by libc into a
    block needs both: memset clears every pointer slot it touches, a
    copy moves pointer slots, and a pointer slot is an aux piece.

    Each triple is a contract read as a rule, stated at any call site:
    - [wp_memset], from [memset_contract]: owning the object's life and
      a block of n bytes from an 8-aligned offset, with their aux
      slots, the call fills the bytes with c's low byte and empties
      every slot that starts in the block ([clear_slots]);
    - [wp_memcpy], from [memcpy_contract]: owning a destination block
      and a source block in another object, of the same length, both
      8-aligned, so in phase, the destination takes the source's bytes,
      and each of its slots the source's when the copy covers all 8 of
      its bytes, or empties ([copy_slots]); the source is handed back;
    - [wp_malloc], from [malloc_contract]: the fresh object's pieces
      ([obj]); no null case, since the selected malloc refuses with a
      resource ending, which is not a return;
    - [wp_strdup], from [strdup_contract]: owning a [string], the call
      returns a fresh object owning a copy of it as a [string].
    The contracts' exact destination frame ([memset_frame], shared by
    the copies) keeps every piece outside the written block
    ([block_frame], through Heap.v's [frame_within]); for strdup, whose
    writes lie in its fresh object, [frame_other] keeps every other
    object's pieces. The blocks' offsets are 8-aligned so that the
    slots a write touches start inside them; the contracts also allow
    unaligned starts, whose first touched slot begins before them. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import ZArith Lia.
From Stdlib Require String.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine Panics
  StepRules ExternalCalls ExternalMachine Pieces Heap ContractFrame Language Logic StringLogic.
Open Scope Z_scope.
Open Scope list_scope.

(** ## Aux pieces *)

(** The pieces of the aux slots holding cs from offset o of the object
    b. *)
Definition aux_ps (b o : Z) (cs : list cap) : list (piece * pval) :=
  zip_with (fun i c => (PAux b i, VAux c)) (seqZ o (Z.of_nat (length cs))) cs.

(** The first slot's piece, then the rest's. *)
Lemma aux_ps_cons b o c cs : aux_ps b o (c :: cs) = (PAux b o, VAux c) :: aux_ps b (o + 1) cs.
Proof.
  unfold aux_ps. cbn [length]. rewrite Nat2Z.inj_succ seqZ_cons; [|lia].
  rewrite Z.pred_succ. reflexivity.
Qed.

(** The pieces of cs are aux pieces at the offsets from o. *)
Lemma aux_ps_keys b o cs : (aux_ps b o cs).*1 = PAux b <$> seqZ o (Z.of_nat (length cs)).
Proof.
  revert o. induction cs as [|c cs IH]; intros o; [reflexivity|].
  rewrite aux_ps_cons. cbn [fmap list_fmap fst]. rewrite IH.
  cbn [length]. rewrite Nat2Z.inj_succ (seqZ_cons o); [|lia]. rewrite Z.pred_succ. reflexivity.
Qed.

(** A byte piece of xs is the i-th byte's, at offset o + i. *)
Lemma byte_ps_elem b o xs l v :
  (l, v) ∈ byte_ps b o xs -> exists i x, xs !! i = Some x /\ l = PByte b (o + Z.of_nat i) /\ v = VByte x.
Proof.
  intros H. apply list_elem_of_lookup in H as [k Hk]. unfold byte_ps in Hk.
  apply lookup_zip_with_Some in Hk as (i & x & E & Hi & Hx). apply lookup_seqZ in Hi as [-> _].
  injection E as -> ->. eauto.
Qed.

(** An aux piece of cs is the i-th slot's, at offset o + i. *)
Lemma aux_ps_elem b o cs l v :
  (l, v) ∈ aux_ps b o cs -> exists i c, cs !! i = Some c /\ l = PAux b (o + Z.of_nat i) /\ v = VAux c.
Proof.
  intros H. apply list_elem_of_lookup in H as [k Hk]. unfold aux_ps in Hk.
  apply lookup_zip_with_Some in Hk as (i & c & E & Hi & Hc). apply lookup_seqZ in Hi as [-> _].
  injection E as -> ->. eauto.
Qed.

(** The i-th slot's piece is among the keys of cs's pieces. *)
Lemma aux_ps_key b o cs i : 0 <= i < Z.of_nat (length cs) -> PAux b (o + i) ∈ (aux_ps b o cs).*1.
Proof.
  intros Hi. rewrite aux_ps_keys. apply list_elem_of_fmap_2. apply elem_of_seqZ. lia.
Qed.

(** The i-th byte's piece is among the keys of xs's pieces. *)
Lemma byte_ps_key b o xs i : 0 <= i < Z.of_nat (length xs) -> PByte b (o + i) ∈ (byte_ps b o xs).*1.
Proof.
  intros Hi. rewrite byte_ps_keys. apply list_elem_of_fmap_2. apply elem_of_seqZ. lia.
Qed.

(** ## Blocks *)

(** The pieces of a block: the life of the object b with the region
    reg, the bytes xs and the aux slots cs from offset o. *)
Definition block_ps (b : Z) (reg : region) (o : Z) (xs : list Z) (cs : list cap) : list (piece * pval) :=
  (PLive b, VLive reg) :: byte_ps b o xs ++ aux_ps b o cs.

(** Blocks of the same lengths have the same keys. *)
Lemma block_ps_keys b reg o xs cs ys ds :
  length ys = length xs -> length ds = length cs ->
  (block_ps b reg o ys ds).*1 = (block_ps b reg o xs cs).*1.
Proof.
  intros Hy Hd. unfold block_ps. cbn [fmap list_fmap fst]. rewrite !fmap_app.
  rewrite !byte_ps_keys !aux_ps_keys Hy Hd. reflexivity.
Qed.

(** The slots cs from offset o once memset has touched each: those
    that start at a multiple of 8 are empty, the rest are as they were.
    For an object at a multiple of 8, these are the slots the contract
    clears. *)
Definition clear_slots (o : Z) (cs : list cap) : list cap :=
  zip_with (fun i c => if i mod 8 =? 0 then CNone else c) (seqZ o (Z.of_nat (length cs))) cs.

(** Clearing keeps the number of slots. *)
Lemma length_clear_slots o cs : length (clear_slots o cs) = length cs.
Proof. unfold clear_slots. rewrite length_zip_with length_seqZ Nat2Z.id. lia. Qed.

(** The i-th cleared slot. *)
Lemma lookup_clear_slots o cs i c :
  clear_slots o cs !! i = Some c ->
  exists c0, cs !! i = Some c0 /\ c = if (o + Z.of_nat i) mod 8 =? 0 then CNone else c0.
Proof.
  unfold clear_slots. intros H. apply lookup_zip_with_Some in H as (k & c0 & -> & Hk & Hc).
  apply lookup_seqZ in Hk as [-> _]. eauto.
Qed.

(** memset's exact frame ([memset_frame]) on the n bytes xs of the
    block at offset o of the live object b, at a multiple of 8, with
    its slots cs, keeps the agreement of every piece outside the
    block. memset and the copies share it. *)
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

(** A memset of the n bytes xs of the block at offset o of the live
    object b, at a multiple of 8, with its slots cs: afterwards its
    bytes are c's low byte and its slots [clear_slots], and every piece
    outside it keeps its agreement ([frame_ok]). *)
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

(** The slots cs of a destination block after a copy of n bytes from
    a source block whose slots are ds, both blocks at multiples of 8,
    so in phase: a slot at a multiple of 8 takes the source's if all 8
    of its bytes were copied, and empties if only some were; the
    others are as they were. *)
Definition copy_slots (n : Z) (ds cs : list cap) : list cap :=
  zip_with (fun i dc => if i mod 8 =? 0 then (if i + 8 <=? n then fst dc else CNone) else snd dc)
    (seqZ 0 (Z.of_nat (length cs))) (zip ds cs).

(** Copying keeps the number of slots. *)
Lemma length_copy_slots n ds cs : length ds = length cs -> length (copy_slots n ds cs) = length cs.
Proof.
  intros H. unfold copy_slots. rewrite length_zip_with length_seqZ Nat2Z.id length_zip. lia.
Qed.

(** The i-th copied slot. *)
Lemma lookup_copy_slots n ds cs i c :
  copy_slots n ds cs !! i = Some c ->
  exists d0 c0, ds !! i = Some d0 /\ cs !! i = Some c0 /\
    c = if Z.of_nat i mod 8 =? 0 then (if Z.of_nat i + 8 <=? n then d0 else CNone) else c0.
Proof.
  unfold copy_slots. intros H. apply lookup_zip_with_Some in H as (k & [d0 c0] & -> & Hk & Hdc).
  apply lookup_seqZ in Hk as [-> _]. apply lookup_zip_with_Some in Hdc as (x & y & E & Hd & Hc).
  injection E as -> ->. exists x, y. auto.
Qed.

(** What a copy writes into the slot at offset i of a destination
    block at b + o, from a source block at b' + o', all at multiples of
    8, for i a multiple of 8: the source's slot if the copy covers all
    8 bytes, else nothing ([copy_slot]). *)
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

(** A copy of the n bytes ys of a source block at offset o' of the live
    object b' into the block at offset o of the live object b, both at
    multiples of 8: afterwards the destination's bytes are ys and its
    slots [copy_slots], and every piece outside it keeps its agreement
    ([block_frame]). *)
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

(** A change that keeps every region, and every byte and aux slot
    outside the live object b, keeps the agreement of every piece of
    another object: [frame_within] with every piece of b as keys. *)
Lemma frame_other m m' b reg l v :
  m_regions m' = m_regions m -> live_disjoint m -> live_at m b reg ->
  (forall a, ~ (b <= a < r_end reg) -> m_bytes m' a = m_bytes m a /\ m_aux m' a = m_aux m a) ->
  piece_id l <> b -> agree_piece m l v -> agree_piece m' l v.
Proof.
  intros Hr Hd Hl Hout Hid.
  set (ks := (PByte b <$> seqZ 0 (r_end reg - b)) ++ (PAux b <$> seqZ 0 (r_end reg - b))).
  apply (frame_within ks m m' b reg Hr Hd Hl).
  - intros a H. apply Hout. intros Ha. apply (H Ha). apply elem_of_app. left.
    apply list_elem_of_fmap_2. apply elem_of_seqZ. lia.
  - intros a H. apply Hout. intros Ha. apply (H Ha). apply elem_of_app. right.
    apply list_elem_of_fmap_2. apply elem_of_seqZ. lia.
  - intros Hk. apply elem_of_app in Hk as [Hk|Hk]; apply list_elem_of_fmap in Hk as (o & -> & _);
      exact (Hid eq_refl).
Qed.

(** The memory and aux triples over any [[runtime]] R. *)
Module MemLogic (R : Runtime).
Module SL := StringLogic R.
Module LG := SL.LG.
Module L := LG.L.
Import L LG SL.

Section mem.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.

(** [bytes] b o xs: owning the bytes xs from offset o of the object b. *)
Definition bytes (b o : Z) (xs : list Z) : iProp Σ := pts (byte_ps b o xs).

(** [auxes] b o cs: owning the aux slots holding cs from offset o of
    the object b. *)
Definition auxes (b o : Z) (cs : list cap) : iProp Σ := pts (aux_ps b o cs).

(** A block's pieces are its life, bytes and slots. *)
Lemma block_pts b reg o xs cs : pts (block_ps b reg o xs cs) ⊣⊢ live b reg ∗ bytes b o xs ∗ auxes b o cs.
Proof. rewrite /block_ps /live /bytes /auxes /pts big_sepL_cons big_sepL_app big_sepL_singleton. done. Qed.

Section calls.
Context {world : Type} (registry : name -> option (contract world))
  (wi : mem -> world -> gmap piece pval -> Prop) `{!SafepointStable wi} (ge : genv).

(** The Iris instance of the registry and wi. *)
Local Instance mem_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry wi ge.

(** The expressions of the language. *)
Local Notation mexpr := (language.expr (nanofil_lang registry ge)).

(** memset's triple, from [memset_contract]: owning the life of the
    object b, at a multiple of 8, with the region reg, and the block of
    the bytes xs and the slots cs from the 8-aligned offset o, inside
    its bounds, where vp reads as the block's pointer, vc as the int c
    and vn as its length, and where the fill keeps the world
    interpretation: the call fills the bytes with c's low byte, clears
    the slots it touches, and binds d to the block's pointer. *)
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

(** malloc's triple, from [malloc_contract]: for a size n that v reads
    as, where an allocation keeps the world interpretation, the call
    binds d to the base pointer of a fresh heap object of n bytes,
    rounded up to 16, whose pieces it owns ([obj]). The selected malloc
    never returns null: a refusal is a resource ending, which is not a
    return, so the triple has no null case. *)
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
      pose proof (agree_piece_registered _ _ _ (Ha l' v0 E)) as Hreg'.
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

(** memcpy's triple, from [memcpy_contract]: owning the destination
    block (the bytes xs and slots cs from offset o of the live object b)
    and the source block (the bytes ys and slots ds from offset o' of
    the live object b', another object, through the capability c', read-write
    or read-only), of the same length, all at multiples of 8, where vd,
    vs and vn read as their pointers and length, and where the copy
    keeps the world interpretation: the destination's bytes become ys,
    its slots [copy_slots], and d is bound to the destination pointer.
    The source is handed back unchanged. *)
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

(** strdup's triple, from [strdup_contract]: owning the string at p,
    which v reads as, in an object at a multiple of 8, the call binds d
    to the base pointer of a fresh heap object holding a copy of the
    string, which it owns as a [string] (its life and the copied bytes;
    the fresh object's other bytes and its aux slots stay unowned), and
    hands the original back. A refusal is a resource ending. *)
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
      pose proof (agree_piece_registered _ _ _ (Ha l' v0 E)) as Hreg'.
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
           ++ intros Hid. pose proof (agree_piece_registered _ _ _ (Ha l' v' Hh)) as Hreg'.
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

End calls.
End mem.
End MemLogic.
