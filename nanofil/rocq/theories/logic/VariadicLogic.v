(** Variadic arguments in the program logic of Logic.v: a variadic
    callee's argument [[snapshot]], the read of its pointer, and
    `va_arg` through a va_list cell. Promoted from HelloVersion.v,
    where `version_etc_va` first needed them.

    A variadic callee starts at [Snapshot xs l] (Semantics.v's
    [call_frame]): one step allocates a [[fresh]] object of 8 bytes
    per argument word, stores each word there ([snapshot_values]: a
    pointer's address in the bytes and its [[capability]] in the
    [[aux]] slot, an integer in the bytes), and binds the hidden
    [va_snapshot] to a read-only pointer to it. [wp_snapshot] hands
    the caller the new object's pieces with the stored values,
    [snapshot_ps], computed from empty memory, which freshness makes
    exact ([snapshot_ps_agree]); [snapshot_ps_cell] and
    [snapshot_ps_pointer] find one argument's cell among them.

    [VaArgs] reads that pointer, frame state only ([wp_va_args]). A
    `va_arg` is a heap write: it reads the cursor stored in the
    va_list cell, reads the argument's cell at the cursor rounded up
    to 8, and stores the advanced cursor back ([wp_va_arg]).
    [va_cursor_ps] is the va_list cell, whose capability stays the
    snapshot's; [wp_va_arg_pointer] reads a pointer cell ([pcell]),
    [wp_va_arg_int] an integer cell ([icell]) at class `w` (its low 4
    bytes) or `l` (all 8). [zero_cell_prefix] turns a zeroed block of
    a fresh object into a null pointer cell, as a va_list or argument
    array starts. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine Identity Panics
  StepRules ExternalCalls ExternalMachine Pieces Heap Language Logic StringLogic MemLogic.
Open Scope Z_scope.
Open Scope list_scope.

(** ## The snapshot's memory *)

(** Snapshot stores at an address depend only on the bytes and
    capability already at that address, not on other memory. *)
Lemma snapshot_values_pointwise xs a m1 m2 t :
  m_bytes m1 t = m_bytes m2 t -> m_aux m1 t = m_aux m2 t ->
  m_bytes (snapshot_values xs a m1) t = m_bytes (snapshot_values xs a m2) t /\
  m_aux (snapshot_values xs a m1) t = m_aux (snapshot_values xs a m2) t.
Proof.
  revert a m1 m2. induction xs as [|x xs IH]; intros a m1 m2 Hb Ha; [exact (conj Hb Ha) |].
  destruct x; cbn [snapshot_values]; apply IH; cbn [store_bytes store_aux m_bytes m_aux];
    try rewrite Hb; try rewrite Ha; reflexivity.
Qed.

(** Taking the snapshot changes no address outside its eight-byte
    argument cells, even for words the snapshot skips. *)
Lemma snapshot_values_outside xs a m t :
  t < a \/ a + 8 * Z.of_nat (length xs) <= t ->
  m_bytes (snapshot_values xs a m) t = m_bytes m t /\ m_aux (snapshot_values xs a m) t = m_aux m t.
Proof.
  revert a m. induction xs as [|x xs IH]; intros a m Hout; [split; reflexivity |].
  cbn [length] in Hout. rewrite Nat2Z.inj_succ in Hout.
  assert (Htail : t < a + 8 \/ a + 8 + 8 * Z.of_nat (length xs) <= t) by lia.
  assert (Hbyte : (a <=? t) && (t <? a + 8) = false).
  { apply andb_false_iff. destruct Hout as [Hout | Hout];
      [left; apply Z.leb_gt; lia | right; apply Z.ltb_ge; lia]. }
  assert (Haux : (t =? a) = false) by (apply Z.eqb_neq; lia).
  destruct x; cbn [snapshot_values];
    match goal with
    | |- m_bytes (snapshot_values xs ?a' ?m') t = _ /\ _ => destruct (IH a' m' Htail) as [Hb Ha]
    end;
    rewrite Hb Ha; cbn [store_bytes store_aux m_bytes m_aux]; rewrite ?Hbyte ?Haux; split; reflexivity.
Qed.

(** The integer a snapshot stores in the bytes of the word x's cell: a
    pointer's address or an integer; none for a word it skips. *)
Definition snapshot_bits (x : word) : option Z :=
  match x with WPtr p => Some (ptr_addr p) | WInt n => Some n | WLimit _ _ => None end.

(** The bytes of argument i survive all the later snapshot stores: byte
    j of its cell is byte j of what [snapshot_bits] says it stores. *)
Lemma snapshot_byte xs i x n a m j :
  xs !! i = Some x -> snapshot_bits x = Some n -> 0 <= j < 8 ->
  m_bytes (snapshot_values xs a m) (a + 8 * Z.of_nat i + j) = byte_of n j.
Proof.
  revert xs a m. induction i as [|i IH]; intros [|y xs] a m Hnth Hn Hj; try discriminate.
  - cbn [lookup list_lookup] in Hnth. injection Hnth as ->. rewrite Z.mul_0_r Z.add_0_r.
    destruct x as [k | p | c s]; cbn [snapshot_bits] in Hn;
      [injection Hn as <- | injection Hn as <- | discriminate]; cbn [snapshot_values];
      rewrite (proj1 (snapshot_values_outside xs (a + 8) _ (a + j) ltac:(left; lia)));
      cbn [store_aux store_bytes m_bytes];
      rewrite (proj2 (Z.leb_le a (a + j)) ltac:(lia)) (proj2 (Z.ltb_lt (a + j) (a + 8)) ltac:(lia));
      cbn [andb]; replace (a + j - a) with j by lia; reflexivity.
  - cbn [lookup list_lookup] in Hnth.
    replace (a + 8 * Z.of_nat (S i) + j) with (a + 8 + 8 * Z.of_nat i + j) by (rewrite Nat2Z.inj_succ; lia).
    destruct y; cbn [snapshot_values]; apply IH; assumption.
Qed.

(** A pointer argument's capability survives all later snapshot stores. *)
Lemma snapshot_pointer_aux xs i p a m :
  xs !! i = Some (WPtr p) -> m_aux (snapshot_values xs a m) (a + 8 * Z.of_nat i) = ptr_cap p.
Proof.
  revert xs a m. induction i as [|i IH]; intros [|x xs] a m Hnth; try discriminate.
  - cbn [lookup list_lookup] in Hnth. injection Hnth as ->.
    cbn [snapshot_values]. rewrite Z.mul_0_r Z.add_0_r.
    rewrite (proj2 (snapshot_values_outside xs (a + 8) _ a ltac:(left; lia))).
    cbn [store_aux m_aux]. rewrite Z.eqb_refl. reflexivity.
  - cbn [lookup list_lookup] in Hnth.
    replace (a + 8 * Z.of_nat (S i)) with (a + 8 + 8 * Z.of_nat i) by (rewrite Nat2Z.inj_succ; lia).
    destruct x; cbn [snapshot_values]; apply IH; assumption.
Qed.

(** ## The snapshot's pieces *)

(** The value of a snapshot piece, computed from empty memory.
    Freshness makes the real allocated cells start with the same zero
    bytes and empty capability slots ([snapshot_ps_agree]). *)
Definition snapshot_piece xs base q (lv : piece * pval) : piece * pval :=
  let m := snapshot_values xs base (allocated empty_mem q base) in
  match lv.1 with
  | PByte b o => (lv.1, VByte (m_bytes m (b + o)))
  | PAux b o => (lv.1, VAux (m_aux m (b + o)))
  | _ => lv
  end.

(** A snapshot owns the keys of its new object ([obj_ps]), with the
    snapshot's bytes and capabilities. *)
Definition snapshot_ps xs base q : list (piece * pval) := snapshot_piece xs base q <$> obj_ps base q.

(** A snapshot's keys are its new object's, so they are distinct
    ([obj_ps_nodup]). *)
Lemma snapshot_ps_keys xs base q : (snapshot_ps xs base q).*1 = (obj_ps base q).*1.
Proof.
  unfold snapshot_ps. rewrite -list_fmap_compose. apply list_fmap_ext.
  intros i [l v] Hi. destruct l; reflexivity.
Qed.

(** The snapshot's pieces hold argument i's whole cell, of the integer
    [snapshot_bits] says it stores. *)
Lemma snapshot_ps_cell xs i x n base q :
  xs !! i = Some x -> snapshot_bits x = Some n -> 8 * Z.of_nat (S i) <= req_extent q ->
  forall l v, (l, v) ∈ cell base (8 * Z.of_nat i) n -> (l, v) ∈ snapshot_ps xs base q.
Proof.
  intros Hnth Hn Hextent l v Hin. unfold cell in Hin.
  apply list_elem_of_fmap in Hin as (j & [= -> ->] & Hj).
  assert (Hjrange : 0 <= j < 8).
  { apply list_elem_of_In in Hj. cbn in Hj. repeat destruct Hj as [<- | Hj]; try contradiction; lia. }
  apply list_elem_of_fmap. exists (PByte base (8 * Z.of_nat i + j), VByte 0). split.
  - unfold snapshot_piece. cbn [fst snd].
    replace (base + (8 * Z.of_nat i + j)) with (base + 8 * Z.of_nat i + j) by lia.
    rewrite (snapshot_byte _ _ _ _ _ _ _ Hnth Hn Hjrange). reflexivity.
  - unfold obj_ps. apply elem_of_cons. right. apply elem_of_app. left.
    apply list_elem_of_fmap. exists (8 * Z.of_nat i + j). split; [reflexivity |].
    apply elem_of_seqZ. rewrite Nat2Z.inj_succ in Hextent. lia.
Qed.

(** The snapshot's pieces hold a pointer argument's whole cell: its
    aux slot and its address bytes ([pcell]). *)
Lemma snapshot_ps_pointer xs i p base q :
  xs !! i = Some (WPtr p) -> 8 * Z.of_nat (S i) <= req_extent q ->
  forall l v, (l, v) ∈ (PAux base (8 * Z.of_nat i), VAux (ptr_cap p)) ::
    cell base (8 * Z.of_nat i) (ptr_addr p) -> (l, v) ∈ snapshot_ps xs base q.
Proof.
  intros Hnth Hextent l v Hin. apply elem_of_cons in Hin as [[= -> ->] | Hin];
    [|exact (snapshot_ps_cell xs i (WPtr p) _ base q Hnth eq_refl Hextent l v Hin)].
  unfold snapshot_ps. apply list_elem_of_fmap.
  exists (PAux base (8 * Z.of_nat i), VAux CNone). split.
  - unfold snapshot_piece. cbn [fst snd]. rewrite (snapshot_pointer_aux _ _ _ _ _ Hnth). reflexivity.
  - unfold obj_ps. apply elem_of_cons. right. apply elem_of_app. right.
    apply list_elem_of_fmap. exists (8 * Z.of_nat i). split; [reflexivity |].
    apply elem_of_seqZ. rewrite Nat2Z.inj_succ in Hextent. lia.
Qed.

(** Each snapshot piece names its fresh object. *)
Lemma snapshot_ps_id xs base q l v : (l, v) ∈ snapshot_ps xs base q -> piece_id l = base.
Proof.
  unfold snapshot_ps. intros Hin. apply list_elem_of_fmap in Hin as ([k u] & Hkv & Hin).
  assert (Hkey : l = k) by (apply (f_equal fst) in Hkv; destruct k; exact Hkv).
  subst l. exact (obj_ps_id _ _ _ _ Hin).
Qed.

(** Every snapshot key is a piece of memory, so a ghost heap that
    agrees with the old memory owns none of them yet. *)
Lemma snapshot_ps_mem xs base q l v : (l, v) ∈ snapshot_ps xs base q -> mem_piece l.
Proof.
  unfold snapshot_ps. intros Hin. apply list_elem_of_fmap in Hin as ([k u] & Hkv & Hin).
  assert (Hkey : l = k) by (apply (f_equal fst) in Hkv; destruct k; exact Hkv).
  subst l. exact (obj_ps_mem _ _ _ _ Hin).
Qed.

(** At a [fresh] base, the computed snapshot pieces agree with the real
    allocation after its argument stores. *)
Lemma snapshot_ps_agree m xs base q :
  Memory.fresh m q base -> all_agree (snapshot_values xs base (allocated m q base)) (snapshot_ps xs base q).
Proof.
  intros (_ & _ & _ & _ & _ & Hz).
  assert (Hsame : forall i, 0 <= i < req_extent q ->
    m_bytes (snapshot_values xs base (allocated m q base)) (base + i) =
      m_bytes (snapshot_values xs base (allocated empty_mem q base)) (base + i) /\
    m_aux (snapshot_values xs base (allocated m q base)) (base + i) =
      m_aux (snapshot_values xs base (allocated empty_mem q base)) (base + i)).
  { intros i Hi. destruct (Hz (base + i) ltac:(lia)) as [Hb Ha].
    apply snapshot_values_pointwise; [exact Hb | exact Ha]. }
  apply all_agree_intro. intros l v Hin.
  unfold snapshot_ps in Hin. apply list_elem_of_fmap in Hin as ([k u] & Hlv & Hin).
  change (agree_piece (snapshot_values xs base (allocated m q base)) (l, v).1 (l, v).2).
  rewrite Hlv. unfold obj_ps in Hin. apply elem_of_cons in Hin as [[= -> ->] | Hin].
  - unfold snapshot_piece. cbn [fst snd agree_piece]. unfold live_at.
    rewrite snapshot_values_regions object_region_allocated Z.eqb_refl. split; reflexivity.
  - apply elem_of_app in Hin as [Hin | Hin];
      apply list_elem_of_fmap in Hin as (i & [= -> ->] & Hi);
      apply elem_of_seqZ in Hi; unfold snapshot_piece; cbn [fst snd agree_piece];
      unfold registered, in_live; rewrite snapshot_values_regions object_region_allocated Z.eqb_refl;
      (split; [discriminate |]); intros reg [= <-] _; cbn [r_end];
      (split; [lia |]); (split; [lia |]).
    + exact (proj1 (Hsame i ltac:(lia))).
    + left. exact (proj2 (Hsame i ltac:(lia))).
Qed.

(** The snapshot's stores keep every piece outside the fresh object's
    keys ([frame_within], from the exact store range). *)
Lemma snapshot_frame m xs base q :
  live_disjoint (allocated m q base) -> 8 * Z.of_nat (length xs) <= req_extent q ->
  frame_ok (obj_ps base q).*1 (allocated m q base) (snapshot_values xs base (allocated m q base)).
Proof.
  intros Hd Hsize. apply (frame_within _ _ _ base (mkRegion base (base + req_extent q) (req_kind q) Live));
    [apply snapshot_values_regions | exact Hd | | |].
  - split; [rewrite object_region_allocated Z.eqb_refl; reflexivity | reflexivity].
  - intros t Hnot. destruct (Z_le_gt_dec base t) as [Hlo | Hlo];
      destruct (Z_lt_ge_dec t (base + req_extent q)) as [Hhi | Hhi];
      try (apply (proj1 (snapshot_values_outside xs base _ t ltac:(lia)))).
    exfalso. apply (Hnot ltac:(cbn; lia)).
    apply list_elem_of_fmap. exists (PByte base (t - base), VByte 0). split; [reflexivity |].
    unfold obj_ps. apply elem_of_cons. right. apply elem_of_app. left.
    apply list_elem_of_fmap. exists (t - base). split; [reflexivity |]. apply elem_of_seqZ. lia.
  - intros t Hnot. destruct (Z_le_gt_dec base t) as [Hlo | Hlo];
      destruct (Z_lt_ge_dec t (base + req_extent q)) as [Hhi | Hhi];
      try (apply (proj2 (snapshot_values_outside xs base _ t ltac:(lia)))).
    exfalso. apply (Hnot ltac:(cbn; lia)).
    apply list_elem_of_fmap. exists (PAux base (t - base), VAux CNone). split; [reflexivity |].
    unfold obj_ps. apply elem_of_cons. right. apply elem_of_app. right.
    apply list_elem_of_fmap. exists (t - base). split; [reflexivity |]. apply elem_of_seqZ. lia.
Qed.

(** The step of a nonempty snapshot: it allocates the argument cells,
    stores the words in them, and binds [va_snapshot] to a read-only
    pointer to them. *)
Lemma rule_snapshot ge f e ls l cs m fuel xs :
  xs <> [] -> forallb snapshot_word xs = true ->
  let q := heap_req 16 (8 * Z.of_nat (length xs)) in
  Semantics.step ge (mkConfig (mkFrame f e ls None (Snapshot xs l)) cs m fuel) =
    Fresh q (fun base => mkConfig
      (mkFrame f (put va_snapshot (WPtr (mkPtr base (Ro base))) e) ls None (Enter l None))
      cs (snapshot_values xs base (allocated m q base)) fuel).
Proof.
  intros Hne Hwords q. destruct xs; [contradiction |].
  cbn [Semantics.step c_frame c_mem c_callers c_fuel fr_at fr_fn fr_env fr_locals fr_doomed].
  rewrite Hwords. reflexivity.
Qed.

(** The pieces of a va_list cell at the object b: its life, the
    cursor's capability and the cursor's address bytes. A read moves
    the address and keeps the capability. *)
Definition va_cursor_ps b reg (cursor : ptr) : list (piece * pval) :=
  [(PLive b, VLive reg); (PAux b 0, VAux (ptr_cap cursor))] ++ cell b 0 (ptr_addr cursor).

(** ## The rules over a Logic instance *)

(** The rules for variadic arguments over the [[runtime]] R and the
    Logic instance LG0. *)
Module VariadicLogicOn (R : Runtime) (LG0 : LogicSig R).
Module LG := LG0.
Module L := LG.L.
Import L LG.

Section variadic.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context {world : Type} (registry : name -> option (contract world))
  (wi : mem -> world -> gmap piece pval -> Prop) `{!SafepointStable wi} (ge : genv).

(** The Iris instance of the registry and wi. *)
Local Instance variadic_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ := nanofil_irisGS registry wi ge.
(** The expressions of the language. *)
Local Notation vexpr := (language.expr (nanofil_lang registry ge)).

(** Eight zero bytes and empty aux slots from offset o of the object
    b are a null pointer cell. *)
Lemma zero_cell b o :
  pts (byte_ps b o (replicate 8 0)) -∗ pts (aux_ps b o (replicate 8 CNone)) -∗ pcell b o null.
Proof.
  assert (Hbyte : forall i, byte_of 0 i = 0).
  { intros i. unfold byte_of. destruct (Z.eq_dec (2 ^ (8 * i)) 0) as [-> | Hne];
      [reflexivity | rewrite Z.div_0_l; [reflexivity | exact Hne]]. }
  assert (Hcell : cell b o 0 = byte_ps b o (replicate 8 0)).
  { unfold cell, byte_ps, seqZ. cbn. rewrite !Hbyte Nat2Z.id. cbn. repeat (f_equal; try lia). }
  rewrite /pcell /pts big_sepL_cons Hcell.
  change (replicate 8 CNone) with (CNone :: replicate 7 CNone). rewrite aux_ps_cons big_sepL_cons.
  iIntros "Hx [Ha _]". iFrame "Ha Hx".
Qed.

(** A zeroed block of 8 + n bytes and slots from offset o, as a fresh
    object's ([obj_zero_block]), starts with a null pointer cell; the
    rest is handed back. A va_list or an argument array gets its null
    cells this way, without expanding the block piece by piece. *)
Lemma zero_cell_prefix b o n :
  pts (byte_ps b o (replicate (8 + n) 0)) -∗ pts (aux_ps b o (replicate (8 + n) CNone)) -∗
  pcell b o null ∗ pts (byte_ps b (o + 8) (replicate n 0)) ∗ pts (aux_ps b (o + 8) (replicate n CNone)).
Proof.
  rewrite !replicate_add byte_ps_app aux_ps_app !pts_app.
  iIntros "[Hx Hrest] [Ha Htail]". iFrame "Hrest Htail". iApply (zero_cell with "Hx Ha").
Qed.

(** Allocating a nonempty variadic snapshot gives its populated pieces
    ([snapshot_ps]), with the read-only pointer bound in the frame:
    [rule_snapshot] lifted through [wp_lift_run]. The snapshot must
    keep the caller's world interpretation. *)
Lemma wp_snapshot f e ls l xs Φ :
  xs <> [] -> forallb snapshot_word xs = true ->
  let q := heap_req 16 (8 * Z.of_nat (length xs)) in
  (forall m wd h base, Memory.fresh m q base -> wi m wd h ->
    wi (snapshot_values xs base (allocated m q base)) wd (overwrite (snapshot_ps xs base q) h)) ->
  ▷ (∀ base, ⌜0 < base /\ base mod req_align q = 0 /\ base + req_extent q <= 2 ^ 48⌝ -∗
    pts (snapshot_ps xs base q) -∗
    WP (ERun (mkFrame f (put va_snapshot (WPtr (mkPtr base (Ro base))) e)
      ls None (Enter l None)) : vexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Snapshot xs l)) : vexpr) {{ Φ }}.
Proof.
  intros Hne Hwords q Hwi.
  assert (Hex : 0 <= req_extent q).
  { pose proof (heap_req_extent 16 (8 * Z.of_nat (length xs))). unfold q. lia. }
  assert (Hal : 0 < req_align q) by (cbn; lia).
  pose proof (fun m fuel => rule_snapshot ge f e ls l [] m fuel xs Hne Hwords) as Hst.
  iIntros "HK". iApply (wp_lift_run with "HK").
  - iIntros (σ) "_ _". iPureIntro. left. unfold fails. rewrite Hst. fold q. lia.
  - iIntros ([m s fuel w]) "Hσ HK". iNext. iIntros (e2 σ2 Hm).
    destruct (moves_core registry ge _ _ _ _ Hm
      ltac:(intros ?; cbn [ls_mem ls_fuel]; rewrite Hst; discriminate))
      as [(c' & E' & _) | [(q' & kk & base & s' & E' & _ & Ha & -> & ->) | (o & m' & E' & _)]];
      cbn [ls_mem ls_fuel ls_rt] in E'; rewrite Hst in E'; try discriminate E'.
    injection E' as <- <-. cbn [conf_expr conf_state stack_expr c_frame c_callers c_mem c_fuel].
    fold q in Ha |- *.
    iDestruct "Hσ" as (h) "[Hh %Hσ]". destruct Hσ as (Hag & Hd & Hr & Hw).
    cbn [ls_mem ls_rt ls_world] in Hag, Hd, Hr, Hw.
    destruct (R.fresh_allocation _ _ _ _ _ Hr Hal Hex Ha) as [Hf Hr_alloc].
    pose proof Hf as (Hpos & Hmod & _ & Hn & _).
    assert (Hd_alloc : live_disjoint (allocated m q base)) by exact (live_disjoint_allocated _ _ _ Hd Hf Hex).
    assert (Hr' : R.ready s' (snapshot_values xs base (allocated m q base))).
    { apply (R.ready_kept _ _ _ Hr_alloc). exact (snapshot_alloc_kept xs m base). }
    pose proof (snapshot_frame m xs base q Hd_alloc (heap_req_extent 16 (8 * Z.of_nat (length xs))))
      as Hframe.
    iMod (pts_alloc h (snapshot_ps xs base q) with "Hh") as "[Hh Hps]".
    { rewrite snapshot_ps_keys. apply obj_ps_nodup. }
    { intros k v Hin. destruct (h !! k) as [u|] eqn:E; [|reflexivity]. exfalso.
      pose proof (agree_piece_registered _ _ _ (snapshot_ps_mem _ _ _ _ _ Hin) (Hag k u E)) as Hreg.
      rewrite (snapshot_ps_id _ _ _ _ _ Hin) in Hreg. exact (Hreg Hn). }
    iModIntro. iSplitL "Hh".
    + iExists _. iFrame "Hh". iPureIntro. cbn [ls_mem ls_rt ls_world].
      split; [|split; [|split]].
      * intros k v Hk. destruct (lookup_overwrite _ _ _ _ Hk) as [Hin | [Hnot Hold]].
        -- exact (all_agree_elem _ _ _ _ (snapshot_ps_agree _ _ _ _ Hf) Hin).
        -- rewrite snapshot_ps_keys in Hnot.
           apply (Hframe k v Hnot). exact (agree_piece_allocated _ _ _ _ _ Hn (Hag k v Hold)).
      * apply (live_disjoint_regions (allocated m q base)); [apply snapshot_values_regions | exact Hd_alloc].
      * exact Hr'.
      * exact (Hwi m w h base Hf Hw).
    + iApply ("HK" with "[%] Hps"). split; [exact Hpos |]. split; [exact Hmod |].
      destruct (R.address_space _ _ Hr' base (mkRegion base (base + req_extent q) (req_kind q) Live))
        as [_ Hend]; [|exact Hend].
      rewrite snapshot_values_regions object_region_allocated Z.eqb_refl. reflexivity.
Qed.

(** [VaArgs] reads the snapshot pointer at the offset off, frame state
    only: [rule_va_args] lifted through [wp_pure_next]. *)
Lemma wp_va_args f e ls l d off rest j p Φ :
  lookup va_snapshot e = Some (WPtr p) ->
  ▷ WP (ERun (mkFrame f (put d (WPtr (mkPtr ((ptr_addr p + off) mod 2 ^ 64) (ptr_cap p))) e)
      ls None (Exec l rest j)) : vexpr) {{ Φ }} -∗
  WP (ERun (mkFrame f e ls None (Exec l (Let d P VaArgs [Const off] :: rest) j)) : vexpr) {{ Φ }}.
Proof. intros Hp. apply (wp_pure_next registry wi ge _ _ []). intros m fuel. apply rule_va_args. exact Hp. Qed.

(** A variadic read is a heap write: owning the pieces ps, every memory
    they agree with reads x by [va_arg_res] and becomes [upd] m, which
    keeps its regions, agrees with ps' (the same keys) and changes
    nothing else, keeping the world interpretation: [rule_va_arg]
    lifted through [wp_write]. *)
Lemma wp_va_arg f e ls l d k args rest j p x ps ps' upd Φ :
  map2_option (value_x ge e) [P] args = Some [WPtr p] -> ps'.*1 = ps.*1 ->
  (forall m, owned_facts ps m ->
    va_arg_res k p m = Some (RVal x, upd m) /\ m_regions (upd m) = m_regions m /\ kept m (upd m) /\
    all_agree (upd m) ps' /\ frame_ok ps'.*1 m (upd m)) ->
  (forall m w h, (forall l v, (l, v) ∈ ps -> h !! l = Some v) -> wi m w h ->
    wi (upd m) w (overwrite ps' h)) ->
  pts ps -∗ ▷ (pts ps' -∗ WP (ERun (mkFrame f (put d x e) ls None (Exec l rest j)) : vexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (Let d k VaArg args :: rest) j)) : vexpr) {{ Φ }}.
Proof.
  intros Hargs Hkeys Hread Hwi. iIntros "Hps HK".
  iApply (wp_write registry wi ge ps ps' _ _ [] upd with "Hps HK"); [exact Hkeys | | exact Hwi].
  intros m fuel Hfacts. destruct (Hread m Hfacts) as (Hres & Hrest).
  split; [exact (rule_va_arg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hargs Hres) | exact Hrest].
Qed.

(** A pointer va_arg reads its snapshot cell and advances only the
    mutable cursor. The source and literal pieces are framed, including
    when the argument is the terminating null pointer. *)
Lemma wp_va_arg_pointer f e ls l d args rest j cb cr sb sr off x ps Φ :
  map2_option (value_x ge e) [P] args = Some [WPtr (mkPtr cb (Obj cb))] ->
  cb mod 8 = 0 -> 0 < sb -> 0 <= off -> sb + off + 8 <= r_end sr -> r_end sr <= 2 ^ 48 ->
  (sb + off) mod 8 = 0 -> 0 <= ptr_addr x < 2 ^ 64 ->
  (ptr_cap x = CNone \/ exists xb xr,
    (ptr_cap x = Obj xb \/ ptr_cap x = Ro xb) /\ (PLive xb, VLive xr) ∈ ps) ->
  (forall m w h,
    (forall k v, (k, v) ∈ va_cursor_ps cb cr (mkPtr (sb + off) (Ro sb)) -> h !! k = Some v) ->
    wi m w h -> wi (store_bytes m cb 8 (sb + off + 8)) w
      (overwrite (va_cursor_ps cb cr (mkPtr (sb + off + 8) (Ro sb))) h)) ->
  pts (va_cursor_ps cb cr (mkPtr (sb + off) (Ro sb))) -∗
  live sb sr -∗ pcell sb off x -∗ pts ps -∗
  ▷ (pts (va_cursor_ps cb cr (mkPtr (sb + off + 8) (Ro sb))) -∗
    live sb sr -∗ pcell sb off x -∗ pts ps -∗
    WP (ERun (mkFrame f (put d (WPtr x) e) ls None (Exec l rest j)) : vexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (Let d P VaArg args :: rest) j)) : vexpr) {{ Φ }}.
Proof.
  intros Hargs Hcb Hsb Hoff Hsend Hsmax Hal Hrange Htarget Hwi.
  set (before := va_cursor_ps cb cr (mkPtr (sb + off) (Ro sb))).
  set (after := va_cursor_ps cb cr (mkPtr (sb + off + 8) (Ro sb))).
  set (reads := [(PLive sb, VLive sr); (PAux sb off, VAux (ptr_cap x))] ++
    cell sb off (ptr_addr x) ++ ps).
  iIntros "Hcursor Hsl Hsc Hps HK".
  iAssert (pts (before ++ reads)) with "[Hcursor Hsl Hsc Hps]" as "Hpieces".
  { rewrite pts_app. iFrame "Hcursor".
    replace reads with ([(PLive sb, VLive sr)] ++
      ((PAux sb off, VAux (ptr_cap x)) :: cell sb off (ptr_addr x)) ++ ps) by reflexivity.
    rewrite !pts_app.
    iFrame "Hsl Hsc Hps". }
  iDestruct (pts_keys_nodup with "Hpieces") as %Hnd.
  rewrite fmap_app in Hnd. apply NoDup_app in Hnd as (_ & Hseparate & _).
  iApply (wp_va_arg f e ls l d P args rest j (mkPtr cb (Obj cb)) (WPtr x)
    (before ++ reads) (after ++ reads) (fun m => store_bytes m cb 8 (sb + off + 8))
    with "Hpieces [HK]").
  - exact Hargs.
  - rewrite !fmap_app. unfold before, after, va_cursor_ps, cell. reflexivity.
  - intros m (Hagree & Hd & _).
    apply all_agree_app in Hagree as [Hcur Hreads].
    unfold before, va_cursor_ps in Hcur. cbn [all_agree fst snd] in Hcur.
    destruct Hcur as (Hclive & Hcaux & Hcbytes).
    unfold reads in Hreads. cbn [all_agree fst snd] in Hreads.
    destruct Hreads as (Hslive & Hsaux & Hrest).
    change (all_agree m (cell sb off (ptr_addr x) ++ ps)) in Hrest.
    destruct (proj1 (all_agree_app m (cell sb off (ptr_addr x)) ps) Hrest) as [Hsbytes Hps].
    destruct (cell_bounds _ _ _ _ _ Hclive Hcbytes) as [Hc0 Hcend].
    destruct (cell_store_ok m cb cr 0 cb (sb + off + 8) Hd Hclive Hc0 ltac:(lia) ltac:(lia))
      as [Hnew Hframe].
    assert (Hframe_reads : all_agree (store_bytes m cb 8 (sb + off + 8)) reads).
    { apply all_agree_intro. intros k v Hin. apply Hframe.
      - intros Hkey. apply (Hseparate k).
        + unfold before, va_cursor_ps. rewrite fmap_app. apply elem_of_app. right. exact Hkey.
        + exact (list_elem_of_fmap_2 fst _ _ Hin).
      - apply (all_agree_elem _ reads k v); [|exact Hin].
        unfold reads. cbn [all_agree fst snd]. split; [exact Hslive |].
        split; [exact Hsaux |].
        apply (proj2 (all_agree_app m (cell sb off (ptr_addr x)) ps)). auto. }
    assert (Hslive' : live_at (store_bytes m cb 8 (sb + off + 8)) sb sr).
    { exact Hslive. }
    assert (Hsaux' : agree_piece (store_bytes m cb 8 (sb + off + 8))
      (PAux sb off) (VAux (ptr_cap x))).
    { apply (all_agree_elem _ reads _ _ Hframe_reads). unfold reads. cbn. right. left. }
    assert (Hsbytes' : all_agree (store_bytes m cb 8 (sb + off + 8))
      (cell sb off (ptr_addr x))).
    { apply all_agree_intro. intros k v Hin. apply (all_agree_elem _ reads k v Hframe_reads).
      unfold reads. apply elem_of_app. right. apply elem_of_app. left. exact Hin. }
    assert (Hcursor : load_bytes m cb 8 = sb + off).
    { replace cb with (cb + 0) at 1 by lia.
      rewrite (cell_load m cb cr 0 (sb + off) (cb + 0) Hclive Hcbytes eq_refl).
      apply Z.mod_small. lia. }
    assert (Hcursor_cap : aux_at m cb = Ro sb).
    { unfold aux_at. replace cb with (cb + 0) at 1 by lia.
      apply (aux_holds_ro m (cb + 0) sb sr); [|exact Hslive].
      exact (aux_piece_holds _ _ _ _ _ Hclive Hcaux). }
    assert (Hresult_cap : aux_at (store_bytes m cb 8 (sb + off + 8)) (sb + off) = ptr_cap x).
    { unfold aux_at. pose proof (aux_piece_holds _ _ _ _ _ Hslive' Hsaux') as Haux.
      destruct Htarget as [Hnull | (xb & xr & [Hobj | Hro] & Hmember)].
      - apply aux_holds_live; [exact Haux | auto].
      - apply aux_holds_live; [exact Haux |]. right. exists xb, xr. split; [exact Hobj |].
        exact (all_agree_elem _ _ _ _ Hps Hmember).
      - rewrite Hro in Haux |- *. apply (aux_holds_ro _ _ _ xr Haux).
        exact (all_agree_elem _ _ _ _ Hps Hmember). }
    split.
    + apply (va_arg_pointer m (mkPtr cb (Obj cb)) (sb + off) (Ro sb)
        (store_bytes m cb 8 (sb + off + 8)) x).
      * cbn [ptr_addr ptr_cap]. apply (access_obj _ _ cr); [exact (proj1 Hclive) | lia | lia | exact Hcb].
      * exact Hcursor.
      * exact Hcursor_cap.
      * exact Hal.
      * apply (access_ro_read _ _ sr); [exact (proj1 Hslive) | lia | exact Hsend | exact Hal].
      * apply store_res_long. cbn [ptr_addr ptr_cap].
        apply (access_obj _ _ cr); [exact (proj1 Hclive) | lia | lia | apply Z.mod_1_r].
      * rewrite (cell_load _ sb sr off (ptr_addr x) (sb + off) Hslive' Hsbytes' eq_refl).
        apply Z.mod_small. exact Hrange.
      * exact Hresult_cap.
    + split; [reflexivity |]. split.
      * apply store_bytes_kept. exact (in_object_live _ _ _ cb Hclive ltac:(lia) ltac:(lia)).
      * split.
        -- apply all_agree_app. split; [|exact Hframe_reads].
           unfold after, va_cursor_ps. cbn [all_agree fst snd]. split; [exact Hclive |].
           split; [exact Hcaux | exact Hnew].
        -- eapply frame_ok_mono; [|exact Hframe]. intros k Hin.
           rewrite fmap_app. apply elem_of_app. left.
           unfold after, va_cursor_ps. rewrite fmap_app. apply elem_of_app. right.
           exact Hin.
  - intros m w h Hown Hw. rewrite overwrite_app.
    rewrite (overwrite_id reads h).
    + apply Hwi; [|exact Hw]. intros k v Hin. apply Hown.
      apply elem_of_app. left. exact Hin.
    + intros k v Hin. apply Hown. apply elem_of_app. right. exact Hin.
  - iNext. iIntros "Hpieces". iEval (rewrite pts_app) in "Hpieces".
    iDestruct "Hpieces" as "[Hcursor Hreads]".
    iEval (rewrite /reads; rewrite pts_app) in "Hreads".
    iDestruct "Hreads" as "[Hhead Htail]".
    iEval (rewrite pts_app) in "Htail". iDestruct "Htail" as "[Hsc Hps]".
    iEval (rewrite /pts !big_sepL_cons) in "Hhead".
    iDestruct "Hhead" as "(Hsl & Hsa & _)".
    iApply ("HK" with "Hcursor [Hsl] [Hsa Hsc] Hps");
      rewrite /live /pcell /pts; iFrame; done.
Qed.

(** An integer va_arg of class `w` or `l` reads the n low bytes (4 or 8)
    of an integer cell of the snapshot at the cursor cur rounded up to
    8, and stores the cursor past them, sb + off + n: d is bound to v
    modulo 2^(8n). Only the va_list cell changes; the snapshot's life
    and cell are handed back. *)
Lemma wp_va_arg_int f e ls l d k n args rest j cb cr cur sb sr off v Φ :
  (k = W /\ n = 4) \/ (k = L /\ n = 8) ->
  map2_option (value_x ge e) [P] args = Some [WPtr (mkPtr cb (Obj cb))] ->
  cb mod 8 = 0 -> 0 < sb -> 0 <= off -> sb + off + 8 <= r_end sr -> r_end sr <= 2 ^ 48 ->
  0 <= cur -> (cur + 8 - 1) / 8 * 8 = sb + off ->
  (forall m wd h,
    (forall k' v', (k', v') ∈ va_cursor_ps cb cr (mkPtr cur (Ro sb)) -> h !! k' = Some v') ->
    wi m wd h -> wi (store_bytes m cb 8 (sb + off + n)) wd
      (overwrite (va_cursor_ps cb cr (mkPtr (sb + off + n) (Ro sb))) h)) ->
  pts (va_cursor_ps cb cr (mkPtr cur (Ro sb))) -∗ live sb sr -∗ icell sb off v -∗
  ▷ (pts (va_cursor_ps cb cr (mkPtr (sb + off + n) (Ro sb))) -∗ live sb sr -∗ icell sb off v -∗
    WP (ERun (mkFrame f (put d (WInt (v mod 2 ^ (8 * n))) e) ls None (Exec l rest j)) : vexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (Let d k VaArg args :: rest) j)) : vexpr) {{ Φ }}.
Proof.
  intros Hk Hargs Hcb Hsb Hoff Hsend Hsmax Hcur0 Hround Hwi.
  assert (Hw : exists w, k <> P /\ class_width k = Some w /\ va_cell k = Some (n, 8) /\
    width_bytes w = n /\ 0 < n <= 8)
    by (destruct Hk as [[-> ->] | [-> ->]]; eexists; repeat split; try discriminate; reflexivity || lia).
  destruct Hw as (w & HkP & Hcw & Hcl & Hwn & Hn).
  assert (Hal : (sb + off) mod 8 = 0) by (rewrite -Hround; apply Z.mod_mul; lia).
  assert (Hle : cur <= sb + off).
  { pose proof (Z.div_mod (cur + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (cur + 8 - 1) 8 ltac:(lia)).
    lia. }
  set (before := va_cursor_ps cb cr (mkPtr cur (Ro sb))).
  set (after := va_cursor_ps cb cr (mkPtr (sb + off + n) (Ro sb))).
  set (reads := [(PLive sb, VLive sr)] ++ cell sb off v).
  iIntros "Hcursor Hsl Hsc HK".
  iAssert (pts (before ++ reads)) with "[Hcursor Hsl Hsc]" as "Hpieces".
  { rewrite /reads !pts_app. iFrame. }
  iDestruct (pts_keys_nodup with "Hpieces") as %Hnd.
  rewrite fmap_app in Hnd. apply NoDup_app in Hnd as (_ & Hseparate & _).
  iApply (wp_va_arg f e ls l d k args rest j (mkPtr cb (Obj cb)) (WInt (v mod 2 ^ (8 * n)))
    (before ++ reads) (after ++ reads) (fun m => store_bytes m cb 8 (sb + off + n))
    with "Hpieces [HK]").
  - exact Hargs.
  - rewrite !fmap_app. unfold before, after, va_cursor_ps, cell. reflexivity.
  - intros m (Hagree & Hd & _).
    apply all_agree_app in Hagree as [Hcur Hreads].
    unfold before, va_cursor_ps in Hcur. cbn [all_agree fst snd] in Hcur.
    destruct Hcur as (Hclive & Hcaux & Hcbytes).
    unfold reads in Hreads. cbn [all_agree fst snd] in Hreads. destruct Hreads as (Hslive & Hsbytes).
    destruct (cell_bounds _ _ _ _ _ Hclive Hcbytes) as [Hc0 Hcend].
    destruct (cell_store_ok m cb cr 0 cb (sb + off + n) Hd Hclive Hc0 ltac:(lia) ltac:(lia))
      as [Hnew Hframe].
    assert (Hframe_reads : all_agree (store_bytes m cb 8 (sb + off + n)) reads).
    { apply all_agree_intro. intros k' v' Hin. apply Hframe.
      - intros Hkey. apply (Hseparate k').
        + unfold before, va_cursor_ps. rewrite fmap_app. apply elem_of_app. right. exact Hkey.
        + exact (list_elem_of_fmap_2 fst _ _ Hin).
      - apply (all_agree_elem _ reads k' v'); [|exact Hin].
        unfold reads. cbn [all_agree fst snd]. split; [exact Hslive | exact Hsbytes]. }
    assert (Hsbytes' : all_agree (store_bytes m cb 8 (sb + off + n)) (cell sb off v)).
    { apply all_agree_intro. intros k' v' Hin. apply (all_agree_elem _ reads k' v' Hframe_reads).
      unfold reads. apply elem_of_app. right. exact Hin. }
    assert (Hcursor : load_bytes m cb 8 = cur).
    { replace cb with (cb + 0) at 1 by lia.
      rewrite (cell_load m cb cr 0 cur (cb + 0) Hclive Hcbytes eq_refl). apply Z.mod_small. lia. }
    assert (Hcursor_cap : aux_at m cb = Ro sb).
    { unfold aux_at. replace cb with (cb + 0) at 1 by lia.
      apply (aux_holds_ro m (cb + 0) sb sr); [|exact Hslive].
      exact (aux_piece_holds _ _ _ _ _ Hclive Hcaux). }
    split.
    + replace (v mod 2 ^ (8 * n)) with
        (load_bytes (store_bytes m cb 8 (sb + off + n)) (sb + off) (width_bytes w)).
      * apply (va_arg_int m k w n (mkPtr cb (Obj cb)) cur (Ro sb) (sb + off)); try assumption.
        -- cbn [ptr_addr ptr_cap]. apply (access_obj _ _ cr); [exact (proj1 Hclive) | lia | lia | exact Hcb].
        -- apply (access_ro_read _ _ sr); [exact (proj1 Hslive) | lia | lia | exact Hal].
        -- apply store_res_long. cbn [ptr_addr ptr_cap].
           apply (access_obj _ _ cr); [exact (proj1 Hclive) | lia | lia | apply Z.mod_1_r].
      * rewrite Hwn. apply (cell_load_low (store_bytes m cb 8 (sb + off + n)) sb sr off v (sb + off) n
          Hslive Hsbytes' eq_refl). lia.
    + split; [reflexivity |]. split.
      * apply store_bytes_kept. exact (in_object_live _ _ _ cb Hclive ltac:(lia) ltac:(lia)).
      * split.
        -- apply all_agree_app. split; [|exact Hframe_reads].
           unfold after, va_cursor_ps. cbn [all_agree fst snd]. split; [exact Hclive |].
           split; [exact Hcaux | exact Hnew].
        -- eapply frame_ok_mono; [|exact Hframe]. intros k' Hin.
           rewrite fmap_app. apply elem_of_app. left.
           unfold after, va_cursor_ps. rewrite fmap_app. apply elem_of_app. right. exact Hin.
  - intros m wd h Hown Hw. rewrite overwrite_app (overwrite_id reads h).
    + apply Hwi; [|exact Hw]. intros k' v' Hin. apply Hown. apply elem_of_app. left. exact Hin.
    + intros k' v' Hin. apply Hown. apply elem_of_app. right. exact Hin.
  - iNext. iIntros "Hpieces". rewrite !pts_app. iDestruct "Hpieces" as "(Hcursor & Hsl & Hsc)".
    iApply ("HK" with "Hcursor Hsl Hsc").
Qed.

End variadic.
End VariadicLogicOn.
