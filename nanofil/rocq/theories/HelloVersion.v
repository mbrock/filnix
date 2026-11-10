(** GNU Hello's version and help helpers through the program logic.
    The output contracts are supplied by the caller's stdio world;
    stdout remains world-owned. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import ZArith Lia.
From Stdlib Require String.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run StepRules Symbolic
  ExternalCalls ExternalMachine Pieces Heap ContractFrame Language Logic StringLogic MemLogic
  HelloModule HelloLeaf Identity Machine Panics.
Open Scope Z_scope.
Open Scope list_scope.

(** The compiled proper-name helper returns its argument unchanged. *)
Definition proper_name_fn : func := Eval vm_compute in hello_fn "proper_name".
(** Its empty entry block returns the pointer. *)
Definition proper_name_start : block := Eval vm_compute in hblk proper_name_fn "start".
(** The entry block is present in the compiled function. *)
Lemma find_proper_name_start :
  find_block (TAtom "start") (fn_blocks proper_name_fn) = Some proper_name_start.
Proof. vm_compute. reflexivity. Qed.
(** Its call frame binds the sole pointer argument. *)
Lemma proper_name_entry p : invocation proper_name_fn [WPtr p] =
  mkFrame proper_name_fn [(TAtom "v0", WPtr p)] [] None (Enter (TAtom "start") None).
Proof. reflexivity. Qed.

(** The help footer prints the bug-reporting addresses. *)
Definition emit_bug_reporting_address_fn : func := Eval vm_compute in hello_fn "emit_bug_reporting_address".
(** Its single block loads stdout and makes four output calls. *)
Definition emit_bug_reporting_address_start : block := Eval vm_compute in
  hblk emit_bug_reporting_address_fn "start".
(** The footer's entry block is present. *)
Lemma find_emit_bug_reporting_address_start :
  find_block (TAtom "start") (fn_blocks emit_bug_reporting_address_fn) =
    Some emit_bug_reporting_address_start.
Proof. vm_compute. reflexivity. Qed.

(** A version-etc literal's pointer in the linked fixture. *)
Definition version_literal (s : String.string) : ptr := Eval vm_compute in
  match lookup (TAtom s) hello_globals with Some p => p | None => mkPtr 0 CNone end.

(** The four exact output argument lists in the help footer: the newline,
    bug address, home-page line, and general-help line. *)
Definition emit_output_args (stdout : ptr) : list (name * list word) :=
  [(TAtom "fputs", [WPtr (version_literal "version-etc#str.45"); WPtr stdout]);
   (TAtom "printf", [WPtr (version_literal "version-etc#str.58");
                     WPtr (version_literal "version-etc#str.59")]);
   (TAtom "printf", [WPtr (version_literal "version-etc#str.60");
                     WPtr (version_literal "version-etc#str.61");
                     WPtr (version_literal "version-etc#str.62")]);
   (TAtom "printf", [WPtr (version_literal "version-etc#str.63");
                     WPtr (version_literal "version-etc#str.64")])].

(** For promotion: reading the hidden variadic snapshot is a pure
    instruction. Its pointer is frame state, not a new heap resource.
    This equation follows [rule_inst] and [inst_step]. *)
Lemma rule_va_args ge f e ls l d off rest j cs m fuel p :
  lookup va_snapshot e = Some (WPtr p) ->
  Semantics.step ge
    (mkConfig (mkFrame f e ls None (Exec l (Let d P VaArgs [Const off] :: rest) j)) cs m fuel) =
  Next (mkConfig
    (mkFrame f (put d (WPtr (mkPtr ((ptr_addr p + off) mod 2 ^ 64) (ptr_cap p))) e)
      ls None (Exec l rest j)) cs m fuel).
Proof.
  intros Hp. apply (rule_inst ge f e ls l (Let d P VaArgs [Const off]) rest j cs m fuel
    (IContinue (put d (WPtr (mkPtr ((ptr_addr p + off) mod 2 ^ 64) (ptr_cap p))) e) ls m)).
  - cbn [inst_step fr_env fr_locals]. rewrite Hp. reflexivity.
  - apply doomed_result_continue. reflexivity.
Qed.

(** For promotion: a successful variadic read updates the cursor's
    memory and binds its result. This is [rule_let] specialized to
    [va_arg_res]; the cursor is not frame-only state. *)
Lemma rule_va_arg ge f e ls l d k args rest j cs m fuel p x m' :
  map2_option (value_x ge e) [P] args = Some [WPtr p] ->
  va_arg_res k p m = Some (RVal x, m') ->
  Semantics.step ge
    (mkConfig (mkFrame f e ls None (Exec l (Let d k VaArg args :: rest) j)) cs m fuel) =
  Next (mkConfig (mkFrame f (put d x e) ls None (Exec l rest j)) cs m' fuel).
Proof.
  intros Hargs Hread. apply rule_let with (classes := [P]) (xs := [WPtr p]);
    [reflexivity | reflexivity | exact Hargs |].
  cbn [op_res]. rewrite Hread. reflexivity.
Qed.

(** For promotion: taking the pointer argument at an aligned cursor
    reads its bytes and capability after advancing the cursor. The
    hypotheses expose both checked reads and the checked cursor write,
    including the case where the write overlaps the argument cell. *)
Lemma va_arg_pointer m p a c m' x :
  access_res m (ptr_addr p) (ptr_cap p) 8 Read 8 = Some ok ->
  load_bytes m (ptr_addr p) 8 = a -> aux_at m (ptr_addr p) = c ->
  a mod 8 = 0 -> access_res m a c 8 Read 8 = Some ok ->
  store_res Wl m (ptr_addr p) (ptr_cap p) (WInt (a + 8)) = Some (ok, m') ->
  load_bytes m' a 8 = ptr_addr x -> aux_at m' a = ptr_cap x ->
  va_arg_res P p m = Some (RVal (WPtr x), m').
Proof.
  intros Hp Ha Hc Hal Hcell Hstore Haddr Hcap.
  assert (Halign : (a + 8 - 1) / 8 * 8 = a).
  { pose proof (Z.div_mod a 8 ltac:(lia)) as Hdiv.
    rewrite Hal in Hdiv.
    replace (a + 8 - 1) with (7 + (a / 8) * 8) by lia.
    rewrite Z.div_add; [|lia].
    replace (7 / 8) with 0 by reflexivity. lia. }
  unfold va_arg_res. rewrite Hp Ha Hc.
  cbn [va_cell class_width width_bytes ptr_addr ptr_cap].
  rewrite Halign Hcell Hstore Haddr Hcap. destruct x. reflexivity.
Qed.

(** For promotion: snapshot stores at an address depend only on the
    bytes and capability already at that address, not on other memory. *)
Lemma snapshot_values_pointwise xs a m1 m2 t :
  m_bytes m1 t = m_bytes m2 t -> m_aux m1 t = m_aux m2 t ->
  m_bytes (snapshot_values xs a m1) t = m_bytes (snapshot_values xs a m2) t /\
  m_aux (snapshot_values xs a m1) t = m_aux (snapshot_values xs a m2) t.
Proof.
  revert a m1 m2. induction xs as [|x xs IH]; intros a m1 m2 Hb Ha;
    [exact (conj Hb Ha) |].
  destruct x; cbn [snapshot_values]; apply IH;
    cbn [store_bytes store_aux m_bytes m_aux];
    try rewrite Hb; try rewrite Ha; reflexivity.
Qed.

(** For promotion: taking the snapshot changes no address outside its
    eight-byte argument cells, even for words the snapshot skips. *)
Lemma snapshot_values_outside xs a m t :
  t < a \/ a + 8 * Z.of_nat (length xs) <= t ->
  m_bytes (snapshot_values xs a m) t = m_bytes m t /\
  m_aux (snapshot_values xs a m) t = m_aux m t.
Proof.
  revert a m. induction xs as [|x xs IH]; intros a m Hout; [split; reflexivity |].
  cbn [length] in Hout. rewrite Nat2Z.inj_succ in Hout.
  assert (Htail : t < a + 8 \/ a + 8 + 8 * Z.of_nat (length xs) <= t).
  { lia. }
  assert (Hbyte : (a <=? t) && (t <? a + 8) = false).
  { apply andb_false_iff. destruct Hout as [Hout | Hout].
    - left. apply Z.leb_gt. lia.
    - right. apply Z.ltb_ge. lia. }
  assert (Haux : (t =? a) = false).
  { apply Z.eqb_neq. destruct Hout as [Hout | Hout];
      rewrite ?Nat2Z.inj_succ in Hout; lia. }
  destruct x; cbn [snapshot_values];
    match goal with
    | |- m_bytes (snapshot_values xs ?a' ?m') t = _ /\ _ =>
        destruct (IH a' m' Htail) as [Hb Ha]
    end;
    rewrite Hb Ha;
    cbn [store_bytes store_aux m_bytes m_aux]; rewrite ?Hbyte ?Haux; split; reflexivity.
Qed.

(** For promotion: values for a snapshot's pieces can be computed from
    empty memory. Freshness guarantees the actual allocated cells start
    with the same zero bytes and empty capability slots. *)
Definition snapshot_piece xs base q (lv : piece * pval) : piece * pval :=
  let m := snapshot_values xs base (allocated empty_mem q base) in
  match lv.1 with
  | PByte b o => (lv.1, VByte (m_bytes m (b + o)))
  | PAux b o => (lv.1, VAux (m_aux m (b + o)))
  | _ => lv
  end.

(** For promotion: a snapshot owns the same keys as the new object,
    populated with the snapshot's bytes and capabilities. *)
Definition snapshot_ps xs base q : list (piece * pval) :=
  snapshot_piece xs base q <$> obj_ps base q.

(** For promotion: populating a snapshot leaves its ownership keys
    unchanged, so their distinctness follows from [obj_ps_nodup]. *)
Lemma snapshot_ps_keys xs base q :
  (snapshot_ps xs base q).*1 = (obj_ps base q).*1.
Proof.
  unfold snapshot_ps. rewrite -list_fmap_compose. apply list_fmap_ext.
  intros i [l v] Hi. destruct l; reflexivity.
Qed.

(** For promotion: each snapshot piece names its fresh object. *)
Lemma snapshot_ps_id xs base q l v :
  (l, v) ∈ snapshot_ps xs base q -> piece_id l = base.
Proof.
  unfold snapshot_ps. intros Hin. apply list_elem_of_fmap in Hin as ([k u] & Hkv & Hin).
  assert (Hkey : l = k).
  { apply (f_equal fst) in Hkv. destruct k; exact Hkv. }
  subst l. exact (obj_ps_id _ _ _ _ Hin).
Qed.

(** For promotion: all snapshot keys are memory pieces, so an old
    agreeing heap cannot already own a key of the fresh object. *)
Lemma snapshot_ps_mem xs base q l v :
  (l, v) ∈ snapshot_ps xs base q -> mem_piece l.
Proof.
  unfold snapshot_ps. intros Hin. apply list_elem_of_fmap in Hin as ([k u] & Hkv & Hin).
  assert (Hkey : l = k).
  { apply (f_equal fst) in Hkv. destruct k; exact Hkv. }
  subst l. exact (obj_ps_mem _ _ _ _ Hin).
Qed.

(** For promotion: freshness makes the computed snapshot pieces agree
    with the real allocation after its argument stores. *)
Lemma snapshot_ps_agree m xs base q :
  Memory.fresh m q base ->
  all_agree (snapshot_values xs base (allocated m q base)) (snapshot_ps xs base q).
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
  rewrite Hlv.
  unfold obj_ps in Hin. apply elem_of_cons in Hin as [[= -> ->] | Hin].
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

(** For promotion: snapshot stores frame every piece outside the fresh
    object's keys. The proof uses [frame_within] and the exact store
    range, not a promise about the caller's memory. *)
Lemma snapshot_frame m xs base q :
  live_disjoint (allocated m q base) -> 8 * Z.of_nat (length xs) <= req_extent q ->
  frame_ok (obj_ps base q).*1 (allocated m q base)
    (snapshot_values xs base (allocated m q base)).
Proof.
  intros Hd Hsize. apply (frame_within _ _ _ base
    (mkRegion base (base + req_extent q) (req_kind q) Live));
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

(** For promotion: the nonempty snapshot equation of [Semantics.step].
    The read-only pointer goes in the frame; the argument cells are
    allocated and populated in memory by that same step. *)
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

(** The helpers over any runtime and caller-supplied world. *)
Module HelloVersion (R : Runtime).
Module HL := HelloLeaf R.
Module ML := HL.ML.
Module SL := ML.SL.
Module LG := ML.LG.
Module L := LG.L.
Import L LG SL ML HL.

Section version.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context {world : Type} (registry : name -> option (contract world))
  (wi : mem -> world -> gmap piece pval -> Prop) `{!SafepointStable wi} (ge : genv).

(** The Iris instance uses exactly the caller's registry and world. *)
Local Instance version_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry wi ge.
(** Expressions in that language. *)
Local Notation hexpr := (language.expr (nanofil_lang registry ge)).

(** For promotion: allocating a nonempty variadic snapshot yields its
    populated pieces, with the read-only pointer installed in the frame.
    This lifts [rule_snapshot] through [wp_lift_run]; only preservation
    of the caller's world interpretation remains a premise. *)
Lemma wp_snapshot f e ls l xs Φ :
  xs <> [] -> forallb snapshot_word xs = true ->
  let q := heap_req 16 (8 * Z.of_nat (length xs)) in
  (forall m wd h base, Memory.fresh m q base -> wi m wd h ->
    wi (snapshot_values xs base (allocated m q base)) wd
      (overwrite (snapshot_ps xs base q) h)) ->
  ▷ (∀ base, ⌜0 < base /\ base mod req_align q = 0 /\ base + req_extent q <= 2 ^ 48⌝ -∗
    pts (snapshot_ps xs base q) -∗
    WP (ERun (mkFrame f (put va_snapshot (WPtr (mkPtr base (Ro base))) e)
      ls None (Enter l None)) : hexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Snapshot xs l)) : hexpr) {{ Φ }}.
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
    assert (Hd_alloc : live_disjoint (allocated m q base)).
    { exact (live_disjoint_allocated _ _ _ Hd Hf Hex). }
    assert (Hr' : R.ready s' (snapshot_values xs base (allocated m q base))).
    { apply (R.ready_kept _ _ _ Hr_alloc). exact (snapshot_alloc_kept xs m base). }
    pose proof (snapshot_frame m xs base q Hd_alloc
      (heap_req_extent 16 (8 * Z.of_nat (length xs)))) as Hframe.
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
      * apply (live_disjoint_regions (allocated m q base));
          [apply snapshot_values_regions | exact Hd_alloc].
      * exact Hr'.
      * exact (Hwi m w h base Hf Hw).
    + iApply ("HK" with "[%] Hps"). split; [exact Hpos |]. split; [exact Hmod |].
      destruct (R.address_space _ _ Hr' base
        (mkRegion base (base + req_extent q) (req_kind q) Live)) as [_ Hend].
      { rewrite snapshot_values_regions object_region_allocated Z.eqb_refl. reflexivity. }
      exact Hend.
Qed.

(** For promotion: the Iris rule for [VaArgs], lifted directly from
    [rule_va_args] through [wp_pure_next]. *)
Lemma wp_va_args f e ls l d off rest j p Φ :
  lookup va_snapshot e = Some (WPtr p) ->
  ▷ WP (ERun (mkFrame f
      (put d (WPtr (mkPtr ((ptr_addr p + off) mod 2 ^ 64) (ptr_cap p))) e)
      ls None (Exec l rest j)) : hexpr) {{ Φ }} -∗
  WP (ERun (mkFrame f e ls None
      (Exec l (Let d P VaArgs [Const off] :: rest) j)) : hexpr) {{ Φ }}.
Proof.
  intros Hp. apply (wp_pure_next registry wi ge _ _ []).
  intros m fuel. apply rule_va_args. exact Hp.
Qed.

(** For promotion: a variadic argument read is a heap write, not a
    pure read of the frame. Owned pieces justify [va_arg_res] and
    retain exactly their keys after the cursor update. This lifts
    [rule_va_arg] through [wp_write], including its world-frame premise. *)
Lemma wp_va_arg f e ls l d k args rest j p x ps ps' upd Φ :
  map2_option (value_x ge e) [P] args = Some [WPtr p] ->
  ps'.*1 = ps.*1 ->
  (forall m, owned_facts ps m ->
    va_arg_res k p m = Some (RVal x, upd m) /\
    m_regions (upd m) = m_regions m /\ kept m (upd m) /\
    all_agree (upd m) ps' /\ frame_ok ps'.*1 m (upd m)) ->
  (forall m w h, (forall l v, (l, v) ∈ ps -> h !! l = Some v) -> wi m w h ->
    wi (upd m) w (overwrite ps' h)) ->
  pts ps -∗ ▷ (pts ps' -∗
    WP (ERun (mkFrame f (put d x e) ls None (Exec l rest j)) : hexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (Let d k VaArg args :: rest) j)) : hexpr) {{ Φ }}.
Proof.
  intros Hargs Hkeys Hread Hwi. iIntros "Hps HK".
  iApply (wp_write registry wi ge ps ps' _ _ [] upd with "Hps HK");
    [exact Hkeys | | exact Hwi].
  intros m fuel Hfacts. destruct (Hread m Hfacts) as (Hres & Hrest).
  split; [exact (rule_va_arg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hargs Hres) | exact Hrest].
Qed.

(** For promotion: a memory-reading operation justified by the world
    interpretation, without claiming ownership of a world-owned cell.
    It is [rule_let] lifted through [wp_read_with]. *)
Lemma wp_world_let f e ls l d k o args rest j classes xs x Φ :
  general_op o = true -> op_arg_classes o k = Some classes ->
  map2_option (value_x ge e) classes args = Some xs ->
  (forall m w h, wi m w h -> op_res o k xs m = Some (OpRes (RVal x) m)) ->
  ▷ WP (ERun (mkFrame f (put d x e) ls None (Exec l rest j)) : hexpr) {{ Φ }} -∗
  WP (ERun (mkFrame f e ls None (Exec l (Let d k o args :: rest) j)) : hexpr) {{ Φ }}.
Proof.
  intros Hg Hc Hargs Hop. iIntros "HK".
  iApply (wp_read_with _ _ _ emp
    (fun m => op_res o k xs m = Some (OpRes (RVal x) m)) _ _ [] with "[] [HK]").
  - iIntros (σ) "(%h & _ & %Hf) _". destruct Hf as (_ & _ & _ & Hw).
    iPureIntro. exact (Hop _ _ _ Hw).
  - intros m fuel Hm. exact (rule_let _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hg Hc Hargs Hm).
  - done.
  - iNext. iIntros "_". iExact "HK".
Qed.

(** The compiled proper-name helper preserves every framed resource:
    it never dereferences the pointer or calls an external function. *)
Lemma proper_name_spec p Φ :
  ▷ Φ (Ret (WPtr p)) -∗
  WP (ERun (invocation proper_name_fn [WPtr p]) : hexpr) {{ Φ }}.
Proof.
  iIntros "HΦ". rewrite proper_name_entry.
  iApply wp_enter; [exact find_proper_name_start | reflexivity |].
  iNext. cbn [b_insts b_jump proper_name_start].
  iApply wp_ret; [reflexivity | reflexivity |]. iNext. iExact "HΦ".
Qed.

Section emit.
(** The footer links the fixture's literals, but libc supplies stdout. *)
Context (Hlinked : hello_linked ge) (stdout_cell stdout : ptr)
  (Hstdout_global : lookup (TAtom "stdout") (ge_globals ge) = Some stdout_cell).

(** The stdio world owns the stdout cell and guarantees its read, not
    an Iris piece owned by the program. *)
Context (wi_stdout : forall m w h, wi m w h ->
  access_res m (raw_address (ptr_addr stdout_cell) 0) (ptr_cap stdout_cell) 8 Read 8 = Some ok /\
  pointer_load_effects m (raw_address (ptr_addr stdout_cell) 0)
    [AuxRead; LowerResolve; AddressRead] = Some stdout).

(** The program-owned pieces containing the footer's format and string
    literals. The stdio precondition reads them through [pts_lookup];
    the world does not have to own them. *)
Context (literal_ps : list (piece * pval)).

(** Output specs supplied by the stdio package. The preconditions are
    required for these four exact calls, including the NUL-terminated
    format and string arguments; output failure cannot waive them. *)
Context (output_spec : name -> contract world)
  (Houtput_reg : forall g xs, In (g, xs) (emit_output_args stdout) -> registry g = Some (output_spec g))
  (Houtput_ret : forall g xs, In (g, xs) (emit_output_args stdout) ->
     contract_returns (output_spec g) = RClass W)
  (Houtput_abi : forall g xs d args, In (g, xs) (emit_output_args stdout) ->
     map (fun a => match a with Arg k _ => k end) args = replicate (length xs) P ->
     contract_abi (output_spec g) (CResult d W) args)
  (Houtput_pre : forall g xs m w h, In (g, xs) (emit_output_args stdout) ->
     (forall l v, (l, v) ∈ literal_ps -> h !! l = Some v) ->
     agrees m h -> wi m w h -> contract_pre (output_spec g) xs m w)
  (Houtput_frame : forall g xs r args s m w h trace values s' m' w',
     In (g, xs) (emit_output_args stdout) ->
     agrees m h -> live_disjoint m -> R.ready s m -> wi m w h ->
     M.E.invoke (output_spec g) r args xs s m w trace (CallReturn values) s' m' w' ->
     agrees m' h /\ live_disjoint m' /\ R.ready s' m' /\ wi m' w' h /\
       exists n, values = [WInt n] /\ 0 <= n < 2 ^ 32).

(** The footer's pure symbol copies find the same literal in ge. *)
Lemma emit_literal_lookup s :
  In s ["version-etc#str.43"; "version-etc#str.45"; "version-etc#str.58";
        "version-etc#str.59"; "version-etc#str.60"; "version-etc#str.61";
        "version-etc#str.62"; "version-etc#str.63"; "version-etc#str.64"] ->
  lookup (TAtom s) (ge_globals ge) = Some (version_literal s).
Proof.
  intros Hin. apply (proj1 (proj2 Hlinked)).
  repeat destruct Hin as [<- | Hin]; try contradiction; vm_compute; reflexivity.
Qed.

(** The output call is safe and returns an arbitrary canonical int,
    retaining the caller's heap and stdio interpretation on errors too. *)
Lemma wp_emit_output f e ls lab d g args rest j xs Φ :
  In (g, xs) (emit_output_args stdout) ->
  map_option (arg_x ge e) args = Some xs ->
  map (fun a => match a with Arg k _ => k end) args = replicate (length xs) P ->
  pts literal_ps -∗
  ▷ (∀ n, pts literal_ps -∗
    WP (ERun (mkFrame f (put d (WInt n) e) ls None (Exec lab rest j)) : hexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
    (Exec lab (Call (CResult d W) (Global g) args :: rest) j)) : hexpr) {{ Φ }}.
Proof.
  intros Hin Hargs Hclasses. iIntros "Hps HK".
  assert (Hg : g = TAtom "fputs" \/ g = TAtom "printf").
  { unfold emit_output_args in Hin. repeat destruct Hin as [H | Hin];
      try contradiction; inversion H; auto. }
  iApply (wp_external _ _ _ _ _ _ _ _ _ _ _ _ (output_spec g) xs (pts literal_ps) with "Hps [HK]").
  - destruct Hg as [-> | ->]; apply hello_outside; try exact (proj1 Hlinked); reflexivity.
  - destruct Hg as [-> | ->]; apply (proj2 (proj2 Hlinked)); reflexivity.
  - destruct Hg as [-> | ->]; reflexivity.
  - exact (Houtput_reg _ _ Hin).
  - exact Hargs.
  - exact (Houtput_abi _ _ _ _ Hin Hclasses).
  - iIntros (σ) "(%h & Hh & %Hf) Hps". destruct Hf as (Ha & _ & _ & Hw).
    iDestruct (pts_lookup with "Hh Hps") as %Hps.
    iPureIntro. exact (Houtput_pre _ _ _ _ _ Hin Hps Ha Hw).
  - iNext. iIntros (σ trace values s' m' w' Hinv) "(%h & Hh & %Hf) Hps".
    destruct Hf as (Ha & Hd & Hr & Hw).
    destruct (Houtput_frame _ _ _ _ _ _ _ _ _ _ _ _ _ Hin Ha Hd Hr Hw Hinv)
      as (Ha' & Hd' & Hr' & Hw' & n & -> & Hn).
    iModIntro. iExists (put d (WInt n) e). iSplit.
    + iPureIntro. unfold external_env. cbn [site_result]. rewrite (Houtput_ret _ _ Hin).
      cbn. rewrite Z.mod_small; [reflexivity | exact Hn].
    + iSplitL "Hh"; [iExists h; iFrame; iPureIntro; auto |]. iApply ("HK" with "Hps").
Qed.

(** The complete help footer, including failed and partial output:
    every stdio result is ignored and every framed resource survives. *)
Lemma emit_bug_reporting_address_spec Φ :
  pts literal_ps -∗ ▷ (pts literal_ps -∗ Φ RetVoid) -∗
  WP (ERun (invocation emit_bug_reporting_address_fn []) : hexpr) {{ Φ }}.
Proof.
  pose proof (emit_literal_lookup "version-etc#str.43" ltac:(simpl; tauto)) as H43.
  pose proof (emit_literal_lookup "version-etc#str.45" ltac:(simpl; tauto)) as H45.
  pose proof (emit_literal_lookup "version-etc#str.58" ltac:(simpl; tauto)) as H58.
  pose proof (emit_literal_lookup "version-etc#str.59" ltac:(simpl; tauto)) as H59.
  pose proof (emit_literal_lookup "version-etc#str.60" ltac:(simpl; tauto)) as H60.
  pose proof (emit_literal_lookup "version-etc#str.61" ltac:(simpl; tauto)) as H61.
  pose proof (emit_literal_lookup "version-etc#str.62" ltac:(simpl; tauto)) as H62.
  pose proof (emit_literal_lookup "version-etc#str.63" ltac:(simpl; tauto)) as H63.
  pose proof (emit_literal_lookup "version-etc#str.64" ltac:(simpl; tauto)) as H64.
  iIntros "Hps HΦ". change (invocation emit_bug_reporting_address_fn []) with
    (mkFrame emit_bug_reporting_address_fn [] [] None (Enter (TAtom "start") None)).
  iApply wp_enter; [exact find_emit_bug_reporting_address_start | reflexivity |]. iNext.
  cbn [b_insts b_jump emit_bug_reporting_address_start].
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; reflexivity |]. iNext.
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; reflexivity |]. iNext.
  iApply wp_world_let; [reflexivity | reflexivity | word_premise | |].
  { intros m w h Hw. apply op_check. exact (proj1 (wi_stdout _ _ _ Hw)). }
  iNext.
  iApply wp_world_let; [reflexivity | reflexivity | word_premise | |].
  { intros m w h Hw. apply op_raw_load_pointer; apply (wi_stdout _ _ _ Hw). }
  iNext.
  iApply (wp_emit_output with "Hps");
    [unfold emit_output_args; left; reflexivity | word_premise | reflexivity |].
  iNext. iIntros (n0) "Hps".
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; reflexivity |]. iNext.
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; reflexivity |]. iNext.
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; reflexivity |]. iNext.
  iApply (wp_emit_output with "Hps");
    [unfold emit_output_args; right; left; reflexivity | word_premise | reflexivity |].
  iNext. iIntros (n1) "Hps".
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; reflexivity |]. iNext.
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; reflexivity |]. iNext.
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; reflexivity |]. iNext.
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; reflexivity |]. iNext.
  iApply (wp_emit_output with "Hps");
    [unfold emit_output_args; right; right; left; reflexivity | word_premise | reflexivity |].
  iNext. iIntros (n2) "Hps".
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; reflexivity |]. iNext.
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; reflexivity |]. iNext.
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; reflexivity |]. iNext.
  iApply (wp_emit_output with "Hps");
    [unfold emit_output_args; right; right; right; left; reflexivity | word_premise | reflexivity |].
  iNext. iIntros (n3) "Hps". iApply wp_ret_void. iNext. iApply ("HΦ" with "Hps").
Qed.

End emit.

End version.
End HelloVersion.
