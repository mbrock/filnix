(** Constant-time code often scans a public tail window of a buffer and
    compares a secret 16-byte sub-window against a fixed lookup table. Two
    questions arise when the compiler translates that pattern to checked IR.
    First, does optimization cancel a secret prefix adjustment so the tail
    window pointer stays public? Second, how does a secret table index interact
    with Fil-C [[capability]] checks, single-run [[poison]] tracking, and
    two-run constant-time noninterference?

    This module answers both questions directly on the checked IR emitted by
    `nanofil -O` from `ct_table_scan.c`, stored in [CtTableScanCode] in
    [IRNotation] with C-level temporary names from [CtTableScanNames]. We first
    run the reflective taint checker from [TaintCheck] to accept `scan_ct` and
    reject `scan_indexed` by computation. Next, concrete forensic checks on
    `scan_indexed` separate bounds-check branching, address-index leakage, and
    exact-size out-of-bounds traps. We then prove plain memory safety for
    `scan_ct` across all valid window lengths and combine it with the
    reflective taint check to obtain universal [[poison]] safety and two-run
    constant-time noninterference. Finally, a minimal rebased loop written in
    [IRNotation] formally separates single-run taint from two-run
    noninterference. *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Maps Syntax Values Validate Memory Runtime Ops Semantics
  Run Machine Panics StepRules Pieces PoisonModel PoisonLogic TaintCheck
  IRNotation FrameNotation CtTableScanCode CtTableScanNames.

Import ListNotations.
Import CtTableScanNames.fn_scan_ct.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.

(** ## Validated checked IR

    Every theorem about `scan_indexed` and `scan_ct` operates directly on the
    typed IR functions emitted by `nanofil -O` in [CtTableScanCode]. Campaign
    1's [[validator]] accepts both functions without hand-transcribed IR or
    runtime decoding. *)

(** Campaign 1's [[validator]] accepts both `scan_indexed` and `scan_ct`. *)
Theorem cttable_valid : valid cttable_module = Some true.
Proof. vm_compute. reflexivity. Qed.

(** Global environment containing both compiled functions. *)
Definition cttable_ge : genv := mkGenv cttable_module [] free_res.

(** ## Reflective taint checking

    Before proving anything about memory bounds or loop execution, we run the
    static reflective taint checker from [TaintCheck] on the compiled IR. The
    specification [scan_ct_tspec] marks the two pointers `buf` and `tbl` and
    the public lengths `len` and `win` as unrestricted, while marking `skip`,
    `start`, every byte and shadow capability in memory, and the returned word
    as fully secret. A single computation accepts `scan_ct` under [pol_strict]
    and rejects `scan_indexed` under both [pol_strict] and [pol_erased]. *)

(** Static taint contract for a read-only scanner over secret data. *)
Definition scan_ct_tspec : tspec :=
  {| ts_args :=
       [WTPtr taint_bot taint_bot;
        WTInt taint_bot;
        WTInt taint_bot;
        WTInt taint_all;
        WTInt taint_all;
        WTPtr taint_bot taint_bot];
     ts_ret := Some (WTInt taint_all);
     ts_mem := taint_all;
     ts_aux := taint_all;
     ts_writes := false |}.

(** Entry table checking `scan_ct` under [scan_ct_tspec]. *)
Definition scan_ct_tspecs : list (name * tspec) :=
  [(TAtom "scan_ct", scan_ct_tspec)].

(** The reflective taint checker accepts `scan_ct` under [pol_strict] with all
    secret inputs and all memory bytes tagged [taint_all]. *)
Theorem scan_ct_taint_ok :
  taint_check_program pol_strict cttable_module scan_ct_tspecs = true.
Proof. vm_compute. reflexivity. Qed.

(** The same checker rejects `scan_indexed` under both [pol_strict] and
    [pol_erased], because the secret counter `i` indexes `tbl[i]`. *)
Theorem scan_indexed_taint_rejected :
  taint_check_fn pol_strict cttable_module [] fn_scan_indexed scan_ct_tspec = false /\
  taint_check_fn pol_erased cttable_module [] fn_scan_indexed scan_ct_tspec = false.
Proof. vm_compute. split; reflexivity. Qed.

(** ## Forensic checks on `scan_indexed`

    Static rejection tells us that `scan_indexed` leaks secrets, while concrete
    executions pinpoint each failure mode. We instantiate a small concrete heap
    and step the compiled IR directly through [prun] and [run_trace]. These
    checks show that `simplify.pl` cancels the secret prefix `skip` in the
    window pointer, that Fil-C's bounds check traps on `taint_branch`, that
    erasing checks still traps on `taint_index` and produces distinct plain
    traces, and that `scan_ct` computes the same result on an exact 16-byte
    table. *)

(** Fixed base addresses and read-only capability pointers for concrete runs. *)
Definition scan_buf_base : Z := 131072.
Definition scan_tbl_base : Z := 131328.

Definition scan_buf_ptr : ptr := mkPtr scan_buf_base (Ro scan_buf_base).
Definition scan_tbl_ptr : ptr := mkPtr scan_tbl_base (Ro scan_tbl_base).

(** Deterministic sample table bytes `tbl[0..15]`. *)
Definition sample_tbl (k : Z) : Z := (17 * k + 5) mod 256.

(** A 24-byte buffer containing [sample_tbl] at offset `4 + start` inside the
    20-byte tail window `buf[4..23]` (`win = 4`). *)
Definition matching_buf_byte (start : Z) (idx : Z) : Z :=
  let j := idx - 4 in
  if (start <=? j) && (j <? start + 16)
  then sample_tbl (j - start)
  else (3 * idx + 1) mod 256.

(** Concrete memory holding a 24-byte buffer at [scan_buf_base] and a
    `tbl_size`-byte table at [scan_tbl_base]. *)
Definition scan_mem (buf_fn tbl_fn : Z -> Z) (tbl_size : Z) : mem :=
  mkMem
    (fun a =>
      if (scan_buf_base <=? a) && (a <? scan_buf_base + 24)
      then buf_fn (a - scan_buf_base) mod 256
      else if (scan_tbl_base <=? a) && (a <? scan_tbl_base + tbl_size)
      then tbl_fn (a - scan_tbl_base) mod 256
      else 0)
    [mkRegion scan_buf_base (scan_buf_base + 24) Heap Live;
     mkRegion scan_tbl_base (scan_tbl_base + tbl_size) Heap Live]
    (fun _ => CNone).

(** Entry frame binding the six arguments of `scan_indexed` or `scan_ct`. *)
Definition scan_frame (f : func) (len win skip start : Z) : frame :=
  mkFrame f
    [(‹tbl›, WPtr scan_tbl_ptr);
     (‹start›, WInt start);
     (‹skip›, WInt skip);
     (‹win›, WInt win);
     (‹len›, WInt len);
     (‹buf›, WPtr scan_buf_ptr)]
    [] None (Enter (TAtom "start") None).

(** Machine configuration for a concrete run of `f`. *)
Definition scan_cfg (f : func) (buf_fn tbl_fn : Z -> Z)
    (tbl_size len win skip start fuel : Z) : config :=
  mkConfig (scan_frame f len win skip start) [] (scan_mem buf_fn tbl_fn tbl_size) fuel.

(** Poison state tagging `skip`, `start`, and buffer/table bytes independently. *)
Definition scan_pstate (t_skip t_start t_bytes : taint) (tbl_size : Z) : pstate :=
  mkPState
    [(‹tbl›, WTPtr taint_bot taint_bot);
     (‹start›, WTInt t_start);
     (‹skip›, WTInt t_skip);
     (‹win›, WTInt taint_bot);
     (‹len›, WTInt taint_bot);
     (‹buf›, WTPtr taint_bot taint_bot)]
    []
    (fun a =>
      if ((scan_buf_base <=? a) && (a <? scan_buf_base + 24))
         || ((scan_tbl_base <=? a) && (a <? scan_tbl_base + tbl_size))
      then pb_secret t_bytes
      else pb_clean)
    (fun _ => taint_bot).

(** When only `skip` and data bytes carry full poison (and `start` stays
    public), `scan_indexed` finishes cleanly under [pol_strict]: additive
    cancellation in `simplify.pl` folds `(buf + skip) + (len - skip)` back to
    `buf + len`, so the window pointer `p` carries no poison. *)
Theorem scan_indexed_p_is_public :
  prun pol_strict cttable_ge 800
    (scan_cfg fn_scan_indexed (matching_buf_byte 2) sample_tbl 20 24 4 19 2 200)
    (scan_pstate taint_all taint_bot taint_all 20) =
    PDone (Ret (WInt 0)) [WTInt taint_all].
Proof. vm_compute. reflexivity. Qed.

(** Marking `start` with [taint_branch] causes Fil-C's capability bounds check
    on `tbl + i` to trap with [CannotBranch] under [pol_strict], even when
    `tbl` is padded to 20 bytes so the check never traps architecturally. *)
Theorem scan_indexed_filc_check_traps_branch :
  prun pol_strict cttable_ge 800
    (scan_cfg fn_scan_indexed (matching_buf_byte 2) sample_tbl 20 24 4 19 2 200)
    (scan_pstate taint_all taint_branch taint_bot 20) =
    PTrap CannotBranch.
Proof. vm_compute. reflexivity. Qed.

(** Under [pol_erased], where Fil-C's capability checks do not emit branch
    leakage events, the same `taint_branch` run completes without a branch
    fault because the bounds check is architecturally never taken. *)
Theorem scan_indexed_erased_branch_passes :
  prun pol_erased cttable_ge 800
    (scan_cfg fn_scan_indexed (matching_buf_byte 2) sample_tbl 20 24 4 19 2 200)
    (scan_pstate taint_all taint_branch taint_bot 20) =
    PDone (Ret (WInt 0)) [WTInt taint_branch].
Proof. vm_compute. reflexivity. Qed.

(** Under [pol_erased] with [taint_index], `scan_indexed` still faults with
    [CannotIndex] when dereferencing `tbl[i]`, showing a genuine memory-address
    dependency rather than a bounds-check artifact. *)
Theorem scan_indexed_load_traps_index :
  prun pol_erased cttable_ge 800
    (scan_cfg fn_scan_indexed (matching_buf_byte 2) sample_tbl 20 24 4 19 2 200)
    (scan_pstate taint_all taint_index taint_bot 20) =
    PTrap CannotIndex.
Proof. vm_compute. reflexivity. Qed.

(** Two plain poison-free runs of `scan_indexed` with different secret offsets
    `start = 1` and `start = 3` emit different operational leakage traces under
    [run_trace], confirming a real two-run address leak. *)
Theorem scan_indexed_two_run_address_leak :
  run_trace pol_erased cttable_ge 800
    (scan_cfg fn_scan_indexed (matching_buf_byte 1) sample_tbl 20 24 4 19 1 200) <>
  run_trace pol_erased cttable_ge 800
    (scan_cfg fn_scan_indexed (matching_buf_byte 3) sample_tbl 20 24 4 19 3 200).
Proof.
  intros H. vm_compute in H. discriminate H.
Qed.

(** On an exact 16-byte table allocation, `scan_indexed` traps with
    [OutOfBounds] when `i` reaches 16 and the loop reads `tbl[16]`. *)
Theorem scan_indexed_exact_tbl_traps_oob :
  prun pol_strict cttable_ge 800
    (scan_cfg fn_scan_indexed (matching_buf_byte 2) sample_tbl 16 24 4 19 2 200)
    (scan_pstate taint_bot taint_bot taint_bot 16) =
    PDone (Trap OutOfBounds) [].
Proof. vm_compute. reflexivity. Qed.

(** On concrete matching and mismatching inputs, `scan_ct` agrees with
    `scan_indexed` while running cleanly under full [taint_all] poison on an
    exact 16-byte table. *)
Theorem scan_ct_matches_indexed :
  let bad_buf (start : Z) (idx : Z) :=
    if idx =? 4 + start + 3 then (matching_buf_byte start idx + 1) mod 256
    else matching_buf_byte start idx in
  let run_ct buf_fn tbl_fn skip start :=
    prun pol_strict cttable_ge (Z.to_nat 10000)
      (scan_cfg fn_scan_ct buf_fn tbl_fn 16 24 4 skip start 1000)
      (scan_pstate taint_all taint_all taint_all 16) in
  let run_idx buf_fn tbl_fn skip start :=
    prun pol_strict cttable_ge 800
      (scan_cfg fn_scan_indexed buf_fn tbl_fn 20 24 4 skip start 200)
      (scan_pstate taint_bot taint_bot taint_bot 20) in
  run_ct (matching_buf_byte 2) sample_tbl 19 2 = PDone (Ret (WInt 0)) [WTInt taint_all] /\
  run_idx (matching_buf_byte 2) sample_tbl 19 2 = PDone (Ret (WInt 0)) [WTInt taint_bot] /\
  run_ct (bad_buf 2) sample_tbl 19 2 = PDone (Ret (WInt 1)) [WTInt taint_all] /\
  run_idx (bad_buf 2) sample_tbl 19 2 = PDone (Ret (WInt 1)) [WTInt taint_bot].
Proof. vm_compute. repeat split; reflexivity. Qed.

(** ## Readable slices and entry states

    Bundling the capability, liveness, and bounds facts for a memory buffer into
    one record keeps every universal theorem statement short and self-contained.
    A [readable_slice] certifies that a pointer refers to a live object whose
    bytes cover `[ptr_addr p, ptr_addr p + len)` without 64-bit wraparound. *)

(** A live, readable memory slice `[ptr_addr p, ptr_addr p + len)`. *)
Record readable_slice (m : mem) (p : ptr) (len : Z) : Prop := mkReadableSlice {
  rs_cap : ptr_cap p = Obj (ptr_addr p) \/ ptr_cap p = Ro (ptr_addr p);
  rs_addr_nonneg : 0 <= ptr_addr p;
  rs_len_nonneg : 0 <= len;
  rs_no_wrap : ptr_addr p + len < 2 ^ 64;
  rs_live_bounds : exists r, live_at m (ptr_addr p) r /\ ptr_addr p + len <= r_end r
}.

(** Slice validity depends only on the live region map, so garbage-collector
    safepoints and secret memory contents both preserve it. *)
Lemma readable_slice_regions m1 m2 p len :
  m_regions m1 = m_regions m2 ->
  readable_slice m1 p len ->
  readable_slice m2 p len.
Proof.
  intros Hreg [Hcap Ha Hl Hwrap [r [[Hobj Hlife] Hbnd]]].
  refine (mkReadableSlice m2 p len Hcap Ha Hl Hwrap _).
  exists r; split; [split; [rewrite <- Hreg; exact Hobj | exact Hlife] | exact Hbnd].
Qed.

(** Every in-bounds byte of a [readable_slice] passes Fil-C's capability read check. *)
Lemma readable_slice_byte_access m p len off :
  readable_slice m p len ->
  0 <= off < len ->
  access_res m (raw_address (ptr_addr p + off) 0) (ptr_cap p) 1 Read 1 = Some (RVal tt).
Proof.
  intros [Hcap Ha Hl Hwrap [r [[Hobj Hlife] Hbnd]]] Hoff.
  unfold access_res, raw_address.
  rewrite Z.add_0_r, (Z.mod_small (ptr_addr p + off) (2 ^ 64) ltac:(lia)).
  destruct Hcap as [Hcap | Hcap]; rewrite Hcap;
    unfold cap_access_res, readonly_access_res, aligned_res;
    rewrite Hobj;
    replace (ptr_addr p <=? ptr_addr p + off) with true by (symmetry; apply Z.leb_le; lia);
    replace (ptr_addr p + off + 1 <=? r_end r) with true by (symmetry; apply Z.leb_le; lia);
    rewrite Z.mod_1_r; reflexivity.
Qed.

(** Every in-bounds unsigned byte load from a [readable_slice] succeeds. *)
Lemma readable_slice_load_byte m p len off :
  readable_slice m p len ->
  0 <= off < len ->
  int_load_res (LdNarrow Ub) W m (raw_address (ptr_addr p + off) 0) (ptr_cap p) =
    Some (RVal (WInt ((m_bytes m (ptr_addr p + off) mod 256) mod 2 ^ 32))).
Proof.
  intros Hsl Hoff.
  pose proof Hsl as [_ Ha _ Hwrap _].
  unfold int_load_res; cbn [fst narrow_type].
  rewrite (readable_slice_byte_access m p len off Hsl Hoff).
  unfold load_bytes, raw_address, extended, extension; cbn [modulus].
  rewrite Z.add_0_r, (Z.mod_small (ptr_addr p + off) (2 ^ 64) ltac:(lia)).
  change (Z.to_nat 1) with 1%nat. cbn. rewrite Z.add_0_r. reflexivity.
Qed.

(** Entry frame binding all six arguments of `scan_ct`. *)
Definition scan_ct_entry (buf tbl : ptr) (len win skip start : Z) : frame :=
  frame{ fn_scan_ct env:
    [(‹tbl›, WPtr tbl);
     (‹start›, WInt start);
     (‹skip›, WInt skip);
     (‹win›, WInt win);
     (‹len›, WInt len);
     (‹buf›, WPtr buf)]
    | enter: @"start" }.

(** Entry taint environment matching [scan_ct_tspec]: `skip` and `start` carry
    full poison while the pointers and public window lengths stay clean. *)
Definition scan_ct_te : tenv :=
  [(‹tbl›, WTPtr taint_bot taint_bot);
   (‹start›, WTInt taint_all);
   (‹skip›, WTInt taint_all);
   (‹win›, WTInt taint_bot);
   (‹len›, WTInt taint_bot);
   (‹buf›, WTPtr taint_bot taint_bot)].

(** Two calls to `scan_ct` with matching public pointers, lengths, and live
    region layout satisfy [ct_rel] under full-memory secret poison, regardless
    of how their memory bytes, shadow capabilities, or secret offsets differ. *)
Lemma scan_ct_inputs_related buf tbl len win skip1 start1 skip2 start2 m1 m2 fuel :
  m_regions m1 = m_regions m2 ->
  ct_rel
    cfg{ (scan_ct_entry buf tbl len win skip1 start1); mem: m1; fuel: fuel }
    cfg{ (scan_ct_entry buf tbl len win skip2 start2); mem: m2; fuel: fuel }
    (mkPState scan_ct_te [] (fun _ => pb_secret taint_all) (fun _ => taint_all)).
Proof.
  intros Hreg.
  unfold ct_rel; cbn; repeat split; try assumption; try reflexivity.
  intros x. unfold scan_ct_te. cbn [lookup]. unfold name_eqb.
  destruct (term_eqb x ‹tbl›); [right; eexists _, _, _; repeat split; congruence|].
  destruct (term_eqb x ‹start›); [right; eexists _, _, _; repeat split; reflexivity|].
  destruct (term_eqb x ‹skip›); [right; eexists _, _, _; repeat split; reflexivity|].
  destruct (term_eqb x ‹win›); [right; eexists _, _, _; repeat split; congruence|].
  destruct (term_eqb x ‹len›); [right; eexists _, _, _; repeat split; congruence|].
  destruct (term_eqb x ‹buf›); [right; eexists _, _, _; repeat split; congruence|].
  left; split; reflexivity.
Qed.

(** Lookup hits the head of [put] on matching names and skips it otherwise. *)
Lemma lookup_put_same {A : Type} (x : name) (v : A) (m : list (name * A)) :
  lookup x (put x v m) = Some v.
Proof. unfold put; cbn [lookup]; unfold name_eqb; rewrite term_eqb_refl; reflexivity. Qed.

Lemma lookup_put_other {A : Type} (x y : name) (v : A) (m : list (name * A)) :
  term_eqb x y = false -> lookup x (put y v m) = lookup x m.
Proof. intros Hne; rewrite lookup_put_name; unfold name_eqb; rewrite Hne; reflexivity. Qed.

(** Helper tactic resolving environment lookups through nested [put]s. *)
Local Ltac solve_lookup :=
  repeat (first
    [ rewrite lookup_put_same
    | rewrite lookup_put_other; [|reflexivity] ]);
  repeat match goal with
      | H : lookup ?x ?e = Some _ |- context [lookup ?x ?e] => rewrite H
      end;
  cbn [word_at_class modulus];
  repeat match goal with
      | H : ?a mod ?m = ?b |- context [?a mod ?m] => rewrite H
      end;
  first [ reflexivity | assumption ].

(** ## Universal safety and constant time for `scan_ct`

    Because [scan_ct_taint_ok] already verified every taint and side-channel
    obligation statically, proving universal constant time for `scan_ct`
    reduces to plain memory safety. Using [plain_safe_by_block_safe], we give a
    three-state block invariant over the entry block `start`, the outer loop
    header `L28`, and the inner loop header `L55`. Each basic block steps in a
    straight line without induction, and the factoring theorem in [TaintCheck]
    lifts that plain safety proof directly to [poison_safe] and identical
    two-run leakage traces. *)

Module CtTableScan (R : Runtime).
Module TC := TaintCheckSound R.
Import TC.PL.

(** The three reachable block checkpoints of `scan_ct`: function entry, outer
    loop header `L28`, and inner loop header `L55`. Every checkpoint preserves
    the initial region layout `m_regions m0`, so garbage-collector safepoints
    at any step keep both slices live and readable. *)
Inductive scan_ct_inv (buf tbl : ptr) (len win : Z) (m0 : mem) : config -> Prop :=
| sci_start skip start m fuel :
    m_regions m = m_regions m0 ->
    scan_ct_inv buf tbl len win m0
      cfg{ (scan_ct_entry buf tbl len win skip start); mem: m; fuel: fuel }
| sci_outer e j m fuel :
    m_regions m = m_regions m0 ->
    0 <= j <= win + 16 ->
    e.[‹win›] = int_val win ->
    e.[‹tbl›] = ptr_val tbl ->
    e.[‹p›] = ptr_val (ptr_shift buf (len - win - 16)) ->
    e.[‹j›] = int_val j ->
    has_ints e [‹start›; ‹i›; ‹res›] ->
    scan_ct_inv buf tbl len win m0
      cfg{ fn_scan_ct env: e | at @"L28" {
             ir[ %"v34" : L = Add %"v4", #16;
                 %"v35" : W = (Cmp Ult L) %"pr.3", %"v34" ]
             => ir{ br %"v35" ? "L29" : "L31" }
           }; mem: m; fuel: fuel }
| sci_inner e j k m fuel :
    m_regions m = m_regions m0 ->
    0 <= j < win + 16 ->
    0 <= k <= 16 ->
    e.[‹win›] = int_val win ->
    e.[‹tbl›] = ptr_val tbl ->
    e.[‹p›] = ptr_val (ptr_shift buf (len - win - 16)) ->
    e.[‹j›] = int_val j ->
    e.[‹k›] = int_val k ->
    has_ints e [‹start›; ‹i›; ‹res›; ‹c›; ‹in_range›; ‹mask›; ‹expected›] ->
    scan_ct_inv buf tbl len win m0
      cfg{ fn_scan_ct env: e | at @"L55" {
             ir[ %"v60" : W = (Cmp Ult L) %"pr.5", #16 ]
             => ir{ br %"v60" ? "L56" : "L58" }
           }; mem: m; fuel: fuel }.

(** Region-preserving collector safepoints preserve [scan_ct_inv]. *)
Lemma scan_ct_inv_regions buf tbl len win m0 c m' :
  scan_ct_inv buf tbl len win m0 c ->
  m_regions m' = m_regions (c_mem c) ->
  scan_ct_inv buf tbl len win m0 (RM.with_mem c m').
Proof.
  intros Hinv Hm'.
  destruct Hinv; cbn [c_mem RM.with_mem] in *;
    [eapply sci_start | eapply sci_outer | eapply sci_inner];
    try (rewrite Hm'; exact H); eassumption.
Qed.

(** Non-failure of [OutOfFuel] and [Ret]. *)
Lemma not_failure_out_of_fuel : ~ failure OutOfFuel.
Proof. unfold failure, refusal. intros H; exact H. Qed.

Lemma not_failure_ret w : ~ failure (Ret w).
Proof. unfold failure. intros H; exact H. Qed.

(** Stepping helper: advance one instruction under [bs_step] and refresh the
    memory hypothesis across any intervening collector safepoint. *)
Local Ltac advance_mem m Hreg :=
  let m' := fresh "m" in
  let Hm' := fresh "Hreg" in
  intros m' Hm'; cbn [c_mem] in Hm';
  unfold RM.with_mem; cbn [c_frame c_callers c_fuel];
  rewrite Hreg in Hm'; clear Hreg;
  let prev := fresh "prev_mem" in rename m into prev;
  rename m' into m, Hm' into Hreg.

(** Entering a block either stops cleanly with [OutOfFuel] when `fuel = 0` or
    steps via [rule_enter] and refreshes the memory invariant. *)
Local Ltac step_enter_or_fuel fuel m Hreg :=
  let Hfuel := fresh "Hfuel" in
  destruct (Z.eqb_spec fuel 0) as [-> | Hfuel];
  [ eapply TC.bs_done; [apply rule_out_of_fuel | apply not_failure_out_of_fuel]
  | eapply TC.bs_step;
    [ eapply (rule_enter _ _ _ _ _ _ _ _ _ _ _ Hfuel);
      [ reflexivity
      | cbn [b_phis phis_env fold_left lookup name_eqb term_eqb String.eqb Ascii.eqb Bool.eqb andb value_x word_at_class modulus];
        reflexivity ]
    | cbn [b_insts b_jump]; advance_mem m Hreg ] ].

(** Every checkpoint of [scan_ct_inv] satisfies [block_safe] by straight-line
    symbolic execution of its basic block. *)
Lemma scan_ct_block_safe buf tbl len win m0 :
  readable_slice m0 buf len ->
  readable_slice m0 tbl 16 ->
  0 <= win -> win + 16 <= len ->
  forall c, scan_ct_inv buf tbl len win m0 c ->
    TC.block_safe cttable_ge (scan_ct_inv buf tbl len win m0) c.
Proof.
  intros Hbuf Htbl Hwin Hlen_ge c Hinv.
  pose proof Hbuf as [_ Hb_buf _ Hbuf_wrap _].
  pose proof Htbl as [_ Hb_tbl _ Htbl_wrap _].
  assert (Hlen_mod : len mod 2 ^ 64 = len) by (apply Z.mod_small; lia).
  assert (Hwin_mod : win mod 2 ^ 64 = win) by (apply Z.mod_small; lia).
  assert (Hlim_mod : (win + 16) mod 2 ^ 64 = win + 16) by (apply Z.mod_small; lia).
  assert (Hb_buf_mod : ptr_addr buf mod 2 ^ 64 = ptr_addr buf) by (apply Z.mod_small; lia).
  assert (Hb_tbl_mod : ptr_addr tbl mod 2 ^ 64 = ptr_addr tbl) by (apply Z.mod_small; lia).
  set (p_off := len - win - 16).
  assert (Hp_addr_mod : (ptr_addr buf + p_off) mod 2 ^ 64 = ptr_addr buf + p_off)
    by (apply Z.mod_small; subst p_off; lia).
  destruct Hinv as
    [skip start m fuel Hreg
    |e j m fuel Hreg Hj Hwin_e Htbl_e Hp_e Hj_e
       ([start_val Hstart_e] & [i_val Hi_e] & [res_val Hres_e] & _)
    |e j k m fuel Hreg Hj Hk Hwin_e Htbl_e Hp_e Hj_e Hk_e
       ([start_val Hstart_e] & [i_val Hi_e] & [res_val Hres_e] &
        [c_val Hc_e] & [inr_val Hinr_e] & [mask_val Hmask_e] & [exp_val Hexp_e] & _)];
    try (unfold ptr_shift in Hp_e).
  - (* Case 1: entry block `start` -> `L28` *)
    unfold scan_ct_entry.
    step_enter_or_fuel fuel m Hreg.
    (* v21 = ‹buf› +p ‹len› *)
    assert (Hm21 : (ptr_addr buf + len) mod 2 ^ 64 = ptr_addr buf + len) by (apply Z.mod_small; lia).
    eapply TC.bs_step.
    { apply (rule_flight _ _ _ _ _ _ _ _ _ _ _ _ _ _
        [WInt (ptr_addr buf); WInt len] (ptr_addr buf + len) (ptr_cap buf));
        [cbn; rewrite Hb_buf_mod, Hlen_mod; reflexivity
        |cbn [alu cond_bit modulus]; rewrite Hm21; reflexivity
        |reflexivity]. }
    advance_mem m Hreg.
    (* v23 = v21 -p ‹win› *)
    assert (Hm23 : (ptr_addr buf + len - win) mod 2 ^ 64 = ptr_addr buf + len - win)
      by (apply Z.mod_small; lia).
    eapply TC.bs_step.
    { apply (rule_flight _ _ _ _ _ _ _ _ _ _ _ _ _ _
        [WInt (ptr_addr buf + len); WInt win] (ptr_addr buf + len - win) (ptr_cap buf));
        [cbn; rewrite Hm21, Hwin_mod; reflexivity
        |cbn [alu cond_bit modulus]; rewrite Hm23; reflexivity
        |reflexivity]. }
    advance_mem m Hreg.
    (* ‹p› = v23 -p 16 *)
    assert (Hm24 : (ptr_addr buf + len - win - 16) mod 2 ^ 64 = ptr_addr buf + p_off).
    { subst p_off. replace (ptr_addr buf + len - win - 16) with (ptr_addr buf + (len - win - 16)) by lia.
      apply Z.mod_small; lia. }
    eapply TC.bs_step.
    { apply (rule_flight _ _ _ _ _ _ _ _ _ _ _ _ _ _
        [WInt (ptr_addr buf + len - win); WInt 16] (ptr_addr buf + p_off) (ptr_cap buf));
        [cbn; rewrite Hm23; reflexivity
        |cbn [alu cond_bit modulus]; rewrite Hm24; reflexivity
        |reflexivity]. }
    advance_mem m Hreg.
    (* goto L28 *)
    eapply TC.bs_step; [apply rule_goto | advance_mem m Hreg].
    cbn [edge_label].
    (* Enter L28 from start *)
    destruct (Z.eqb_spec (fuel - 1) 0) as [Hfuel0 | Hfuel1].
    { rewrite Hfuel0. eapply TC.bs_done; [apply rule_out_of_fuel | apply not_failure_out_of_fuel]. }
    eapply TC.bs_inv.
    { eapply (rule_enter _ _ _ _ _ _ _ _ _ _ _ Hfuel1); reflexivity. }
    cbn [b_insts b_jump].
    eapply (sci_outer buf tbl len win m0 _ 0 m);
      try assumption; try lia; unfold ptr_shift; try solve_lookup;
      repeat split; eexists; solve_lookup.
  - (* Case 2: outer loop header `L28` -> `L31` (done) or `L29` -> `L55` *)
    assert (Hj_mod : j mod 2 ^ 64 = j) by (apply Z.mod_small; lia).
    (* v34 = add ‹win›, 16 *)
    eapply TC.bs_step.
    { apply (rule_let _ _ _ _ _ _ _ _ _ _ _ _ _ _ [L; L] [WInt win; WInt 16] (WInt (win + 16)) m);
        [reflexivity | reflexivity | cbn [map2_option value_x]; solve_lookup
        | unfold op_res, op_res_int; cbn [additive_res alu cond_bit modulus]; rewrite Hlim_mod; reflexivity]. }
    advance_mem m Hreg.
    (* v35 = cmp ult ‹j›, v34 *)
    set (cond := if j <? win + 16 then 1 else 0).
    eapply TC.bs_step.
    { apply (rule_let _ _ _ _ _ _ _ _ _ _ _ _ _ _ [L; L] [WInt j; WInt (win + 16)] (WInt cond) m);
        [reflexivity | reflexivity | cbn [map2_option value_x]; solve_lookup
        | unfold op_res, op_res_int; cbn [alu cond_bit modulus]; reflexivity]. }
    advance_mem m Hreg.
    destruct (Z.ltb_spec j (win + 16)) as [Hj_lt | Hj_ge]; subst cond; cbn [Z.ltb] in *.
    + (* j < win + 16: branch to L29 *)
      eapply TC.bs_step.
      { apply (rule_branch _ _ _ _ _ _ _ _ _ _ _ 1). cbn [value_x]; solve_lookup. }
      advance_mem m Hreg.
      cbn [edge_label Z.eqb].
      step_enter_or_fuel fuel m Hreg.
      (* v39 = ‹p› +p ‹j› *)
      assert (Haddr_mod : (ptr_addr buf + p_off + j) mod 2 ^ 64 = ptr_addr buf + p_off + j)
        by (apply Z.mod_small; subst p_off; lia).
      eapply TC.bs_step.
      { apply (rule_flight _ _ _ _ _ _ _ _ _ _ _ _ _ _
          [WInt (ptr_addr buf + p_off); WInt j] (ptr_addr buf + p_off + j) (ptr_cap buf));
          [cbn [map_option flight_arg_x value_x]; repeat (rewrite lookup_put_other; [|reflexivity]);
           rewrite Hp_e, Hj_e; cbn [word_at_class modulus ptr_addr]; fold p_off; rewrite Hp_addr_mod, Hj_mod; reflexivity
          |cbn [alu cond_bit modulus]; rewrite Haddr_mod; reflexivity
          |cbn [flight_cap value_x]; repeat (rewrite lookup_put_other; [|reflexivity]); rewrite Hp_e; reflexivity]. }
      advance_mem m Hreg.
      (* chk0 = check 0 1 read 1 [v39] *)
      assert (Hbuf_m : readable_slice m buf len) by (eapply readable_slice_regions; [symmetry; exact Hreg | exact Hbuf]).
      eapply TC.bs_step.
      { apply (rule_let _ _ _ _ _ _ _ _ _ _ _ _ _ _ [P]
          [WPtr (mkPtr (ptr_addr buf + p_off + j) (ptr_cap buf))]
          (WPtr (mkPtr (ptr_addr buf + p_off + j) (ptr_cap buf))) m);
          [reflexivity | reflexivity | cbn [map2_option value_x]; solve_lookup
          | cbn [op_res op_res_int ptr_addr ptr_cap]; change (1 - 0) with 1;
            replace (ptr_addr buf + p_off + j) with (ptr_addr buf + (p_off + j)) by lia;
            rewrite (readable_slice_byte_access m buf len (p_off + j) Hbuf_m ltac:(subst p_off; lia));
            reflexivity]. }
      advance_mem m Hreg.
      (* ‹c› = raw_load ub 0 [chk0] *)
      assert (Hbuf_m2 : readable_slice m buf len) by (eapply readable_slice_regions; [symmetry; exact Hreg | exact Hbuf]).
      set (cv := (m_bytes m (ptr_addr buf + (p_off + j)) mod 256) mod 2 ^ 32).
      eapply TC.bs_step.
      { apply (rule_let _ _ _ _ _ _ _ _ _ _ _ _ _ _ [A]
          [WPtr (mkPtr (ptr_addr buf + p_off + j) (ptr_cap buf))] (WInt cv) m);
          [reflexivity | reflexivity | cbn [map2_option value_x]; solve_lookup
          | cbn [op_res op_res_int ptr_addr ptr_cap];
            replace (ptr_addr buf + p_off + j) with (ptr_addr buf + (p_off + j)) by lia;
            rewrite (readable_slice_load_byte m buf len (p_off + j) Hbuf_m2 ltac:(subst p_off; lia));
            reflexivity]. }
      advance_mem m Hreg.
      (* ‹j>=ustart› = cmp uge ‹j›, ‹start› *)
      set (smod := start_val mod 2 ^ 64).
      set (c44 := if smod <=? j then 1 else 0).
      eapply TC.bs_step.
      { apply (rule_let _ _ _ _ _ _ _ _ _ _ _ _ _ _ [L; L] [WInt j; WInt smod] (WInt c44) m);
          [reflexivity | reflexivity | cbn [map2_option value_x]; solve_lookup | reflexivity]. }
      advance_mem m Hreg.
      (* v47 = add ‹start›, 16 *)
      set (n47 := (smod + 16) mod 2 ^ 64).
      eapply TC.bs_step.
      { apply (rule_let _ _ _ _ _ _ _ _ _ _ _ _ _ _ [L; L] [WInt smod; WInt 16] (WInt n47) m);
          [reflexivity | reflexivity | cbn [map2_option value_x]; solve_lookup | reflexivity]. }
      advance_mem m Hreg.
      (* v48 = cmp ult ‹j›, v47 *)
      set (c48 := if j <? (n47 mod 2 ^ 64) then 1 else 0).
      eapply TC.bs_step.
      { apply (rule_let _ _ _ _ _ _ _ _ _ _ _ _ _ _ [L; L] [WInt j; WInt (n47 mod 2 ^ 64)] (WInt c48) m);
          [reflexivity | reflexivity | cbn [map2_option value_x]; solve_lookup | reflexivity]. }
      advance_mem m Hreg.
      (* ‹in_range› = and ‹j>=ustart›, v48 *)
      set (n49 := Z.land (c44 mod 2 ^ 32) (c48 mod 2 ^ 32)).
      eapply TC.bs_step.
      { apply (rule_let _ _ _ _ _ _ _ _ _ _ _ _ _ _ [W; W] [WInt (c44 mod 2 ^ 32); WInt (c48 mod 2 ^ 32)] (WInt n49) m);
          [reflexivity | reflexivity | cbn [map2_option value_x]; solve_lookup | reflexivity]. }
      advance_mem m Hreg.
      (* ‹mask› = sub 0, ‹in_range› *)
      set (n52 := (0 - (n49 mod 2 ^ 32)) mod 2 ^ 32).
      eapply TC.bs_step.
      { apply (rule_let _ _ _ _ _ _ _ _ _ _ _ _ _ _ [W; W] [WInt 0; WInt (n49 mod 2 ^ 32)] (WInt n52) m);
          [reflexivity | reflexivity | cbn [map2_option value_x]; solve_lookup | reflexivity]. }
      advance_mem m Hreg.
      (* goto L55 *)
      eapply TC.bs_step; [apply rule_goto | advance_mem m Hreg].
      cbn [edge_label].
      (* Enter L55 from L29 *)
      destruct (Z.eqb_spec (fuel - 1) 0) as [Hfuel0 | Hfuel1].
      { rewrite Hfuel0. eapply TC.bs_done; [apply rule_out_of_fuel | apply not_failure_out_of_fuel]. }
      eapply TC.bs_inv.
      { eapply (rule_enter _ _ _ _ _ _ _ _ _ _ _ Hfuel1); reflexivity. }
      cbn [b_insts b_jump].
      eapply (sci_inner buf tbl len win m0 _ j 0 m);
        try assumption; try lia; unfold ptr_shift; try solve_lookup;
        repeat split; eexists; solve_lookup.
    + (* j = win + 16: branch to L31 and return ‹res› *)
      eapply TC.bs_step.
      { apply (rule_branch _ _ _ _ _ _ _ _ _ _ _ 0). cbn [value_x]; solve_lookup. }
      advance_mem m Hreg.
      cbn [edge_label Z.eqb].
      step_enter_or_fuel fuel m Hreg.
      eapply TC.bs_done; [| apply not_failure_ret].
      rewrite (rule_ret _ _ _ _ _ _ _ _ _ W (WInt (res_val mod 2 ^ 32)));
        [apply (rule_return_top _ _ _ _ m); reflexivity
        |reflexivity
        |cbn [value_x]; solve_lookup].
  - (* Case 3: inner loop header `L55` -> `L56` (next k) or `L58` (next j) *)
    assert (Hk_mod : k mod 2 ^ 64 = k) by (apply Z.mod_small; lia).
    assert (Hj_mod : j mod 2 ^ 64 = j) by (apply Z.mod_small; lia).
    set (kcond := if k <? 16 then 1 else 0).
    eapply TC.bs_step.
    { apply (rule_let _ _ _ _ _ _ _ _ _ _ _ _ _ _ [L; L] [WInt k; WInt 16] (WInt kcond) m);
        [reflexivity | reflexivity | cbn [map2_option value_x]; solve_lookup | reflexivity]. }
    advance_mem m Hreg.
    destruct (Z.ltb_spec k 16) as [Hk_lt | Hk_ge]; subst kcond; cbn [Z.ltb] in *.
    + (* k < 16: branch to L56 *)
      eapply TC.bs_step.
      { apply (rule_branch _ _ _ _ _ _ _ _ _ _ _ 1). cbn [value_x]; solve_lookup. }
      advance_mem m Hreg.
      cbn [edge_label Z.eqb].
      step_enter_or_fuel fuel m Hreg.
      (* ‹k==i› = cmp eq ‹k›, ‹i› *)
      set (imod := i_val mod 2 ^ 64).
      set (eqb := if k =? imod then 1 else 0).
      eapply TC.bs_step.
      { apply (rule_let _ _ _ _ _ _ _ _ _ _ _ _ _ _ [L; L] [WInt k; WInt imod] (WInt eqb) m);
          [reflexivity | reflexivity | cbn [map2_option value_x]; solve_lookup | reflexivity]. }
      advance_mem m Hreg.
      (* ‹eq_mask› = sub 0, ‹k==i› *)
      set (eqm := (0 - (eqb mod 2 ^ 32)) mod 2 ^ 32).
      eapply TC.bs_step.
      { apply (rule_let _ _ _ _ _ _ _ _ _ _ _ _ _ _ [W; W] [WInt 0; WInt (eqb mod 2 ^ 32)] (WInt eqm) m);
          [reflexivity | reflexivity | cbn [map2_option value_x]; solve_lookup | reflexivity]. }
      advance_mem m Hreg.
      (* v69 = ‹tbl› +p ‹k› *)
      assert (Haddr_mod : (ptr_addr tbl + k) mod 2 ^ 64 = ptr_addr tbl + k) by (apply Z.mod_small; lia).
      eapply TC.bs_step.
      { apply (rule_flight _ _ _ _ _ _ _ _ _ _ _ _ _ _
          [WInt (ptr_addr tbl); WInt k] (ptr_addr tbl + k) (ptr_cap tbl));
          [cbn [map_option flight_arg_x value_x]; repeat (rewrite lookup_put_other; [|reflexivity]);
           rewrite Htbl_e, Hk_e; cbn [word_at_class modulus ptr_addr]; rewrite Hb_tbl_mod, Hk_mod; reflexivity
          |cbn [alu cond_bit modulus]; rewrite Haddr_mod; reflexivity
          |cbn [flight_cap value_x]; repeat (rewrite lookup_put_other; [|reflexivity]); rewrite Htbl_e; reflexivity]. }
      advance_mem m Hreg.
      (* chk1 = check 0 1 read 1 [v69] *)
      assert (Htbl_m : readable_slice m tbl 16) by (eapply readable_slice_regions; [symmetry; exact Hreg | exact Htbl]).
      eapply TC.bs_step.
      { apply (rule_let _ _ _ _ _ _ _ _ _ _ _ _ _ _ [P]
          [WPtr (mkPtr (ptr_addr tbl + k) (ptr_cap tbl))]
          (WPtr (mkPtr (ptr_addr tbl + k) (ptr_cap tbl))) m);
          [reflexivity | reflexivity | cbn [map2_option value_x]; solve_lookup
          | cbn [op_res op_res_int ptr_addr ptr_cap]; change (1 - 0) with 1;
            rewrite (readable_slice_byte_access m tbl 16 k Htbl_m ltac:(lia)); reflexivity]. }
      advance_mem m Hreg.
      (* v70 = raw_load ub 0 [chk1] *)
      assert (Htbl_m2 : readable_slice m tbl 16) by (eapply readable_slice_regions; [symmetry; exact Hreg | exact Htbl]).
      set (tbv := (m_bytes m (ptr_addr tbl + k) mod 256) mod 2 ^ 32).
      eapply TC.bs_step.
      { apply (rule_let _ _ _ _ _ _ _ _ _ _ _ _ _ _ [A]
          [WPtr (mkPtr (ptr_addr tbl + k) (ptr_cap tbl))] (WInt tbv) m);
          [reflexivity | reflexivity | cbn [map2_option value_x]; solve_lookup
          | cbn [op_res op_res_int ptr_addr ptr_cap];
            rewrite (readable_slice_load_byte m tbl 16 k Htbl_m2 ltac:(lia)); reflexivity]. }
      advance_mem m Hreg.
      (* v72 = and v70, ‹eq_mask› *)
      set (n72 := Z.land (tbv mod 2 ^ 32) (eqm mod 2 ^ 32)).
      eapply TC.bs_step.
      { apply (rule_let _ _ _ _ _ _ _ _ _ _ _ _ _ _ [W; W] [WInt (tbv mod 2 ^ 32); WInt (eqm mod 2 ^ 32)] (WInt n72) m);
          [reflexivity | reflexivity | cbn [map2_option value_x]; solve_lookup | reflexivity]. }
      advance_mem m Hreg.
      (* ‹expected@L56› = or ‹expected›, v72 *)
      set (n73 := Z.lor (exp_val mod 2 ^ 32) (n72 mod 2 ^ 32)).
      eapply TC.bs_step.
      { apply (rule_let _ _ _ _ _ _ _ _ _ _ _ _ _ _ [W; W] [WInt (exp_val mod 2 ^ 32); WInt (n72 mod 2 ^ 32)] (WInt n73) m);
          [reflexivity | reflexivity | cbn [map2_option value_x]; solve_lookup | reflexivity]. }
      advance_mem m Hreg.
      (* ‹k@L56› = add ‹k›, 1 *)
      assert (Hk1_mod : (k + 1) mod 2 ^ 64 = k + 1) by (apply Z.mod_small; lia).
      eapply TC.bs_step.
      { apply (rule_let _ _ _ _ _ _ _ _ _ _ _ _ _ _ [L; L] [WInt k; WInt 1] (WInt (k + 1)) m);
          [reflexivity | reflexivity | cbn [map2_option value_x]; solve_lookup
          | unfold op_res, op_res_int; cbn [additive_res alu cond_bit modulus]; rewrite Hk1_mod; reflexivity]. }
      advance_mem m Hreg.
      (* goto poll L55 *)
      eapply TC.bs_step; [apply rule_goto | advance_mem m Hreg].
      cbn [edge_label].
      (* Enter L55 from L56 *)
      destruct (Z.eqb_spec (fuel - 1) 0) as [Hfuel0 | Hfuel1].
      { rewrite Hfuel0. eapply TC.bs_done; [apply rule_out_of_fuel | apply not_failure_out_of_fuel]. }
      eapply TC.bs_inv.
      { eapply (rule_enter _ _ _ _ _ _ _ _ _ _ _ Hfuel1);
          [reflexivity
          |cbn [b_phis phis_env fold_left lookup name_eqb term_eqb String.eqb Ascii.eqb Bool.eqb andb value_x word_at_class modulus];
           reflexivity]. }
      cbn [b_insts b_jump].
      eapply (sci_inner buf tbl len win m0 _ j (k + 1) m);
        try assumption; try lia; unfold ptr_shift; try solve_lookup;
        repeat split; eexists; solve_lookup.
    + (* k = 16: branch to L58 -> L28 *)
      eapply TC.bs_step.
      { apply (rule_branch _ _ _ _ _ _ _ _ _ _ _ 0). cbn [value_x]; solve_lookup. }
      advance_mem m Hreg.
      cbn [edge_label Z.eqb].
      step_enter_or_fuel fuel m Hreg.
      (* v79 = xor ‹c›, ‹expected› *)
      set (n79 := Z.lxor (c_val mod 2 ^ 32) (exp_val mod 2 ^ 32)).
      eapply TC.bs_step.
      { apply (rule_let _ _ _ _ _ _ _ _ _ _ _ _ _ _ [W; W] [WInt (c_val mod 2 ^ 32); WInt (exp_val mod 2 ^ 32)] (WInt n79) m);
          [reflexivity | reflexivity | cbn [map2_option value_x]; solve_lookup | reflexivity]. }
      advance_mem m Hreg.
      (* v81 = and v79, ‹mask› *)
      set (n81 := Z.land (n79 mod 2 ^ 32) (mask_val mod 2 ^ 32)).
      eapply TC.bs_step.
      { apply (rule_let _ _ _ _ _ _ _ _ _ _ _ _ _ _ [W; W] [WInt (n79 mod 2 ^ 32); WInt (mask_val mod 2 ^ 32)] (WInt n81) m);
          [reflexivity | reflexivity | cbn [map2_option value_x]; solve_lookup | reflexivity]. }
      advance_mem m Hreg.
      (* ‹res@L58› = or ‹res›, v81 *)
      set (n82 := Z.lor (res_val mod 2 ^ 32) (n81 mod 2 ^ 32)).
      eapply TC.bs_step.
      { apply (rule_let _ _ _ _ _ _ _ _ _ _ _ _ _ _ [W; W] [WInt (res_val mod 2 ^ 32); WInt (n81 mod 2 ^ 32)] (WInt n82) m);
          [reflexivity | reflexivity | cbn [map2_option value_x]; solve_lookup | reflexivity]. }
      advance_mem m Hreg.
      (* v85 = ext uw ‹in_range› *)
      set (n85 := ((inr_val mod 2 ^ 32) mod 2 ^ 32) mod 2 ^ 64).
      eapply TC.bs_step.
      { apply (rule_let _ _ _ _ _ _ _ _ _ _ _ _ _ _ [W] [WInt (inr_val mod 2 ^ 32)] (WInt n85) m);
          [reflexivity | reflexivity | cbn [map2_option value_x]; solve_lookup | reflexivity]. }
      advance_mem m Hreg.
      (* ‹i@L58› = add ‹i›, v85 *)
      set (n86 := ((i_val mod 2 ^ 64) + (n85 mod 2 ^ 64)) mod 2 ^ 64).
      eapply TC.bs_step.
      { apply (rule_let _ _ _ _ _ _ _ _ _ _ _ _ _ _ [L; L] [WInt (i_val mod 2 ^ 64); WInt (n85 mod 2 ^ 64)] (WInt n86) m);
          [reflexivity | reflexivity | cbn [map2_option value_x]; solve_lookup | reflexivity]. }
      advance_mem m Hreg.
      (* ‹j@L58› = add ‹j›, 1 *)
      assert (Hj1_mod : (j + 1) mod 2 ^ 64 = j + 1) by (apply Z.mod_small; lia).
      eapply TC.bs_step.
      { apply (rule_let _ _ _ _ _ _ _ _ _ _ _ _ _ _ [L; L] [WInt j; WInt 1] (WInt (j + 1)) m);
          [reflexivity | reflexivity | cbn [map2_option value_x]; solve_lookup
          | unfold op_res, op_res_int; cbn [additive_res alu cond_bit modulus]; rewrite Hj1_mod; reflexivity]. }
      advance_mem m Hreg.
      (* goto poll L28 *)
      eapply TC.bs_step; [apply rule_goto | advance_mem m Hreg].
      cbn [edge_label].
      (* Enter L28 from L58 *)
      destruct (Z.eqb_spec (fuel - 1) 0) as [Hfuel0 | Hfuel1].
      { rewrite Hfuel0. eapply TC.bs_done; [apply rule_out_of_fuel | apply not_failure_out_of_fuel]. }
      eapply TC.bs_inv.
      { eapply (rule_enter _ _ _ _ _ _ _ _ _ _ _ Hfuel1);
          [reflexivity
          |cbn [b_phis phis_env fold_left lookup name_eqb term_eqb String.eqb Ascii.eqb Bool.eqb andb value_x word_at_class modulus];
           reflexivity]. }
      cbn [b_insts b_jump].
      eapply (sci_outer buf tbl len win m0 _ (j + 1) m);
        try assumption; try lia; unfold ptr_shift; try solve_lookup;
        repeat split; eexists; solve_lookup.
Qed.

(** Plain memory safety for `scan_ct`: for every readable `buf` of length `len`,
    exact 16-byte `tbl`, and valid public window `win + 16 <= len`, no reachable
    machine state panics or goes stuck. *)
Theorem scan_ct_plain_safe buf tbl len win skip start m s fuel :
  readable_slice m buf len ->
  readable_slice m tbl 16 ->
  0 <= win -> win + 16 <= len ->
  TC.plain_safe cttable_ge (scan_ct_entry buf tbl len win skip start) m s fuel.
Proof.
  intros Hbuf Htbl Hwin Hlen_ge.
  eapply (TC.plain_safe_by_block_safe cttable_ge (scan_ct_inv buf tbl len win m)).
  - apply sci_start. reflexivity.
  - apply scan_ct_inv_regions.
  - apply scan_ct_block_safe; assumption.
Qed.

(** Universal poison safety for `scan_ct`: combining [scan_ct_plain_safe] with
    the reflective check [scan_ct_taint_ok] proves that `scan_ct` avoids every
    panic and [pol_strict] poison fault for any poison map without
    `CannotLoad` redzones. *)
Theorem scan_ct_safe buf tbl len win skip start m pm paux s fuel :
  readable_slice m buf len ->
  readable_slice m tbl 16 ->
  0 <= win -> win + 16 <= len ->
  (forall a, pb_no_load (pm a) = false) ->
  poison_safe pol_strict cttable_ge
    (scan_ct_entry buf tbl len win skip start)
    scan_ct_te m pm paux s fuel.
Proof.
  intros Hbuf Htbl Hwin Hlen_ge Hnoload.
  eapply (TC.taint_check_poison_safe pol_strict cttable_ge scan_ct_tspecs
            (TAtom "scan_ct") fn_scan_ct scan_ct_tspec);
    try exact scan_ct_taint_ok; try reflexivity; try assumption.
  - exists (TAtom "start"). split; reflexivity.
  - exists scan_ct_te. split; reflexivity.
  - repeat split; [apply Hnoload | apply taint_le_all_r | discriminate | intro; apply taint_le_all_r].
  - eapply scan_ct_plain_safe; eassumption.
Qed.

(** Universal two-run constant-time theorem for `scan_ct`: for every readable
    buffer `buf` of public length `len`, exact 16-byte table `tbl`, and valid
    public window `win + 16 <= len`, any two executions with the same live
    region layout emit the exact same plain operational leakage trace under
    [pol_strict], no matter how `skip`, `start`, or any byte or capability in
    memory differ. *)
Theorem scan_ct_constant_time buf tbl len win skip1 start1 skip2 start2 m1 m2 s fuel :
  readable_slice m1 buf len ->
  readable_slice m1 tbl 16 ->
  0 <= win -> win + 16 <= len ->
  m_regions m1 = m_regions m2 ->
  R.ready s m1 -> R.ready s m2 ->
  forall steps, exists tr,
    PD.driver_trace pol_strict cttable_ge steps
      cfg{ (scan_ct_entry buf tbl len win skip1 start1); mem: m1; fuel: fuel } s = Some tr /\
    PD.driver_trace pol_strict cttable_ge steps
      cfg{ (scan_ct_entry buf tbl len win skip2 start2); mem: m2; fuel: fuel } s = Some tr.
Proof.
  intros Hbuf Htbl Hwin Hlen_ge Hreg Hr1 Hr2 steps.
  eapply (TC.taint_check_constant_time pol_strict cttable_ge scan_ct_tspecs
            (TAtom "scan_ct") fn_scan_ct scan_ct_tspec
            (scan_ct_entry buf tbl len win skip1 start1)
            (scan_ct_entry buf tbl len win skip2 start2)
            scan_ct_te m1 m2 (fun _ => pb_secret taint_all) (fun _ => taint_all) s fuel);
    try exact scan_ct_taint_ok; try reflexivity; try assumption.
  - exists (TAtom "start"). split; reflexivity.
  - exists scan_ct_te. split; reflexivity.
  - repeat split; reflexivity.
  - apply scan_ct_inputs_related. exact Hreg.
  - eapply scan_ct_plain_safe; eassumption.
Qed.

End CtTableScan.

(** ## Separating single-run taint from two-run noninterference

    Optimizing compilers sometimes rebase a public loop induction variable by a
    secret offset, computing `base = buf + sec`, `lim = len - sec`, and
    `k = j - sec`. Single-run taint tracking flags both `base + k` and
    `k == lim` as secret-dependent even though the secret cancels modulo
    `2 ^ 64` at every step.

    The minimal validated IR function below models this transformation in
    [IRNotation] and proves both sides of the separation. Both the static
    checker [taint_check_fn] and dynamic [prun] reject it with [CannotBranch]
    and [CannotIndex], whereas direct two-run simulation proves that its plain
    operational leakage trace is identical for every pair of secret offsets. *)

(** Minimal checked-IR loop rebasing both the base pointer and the loop counter
    by the secret offset `sec`. *)
Definition rebased_scan_fn : func :=
  ir_fn{ "export" "rebased_scan"(P %"buf", L %"len", L %"sec") -> (RClass W) {
  @"start":
    %"base" = %"buf" +p %"sec";
    %"lim" : L = Sub %"len", %"sec";
    %"k0" : L = Sub #0, %"sec"
    => goto "loop";
  @"loop" [%"k" : L = phi("start" => %"k0", "body" => %"k1");
           %"acc" : W = phi("start" => #0, "body" => %"acc1")]:
    %"done" : W = (Cmp Eq L) %"k", %"lim"
    => br %"done" ? "exit" : "body";
  @"body":
    %"addr" = %"base" +p %"k";
    %"chk" : A = (Check 0 1 Read 1) %"addr";
    %"b" : W = (RawLoad (LdNarrow Ub) 0) %"chk";
    %"acc1" : W = Xor %"acc", %"b";
    %"k1" : L = Add %"k", #1
    => goto poll "loop";
  @"exit":
    => ret %"acc"
} }.

Definition rebased_module : module := [IFunc rebased_scan_fn].
Definition rebased_ge : genv := mkGenv rebased_module [] free_res.

(** Campaign 1's [[validator]] accepts [rebased_scan_fn]. *)
Theorem rebased_scan_valid : valid rebased_module = Some true.
Proof. vm_compute. reflexivity. Qed.

(** Static taint contract marking `sec` secret and `buf`, `len` public. *)
Definition rebased_tspec : tspec :=
  {| ts_args := [WTPtr taint_bot taint_bot; WTInt taint_bot; WTInt taint_all];
     ts_ret := Some (WTInt taint_all);
     ts_mem := taint_bot;
     ts_aux := taint_bot;
     ts_writes := false |}.

(** The static reflective taint checker rejects [rebased_scan_fn] under both
    [pol_strict] and [pol_erased]. *)
Theorem rebased_scan_taint_rejected :
  taint_check_fn pol_strict rebased_module [] rebased_scan_fn rebased_tspec = false /\
  taint_check_fn pol_erased rebased_module [] rebased_scan_fn rebased_tspec = false.
Proof. vm_compute. split; reflexivity. Qed.

Definition rebased_entry (buf : ptr) (len sec : Z) : frame :=
  frame{ rebased_scan_fn env:
    [(TAtom "sec", WInt sec); (TAtom "len", WInt len); (TAtom "buf", WPtr buf)]
    | enter: @"start" }.

Definition rebased_te (t_sec : taint) : tenv :=
  [(TAtom "sec", WTInt t_sec); (TAtom "len", WTInt taint_bot);
   (TAtom "buf", WTPtr taint_bot taint_bot)].

(** Single-run dynamic taint rejects [rebased_scan_fn] on both branch poison
    (at the loop exit test `k == lim`) and index poison (at `base + k`). *)
Theorem rebased_scan_taint_rejects :
  let m := scan_mem (fun k => k) sample_tbl 16 in
  prun pol_strict rebased_ge 10
    cfg{ (rebased_entry scan_buf_ptr 4 17); mem: m; fuel: 50 }
    (mkPState (rebased_te taint_branch) [] (fun _ => pb_clean) (fun _ => taint_bot)) =
    PTrap CannotBranch /\
  prun pol_erased rebased_ge 15
    cfg{ (rebased_entry scan_buf_ptr 4 17); mem: m; fuel: 50 }
    (mkPState (rebased_te taint_index) [] (fun _ => pb_clean) (fun _ => taint_bot)) =
    PTrap CannotIndex.
Proof. vm_compute. split; reflexivity. Qed.

(** Modular cancellation identities modulo `2 ^ 64` that make the rebased
    loop's exit comparison and dereferenced address independent of `sec`. *)
Lemma mod64_cancel_eq (a b s : Z) :
  0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
  (((a - s) mod 2 ^ 64) =? ((b - s) mod 2 ^ 64)) = (a =? b).
Proof.
  intros Ha Hb.
  destruct (Z.eqb_spec a b) as [-> | Hne].
  - rewrite Z.eqb_refl. reflexivity.
  - apply Z.eqb_neq. intros Heq.
    apply Hne.
    assert (Hdiff : ((a - s) - (b - s)) mod 2 ^ 64 = 0).
    { rewrite Zminus_mod, Heq, Z.sub_diag, Zmod_0_l. reflexivity. }
    replace ((a - s) - (b - s)) with (a - b) in Hdiff by lia.
    apply Z.mod_divide in Hdiff; [|lia].
    destruct Hdiff as [q Hq].
    assert (Hq0 : q = 0) by nia. lia.
Qed.

Lemma mod64_cancel_add (b s j : Z) :
  (((b + s) mod 2 ^ 64) + ((j - s) mod 2 ^ 64)) mod 2 ^ 64 = (b + j) mod 2 ^ 64.
Proof.
  rewrite <- Zplus_mod.
  replace (b + s + (j - s)) with (b + j) by lia.
  reflexivity.
Qed.

Lemma mod64_step_k (j s : Z) :
  (((j - s) mod 2 ^ 64) + 1) mod 2 ^ 64 = ((j + 1) - s) mod 2 ^ 64.
Proof.
  rewrite Zplus_mod_idemp_l.
  replace (j - s + 1) with (j + 1 - s) by lia.
  reflexivity.
Qed.

(** Loop-header environment for [rebased_scan_fn]: at public iteration `j`,
    the base pointer is shifted up by `s` while `lim` and `k` are shifted down
    by `s`, all modulo `2 ^ 64`. *)
Record rebased_loop_env (e : env) (buf : ptr) (len j s : Z) : Prop :=
  mkRebasedLoopEnv {
    rle_base : e.[@"base"] = ptr_val (ptr_shift_mod buf s);
    rle_lim : e.[@"lim"] = int_val ((len - s) mod 2 ^ 64);
    rle_k : e.[@"k"] = int_val ((j - s) mod 2 ^ 64);
    rle_acc : has_int e (TAtom "acc")
  }.

(** Machine configuration at the `loop` header of [rebased_scan_fn]. *)
Definition rebased_loop_cfg (e : env) (m : mem) (fuel : Z) : config :=
  cfg{ rebased_scan_fn env: e | at @"loop" {
         ir[ %"done" : W = (Cmp Eq L) %"k", %"lim" ]
         => ir{ br %"done" ? "exit" : "body" }
       }; mem: m; fuel: fuel }.

(** Emit at most `steps` events from a straight-line block `evs`, then continue
    with `rest` on any remaining step budget. *)
Fixpoint prefix_then (steps : nat) (evs : list leak_event)
    (rest : nat -> list leak_event) : list leak_event :=
  match steps, evs with
  | O, _ => []
  | S n, [] => rest (S n)
  | S n, ev :: tl => ev :: prefix_then n tl rest
  end.

(** Secret-independent leakage events emitted by one iteration of `body` at
    public byte offset `j`. *)
Definition rebased_body_events (pol : poison_policy) (buf : ptr) (j : Z)
    : list leak_event :=
  [LeakEnter (TAtom "body") (Some (TAtom "loop"));
   LeakPure;
   if pol_check_branches pol
   then LeakCheck (Check 0 1 Read 1) (mkPtr (ptr_addr buf + j) (ptr_cap buf))
   else LeakPure;
   LeakMem Read (ptr_addr buf + j) 1;
   LeakPure;
   LeakPure;
   LeakGoto (TAtom "loop")].

(** Secret-independent reference trace of [rebased_scan_fn] from iteration `j`
    with `rem` iterations remaining (`j + rem = len`). *)
Fixpoint rebased_loop_trace (pol : poison_policy) (buf : ptr)
    (rem : nat) (j fuel : Z) (steps : nat) : list leak_event :=
  match rem with
  | O =>
      prefix_then steps [LeakPure; LeakBranch true (TAtom "exit")]
        (fun n =>
          if fuel =? 0 then prefix_then n [LeakDone "out_of_fuel"] (fun _ => [])
          else prefix_then n
            [LeakEnter (TAtom "exit") (Some (TAtom "loop")); LeakRet]
            (fun _ => []))
  | S rem' =>
      prefix_then steps [LeakPure; LeakBranch false (TAtom "body")]
        (fun n =>
          if fuel =? 0 then prefix_then n [LeakDone "out_of_fuel"] (fun _ => [])
          else
            prefix_then n (rebased_body_events pol buf j)
              (fun m =>
                if (fuel - 1) =? 0 then prefix_then m [LeakDone "out_of_fuel"] (fun _ => [])
                else prefix_then m [LeakEnter (TAtom "loop") (Some (TAtom "body"))]
                  (rebased_loop_trace pol buf rem' (j + 1) (fuel - 2))))
  end.

(** Secret-independent reference trace of [rebased_scan_fn] from entry. *)
Definition rebased_scan_trace (pol : poison_policy) (buf : ptr)
    (len fuel : Z) (steps : nat) : list leak_event :=
  if fuel =? 0 then
    prefix_then steps [LeakDone "out_of_fuel"] (fun _ => [])
  else
    prefix_then steps
      [LeakEnter (TAtom "start") None; LeakPure; LeakPure; LeakPure;
       LeakGoto (TAtom "loop")]
      (fun n =>
        if (fuel - 1) =? 0 then prefix_then n [LeakDone "out_of_fuel"] (fun _ => [])
        else prefix_then n [LeakEnter (TAtom "loop") (Some (TAtom "start"))]
          (rebased_loop_trace pol buf (Z.to_nat len) 0 (fuel - 2))).

(** Advancing one non-terminal step matches the head event of [prefix_then]. *)
Lemma run_trace_prefix_next pol ge n c c' ev evs rest :
  Semantics.step ge c = Next c' ->
  leak_of pol ge c = ev ->
  run_trace pol ge n c' = Some (prefix_then n evs rest) ->
  run_trace pol ge (S n) c = Some (prefix_then (S n) (ev :: evs) rest).
Proof.
  intros Hst Hlk Hrest. cbn [run_trace prefix_then].
  rewrite Hst, Hlk, Hrest. reflexivity.
Qed.

(** Advancing one terminal step matches a one-event [prefix_then] tail. *)
Lemma run_trace_prefix_done pol ge n c o ev :
  Semantics.step ge c = Done o ->
  leak_of pol ge c = ev ->
  run_trace pol ge (S n) c = Some (prefix_then (S n) [ev] (fun _ => [])).
Proof.
  intros Hst Hlk. cbn [run_trace prefix_then].
  rewrite Hst, Hlk. destruct n; reflexivity.
Qed.

(** Handing off an empty [prefix_then] block to its continuation `rest`. *)
Lemma run_trace_prefix_nil pol ge n c rest :
  (forall m, n = S m -> run_trace pol ge (S m) c = Some (rest (S m))) ->
  run_trace pol ge n c = Some (prefix_then n [] rest).
Proof.
  destruct n as [|m]; intros H; [reflexivity | exact (H m eq_refl)].
Qed.

(** Single-step helpers for advancing a straight-line trace proof. *)
Local Ltac trace_next rule_tac leak_tac :=
  match goal with
  | |- run_trace _ _ (S _) _ = Some _ =>
      eapply run_trace_prefix_next; [rule_tac | leak_tac |]
  | |- run_trace _ _ ?steps _ = Some _ =>
      destruct steps as [|steps]; [reflexivity|];
      eapply run_trace_prefix_next; [rule_tac | leak_tac |]
  end.

Local Ltac trace_done rule_tac leak_tac :=
  match goal with
  | |- run_trace _ _ (S _) _ = Some _ =>
      eapply run_trace_prefix_done; [rule_tac | leak_tac]
  | |- run_trace _ _ ?steps _ = Some _ =>
      destruct steps as [|steps]; [reflexivity|];
      eapply run_trace_prefix_done; [rule_tac | leak_tac]
  end.

(** Single-run characterization of the `loop` block: for any secret offset `s`,
    the loop emits the secret-independent reference trace [rebased_loop_trace]. *)
Lemma rebased_loop_trace_eq pol buf m len s :
  readable_slice m buf len ->
  forall rem j fuel e steps,
    0 <= j -> j + Z.of_nat rem = len ->
    rebased_loop_env e buf len j s ->
    run_trace pol rebased_ge steps (rebased_loop_cfg e m fuel) =
      Some (rebased_loop_trace pol buf rem j fuel steps).
Proof.
  intros Hsl rem.
  pose proof Hsl as [_ Hb Hlen Hblim _].
  induction rem as [|rem IH]; intros j fuel e steps Hj Hrem [Hbase Hlim Hk [acc Hacc]];
    unfold rebased_loop_cfg; unfold ptr_shift_mod in Hbase; cbn [rebased_loop_trace].
  - (* Exit iteration: j = len *)
    assert (Hj_eq : j = len) by lia. subst j.
    assert (Hcmp : ((len - s) mod 2 ^ 64 =? (len - s) mod 2 ^ 64) = true) by apply Z.eqb_refl.
    trace_next
      ltac:(apply (rule_let _ _ _ _ _ _ _ _ _ _ _ _ _ _ [L; L]
              [WInt ((len - s) mod 2 ^ 64); WInt ((len - s) mod 2 ^ 64)] (WInt 1) m);
            try reflexivity;
            [cbn [map2_option value_x]; rewrite Hk, Hlim; cbn [word_at_class modulus];
             repeat rewrite Zmod_mod; reflexivity
            |unfold op_res, op_res_int; cbn; rewrite Hcmp; reflexivity])
      ltac:(reflexivity).
    trace_next
      ltac:(apply (rule_branch _ _ _ _ _ _ _ _ _ _ _ 1); cbn [value_x]; solve_lookup)
      ltac:(cbn [leak_of c_frame fr_at fr_env value_x]; rewrite lookup_put_same; reflexivity).
    cbn [edge_label Z.eqb].
    apply run_trace_prefix_nil. intros n _.
    destruct (Z.eqb_spec fuel 0) as [-> | Hfuel].
    + trace_done ltac:(apply rule_out_of_fuel) ltac:(reflexivity).
    + trace_next
        ltac:(eapply (rule_enter _ _ _ _ _ _ _ _ _ _ _ Hfuel); reflexivity)
        ltac:(cbn [leak_of rebased_entry c_frame c_fuel fr_at]; rewrite (proj2 (Z.eqb_neq fuel 0) Hfuel); reflexivity).
      cbn [b_insts b_jump].
      trace_done
        ltac:(rewrite (rule_ret _ _ _ _ _ _ _ _ _ W (WInt (acc mod 2 ^ 32)));
              [apply (rule_return_top _ _ _ _ m); reflexivity
              |reflexivity | cbn [value_x]; solve_lookup])
        ltac:(reflexivity).
  - (* Body iteration: j < len *)
    assert (Hcmp : ((j - s) mod 2 ^ 64 =? (len - s) mod 2 ^ 64) = false).
    { rewrite mod64_cancel_eq by lia. apply Z.eqb_neq; lia. }
    assert (Hbj : (ptr_addr buf + j) mod 2 ^ 64 = ptr_addr buf + j) by (apply Z.mod_small; lia).
    assert (Hadd : (((ptr_addr buf + s) mod 2 ^ 64) + ((j - s) mod 2 ^ 64)) mod 2 ^ 64 = ptr_addr buf + j)
      by (rewrite mod64_cancel_add; exact Hbj).
    set (bv := (m_bytes m (ptr_addr buf + j) mod 256) mod 2 ^ 32).
    set (acc' := Z.lxor (acc mod 2 ^ 32) (bv mod 2 ^ 32)).
    trace_next
      ltac:(apply (rule_let _ _ _ _ _ _ _ _ _ _ _ _ _ _ [L; L]
              [WInt ((j - s) mod 2 ^ 64); WInt ((len - s) mod 2 ^ 64)] (WInt 0) m);
            try reflexivity;
            [cbn [map2_option value_x]; rewrite Hk, Hlim; cbn [word_at_class modulus];
             repeat rewrite Zmod_mod; reflexivity
            |unfold op_res, op_res_int; cbn; rewrite Hcmp; reflexivity])
      ltac:(reflexivity).
    trace_next
      ltac:(apply (rule_branch _ _ _ _ _ _ _ _ _ _ _ 0); cbn [value_x]; solve_lookup)
      ltac:(cbn [leak_of c_frame fr_at fr_env value_x]; rewrite lookup_put_same; reflexivity).
    cbn [edge_label Z.eqb].
    apply run_trace_prefix_nil. intros n _.
    destruct (Z.eqb_spec fuel 0) as [-> | Hfuel].
    + trace_done ltac:(apply rule_out_of_fuel) ltac:(reflexivity).
    + unfold rebased_body_events.
      trace_next
        ltac:(eapply (rule_enter _ _ _ _ _ _ _ _ _ _ _ Hfuel); reflexivity)
        ltac:(cbn [leak_of rebased_entry c_frame c_fuel fr_at]; rewrite (proj2 (Z.eqb_neq fuel 0) Hfuel); reflexivity).
      cbn [b_insts b_jump].
      trace_next
        ltac:(apply (rule_flight _ _ _ _ _ _ _ _ _ _ _ _ _ _
                [WInt ((ptr_addr buf + s) mod 2 ^ 64); WInt ((j - s) mod 2 ^ 64)] (ptr_addr buf + j) (ptr_cap buf));
              [cbn [map_option flight_arg_x value_x]; repeat (rewrite lookup_put_other; [|reflexivity]);
               rewrite Hbase, Hk; cbn [word_at_class modulus ptr_addr]; repeat rewrite Zmod_mod; reflexivity
              |cbn [alu cond_bit modulus]; rewrite Hadd; reflexivity
              |cbn [flight_cap value_x]; repeat (rewrite lookup_put_other; [|reflexivity]); rewrite Hbase; reflexivity])
        ltac:(reflexivity).
      trace_next
        ltac:(apply (rule_let _ _ _ _ _ _ _ _ _ _ _ _ _ _ [P]
                [WPtr (mkPtr (ptr_addr buf + j) (ptr_cap buf))]
                (WPtr (mkPtr (ptr_addr buf + j) (ptr_cap buf))) m);
              try reflexivity;
              cbn [op_res op_res_int ptr_addr ptr_cap]; change (1 - 0) with 1;
              rewrite (readable_slice_byte_access m buf len j Hsl ltac:(lia)); reflexivity)
        ltac:(cbn [leak_of c_frame fr_at fr_env value_x]; rewrite lookup_put_same; reflexivity).
      trace_next
        ltac:(apply (rule_let _ _ _ _ _ _ _ _ _ _ _ _ _ _ [A]
                [WPtr (mkPtr (ptr_addr buf + j) (ptr_cap buf))] (WInt bv) m);
              try reflexivity;
              cbn [op_res op_res_int ptr_addr ptr_cap];
              rewrite (readable_slice_load_byte m buf len j Hsl ltac:(lia)); reflexivity)
        ltac:(cbn [leak_of c_frame fr_at fr_env value_x load_type_bytes];
              rewrite lookup_put_same; cbn [word_at_class ptr_addr]; unfold raw_address;
              rewrite Z.add_0_r, Hbj; reflexivity).
      trace_next
        ltac:(apply (rule_let _ _ _ _ _ _ _ _ _ _ _ _ _ _ [W; W]
                [WInt (acc mod 2 ^ 32); WInt (bv mod 2 ^ 32)] (WInt acc') m);
              try reflexivity; cbn [map2_option value_x]; solve_lookup)
        ltac:(reflexivity).
      trace_next
        ltac:(apply (rule_let _ _ _ _ _ _ _ _ _ _ _ _ _ _ [L; L]
                [WInt ((j - s) mod 2 ^ 64); WInt 1] (WInt (((j + 1) - s) mod 2 ^ 64)) m);
              try reflexivity;
              [cbn [map2_option value_x]; repeat (rewrite lookup_put_other; [|reflexivity]);
               rewrite Hk; cbn [word_at_class modulus]; rewrite Zmod_mod; reflexivity
              |unfold op_res, op_res_int; cbn [additive_res alu cond_bit modulus]; rewrite mod64_step_k; reflexivity])
        ltac:(reflexivity).
      trace_next ltac:(apply rule_goto) ltac:(reflexivity).
      cbn [edge_label].
      apply run_trace_prefix_nil. intros m_rem _.
      destruct (Z.eqb_spec (fuel - 1) 0) as [Hfuel1 | Hfuel1].
      * trace_done
          ltac:(rewrite Hfuel1; apply rule_out_of_fuel)
          ltac:(cbn [leak_of c_frame c_fuel fr_at]; rewrite Hfuel1; reflexivity).
      * trace_next
          ltac:(eapply (rule_enter _ _ _ _ _ _ _ _ _ _ _ Hfuel1);
                [reflexivity
                |cbn [b_phis phis_env fold_left lookup name_eqb term_eqb String.eqb Ascii.eqb Bool.eqb andb value_x word_at_class modulus];
                 reflexivity])
          ltac:(cbn [leak_of c_frame c_fuel fr_at]; rewrite (proj2 (Z.eqb_neq (fuel - 1) 0) Hfuel1); reflexivity).
        cbn [b_insts b_jump].
        apply run_trace_prefix_nil. intros k_rem _.
        replace (fuel - 1 - 1) with (fuel - 2) by lia.
        apply (IH (j + 1) (fuel - 2)); [lia | lia |].
        constructor; unfold ptr_shift_mod;
          [solve_lookup
          |solve_lookup
          |cbn [lookup]; repeat (first [rewrite lookup_put_same | rewrite lookup_put_other; [|reflexivity]]);
           rewrite Zmod_mod; reflexivity
          |eexists; solve_lookup].
Qed.

(** Loop-level simulation: at any public iteration `j`, two rebased executions
    with arbitrary secrets `s1` and `s2` emit the exact same plain [run_trace]
    under any policy [pol]. *)
Lemma rebased_loop_traces_equal pol buf m len s1 s2 steps j fuel e1 e2 :
  readable_slice m buf len ->
  0 <= j <= len ->
  rebased_loop_env e1 buf len j s1 ->
  rebased_loop_env e2 buf len j s2 ->
  run_trace pol rebased_ge steps (rebased_loop_cfg e1 m fuel) =
  run_trace pol rebased_ge steps (rebased_loop_cfg e2 m fuel).
Proof.
  intros Hsl Hj He1 He2.
  rewrite (rebased_loop_trace_eq pol buf m len s1 Hsl (Z.to_nat (len - j)) j fuel e1 steps ltac:(lia) ltac:(lia) He1).
  rewrite (rebased_loop_trace_eq pol buf m len s2 Hsl (Z.to_nat (len - j)) j fuel e2 steps ltac:(lia) ltac:(lia) He2).
  reflexivity.
Qed.

(** Single-run characterization from function entry: for any secret offset `s`,
    [rebased_scan_fn] emits the secret-independent reference trace
    [rebased_scan_trace]. *)
Lemma rebased_scan_trace_eq pol buf m len s fuel steps :
  readable_slice m buf len ->
  run_trace pol rebased_ge steps cfg{ (rebased_entry buf len s); mem: m; fuel: fuel } =
    Some (rebased_scan_trace pol buf len fuel steps).
Proof.
  intros Hsl.
  pose proof Hsl as [_ Hb Hlen Hblim _].
  assert (Hb_mod : ptr_addr buf mod 2 ^ 64 = ptr_addr buf) by (apply Z.mod_small; lia).
  assert (Hlen_mod : len mod 2 ^ 64 = len) by (apply Z.mod_small; lia).
  unfold rebased_scan_trace.
  destruct (Z.eqb_spec fuel 0) as [-> | Hfuel].
  - trace_done ltac:(apply rule_out_of_fuel) ltac:(reflexivity).
  - trace_next
      ltac:(eapply (rule_enter _ _ _ _ _ _ _ _ _ _ _ Hfuel); reflexivity)
      ltac:(cbn [leak_of rebased_entry c_frame c_fuel fr_at]; rewrite (proj2 (Z.eqb_neq fuel 0) Hfuel); reflexivity).
    cbn [b_insts b_jump].
    trace_next
      ltac:(apply (rule_flight _ _ _ _ _ _ _ _ _ _ _ _ _ _
              [WInt (ptr_addr buf); WInt (s mod 2 ^ 64)] ((ptr_addr buf + s) mod 2 ^ 64) (ptr_cap buf));
            [cbn [map_option flight_arg_x value_x lookup name_eqb term_eqb String.eqb Ascii.eqb Bool.eqb andb word_at_class modulus ptr_addr];
             rewrite Hb_mod; reflexivity
            |cbn [alu cond_bit modulus]; rewrite Zplus_mod_idemp_r; reflexivity
            |cbn [flight_cap value_x lookup name_eqb term_eqb String.eqb Ascii.eqb Bool.eqb andb]; reflexivity])
      ltac:(reflexivity).
    trace_next
      ltac:(apply (rule_let _ _ _ _ _ _ _ _ _ _ _ _ _ _ [L; L]
              [WInt len; WInt (s mod 2 ^ 64)] (WInt ((len - s) mod 2 ^ 64)) m);
            try reflexivity;
            [cbn [map2_option value_x]; repeat (first [rewrite lookup_put_same | rewrite lookup_put_other; [|reflexivity]]);
             cbn [lookup name_eqb term_eqb String.eqb Ascii.eqb Bool.eqb andb word_at_class modulus];
             rewrite Hlen_mod; reflexivity
            |unfold op_res, op_res_int; cbn [additive_res alu cond_bit modulus]; rewrite Zminus_mod_idemp_r; reflexivity])
      ltac:(reflexivity).
    trace_next
      ltac:(apply (rule_let _ _ _ _ _ _ _ _ _ _ _ _ _ _ [L; L]
              [WInt 0; WInt (s mod 2 ^ 64)] (WInt ((0 - s) mod 2 ^ 64)) m);
            try reflexivity;
            unfold op_res, op_res_int; cbn [additive_res alu cond_bit modulus]; rewrite Zminus_mod_idemp_r; reflexivity)
      ltac:(reflexivity).
    trace_next ltac:(apply rule_goto) ltac:(reflexivity).
    cbn [edge_label].
    apply run_trace_prefix_nil. intros n _.
    destruct (Z.eqb_spec (fuel - 1) 0) as [Hfuel1 | Hfuel1].
    + trace_done
        ltac:(rewrite Hfuel1; apply rule_out_of_fuel)
        ltac:(cbn [leak_of c_frame c_fuel fr_at]; rewrite Hfuel1; reflexivity).
    + trace_next
        ltac:(eapply (rule_enter _ _ _ _ _ _ _ _ _ _ _ Hfuel1);
              [reflexivity
              |cbn [b_phis phis_env fold_left lookup name_eqb term_eqb String.eqb Ascii.eqb Bool.eqb andb value_x word_at_class modulus];
               reflexivity])
        ltac:(cbn [leak_of c_frame c_fuel fr_at]; rewrite (proj2 (Z.eqb_neq (fuel - 1) 0) Hfuel1); reflexivity).
      cbn [b_insts b_jump].
      apply run_trace_prefix_nil. intros k_rem _.
      replace (fuel - 1 - 1) with (fuel - 2) by lia.
      apply (rebased_loop_trace_eq pol buf m len s Hsl (Z.to_nat len) 0 (fuel - 2)); [lia | lia |].
      constructor; unfold ptr_shift_mod;
        [solve_lookup
        |solve_lookup
        |cbn [lookup]; repeat (first [rewrite lookup_put_same | rewrite lookup_put_other; [|reflexivity]]);
         rewrite Zmod_mod; reflexivity
        |eexists; solve_lookup].
Qed.

(** Full two-run constant-time theorem for [rebased_scan_fn]: for any policy
    [pol], any readable buffer slice of length `len`, and any two secret
    offsets `s1` and `s2`, both executions emit the identical plain operational
    trace. Together with [rebased_scan_taint_rejected] and
    [rebased_scan_taint_rejects], this formally separates single-run taint
    from two-run constant-time noninterference. *)
Theorem rebased_scan_two_run_constant_time pol buf m len s1 s2 fuel steps :
  readable_slice m buf len ->
  run_trace pol rebased_ge steps cfg{ (rebased_entry buf len s1); mem: m; fuel: fuel } =
  run_trace pol rebased_ge steps cfg{ (rebased_entry buf len s2); mem: m; fuel: fuel }.
Proof.
  intros Hsl.
  rewrite (rebased_scan_trace_eq pol buf m len s1 fuel steps Hsl).
  rewrite (rebased_scan_trace_eq pol buf m len s2 fuel steps Hsl).
  reflexivity.
Qed.

(** ## Concrete runtime instantiation

    Instantiating [CtTableScan] with the reference interpreter runtime
    [InterpRuntime] lets Rocq check the assumptions of the safety and
    constant-time theorems for that runtime. *)

Module InterpCtTableScan := CtTableScan InterpRuntime.
Print Assumptions cttable_valid.
Print Assumptions scan_ct_taint_ok.
Print Assumptions scan_indexed_taint_rejected.
Print Assumptions InterpCtTableScan.scan_ct_plain_safe.
Print Assumptions InterpCtTableScan.scan_ct_safe.
Print Assumptions InterpCtTableScan.scan_ct_constant_time.
Print Assumptions rebased_scan_taint_rejected.
Print Assumptions rebased_scan_two_run_constant_time.
