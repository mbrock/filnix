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
  Run Machine Panics StepRules Pieces PoisonModel PoisonLogic TaintCheck IRNotation
  CtTableScanCode CtTableScanNames.

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
  mkFrame fn_scan_ct
    [(‹tbl›, WPtr tbl);
     (‹start›, WInt start);
     (‹skip›, WInt skip);
     (‹win›, WInt win);
     (‹len›, WInt len);
     (‹buf›, WPtr buf)]
    [] None (Enter (TAtom "start") None).

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
    (mkConfig (scan_ct_entry buf tbl len win skip1 start1) [] m1 fuel)
    (mkConfig (scan_ct_entry buf tbl len win skip2 start2) [] m2 fuel)
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
      (mkConfig (scan_ct_entry buf tbl len win skip start) [] m fuel)
| sci_outer e j i_val res_val start_val m fuel :
    m_regions m = m_regions m0 ->
    0 <= j <= win + 16 ->
    lookup ‹win› e = Some (WInt win) ->
    lookup ‹start› e = Some (WInt start_val) ->
    lookup ‹tbl› e = Some (WPtr tbl) ->
    lookup ‹p› e = Some (WPtr (mkPtr (ptr_addr buf + (len - win - 16)) (ptr_cap buf))) ->
    lookup ‹j› e = Some (WInt j) ->
    lookup ‹i› e = Some (WInt i_val) ->
    lookup ‹res› e = Some (WInt res_val) ->
    scan_ct_inv buf tbl len win m0
      (mkConfig (mkFrame fn_scan_ct e [] None
        (Exec (TAtom "L28")
          [Let (TAtom "v34") L Add [Tmp ‹win›; Const 16];
           Let (TAtom "v35") W (Cmp Ult L) [Tmp ‹j›; Tmp (TAtom "v34")]]
          (JBranch (Tmp (TAtom "v35")) (To (TAtom "L29")) (To (TAtom "L31")))))
        [] m fuel)
| sci_inner e j k i_val res_val start_val c_val inr_val mask_val exp_val m fuel :
    m_regions m = m_regions m0 ->
    0 <= j < win + 16 ->
    0 <= k <= 16 ->
    lookup ‹win› e = Some (WInt win) ->
    lookup ‹start› e = Some (WInt start_val) ->
    lookup ‹tbl› e = Some (WPtr tbl) ->
    lookup ‹p› e = Some (WPtr (mkPtr (ptr_addr buf + (len - win - 16)) (ptr_cap buf))) ->
    lookup ‹j› e = Some (WInt j) ->
    lookup ‹i› e = Some (WInt i_val) ->
    lookup ‹res› e = Some (WInt res_val) ->
    lookup ‹c› e = Some (WInt c_val) ->
    lookup ‹in_range› e = Some (WInt inr_val) ->
    lookup ‹mask› e = Some (WInt mask_val) ->
    lookup ‹k› e = Some (WInt k) ->
    lookup ‹expected› e = Some (WInt exp_val) ->
    scan_ct_inv buf tbl len win m0
      (mkConfig (mkFrame fn_scan_ct e [] None
        (Exec (TAtom "L55")
          [Let ‹k<u16› W (Cmp Ult L) [Tmp ‹k›; Const 16]]
          (JBranch (Tmp ‹k<u16›) (To (TAtom "L56")) (To (TAtom "L58")))))
        [] m fuel).

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
    |e j i_val res_val start_val m fuel Hreg Hj Hwin_e Hstart_e Htbl_e Hp_e Hj_e Hi_e Hres_e
    |e j k i_val res_val start_val c_val inr_val mask_val exp_val m fuel
       Hreg Hj Hk Hwin_e Hstart_e Htbl_e Hp_e Hj_e Hi_e Hres_e Hc_e Hinr_e Hmask_e Hk_e Hexp_e].
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
    eapply (sci_outer buf tbl len win m0 _ 0 0 0 start m);
      try assumption; try lia; solve_lookup.
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
      eapply (sci_inner buf tbl len win m0 _ j 0 i_val res_val start_val cv n49 n52 0 m);
        try assumption; try lia; solve_lookup.
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
      eapply (sci_inner buf tbl len win m0 _ j (k + 1) i_val res_val start_val c_val inr_val mask_val (n73 mod 2 ^ 32) m);
        try assumption; try lia; solve_lookup.
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
      eapply (sci_outer buf tbl len win m0 _ (j + 1) (n86 mod 2 ^ 64) (n82 mod 2 ^ 32) start_val m);
        try assumption; try lia; solve_lookup.
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
      (mkConfig (scan_ct_entry buf tbl len win skip1 start1) [] m1 fuel) s = Some tr /\
    PD.driver_trace pol_strict cttable_ge steps
      (mkConfig (scan_ct_entry buf tbl len win skip2 start2) [] m2 fuel) s = Some tr.
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
  mkFrame rebased_scan_fn
    [(TAtom "sec", WInt sec); (TAtom "len", WInt len); (TAtom "buf", WPtr buf)]
    [] None (Enter (TAtom "start") None).

Definition rebased_te (t_sec : taint) : tenv :=
  [(TAtom "sec", WTInt t_sec); (TAtom "len", WTInt taint_bot);
   (TAtom "buf", WTPtr taint_bot taint_bot)].

(** Single-run dynamic taint rejects [rebased_scan_fn] on both branch poison
    (at the loop exit test `k == lim`) and index poison (at `base + k`). *)
Theorem rebased_scan_taint_rejects :
  let m := scan_mem (fun k => k) sample_tbl 16 in
  prun pol_strict rebased_ge 10
    (mkConfig (rebased_entry scan_buf_ptr 4 17) [] m 50)
    (mkPState (rebased_te taint_branch) [] (fun _ => pb_clean) (fun _ => taint_bot)) =
    PTrap CannotBranch /\
  prun pol_erased rebased_ge 15
    (mkConfig (rebased_entry scan_buf_ptr 4 17) [] m 50)
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

Lemma run_trace_step_eq pol ge n c1 c2 c1' c2' :
  leak_of pol ge c1 = leak_of pol ge c2 ->
  Semantics.step ge c1 = Next c1' ->
  Semantics.step ge c2 = Next c2' ->
  run_trace pol ge n c1' = run_trace pol ge n c2' ->
  run_trace pol ge (S n) c1 = run_trace pol ge (S n) c2.
Proof.
  intros Hl Hs1 Hs2 Hrest. cbn [run_trace]. rewrite Hs1, Hs2, Hl, Hrest. reflexivity.
Qed.

Lemma run_trace_done_eq pol ge n c1 c2 o1 o2 :
  leak_of pol ge c1 = leak_of pol ge c2 ->
  Semantics.step ge c1 = Done o1 ->
  Semantics.step ge c2 = Done o2 ->
  run_trace pol ge (S n) c1 = run_trace pol ge (S n) c2.
Proof.
  intros Hl Hs1 Hs2. cbn [run_trace]. rewrite Hs1, Hs2, Hl. reflexivity.
Qed.

(** Loop-level simulation: at the start of any iteration `j`, two rebased
    executions with arbitrary secrets `s1` and `s2` emit the exact same plain
    [run_trace] under any policy [pol]. *)
Lemma rebased_loop_traces_equal pol buf m len s1 s2 :
  readable_slice m buf len ->
  forall steps j acc fuel e1 e2,
    0 <= j <= len ->
    lookup (TAtom "base") e1 = Some (WPtr (mkPtr ((ptr_addr buf + s1) mod 2 ^ 64) (ptr_cap buf))) ->
    lookup (TAtom "lim") e1 = Some (WInt ((len - s1) mod 2 ^ 64)) ->
    lookup (TAtom "k") e1 = Some (WInt ((j - s1) mod 2 ^ 64)) ->
    lookup (TAtom "acc") e1 = Some (WInt acc) ->
    lookup (TAtom "base") e2 = Some (WPtr (mkPtr ((ptr_addr buf + s2) mod 2 ^ 64) (ptr_cap buf))) ->
    lookup (TAtom "lim") e2 = Some (WInt ((len - s2) mod 2 ^ 64)) ->
    lookup (TAtom "k") e2 = Some (WInt ((j - s2) mod 2 ^ 64)) ->
    lookup (TAtom "acc") e2 = Some (WInt acc) ->
    run_trace pol rebased_ge steps
      (mkConfig (mkFrame rebased_scan_fn e1 [] None
        (Exec (TAtom "loop")
          [Let (TAtom "done") W (Cmp Eq L) [Tmp (TAtom "k"); Tmp (TAtom "lim")]]
          (JBranch (Tmp (TAtom "done")) (To (TAtom "exit")) (To (TAtom "body")))))
        [] m fuel) =
    run_trace pol rebased_ge steps
      (mkConfig (mkFrame rebased_scan_fn e2 [] None
        (Exec (TAtom "loop")
          [Let (TAtom "done") W (Cmp Eq L) [Tmp (TAtom "k"); Tmp (TAtom "lim")]]
          (JBranch (Tmp (TAtom "done")) (To (TAtom "exit")) (To (TAtom "body")))))
        [] m fuel).
Proof.
  intros Hsl steps.
  pose proof Hsl as [_ Hb Hlen Hblim _].
  induction steps as [steps IH] using lt_wf_ind.
  intros j acc fuel e1 e2 Hj Hbase1 Hlim1 Hk1 Hacc1 Hbase2 Hlim2 Hk2 Hacc2.
  destruct steps as [|n1]; [reflexivity|].
  assert (Hcmp1 : ((j - s1) mod 2 ^ 64 =? (len - s1) mod 2 ^ 64) = (j =? len))
    by (apply mod64_cancel_eq; lia).
  assert (Hcmp2 : ((j - s2) mod 2 ^ 64 =? (len - s2) mod 2 ^ 64) = (j =? len))
    by (apply mod64_cancel_eq; lia).
  assert (Hmod_k1 : ((j - s1) mod 2 ^ 64) mod 2 ^ 64 = (j - s1) mod 2 ^ 64) by apply Zmod_mod.
  assert (Hmod_l1 : ((len - s1) mod 2 ^ 64) mod 2 ^ 64 = (len - s1) mod 2 ^ 64) by apply Zmod_mod.
  assert (Hmod_k2 : ((j - s2) mod 2 ^ 64) mod 2 ^ 64 = (j - s2) mod 2 ^ 64) by apply Zmod_mod.
  assert (Hmod_l2 : ((len - s2) mod 2 ^ 64) mod 2 ^ 64 = (len - s2) mod 2 ^ 64) by apply Zmod_mod.
  set (done_val := if j =? len then 1 else 0).
  eapply run_trace_step_eq.
  - reflexivity.
  - apply (rule_let _ _ _ _ _ _ _ _ _ _ _ _ _ _ [L; L]
      [WInt ((j - s1) mod 2 ^ 64); WInt ((len - s1) mod 2 ^ 64)] (WInt done_val) m);
      try reflexivity.
    + cbn [map2_option value_x]; rewrite Hk1, Hlim1; cbn [word_at_class modulus];
        rewrite Hmod_k1, Hmod_l1; reflexivity.
    + unfold op_res, op_res_int; cbn; rewrite Hcmp1; reflexivity.
  - apply (rule_let _ _ _ _ _ _ _ _ _ _ _ _ _ _ [L; L]
      [WInt ((j - s2) mod 2 ^ 64); WInt ((len - s2) mod 2 ^ 64)] (WInt done_val) m);
      try reflexivity.
    + cbn [map2_option value_x]; rewrite Hk2, Hlim2; cbn [word_at_class modulus];
        rewrite Hmod_k2, Hmod_l2; reflexivity.
    + unfold op_res, op_res_int; cbn; rewrite Hcmp2; reflexivity.
  - destruct n1 as [|n2]; [reflexivity|].
    destruct (Z.eqb_spec j len) as [-> | Hj_ne]; subst done_val; cbn [Z.eqb] in *.
    + eapply run_trace_step_eq.
      * cbn [leak_of c_frame fr_at fr_env value_x]; repeat rewrite lookup_put_same; reflexivity.
      * apply (rule_branch _ _ _ _ _ _ _ _ _ _ _ 1).
        cbn [value_x]; rewrite lookup_put_same; reflexivity.
      * apply (rule_branch _ _ _ _ _ _ _ _ _ _ _ 1).
        cbn [value_x]; rewrite lookup_put_same; reflexivity.
      * cbn [edge_label Z.eqb].
        destruct n2 as [|n3]; [reflexivity|].
        destruct (Z.eqb_spec fuel 0) as [-> | Hfuel].
        { eapply run_trace_done_eq; [reflexivity | apply rule_out_of_fuel | apply rule_out_of_fuel]. }
        eapply run_trace_step_eq; [reflexivity
          | eapply (rule_enter _ _ _ _ _ _ _ _ _ (mkBlock (TAtom "exit") [] [] (JRet (Tmp (TAtom "acc")))) _ Hfuel); reflexivity
          | eapply (rule_enter _ _ _ _ _ _ _ _ _ (mkBlock (TAtom "exit") [] [] (JRet (Tmp (TAtom "acc")))) _ Hfuel); reflexivity |].
        cbn [b_insts b_jump].
        destruct n3 as [|n4]; [reflexivity|].
        eapply run_trace_done_eq; [reflexivity | |].
        -- rewrite (rule_ret _ _ _ _ _ _ _ _ _ W (WInt (acc mod 2 ^ 32)));
             [apply (rule_return_top _ _ _ _ m); reflexivity
             |reflexivity
             |cbn [value_x]; solve_lookup].
        -- rewrite (rule_ret _ _ _ _ _ _ _ _ _ W (WInt (acc mod 2 ^ 32)));
             [apply (rule_return_top _ _ _ _ m); reflexivity
             |reflexivity
             |cbn [value_x]; solve_lookup].
    + eapply run_trace_step_eq.
      * cbn [leak_of c_frame fr_at fr_env value_x]; repeat rewrite lookup_put_same; reflexivity.
      * apply (rule_branch _ _ _ _ _ _ _ _ _ _ _ 0).
        cbn [value_x]; rewrite lookup_put_same; reflexivity.
      * apply (rule_branch _ _ _ _ _ _ _ _ _ _ _ 0).
        cbn [value_x]; rewrite lookup_put_same; reflexivity.
      * cbn [edge_label Z.eqb].
        destruct n2 as [|n3]; [reflexivity|].
        destruct (Z.eqb_spec fuel 0) as [-> | Hfuel].
        { eapply run_trace_done_eq; [reflexivity | apply rule_out_of_fuel | apply rule_out_of_fuel]. }
        eapply run_trace_step_eq; [reflexivity
          | eapply (rule_enter _ _ _ _ _ _ _ _ _ _ _ Hfuel); reflexivity
          | eapply (rule_enter _ _ _ _ _ _ _ _ _ _ _ Hfuel); reflexivity |].
        cbn [b_insts b_jump].
        destruct n3 as [|n4]; [reflexivity|].
        assert (Hbj : (ptr_addr buf + j) mod 2 ^ 64 = ptr_addr buf + j) by (apply Z.mod_small; lia).
        assert (Hadd1 : (((ptr_addr buf + s1) mod 2 ^ 64) + ((j - s1) mod 2 ^ 64)) mod 2 ^ 64 = ptr_addr buf + j)
          by (rewrite mod64_cancel_add; exact Hbj).
        assert (Hadd2 : (((ptr_addr buf + s2) mod 2 ^ 64) + ((j - s2) mod 2 ^ 64)) mod 2 ^ 64 = ptr_addr buf + j)
          by (rewrite mod64_cancel_add; exact Hbj).
        assert (Hbs1 : ((ptr_addr buf + s1) mod 2 ^ 64) mod 2 ^ 64 = (ptr_addr buf + s1) mod 2 ^ 64) by apply Zmod_mod.
        assert (Hbs2 : ((ptr_addr buf + s2) mod 2 ^ 64) mod 2 ^ 64 = (ptr_addr buf + s2) mod 2 ^ 64) by apply Zmod_mod.
        eapply run_trace_step_eq; [reflexivity | | |].
        -- apply (rule_flight _ _ _ _ _ _ _ _ _ _ _ _ _ _
             [WInt ((ptr_addr buf + s1) mod 2 ^ 64); WInt ((j - s1) mod 2 ^ 64)] (ptr_addr buf + j) (ptr_cap buf)).
           ++ cbn [map_option flight_arg_x value_x];
              repeat (rewrite lookup_put_other; [|reflexivity]);
              rewrite Hbase1, Hk1;
              cbn [word_at_class modulus ptr_addr]; rewrite Hbs1, Hmod_k1; reflexivity.
           ++ cbn [alu cond_bit modulus]; rewrite Hadd1; reflexivity.
           ++ cbn [flight_cap value_x]; repeat (rewrite lookup_put_other; [|reflexivity]); rewrite Hbase1; reflexivity.
        -- apply (rule_flight _ _ _ _ _ _ _ _ _ _ _ _ _ _
             [WInt ((ptr_addr buf + s2) mod 2 ^ 64); WInt ((j - s2) mod 2 ^ 64)] (ptr_addr buf + j) (ptr_cap buf)).
           ++ cbn [map_option flight_arg_x value_x];
              repeat (rewrite lookup_put_other; [|reflexivity]);
              rewrite Hbase2, Hk2;
              cbn [word_at_class modulus ptr_addr]; rewrite Hbs2, Hmod_k2; reflexivity.
           ++ cbn [alu cond_bit modulus]; rewrite Hadd2; reflexivity.
           ++ cbn [flight_cap value_x]; repeat (rewrite lookup_put_other; [|reflexivity]); rewrite Hbase2; reflexivity.
        -- destruct n4 as [|n5]; [reflexivity|].
           pose proof (readable_slice_byte_access m buf len j Hsl ltac:(lia)) as Hchk_ok.
           eapply run_trace_step_eq.
           ++ cbn [leak_of c_frame fr_at fr_env value_x]; repeat rewrite lookup_put_same; reflexivity.
           ++ apply (rule_let _ _ _ _ _ _ _ _ _ _ _ _ _ _ [P]
                [WPtr (mkPtr (ptr_addr buf + j) (ptr_cap buf))]
                (WPtr (mkPtr (ptr_addr buf + j) (ptr_cap buf))) m);
                try reflexivity;
                cbn [op_res op_res_int ptr_addr ptr_cap]; change (1 - 0) with 1; rewrite Hchk_ok; reflexivity.
           ++ apply (rule_let _ _ _ _ _ _ _ _ _ _ _ _ _ _ [P]
                [WPtr (mkPtr (ptr_addr buf + j) (ptr_cap buf))]
                (WPtr (mkPtr (ptr_addr buf + j) (ptr_cap buf))) m);
                try reflexivity;
                cbn [op_res op_res_int ptr_addr ptr_cap]; change (1 - 0) with 1; rewrite Hchk_ok; reflexivity.
           ++ destruct n5 as [|n6]; [reflexivity|].
              set (bv := (m_bytes m (ptr_addr buf + j) mod 256) mod 2 ^ 32).
              pose proof (readable_slice_load_byte m buf len j Hsl ltac:(lia)) as Hload_ok.
              eapply run_trace_step_eq.
              ** cbn [leak_of c_frame fr_at fr_env value_x]; repeat rewrite lookup_put_same; reflexivity.
              ** apply (rule_let _ _ _ _ _ _ _ _ _ _ _ _ _ _ [A]
                   [WPtr (mkPtr (ptr_addr buf + j) (ptr_cap buf))] (WInt bv) m);
                   try reflexivity;
                   cbn [op_res op_res_int ptr_addr ptr_cap]; rewrite Hload_ok; reflexivity.
              ** apply (rule_let _ _ _ _ _ _ _ _ _ _ _ _ _ _ [A]
                   [WPtr (mkPtr (ptr_addr buf + j) (ptr_cap buf))] (WInt bv) m);
                   try reflexivity;
                   cbn [op_res op_res_int ptr_addr ptr_cap]; rewrite Hload_ok; reflexivity.
              ** destruct n6 as [|n7]; [reflexivity|].
                 set (acc' := Z.lxor (acc mod 2 ^ 32) (bv mod 2 ^ 32)).
                 eapply run_trace_step_eq; [reflexivity | | |].
                 --- apply (rule_let _ _ _ _ _ _ _ _ _ _ _ _ _ _ [W; W]
                       [WInt (acc mod 2 ^ 32); WInt (bv mod 2 ^ 32)] (WInt acc') m);
                       try reflexivity;
                       cbn [map2_option value_x];
                       repeat (first [rewrite lookup_put_same | rewrite lookup_put_other; [|reflexivity]]);
                       rewrite Hacc1; reflexivity.
                 --- apply (rule_let _ _ _ _ _ _ _ _ _ _ _ _ _ _ [W; W]
                       [WInt (acc mod 2 ^ 32); WInt (bv mod 2 ^ 32)] (WInt acc') m);
                       try reflexivity;
                       cbn [map2_option value_x];
                       repeat (first [rewrite lookup_put_same | rewrite lookup_put_other; [|reflexivity]]);
                       rewrite Hacc2; reflexivity.
                 --- destruct n7 as [|n8]; [reflexivity|].
                     eapply run_trace_step_eq; [reflexivity | | |].
                     +++ apply (rule_let _ _ _ _ _ _ _ _ _ _ _ _ _ _ [L; L]
                           [WInt ((j - s1) mod 2 ^ 64); WInt 1] (WInt (((j + 1) - s1) mod 2 ^ 64)) m);
                           try reflexivity.
                         *** cbn [map2_option value_x];
                             repeat (rewrite lookup_put_other; [|reflexivity]);
                             rewrite Hk1; cbn [word_at_class modulus]; rewrite Hmod_k1; reflexivity.
                         *** unfold op_res, op_res_int; cbn [additive_res alu cond_bit modulus];
                             rewrite mod64_step_k; reflexivity.
                     +++ apply (rule_let _ _ _ _ _ _ _ _ _ _ _ _ _ _ [L; L]
                           [WInt ((j - s2) mod 2 ^ 64); WInt 1] (WInt (((j + 1) - s2) mod 2 ^ 64)) m);
                           try reflexivity.
                         *** cbn [map2_option value_x];
                             repeat (rewrite lookup_put_other; [|reflexivity]);
                             rewrite Hk2; cbn [word_at_class modulus]; rewrite Hmod_k2; reflexivity.
                         *** unfold op_res, op_res_int; cbn [additive_res alu cond_bit modulus];
                             rewrite mod64_step_k; reflexivity.
                     +++ destruct n8 as [|n9]; [reflexivity|].
                         eapply run_trace_step_eq; [reflexivity | apply rule_goto | apply rule_goto |].
                         cbn [edge_label].
                         destruct n9 as [|n10]; [reflexivity|].
                         destruct (Z.eqb_spec (fuel - 1) 0) as [Hfuel0 | Hfuel'].
                         *** rewrite Hfuel0.
                             eapply run_trace_done_eq; [reflexivity | apply rule_out_of_fuel | apply rule_out_of_fuel].
                         *** eapply run_trace_step_eq; [reflexivity
                               | eapply (rule_enter _ _ _ _ _ _ _ _ _ _ _ Hfuel');
                                 [reflexivity
                                 |cbn [b_phis phis_env fold_left lookup name_eqb term_eqb String.eqb Ascii.eqb Bool.eqb andb value_x word_at_class modulus];
                                   reflexivity]
                               | eapply (rule_enter _ _ _ _ _ _ _ _ _ _ _ Hfuel');
                                 [reflexivity
                                 |cbn [b_phis phis_env fold_left lookup name_eqb term_eqb String.eqb Ascii.eqb Bool.eqb andb value_x word_at_class modulus];
                                   reflexivity] |].
                             cbn [b_insts b_jump].
                             eapply (IH n10 ltac:(lia) (j + 1) (acc' mod 2 ^ 32) (fuel - 1 - 1));
                               first
                                 [ lia
                                 | repeat (first [rewrite lookup_put_same | rewrite lookup_put_other; [|reflexivity]]);
                                   try rewrite Hbase1; try rewrite Hlim1; try rewrite Hbase2; try rewrite Hlim2;
                                   rewrite ?Zmod_mod; reflexivity ].
Qed.

(** Full two-run constant-time theorem for [rebased_scan_fn]: for any policy
    [pol], any readable buffer slice of length `len`, and any two secret
    offsets `s1` and `s2`, both executions emit the identical plain operational
    trace. Together with [rebased_scan_taint_rejected] and
    [rebased_scan_taint_rejects], this formally separates single-run taint
    from two-run constant-time noninterference. *)
Theorem rebased_scan_two_run_constant_time pol buf m len s1 s2 fuel steps :
  readable_slice m buf len ->
  run_trace pol rebased_ge steps (mkConfig (rebased_entry buf len s1) [] m fuel) =
  run_trace pol rebased_ge steps (mkConfig (rebased_entry buf len s2) [] m fuel).
Proof.
  intros Hsl.
  pose proof Hsl as [_ Hb Hlen Hblim _].
  assert (Hb_mod : ptr_addr buf mod 2 ^ 64 = ptr_addr buf) by (apply Z.mod_small; lia).
  assert (Hlen_mod : len mod 2 ^ 64 = len) by (apply Z.mod_small; lia).
  destruct steps as [|n1]; [reflexivity|].
  destruct (Z.eqb_spec fuel 0) as [-> | Hfuel1].
  { eapply run_trace_done_eq; [reflexivity | apply rule_out_of_fuel | apply rule_out_of_fuel]. }
  eapply run_trace_step_eq; [reflexivity
    | eapply (rule_enter _ _ _ _ _ _ _ _ _ _ _ Hfuel1); reflexivity
    | eapply (rule_enter _ _ _ _ _ _ _ _ _ _ _ Hfuel1); reflexivity |].
  cbn [b_insts b_jump].
  destruct n1 as [|n2]; [reflexivity|].
  eapply run_trace_step_eq; [reflexivity | | |].
  - apply (rule_flight _ _ _ _ _ _ _ _ _ _ _ _ _ _
      [WInt (ptr_addr buf); WInt (s1 mod 2 ^ 64)] ((ptr_addr buf + s1) mod 2 ^ 64) (ptr_cap buf));
      [cbn [map_option flight_arg_x value_x lookup name_eqb term_eqb String.eqb Ascii.eqb Bool.eqb andb word_at_class modulus ptr_addr];
        rewrite Hb_mod; reflexivity
      |cbn [alu cond_bit modulus]; rewrite Zplus_mod_idemp_r; reflexivity
      |cbn [flight_cap value_x lookup name_eqb term_eqb String.eqb Ascii.eqb Bool.eqb andb]; reflexivity].
  - apply (rule_flight _ _ _ _ _ _ _ _ _ _ _ _ _ _
      [WInt (ptr_addr buf); WInt (s2 mod 2 ^ 64)] ((ptr_addr buf + s2) mod 2 ^ 64) (ptr_cap buf));
      [cbn [map_option flight_arg_x value_x lookup name_eqb term_eqb String.eqb Ascii.eqb Bool.eqb andb word_at_class modulus ptr_addr];
        rewrite Hb_mod; reflexivity
      |cbn [alu cond_bit modulus]; rewrite Zplus_mod_idemp_r; reflexivity
      |cbn [flight_cap value_x lookup name_eqb term_eqb String.eqb Ascii.eqb Bool.eqb andb]; reflexivity].
  - destruct n2 as [|n3]; [reflexivity|].
    eapply run_trace_step_eq; [reflexivity | | |].
    + apply (rule_let _ _ _ _ _ _ _ _ _ _ _ _ _ _ [L; L]
        [WInt len; WInt (s1 mod 2 ^ 64)] (WInt ((len - s1) mod 2 ^ 64)) m);
        try reflexivity.
      * cbn [map2_option value_x];
        repeat (first [rewrite lookup_put_same | rewrite lookup_put_other; [|reflexivity]]);
        cbn [lookup name_eqb term_eqb String.eqb Ascii.eqb Bool.eqb andb word_at_class modulus];
        rewrite Hlen_mod; reflexivity.
      * unfold op_res, op_res_int; cbn [additive_res alu cond_bit modulus]; rewrite Zminus_mod_idemp_r; reflexivity.
    + apply (rule_let _ _ _ _ _ _ _ _ _ _ _ _ _ _ [L; L]
        [WInt len; WInt (s2 mod 2 ^ 64)] (WInt ((len - s2) mod 2 ^ 64)) m);
        try reflexivity.
      * cbn [map2_option value_x];
        repeat (first [rewrite lookup_put_same | rewrite lookup_put_other; [|reflexivity]]);
        cbn [lookup name_eqb term_eqb String.eqb Ascii.eqb Bool.eqb andb word_at_class modulus];
        rewrite Hlen_mod; reflexivity.
      * unfold op_res, op_res_int; cbn [additive_res alu cond_bit modulus]; rewrite Zminus_mod_idemp_r; reflexivity.
    + destruct n3 as [|n4]; [reflexivity|].
      eapply run_trace_step_eq; [reflexivity | | |].
      * apply (rule_let _ _ _ _ _ _ _ _ _ _ _ _ _ _ [L; L]
          [WInt 0; WInt (s1 mod 2 ^ 64)] (WInt ((0 - s1) mod 2 ^ 64)) m);
          try reflexivity;
          unfold op_res, op_res_int; cbn [additive_res alu cond_bit modulus];
          rewrite Zminus_mod_idemp_r; reflexivity.
      * apply (rule_let _ _ _ _ _ _ _ _ _ _ _ _ _ _ [L; L]
          [WInt 0; WInt (s2 mod 2 ^ 64)] (WInt ((0 - s2) mod 2 ^ 64)) m);
          try reflexivity;
          unfold op_res, op_res_int; cbn [additive_res alu cond_bit modulus];
          rewrite Zminus_mod_idemp_r; reflexivity.
      * destruct n4 as [|n5]; [reflexivity|].
        eapply run_trace_step_eq; [reflexivity | apply rule_goto | apply rule_goto |].
        cbn [edge_label].
        destruct n5 as [|n6]; [reflexivity|].
        destruct (Z.eqb_spec (fuel - 1) 0) as [Hfuel0 | Hfuel2].
        { rewrite Hfuel0. eapply run_trace_done_eq; [reflexivity | apply rule_out_of_fuel | apply rule_out_of_fuel]. }
        eapply run_trace_step_eq; [reflexivity
          | eapply (rule_enter _ _ _ _ _ _ _ _ _ _ _ Hfuel2);
            [reflexivity
            |cbn [b_phis phis_env fold_left lookup name_eqb term_eqb String.eqb Ascii.eqb Bool.eqb andb value_x word_at_class modulus];
             reflexivity]
          | eapply (rule_enter _ _ _ _ _ _ _ _ _ _ _ Hfuel2);
            [reflexivity
            |cbn [b_phis phis_env fold_left lookup name_eqb term_eqb String.eqb Ascii.eqb Bool.eqb andb value_x word_at_class modulus];
             reflexivity] |].
        cbn [b_insts b_jump].
        eapply (rebased_loop_traces_equal pol buf m len s1 s2 Hsl
                  n6 0 0 (fuel - 1 - 1));
          first
            [ lia
            | repeat (first [rewrite lookup_put_same | rewrite lookup_put_other; [|reflexivity]]);
              cbn [lookup name_eqb term_eqb String.eqb Ascii.eqb Bool.eqb andb];
              rewrite ?Zmod_mod; reflexivity ].
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
