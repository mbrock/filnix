(** Constant-time algorithms often scan a public tail window of a buffer and
    compare a secret sub-window against a small fixed table. When the loop
    computes its window pointer through a cancelled secret offset and then
    indexes the table by a secret counter, two distinct questions arise: does
    the compiler eliminate the cancelled secret offset, and how does the
    remaining secret table index interact with Fil-C capability checks and
    two-run constant-time noninterference?

    This module formalizes both a secret-indexed scanner (`scan_indexed`) and
    an index-free constant-time replacement (`scan_ct`) directly on the checked
    IR emitted by `nanofil -O` from `ct_table_scan.c` and rendered in
    [IRNotation] with C source-hint temporary names from [CtTableScanNames].
    First, we show that additive cancellation in `simplify.pl` keeps the window
    pointer public even though the C source computes
    `buf += skip; len -= skip; p = buf + len - win - 16`. Second, we separate
    three effects of the secret index `tbl[i]`: Fil-C's bounds check traps with
    `CannotBranch` under `pol_strict` even when the table has slack, erasing
    the check still trips `CannotIndex` and produces distinct plain operational
    traces, and an exact 16-byte table traps with `OutOfBounds` when `i`
    reaches 16. Third, we prove in [[separation-logic]] that `scan_ct` is
    memory-safe on an exact 16-byte table and two-run constant-time for every
    public window length and every secret input. Finally, we include a minimal
    rebased loop (`rebased_scan_fn`) separating single-run dynamic taint from
    two-run operational noninterference. *)

From Stdlib Require Import String ZArith List Bool Lia.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy.
From iris.base_logic.lib Require Import gen_heap.
From Nanofil Require Import Term Maps Syntax Values Validate Memory Runtime Ops Semantics
  Run Machine Panics StepRules Pieces Heap Language Logic PoisonModel PoisonLogic
  CtTableScanCode CtTableScanNames.

Import ListNotations.
Import CtTableScanNames.fn_scan_ct.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.

(** ## Validated checked IR

    Every theorem about `scan_indexed` and `scan_ct` operates directly on the
    typed IR functions emitted by `nanofil -O` in [CtTableScanCode], with
    source-hint C names from [CtTableScanNames] naming the SSA temporaries.
    Campaign 1's [[validator]] accepts both functions without hand-transcribed
    IR or runtime decoding. *)

(** Campaign 1's [[validator]] accepts both `scan_indexed` and `scan_ct`. *)
Theorem cttable_valid : valid cttable_module = Some true.
Proof. vm_compute. reflexivity. Qed.

(** Global environment containing both compiled functions. *)
Definition cttable_ge : genv := mkGenv cttable_module [] free_res.

(** ## Concrete forensic checks on `scan_indexed`

    Before proving universal theorems about `scan_ct`, we instantiate a small
    concrete heap to pin down the exact failure modes of `scan_indexed`. These
    computational proofs check the compiled IR directly through [prun] and
    [run_trace]. *)

(** Fixed base addresses and read-only capability pointers for concrete runs. *)
Definition scan_buf_base : Z := 131072.
Definition scan_tbl_base : Z := 131328.

Definition scan_buf_ptr : ptr := mkPtr scan_buf_base (Ro scan_buf_base).
Definition scan_tbl_ptr : ptr := mkPtr scan_tbl_base (Ro scan_tbl_base).

(** Deterministic sample table bytes `tbl[0..15]`. *)
Definition sample_tbl (k : Z) : Z := (17 * k + 5) mod 256.

(** Construct a 24-byte buffer `buf` containing `sample_tbl` at offset
    `4 + start` inside the 20-byte tail window `buf[4..23]` (`win = 4`). *)
Definition matching_buf_byte (start : Z) (idx : Z) : Z :=
  let j := idx - 4 in
  if (start <=? j) && (j <? start + 16)
  then sample_tbl (j - start)
  else (3 * idx + 1) mod 256.

(** Memory containing a 24-byte buffer at [scan_buf_base] and a `tbl_size`-byte
    table at [scan_tbl_base]. *)
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

(** Entry frame calling `f` with public `len` and `win` and secret `skip` and `start`. *)
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
    (tbl_size len win skip start : Z) (fuel : nat) : config :=
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

(** When only `skip` and data bytes carry full poison (and `start` stays public),
    `scan_indexed` finishes cleanly under [pol_strict]: additive cancellation in
    `simplify.pl` folds `(buf + skip) + (len - skip)` back to `buf + len` so the
    window pointer `p` carries no poison. *)
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
    leakage events, the exact same `taint_branch` run completes without a
    branch fault because the bounds check is architecturally never taken. *)
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
      (scan_cfg fn_scan_ct buf_fn tbl_fn 16 24 4 skip start (Z.to_nat 1000))
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

(** ## Universal Iris proof of `scan_ct`

    Concrete runs test only fixed dimensions. Using [[separation-logic]] over
    the dual value and [[poison]] heaps, we verify `scan_ct` for every public
    `len` and `win` satisfying `win + 16 <= len`, arbitrary secret `skip` and
    `start`, arbitrary secret bytes in `buf[0..len-1]`, and an exact 16-byte
    secret table `tbl[0..15]`. *)

(** Entry frame binding all six parameters of `scan_ct`. *)
Definition scan_ct_entry (p_buf p_tbl : ptr) (len win skip start : Z) : frame :=
  mkFrame fn_scan_ct
    [(‹tbl›, WPtr p_tbl);
     (‹start›, WInt start);
     (‹skip›, WInt skip);
     (‹win›, WInt win);
     (‹len›, WInt len);
     (‹buf›, WPtr p_buf)]
    [] None (Enter (TAtom "start") None).

(** Entry taint environment: `skip` and `start` carry full poison while the
    buffer pointers and public window lengths stay unrestricted. *)
Definition scan_ct_te : tenv :=
  [(‹tbl›, WTPtr taint_bot taint_bot);
   (‹start›, WTInt taint_all);
   (‹skip›, WTInt taint_all);
   (‹win›, WTInt taint_bot);
   (‹len›, WTInt taint_bot);
   (‹buf›, WTPtr taint_bot taint_bot)].

(** Two calls to `scan_ct` with matching public pointers and lengths satisfy
    [ct_rel] whenever their memories differ only in poisoned bytes. *)
Lemma scan_ct_inputs_related p_buf p_tbl len win skip1 start1 skip2 start2 m1 m2 pm paux fuel :
  m_regions m1 = m_regions m2 ->
  (forall a, m_bytes m1 a <> m_bytes m2 a -> pb_taint (pm a) = taint_all) ->
  (forall a, m_aux m1 a <> m_aux m2 a -> paux a = taint_all) ->
  ct_rel
    (mkConfig (scan_ct_entry p_buf p_tbl len win skip1 start1) [] m1 fuel)
    (mkConfig (scan_ct_entry p_buf p_tbl len win skip2 start2) [] m2 fuel)
    (mkPState scan_ct_te [] pm paux).
Proof.
  intros Hreg Hbytes Haux.
  unfold ct_rel; cbn; repeat split; try assumption; try reflexivity.
  - intros x. unfold scan_ct_te. cbn [lookup]. unfold name_eqb.
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

Lemma lookup_put_neq {A : Type} (x y : name) (v : A) (m : list (name * A)) :
  x <> y -> lookup x (put y v m) = lookup x m.
Proof.
  intros Hne; rewrite lookup_put_name; unfold name_eqb.
  destruct (term_eqb x y) eqn:E; [exfalso; apply Hne; apply term_eqb_eq; exact E | reflexivity].
Qed.

(** Helper tactic resolving environment lookups through nested [put]s. *)
Local Ltac solve_lookup :=
  repeat (first
    [ rewrite lookup_put_same
    | rewrite lookup_put_other; [|reflexivity] ]);
  try match goal with
      | H : lookup ?x ?e = Some _ |- context [lookup ?x ?e] => rewrite H
      end;
  cbn [word_at_class modulus];
  repeat match goal with
      | H : ?a mod ?m = ?b |- context [?a mod ?m] => rewrite H
      end;
  first [ reflexivity | assumption ].

(** Predicates identifying integer scalar classes and total binary ops. *)
Definition int_classb (k : class) : bool :=
  match k with W | L => true | _ => false end.

Definition bin_int_opb (o : op) : bool :=
  match o with Add | Sub | Xor | And | Or | Sar | Shr => true | _ => false end.

(** Binary arithmetic operations on integer scalars always succeed. *)
Lemma alu_int_total_bin o k a b :
  bin_int_opb o = true -> int_classb k = true ->
  exists n, alu o k [WInt a; WInt b] = Some (WInt n).
Proof.
  intros Ho Hk.
  destruct o; try discriminate Ho; destruct k; try discriminate Hk;
    cbn [alu cond_bit modulus]; eexists; reflexivity.
Qed.

(** Joining any taint with [taint_all] yields [taint_all]. *)
Lemma taint_join_all_l t : taint_join taint_all t = taint_all.
Proof. destruct t; reflexivity. Qed.

Lemma taint_join_all_r t : taint_join t taint_all = taint_all.
Proof. destruct t; unfold taint_join, taint_all; cbn; rewrite !orb_true_r; reflexivity. Qed.

(** In-bounds indexing into a list succeeds. *)
Lemma nth_error_some_lt {A : Type} (xs : list A) (k : nat) :
  (k < length xs)%nat -> exists x, nth_error xs k = Some x.
Proof.
  intros Hlt. destruct (nth_error xs k) as [x|] eqn:E; [exists x; reflexivity|].
  apply nth_error_None in E. lia.
Qed.

(** Indexing into [replicate] returns the replicated element. *)
Lemma nth_error_replicate_some {A : Type} (n : nat) (x : A) (k : nat) :
  (k < n)%nat -> nth_error (replicate n x) k = Some x.
Proof.
  revert k. induction n as [|n IH]; intros [|k] Hlt; cbn; try lia.
  - reflexivity.
  - apply IH; lia.
Qed.

Lemma nth_error_replicate_inv {A : Type} (n : nat) (x y : A) (k : nat) :
  nth_error (replicate n x) k = Some y -> y = x.
Proof.
  revert k. induction n as [|n IH]; intros [|k] H; cbn in H; try discriminate.
  - injection H; auto.
  - eapply IH; exact H.
Qed.

Module CtTableScan (R : Runtime).
Module PL := PoisonLogic R.
Import PL.

Section proof.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ, !gen_heapGS ppiece ppval Σ}.
Local Instance cttable_iris : irisGS_gen hlc (poison_lang pol_strict cttable_ge) Σ :=
  poison_irisGS pol_strict cttable_ge.
Local Abbreviation pexprL := (language.expr (poison_lang pol_strict cttable_ge)).

(** Helper tactic discharging side conditions of pure integer `Let` steps. *)
Local Ltac solve_plet_side :=
  first
    [ reflexivity
    | assumption
    | cbn [value_x word_at_class modulus]; solve_lookup
    | cbn [value_t]; solve_lookup
    | cbn [alu extended]; reflexivity ].

(** Stepping a pure binary integer `Let` updates the environment and taint
    environment without touching memory. *)
Lemma wp_plet_int_bin f e te ls l d k o v1 v2 rest j c1 c2 n1 n2 n t1 t2 Φ :
  pure_scalar_op o = true ->
  int_classb k = true -> int_classb c1 = true ->
  op_arg_classes o k = Some [c1; c2] ->
  value_x cttable_ge e c1 v1 = Some (WInt n1) ->
  value_x cttable_ge e c2 v2 = Some (WInt n2) ->
  value_t te c1 v1 = Some (WTInt t1) ->
  value_t te c2 v2 = Some (WTInt t2) ->
  is_zero_idiom o k [v1; v2] = false ->
  op_checks_vartime pol_strict o k = false ->
  alu o k [WInt n1; WInt n2] = Some (WInt n) ->
  ▷ WP (PRun (mkFrame f (put d (WInt n) e) ls None (Exec l rest j))
        (put d (WTInt (taint_join t1 t2)) te) : pexprL) {{ Φ }} -∗
  WP (PRun (mkFrame f e ls None (Exec l (Let d k o [v1; v2] :: rest) j)) te : pexprL) {{ Φ }}.
Proof using Type.
  intros Hp Hfk Hfc1 Hc Hx1 Hx2 Ht1 Ht2 Hz Hvt Halu.
  assert (Hg : general_op o = true) by (destruct o; cbn in Hp |- *; try discriminate; reflexivity).
  iApply (wp_plet pol_strict cttable_ge f e te ls l d k o [v1; v2] rest j
    [c1; c2] [WInt n1; WInt n2] (WInt n) (WTInt (taint_join t1 t2)));
    [exact Hg | exact Hc | | |].
  - cbn [map2_option]; rewrite Hx1 Hx2; reflexivity.
  - intros m.
    destruct k; try discriminate Hfk;
      destruct c1; try discriminate Hfc1;
      destruct o; cbn in Hp, Hc; try discriminate;
      try (injection Hc as ? ?; subst);
      unfold op_res, op_res_int, additive_res; cbn [fmt_of];
      rewrite Halu; reflexivity.
  - intros pm paux. unfold let_tstep. rewrite Hz.
    cbn [ps_tenv ps_callers ps_mem ps_aux].
    destruct k; try discriminate Hfk;
      destruct o; cbn in Hp, Hc; try discriminate;
      try (injection Hc as ? ?; subst);
      cbn [op_arg_classes map2_option]; rewrite Ht1 Ht2;
      cbn [join_taints map_option pure_scalar_op scalar_wt]; rewrite Hvt;
      cbn [andb]; rewrite ?taint_join_bot_r; reflexivity.
Qed.

Definition un_int_opb (o : op) : bool :=
  match o with Copy | Ext _ => true | _ => false end.

(** Stepping a pure unary integer `Let` (`Copy` or `Ext Uw`). *)
Lemma wp_plet_int_un f e te ls l d k o v1 rest j c1 n1 n t1 Φ :
  un_int_opb o = true ->
  int_classb k = true ->
  op_arg_classes o k = Some [c1] ->
  value_x cttable_ge e c1 v1 = Some (WInt n1) ->
  value_t te c1 v1 = Some (WTInt t1) ->
  is_zero_idiom o k [v1] = false ->
  op_checks_vartime pol_strict o k = false ->
  alu o k [WInt n1] = Some (WInt n) ->
  ▷ WP (PRun (mkFrame f (put d (WInt n) e) ls None (Exec l rest j))
        (put d (WTInt t1) te) : pexprL) {{ Φ }} -∗
  WP (PRun (mkFrame f e ls None (Exec l (Let d k o [v1] :: rest) j)) te : pexprL) {{ Φ }}.
Proof using Type.
  intros Hp Hfk Hc Hx1 Ht1 Hz Hvt Halu.
  assert (Hg : general_op o = true) by (destruct o; cbn in Hp |- *; try discriminate; reflexivity).
  iApply (wp_plet pol_strict cttable_ge f e te ls l d k o [v1] rest j
    [c1] [WInt n1] (WInt n) (WTInt t1));
    [exact Hg | exact Hc | | |].
  - cbn [map2_option]; rewrite Hx1; reflexivity.
  - intros m.
    destruct k; try discriminate Hfk;
      destruct o; cbn in Hp, Hc; try discriminate;
      try (injection Hc as ?; subst);
      unfold op_res, op_res_int; cbn [fmt_of];
      rewrite Halu; reflexivity.
  - intros pm paux. unfold let_tstep. rewrite Hz.
    cbn [ps_tenv ps_callers ps_mem ps_aux].
    destruct k; try discriminate Hfk;
      destruct o; cbn in Hp, Hc; try discriminate;
      try (injection Hc as ?; subst);
      cbn [op_arg_classes map2_option]; rewrite Ht1;
      cbn [join_taints map_option pure_scalar_op scalar_wt]; rewrite ?Hvt;
      cbn [andb]; rewrite ?taint_join_bot_r; reflexivity.
Qed.

(** The inner loop `L55` scans all remaining entries `k .. 15` of the exact
    16-byte `tbl` buffer using public index `‹k›` and exits to `L58` with
    all heap ownership restored and a secret accumulated table byte in
    `‹expected›`. *)
Lemma scan_ct_inner_spec b_tbl cap_tbl reg_tbl tbl_xs dq pdq
    (k_rem : nat) (k_start : Z) (i_val exp_val : Z) (ti texp : taint)
    (e : env) (te : tenv) Φ :
  cap_tbl = Obj b_tbl \/ cap_tbl = Ro b_tbl ->
  0 <= b_tbl -> b_tbl + 16 < 2 ^ 64 -> b_tbl + 16 <= r_end reg_tbl ->
  length tbl_xs = 16%nat ->
  0 <= k_start -> k_start + Z.of_nat k_rem = 16 ->
  lookup ‹tbl› e = Some (WPtr (mkPtr b_tbl cap_tbl)) ->
  lookup ‹tbl› te = Some (WTPtr taint_bot taint_bot) ->
  lookup ‹i› e = Some (WInt i_val) ->
  lookup ‹i› te = Some (WTInt ti) ->
  lookup ‹k› e = Some (WInt k_start) ->
  lookup ‹k› te = Some (WTInt taint_bot) ->
  lookup ‹expected› e = Some (WInt exp_val) ->
  lookup ‹expected› te = Some (WTInt texp) ->
  ptsq dq [(PLive b_tbl, VLive reg_tbl)] -∗
  ptsq dq (bytes_ps b_tbl 0 tbl_xs) -∗
  pptsq pdq (pbytes_ps b_tbl 0 (replicate 16 (pb_secret taint_all))) -∗
  (∀ e' te' exp_out texp_out,
    ⌜(forall x, x <> ‹k› -> x <> ‹expected› ->
       x <> ‹k<u16› -> x <> ‹k==i› -> x <> ‹eq_mask› ->
       x <> TAtom "v69" -> x <> TAtom "chk1" -> x <> TAtom "v70" ->
       x <> TAtom "v72" -> x <> ‹expected@L56› -> x <> ‹k@L56› ->
       lookup x e' = lookup x e /\ lookup x te' = lookup x te)⌝ -∗
    ⌜lookup ‹expected› e' = Some (WInt exp_out)⌝ -∗
    ⌜lookup ‹expected› te' = Some (WTInt texp_out)⌝ -∗
    ptsq dq [(PLive b_tbl, VLive reg_tbl)] -∗
    ptsq dq (bytes_ps b_tbl 0 tbl_xs) -∗
    pptsq pdq (pbytes_ps b_tbl 0 (replicate 16 (pb_secret taint_all))) -∗
    WP (PRun (mkFrame fn_scan_ct e' [] None (Enter (TAtom "L58") (Some (TAtom "L55"))))
          te' : pexprL) {{ Φ }}) -∗
  WP (PRun (mkFrame fn_scan_ct e [] None
        (Exec (TAtom "L55")
          [Let ‹k<u16› W (Cmp Ult L) [Tmp ‹k›; Const 16]]
          (JBranch (Tmp ‹k<u16›) (To (TAtom "L56")) (To (TAtom "L58")))))
        te : pexprL) {{ Φ }}.
Proof using Type.
  intros Hcap Hb Hlim Hrend Hlen.
  induction k_rem as [|k_rem IH] in k_start, exp_val, texp, e, te |- *.
  - intros Hk0 Hk16 Hv10 Htv10 Hpr2 Htpr2 Hpr5 Htpr5 Hpr4 Htpr4.
    iIntros "Hlp Hxsp Hpbsp Hcont".
    assert (Hk : k_start = 16) by lia. subst k_start.
    iApply (wp_plet_int_bin _ _ _ _ _ _ _ _ _ _ _ _ L L 16 16 0 taint_bot taint_bot);
      try solve_plet_side.
    iNext.
    iApply (wp_pbranch pol_strict cttable_ge _ _ _ _ _ _ _ _ 0 taint_bot);
      [cbn [value_x word_at_class modulus]; solve_lookup
      |cbn [value_t]; solve_lookup
      |reflexivity|].
    iNext.
    iApply ("Hcont" $! (put ‹k<u16› (WInt 0) e)
      (put ‹k<u16› (WTInt (taint_join taint_bot taint_bot)) te)
      exp_val texp with "[] [] [] Hlp Hxsp Hpbsp").
    + iPureIntro; intros x _ _ H60 _ _ _ _ _ _ _ _;
        split; apply lookup_put_neq; exact H60.
    + iPureIntro; rewrite lookup_put_other; [exact Hpr4 | reflexivity].
    + iPureIntro; rewrite lookup_put_other; [exact Htpr4 | reflexivity].
  - intros Hk0 Hk16 Hv10 Htv10 Hpr2 Htpr2 Hpr5 Htpr5 Hpr4 Htpr4.
    iIntros "Hlp Hxsp Hpbsp Hcont".
    assert (Hk_lt : k_start < 16) by lia.
    assert (Hk_mod : k_start mod 2 ^ 64 = k_start) by (apply Z.mod_small; lia).
    assert (Hcmp : (k_start <? 16) = true) by (apply Z.ltb_lt; lia).
    (* ‹k<u16› = cmp ult ‹k›, 16 *)
    iApply (wp_plet_int_bin _ _ _ _ _ _ _ _ _ _ _ _ L L k_start 16 1 taint_bot taint_bot);
      try solve_plet_side;
      [cbn [alu cond_bit modulus]; rewrite Hcmp; reflexivity|].
    iNext.
    (* branch ‹k<u16› -> L56 *)
    iApply (wp_pbranch pol_strict cttable_ge _ _ _ _ _ _ _ _ 1 taint_bot);
      [cbn [value_x word_at_class modulus]; solve_lookup
      |cbn [value_t]; solve_lookup
      |reflexivity|].
    iNext.
    (* Enter L56 from L55 *)
    iApply (wp_penter pol_strict cttable_ge _ _ _ _ _ _ _ _ _);
      [reflexivity | reflexivity | reflexivity |].
    iNext.
    cbn [b_insts b_jump].
    (* ‹k==i› = cmp eq ‹k›, ‹i› *)
    set (eq_b := if k_start =? (i_val mod 2 ^ 64) then 1 else 0).
    iApply (wp_plet_int_bin _ _ _ _ _ _ _ _ _ _ _ _ L L k_start (i_val mod 2 ^ 64) eq_b taint_bot ti);
      try solve_plet_side.
    iNext.
    (* ‹eq_mask› = sub 0, ‹k==i› *)
    destruct (alu_int_total_bin Sub W 0 (eq_b mod 2 ^ 32) ltac:(auto) ltac:(auto)) as [eq_mask H65].
    iApply (wp_plet_int_bin _ _ _ _ _ _ _ _ _ _ _ _ W W 0 (eq_b mod 2 ^ 32) eq_mask taint_bot (taint_join taint_bot ti));
      try solve_plet_side.
    iNext.
    (* v69 = ‹tbl› +p ‹k› *)
    assert (Haddr_mod : (b_tbl + k_start) mod 2 ^ 64 = b_tbl + k_start)
      by (apply Z.mod_small; lia).
    iApply (wp_pflight pol_strict cttable_ge _ _ _ _ _ _ _ _ _ _ _
              [WInt b_tbl; WInt k_start] [taint_bot; taint_bot]
              (b_tbl + k_start) cap_tbl taint_bot);
      [cbn [map_option flight_arg_x value_x word_at_class modulus];
       repeat (rewrite lookup_put_other; [|reflexivity]);
       rewrite Hv10 Hpr5; cbn [word_at_class modulus ptr_addr];
       rewrite (Z.mod_small b_tbl (2 ^ 64) ltac:(lia)) Hk_mod; reflexivity
      |cbn [map_option flight_arg_t value_t];
       repeat (rewrite lookup_put_other; [|reflexivity]);
       rewrite Htv10 Htpr5; reflexivity
      |cbn [alu cond_bit modulus]; rewrite Haddr_mod; reflexivity
      |cbn [flight_cap value_x];
       repeat (rewrite lookup_put_other; [|reflexivity]);
       rewrite Hv10; reflexivity
      |cbn [flight_cap_t value_t];
       repeat (rewrite lookup_put_other; [|reflexivity]);
       rewrite Htv10; reflexivity
      |reflexivity|].
    iNext.
    (* chk1 = check 0 1 read 1 [v69] *)
    iApply (wp_pcheck_read pol_strict cttable_ge _ _ _ _ _ _ _ _ _ _ _ _
              (mkPtr (b_tbl + k_start) cap_tbl) taint_bot taint_bot b_tbl reg_tbl dq with "Hlp");
      [cbn [value_x word_at_class modulus]; solve_lookup
      |cbn [value_t]; solve_lookup
      |reflexivity
      |exact Hcap
      |unfold raw_address; cbn [ptr_addr]; rewrite Z.add_0_r Haddr_mod; lia
      |unfold raw_address; cbn [ptr_addr]; rewrite Z.add_0_r Haddr_mod; lia
      |unfold raw_address; cbn [ptr_addr]; apply Z.mod_1_r|].
    iNext. iIntros "Hlp".
    (* v70 = raw_load ub 0 [chk1] *)
    set (k_nat := Z.to_nat k_start).
    assert (Hk_nat : Z.of_nat k_nat = k_start) by (subst k_nat; lia).
    destruct (nth_error_some_lt tbl_xs k_nat ltac:(lia)) as [tb Htb].
    assert (Hpb : nth_error (replicate 16 (pb_secret taint_all)) k_nat = Some (pb_secret taint_all))
      by (apply nth_error_replicate_some; lia).
    iApply (wp_praw_load_byte_at pol_strict cttable_ge _ _ _ _ _ _ _ _ _ _ _ _
              (mkPtr (b_tbl + k_start) cap_tbl) b_tbl reg_tbl 0 k_nat
              tbl_xs tb (replicate 16 (pb_secret taint_all)) (pb_secret taint_all)
              (WInt (tb mod 256)) taint_bot taint_bot dq pdq
              with "Hlp Hxsp Hpbsp");
      [reflexivity
      |cbn [value_x word_at_class modulus]; solve_lookup
      |cbn [value_t]; solve_lookup
      |reflexivity
      |unfold extended; cbn; rewrite (Z.mod_small (tb mod 256) (2 ^ 32)
          ltac:(pose proof (Z.mod_pos_bound tb 256 ltac:(lia)); lia)); reflexivity
      |exact Hcap
      |unfold raw_address; cbn [ptr_addr]; rewrite Z.add_0_r Z.add_0_l Haddr_mod Hk_nat; lia
      |exact Htb
      |exact Hpb
      |reflexivity | reflexivity | reflexivity|].
    iNext. iIntros "Hlp Hxsp Hpbsp".
    (* v72 = and v70, ‹eq_mask› *)
    set (tb_u := tb mod 256).
    destruct (alu_int_total_bin And W (tb_u mod 2 ^ 32) (eq_mask mod 2 ^ 32) ltac:(auto) ltac:(auto)) as [masked H72].
    iApply (wp_plet_int_bin _ _ _ _ _ _ _ _ _ _ _ _ W W (tb_u mod 2 ^ 32) (eq_mask mod 2 ^ 32) masked
              taint_all (taint_join taint_bot (taint_join taint_bot ti)));
      try solve_plet_side.
    iNext.
    (* ‹expected@L56› = or ‹expected›, v72 *)
    destruct (alu_int_total_bin Or W (exp_val mod 2 ^ 32) (masked mod 2 ^ 32) ltac:(auto) ltac:(auto)) as [exp_next H73].
    iApply (wp_plet_int_bin _ _ _ _ _ _ _ _ _ _ _ _ W W (exp_val mod 2 ^ 32) (masked mod 2 ^ 32) exp_next
              texp (taint_join taint_all (taint_join taint_bot (taint_join taint_bot ti))));
      try solve_plet_side.
    iNext.
    (* ‹k@L56› = add ‹k›, 1 *)
    assert (Hk1_mod : (k_start + 1) mod 2 ^ 64 = k_start + 1) by (apply Z.mod_small; lia).
    iApply (wp_plet_int_bin _ _ _ _ _ _ _ _ _ _ _ _ L L k_start 1 (k_start + 1) taint_bot taint_bot);
      try solve_plet_side;
      [cbn [alu cond_bit modulus]; rewrite Hk1_mod; reflexivity|].
    iNext.
    (* goto poll L55 *)
    iApply (wp_pgoto pol_strict cttable_ge).
    iNext.
    (* Enter L55 from L56 *)
    iApply (wp_penter pol_strict cttable_ge _ _ _ _ _ _ _ _ _);
      [reflexivity
      |cbn [b_phis phis_env fold_left lookup name_eqb term_eqb String.eqb Ascii.eqb Bool.eqb andb value_x word_at_class modulus];
        reflexivity
      |cbn [b_phis phis_tenv fold_left lookup name_eqb term_eqb String.eqb Ascii.eqb Bool.eqb andb value_t];
        reflexivity|].
    iNext.
    cbn [b_insts b_jump].
    (* Apply IH for k_start + 1 *)
    iApply (IH (k_start + 1) (exp_next mod 2 ^ 32)
      (taint_join texp (taint_join taint_all (taint_join taint_bot (taint_join taint_bot ti))))
      with "Hlp Hxsp Hpbsp [Hcont]");
      [lia | lia | solve_lookup | solve_lookup | solve_lookup | solve_lookup
      | solve_lookup | solve_lookup | solve_lookup | solve_lookup |].
    iIntros (e' te' exp_out texp_out Hpres Hpr4' Htpr4') "Hlp Hxsp Hpbsp".
    iApply ("Hcont" $! e' te' exp_out texp_out with "[] [] [] Hlp Hxsp Hpbsp");
      try (iPureIntro; assumption).
    iPureIntro. intros x Hx5 Hx4 H60 H64 H65' H69 Hchk1 H70 H72' H73' H75.
    destruct (Hpres x Hx5 Hx4 H60 H64 H65' H69 Hchk1 H70 H72' H73' H75) as [He Hte].
    rewrite He Hte.
    split; repeat (rewrite lookup_put_neq; [|assumption]); reflexivity.
Qed.

(** The outer loop `L28` iterates over every remaining byte `j .. win + 15`
    of the public tail window, loading `p[j]` at public address `b_buf + p_off + j`,
    invoking [scan_ct_inner_spec] on the exact 16-byte table, and returning a
    secret integer result at `L31`. *)
Lemma scan_ct_outer_spec b_buf cap_buf reg_buf buf_xs
    b_tbl cap_tbl reg_tbl tbl_xs dq pdq
    len win start p_off
    (j_rem : nat) (j_start i_val res_val : Z) (ti tres : taint)
    (e : env) (te : tenv) :
  cap_buf = Obj b_buf \/ cap_buf = Ro b_buf ->
  cap_tbl = Obj b_tbl \/ cap_tbl = Ro b_tbl ->
  0 <= b_buf -> b_buf + len < 2 ^ 64 -> b_buf + len <= r_end reg_buf ->
  0 <= b_tbl -> b_tbl + 16 < 2 ^ 64 -> b_tbl + 16 <= r_end reg_tbl ->
  0 <= win -> win + 16 <= len ->
  p_off = len - win - 16 ->
  length buf_xs = Z.to_nat len ->
  length tbl_xs = 16%nat ->
  0 <= j_start -> j_start + Z.of_nat j_rem = win + 16 ->
  lookup ‹win› e = Some (WInt win) ->
  lookup ‹win› te = Some (WTInt taint_bot) ->
  lookup ‹start› e = Some (WInt start) ->
  lookup ‹start› te = Some (WTInt taint_all) ->
  lookup ‹tbl› e = Some (WPtr (mkPtr b_tbl cap_tbl)) ->
  lookup ‹tbl› te = Some (WTPtr taint_bot taint_bot) ->
  lookup ‹p› e = Some (WPtr (mkPtr (b_buf + p_off) cap_buf)) ->
  lookup ‹p› te = Some (WTPtr taint_bot taint_bot) ->
  lookup ‹j› e = Some (WInt j_start) ->
  lookup ‹j› te = Some (WTInt taint_bot) ->
  lookup ‹i› e = Some (WInt i_val) ->
  lookup ‹i› te = Some (WTInt ti) ->
  lookup ‹res› e = Some (WInt res_val) ->
  lookup ‹res› te = Some (WTInt tres) ->
  ptsq dq [(PLive b_buf, VLive reg_buf)] -∗
  ptsq dq (bytes_ps b_buf 0 buf_xs) -∗
  pptsq pdq (pbytes_ps b_buf 0 (replicate (length buf_xs) (pb_secret taint_all))) -∗
  ptsq dq [(PLive b_tbl, VLive reg_tbl)] -∗
  ptsq dq (bytes_ps b_tbl 0 tbl_xs) -∗
  pptsq pdq (pbytes_ps b_tbl 0 (replicate 16 (pb_secret taint_all))) -∗
  WP (PRun (mkFrame fn_scan_ct e [] None
        (Exec (TAtom "L28")
          [Let (TAtom "v34") L Add [Tmp ‹win›; Const 16];
           Let (TAtom "v35") W (Cmp Ult L) [Tmp ‹j›; Tmp (TAtom "v34")]]
          (JBranch (Tmp (TAtom "v35")) (To (TAtom "L29")) (To (TAtom "L31")))))
        te : pexprL)
    {{ v, ∃ n t, ⌜v = (Ret (WInt n), [WTInt t])⌝ }}.
Proof using Type.
  intros Hcap_buf Hcap_tbl Hb_buf Hbuf_lim Hrend_buf Hb_tbl Htbl_lim Hrend_tbl
    Hwin Hlen_ge Hpoff Hlen_buf Hlen_tbl.
  assert (Hwin_mod : win mod 2 ^ 64 = win) by (apply Z.mod_small; lia).
  assert (Hlim_mod : (win + 16) mod 2 ^ 64 = win + 16) by (apply Z.mod_small; lia).
  induction j_rem as [|j_rem IH] in j_start, i_val, res_val, ti, tres, e, te |- *.
  - intros Hj0 Hjlim Hv4 Htv4 Hv8 Htv8 Hv10 Htv10 Hv24 Htv24
      Hpr3 Htpr3 Hpr2 Htpr2 Hpr1 Htpr1.
    iIntros "Hlo Hxso Hpbso Hlp Hxsp Hpbsp".
    assert (Hj : j_start = win + 16) by lia. subst j_start.
    iApply (wp_plet_int_bin _ _ _ _ _ _ _ _ _ _ _ _ L L win 16 (win + 16) taint_bot taint_bot);
      try solve_plet_side;
      [cbn [alu cond_bit modulus]; rewrite Hlim_mod; reflexivity|].
    iNext.
    iApply (wp_plet_int_bin _ _ _ _ _ _ _ _ _ _ _ _ L L (win + 16) (win + 16) 0 taint_bot taint_bot);
      try solve_plet_side;
      [cbn [alu cond_bit modulus]; rewrite Z.ltb_irrefl; reflexivity|].
    iNext.
    iApply (wp_pbranch pol_strict cttable_ge _ _ _ _ _ _ _ _ 0 taint_bot);
      [cbn [value_x word_at_class modulus]; solve_lookup
      |cbn [value_t]; solve_lookup
      |reflexivity|].
    iNext.
    iApply (wp_penter pol_strict cttable_ge _ _ _ _ _ _ _ _ _);
      [reflexivity | reflexivity | reflexivity |].
    iNext.
    cbn [b_insts b_jump].
    iApply (wp_pret pol_strict cttable_ge _ _ _ _ _ W (WInt (res_val mod 2 ^ 32)));
      [reflexivity
      |cbn [value_x word_at_class modulus]; solve_lookup
      |cbn [value_t]; solve_lookup|].
    iNext. iExists (res_val mod 2 ^ 32), tres. iPureIntro. reflexivity.
  - intros Hj0 Hjlim Hv4 Htv4 Hv8 Htv8 Hv10 Htv10 Hv24 Htv24
      Hpr3 Htpr3 Hpr2 Htpr2 Hpr1 Htpr1.
    iIntros "Hlo Hxso Hpbso Hlp Hxsp Hpbsp".
    assert (Hj_lt : j_start < win + 16) by lia.
    assert (Hj_mod : j_start mod 2 ^ 64 = j_start) by (apply Z.mod_small; lia).
    assert (Hcmp : (j_start <? win + 16) = true) by (apply Z.ltb_lt; lia).
    iApply (wp_plet_int_bin _ _ _ _ _ _ _ _ _ _ _ _ L L win 16 (win + 16) taint_bot taint_bot);
      try solve_plet_side;
      [cbn [alu cond_bit modulus]; rewrite Hlim_mod; reflexivity|].
    iNext.
    iApply (wp_plet_int_bin _ _ _ _ _ _ _ _ _ _ _ _ L L j_start (win + 16) 1 taint_bot taint_bot);
      try solve_plet_side;
      [cbn [alu cond_bit modulus]; rewrite Hcmp; reflexivity|].
    iNext.
    iApply (wp_pbranch pol_strict cttable_ge _ _ _ _ _ _ _ _ 1 taint_bot);
      [cbn [value_x word_at_class modulus]; solve_lookup
      |cbn [value_t]; solve_lookup
      |reflexivity|].
    iNext.
    iApply (wp_penter pol_strict cttable_ge _ _ _ _ _ _ _ _ _);
      [reflexivity | reflexivity | reflexivity |].
    iNext.
    cbn [b_insts b_jump].
    (* v39 = ‹p› +p ‹j› *)
    assert (Hpoff_addr_mod : (b_buf + p_off) mod 2 ^ 64 = b_buf + p_off)
      by (apply Z.mod_small; lia).
    assert (Haddr_mod : (b_buf + p_off + j_start) mod 2 ^ 64 = b_buf + p_off + j_start)
      by (apply Z.mod_small; lia).
    iApply (wp_pflight pol_strict cttable_ge _ _ _ _ _ _ _ _ _ _ _
              [WInt (b_buf + p_off); WInt j_start] [taint_bot; taint_bot]
              (b_buf + p_off + j_start) cap_buf taint_bot);
      [cbn [map_option flight_arg_x value_x word_at_class modulus];
       repeat (rewrite lookup_put_other; [|reflexivity]);
       rewrite Hv24 Hpr3; cbn [word_at_class modulus ptr_addr];
       rewrite Hpoff_addr_mod Hj_mod; reflexivity
      |cbn [map_option flight_arg_t value_t];
       repeat (rewrite lookup_put_other; [|reflexivity]);
       rewrite Htv24 Htpr3; reflexivity
      |cbn [alu cond_bit modulus]; rewrite Haddr_mod; reflexivity
      |cbn [flight_cap value_x];
       repeat (rewrite lookup_put_other; [|reflexivity]);
       rewrite Hv24; reflexivity
      |cbn [flight_cap_t value_t];
       repeat (rewrite lookup_put_other; [|reflexivity]);
       rewrite Htv24; reflexivity
      |reflexivity|].
    iNext.
    (* chk0 = check 0 1 read 1 [v39] *)
    iApply (wp_pcheck_read pol_strict cttable_ge _ _ _ _ _ _ _ _ _ _ _ _
              (mkPtr (b_buf + p_off + j_start) cap_buf) taint_bot taint_bot b_buf reg_buf dq with "Hlo");
      [cbn [value_x word_at_class modulus]; solve_lookup
      |cbn [value_t]; solve_lookup
      |reflexivity
      |exact Hcap_buf
      |unfold raw_address; cbn [ptr_addr]; rewrite Z.add_0_r Haddr_mod; lia
      |unfold raw_address; cbn [ptr_addr]; rewrite Z.add_0_r Haddr_mod; lia
      |unfold raw_address; cbn [ptr_addr]; apply Z.mod_1_r|].
    iNext. iIntros "Hlo".
    (* ‹c› = raw_load ub 0 [chk0] *)
    set (j_idx := Z.to_nat (p_off + j_start)).
    assert (Hj_idx : Z.of_nat j_idx = p_off + j_start) by (subst j_idx; lia).
    destruct (nth_error_some_lt buf_xs j_idx ltac:(lia)) as [cb Hcb].
    assert (Hpb_buf : nth_error (replicate (length buf_xs) (pb_secret taint_all)) j_idx = Some (pb_secret taint_all))
      by (apply nth_error_replicate_some; lia).
    iApply (wp_praw_load_byte_at pol_strict cttable_ge _ _ _ _ _ _ _ _ _ _ _ _
              (mkPtr (b_buf + p_off + j_start) cap_buf) b_buf reg_buf 0 j_idx
              buf_xs cb (replicate (length buf_xs) (pb_secret taint_all)) (pb_secret taint_all)
              (WInt (cb mod 256)) taint_bot taint_bot dq pdq
              with "Hlo Hxso Hpbso");
      [reflexivity
      |cbn [value_x word_at_class modulus]; solve_lookup
      |cbn [value_t]; solve_lookup
      |reflexivity
      |unfold extended; cbn; rewrite (Z.mod_small (cb mod 256) (2 ^ 32)
          ltac:(pose proof (Z.mod_pos_bound cb 256 ltac:(lia)); lia)); reflexivity
      |exact Hcap_buf
      |unfold raw_address; cbn [ptr_addr]; rewrite Z.add_0_r Z.add_0_l Haddr_mod Hj_idx; lia
      |exact Hcb
      |exact Hpb_buf
      |reflexivity | reflexivity | reflexivity|].
    iNext. iIntros "Hlo Hxso Hpbso".
    (* ‹j>=ustart› = cmp uge l ‹j›, ‹start› *)
    set (c44 := if (start mod 2 ^ 64) <=? j_start then 1 else 0).
    iApply (wp_plet_int_bin _ _ _ _ _ _ _ _ _ _ _ _ L L j_start (start mod 2 ^ 64) c44 taint_bot taint_all);
      try solve_plet_side.
    iNext.
    (* v47 = add l ‹start›, 16 *)
    destruct (alu_int_total_bin Add L (start mod 2 ^ 64) 16 ltac:(auto) ltac:(auto)) as [n47 H47].
    iApply (wp_plet_int_bin _ _ _ _ _ _ _ _ _ _ _ _ L L (start mod 2 ^ 64) 16 n47 taint_all taint_bot);
      try solve_plet_side.
    iNext.
    (* v48 = cmp ult l ‹j›, v47 *)
    set (c48 := if j_start <? (n47 mod 2 ^ 64) then 1 else 0).
    iApply (wp_plet_int_bin _ _ _ _ _ _ _ _ _ _ _ _ L L j_start (n47 mod 2 ^ 64) c48 taint_bot (taint_join taint_all taint_bot));
      try solve_plet_side.
    iNext.
    (* ‹in_range› = and w ‹j>=ustart›, v48 *)
    destruct (alu_int_total_bin And W (c44 mod 2 ^ 32) (c48 mod 2 ^ 32) ltac:(auto) ltac:(auto)) as [n49 H49].
    iApply (wp_plet_int_bin _ _ _ _ _ _ _ _ _ _ _ _ W W (c44 mod 2 ^ 32) (c48 mod 2 ^ 32) n49
              (taint_join taint_bot taint_all) (taint_join taint_bot (taint_join taint_all taint_bot)));
      try solve_plet_side.
    iNext.
    (* ‹mask› = sub w 0, ‹in_range› *)
    destruct (alu_int_total_bin Sub W 0 (n49 mod 2 ^ 32) ltac:(auto) ltac:(auto)) as [n52 H52].
    iApply (wp_plet_int_bin _ _ _ _ _ _ _ _ _ _ _ _ W W 0 (n49 mod 2 ^ 32) n52
              taint_bot (taint_join (taint_join taint_bot taint_all) (taint_join taint_bot (taint_join taint_all taint_bot))));
      try solve_plet_side.
    iNext.
    (* goto L55 *)
    iApply (wp_pgoto pol_strict cttable_ge).
    iNext.
    (* Enter L55 from L29 *)
    iApply (wp_penter pol_strict cttable_ge _ _ _ _ _ _ _ _ _);
      [reflexivity | reflexivity | reflexivity |].
    iNext.
    cbn [b_insts b_jump].
    (* Run inner loop scan_ct_inner_spec *)
    iApply (scan_ct_inner_spec b_tbl cap_tbl reg_tbl tbl_xs dq pdq 16%nat 0 i_val 0 ti taint_bot
              with "Hlp Hxsp Hpbsp [Hlo Hxso Hpbso]");
      [exact Hcap_tbl | lia | lia | lia | exact Hlen_tbl | lia | lia
      | solve_lookup | solve_lookup | solve_lookup | solve_lookup
      | solve_lookup | solve_lookup | solve_lookup | solve_lookup |].
    iIntros (e1 te1 exp_out texp_out Hpres Hpr4' Htpr4') "Hlp Hxsp Hpbsp".
    (* Enter L58 from L55 *)
    iApply (wp_penter pol_strict cttable_ge _ _ _ _ _ _ _ _ _);
      [reflexivity | reflexivity | reflexivity |].
    iNext.
    cbn [b_insts b_jump].
    assert (He1_v40 : lookup ‹c› e1 = Some (WInt (cb mod 256))).
    { destruct (Hpres ‹c› ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
        ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
        ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)) as [H _].
      rewrite H; solve_lookup. }
    assert (Hte1_v40 : lookup ‹c› te1 = Some (WTInt taint_all)).
    { destruct (Hpres ‹c› ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
        ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
        ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)) as [_ H].
      rewrite H; solve_lookup. }
    assert (He1_v49 : lookup ‹in_range› e1 = Some (WInt n49)).
    { destruct (Hpres ‹in_range› ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
        ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
        ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)) as [H _].
      rewrite H; solve_lookup. }
    assert (Hte1_v49 : lookup ‹in_range› te1 = Some (WTInt taint_all)).
    { destruct (Hpres ‹in_range› ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
        ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
        ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)) as [_ H].
      rewrite H; solve_lookup. }
    assert (He1_v52 : lookup ‹mask› e1 = Some (WInt n52)).
    { destruct (Hpres ‹mask› ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
        ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
        ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)) as [H _].
      rewrite H; solve_lookup. }
    assert (Hte1_v52 : lookup ‹mask› te1 = Some (WTInt taint_all)).
    { destruct (Hpres ‹mask› ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
        ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
        ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)) as [_ H].
      rewrite H; solve_lookup. }
    assert (He1_pr1 : lookup ‹res› e1 = Some (WInt res_val)).
    { destruct (Hpres ‹res› ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
        ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
        ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)) as [H _].
      rewrite H; solve_lookup. }
    assert (Hte1_pr1 : lookup ‹res› te1 = Some (WTInt tres)).
    { destruct (Hpres ‹res› ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
        ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
        ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)) as [_ H].
      rewrite H; solve_lookup. }
    assert (He1_pr2 : lookup ‹i› e1 = Some (WInt i_val)).
    { destruct (Hpres ‹i› ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
        ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
        ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)) as [H _].
      rewrite H; solve_lookup. }
    assert (Hte1_pr2 : lookup ‹i› te1 = Some (WTInt ti)).
    { destruct (Hpres ‹i› ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
        ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
        ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)) as [_ H].
      rewrite H; solve_lookup. }
    assert (He1_pr3 : lookup ‹j› e1 = Some (WInt j_start)).
    { destruct (Hpres ‹j› ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
        ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
        ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)) as [H _].
      rewrite H; solve_lookup. }
    assert (Hte1_pr3 : lookup ‹j› te1 = Some (WTInt taint_bot)).
    { destruct (Hpres ‹j› ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
        ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
        ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)) as [_ H].
      rewrite H; solve_lookup. }
    (* v79 = xor ‹c›, ‹expected› *)
    destruct (alu_int_total_bin Xor W ((cb mod 256) mod 2 ^ 32) (exp_out mod 2 ^ 32) ltac:(auto) ltac:(auto)) as [n79 H79].
    iApply (wp_plet_int_bin _ _ _ _ _ _ _ _ _ _ _ _ W W ((cb mod 256) mod 2 ^ 32) (exp_out mod 2 ^ 32) n79 taint_all texp_out);
      try solve_plet_side.
    iNext.
    (* v81 = and v79, ‹mask› *)
    destruct (alu_int_total_bin And W (n79 mod 2 ^ 32) (n52 mod 2 ^ 32) ltac:(auto) ltac:(auto)) as [n81 H81].
    iApply (wp_plet_int_bin _ _ _ _ _ _ _ _ _ _ _ _ W W (n79 mod 2 ^ 32) (n52 mod 2 ^ 32) n81
              (taint_join taint_all texp_out) taint_all);
      try solve_plet_side.
    iNext.
    (* ‹res@L58› = or ‹res›, v81 *)
    destruct (alu_int_total_bin Or W (res_val mod 2 ^ 32) (n81 mod 2 ^ 32) ltac:(auto) ltac:(auto)) as [n82 H82].
    iApply (wp_plet_int_bin _ _ _ _ _ _ _ _ _ _ _ _ W W (res_val mod 2 ^ 32) (n81 mod 2 ^ 32) n82
              tres (taint_join (taint_join taint_all texp_out) taint_all));
      try solve_plet_side.
    iNext.
    (* v85 = ext uw ‹in_range› *)
    set (n85 := ((n49 mod 2 ^ 32) mod 2 ^ 32) mod 2 ^ 64).
    iApply (wp_plet_int_un _ _ _ _ _ _ _ _ _ _ _ W (n49 mod 2 ^ 32) n85 taint_all);
      try solve_plet_side.
    iNext.
    (* ‹i@L58› = add ‹i›, v85 *)
    destruct (alu_int_total_bin Add L (i_val mod 2 ^ 64) (n85 mod 2 ^ 64) ltac:(auto) ltac:(auto)) as [n86 H86].
    iApply (wp_plet_int_bin _ _ _ _ _ _ _ _ _ _ _ _ L L (i_val mod 2 ^ 64) (n85 mod 2 ^ 64) n86 ti taint_all);
      try solve_plet_side.
    iNext.
    (* ‹j@L58› = add ‹j›, 1 *)
    assert (Hj1_mod : (j_start + 1) mod 2 ^ 64 = j_start + 1) by (apply Z.mod_small; lia).
    iApply (wp_plet_int_bin _ _ _ _ _ _ _ _ _ _ _ _ L L j_start 1 (j_start + 1) taint_bot taint_bot);
      try solve_plet_side;
      [cbn [alu cond_bit modulus]; rewrite Hj1_mod; reflexivity|].
    iNext.
    (* goto poll L28 *)
    iApply (wp_pgoto pol_strict cttable_ge).
    iNext.
    (* Enter L28 from L58 *)
    iApply (wp_penter pol_strict cttable_ge _ _ _ _ _ _ _ _ _);
      [reflexivity
      |cbn [b_phis phis_env fold_left lookup name_eqb term_eqb String.eqb Ascii.eqb Bool.eqb andb value_x word_at_class modulus];
        reflexivity
      |cbn [b_phis phis_tenv fold_left lookup name_eqb term_eqb String.eqb Ascii.eqb Bool.eqb andb value_t];
        reflexivity|].
    iNext.
    cbn [b_insts b_jump].
    (* Apply IH for j_start + 1 *)
    iApply (IH (j_start + 1) (n86 mod 2 ^ 64) (n82 mod 2 ^ 32)
      (taint_join ti taint_all)
      (taint_join tres (taint_join (taint_join taint_all texp_out) taint_all))
      with "Hlo Hxso Hpbso Hlp Hxsp Hpbsp").
    + lia.
    + lia.
    + repeat (rewrite lookup_put_other; [|reflexivity]);
        destruct (Hpres ‹win› ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
          ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
          ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)) as [H _];
        rewrite H; solve_lookup.
    + repeat (rewrite lookup_put_other; [|reflexivity]);
        destruct (Hpres ‹win› ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
          ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
          ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)) as [_ H];
        rewrite H; solve_lookup.
    + repeat (rewrite lookup_put_other; [|reflexivity]);
        destruct (Hpres ‹start› ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
          ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
          ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)) as [H _];
        rewrite H; solve_lookup.
    + repeat (rewrite lookup_put_other; [|reflexivity]);
        destruct (Hpres ‹start› ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
          ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
          ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)) as [_ H];
        rewrite H; solve_lookup.
    + repeat (rewrite lookup_put_other; [|reflexivity]);
        destruct (Hpres ‹tbl› ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
          ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
          ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)) as [H _];
        rewrite H; solve_lookup.
    + repeat (rewrite lookup_put_other; [|reflexivity]);
        destruct (Hpres ‹tbl› ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
          ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
          ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)) as [_ H];
        rewrite H; solve_lookup.
    + repeat (rewrite lookup_put_other; [|reflexivity]);
        destruct (Hpres ‹p› ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
          ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
          ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)) as [H _];
        rewrite H; solve_lookup.
    + repeat (rewrite lookup_put_other; [|reflexivity]);
        destruct (Hpres ‹p› ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
          ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
          ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)) as [_ H];
        rewrite H; solve_lookup.
    + solve_lookup.
    + solve_lookup.
    + solve_lookup.
    + solve_lookup.
    + solve_lookup.
    + solve_lookup.
Qed.

(** Full weakest-precondition specification of `scan_ct`: given ownership of
    `buf[0..len-1]` and an exact 16-byte `tbl[0..15]`, `scan_ct` finishes
    without panics or [pol_strict] poison faults and returns a secret integer. *)
Lemma scan_ct_spec b_buf cap_buf reg_buf buf_xs
    b_tbl cap_tbl reg_tbl tbl_xs dq pdq
    len win skip start :
  cap_buf = Obj b_buf \/ cap_buf = Ro b_buf ->
  cap_tbl = Obj b_tbl \/ cap_tbl = Ro b_tbl ->
  0 <= b_buf -> b_buf + len < 2 ^ 64 -> b_buf + len <= r_end reg_buf ->
  0 <= b_tbl -> b_tbl + 16 < 2 ^ 64 -> b_tbl + 16 <= r_end reg_tbl ->
  0 <= win -> win + 16 <= len ->
  length buf_xs = Z.to_nat len ->
  length tbl_xs = 16%nat ->
  ptsq dq [(PLive b_buf, VLive reg_buf)] -∗
  ptsq dq (bytes_ps b_buf 0 buf_xs) -∗
  pptsq pdq (pbytes_ps b_buf 0 (replicate (length buf_xs) (pb_secret taint_all))) -∗
  ptsq dq [(PLive b_tbl, VLive reg_tbl)] -∗
  ptsq dq (bytes_ps b_tbl 0 tbl_xs) -∗
  pptsq pdq (pbytes_ps b_tbl 0 (replicate 16 (pb_secret taint_all))) -∗
  WP (PRun (scan_ct_entry (mkPtr b_buf cap_buf) (mkPtr b_tbl cap_tbl) len win skip start)
        scan_ct_te : pexprL)
    {{ v, ∃ n t, ⌜v = (Ret (WInt n), [WTInt t])⌝ }}.
Proof using Type.
  intros Hcap_buf Hcap_tbl Hb_buf Hbuf_lim Hrend_buf Hb_tbl Htbl_lim Hrend_tbl
    Hwin Hlen_ge Hlen_buf Hlen_tbl.
  iIntros "Hlo Hxso Hpbso Hlp Hxsp Hpbsp".
  iApply (wp_penter pol_strict cttable_ge _ _ _ _ _ _ _ _ _);
    [reflexivity | reflexivity | reflexivity |].
  iNext.
  cbn [b_insts b_jump].
  assert (Hlen_mod : len mod 2 ^ 64 = len) by (apply Z.mod_small; lia).
  assert (Hwin_mod : win mod 2 ^ 64 = win) by (apply Z.mod_small; lia).
  (* v21 = ‹buf› +p ‹len› *)
  assert (Hm21 : (b_buf + len) mod 2 ^ 64 = b_buf + len) by (apply Z.mod_small; lia).
  iApply (wp_pflight pol_strict cttable_ge _ _ _ _ _ _ _ _ _ _ _
            [WInt b_buf; WInt len] [taint_bot; taint_bot] (b_buf + len) cap_buf taint_bot);
    [cbn; rewrite (Z.mod_small b_buf (2 ^ 64) ltac:(lia)) Hlen_mod; reflexivity
    |reflexivity
    |cbn [alu cond_bit modulus]; rewrite Hm21; reflexivity
    |reflexivity | reflexivity | reflexivity|].
  iNext.
  (* v23 = flight sub [address(v21), ‹win›] *)
  assert (Hm23 : (b_buf + len - win) mod 2 ^ 64 = b_buf + len - win) by (apply Z.mod_small; lia).
  iApply (wp_pflight pol_strict cttable_ge _ _ _ _ _ _ _ _ _ _ _
            [WInt (b_buf + len); WInt win] [taint_bot; taint_bot]
            (b_buf + len - win) cap_buf taint_bot);
    [cbn; rewrite Hm21 Hwin_mod; reflexivity
    |reflexivity | cbn [alu cond_bit modulus]; rewrite Hm23; reflexivity
    |reflexivity | reflexivity | reflexivity|].
  iNext.
  (* ‹p› = flight sub [address(v23), 16] *)
  set (p_off := len - win - 16).
  assert (Hm24 : (b_buf + len - win - 16) mod 2 ^ 64 = b_buf + p_off).
  { subst p_off. replace (b_buf + len - win - 16) with (b_buf + (len - win - 16)) by lia.
    apply Z.mod_small; lia. }
  iApply (wp_pflight pol_strict cttable_ge _ _ _ _ _ _ _ _ _ _ _
            [WInt (b_buf + len - win); WInt 16] [taint_bot; taint_bot]
            (b_buf + p_off) cap_buf taint_bot);
    [cbn; rewrite Hm23; reflexivity
    |reflexivity | cbn [alu cond_bit modulus]; rewrite Hm24; reflexivity
    |reflexivity | reflexivity | reflexivity|].
  iNext.
  (* goto L28 *)
  iApply (wp_pgoto pol_strict cttable_ge).
  iNext.
  (* Enter L28 from start *)
  iApply (wp_penter pol_strict cttable_ge _ _ _ _ _ _ _ _ _);
    [reflexivity | reflexivity | reflexivity |].
  iNext.
  cbn [b_insts b_jump].
  iApply (scan_ct_outer_spec b_buf cap_buf reg_buf buf_xs
            b_tbl cap_tbl reg_tbl tbl_xs dq pdq
            len win start p_off
            (Z.to_nat (win + 16)) 0 0 0 taint_bot taint_bot _ _
            Hcap_buf Hcap_tbl Hb_buf Hbuf_lim Hrend_buf Hb_tbl Htbl_lim Hrend_tbl
            Hwin Hlen_ge eq_refl Hlen_buf Hlen_tbl ltac:(lia) ltac:(lia)
            with "Hlo Hxso Hpbso Hlp Hxsp Hpbsp");
    try (cbn [lookup]; unfold name_eqb; cbn [term_eqb]; reflexivity).
Qed.

End proof.

(** ## From one-run Iris safety to universal two-run constant time

    Instantiating the Iris ghost heaps once eliminates every logical parameter
    and lifts [scan_ct_spec] to ordinary machine adequacy. Any two runs with
    different secret `skip`, `start`, `buf` bytes, and `tbl` bytes then emit
    the identical plain operational leakage trace under [pol_strict]. *)

Definition cttableΣ : gFunctors := #[invΣ; gen_heapΣ piece pval; gen_heapΣ ppiece ppval].
Local Instance cttableΣ_inv : invGpreS cttableΣ.
Proof. apply subG_invΣ. apply _. Qed.
Local Instance cttableΣ_heap : gen_heapGpreS piece pval cttableΣ.
Proof. apply subG_gen_heapGpreS. apply _. Qed.
Local Instance cttableΣ_poison : gen_heapGpreS ppiece ppval cttableΣ.
Proof. apply subG_gen_heapGpreS. apply _. Qed.

(** Disjoint objects have non-overlapping value pieces for adequacy setup. *)
Lemma NoDup_two_slices b_buf reg_buf buf_xs b_tbl reg_tbl tbl_xs :
  b_buf <> b_tbl ->
  NoDup ((((PLive b_buf, VLive reg_buf) :: bytes_ps b_buf 0 buf_xs) ++
          ((PLive b_tbl, VLive reg_tbl) :: bytes_ps b_tbl 0 tbl_xs)).*1).
Proof.
  intros Hne. rewrite fmap_app. apply NoDup_app.
  repeat split.
  - cbn. apply NoDup_cons; split; [apply live_not_in_bytes_ps | apply NoDup_bytes_ps].
  - intros l Hin1 Hin2. cbn in Hin1, Hin2.
    apply elem_of_cons in Hin1 as [-> | Hin1];
      apply elem_of_cons in Hin2 as [H2 | Hin2].
    + injection H2; congruence.
    + exact (live_not_in_bytes_ps _ _ _ _ Hin2).
    + subst l. exact (live_not_in_bytes_ps _ _ _ _ Hin1).
    + pose proof (bytes_ps_piece_id _ _ _ _ Hin1) as H1.
      pose proof (bytes_ps_piece_id _ _ _ _ Hin2) as H2. congruence.
  - cbn. apply NoDup_cons; split; [apply live_not_in_bytes_ps | apply NoDup_bytes_ps].
Qed.

(** Disjoint objects have non-overlapping poison pieces for adequacy setup. *)
Lemma NoDup_two_pslices b_buf pbs_buf b_tbl pbs_tbl :
  b_buf <> b_tbl ->
  NoDup ((pbytes_ps b_buf 0 pbs_buf ++ pbytes_ps b_tbl 0 pbs_tbl).*1).
Proof.
  intros Hne. rewrite fmap_app. apply NoDup_app.
  repeat split.
  - apply NoDup_pbytes_ps.
  - intros l Hin1 Hin2.
    pose proof (pbytes_ps_ppiece_id _ _ _ _ Hin1) as H1.
    pose proof (pbytes_ps_ppiece_id _ _ _ _ Hin2) as H2. congruence.
  - apply NoDup_pbytes_ps.
Qed.

(** Building the byte list from a memory region records every byte in `[0, n)`. *)
Definition read_bytes_list (m : mem) (b : Z) (n : nat) : list Z :=
  map (fun k => m_bytes m (b + Z.of_nat k)) (seq 0 n).

Lemma length_read_bytes_list m b n :
  length (read_bytes_list m b n) = n.
Proof. unfold read_bytes_list. rewrite length_map length_seq. reflexivity. Qed.

Lemma nth_error_read_bytes_list m b n k x :
  nth_error (read_bytes_list m b n) k = Some x ->
  m_bytes m (b + 0 + Z.of_nat k) = x.
Proof.
  unfold read_bytes_list. rewrite nth_error_map.
  destruct (nth_error (seq 0 n) k) as [j|] eqn:Ej; [|discriminate].
  cbn. intros [= <-].
  assert (Hk : (k < n)%nat).
  { destruct (Nat.lt_ge_cases k n); [exact H|].
    rewrite (proj2 (nth_error_None (seq 0 n) k) ltac:(rewrite length_seq; lia)) in Ej.
    discriminate Ej. }
  assert (Heq : j = k).
  { assert (Hgen : forall s k j, nth_error (seq s n) k = Some j -> j = (s + k)%nat).
    { clear k j Ej Hk. induction n as [|n IH]; intros s [|k] j Ej; cbn in Ej; try discriminate.
      - injection Ej as <-. lia.
      - pose proof (IH (S s) k j Ej). lia. }
    pose proof (Hgen 0%nat k j Ej). lia. }
  subst j. rewrite Z.add_0_r. reflexivity.
Qed.

(** Every valid call to `scan_ct` avoids panics and [pol_strict] poison
    faults across all reachable machine states and finite driver runs. *)
Theorem scan_ct_safe b_buf cap_buf reg_buf b_tbl cap_tbl reg_tbl
    len win skip start m pm paux s fuel :
  b_buf <> b_tbl ->
  cap_buf = Obj b_buf \/ cap_buf = Ro b_buf ->
  cap_tbl = Obj b_tbl \/ cap_tbl = Ro b_tbl ->
  R.ready s m -> live_disjoint m ->
  live_at m b_buf reg_buf -> live_at m b_tbl reg_tbl ->
  0 <= b_buf -> b_buf + len < 2 ^ 64 -> b_buf + len <= r_end reg_buf ->
  0 <= b_tbl -> b_tbl + 16 < 2 ^ 64 -> b_tbl + 16 <= r_end reg_tbl ->
  0 <= win -> win + 16 <= len ->
  (forall k, 0 <= k < len -> pm (b_buf + k) = pb_secret taint_all) ->
  (forall k, 0 <= k < 16 -> pm (b_tbl + k) = pb_secret taint_all) ->
  poison_safe pol_strict cttable_ge
    (scan_ct_entry (mkPtr b_buf cap_buf) (mkPtr b_tbl cap_tbl) len win skip start)
    scan_ct_te m pm paux s fuel.
Proof.
  intros Hne Hcap_buf Hcap_tbl Hr Hd Hlv_buf Hlv_tbl
    Hb_buf Hbuf_lim Hrend_buf Hb_tbl Htbl_lim Hrend_tbl
    Hwin Hlen_ge Hpm_buf Hpm_tbl.
  set (buf_xs := read_bytes_list m b_buf (Z.to_nat len)).
  set (tbl_xs := read_bytes_list m b_tbl 16%nat).
  set (ps := ((PLive b_buf, VLive reg_buf) :: bytes_ps b_buf 0 buf_xs) ++
             ((PLive b_tbl, VLive reg_tbl) :: bytes_ps b_tbl 0 tbl_xs)).
  set (pps := pbytes_ps b_buf 0 (replicate (length buf_xs) (pb_secret taint_all)) ++
              pbytes_ps b_tbl 0 (replicate 16 (pb_secret taint_all))).
  apply (wp_poison_safe _ _ _ _ _ _ _ _ _
    (fun v _ => exists n t, v = (Ret (WInt n), [WTInt t]))).
  apply (poison_pieces_adequate cttableΣ pol_strict cttable_ge _ _ _ _ _ _ fuel ps pps
    (fun v => exists n t, v = (Ret (WInt n), [WTInt t])));
    try assumption.
  - apply all_agree_app; split; cbn [all_agree]; split.
    + exact Hlv_buf.
    + apply (all_agree_bytes_ps m b_buf reg_buf 0 buf_xs Hlv_buf ltac:(lia));
        [subst buf_xs; rewrite length_read_bytes_list; lia
        |intros k x Hk; exact (nth_error_read_bytes_list m b_buf (Z.to_nat len) k x Hk)].
    + exact Hlv_tbl.
    + apply (all_agree_bytes_ps m b_tbl reg_tbl 0 tbl_xs Hlv_tbl ltac:(lia));
        [subst tbl_xs; rewrite length_read_bytes_list; lia
        |intros k x Hk; exact (nth_error_read_bytes_list m b_tbl 16%nat k x Hk)].
  - apply all_p_agree_app; split.
    + apply (all_p_agree_pbytes_ps m pm paux b_buf reg_buf 0 _ Hlv_buf ltac:(lia)).
      * subst buf_xs. rewrite length_replicate length_read_bytes_list. lia.
      * intros k pb Hk.
        assert (Hlt : (k < length buf_xs)%nat).
        { destruct (Nat.lt_ge_cases k (length buf_xs)); [exact H|].
          rewrite (proj2 (nth_error_None (replicate (length buf_xs) (pb_secret taint_all)) k)
            ltac:(rewrite length_replicate; lia)) in Hk.
          discriminate Hk. }
        pose proof (nth_error_replicate_inv _ _ _ _ Hk) as ->.
        rewrite Z.add_0_r. apply Hpm_buf. subst buf_xs; rewrite length_read_bytes_list in Hlt; lia.
    + apply (all_p_agree_pbytes_ps m pm paux b_tbl reg_tbl 0 _ Hlv_tbl ltac:(lia)).
      * rewrite length_replicate. lia.
      * intros k pb Hk.
        assert (Hlt : (k < 16)%nat).
        { destruct (Nat.lt_ge_cases k 16); [exact H|].
          rewrite (proj2 (nth_error_None (replicate 16 (pb_secret taint_all)) k)
            ltac:(rewrite length_replicate; lia)) in Hk.
          discriminate Hk. }
        pose proof (nth_error_replicate_inv _ _ _ _ Hk) as ->.
        rewrite Z.add_0_r. apply Hpm_tbl. lia.
  - apply NoDup_two_slices; exact Hne.
  - apply NoDup_two_pslices; exact Hne.
  - intros Hinv Hheap Hpoison. simpl.
    iIntros "Hps Hpps".
    subst ps pps.
    rewrite !pts_ptsq !ppts_pptsq !ptsq_app !pptsq_app.
    iDestruct "Hps" as "[Hbuf Htbl]".
    iDestruct "Hpps" as "[Hpbuf Hptbl]".
    change ((PLive b_buf, VLive reg_buf) :: bytes_ps b_buf 0 buf_xs)
      with ([(PLive b_buf, VLive reg_buf)] ++ bytes_ps b_buf 0 buf_xs).
    change ((PLive b_tbl, VLive reg_tbl) :: bytes_ps b_tbl 0 tbl_xs)
      with ([(PLive b_tbl, VLive reg_tbl)] ++ bytes_ps b_tbl 0 tbl_xs).
    rewrite !ptsq_app.
    iDestruct "Hbuf" as "[Hlo Hxso]".
    iDestruct "Htbl" as "[Hlp Hxsp]".
    iApply (wp_wand with "[Hlo Hxso Hpbuf Hlp Hxsp Hptbl]").
    + iApply (scan_ct_spec b_buf cap_buf reg_buf buf_xs
                b_tbl cap_tbl reg_tbl tbl_xs (DfracOwn 1) (DfracOwn 1)
                len win skip start
                Hcap_buf Hcap_tbl Hb_buf Hbuf_lim Hrend_buf Hb_tbl Htbl_lim Hrend_tbl
                Hwin Hlen_ge
                ltac:(subst buf_xs; apply length_read_bytes_list)
                ltac:(subst tbl_xs; apply length_read_bytes_list)
                with "Hlo Hxso Hpbuf Hlp Hxsp Hptbl").
    + iIntros (v) "H". iDestruct "H" as (n t) "%H". eauto.
Qed.

(** Universal two-run constant-time theorem for `scan_ct`: for every public
    `len` and `win` (`win + 16 <= len`), any two executions differing in
    secret `skip`, `start`, `buf` bytes, or exact 16-byte `tbl` bytes emit
    the identical plain operational leakage trace under [pol_strict]. *)
Theorem scan_ct_constant_time b_buf cap_buf reg_buf b_tbl cap_tbl reg_tbl
    len win skip1 start1 skip2 start2 m1 m2 pm paux s fuel :
  b_buf <> b_tbl ->
  cap_buf = Obj b_buf \/ cap_buf = Ro b_buf ->
  cap_tbl = Obj b_tbl \/ cap_tbl = Ro b_tbl ->
  R.ready s m1 -> R.ready s m2 -> live_disjoint m1 ->
  live_at m1 b_buf reg_buf -> live_at m1 b_tbl reg_tbl ->
  0 <= b_buf -> b_buf + len < 2 ^ 64 -> b_buf + len <= r_end reg_buf ->
  0 <= b_tbl -> b_tbl + 16 < 2 ^ 64 -> b_tbl + 16 <= r_end reg_tbl ->
  0 <= win -> win + 16 <= len ->
  (forall k, 0 <= k < len -> pm (b_buf + k) = pb_secret taint_all) ->
  (forall k, 0 <= k < 16 -> pm (b_tbl + k) = pb_secret taint_all) ->
  m_regions m1 = m_regions m2 ->
  (forall a, m_bytes m1 a <> m_bytes m2 a -> pb_taint (pm a) = taint_all) ->
  (forall a, m_aux m1 a <> m_aux m2 a -> paux a = taint_all) ->
  forall steps, exists tr,
    PD.driver_trace pol_strict cttable_ge steps
      (mkConfig (scan_ct_entry (mkPtr b_buf cap_buf) (mkPtr b_tbl cap_tbl) len win skip1 start1) [] m1 fuel) s = Some tr /\
    PD.driver_trace pol_strict cttable_ge steps
      (mkConfig (scan_ct_entry (mkPtr b_buf cap_buf) (mkPtr b_tbl cap_tbl) len win skip2 start2) [] m2 fuel) s = Some tr.
Proof.
  intros Hne Hcap_buf Hcap_tbl Hr1 Hr2 Hd Hlv_buf Hlv_tbl
    Hb_buf Hbuf_lim Hrend_buf Hb_tbl Htbl_lim Hrend_tbl
    Hwin Hlen_ge Hpm_buf Hpm_tbl Hreg Hbytes Haux steps.
  eapply (wp_ct_driver_plain pol_strict cttable_ge
            (scan_ct_entry (mkPtr b_buf cap_buf) (mkPtr b_tbl cap_tbl) len win skip1 start1)
            (scan_ct_entry (mkPtr b_buf cap_buf) (mkPtr b_tbl cap_tbl) len win skip2 start2)
            scan_ct_te m1 m2 pm paux s fuel);
    try reflexivity; try assumption.
  - apply scan_ct_inputs_related; assumption.
  - apply (scan_ct_safe b_buf cap_buf reg_buf b_tbl cap_tbl reg_tbl
      len win skip1 start1 m1 pm paux s fuel); assumption.
Qed.

End CtTableScan.

(** ## Separating single-run taint from two-run noninterference

    Optimizing compilers sometimes rebase a public loop induction variable by a
    secret offset, computing `base = buf + sec`, `lim = len - sec`, and
    `k = j - sec`. Single-run dynamic taint flags both `base + k` and `k == lim`
    as secret-dependent even though the secret cancels modulo 2^64 at every
    step.

    The minimal validated IR function below models
    this transformation and proves both sides of the separation: single-run
    poison tracking rejects it with both [CannotBranch] and [CannotIndex],
    whereas its plain two-run operational leakage trace is provably identical
    for all secrets. *)

(** Minimal checked-IR loop rebasing both the base pointer and the loop counter
    by the secret offset `sec`. *)
Definition rebased_scan_fn : func :=
  mkFunc (TAtom "rebased_scan") (TAtom "export") (RClass W)
    [(P, TAtom "buf"); (L, TAtom "len"); (L, TAtom "sec")]
    [mkBlock (TAtom "start") []
       [Flight (TAtom "base") Add [FAddress (Tmp (TAtom "buf")); FValue (Tmp (TAtom "sec"))] (LowerOf (Tmp (TAtom "buf")));
        Let (TAtom "lim") L Sub [Tmp (TAtom "len"); Tmp (TAtom "sec")];
        Let (TAtom "k0") L Sub [Const 0; Tmp (TAtom "sec")]]
       (JGoto (To (TAtom "loop")));
     mkBlock (TAtom "loop")
       [Phi (TAtom "k") L [(TAtom "start", Tmp (TAtom "k0")); (TAtom "body", Tmp (TAtom "k1"))];
        Phi (TAtom "acc") W [(TAtom "start", Const 0); (TAtom "body", Tmp (TAtom "acc1"))]]
       [Let (TAtom "done") W (Cmp Eq L) [Tmp (TAtom "k"); Tmp (TAtom "lim")]]
       (JBranch (Tmp (TAtom "done")) (To (TAtom "exit")) (To (TAtom "body")));
     mkBlock (TAtom "body") []
       [Flight (TAtom "addr") Add [FAddress (Tmp (TAtom "base")); FValue (Tmp (TAtom "k"))] (LowerOf (Tmp (TAtom "base")));
        Let (TAtom "chk") A (Check 0 1 Read 1) [Tmp (TAtom "addr")];
        Let (TAtom "b") W (RawLoad (LdNarrow Ub) 0) [Tmp (TAtom "chk")];
        Let (TAtom "acc1") W Xor [Tmp (TAtom "acc"); Tmp (TAtom "b")];
        Let (TAtom "k1") L Add [Tmp (TAtom "k"); Const 1]]
       (JGoto (Poll (TAtom "loop")));
     mkBlock (TAtom "exit") [] []
       (JRet (Tmp (TAtom "acc")))].

Definition rebased_module : module := [IFunc rebased_scan_fn].
Definition rebased_ge : genv := mkGenv rebased_module [] free_res.

(** Campaign 1's [[validator]] accepts [rebased_scan_fn]. *)
Theorem rebased_scan_valid : valid rebased_module = Some true.
Proof. vm_compute. reflexivity. Qed.

Definition rebased_entry (p_buf : ptr) (len sec : Z) : frame :=
  mkFrame rebased_scan_fn
    [(TAtom "sec", WInt sec); (TAtom "len", WInt len); (TAtom "buf", WPtr p_buf)]
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

(** Modular cancellation identities modulo 2^64 that make the rebased loop's
    exit comparison and dereferenced address independent of `sec`. *)
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
    { rewrite Zminus_mod Heq Z.sub_diag Zmod_0_l. reflexivity. }
    replace ((a - s) - (b - s)) with (a - b) in Hdiff by lia.
    apply Z.mod_divide in Hdiff; [|lia].
    destruct Hdiff as [q Hq].
    assert (Hq0 : q = 0) by nia. lia.
Qed.

Lemma mod64_cancel_add (b s j : Z) :
  (((b + s) mod 2 ^ 64) + ((j - s) mod 2 ^ 64)) mod 2 ^ 64 = (b + j) mod 2 ^ 64.
Proof.
  rewrite -Zplus_mod.
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
  intros Hl Hs1 Hs2 Hrest. cbn [run_trace]. rewrite Hs1 Hs2 Hl Hrest. reflexivity.
Qed.

Lemma run_trace_done_eq pol ge n c1 c2 o1 o2 :
  leak_of pol ge c1 = leak_of pol ge c2 ->
  Semantics.step ge c1 = Done o1 ->
  Semantics.step ge c2 = Done o2 ->
  run_trace pol ge (S n) c1 = run_trace pol ge (S n) c2.
Proof.
  intros Hl Hs1 Hs2. cbn [run_trace]. rewrite Hs1 Hs2 Hl. reflexivity.
Qed.

(** Loop-level simulation: at the start of any iteration `j`, two rebased
    executions with arbitrary secrets `s1` and `s2` emit the exact same plain
    [run_trace] under any policy [pol]. *)
Lemma rebased_loop_traces_equal pol b cap reg m len s1 s2 :
  cap = Obj b \/ cap = Ro b ->
  live_at m b reg ->
  0 <= b -> 0 <= len -> b + len < 2 ^ 64 -> b + len <= r_end reg ->
  forall steps j acc fuel e1 e2,
    0 <= j <= len ->
    lookup (TAtom "base") e1 = Some (WPtr (mkPtr ((b + s1) mod 2 ^ 64) cap)) ->
    lookup (TAtom "lim") e1 = Some (WInt ((len - s1) mod 2 ^ 64)) ->
    lookup (TAtom "k") e1 = Some (WInt ((j - s1) mod 2 ^ 64)) ->
    lookup (TAtom "acc") e1 = Some (WInt acc) ->
    lookup (TAtom "base") e2 = Some (WPtr (mkPtr ((b + s2) mod 2 ^ 64) cap)) ->
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
  intros Hcap Hlv Hb Hlen Hblim Hrend steps.
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
    + cbn [map2_option value_x]; rewrite Hk1 Hlim1; cbn [word_at_class modulus];
        rewrite Hmod_k1 Hmod_l1; reflexivity.
    + unfold op_res, op_res_int; cbn; rewrite Hcmp1; reflexivity.
  - apply (rule_let _ _ _ _ _ _ _ _ _ _ _ _ _ _ [L; L]
      [WInt ((j - s2) mod 2 ^ 64); WInt ((len - s2) mod 2 ^ 64)] (WInt done_val) m);
      try reflexivity.
    + cbn [map2_option value_x]; rewrite Hk2 Hlim2; cbn [word_at_class modulus];
        rewrite Hmod_k2 Hmod_l2; reflexivity.
    + unfold op_res, op_res_int; cbn; rewrite Hcmp2; reflexivity.
  - destruct n1 as [|n2]; [reflexivity|].
    destruct (Z.eqb_spec j len) as [-> | Hj_ne]; subst done_val; cbn [Z.eqb] in *.
    + eapply run_trace_step_eq.
      * cbn [leak_of c_frame fr_at fr_env value_x]; rewrite !lookup_put_same; reflexivity.
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
      * cbn [leak_of c_frame fr_at fr_env value_x]; rewrite !lookup_put_same; reflexivity.
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
        assert (Hbj : (b + j) mod 2 ^ 64 = b + j) by (apply Z.mod_small; lia).
        assert (Hadd1 : (((b + s1) mod 2 ^ 64) + ((j - s1) mod 2 ^ 64)) mod 2 ^ 64 = b + j)
          by (rewrite mod64_cancel_add; exact Hbj).
        assert (Hadd2 : (((b + s2) mod 2 ^ 64) + ((j - s2) mod 2 ^ 64)) mod 2 ^ 64 = b + j)
          by (rewrite mod64_cancel_add; exact Hbj).
        assert (Hbs1 : ((b + s1) mod 2 ^ 64) mod 2 ^ 64 = (b + s1) mod 2 ^ 64) by apply Zmod_mod.
        assert (Hbs2 : ((b + s2) mod 2 ^ 64) mod 2 ^ 64 = (b + s2) mod 2 ^ 64) by apply Zmod_mod.
        eapply run_trace_step_eq; [reflexivity | | |].
        -- apply (rule_flight _ _ _ _ _ _ _ _ _ _ _ _ _ _
             [WInt ((b + s1) mod 2 ^ 64); WInt ((j - s1) mod 2 ^ 64)] (b + j) cap).
           ++ cbn [map_option flight_arg_x value_x];
              repeat (rewrite lookup_put_other; [|reflexivity]);
              rewrite Hbase1 Hk1;
              cbn [word_at_class modulus ptr_addr]; rewrite Hbs1 Hmod_k1; reflexivity.
           ++ cbn [alu cond_bit modulus]; rewrite Hadd1; reflexivity.
           ++ cbn [flight_cap value_x]; repeat (rewrite lookup_put_other; [|reflexivity]); rewrite Hbase1; reflexivity.
        -- apply (rule_flight _ _ _ _ _ _ _ _ _ _ _ _ _ _
             [WInt ((b + s2) mod 2 ^ 64); WInt ((j - s2) mod 2 ^ 64)] (b + j) cap).
           ++ cbn [map_option flight_arg_x value_x];
              repeat (rewrite lookup_put_other; [|reflexivity]);
              rewrite Hbase2 Hk2;
              cbn [word_at_class modulus ptr_addr]; rewrite Hbs2 Hmod_k2; reflexivity.
           ++ cbn [alu cond_bit modulus]; rewrite Hadd2; reflexivity.
           ++ cbn [flight_cap value_x]; repeat (rewrite lookup_put_other; [|reflexivity]); rewrite Hbase2; reflexivity.
        -- destruct n4 as [|n5]; [reflexivity|].
           assert (Hchk_ok : access_res m (raw_address (b + j) 0) cap 1 Read 1 = Some (RVal tt)).
           { unfold access_res, raw_address; rewrite Z.add_0_r Hbj.
             destruct Hlv as [Hobj _].
             destruct Hcap as [-> | ->]; unfold cap_access_res, readonly_access_res, aligned_res;
               rewrite Hobj;
               replace (b <=? b + j) with true by (symmetry; apply Z.leb_le; lia);
               replace (b + j + 1 <=? r_end reg) with true by (symmetry; apply Z.leb_le; lia);
               rewrite Z.mod_1_r; reflexivity. }
           eapply run_trace_step_eq.
           ++ cbn [leak_of c_frame fr_at fr_env value_x]; rewrite !lookup_put_same; reflexivity.
           ++ apply (rule_let _ _ _ _ _ _ _ _ _ _ _ _ _ _ [P] [WPtr (mkPtr (b + j) cap)] (WPtr (mkPtr (b + j) cap)) m);
                try reflexivity;
                cbn [op_res op_res_int ptr_addr ptr_cap]; rewrite Hchk_ok; reflexivity.
           ++ apply (rule_let _ _ _ _ _ _ _ _ _ _ _ _ _ _ [P] [WPtr (mkPtr (b + j) cap)] (WPtr (mkPtr (b + j) cap)) m);
                try reflexivity;
                cbn [op_res op_res_int ptr_addr ptr_cap]; rewrite Hchk_ok; reflexivity.
           ++ destruct n5 as [|n6]; [reflexivity|].
              set (bv := (m_bytes m (b + j) mod 256) mod 2 ^ 32).
              assert (Hload_ok : int_load_res (LdNarrow Ub) W m (raw_address (b + j) 0) cap = Some (RVal (WInt bv))).
              { unfold int_load_res; cbn [fst narrow_type]; rewrite Hchk_ok.
                unfold load_bytes, raw_address, extended, extension; cbn [modulus].
                rewrite Z.add_0_r Hbj. change (Z.to_nat 1) with 1%nat.
                cbn; rewrite Z.add_0_r; reflexivity. }
              eapply run_trace_step_eq.
              ** cbn [leak_of c_frame fr_at fr_env value_x]; rewrite !lookup_put_same; reflexivity.
              ** apply (rule_let _ _ _ _ _ _ _ _ _ _ _ _ _ _ [A] [WPtr (mkPtr (b + j) cap)] (WInt bv) m);
                   try reflexivity;
                   cbn [op_res op_res_int ptr_addr ptr_cap]; rewrite Hload_ok; reflexivity.
              ** apply (rule_let _ _ _ _ _ _ _ _ _ _ _ _ _ _ [A] [WPtr (mkPtr (b + j) cap)] (WInt bv) m);
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
    [pol], any live buffer of length `len`, and any two secret offsets `s1` and
    `s2`, both executions emit the identical plain operational trace. Together
    with [rebased_scan_taint_rejects], this formally separates single-run
    dynamic taint from two-run constant-time noninterference. *)
Theorem rebased_scan_two_run_constant_time pol b cap reg m len s1 s2 fuel steps :
  cap = Obj b \/ cap = Ro b ->
  live_at m b reg ->
  0 <= b -> 0 <= len -> b + len < 2 ^ 64 -> b + len <= r_end reg ->
  run_trace pol rebased_ge steps (mkConfig (rebased_entry (mkPtr b cap) len s1) [] m fuel) =
  run_trace pol rebased_ge steps (mkConfig (rebased_entry (mkPtr b cap) len s2) [] m fuel).
Proof.
  intros Hcap Hlv Hb Hlen Hblim Hrend.
  assert (Hb_mod : b mod 2 ^ 64 = b) by (apply Z.mod_small; lia).
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
  - apply (rule_flight _ _ _ _ _ _ _ _ _ _ _ _ _ _ [WInt b; WInt (s1 mod 2 ^ 64)] ((b + s1) mod 2 ^ 64) cap);
      [cbn [map_option flight_arg_x value_x lookup name_eqb term_eqb String.eqb Ascii.eqb Bool.eqb andb word_at_class modulus ptr_addr];
        rewrite Hb_mod; reflexivity
      |cbn [alu cond_bit modulus]; rewrite Zplus_mod_idemp_r; reflexivity
      |cbn [flight_cap value_x lookup name_eqb term_eqb String.eqb Ascii.eqb Bool.eqb andb]; reflexivity].
  - apply (rule_flight _ _ _ _ _ _ _ _ _ _ _ _ _ _ [WInt b; WInt (s2 mod 2 ^ 64)] ((b + s2) mod 2 ^ 64) cap);
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
        eapply (rebased_loop_traces_equal pol b cap reg m len s1 s2 Hcap Hlv Hb Hlen Hblim Hrend
                  n6 0 0 (fuel - 1 - 1));
          first
            [ lia
            | repeat (first [rewrite lookup_put_same | rewrite lookup_put_other; [|reflexivity]]);
              cbn [lookup name_eqb term_eqb String.eqb Ascii.eqb Bool.eqb andb];
              rewrite ?Zmod_mod; reflexivity ].
Qed.
