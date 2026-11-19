(** Glibc reads the environment counter and environment pointer before testing
    the name's first byte. A null environment therefore returns without
    reading the name. This proof retains readable name ownership because a
    general caller must also support executions with a nonempty environment.

    The proof does not cover concurrent changes to the environment. It follows
    the generated instructions: the counter load is ordinary, whereas the
    pointer load is atomic. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run
  Machine Pieces Heap Language Logic ExternalCalls StepRules.
From Glibc Require Import Unit_stdlib_getenv_os.
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics WordString.
Import ListNotations LG0 LG0.L ProgramAbbreviations.
Open Scope Z_scope.

(** The checked function accepts exactly one pointer argument. *)
Definition getenv_frame p :=
  mkFrame Unit_stdlib_getenv_os.fn___GI_getenv [(TAtom "v0", WPtr p)] [] None (Enter (TAtom "start") None).

(** This frame is the actual result of binding the captured call's arguments. *)
Lemma getenv_call_frame p : call_frame Unit_stdlib_getenv_os.fn___GI_getenv [WPtr p] = Some (getenv_frame p).
Proof. reflexivity. Qed.

Section entry.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Instance getenv_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** Reading an atomic pointer cell needs its address bytes, shadow capability,
    and the target's lifetime. All three shares survive the instruction. *)
Lemma getenv_atomic_load f e ls l d off args rest j classes p b reg o x reg' dq1 dq2 dq3 Φ :
  op_arg_classes (RawLoadPointer off [AtomicRead]) P = Some classes ->
  map2_option (value_x ge e) classes args = Some [WPtr p] ->
  ptr_cap p = Obj b \/ ptr_cap p = Ro b ->
  raw_address (ptr_addr p) off = b + o -> (b + o) mod 8 = 0 ->
  0 <= ptr_addr x < 2 ^ 64 ->
  liveq dq1 b reg -∗ pcellq dq2 b o x -∗ live_capq dq3 (ptr_cap x) reg' -∗
  ▷ (liveq dq1 b reg -∗ pcellq dq2 b o x -∗ live_capq dq3 (ptr_cap x) reg' -∗
     WP (ERun (mkFrame f (put d (WPtr x) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
       (Exec l (Let d P (RawLoadPointer off [AtomicRead]) args :: rest) j)) : gexpr) {{ Φ }}.
Proof using Type.
  intros Hc Hx Hp Ha Hal Hrange. iIntros "Hl Hc Hcap HK".
  iApply (wp_read_with registry (os_wi w0) ge
            (liveq dq1 b reg ∗ pcellq dq2 b o x ∗ live_capq dq3 (ptr_cap x) reg')%I
            (fun m => live_at m b reg /\ agree_piece m (PAux b o) (VAux (ptr_cap x)) /\
                      all_agree m (cell b o (ptr_addr x)) /\ ~ freed_in (m_regions m) (ptr_cap x))
            _ _ [] with "[$Hl $Hc $Hcap] [HK]").
  - iIntros (σ) "Hσ (Hl & Hc & Hcap)".
    iDestruct (ptsq_facts with "Hσ Hl") as %([Hlv _] & _).
    iDestruct (ptsq_facts with "Hσ Hc") as %([Hax Hcl] & _).
    iDestruct (live_capq_facts with "Hσ Hcap") as %Hkept. iPureIntro. auto.
  - intros m fuel (Hlv & Hax & Hcl & Hkept).
    destruct (cell_bounds _ _ _ _ _ Hlv Hcl) as [Ho He].
    apply rule_let with (classes := classes) (xs := [WPtr p]);
      [reflexivity | exact Hc | exact Hx |].
    apply op_raw_load_pointer.
    + rewrite Ha. apply (access_read _ b reg);
        [exact Hp | exact (proj1 Hlv) | lia | lia | exact Hal].
    + replace (pointer_load_effects m (raw_address (ptr_addr p) off) [AtomicRead])
        with (Some (mkPtr (load_bytes m (raw_address (ptr_addr p) off) 8)
                         (aux_at m (raw_address (ptr_addr p) off)))) by reflexivity.
      rewrite Ha (cell_load m b reg o (ptr_addr x) (b + o) Hlv Hcl eq_refl).
      rewrite Z.mod_small; [|exact Hrange]. unfold aux_at.
      rewrite (aux_holds_kept _ _ _ (aux_piece_holds _ _ _ _ _ Hlv Hax) Hkept).
      destruct x; reflexivity.
  - iNext. iIntros "(Hl & Hc & Hcap)". iApply ("HK" with "Hl Hc Hcap").
Qed.

(** The global cells retain their read shares and exact values. The environment
    cell includes its shadow [[capability]], not just the pointer's address. *)
Definition getenv_globals dq bc rc be re counter ep : iProp Σ :=
  liveq dq bc rc ∗ icellq dq bc 0 counter ∗ liveq dq be re ∗ pcellq dq be 0 ep.

(** A parser may request this contract for its readable POSIXLY_CORRECT literal.
    Its resource G must account for the environment; this definition does not
    supply a proof of traversal or permit arbitrary unreadable arguments. *)
Definition getenv_name_contract (G : iProp Σ) p s : iProp Σ :=
  □ (word_string DfracDiscarded p s -∗ G -∗
     WP (ERun (getenv_frame p) : gexpr)
       {{ v, (∃ q, ⌜v = Ret (WPtr q)⌝ ∗ G)%I }}).

(** A null environment returns null after reading both globals. The arbitrary
    caller frame and readable name remain owned, together with both global
    cells. Nonempty environments still require a separate traversal proof. *)
Lemma getenv_empty p s dq bc rc be re counter (E : iProp Σ) Φ :
  lookup (TAtom "__environ_counter") (ge_globals ge) = Some (mkPtr bc (Obj bc)) ->
  lookup (TAtom "__environ") (ge_globals ge) = Some (mkPtr be (Obj be)) ->
  0 < bc -> bc + 8 <= r_end rc -> r_end rc <= 2 ^ 48 ->
  0 < be -> be + 8 <= r_end re -> r_end re <= 2 ^ 48 -> be mod 8 = 0 ->
  word_string DfracDiscarded p s -∗ getenv_globals dq bc rc be re counter null -∗ E -∗
  (word_string DfracDiscarded p s -∗ getenv_globals dq bc rc be re counter null -∗ E -∗
   Φ (Ret (WPtr null))) -∗
  WP (ERun (getenv_frame p) : gexpr) {{ Φ }}.
Proof using Type.
  intros Hcounter Henv Hbc Hrc Hrcmax Hbe Hre Hremax Hal.
  iIntros "#Hname (Hcl & Hcc & Hel & Hec) HE HK".
  unfold getenv_frame.
  step. step. step. step_global Hcounter.
  check_read_dq "Hcl" by (unfold raw_address; cbn; rewrite Z.add_0_r;
    rewrite Z.mod_small; lia).
  iNext. iIntros "Hcl".
  iApply (wp_raw_load_read_dq with "Hcl Hcc");
    [reflexivity | reflexivity | left; reflexivity |
     unfold raw_address; cbn; rewrite Z.add_0_r Z.mod_small; lia |].
  iNext. iIntros "Hcl Hcc". step_global Henv.
  check_read_dq "Hel" by (unfold raw_address; cbn; rewrite Z.add_0_r;
    rewrite (Z.mod_small be (2 ^ 64)); [first [lia | exact Hal] | lia]).
  iNext. iIntros "Hel".
  iAssert (live_capq dq (ptr_cap null) re) with "[]" as "Hnil"; [done |].
  iApply (getenv_atomic_load with "Hel Hec Hnil");
    [reflexivity | reflexivity | left; reflexivity |
     unfold raw_address; cbn; rewrite Z.add_0_r Z.mod_small; lia |
     rewrite Z.add_0_r; exact Hal | cbn; lia |].
  iNext. iIntros "Hel Hec _".
  step. step. step. branch. step. branch. step.
  iApply wp_ret; [reflexivity | reflexivity |]. iNext.
  iApply ("HK" with "Hname [Hcl Hcc Hel Hec] HE").
  iFrame.
Qed.

(** When the environment pointer is null, getenv satisfies the name contract
    without accessing other caller memory. The caller supplies both global
    cells as part of G. *)
Lemma getenv_empty_contract p s dq bc rc be re counter (E : iProp Σ) :
  lookup (TAtom "__environ_counter") (ge_globals ge) = Some (mkPtr bc (Obj bc)) ->
  lookup (TAtom "__environ") (ge_globals ge) = Some (mkPtr be (Obj be)) ->
  0 < bc -> bc + 8 <= r_end rc -> r_end rc <= 2 ^ 48 ->
  0 < be -> be + 8 <= r_end re -> r_end re <= 2 ^ 48 -> be mod 8 = 0 ->
  ⊢ getenv_name_contract (getenv_globals dq bc rc be re counter null ∗ E) p s.
Proof using Type.
  intros Hcounter Henv Hbc Hrc Hrcmax Hbe Hre Hremax Hal.
  iModIntro. iIntros "#Hname [HG HE]".
  iApply (getenv_empty with "Hname HG HE"); try eassumption.
  iIntros "_ HG HE". iExists null. iFrame. done.
Qed.
End entry.
