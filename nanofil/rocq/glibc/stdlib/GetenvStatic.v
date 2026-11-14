(** Glibc's getenv searches an unchanged environment for a readable name.
    The caller supplies the environment array and its strings, and keeps
    ownership after the call. This proof combines the global reads, name
    check, strlen call, and finite scan to establish that contract. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run
  Machine Pieces Heap Language Logic ExternalCalls StepRules Symbolic.
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics WordString
  GetoptBytes GetenvCode GetenvEntry GetenvName GetenvScan StrlenLogic StrlenWord StrncmpCode.
Import ListNotations LG0 LG0.L ProgramAbbreviations GetoptBytes GetoptBytes.ML.
Open Scope Z_scope.

(** Empty names return null before scanning any entries. Other names use
    the same comparison tests as the captured function. *)
Definition getenv_result (s : list Z) entries :=
  match s with [] => null | _ :: _ => getenv_scan_result s entries end.

Section storage.
Context `{!gen_heapGS piece pval Σ}.

(** The environment is either a null pointer or a live, null-terminated
    array. The array may contain no strings while still owning its sentinel. *)
Definition getenv_storage dq dqt ep entries : iProp Σ :=
  ⌜ep = null /\ entries = []⌝ ∨
  ∃ b reg o, ⌜ep = mkPtr (b + o) (Obj b)⌝ ∗ getenv_vector dq dqt b reg o entries.

(** The computed result is null or a readable suffix of an owned entry.
    Extracting that persistent read permission leaves the storage unchanged. *)
Lemma getenv_storage_value p s dq dqt ep entries :
  word_string DfracDiscarded p s -∗ getenv_storage dq dqt ep entries -∗
  getenv_storage dq dqt ep entries ∗ getenv_value (getenv_result s entries).
Proof.
  iIntros "#Hname HS". destruct s as [|a s].
  - iFrame. iLeft. done.
  - iDestruct "HS" as "[%Hnull | HS]".
    + destruct Hnull as [-> ->]. iSplit; iLeft; done.
    + iDestruct "HS" as (b reg o ->) "(%Hbounds & Hl & Hcells)".
      iDestruct (getenv_cells_value with "Hname Hcells") as "[Hcells Hv]"; [discriminate|].
      iFrame "Hv". iRight. iExists b, reg, o. iSplit; [done|].
      unfold getenv_vector. iFrame. done.
Qed.
End storage.

Section static.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context `{!Defines ge "__GI_strlen" glibc_strlen}.
Context `{!Defines ge "__GI_strncmp" glibc_strncmp}.
Local Instance getenv_static_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** Loading the environment pointer requires evidence that its array still
    exists. The proof borrows that evidence for the load and returns it
    before scanning. It also keeps the counter readable and unchanged. *)
Lemma getenv_static_nonnull p s entries dq dqa dqt bc rc be re counter b reg o (E : iProp Σ) Φ :
  lookup (TAtom "__environ_counter") (ge_globals ge) = Some (mkPtr bc (Obj bc)) ->
  lookup (TAtom "__environ") (ge_globals ge) = Some (mkPtr be (Obj be)) ->
  0 < bc -> bc + 8 <= r_end rc -> r_end rc <= 2 ^ 48 ->
  0 < be -> be + 8 <= r_end re -> r_end re <= 2 ^ 48 -> be mod 8 = 0 ->
  word_string DfracDiscarded p s -∗
  getenv_globals dq bc rc be re counter (mkPtr (b + o) (Obj b)) -∗
  getenv_vector dqa dqt b reg o entries -∗ E -∗
  (getenv_globals dq bc rc be re counter (mkPtr (b + o) (Obj b)) -∗
   getenv_vector dqa dqt b reg o entries -∗ E -∗
   Φ (Ret (WPtr (getenv_result s entries)))) -∗
  WP (ERun (getenv_frame p) : gexpr) {{ Φ }}.
Proof.
  intros Hcounter Henv Hbc Hrc Hrcmax Hbe Hre Hremax Hal.
  iIntros "#Hname Hglobals (%Hbounds & Hl & Hcells) HE HK".
  destruct Hbounds as (Hb & Ho & Hend & Hspace & Halarray).
  iAssert (live_capq dqa (Obj b) reg) with "[Hl]" as "Htarget"; [iExact "Hl"|].
  iCombine "Hcells HE" as "HG".
  iApply (getenv_nonnull_entry with "Hname Hglobals Htarget HG"); try eassumption; [cbn; lia|].
  iIntros "Hglobals Hl (Hcells & HE)".
  iCombine "Hglobals Hl Hcells HE" as "HG".
  iApply (getenv_name_guard with "Hname HG"); [reflexivity|].
  destruct s as [|a s].
  - iIntros "(Hglobals & Hl & Hcells & HE)".
    iApply ("HK" with "Hglobals [Hl Hcells] HE"). unfold getenv_vector. iFrame. done.
  - iIntros "((Hcl & Hcc & Hel & Hec) & Hl & Hcells & HE)".
    step.
    iApply (StrlenWord.wp_call_glibc_strlen registry (os_wi w0) ge with "Hname");
      [vx |apply defines |reflexivity |].
    iNext. iIntros "_". cbn [fr_fn fr_env fr_locals fr_doomed fr_at]. step.
    iDestruct (ws_shape with "Hname") as %(_ & Hpos & Hlen).
    rewrite (Z.mod_small (Z.of_nat (length (a :: s))) (2 ^ 64)); [|lia].
    iCombine "Hel Hec HE" as "HE".
    iApply (getenv_scan _ true with "Hname [Hl Hcells] Hcl Hcc HE");
      try eassumption; try discriminate;
      try (unfold getenv_name_env, getenv_nonnull_env; reflexivity).
    + unfold getenv_vector. iFrame. done.
    + iIntros "Hvector Hcl Hcc (Hel & Hec & HE)".
      iApply ("HK" with "[Hcl Hcc Hel Hec] Hvector HE"). unfold getenv_globals. iFrame.
Qed.

(** The complete call preserves both global cells, the entire vector,
    every entry's readable string and target lifetime, and arbitrary E.
    The name may be empty or contain equals signs. *)
Lemma getenv_static_call p s entries ep dq dqa dqt bc rc be re counter (E : iProp Σ) Φ :
  lookup (TAtom "__environ_counter") (ge_globals ge) = Some (mkPtr bc (Obj bc)) ->
  lookup (TAtom "__environ") (ge_globals ge) = Some (mkPtr be (Obj be)) ->
  0 < bc -> bc + 8 <= r_end rc -> r_end rc <= 2 ^ 48 ->
  0 < be -> be + 8 <= r_end re -> r_end re <= 2 ^ 48 -> be mod 8 = 0 ->
  word_string DfracDiscarded p s -∗ getenv_globals dq bc rc be re counter ep -∗
  getenv_storage dqa dqt ep entries -∗ E -∗
  (getenv_globals dq bc rc be re counter ep -∗ getenv_storage dqa dqt ep entries -∗ E -∗
   getenv_value (getenv_result s entries) -∗
   Φ (Ret (WPtr (getenv_result s entries)))) -∗
  WP (ERun (getenv_frame p) : gexpr) {{ Φ }}.
Proof.
  intros Hcounter Henv Hbc Hrc Hrcmax Hbe Hre Hremax Hal.
  iIntros "#Hname HG HS HE HK".
  iDestruct (getenv_storage_value with "Hname HS") as "[HS #Hv]".
  iDestruct "HS" as "[%Hnull | HS]".
  - destruct Hnull as [-> ->].
    iApply (getenv_empty with "Hname HG HE"); try eassumption.
    iIntros "_ HG HE".
    assert (Hr : getenv_result s [] = null) by (destruct s; reflexivity).
    rewrite Hr. iApply ("HK" with "HG [] HE Hv"). iLeft. done.
  - iDestruct "HS" as (b reg o ->) "HV".
    iApply (getenv_static_nonnull with "Hname HG HV HE"); try eassumption.
    iIntros "HG HV HE". iApply ("HK" with "HG [HV] HE Hv").
    iRight. iExists b, reg, o. iFrame. done.
Qed.

(** This supplies the readable-name interface without hiding a whole-getenv
    premise inside G. The caller explicitly owns the static environment. *)
Lemma getenv_static_name_contract p s entries ep dq dqa dqt bc rc be re counter (E : iProp Σ) :
  lookup (TAtom "__environ_counter") (ge_globals ge) = Some (mkPtr bc (Obj bc)) ->
  lookup (TAtom "__environ") (ge_globals ge) = Some (mkPtr be (Obj be)) ->
  0 < bc -> bc + 8 <= r_end rc -> r_end rc <= 2 ^ 48 ->
  0 < be -> be + 8 <= r_end re -> r_end re <= 2 ^ 48 -> be mod 8 = 0 ->
  ⊢ getenv_name_contract
    (getenv_globals dq bc rc be re counter ep ∗ getenv_storage dqa dqt ep entries ∗ E) p s.
Proof.
  intros Hcounter Henv Hbc Hrc Hrcmax Hbe Hre Hremax Hal.
  iModIntro. iIntros "#Hname (HG & HS & HE)".
  iApply (getenv_static_call with "Hname HG HS HE"); try eassumption.
  iIntros "HG HS HE _". iExists (getenv_result s entries). iFrame. done.
Qed.
End static.
