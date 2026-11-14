From Glibc Require Import GlibcProgram.
(** Flushing the staging array updates printf's count before sending its
    bytes through the stream's jump table. A returned count that differs from
    the request marks failure, but does not discard the staged bytes.

    This proof connects the function entry to the stream call and its count
    comparison. The stream call and the following buffer selection remain
    explicit obligations; neither is assumed to accept all bytes. *)
From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry FileInv LibioLogic SysWrappers
  LibioCloseSteps LibioXsputnCode PrintfBufferFileCode PrintfBufferXsputnEntry
  PrintfBufferXsputnCaller.
From Glibc Require FileInv LibioCloseSteps LibioLogic LibioPutsInv OsWorld PrintfBufferXsputnCall PrintfBufferXsputnCaller PrintfBufferXsputnEntry SysWrappers.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.


Import LibioPutsInv LibioCloseSteps SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).
Context (F : ptr -> iProp Σ)
  (E : iProp Σ).
Context (Hfn : ge_fn ge "_IO_new_file_xsputn" glibc__IO_new_file_xsputn).
Context (Hcall : PrintfBufferXsputnCall.printf_xsputn_call_spec w0 registry ge F E).

(** Both continuations receive the updated unsigned count and the original bytes.
    A count mismatch returns with failure; an exact count reaches L40 with the
    original printf mode and the stream resources returned by the call. *)
Lemma wp_printf_xsputn_staging fr bb breg fb vb vreg xs mode written Φ :
  let n := Z.of_nat (length xs) in
  call_frame glibc___printf_buffer_flush_to_file [WPtr (mkPtr bb (Obj bb))] = Some fr ->
  0 < bb -> bb mod 8 = 0 -> bb + 176 <= r_end breg -> r_end breg <= 2 ^ 63 ->
  0 < fb -> fb mod 8 = 0 -> n <= 128 -> Forall (fun y => 0 <= y < 256) xs ->
  0 <= written < 2 ^ 64 ->
  (F (mkPtr fb (Obj fb)) ⊢ ∃ freg dqf,
    ⌜fb + 224 <= r_end freg /\ r_end freg <= 2 ^ 63⌝ ∗
    liveq dqf fb freg ∗ pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) ∗
    (liveq dqf fb freg -∗ pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗
      F (mkPtr fb (Obj fb)))) ->
  vtables_ro ge vb vreg -∗ live bb breg -∗
  pcell bb 0 (mkPtr (bb + 48) (Obj bb)) -∗
  pcell bb 8 (mkPtr (bb + 48 + n) (Obj bb)) -∗
  pcell bb 16 (mkPtr (bb + 176) (Obj bb)) -∗ icell bb 24 written -∗
  pcell bb 40 (mkPtr fb (Obj fb)) -∗ bytes bb 48 xs -∗
  int_cell bb 32 mode -∗ F (mkPtr fb (Obj fb)) -∗ E -∗
  (live bb breg -∗ pcell bb 0 (mkPtr (bb + 48) (Obj bb)) -∗
    pcell bb 8 (mkPtr (bb + 48 + n) (Obj bb)) -∗
    pcell bb 16 (mkPtr (bb + 176) (Obj bb)) -∗ icell bb 24 ((written + n) mod 2 ^ 64) -∗
    pcell bb 40 (mkPtr fb (Obj fb)) -∗ bytes bb 48 xs -∗ int_cell bb 32 0 -∗
    F (mkPtr fb (Obj fb)) -∗ E -∗ Φ RetVoid) -∗
  (∀ e', ⌜lookup (TAtom "v0") e' = Some (WPtr (mkPtr bb (Obj bb)))⌝ -∗
    live bb breg -∗ pcell bb 0 (mkPtr (bb + 48) (Obj bb)) -∗
    pcell bb 8 (mkPtr (bb + 48 + n) (Obj bb)) -∗
    pcell bb 16 (mkPtr (bb + 176) (Obj bb)) -∗ icell bb 24 ((written + n) mod 2 ^ 64) -∗
    pcell bb 40 (mkPtr fb (Obj fb)) -∗ bytes bb 48 xs -∗ int_cell bb 32 mode -∗
    F (mkPtr fb (Obj fb)) -∗ E -∗
    WP (ERun (mkFrame glibc___printf_buffer_flush_to_file e' [] None
      (Enter (TAtom "L40") (Some (TAtom "iw_1.join")))) : sexpr) {{ Φ }}) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  cbn zeta. intros Hfr Hbb Hba Hbe Hbr Hfb Hfa Hlen Hxs Hw Hborrow.
  set (P := (pcell bb 0 (mkPtr (bb + 48) (Obj bb)) ∗
    pcell bb 16 (mkPtr (bb + 176) (Obj bb)) ∗
    icell bb 24 ((written + Z.of_nat (length xs)) mod 2 ^ 64))%I).
  assert (Hframed : PrintfBufferXsputnCall.printf_xsputn_call_spec w0 registry ge F (E ∗ P)).
  { intros fr' fp b reg dq ys Ψ Hb Ha Hlen' He Hr Hys Hframe.
    iIntros "HF (HE & HP) Hl Hys HK".
    iApply (Hcall fr' fp b reg dq ys with "HF HE Hl Hys"); try assumption.
    iNext. iIntros (r Hret) "HF HE Hl Hys".
    iApply ("HK" $! r with "[%] HF [HE HP] Hl Hys"); [done | iFrame]. }
  iIntros "#Hvt Hb Hbase Hptr Hend Hw Hfp Hxs Hm HF HE Hfail Hselect".
  iApply (PrintfBufferXsputnEntry.wp_printf_xsputn_entry fr bb breg (Z.of_nat (length xs)) written
    with "Hb Hbase Hptr Hend Hw"); try assumption; try lia.
  iIntros (e (Hv0 & Hchk & Hchk1)) "Hb Hbase Hptr Hend Hw".
  iApply (PrintfBufferXsputnCaller.wp_printf_xsputn_caller F (E ∗ P) Hfn Hframed
    e (Some (TAtom "start")) bb breg fb vb vreg xs mode
    with "Hvt Hb Hptr Hfp Hxs Hm HF [HE Hbase Hend Hw] [Hfail] [Hselect]"); try assumption.
  - rewrite /P. iFrame.
  - rewrite /P. iIntros "Hb Hptr Hfp Hxs Hm HF (HE & Hbase & Hend & Hw)".
    iApply ("Hfail" with "Hb Hbase Hptr Hend Hw Hfp Hxs Hm HF HE").
  - rewrite /P. iIntros (e' Hv0') "Hb Hptr Hfp Hxs Hm HF (HE & Hbase & Hend & Hw)".
    iApply ("Hselect" $! e' with "[%] Hb Hbase Hptr Hend Hw Hfp Hxs Hm HF HE"). done.
Qed.

End rules.
