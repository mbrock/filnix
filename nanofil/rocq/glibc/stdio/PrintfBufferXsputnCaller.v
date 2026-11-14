(** Printf sends the bytes in its staging array through the stream's jump
    table. It checks the returned count and marks the printf buffer failed
    whenever that count differs from the request.

    The caller keeps its source bytes when the stream reports a short write.
    This proof covers the pointer reads and count comparison, but requires
    separate proofs of the stream call and the subsequent buffer selection. *)
From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry FileInv LibioLogic SysWrappers
  LibioCloseSteps LibioXsputnCode PrintfBufferFileCode PrintfBufferXsputnPrelude
  PrintfBufferXsputnCall PrintfBufferXsputnReturn.
From Glibc Require FileInv LibioCloseSteps LibioLogic LibioPutsInv OsWorld PrintfBufferXsputnCall PrintfBufferXsputnPrelude PrintfBufferXsputnReturn SysWrappers.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.


Import LibioPutsInv LibioCloseSteps SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
Local Instance caller_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).
Context (F : ptr -> iProp Σ) (E : iProp Σ).
Context (Hfn : ge_fn ge "_IO_new_file_xsputn" glibc__IO_new_file_xsputn).
Context (Hcall : PrintfBufferXsputnCall.printf_xsputn_call_spec w0 registry ge F E).

(** Printf requests exactly the number of staged bytes, from zero through 128.
    Every returned count preserves those bytes. A count mismatch marks failure;
    an exact count proceeds to buffer selection at L40. *)
Lemma wp_printf_xsputn_caller e from bb breg fb vb vreg xs mode Φ :
  let n := Z.of_nat (length xs) in
  0 < bb -> bb mod 8 = 0 -> bb + 176 <= r_end breg -> r_end breg <= 2 ^ 63 ->
  0 < fb -> fb mod 8 = 0 -> n <= 128 -> Forall (fun y => 0 <= y < 256) xs ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr bb (Obj bb))) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr (bb + 24) (Obj bb))) ->
  lookup (TAtom "chk1") e = Some (WPtr (mkPtr (bb + 8) (Obj bb))) ->
  (F (mkPtr fb (Obj fb)) ⊢ ∃ freg dqf,
    ⌜fb + 224 <= r_end freg /\ r_end freg <= 2 ^ 63⌝ ∗
    liveq dqf fb freg ∗ pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) ∗
    (liveq dqf fb freg -∗ pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗
      F (mkPtr fb (Obj fb)))) ->
  vtables_ro ge vb vreg -∗ live bb breg -∗
  pcell bb 8 (mkPtr (bb + 48 + n) (Obj bb)) -∗ pcell bb 40 (mkPtr fb (Obj fb)) -∗
  bytes bb 48 xs -∗ int_cell bb 32 mode -∗ F (mkPtr fb (Obj fb)) -∗ E -∗
  (live bb breg -∗ pcell bb 8 (mkPtr (bb + 48 + n) (Obj bb)) -∗
    pcell bb 40 (mkPtr fb (Obj fb)) -∗ bytes bb 48 xs -∗ int_cell bb 32 0 -∗
    F (mkPtr fb (Obj fb)) -∗ E -∗ Φ RetVoid) -∗
  (∀ e', ⌜lookup (TAtom "v0") e' = Some (WPtr (mkPtr bb (Obj bb)))⌝ -∗
    live bb breg -∗ pcell bb 8 (mkPtr (bb + 48 + n) (Obj bb)) -∗
    pcell bb 40 (mkPtr fb (Obj fb)) -∗ bytes bb 48 xs -∗ int_cell bb 32 mode -∗
    F (mkPtr fb (Obj fb)) -∗ E -∗
    WP (ERun (mkFrame glibc___printf_buffer_flush_to_file e' [] None
      (Enter (TAtom "L40") (Some (TAtom "iw_1.join")))) : sexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame glibc___printf_buffer_flush_to_file e [] None
    (Enter (TAtom "L14") from)) : sexpr) {{ Φ }}.
Proof.
  cbn zeta. intros Hbb Hba Hbe Hbr Hfb Hfa Hlen Hxs Hv0 Hchk Hchk1 Hborrow.
  iIntros "#Hvt Hb Hptr Hfp Hxs Hm HF HE Hfail Hselect".
  iDestruct (Hborrow with "HF") as (freg dqf (Hfe & Hfr)) "(Hf & Hvtp & Hclose)".
  iApply (PrintfBufferXsputnPrelude.wp_printf_xsputn_prelude w0 registry ge Hfn
    e from bb breg fb freg dqf vb vreg (Z.of_nat (length xs))
    with "Hvt Hb Hf Hptr Hfp Hvtp"); try assumption; try lia.
  iIntros (e' (Hv0' & Hchk' & Hfn' & Hfp' & Hsrc' & Hcount')) "Hb Hf Hptr Hfp Hvtp".
  iDestruct ("Hclose" with "Hf Hvtp") as "HF".
  iApply (PrintfBufferXsputnCall.wp_printf_xsputn_call w0 registry ge F E Hfn Hcall
    e' (mkPtr fb (Obj fb)) bb breg (DfracOwn 1%Qp) xs with "HF HE Hb Hxs");
    try assumption; try lia.
  iIntros (r e'' (Hr & Hv0'' & Hchk'' & Hcount'' & Hret)) "HF HE Hb Hxs".
  destruct (Z.eq_dec r (Z.of_nat (length xs))) as [->|Hneq].
  - iApply (PrintfBufferXsputnReturn.wp_printf_xsputn_complete w0 registry ge e'' (Z.of_nat (length xs)));
      try assumption; try lia.
    iApply ("Hselect" with "[%] Hb Hptr Hfp Hxs Hm HF HE"). lookups; reflexivity.
  - iApply (PrintfBufferXsputnReturn.wp_printf_xsputn_mismatch w0 registry ge e'' bb breg mode r (Z.of_nat (length xs))
      with "Hb Hm"); try assumption; try lia.
    iNext. iIntros "Hb Hm".
    iApply ("Hfail" with "Hb Hptr Hfp Hxs Hm HF HE").
Qed.

End rules.
