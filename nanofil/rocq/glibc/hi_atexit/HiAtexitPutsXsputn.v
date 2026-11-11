(** This file connects puts to the output function proved for the
    linked program. The call borrows the string's bytes and returns
    its original word-aligned memory window. It also preserves
    stdout's buffer, stream fields and allocator state on failure. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsWorld OsRegistry FileInv WordString
  HiAtexitBase HiAtexitGe HiAtexitAlloc HiAtexitOutputState HiAtexitXsputn HiAtexitStdout HiAtexitStringBytes.
Import ListNotations.
Open Scope Z_scope.
Import HPI HPI.CS.SW.FI HPI.CS.SW.FI.ML HPI.CS.SW.FI.LG HPI.CS.SW.FI.L HXB HXB.DX.RM.SM.TL.BY.BF.
Local Opaque HiAtexitFns.hi_ge.

(** Proof-mode searches keep the stream and allocator resources
    folded instead of expanding their memory layouts. *)
#[local] Hint Opaque vtables_ro hi_stdout_before hi_stdout_after word_string hi_malloc_state
  : typeclass_instances.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (dq : dfrac) (mp tc dummy : Z) (mpr tcr dr : region).
Context (Hmp : lookup (TAtom "malloc#mp_") (ge_globals hge) = Some (mkPtr mp (Obj mp)))
  (Htc : lookup (TAtom "tcache") (ge_globals hge) = Some (mkPtr tc (Obj tc))).

(** The callee runs in the linked program and its actual OS registry. *)
Local Instance hi_puts_xsputn_irisGS : irisGS_gen hlc (nanofil_lang glibc_os_registry hge) Σ :=
  nanofil_irisGS glibc_os_registry (os_wi w0) hge.

(** Writing a nonempty string leaves stdout with a buffer even when
    the write fails. This rule also returns the string, allocator state
    and read-only jump tables that the caller lent to output. *)
Lemma hi_puts_xsputn eb vb vreg :
  ow_errno w0 = Some (mkPtr eb (Obj eb)) ->
  xsputn_spec_for w0 glibc_os_registry hge (hi_stdout_before w0 eb vb)
    (fun s fp _ held => hi_stdout_after w0 eb vb s fp held)
    (vtables_ro hge vb vreg ∗ hi_malloc_state dq mp tc dummy mpr tcr dr).
Proof.
  intros Heb fr fp p dq' s Φ Hfr. iIntros "Hf Hstr [#Hvt HM] HK".
  iEval (unfold hi_stdout_before) in "Hf".
  iDestruct "Hf" as (fb freg nb wp we lb fl f2 fd tw off Hp) "(Hl & Hvtp & Hwb & Hxf & Htail)".
  destruct Hp as (-> & Hfb & Hal & Hend & Hreg & Hlb).
  iAssert (xfields w0 eb fb nb) with "[Hxf]" as "Hxf".
  { iExists fl, f2, fd, tw, off, (2 ^ 32 - 1). iExact "Hxf". }
  iDestruct (hi_word_string_bytes with "Hstr") as (b breg so (Hp & Hcap & Hb & Hb8 & Hso & Hbend & Hbreg & Hys))
    "(Hbl & Hys & Hstrback)".
  rewrite Hp in Hfr.
  iApply (hge_xsputn w0 dq mp tc dummy mpr tcr dr Hmp Htc with
    "Hvt Hl Hvtp Hwb [$Hxf $HM] Hbl Hys"); try eassumption; try lia.
  iNext. iIntros (r nb' wp' we' [Hr Hprogress]) "Hl Hvtp Hwb [Hxf HM] Hbl Hys".
  iDestruct ("Hstrback" with "Hbl Hys") as "Hstr".
  iApply ("HK" with "[%] [Hl Hvtp Hwb Hxf Htail] Hstr [$Hvt $HM]").
  - destruct Hr as [-> | Hr]; lia.
  - unfold hi_stdout_after. iExists fb, freg, nb', wp', we', lb. iFrame "Hl Hvtp Hwb Hxf Htail".
    iPureIntro. split_and!; try assumption; try reflexivity.
    intros Hnonempty. apply Hprogress. destruct s; [contradiction|]. cbn [length]. lia.
Qed.

End rules.
