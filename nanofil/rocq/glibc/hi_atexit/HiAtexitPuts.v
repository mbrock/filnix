(** This file proves puts for the actual linked hi_atexit program.
    Its string-output and newline calls use proved glibc functions,
    not assumed call rules. A nonempty input leaves stdout with an
    allocated buffer even when output fails, so closing it remains
    safe without assuming a successful write. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsWorld OsRegistry FileInv WordString LibioPuts LibioPutsCode
  HiAtexitBase HiAtexitGe HiAtexitFns HiAtexitAlloc HiAtexitStdout
  HiAtexitPutsXsputn HiAtexitPutsNl HiAtexitPutsOverflow HiAtexitPutsRules.
Import ListNotations.
Open Scope Z_scope.
Import HP.PN.PB.PM.PC.PU.PL.
Import PI PI.CS.SW.FI PI.CS.SW.FI.ML PI.CS.SW.FI.LG PI.CS.SW.FI.L.

(** Proof-mode searches keep the stream and allocator resources
    folded instead of expanding their memory layouts. *)
#[local] Hint Opaque vtables_ro hi_stdout_before hi_stdout_after word_string hi_malloc_state
  : typeclass_instances.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (dq : dfrac) (mp tc dummy : Z) (mpr tcr dr : region).
Context (Hmp : lookup (TAtom "malloc#mp_") (ge_globals hge) = Some (mkPtr mp (Obj mp)))
  (Htc : lookup (TAtom "tcache") (ge_globals hge) = Some (mkPtr tc (Obj tc))).

(** Puts runs with the linked program's actual OS registry. *)
Local Instance hi_puts_irisGS : irisGS_gen hlc (nanofil_lang glibc_os_registry hge) Σ :=
  nanofil_irisGS glibc_os_registry (os_wi w0) hge.
Local Notation sexpr := (language.expr (nanofil_lang glibc_os_registry hge)).

(** The return count may indicate failure. In every case puts
    releases stdout's lock and returns the string, allocator state
    and stream resources needed by the close callback. *)
Lemma hi_puts fr p dq' s so soreg fp mode eb vb vreg sb sreg Φ :
  call_frame glibc__IO_puts [WPtr p] = Some fr ->
  lookup (TAtom "stdout") (ge_globals hge) = Some (mkPtr so (Obj so)) ->
  so mod 8 = 0 -> so + 8 <= r_end soreg ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> ptr_addr (ow_self w0) <> 0 ->
  vtables_ro hge vb vreg -∗ single_ro hge sb sreg -∗ word_string dq' p s -∗
  live so soreg -∗ pcell so 0 fp -∗ hi_stdout_before w0 eb vb fp mode None -∗
  hi_malloc_state dq mp tc dummy mpr tcr dr -∗
  ▷ (∀ r, ⌜puts_ret (Z.of_nat (length s)) r⌝ -∗ word_string dq' p s -∗
     live so soreg -∗ pcell so 0 fp -∗ hi_stdout_after w0 eb vb s fp None -∗
     hi_malloc_state dq mp tc dummy mpr tcr dr -∗ Φ (Ret (WInt r))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hgso Hsoal Hsoend Heb Hself.
  iIntros "#Hvt #Hsingle Hstr Hso Hsoc Hf HM HK".
  iApply (HP.wp_glibc__IO_puts_for w0 glibc_os_registry hge (fun n c H => H) (hi_sys_external _)
    vb vreg (vtables_ro hge vb vreg ∗ hi_malloc_state dq mp tc dummy mpr tcr dr)
    (hi_stdout_before w0 eb vb) (fun s fp _ held => hi_stdout_after w0 eb vb s fp held)
    (hi_stdout_before_open w0 eb vb) (fun s fp _ held => hi_stdout_after_lock w0 eb vb s fp held)
    (hi_stdout_before_wide w0 eb vb) (hi_ge_xsputn _)
    (hi_puts_xsputn w0 dq mp tc dummy mpr tcr dr Hmp Htc eb vb vreg Heb)
    (fun s e so soreg fb Φ Hg Ha He =>
      hi_puts_L180 w0 dq mp tc dummy mpr tcr dr
        (hi_puts_overflow w0 dq mp tc dummy mpr tcr dr Hmp Htc)
        s e so soreg fb eb vb vreg Φ Hg Ha He Heb)
    with "Hvt Hsingle Hstr Hso Hsoc Hf [$Hvt $HM]"); try assumption.
  - exact (hi_find___GI_strlen _).
  - iNext. iIntros (r Hr) "Hstr Hso Hsoc Hf [_ HM]".
    iApply ("HK" with "[%] Hstr Hso Hsoc Hf HM"). exact Hr.
Qed.

End rules.
