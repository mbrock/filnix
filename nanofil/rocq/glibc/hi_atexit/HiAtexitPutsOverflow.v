(** The newline in puts calls an overflow wrapper when stdout has
    no room. The wrapper chooses byte output and calls the stream's
    overflow function. This file connects both calls to the linked
    program's proofs while retaining the stream and allocator state. *)

From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry FileInv LibioLogic SysWrappers
  LibioGenCode LibioOverflowGen LibioXsputnBase LibioDefaultXsputnBuf AllocLogic
  HiAtexitBase HiAtexitGe HiAtexitFns HiAtexitSetb HiAtexitAlloc HiAtexitXsputnOverflow
  HiAtexitOutputState HiAtexitStdout HiAtexitOverflowRules.
From Glibc Require FileInv LibioCloseSteps LibioDefaultXsputnBuf LibioLogic LibioOverflowGen LibioPutsInv LibioPutsLock LibioXsputnBase LibioXsputnSetp OsWorld SysWrappers.
Import ListNotations.
Open Scope Z_scope.

Import LibioPutsLock.
Import LibioPutsInv LibioCloseSteps SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.
Import LibioXsputnSetp.
Import LibioXsputnBase LibioDefaultXsputnBuf.
Local Opaque HiAtexitFns.hi_ge.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (dq : dfrac) (mp tc dummy : Z) (mpr tcr dr : region).
Context (Hmp : lookup (TAtom "malloc#mp_") (ge_globals hge) = Some (mkPtr mp (Obj mp)))
  (Htc : lookup (TAtom "tcache") (ge_globals hge) = Some (mkPtr tc (Obj tc))).

(** Overflow runs with the linked program's actual OS registry. *)
Local Instance hi_puts_overflow_irisGS : irisGS_gen hlc (nanofil_lang glibc_os_registry hge) Σ :=
  nanofil_irisGS glibc_os_registry (os_wi w0) hge.
Local Notation sexpr := (language.expr (nanofil_lang glibc_os_registry hge)).

(** Every function called during buffer allocation or flushing is
    present in the linked environment and has a proved rule. *)
Definition hge_output_overflow :=
  hi_xsputn_overflow (Σ := Σ) w0 glibc_os_registry hge (fun n c H => H) (hi_sys_external _)
    (hi_ge_file_stat _) (hi_find___GI___fstat64 _) (hi_find___gnu_dev_major _) (hi_find___isatty_nostatus _)
    (hi_find___GI__IO_setb _) (hi_find_free _) hge_frees (proj1 hge_zgc_free) (proj2 hge_zgc_free)
    (hi_find_malloc _) (hi_find_malloc___libc_malloc2 _) dq mp tc dummy mpr tcr dr Hmp Htc
    (hi_ge_doallocate _) (hi_find___GI__IO_doallocbuf _) (hi_find___GI___write _) (hi_ge_file_write _)
    (hi_find__IO_new_do_write _).

(** The wrapper may orient stdout, allocate its first buffer or
    flush an existing one. A failed write still returns the buffer
    and all the fields that the close callback needs. *)
Lemma hi_puts_overflow s fr fp eb vb vreg Φ :
  call_frame glibc___overflow [WPtr fp; WInt 10] = Some fr ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) ->
  vtables_ro hge vb vreg -∗ hi_stdout_after w0 eb vb s fp (Some 0) -∗
  hi_malloc_state dq mp tc dummy mpr tcr dr -∗
  ▷ (∀ r, ⌜r = 10 \/ r = 2 ^ 32 - 1⌝ -∗ hi_stdout_after w0 eb vb s fp (Some 0) -∗
     hi_malloc_state dq mp tc dummy mpr tcr dr -∗ Φ (Ret (WInt r))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Heb. iIntros "#Hvt Hf HM HK".
  iDestruct "Hf" as (fb freg nb wp we lb (-> & Hfb & Hal & Hend & Hreg & Hlb & Hprogress))
    "(Hl & Hvtp & Hwb & Hxf & Htail)".
  iDestruct "Hxf" as (fl f2 fd tw off m Hp)
    "(Hfl & Hfl2 & Hfd & Htw & Hoff & Hcol & Hmode & Herr)".
  destruct Hp as (Happ & Hf2 & Hfd & Hm & Hflags & Hfd31 & Hf2160).
  iApply (LibioOverflowGen.wp_glibc___overflow w0 glibc_os_registry hge (hi_ge_overflow _)
    fr fb freg 10 m vb vreg with "Hvt Hl Hmode Hvtp"); try assumption; try lia.
  iNext. iIntros (fr' Hfr') "Hl Hmode Hvtp".
  iApply (hge_output_overflow eb Heb fr' fb freg nb wp we 10 vb vreg with
    "Hvt Hl Hvtp Hwb [Hfl Hfl2 Hfd Htw Hoff Hcol Hmode Herr HM]");
    try assumption; try (left; lia).
  { iFrame "HM". iExists fl, f2, fd, tw, off, (2 ^ 32 - 1).
    iFrame "Hfl Hfl2 Hfd Htw Hoff Hcol Hmode Herr". iPureIntro. tauto. }
  iNext. iIntros (r nb' wp' we' [Hr Hallocated]) "Hl Hvtp Hwb [Hxf HM]".
  change (r = 4294967295 \/ r = 10) in Hr.
  iExists r. iSplit; [iPureIntro; split; [reflexivity | destruct Hr; lia]|].
  iApply ("HK" with "[%] [Hl Hvtp Hwb Hxf Htail] HM"); [destruct Hr; tauto|].
  iExists fb, freg, nb', wp', we', lb. iFrame "Hl Hvtp Hwb Hxf Htail". iPureIntro.
  split_and!; try assumption; try reflexivity. intros _. exact Hallocated.
Qed.

End rules.
