(** Once stdout has a buffer, an overflow either stores the next byte
    or flushes the pending bytes first. This proof connects that
    concrete overflow rule to the buffer and field predicates used by
    string output. The buffer remains a heap object even on write errors. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry SysCode LibioReadCode LibioDoWriteCode FileInv
  LibioLogic SysWrappers LibioOverflowBase LibioXsputnBase HiAtexitBase
  HiAtexitOverflow HiAtexitOutputState.
Import ListNotations.
Open Scope Z_scope.
Import HOB HOB.SW HOB.SW.FI.ML HOB.SW.FI.LG HOB.SW.FI.L HOB.SW.OW HOB.SW.FI HOB.SW.ST.
Import HXB HXB.DX.RM.SM.TL.BY.BF.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
Context (Hreg : holds_os registry) (Hext : sys_external ge).
Context (Hwrite : find_fn ge (TAtom "__GI___write") = Some (Defined glibc___libc_write))
  (Hfw : ge_fn ge "_IO_new_file_write" glibc__IO_new_file_write)
  (Hdwf : find_fn ge (TAtom "_IO_new_do_write") = Some (Defined glibc__IO_new_do_write)).

(** The program logic uses the same OS world as the overflow proof. *)
Local Instance hi_buffered_overflow_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** Overflow preserves the stronger output fields and every owned
    capability slot. It may change the pending count and write end. *)
Lemma hi_buffered_overflow fr eb fb freg vb vreg bb sz wp we ch Φ :
  call_frame glibc__IO_new_file_overflow [WPtr (mkPtr fb (Obj fb)); WInt ch] = Some fr ->
  (0 <= ch < 256 \/ ch = 2 ^ 32 - 1) ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  vtables_ro ge vb vreg -∗ live fb freg -∗ pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗
  wbuf fb (Some (bb, sz)) wp we -∗ xfields w0 eb fb (Some (bb, sz)) -∗
  ▷ (∀ r wp' we', ⌜ovf_ret ch r⌝ -∗ live fb freg -∗
     pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗
     wbuf fb (Some (bb, sz)) wp' we' -∗ xfields w0 eb fb (Some (bb, sz)) -∗ Φ (Ret (WInt r))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hch Heb Hfb Hal Hend Hregend.
  iIntros "#Hvt Hl Hvtp Hwb Hxf HK".
  iDestruct "Hxf" as (fl f2 fd tw off m (Happ & Hf2 & Hfd & Hm & Hflags & Hfd31 & Hf2160))
    "(Hfl & Hfl2 & Hfdc & Htw & Hoff & Hcol & Hmode & Herr)".
  pose proof (xs_flags_mask _ _ 8 eq_refl Hflags) as Hnw.
  pose proof (proj2 Hflags) as Hput.
  iDestruct (hi_wbuf_to_ovf with "Hwb Hfl Htw Hoff") as (breg xs cs k [Hb8 [Hheap Hlc]]) "[Hst Hcs]".
  iDestruct "Hfl2" as "[%Hf2r Hfl2]".
  iApply (hi_overflow w0 registry ge Hreg Hext Hwrite Hfw Hdwf
    fr fb freg ch f2 fd eb m vb vreg bb breg sz k we xs fl tw off with
    "Hvt Hl [$Hfl2 $Hfdc $Herr $Hcol $Hmode $Hvtp //] Hst"); try assumption.
  iNext. iIntros (r k' we' xs' fl' tw' off' [Hr Hfl']) "Hl (Hfl2 & Hfdc & Herr & Hcol & Hmode & Hvtp) Hst".
  iDestruct (hi_ovf_to_wbuf _ _ _ _ _ _ _ _ _ _ _ Hb8 Hheap Hlc with "Hst Hcs")
    as "(Hwb & Hfl & Htw & Hoff)".
  assert (Hflags' : xs_flags (Some (bb, sz)) fl').
  { destruct Hfl' as [-> | ->]; [exact Hflags | apply xs_flags_error; exact Hflags]. }
  pose proof (xs_flags_mask _ _ io_is_appending eq_refl Hflags') as Happ'.
  change (Z.land fl' io_is_appending = 0) in Happ'.
  iApply ("HK" with "[%] Hl Hvtp Hwb [Hfl Hfl2 Hfdc Htw Hoff Hcol Hmode Herr]"); [exact Hr|].
  iExists fl', f2, fd, tw', off', m. iFrame. iPureIntro.
  tauto.
Qed.

End rules.
