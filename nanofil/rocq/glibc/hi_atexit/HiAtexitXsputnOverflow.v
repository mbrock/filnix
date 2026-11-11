(** String output may overflow before stdout has a buffer or after
    writing has started. Both cases use proved glibc code here. The
    resulting rule preserves stdout's stronger field invariant and
    the allocator state, so string output needs no assumed callee. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry SysCode LibioReadCode LibioDoWriteCode FileInv
  LibioLogic SysWrappers AllocLogic LibioOverflowBase LibioOverflowAllocSetg LibioDefaultXsputnBuf
  LibioXsputnBase HiAtexitBase HiAtexitSetb HiAtexitAlloc HiAtexitOverflowAlloc
  HiAtexitOutputState HiAtexitBufferedOverflow.
Import ListNotations.
Open Scope Z_scope.
Import HOB HOB.SW HOB.SW.FI.ML HOB.SW.FI.LG HOB.SW.FI.L HOB.SW.OW HOB.SW.FI HOB.SW.ST.
Import HXB HXB.DX.RM.SM.TL.BY.BF.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
Context (Hreg : holds_os registry) (Hext : sys_external ge).
Context (Hstat : ge_fn ge "__GI__IO_file_stat" glibc__IO_file_stat)
  (Hfstat : find_fn ge (TAtom "__GI___fstat64") = Some (Defined glibc___fstat64))
  (Hmaj : find_fn ge (TAtom "__gnu_dev_major") = Some (Defined glibc___gnu_dev_major))
  (Hisatty : find_fn ge (TAtom "__isatty_nostatus") = Some (Defined glibc___isatty_nostatus))
  (Hsetb : find_fn ge (TAtom "__GI__IO_setb") = Some (Defined glibc__IO_setb)).
Context (Hfree_fn : find_fn ge (TAtom "free") = Some (Defined free_fn)) (Hfh : frees_heap (ge_free ge))
  (Hzf : find_fn ge zgc_free_name = None) (Hzg : lookup zgc_free_name (ge_globals ge) = None).
Context (Hmalloc_fn : find_fn ge (TAtom "malloc") = Some (Defined malloc_fn))
  (Hmalloc2 : find_fn ge (TAtom "malloc#__libc_malloc2") = Some (Defined malloc2_fn)).
Context (dq : dfrac) (mp tc dummy : Z) (mpr tcr dr : region).
Context (Hmp : lookup (TAtom "malloc#mp_") (ge_globals ge) = Some (mkPtr mp (Obj mp)))
  (Htc : lookup (TAtom "tcache") (ge_globals ge) = Some (mkPtr tc (Obj tc))).
Context (Hda : ge_fn ge "__GI__IO_file_doallocate" glibc__IO_file_doallocate)
  (Hdab : find_fn ge (TAtom "__GI__IO_doallocbuf") = Some (Defined glibc__IO_doallocbuf))
  (Hwrite : find_fn ge (TAtom "__GI___write") = Some (Defined glibc___libc_write))
  (Hfw : ge_fn ge "_IO_new_file_write" glibc__IO_new_file_write)
  (Hdwf : find_fn ge (TAtom "_IO_new_do_write") = Some (Defined glibc__IO_new_do_write)).
Context (eb : Z) (Heb : ow_errno w0 = Some (mkPtr eb (Obj eb))).

(** The overflow rule uses the same OS world as string output. *)
Local Instance hi_xsputn_overflow_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.

(** Overflow allocates a buffer on the first write and reuses it on
    later writes. Both paths call only functions proved here. *)
Lemma hi_xsputn_overflow :
  overflow_spec w0 registry ge (xos w0 eb (fun _ _ => hi_malloc_state dq mp tc dummy mpr tcr dr)).
Proof.
  intros fr fb freg nb wp we ch vb vreg Φ Hfr Hch Hfb Hal Hend Hregend.
  iIntros "#Hvt Hl Hvtp Hwb (Hxf & HM) HK".
  destruct nb as [[bb sz] |].
  - iApply (hi_buffered_overflow w0 registry ge Hreg Hext Hwrite Hfw Hdwf
      fr eb fb freg vb vreg bb sz wp we ch with "Hvt Hl Hvtp Hwb Hxf");
      try assumption.
    iNext. iIntros (r wp' we' Hr) "Hl Hvtp Hwb Hxf".
    iApply ("HK" with "[%] Hl Hvtp Hwb [$Hxf $HM]"). exact Hr.
  - iDestruct "Hxf" as (fl f2 fd tw off m (Happ & Hf2 & Hfd & Hm & Hflags & Hfd31 & Hf2160))
      "(Hfl & Hfl2 & Hfdc & Htw & Hoff & Hcol & Hmode & Herr)".
    iDestruct "Hwb" as "((Hrp & Hre & Hrb & Hwb & Hbase & Hbend) & Hwp & Hwe & [%Hwp %Hwe])".
    subst wp we. iDestruct "Hfl" as "[%Hflr Hfl]". iDestruct "Hfl2" as "[%Hf2r Hfl2]".
    pose proof (xs_flags_mask _ _ 8 eq_refl Hflags) as Hnw.
    pose proof (xs_flags_mask _ _ 256 eq_refl Hflags) as Hbackup.
    pose proof (xs_flags_mask _ _ io_unbuffered eq_refl Hflags) as Hunbuf.
    pose proof (proj2 Hflags) as Hput.
    iApply (hi_overflow_alloc w0 registry ge Hreg Hext Hstat Hfstat Hmaj Hisatty Hsetb Hfree_fn Hfh Hzf Hzg
      Hmalloc_fn Hmalloc2 dq mp tc dummy mpr tcr dr Hmp Htc Hda Hdab Hwrite Hfw Hdwf
      fr fb freg ch f2 fd eb m vb vreg fl tw off null null null null null null with
      "Hvt Hl [$Hfl2 $Hfdc $Herr $Hcol $Hmode $Hvtp //] [$Hfl //] Htw Hoff Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend HM");
      try assumption.
    iNext. iIntros (r bb breg sz k' we' xs' fl' tw' off' (Hr & Hsz & Hout & Hheap & Hb16 & Hb48))
      "Hl (Hfl2 & Hfdc & Herr & Hcol & Hmode & Hvtp) Hst Hcs HM".
    assert (Hb8 : bb mod 8 = 0).
    { apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hb16; [|lia].
      destruct Hb16 as [k Hk]. exists (2 * k). lia. }
    iDestruct (hi_ovf_to_wbuf _ _ _ _ _ _ _ _ _ _ _ Hb8 Hheap (length_replicate _ _) with "Hst Hcs")
      as "(Hwb & Hfl & Htw & Hoff)".
    pose proof (hi_xs_flags_alloc _ _ bb sz Hflags Hflr Hout) as Hflags'.
    pose proof (xs_flags_mask _ _ io_is_appending eq_refl Hflags') as Happ'.
    change (Z.land fl' io_is_appending = 0) in Happ'.
    iAssert (xfields w0 eb fb (Some (bb, sz))) with "[Hfl Hfl2 Hfdc Htw Hoff Hcol Hmode Herr]" as "Hxf".
    { iExists fl', f2, fd, tw', off', m. iFrame. iPureIntro. tauto. }
    iApply ("HK" with "[%] Hl Hvtp Hwb [$Hxf $HM]"). exact Hr.
Qed.

End rules.
