From Glibc Require Fix.
From Glibc Require Import Unit_io_fstat64_os Unit_io_write_os Unit_libio_filedoalloc_os Unit_libio_fileops_os Unit_libio_genops_os.
From Glibc Require Import Unit_misc_makedev_os Unit_termios_isatty_nostatus_os.
From Glibc Require Import GlibcProgram.
(** String output may overflow before stdout has a buffer or after
    writing has started. Both cases use proved glibc code here. The
    resulting rule preserves stdout's stronger field invariant and
    the allocator state, so string output needs no assumed callee. *)

From Glibc Require Import GlibcTactics OsTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry FileInv
  LibioLogic SysWrappers AllocLogic LibioDefaultXsputnBuf
  LibioXsputnBase AllocCall StreamOverflowAlloc
  StreamOutputState HiAtexitBufferedOverflow.
Import ListNotations.
Open Scope Z_scope.
Import SysWrappers Fix.ML0 Fix.LG0 Fix.LG0.L OsWorld FileInv LibioLogic.
Import LibioXsputnBase LibioDefaultXsputnBuf.

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (Hreg : holds_os registry)
  (Hext : sys_external ge).
Context (Hstat : ge_fn ge "__GI__IO_file_stat" Unit_libio_fileops_os.fn___GI__IO_file_stat)
  `{Hfstat : !Defines ge "__GI___fstat64" Unit_io_fstat64_os.fn___GI___fstat64}
  `{Hmaj : !Defines ge "__gnu_dev_major" Unit_misc_makedev_os.fn___gnu_dev_major}
  `{Hisatty : !Defines ge "__isatty_nostatus" Unit_termios_isatty_nostatus_os.fn___isatty_nostatus}
  `{Hsetb : !Defines ge "__GI__IO_setb" Unit_libio_genops_os.fn___GI__IO_setb}.
Context `{Hfree_fn : !Defines ge "free" free_fn}
  (Hfh : frees_heap (ge_free ge))
  (Hzf : find_fn ge zgc_free_name = None)
  (Hzg : lookup zgc_free_name (ge_globals ge) = None).
Context `{Hmalloc_fn : !Defines ge "malloc" malloc_fn}
  `{Hmalloc2 : !Defines ge "glibc_malloc#__libc_malloc2" malloc2_fn}.
Context (dq : dfrac)
  (mp tc dummy : Z)
  (mpr tcr dr : region).
Context (Hmp : lookup (TAtom "glibc_malloc#mp_") (ge_globals ge) = Some (mkPtr mp (Obj mp)))
  (Htc : lookup (TAtom "tcache") (ge_globals ge) = Some (mkPtr tc (Obj tc))).
Context (Hda : ge_fn ge "__GI__IO_file_doallocate" Unit_libio_filedoalloc_os.fn___GI__IO_file_doallocate)
  `{Hdab : !Defines ge "__GI__IO_doallocbuf" Unit_libio_genops_os.fn___GI__IO_doallocbuf}
  `{Hwrite : !Defines ge "__GI___write" Unit_io_write_os.fn___GI___libc_write}
  (Hfw : ge_fn ge "_IO_new_file_write" Unit_libio_fileops_os.fn__IO_new_file_write)
  `{Hdwf : !Defines ge "_IO_new_do_write" Unit_libio_fileops_os.fn__IO_new_do_write}.
Context (eb : Z)
  (Heb : ow_errno w0 = Some (mkPtr eb (Obj eb))).


(** Overflow allocates a buffer on the first write and reuses it on
    later writes. Both paths call only functions proved here. *)
Lemma hi_xsputn_overflow :
  overflow_spec w0 registry ge (xos w0 eb (fun _ _ => malloc_call_state dq mp tc dummy mpr tcr dr)).
Proof using Hda Hdab Hdwf Heb Hext Hfh Hfree_fn Hfstat Hfw Hisatty Hmaj Hmalloc2 Hmalloc_fn Hmp Hreg Hsetb Hstat Htc Hwrite Hzf Hzg.
  intros fr fb freg nb wp we ch vb vreg Φ Hfr Hch Hfb Hal Hend Hregend.
  iIntros "#Hvt Hl Hvtp Hwb (Hxf & HM) HK".
  destruct nb as [[bb sz] |].
  - iApply (hi_buffered_overflow Hreg Hext Hfw
      fr eb fb freg vb vreg bb sz wp we ch with "Hvt Hl Hvtp Hwb Hxf");
      try assumption.
    iNext. iIntros (r wp' we' Hr) "Hl Hvtp Hwb Hxf".
    iApply ("HK" with "[%] Hl Hvtp Hwb [$Hxf $HM]"). split; [exact Hr | discriminate].
  - iDestruct "Hxf" as (fl f2 fd tw off m (Happ & Hf2x & Hfd & Hm & Hflags & Hfd31))
      "(Hfl & Hfl2 & Hfdc & Htw & Hoff & Hcol & Hmode & Herr)".
    pose proof Hf2x as [Hf2 Hf2160].
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
    iApply ("HK" with "[%] Hl Hvtp Hwb [$Hxf $HM]"). split; [exact Hr | discriminate].
Qed.

End rules.
