(** A buffered stream installs its first buffer through the allocator
    and reuses it on subsequent writes. Both cases return the bytes
    and capability slots of a heap allocation. This lets the next
    writer use the buffer and lets the stream free it on close. *)

From Glibc Require Import Unit_io_fstat64_os Unit_io_write_nocancel_os Unit_io_write_os Unit_libio_filedoalloc_os Unit_libio_fileops_os.
From Glibc Require Import Unit_libio_genops_os Unit_misc_makedev_os Unit_termios_isatty_nostatus_os.
From Glibc Require Import GlibcProgram GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic MemLogic.
From Glibc Require Import Fix OsBlocks OsWorld OsRegistry SysWrappers FileInv LibioLogic
  LibioOverflowBase LibioSetb LibioOverflowAllocSetg LibioOverflowAlloc LibioDefaultXsputnBuf
  AllocCall StreamOverflowAlloc StreamOutputState AllocLogic AllocRo LibioOverflowHeapStart.
Import ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0 Fix.LG0.L OsWorld FileInv LibioLogic.
Open Scope Z_scope.

(** Allocation may discover a terminal and enable line buffering. It
    also clears the user-buffer flag. Reusing a buffer makes neither
    change. *)
Definition heap_overflow_flags (nb : option (Z * Z)) fl fl' :=
  match nb with None => ovf_alloc_flags fl fl' | Some _ => heap_put_flags fl fl' end.

Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (Hreg : holds_os registry) (Hext : sys_external ge).
Context (Hstat : ge_fn ge "__GI__IO_file_stat" Unit_libio_fileops_os.fn___GI__IO_file_stat)
  `{Hfstat : !Defines ge "__GI___fstat64" Unit_io_fstat64_os.fn___GI___fstat64} `{Hmaj : !Defines ge "__gnu_dev_major" Unit_misc_makedev_os.fn___gnu_dev_major}
  `{Hisatty : !Defines ge "__isatty_nostatus" Unit_termios_isatty_nostatus_os.fn___isatty_nostatus} `{Hsetb : !Defines ge "__GI__IO_setb" Unit_libio_genops_os.fn___GI__IO_setb}.
Context `{Hfree_fn : !Defines ge "free" free_fn} (Hfh : frees_heap (ge_free ge))
  (Hzf : find_fn ge zgc_free_name = None) (Hzg : lookup zgc_free_name (ge_globals ge) = None).
Context `{Hmalloc : !Defines ge "malloc" malloc_fn} `{Hmalloc2 : !Defines ge "glibc_malloc#__libc_malloc2" malloc2_fn}.
Context (Hda : ge_fn ge "__GI__IO_file_doallocate" Unit_libio_filedoalloc_os.fn___GI__IO_file_doallocate)
  `{Hdab : !Defines ge "__GI__IO_doallocbuf" Unit_libio_genops_os.fn___GI__IO_doallocbuf}.
Context `{Hwrite : !Defines ge "__GI___write" Unit_io_write_os.fn___GI___libc_write} (Hfw : ge_fn ge "_IO_new_file_write" Unit_libio_fileops_os.fn__IO_new_file_write)
  `{Hdwf : !Defines ge "_IO_new_do_write" Unit_libio_fileops_os.fn__IO_new_do_write}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** The jump-table entry accepts both a byte and EOF. It preserves the
    descriptor, mode, second flags word and vtable, and gives its caller
    the actual write pointers. An existing allocation keeps its base
    and size. *)
Lemma wp_heap_file_buffer fr fb freg ch f2 fd eb mode vb vr nb wp we fl tw off Φ :
  call_frame Unit_libio_fileops_os.fn__IO_new_file_overflow [WPtr (mkPtr fb (Obj fb)); WInt ch] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb+file_size <= r_end freg -> r_end freg <= 2^63 ->
  (0 <= ch < 256 \/ ch = 2^32-1) ->
  (Z.land f2 2 = 0 \/ Z.land f2 2 = 2 /\ find_fn ge (TAtom "__GI___write_nocancel") = Some (Defined Unit_io_write_nocancel_os.fn___GI___write_nocancel)) ->
  In fd (ow_fds w0) -> 0 <= fd < 2^31 -> Z.land fl io_is_appending = 0 -> Z.land fl 8 = 0 ->
  Z.land fl 256 = 0 -> Z.land fl io_unbuffered = 0 -> (nb = None -> Z.land fl 2048 = 0) ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> (mode = 0 \/ mode = 2^32-1) ->
  vtables_ro ge vb vr -∗ malloc_ro -∗ live fb freg -∗ ovf_fixed fb f2 fd eb mode vb -∗
  wbuf fb nb wp we -∗ int_cell fb off_flags fl -∗ icell fb off_total_written tw -∗ icell fb off_offset off -∗
  ▷ (∀ r bb sz k we' fl' tw' off', ⌜LibioOverflowBase.ovf_ret ch r /\ (nb = None \/ nb = Some (bb,sz)) /\ heap_overflow_flags nb fl fl'⌝ -∗
     live fb freg -∗ ovf_fixed fb f2 fd eb mode vb -∗ wbuf fb (Some (bb,sz)) (mkPtr (bb+k) (Obj bb)) we' -∗
     int_cell fb off_flags fl' -∗ icell fb off_total_written tw' -∗ icell fb off_offset off' -∗ Φ (Ret (WInt r))) -∗
  WP (ERun fr : gexpr) {{ Φ }}.
Proof using Type*.
  intros Hfr Hfb Hal Hend Hr Hch Hready Hin Hfd Happ Hnw Hbk Hu Hfresh He Hmd.
  iIntros "#Hvt #HM Hl Hfx Hbuf Hfl Htw Hoff HK".
  iDestruct "Hfx" as "([%Hf2 Hf2] & Hfd & Herr & Hcol & Hmode & Hvtp)".
  destruct nb as [[bb sz]|].
  - iDestruct (hi_wbuf_to_ovf with "Hbuf Hfl Htw Hoff") as (br xs cs k (Hb8 & Hheap & Hlc)) "[Hst Hcs]".
    iApply (wp_heap_existing Hreg Hext Hfw fr fb freg ch f2 fd eb mode vb vr bb br sz k we xs fl tw off
      with "Hvt Hl [$Hf2 $Hfd $Herr $Hcol $Hmode $Hvtp //] Hst"); try assumption.
    iNext. iIntros (r k' we' xs' fl' tw' off' [Hr' Hflags]) "Hl Hfx Hst".
    iDestruct (hi_ovf_to_wbuf _ _ _ _ _ _ _ _ _ _ _ Hb8 Hheap Hlc with "Hst Hcs") as "(Hbuf & Hfl & Htw & Hoff)".
    iApply ("HK" with "[%] Hl Hfx Hbuf Hfl Htw Hoff"). auto.
  - iDestruct "HM" as (mp tc dm mr tr dr [Hmp Htc]) "#HM".
    pose proof (hi_doallocbuf w0 registry ge Hreg Hext Hstat Hfstat Hmaj Hisatty Hsetb Hfree_fn Hfh Hzf Hzg
      Hmalloc Hmalloc2 DfracDiscarded mp tc dm mr tr dr Hmp Htc Hda) as Halloc.
    pose proof (wp_ovf_L33 (malloc_call_state DfracDiscarded mp tc dm mr tr dr) Halloc (heap_switch_to_putting Hreg Hext Hfw)) as H33.
    iDestruct "Hbuf" as "((Hrp & Hre & Hrb & Hwb & Hb & He') & Hwp & Hwe & [%Ewp %Ewe])". subst wp we.
    iApply (wp_glibc__IO_new_file_overflow_alloc _ H33 fr fb freg ch f2 fd eb mode vb vr fl tw off null null null null null null
      with "Hvt Hl [$Hf2 $Hfd $Herr $Hcol $Hmode $Hvtp //] Hfl Htw Hoff Hrp Hre Hrb Hwb Hwp Hwe Hb He' HM");
      try first [assumption | apply Hfresh; reflexivity].
    iNext. iIntros (r bb br sz k' we' xs' fl' tw' off' (Hr' & Hsz & Hflags & Hheap & Hb16 & Hb48)) "Hl Hfx Hst Hcs _".
    assert (Hb8 : bb mod 8 = 0).
    { apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hb16; [|lia]. destruct Hb16 as [j ->]. exists (2*j). lia. }
    iDestruct (hi_ovf_to_wbuf _ _ _ _ _ _ _ _ _ _ _ Hb8 Hheap (length_replicate _ _) with "Hst Hcs") as "(Hbuf & Hfl & Htw & Hoff)".
    iApply ("HK" with "[%] Hl Hfx Hbuf Hfl Htw Hoff"). auto.
Qed.
End rules.
