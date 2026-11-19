(** The public overflow function orients a stream before it calls the
    stream's overflow method. The method returns a heap buffer on every
    path of a buffered write. The next caller can therefore write to
    the same stream or close it, whether this write succeeded or failed. *)

From Glibc Require Import Unit_io_fstat64_os Unit_io_write_nocancel_os Unit_io_write_os Unit_libio_filedoalloc_os Unit_libio_fileops_os.
From Glibc Require Import Unit_libio_genops_os Unit_misc_makedev_os Unit_termios_isatty_nostatus_os.
From Glibc Require Import GlibcProgram GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic MemLogic.
From Glibc Require Import Fix OsBlocks OsWorld OsRegistry SysWrappers FileInv FileIdle FileTidy LibioLogic
  LibioOverflowBase LibioOverflowGen LibioStreamTidy
  LibioPutsInv LibioFputsSpec PrintfStreamInv PrintfStreamHeap AllocRo AllocLogic HiAtexitSetb
  LibioOverflowHeapBuffer LibioOverflowHeapIdle.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.
Open Scope Z_scope.

Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (Hreg : holds_os registry) (Hext : sys_external ge).
Context (Hstat : ge_fn ge "__GI__IO_file_stat" Unit_libio_fileops_os.fn___GI__IO_file_stat)
  `{!Defines ge "__GI___fstat64" Unit_io_fstat64_os.fn___GI___fstat64} `{!Defines ge "__gnu_dev_major" Unit_misc_makedev_os.fn___gnu_dev_major}
  `{!Defines ge "__isatty_nostatus" Unit_termios_isatty_nostatus_os.fn___isatty_nostatus} `{!Defines ge "__GI__IO_setb" Unit_libio_genops_os.fn___GI__IO_setb}.
Context `{!Defines ge "free" free_fn} (Hfh : frees_heap (ge_free ge))
  (Hzf : find_fn ge zgc_free_name = None) (Hzg : lookup zgc_free_name (ge_globals ge) = None).
Context `{!Defines ge "malloc" malloc_fn} `{!Defines ge "glibc_malloc#__libc_malloc2" malloc2_fn}.
Context (Hda : ge_fn ge "__GI__IO_file_doallocate" Unit_libio_filedoalloc_os.fn___GI__IO_file_doallocate)
  `{!Defines ge "__GI__IO_doallocbuf" Unit_libio_genops_os.fn___GI__IO_doallocbuf}.
Context `{!Defines ge "__GI___write" Unit_io_write_os.fn___GI___libc_write} (Hfw : ge_fn ge "_IO_new_file_write" Unit_libio_fileops_os.fn__IO_new_file_write)
  `{!Defines ge "_IO_new_do_write" Unit_libio_fileops_os.fn__IO_new_do_write}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** A direct call leaves the stream's mode alone. It returns the exact
    heap buffer and flag changes, rather than hiding them behind the
    idle-stream predicate. Lock and wide-character ownership stay with
    the caller throughout the write. *)
Lemma wp_heap_file_fields fr fb freg st nb ch vb vr eb Φ :
  let fd := fs_fileno st in let fl := fs_flags st in let f2 := fs_flags2 st in
  call_frame Unit_libio_fileops_os.fn__IO_new_file_overflow [WPtr (mkPtr fb (Obj fb)); WInt ch] = Some fr ->
  (0 <= ch < 256 \/ ch = 2^32-1) -> fb mod 8 = 0 -> 0 < fb -> fb+file_size <= r_end freg -> r_end freg <= 2^63 ->
  flags_ok st -> idle_ok fd (fs_with_flags2 st 0) -> fs_vtable st = mkPtr (vb+vt_file) (Ro vb) ->
  buf_ptrs_ok fb (heap_kind nb) (fs_ptrs st) -> short_idle (heap_kind nb) st ->
  has fl io_unbuffered = false -> has fl io_no_writes = false ->
  (Z.land f2 2 = 0 \/ Z.land f2 2 = 2 /\ find_fn ge (TAtom "__GI___write_nocancel") = Some (Defined Unit_io_write_nocancel_os.fn___GI___write_nocancel)) ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> In fd (ow_fds w0) ->
  vtables_ro ge vb vr -∗ malloc_ro -∗ live fb freg -∗ file_fields fb st -∗ buf_idle (heap_kind nb) -∗ errno_any eb -∗
  ▷ (∀ r bb sz k we fl' tw' off', let st' := heap_file_state st bb sz k we fl' tw' off' in
    ⌜ovf_ret ch r /\ (nb = None \/ nb = Some (bb,sz)) /\ heap_overflow_flags nb fl fl' /\
      flags_ok st' /\ idle_ok fd (fs_with_flags2 st' 0) /\ short_idle (NbHeap bb sz) st' /\ buf_ptrs_ok fb (NbHeap bb sz) (fs_ptrs st')⌝ -∗
    live fb freg -∗ file_fields fb st' -∗ buf_idle (NbHeap bb sz) -∗ errno_any eb -∗ Φ (Ret (WInt r))) -∗
  WP (ERun fr : gexpr) {{ Φ }}.
Proof using Type*.
  cbn zeta. intros Hfr Hch Hal Hfb Hend Hr Hok Hi Hvt Hb Hshort Hu Hnw Hready He Hin.
  iIntros "#Hvt #HM Hl Hf Hb Herr HK".
  iDestruct (heap_fields fb st nb vb eb with "Hf Hb Herr") as "(Hbuf & Hfix & Hfl & Htw & Hoff & Hclose)"; try assumption.
  pose proof Hi as (Hfd & _ & Hmd & _ & _ & _ & _ & _ & _ & _ & _ & Happ & _).
  pose proof Hok as (_ & _ & _ & Hbk & _). cbn [fs_with_flags2 fs_flags fs_mode] in Hmd, Happ.
  unfold has in Hu, Hnw, Hbk, Happ. apply Bool.negb_false_iff, Z.eqb_eq in Hu, Hnw, Hbk, Happ.
  iApply (wp_heap_file_buffer Hreg Hext Hstat Hfh Hzf Hzg Hda Hfw fr fb freg ch (fs_flags2 st) (fs_fileno st) eb (fs_mode st)
    vb vr nb (fs_ptr st 4) (fs_ptr st 5) (fs_flags st) (fs_total st) (fs_offset st) with "Hvt HM Hl Hfix Hbuf Hfl Htw Hoff");
    try first [assumption | intuition lia].
  { intros ->. destruct Hshort as [_ H]. unfold has in H. apply Bool.negb_false_iff, Z.eqb_eq in H. exact H. }
  iNext. iIntros (r bb sz k we fl' tw' off' (Hr' & Hnb & Hflags)) "Hl Hfix Hbuf Hfl Htw Hoff".
  iDestruct ("Hclose" with "[%] Hbuf Hfix Hfl Htw Hoff") as "(%Hpost & Hf & Hb & Herr)"; [auto|].
  iApply ("HK" with "[%] Hl Hf Hb Herr"). tauto.
Qed.

(** The public wrapper borrows the mode and jump-table pointer before
    it calls the file method. It leaves the pointer alone and can
    replace an unoriented stream's mode with byte orientation. *)
Local Lemma heap_orient_fields fb st : file_fields fb st ⊢
  int_cell fb off_mode (fs_mode st) ∗ pcell fb off_vtable (fs_vtable st) ∗
  (∀ m, int_cell fb off_mode m -∗ pcell fb off_vtable (fs_vtable st) -∗ file_fields fb (fs_with_mode st m)).
Proof using Type.
  iIntros "(%Hlen & Hfl & Hps & Hfd & Hf2 & Hold & %Hcl & Hcol & Hlp & Hoff & Hcv & Hwd & Hfrl & Hfrb & $ & Htw & $)".
  iIntros (m) "Hmd Hvt". unfold file_fields, fs_with_mode. cbn. iFrame. done.
Qed.

(** The wrapper accepts a byte, orients the stream and returns either
    the byte or EOF. It also returns the caller's lock state and all
    the fields that the next narrow write needs. *)
Theorem wp_overflow_heap (Hov : ge_fn ge "_IO_new_file_overflow" Unit_libio_fileops_os.fn__IO_new_file_overflow) : overflow_heap_rule.
Proof using Type*.
  intros fr vb self fb freg st nb f2 held ch eb Φ fp fd Hfr Hch Hal Hfb Hend Hr Hok Hi Ef2 Hvt Hb Hshort Hu Hnw Hready He Hin Hg.
  iIntros "#Hro #HM Hl Hf Hlk Hb Hw Herr HK". subst fp fd f2.
  iDestruct "Hro" as (vr sb sr) "[#Hvt _]".
  iAssert (∃ kind, ⌜nb = heap_kind kind⌝ ∗ buf_idle nb)%I with "[Hb]" as (kind ->) "Hb".
  { destruct nb as [| |bb sz|b]; [iExists None; iFrame; done | destruct Hshort as (_ & H & _); congruence |
    iExists (Some (bb,sz)); iFrame; done | iDestruct "Hb" as "[]"]. }
  iDestruct (heap_orient_fields with "Hf") as "(Hmd & Hvtp & Hclose)". iEval (rewrite Hvt) in "Hvtp".
  pose proof Hi as (_ & _ & Hmd & _). cbn [fs_with_flags2 fs_mode] in Hmd.
  iApply (wp_glibc___overflow Hov fr fb freg ch (fs_mode st) vb vr with "Hvt Hl Hmd Hvtp"); try first [assumption | lia].
  iNext. iIntros (fr' Hfr') "Hl Hmd Hvtp". iEval (rewrite -Hvt) in "Hvtp".
  iDestruct ("Hclose" with "Hmd Hvtp") as "Hf". set (stn := fs_with_mode st (2^32-1)).
  iApply (wp_heap_file_fields fr' fb freg stn kind ch vb vr eb with "Hvt HM Hl Hf Hb Herr"); try first [assumption | left; assumption].
  { unfold stn, idle_ok, fs_with_flags2, fs_with_mode in *. cbn [fs_fileno fs_flags fs_ptrs fs_mode fs_column fs_lock fs_flags2] in *. tauto. }
  iNext. iIntros (r bb sz k we fl' tw' off' (Hret & _ & _ & Hflags & Hid & Hsh & Hbuf)) "Hl Hf Hb Herr".
  assert (Hne : ch <> 2^32-1) by lia. unfold ovf_ret in Hret. rewrite (proj2 (Z.eqb_neq _ _) Hne) in Hret.
  iExists r. iSplit; [iPureIntro; intuition lia|].
  iApply ("HK" with "[%] [Hl Hf Hb Hw Hlk] Herr"); [tauto|].
  iExists fb, freg, (heap_file_state stn bb sz k we fl' tw' off'), (NbHeap bb sz).
  iFrame "Hl Hf Hb Hw Hlk". iPureIntro. intuition.
Qed.
End rules.
