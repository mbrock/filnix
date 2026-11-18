(** When glibc cannot put a byte directly into an unbuffered stream,
    it calls the stream's overflow function. That function sends the
    byte through the stream's own short buffer. Both a failed write
    and a successful one must leave the stream idle again. *)

From Glibc Require Import GlibcProgram GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic MemLogic.
From Glibc Require Import Fix OsBlocks OsWorld OsRegistry SysCode SysWrappers FileInv FileIdle FileTidy
  PrintfStreamInv LibioFputsSpec LibioLogic LibioReadCode LibioDoWriteCode LibioGenCode LibioSetb LibioOverflowGen
  LibioOverflowBase LibioOverflowShortWrite LibioOverflowShortSend LibioOverflowShortStart LibioOverflowShortIdle.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.
Open Scope Z_scope.

Section overflow.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (Hreg : holds_os registry) (Hext : sys_external ge) (Hfree : free_rule w0 registry ge).
Context `{!Defines ge "__GI__IO_doallocbuf" glibc__IO_doallocbuf}.
Context `{!Defines ge "__GI__IO_setb" glibc__IO_setb}.
Context `{!Defines ge "__GI___write" glibc___libc_write}.
Context `{!Defines ge "_IO_new_do_write" glibc__IO_new_do_write}.
Context (Hfw : ge_fn ge "_IO_new_file_write" glibc__IO_new_file_write).
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** A request to flush an empty stream returns zero. A request to
    write a byte returns that byte or EOF. Both cases return the same
    fields that the stream lent, including the flags2 and mode cells. *)
Lemma wp_short_file_overflow fr fb freg ch f2 fd eb mode vb vreg fresh rb fl tw off byte Φ :
  call_frame glibc__IO_new_file_overflow [WPtr (mkPtr fb (Obj fb)); WInt ch] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2^63 ->
  (0 <= ch < 256 \/ ch = 2^32-1) -> Z.land fl 8 = 0 -> Z.land fl 256 = 0 -> Z.land fl 2 <> 0 ->
  (fresh = true -> Z.land fl 2048 = 0) -> Z.land fl io_is_appending = 0 ->
  (Z.land f2 2 = 0 \/ Z.land f2 2 = 2 /\ find_fn ge (TAtom "__GI___write_nocancel") = Some (Defined glibc___write_nocancel)) ->
  In fd (ow_fds w0) -> ow_errno w0 = Some (mkPtr eb (Obj eb)) -> (mode = 0 \/ mode = 2^32-1) ->
  vtables_ro ge vb vreg -∗ live fb freg -∗ ovf_fixed fb f2 fd eb mode vb -∗ short_input fb fresh rb -∗
  int_cell fb off_flags fl -∗ icell fb off_total_written tw -∗ icell fb off_offset off -∗ bytes fb off_shortbuf [byte] -∗
  ▷ (∀ r rb' byte' fl' tw' off', ⌜ovf_ret ch r /\ (ch = 2^32-1 -> r = 0) /\
       ((fresh = false /\ rb' = rb) \/ rb' = short_ptr fb) /\ short_flags fresh fl fl'⌝ -∗
     live fb freg -∗ ovf_fixed fb f2 fd eb mode vb -∗ short_state fb rb' fl' tw' off' byte' -∗ Φ (Ret (WInt r))) -∗
  WP (ERun fr : gexpr) {{ Φ }}.
Proof using Type*.
  intros Hfr Hfb Hal Hend Hrend Hch Hnw Hbk Hu Hfresh Happ Hready Hin He Hmd.
  iIntros "#Hvt Hl ([%Hf2 Hf2] & Hfd & Herr & Hcol & Hmode & Hvtp) (Hrp & Hre & Hrb & Hwb & Hwp & Hwe & Hbase & Hbend) Hfl Htw Hoff Hbyte HK".
  iApply (wp_short_start Hfree _ fb freg ch fl mode fresh rb with "Hl Hfl Hmode Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend"); try assumption.
  iNext. iIntros (e from fl1 rb1 (H0 & H2 & Hc & Hs & Hrb)) "Hl Hfl Hmode Hptrs".
  assert (Hflags : short_flags fresh fl fl1) by (exists fl1; auto).
  iApply (wp_short_send Hreg Hext Hfw fb freg ch f2 fd eb mode vb vreg rb1 fl1 tw off byte from e with
    "Hvt Hl [$Hf2 $Hfd $Herr $Hcol $Hmode $Hvtp //] [$Hptrs $Hfl $Htw $Hoff $Hbyte]");
    try first [assumption | rewrite (short_flags_mask _ _ _ _ Hflags); [assumption|reflexivity..]].
  iNext. iIntros (r fl' tw' off' rb' byte' (Hr & Hef & Hfl' & Hrb')) "Hl Hfix Hst".
  iApply ("HK" with "[%] Hl Hfix Hst"). split_and!; try assumption; [destruct Hrb' as [->| ->]; tauto | exists fl1; auto].
Qed.

Context (Hov : ge_fn ge "_IO_new_file_overflow" glibc__IO_new_file_overflow).

(** The public overflow wrapper first orients the stream and then calls
    its overflow slot. The stream comes back tidy on the same descriptor,
    with its lock and its second flags word unchanged. *)
Lemma wp_overflow_short fr vb self fb freg st nb flags2 held ch eb Φ :
  let fp := mkPtr fb (Obj fb) in let fd := fs_fileno st in
  call_frame glibc___overflow [WPtr fp; WInt ch] = Some fr -> 0 <= ch < 256 ->
  fb mod 8 = 0 -> 0 < fb -> fb+file_size <= r_end freg -> r_end freg <= 2^63 -> flags_ok st ->
  idle_ok fd (fs_with_flags2 st 0) -> fs_flags2 st = flags2 -> fs_vtable st = mkPtr (vb+vt_file) (Ro vb) ->
  buf_ptrs_ok fb nb (fs_ptrs st) -> short_idle nb st -> has (fs_flags st) io_unbuffered = true ->
  has (fs_flags st) io_no_writes = false ->
  (Z.land flags2 2 = 0 \/ Z.land flags2 2 = 2 /\ find_fn ge (TAtom "__GI___write_nocancel") = Some (Defined glibc___write_nocancel)) ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> In fd (ow_fds w0) ->
  fputs_ro vb -∗ live fb freg -∗ file_fields fb st -∗ lock_inv self (fs_lock st) held -∗ buf_idle nb -∗
  wide_idle vb (fs_wide st) (fs_codecvt st) -∗ errno_any eb -∗
  ▷ (∀ r, ⌜r = ch \/ r = 2^32-1⌝ -∗ file_tidy vb self fp fd flags2 held -∗ errno_any eb -∗ Φ (Ret (WInt r))) -∗
  WP (ERun fr : gexpr) {{ Φ }}.
Proof using Type*.
  cbn zeta. intros Hfr Hch Hal Hfb Hend Hrend Hok Hi Hf2 Hvt Hb Hshort Hu Hnw Hready He Hin.
  iIntros "#Hro Hl Hf Hlk Hb Hw Herr HK". iDestruct "Hro" as (vr sb sr) "[#Hvt _]".
  iAssert (⌜exists fresh : bool, nb = if fresh then NbNone else NbShort⌝)%I with "[Hb]" as %(fresh & ->).
  { destruct nb; try (iPureIntro; first [exists true; reflexivity | exists false; reflexivity]);
      [destruct Hshort as (_ & Hb0 & _); congruence | iDestruct "Hb" as "[]"]. }
  iDestruct (short_fields vb self fb freg st fresh (fs_fileno st) flags2 held eb with "Hf Hlk Hw Herr") as (rb byte)
    "(Hp & Hfl & Htw & Hoff & Hbyte & (Hf2 & Hfd & Herr & Hcol & Hmode & Hvtp) & Hclose)"; try assumption.
  pose proof Hok as (_ & _ & _ & Hbk & _). pose proof Hi as (_ & _ & Hmode & _ & _ & _ & _ & _ & _ & _ & _ & Happ & _).
  cbn [fs_with_flags2 fs_mode fs_flags] in Hmode, Happ.
  iApply (wp_glibc___overflow Hov fr fb freg ch (fs_mode st) vb vr with "Hvt Hl Hmode Hvtp"); try first [assumption | lia].
  iNext. iIntros (fr' Hfr') "Hl Hmode Hvtp".
  unfold has in Hu, Hnw, Hbk, Happ. apply negb_true_iff, Z.eqb_neq in Hu.
  apply negb_false_iff, Z.eqb_eq in Hnw, Hbk, Happ.
  iApply (wp_short_file_overflow fr' fb freg ch flags2 (fs_fileno st) eb (2^32-1) vb vr fresh rb (fs_flags st) (fs_total st) (fs_offset st) byte
    with "Hvt Hl [$Hf2 $Hfd $Herr $Hcol $Hmode $Hvtp] Hp Hfl Htw Hoff Hbyte"); try first [assumption | left; lia | right; reflexivity].
  { intros ->. destruct Hshort as [_ H]. unfold has in H. apply negb_false_iff, Z.eqb_eq in H. exact H. }
  iNext. iIntros (r rb' b' fl' tw' off' (Hr & _ & Hrb & Hflags)) "Hl Hfix Hst".
  iDestruct ("Hclose" with "[%] Hl Hst Hfix") as "[Htidy Herr]"; [intuition|].
  assert (Hne : ch <> 2^32-1) by lia. unfold ovf_ret in Hr. rewrite (proj2 (Z.eqb_neq _ _) Hne) in Hr.
  iExists r. iSplit; [iPureIntro; intuition lia|]. iApply ("HK" with "[%] Htidy Herr"); tauto.
Qed.
End overflow.
