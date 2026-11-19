(** On an unbuffered stream, glibc has no room to copy any of the input
    into the stream. It flushes the empty stream, installing its short
    buffer if necessary, then writes the whole string from the caller's
    buffer. A partial write leaves the stream just as empty as a full one. *)

From Glibc Require Import Unit_io_write_nocancel_os Unit_io_write_os Unit_libio_fileops_os Unit_libio_genops_os.
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic MemLogic.
From Glibc Require Import Fix OsBlocks OsWorld OsRegistry SysWrappers FileInv FileIdle FileTidy
  PrintfStreamInv LibioFputsSpec LibioLogic LibioPutsInv LibioSetb
  LibioOverflowBase LibioOverflowShortWrite LibioOverflowShortSend LibioOverflowShortIdle
  LibioOverflowShort LibioXsputnShortWrite.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.
Open Scope Z_scope.
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.

Section xsputn.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** The write pointer and write end are equal before the first write
    and after every later write. The space test therefore skips the copy
    and passes the original pointer and count to the flush path. *)
Lemma wp_xs_short_enter fr fb freg src n fresh rb fl Φ :
  call_frame Unit_libio_fileops_os.fn__IO_new_file_xsputn [WPtr (mkPtr fb (Obj fb)); WPtr src; WInt n] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb+file_size <= r_end freg -> r_end freg <= 2^63 ->
  0 < n < 2^63 -> Z.land fl 512 = 0 ->
  live fb freg -∗ int_cell fb off_flags fl -∗ short_input fb fresh rb -∗
  ▷ (∀ e, ⌜lookup (TAtom "v0") e = Some (WPtr (mkPtr fb (Obj fb))) /\
       lookup (TAtom "chk0") e = Some (WPtr (mkPtr fb (Obj fb))) /\
       lookup (TAtom "v4") e = Some (WInt n) /\ lookup (TAtom "pr.5") e = Some (WInt n) /\
       lookup (TAtom "pr.1") e = Some (WPtr src)⌝ -∗
     live fb freg -∗ int_cell fb off_flags fl -∗ short_input fb fresh rb -∗
     WP (ERun (mkFrame Unit_libio_fileops_os.fn__IO_new_file_xsputn e [] None (Enter (TAtom "L120") (Some (TAtom "L96")))) : gexpr) {{ Φ }}) -∗
  WP (ERun fr : gexpr) {{ Φ }}.
Proof using Type.
  intros Hfr Hfb Hal Hend Hrend Hn H512. injection Hfr as <-. unfold file_size in Hend.
  iIntros "Hl [%Hfl Hflags] (Hrp & Hre & Hrb & Hwb & Hwp & Hwe & Hbase & Hbend) HK".
  step. step. branch_as true. adv. load_s32 "Hl" "Hflags". adv. branch_as true. adv. branch_as true. adv.
  destruct fresh; cbn beta iota; unfold short_ptr, off_shortbuf.
  1: load_null "Hl" "Hwe"; adv; load_null "Hl" "Hwp".
  2: load_self_using wp_raw_load_pointer_self "Hl Hwe"; adv; load_self_using wp_raw_load_pointer_self "Hl Hwp".
  all: adv; branch_as true; adv; branch_as true; adv; branch_as false;
    iApply ("HK" with "[%] Hl [$Hflags //] [$Hrp $Hre $Hrb $Hwb $Hwp $Hwe $Hbase $Hbend]");
    split_and!; first [lk_prove | lookups; repeat f_equal; unwrap2; lia].
Qed.

Context (Hreg : holds_os registry) (Hext : sys_external ge) (Hfree : free_rule w0 registry ge).
Context `{!Defines ge "__GI__IO_doallocbuf" Unit_libio_genops_os.fn___GI__IO_doallocbuf}.
Context `{!Defines ge "__GI__IO_setb" Unit_libio_genops_os.fn___GI__IO_setb}.
Context `{!Defines ge "__GI___write" Unit_io_write_os.fn___GI___libc_write}.
Context `{!Defines ge "_IO_new_do_write" Unit_libio_fileops_os.fn__IO_new_do_write}.
Context (Hfw : ge_fn ge "_IO_new_file_write" Unit_libio_fileops_os.fn__IO_new_file_write)
  (Hov : ge_fn ge "_IO_new_file_overflow" Unit_libio_fileops_os.fn__IO_new_file_overflow).

(** The caller gets its input share and a tidy stream back. On a
    nonempty input, even an error leaves the write pointer and write
    end at the short byte, with nothing pending and no room. *)
Lemma wp_xsputn_short fr vb self fb freg st nb flags2 held dq b reg o c ys eb Φ :
  let fp := mkPtr fb (Obj fb) in let n := Z.of_nat (length ys) in let fd := fs_fileno st in
  call_frame Unit_libio_fileops_os.fn__IO_new_file_xsputn [WPtr fp; WPtr (mkPtr (b+o) c); WInt n] = Some fr ->
  fb mod 8 = 0 -> 0 < fb -> fb+file_size <= r_end freg -> r_end freg <= 2^63 -> flags_ok st ->
  idle_ok fd (fs_with_flags2 st 0) -> fs_flags2 st = flags2 -> fs_vtable st = mkPtr (vb+vt_file) (Ro vb) ->
  buf_ptrs_ok fb nb (fs_ptrs st) -> short_idle nb st -> has (fs_flags st) io_unbuffered = true ->
  has (fs_flags st) io_no_writes = false ->
  (Z.land flags2 2 = 0 \/ Z.land flags2 2 = 2 /\ find_fn ge (TAtom "__GI___write_nocancel") = Some (Defined Unit_io_write_nocancel_os.fn___GI___write_nocancel)) ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> In fd (ow_fds w0) ->
  (c = Obj b \/ c = Ro b) -> 0 < b -> 0 <= o -> b+o+n <= r_end reg -> r_end reg <= 2^63 -> Forall (fun y => 0 <= y < 256) ys ->
  fputs_ro vb -∗ live fb freg -∗ file_fields fb st -∗ lock_inv self (fs_lock st) held -∗ buf_idle nb -∗
  wide_idle vb (fs_wide st) (fs_codecvt st) -∗ errno_any eb -∗ liveq dq b reg -∗ bytesq dq b o ys -∗
  ▷ (∀ r, ⌜r = 2^64-1 \/ 0 <= r <= n⌝ -∗ file_tidy vb self fp fd flags2 held -∗ errno_any eb -∗
     liveq dq b reg -∗ bytesq dq b o ys -∗ Φ (Ret (WInt r))) -∗ WP (ERun fr : gexpr) {{ Φ }}.
Proof using Type*.
  intros fp n fd Hfr Hal Hfb Hend Hrend Hok Hi Hf2 Hvt Hb Hshort Hu Hnw Hready He Hin Hc Hb0 Ho Hen Hr Hy.
  iIntros "#Hro Hl Hf Hlk Hb Hw Herr Hbl Hys HK". subst fp fd. iDestruct "Hro" as (vr sb sr) "[#Hvt _]".
  destruct (Z.eq_dec n 0) as [H0|Hn].
  { injection Hfr as <-. step. step. branch_as false. step. iApply wp_ret; [reflexivity|vx|]. iNext.
    change (0 mod 2^64) with 0. iApply ("HK" $! 0 with "[%] [Hl Hf Hlk Hb Hw] Herr Hbl Hys"); [right; lia|].
    iExists fb, freg, st, nb. iFrame. done. }
  iAssert (⌜exists fresh : bool, nb = if fresh then NbNone else NbShort⌝)%I with "[Hb]" as %(fresh & ->).
  { destruct nb; try (iPureIntro; first [exists true; reflexivity | exists false; reflexivity]);
      [destruct Hshort as (_ & Hb0' & _); congruence | iDestruct "Hb" as "[]"]. }
  iDestruct (short_fields vb self fb freg st fresh (fs_fileno st) flags2 held eb with "Hf Hlk Hw Herr") as (rb byte)
    "(Hp & Hfl & Htw & Hoff & Hbyte & (Hf2 & Hfd & Herr & Hcol & Hmode & Hvtp) & Hclose)"; try assumption.
  pose proof (proj1 (proj1 Hshort) Hu) as Hline. pose proof Hok as (_ & _ & _ & Hbk & _).
  pose proof Hi as (_ & _ & Hmode & _ & _ & _ & _ & _ & _ & _ & _ & Happ & _).
  cbn [fs_with_flags2 fs_mode fs_flags] in Hmode, Happ.
  unfold has in Hu, Hnw, Hbk, Happ, Hline. apply negb_true_iff, Z.eqb_neq in Hu.
  apply negb_false_iff, Z.eqb_eq in Hnw, Hbk, Happ, Hline.
  assert (Hpos : 0 < n < 2^63) by (unfold n in *; lia).
  iApply (wp_xs_short_enter fr fb freg (mkPtr (b+o) c) n fresh rb (fs_flags st) with "Hl Hfl Hp"); try assumption.
  iNext. iIntros (e (Hv0 & Hc0 & Hv4 & Hp5 & Hp1)) "Hl Hfl Hp".
  iPoseProof (vtables_slot ge vb vr slot_overflow "_IO_new_file_overflow" with "Hvt") as "#Hslot"; [cbn; tauto|].
  iAssert (live_capq DfracDiscarded (ptr_cap (sym_ptr ge "_IO_new_file_overflow")) vr) as "Hfc". { rewrite (ge_fn_cap _ _ _ Hov). done. }
  iPoseProof "Hvt" as "((%Hvg & %Hvend & %Hval & %Hvb & %Hvr) & Hvl & _)". unfold io_vtables_size in Hvend. unfold file_size in Hend.
  adv. iApply (wp_raw_load_pointer_dq with "Hl Hvtp Hvl"); [reflexivity|vx|left; reflexivity|ar|ar|cbn; unfold vt_file in *; lia|].
  iNext. iIntros "Hl Hvtp #Hvl'". do 5 step. branch_as true. step. step. norm. check_read_dq "Hvl'" by ar. iNext. iIntros "_".
  iApply (wp_raw_load_pointer_dq with "Hvl' Hslot Hfc"); [reflexivity|vx|right; reflexivity|ar|ar|apply (ge_fn_addr _ _ _ Hov)|].
  iNext. iIntros "_ _ _". iApply wp_check_function; [vx|apply (ge_fn_check _ _ _ Hov)|]. iNext.
  iApply wp_raw_call_bind; [vx|apply (ge_fn_cap _ _ _ Hov)|apply (ge_fn_check _ _ _ Hov)|vx|apply (ge_fn_find _ _ _ Hov)|reflexivity|reflexivity|]. iNext.
  iApply (wp_short_file_overflow Hreg Hext Hfree Hfw _ fb freg (2^32-1) flags2 (fs_fileno st) eb (fs_mode st) vb vr fresh rb (fs_flags st) (fs_total st) (fs_offset st) byte
    with "Hvt Hl [$Hf2 $Hfd $Herr $Hcol $Hmode $Hvtp] Hp Hfl Htw Hoff Hbyte"); try first [assumption|reflexivity|right; reflexivity].
  { intros ->. destruct Hshort as [_ H]. unfold has in H. apply negb_false_iff, Z.eqb_eq in H. exact H. }
  iNext. iIntros (r rb' b' fl' tw' off' (_ & Heof & _ & Hflags)) "Hl Hfix Hst". specialize (Heof eq_refl). subst r.
  iExists _. iSplit; [done|]. iNext. cbn [fr_fn fr_env fr_locals fr_doomed fr_at]. step. branch_as true.
  assert (Happ' : Z.land fl' io_is_appending = 0) by (rewrite (short_flags_mask _ _ _ _ Hflags); auto; reflexivity).
  assert (Hmask : Z.land fl' 514 <> 0).
  { intro Hz. apply Hu. change io_unbuffered with (Z.land 514 2). rewrite -(short_flags_mask _ _ _ _ Hflags) // Z.land_assoc Hz. reflexivity. }
  iApply (wp_xs_short_write Hreg Hext Hfw fb freg rb' fl' flags2 (fs_fileno st) tw' off' b' (fs_mode st) vb vr dq b reg o c ys eb with "Hvt Hl Hfix Hst Hbl Hys");
    try first [assumption | lia | lk_prove].
  iNext. iIntros (r fl'' tw'' off'' Hpost) "Hl Hfix Hst Hbl Hys".
  assert (Hflags' : short_flags fresh (fs_flags st) fl'').
  { destruct Hpost as [[_ ->]|[_ ->]]; [exact Hflags|]. destruct Hflags as (f & Hf & [->| ->]); exists f; split; [exact Hf|right; reflexivity|exact Hf|right; apply lor_err_twice]. }
  iDestruct ("Hclose" with "[%] Hl Hst Hfix") as "[Htidy Herr]"; [intuition|].
  iApply ("HK" with "[%] Htidy Herr Hbl Hys"). right. destruct Hpost as [[-> _]|[? _]]; lia.
Qed.
End xsputn.
