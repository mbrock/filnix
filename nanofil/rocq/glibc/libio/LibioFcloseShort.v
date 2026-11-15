(** Fclose can close static stderr without freeing its in-object short buffer.
    This rule covers empty pending output in a narrow or unoriented stream.
    It takes the free lock, closes the descriptor, releases the lock and
    removes the stream from the list, even when descriptor close fails.
    Nonempty output and Hello's surrounding close callback remain separate. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics OsBlocks OsWorld OsRegistry
  SysCode SysWrappers LibioReadCode LibioDoWriteCode LibioCloseItCode LibioGenCode
  LibioUnlinkCode LibioUnlink LibioFcloseCode FileInv LibioLogic LibioCloseSteps LibioCloseItEnd
  LibioFcloseTail LibioFcloseLock LibioFclose LibioCloseItShort.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L OsWorld
  FileInv LibioLogic LibioCloseSteps.
Open Scope Z_scope.

Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (Hreg : holds_os registry) (Hext : sys_external ge).
Context `{Hcn : !Defines ge "__GI___close_nocancel" glibc___close_nocancel}
  (Hfc : ge_fn ge "__GI__IO_file_close" glibc__IO_file_close)
  `{Hsetb : !Defines ge "__GI__IO_setb" glibc__IO_setb}
  `{Hdwf : !Defines ge "_IO_new_do_write" glibc__IO_new_do_write}
  `{Hfum : !Defines ge "__GI__IO_unsave_markers" glibc__IO_unsave_markers}
  `{Hpush : !Defines ge "__GI___libc_cleanup_push_defer" glibc___libc_cleanup_push_defer}
  `{Hpop : !Defines ge "__GI___libc_cleanup_pop_restore" glibc___libc_cleanup_pop_restore}
  `{Hunl : !Defines ge "__GI__IO_un_link" glibc__IO_un_link}
  `{Hdf : !Defines ge "__GI__IO_default_finish" glibc__IO_default_finish}
  (Hff : ge_fn ge "_IO_new_file_finish" glibc__IO_new_file_finish)
  `{Hcif : !Defines ge "_IO_file_close_maybe_unlink" glibc__IO_file_close_maybe_unlink}.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** The linked stderr address differs from stdin and stdout, so the actual
    final comparison selects the static-object return. The descriptor result
    survives unlink and finish. Errno ownership, cleanup state, remaining
    stream lifetimes and arbitrary caller resources all return to the caller. *)
Lemma wp_glibc__IO_new_fclose_stderr_short_empty fr pre post fb freg fl f2 fd off rp re rb we be eb vb vreg
    lb lbreg sb sreg fcp pin pout md (E : iProp Σ) Φ :
  let fp := mkPtr fb (Obj fb) in
  let buf := mkPtr (fb + off_shortbuf) (Obj fb) in
  call_frame glibc__IO_new_fclose [WPtr fp] = Some fr ->
  lookup (TAtom "_IO_2_1_stderr_") (ge_globals ge) = Some fp ->
  lookup (TAtom "_IO_2_1_stdout_") (ge_globals ge) = Some pout -> ptr_addr pout <> fb ->
  0 <= ptr_addr pout < 2 ^ 64 ->
  lookup (TAtom "_IO_2_1_stdin_") (ge_globals ge) = Some pin -> ptr_addr pin <> fb ->
  0 <= ptr_addr pin < 2 ^ 64 ->
  lookup (TAtom "glibc_genops#flush_cleanup") (ge_globals ge) = Some fcp -> 0 <= ptr_addr fcp < 2 ^ 64 ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  0 <= f2 < 2 ^ 32 -> Z.land f2 32 = 0 -> 0 <= fd < 2 ^ 31 ->
  0 <= fl < 2 ^ 32 -> Z.land fl io_no_writes = 0 -> Z.land fl io_currently_putting <> 0 ->
  Z.land fl io_user_buf <> 0 -> has fl io_user_lock = false ->
  has fl io_linked = true -> has fl io_is_filebuf = true ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> 0 < lb -> md = 0 \/ md = 2 ^ 32 - 1 ->
  vtables_ro ge vb vreg -∗ single_ro ge sb sreg -∗ tcb_cleanup_inv (ow_self w0) -∗
  live fb freg -∗ int_cell fb off_flags fl -∗ int_cell fb off_flags2 f2 -∗ int_cell fb off_fileno fd -∗
  icell fb off_offset off -∗ errno_any eb -∗
  pcell fb 8 rp -∗ pcell fb 16 re -∗ pcell fb 24 rb -∗ pcell fb 32 buf -∗ pcell fb 40 buf -∗
  pcell fb 48 we -∗ pcell fb off_buf_base buf -∗ pcell fb off_buf_end be -∗
  int_cell fb off_mode md -∗ pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗
  pcell fb 80 null -∗ pcell fb 96 null -∗
  pcell fb off_lock (mkPtr lb (Obj lb)) -∗ lock_state lb lbreg 0 0 null -∗
  io_list_inv ge (pre ++ fp :: post) -∗ ([∗ list] g ∈ pre ++ post, stream_life g) -∗ E -∗
  ▷ (∀ k, ⌜k = 0 \/ k = 2 ^ 32 - 1⌝ -∗ tcb_cleanup_inv (ow_self w0) -∗
     live fb freg -∗ int_cell fb off_flags (Z.land (closed_flags fl) 4294967167) -∗
     (∃ f2', int_cell fb off_flags2 f2') -∗ int_cell fb off_fileno (2 ^ 32 - 1) -∗
     icell fb off_offset (2 ^ 64 - 1) -∗ errno_any eb -∗
     pcell fb 8 null -∗ pcell fb 16 null -∗ pcell fb 24 null -∗ pcell fb 32 null -∗ pcell fb 40 null -∗
     pcell fb 48 null -∗ pcell fb off_buf_base null -∗ pcell fb off_buf_end null -∗
     int_cell fb off_mode md -∗ pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗
     pcell fb 80 null -∗ pcell fb 96 null -∗
     pcell fb off_lock (mkPtr lb (Obj lb)) -∗ lock_state lb lbreg 0 0 null -∗
     io_list_inv ge (pre ++ post) -∗ ([∗ list] g ∈ pre ++ post, stream_life g) -∗
     (∃ c p, pcell fb off_chain c ∗ pcell fb off_prevchain p) -∗ E -∗ Φ (Ret (WInt k))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros fp buf Hfr Hgerr Hgout Hout Houtr Hgin Hin Hinr Hcleanup Hfcr Hfb Hfal Hfend Hfreg
    Hf2r Hf232 Hfdr Hfl Hnw Hcp Hub Hul Hlnk Hfb8 He Hlb Hmd. subst fp buf.
  iIntros "#Hvt #Hs Htcb Hl Hfl Hfl2 Hfd Hoff Herr Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend Hmode Hvtp
    H80 H96 Hlp Hlk Hio Hlives HE HK".
  unfold file_size in Hfend.
  pose proof Hfb8 as Hfb8'. unfold has, io_is_filebuf in Hfb8'. apply negb_true_iff, Z.eqb_neq in Hfb8'.
  assert (0 <= Z.land fl 8192 < 2 ^ 32) by (apply land_lt32; lia).
  iApply (wp_fclose_start Hreg Hext _ _ _ _ _ _ _ _ _ Hfr with "Hs Htcb Hl Hfl Hlp Hlk"); try close_side.
  iIntros (e from [Hv0 Hc0]) "Htcb Hl Hfl Hlp Hlk".
  iApply (wp_live_fit1 with "Hl"). iIntros ([Hf0 Hf48]) "Hl".
  iDestruct "Hfl" as "[_ Hfl]".
  step. check "Hl". load_s32 "Hl" "Hfl". step. branch_as false. step.
  iAssert (int_cell fb off_flags fl) with "[Hfl]" as "Hfl"; [iSplit; [done | iExact "Hfl"]|].
  iApply wp_call_bind; [vx | exact Hcif | reflexivity |]. iNext.
  iApply (wp_glibc__IO_file_close_short_empty Hreg Hext Hfc
    with "Hvt Hl Hfl Hfl2 Hfd Hoff Hmode Hvtp Herr Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend H80 H96 HE");
    try close_side; try exact Hmd.
  iNext. iIntros (k Hk) "Hl Hfl Hfl2 Hfd Hoff Hmode Hvtp Herr H8 H16 H24 H32 H40 H48 Hbb Hbe H80 H96 HE". resume.
  iDestruct "Hfl2" as "[%Hf2r' Hfl2]".
  step. check "Hl". load_s32 "Hl" "Hfl2". step. step. step. load_s32 "Hl" "Hfl2". step. step. step. check "Hl". store_int "Hl" "Hfl2". step.
  iAssert (∃ f2', int_cell fb off_flags2 f2')%I with "[Hfl2]" as "Hfl2".
  { iExists _. iSplit; [iPureIntro | iExact "Hfl2"].
    first [apply Z.mod_pos_bound; lia | apply lor_lt32; apply Z.mod_pos_bound; lia]. }
  iDestruct "Hfl" as "[%Hclr Hfl]".
  iAssert (int_cell fb off_flags (closed_flags fl)) with "[Hfl]" as "Hfl"; [iSplit; [done | iExact "Hfl"]|].
  assert (Hcl : has (closed_flags fl) io_linked = true).
  { unfold has, io_linked. rewrite closed_linked. exact Hlnk. }
  assert (Hcu : has (closed_flags fl) io_user_lock = false).
  { unfold has, io_user_lock. rewrite closed_user_lock. reflexivity. }
  assert (Hkr : 0 <= k < 2 ^ 32) by (destruct Hk as [-> | ->]; lia).
  cbn [edge_label]. iApply (wp_fclose_L101_static_output Hff
    (LibioUnlink.wp_glibc__IO_un_link Hreg Hext) LibioUnlink.wp_glibc__IO_un_link_unlinked
    with "Hvt Hs Htcb Hl Hfl Hlp Hlk Hio Hlives Hfd Hmode Hvtp Hbb H80 H96 [-]");
    try close_side; try exact Hmd.
  { right. auto. }
  iNext. iIntros "Htcb Hl Hfl Hlp Hlk Hio Hlives Hlinks Hfd Hmode Hvtp Hbb H80 H96".
  rewrite (Z.mod_small k (2 ^ 32) Hkr).
  iApply ("HK" $! k with "[%] Htcb Hl Hfl Hfl2 Hfd Hoff Herr H8 H16 H24 H32 H40 H48 Hbb Hbe
    Hmode Hvtp H80 H96 Hlp Hlk Hio Hlives Hlinks HE"). exact Hk.
Qed.
End rules.
