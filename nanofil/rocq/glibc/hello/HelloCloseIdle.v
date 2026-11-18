(** Hello closes stdout and stderr at exit, and each of them is idle
    between calls, as [FileIdle](FileIdle.v) describes. An idle stream
    may have no buffer, its one-byte short buffer or a heap buffer, and
    only a heap buffer can hold pending output. This file proves that
    `c: _IO_file_close_maybe_unlink` closes an idle stream in every one
    of these states. *)

From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry SysCode SysWrappers LibioReadCode LibioDoWriteCode
  LibioCloseItCode LibioGenCode FileInv FileIdle LibioLogic LibioCloseSteps LibioCloseItEnd LibioCloseItMid
  LibioPutsInv LibioFflushIdle LibioGenLeaves LibioUnlinkCode LibioFcloseCode LibioFcloseTail LibioFcloseLock
  LibioFclose LibioUnlink HelloClosedStdout.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L OsWorld
  FileInv LibioLogic LibioCloseSteps LibioFcloseTail.
Open Scope Z_scope.

(** ## Closing a stream that is not putting

    Most idle streams have nothing to write when Hello closes them. The
    close function then skips the write and only closes the descriptor
    and drops the buffer. This section proves that path. *)

Section quiet.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (Hfc : ge_fn ge "__GI__IO_file_close" glibc__IO_file_close)
  `{Hsetb : !Defines ge "__GI__IO_setb" glibc__IO_setb}
  `{Hfum : !Defines ge "__GI__IO_unsave_markers" glibc__IO_unsave_markers}.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

Local Ltac load_buf H :=
  iApply (wp_load_buf_ptr with H);
    [reflexivity | vx | reflexivity | a2 | a2 | lia | lia | eassumption |];
  iNext; iIntros H.

(** A stream that is not putting has no output to write. The close
    function then asks whether the stream read ahead of its descriptor.
    An idle stream never did, because its read pointer equals its read
    end. So the function goes on to close the descriptor and drop the
    buffer, and [wp_close_it_L18_with] proves that part. The buffer
    resource B is whatever the setb rule needs. The rule reads the two
    read pointers while it still holds the whole idle buffer, and only
    then gives the buffer up as B. *)
Lemma wp_close_it_quiet (B : Z -> Z -> ptr -> iProp Σ) (Hclose : close_spec w0 registry ge)
    (Hsb : setb_spec_with w0 registry ge B)
    fr fb freg fl f2 fd off md nb p p24 p32 p40 p48 bp be vb vreg eb Φ :
  call_frame glibc__IO_file_close_maybe_unlink [WPtr (mkPtr fb (Obj fb)); WInt 0] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  0 <= f2 < 2 ^ 32 -> Z.land f2 32 = 0 -> 0 <= fd < 2 ^ 31 ->
  0 <= fl < 2 ^ 32 -> Z.land fl io_no_writes = 0 -> Z.land fl io_currently_putting = 0 ->
  Z.land fl io_in_backup = 0 -> ow_errno w0 = Some (mkPtr eb (Obj eb)) -> md = 0 \/ md = 2 ^ 32 - 1 ->
  in_buf fb nb p ->
  vtables_ro ge vb vreg -∗ live fb freg -∗ int_cell fb off_flags fl -∗
  int_cell fb off_flags2 f2 -∗ int_cell fb off_fileno fd -∗ icell fb off_offset off -∗
  int_cell fb off_mode md -∗ pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗ errno_any eb -∗
  pcell fb 8 p -∗ pcell fb 16 p -∗ pcell fb 24 p24 -∗ pcell fb 32 p32 -∗ pcell fb 40 p40 -∗
  pcell fb 48 p48 -∗ pcell fb off_buf_base bp -∗ pcell fb off_buf_end be -∗
  pcell fb 80 null -∗ pcell fb 96 null -∗ buf_idle nb -∗ (buf_idle nb -∗ B fb fl bp) -∗
  ▷ (∀ k, ⌜k = 0 \/ k = 2 ^ 32 - 1⌝ -∗
     live fb freg -∗ int_cell fb off_flags (closed_flags fl) -∗ int_cell fb off_flags2 f2 -∗
     int_cell fb off_fileno (2 ^ 32 - 1) -∗ icell fb off_offset (2 ^ 64 - 1) -∗
     int_cell fb off_mode md -∗ pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗ errno_any eb -∗
     pcell fb 8 null -∗ pcell fb 16 null -∗ pcell fb 24 null -∗ pcell fb 32 null -∗ pcell fb 40 null -∗
     pcell fb 48 null -∗ pcell fb off_buf_base null -∗ pcell fb off_buf_end null -∗
     pcell fb 80 null -∗ pcell fb 96 null -∗ Φ (Ret (WInt k))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof using Type*.
  intros Hfr. injection Hfr as <-.
  intros Hfb Hfal Hfend Hfreg Hf2r Hf232 Hfdr Hfl Hnw Hcp Hbk He Hmd Hin.
  iIntros "#Hvt Hl Hfl Hfl2 Hfd Hoff Hmode Hvtp Herr Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend H80 H96 Hb HB HK".
  unfold file_size in Hfend. unfold io_no_writes in Hnw. unfold io_currently_putting in Hcp.
  unfold io_in_backup in Hbk.
  iApply (wp_live_fit1 with "Hl"). iIntros ([Hf0 Hf48]) "Hl".
  assert (0 <= fd < 2 ^ 32) by lia.
  assert (0 <= Z.land fl 8 < 2 ^ 32) by (rewrite Hnw; lia).
  assert (0 <= Z.land fl 2048 < 2 ^ 32) by (rewrite Hcp; lia).
  assert (0 <= Z.land fl 256 < 2 ^ 32) by (rewrite Hbk; lia).
  iDestruct "Hfd" as "[_ Hfd]". iDestruct "Hfl" as "[_ Hfl]". iDestruct "Hmode" as "[%Hmr Hmode]".
  (* start, L7, L23, L24: open, writable and not putting. *)
  step. step. check "Hl". load_s32 "Hl" "Hfd". step. branch_as true.
  step. check "Hl". load_s32 "Hl" "Hfl". step. step. branch_as false.
  step. load_s32 "Hl" "Hfl". step. step. step. step. branch_as true.
  (* L17, L81, L86: open, no backup area, narrow. *)
  step. step. load_s32 "Hl" "Hfd". step. branch_as false.
  step. load_s32 "Hl" "Hfl". step. branch_as true.
  step. step. check "Hl". load_s32 "Hl" "Hmode". step.
  assert (Esx : (sign_extension (2 ^ 32) (2 ^ 31) (md mod 2 ^ 32) <=?
                sign_extension (2 ^ 32) (2 ^ 31) (0 mod 2 ^ 32)) = true)
    by (destruct Hmd as [-> | ->]; reflexivity).
  rewrite Esx. clear Esx. branch.
  (* L92, L87, L110, L82: the read pointer equals the read end, so no seek. *)
  step. step. check "Hl". load_buf "Hl Hrp Hb". step. load_buf "Hl Hre Hb". step. step. step.
  step. step. branch_as true.
  step. step. check "Hl". load_s32 "Hl" "Hmode". step.
  assert (Esx : (sign_extension (2 ^ 32) (2 ^ 31) (0 mod 2 ^ 32) <? sign_extension (2 ^ 32) (2 ^ 31) (md mod 2 ^ 32))
                = false) by (destruct Hmd as [-> | ->]; reflexivity).
  rewrite Esx. clear Esx. branch. step. branch_as true.
  (* L18: close the descriptor and drop the buffer. *)
  iAssert (int_cell fb off_flags fl) with "[Hfl]" as "Hfl"; [iSplit; [done | iExact "Hfl"]|].
  iAssert (int_cell fb off_fileno fd) with "[Hfd]" as "Hfd"; [iSplit; [done | iExact "Hfd"]|].
  iAssert (int_cell fb off_mode md) with "[Hmode]" as "Hmode"; [iSplit; [done | iExact "Hmode"]|].
  iApply (LibioCloseItMid.wp_close_it_L18_with Hfc Hclose B Hsb
    glibc__IO_unsave_markers LibioGenLeaves.unsave_spec_holds
    with "Hvt Hl Hfl Hfl2 Hfd Hoff Hmode Hvtp Herr Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend [Hb HB] H80 H96");
    first [intros blk Hblk; vm_compute in Hblk; injection Hblk as <-; reflexivity | try close_side; try exact Hmd].
  { iApply ("HB" with "Hb"). }
  iNext. iIntros (k Hk) "Hl Hfl Hfl2 Hfd Hoff Hmode Hvtp Herr H8 H16 H24 H32 H40 H48 Hbb Hbe H80 H96".
  assert (Ek : (if k =? 0 then 0 else k) = k) by (destruct Hk as [-> | ->]; reflexivity).
  rewrite Ek. iApply ("HK" $! k with "[%] Hl Hfl Hfl2 Hfd Hoff Hmode Hvtp Herr
    H8 H16 H24 H32 H40 H48 Hbb Hbe H80 H96"). exact Hk.
Qed.
End quiet.

(** ## Closing a static stream

    Fclose takes the stream's lock, calls the close function above,
    marks the stream closed, releases the lock and unlinks the stream.
    Only the close function depends on the stream's buffer, so the rule
    below takes its triple as a premise. *)

(** After the close function, the stream's descriptor is gone, every
    buffer pointer is null and its flags are the closed flags. The
    predicate [closed_it] names those fields. *)
Definition closed_it `{!gen_heapGS piece pval Σ} (fb vb md f2 fl : Z) : iProp Σ :=
  int_cell fb off_flags (closed_flags fl) ∗ int_cell fb off_flags2 f2 ∗
  int_cell fb off_fileno (2 ^ 32 - 1) ∗ icell fb off_offset (2 ^ 64 - 1) ∗
  int_cell fb off_mode md ∗ pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) ∗
  pcell fb 8 null ∗ pcell fb 16 null ∗ pcell fb 24 null ∗ pcell fb 32 null ∗ pcell fb 40 null ∗
  pcell fb 48 null ∗ pcell fb off_buf_base null ∗ pcell fb off_buf_end null ∗
  pcell fb 80 null ∗ pcell fb 96 null.

Section fclose.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (Hreg : holds_os registry) (Hext : sys_external ge).
Context `{Hunl : !Defines ge "__GI__IO_un_link" glibc__IO_un_link}
  `{Hpush : !Defines ge "__GI___libc_cleanup_push_defer" glibc___libc_cleanup_push_defer}
  `{Hpop : !Defines ge "__GI___libc_cleanup_pop_restore" glibc___libc_cleanup_pop_restore}
  `{Hdf : !Defines ge "__GI__IO_default_finish" glibc__IO_default_finish}
  (Hff : ge_fn ge "_IO_new_file_finish" glibc__IO_new_file_finish)
  `{Hcif : !Defines ge "_IO_file_close_maybe_unlink" glibc__IO_file_close_maybe_unlink}.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** Hello closes stdout and stderr, which are static objects, so fclose
    does not free them. The closed object keeps the fields that a later
    flush of stdout reads, as [closed_stdout] describes. The close
    function's triple takes the stream's lifetime and flags and any
    other resources R, and gives back resources R'. It may change the
    flags only by setting the write-error bit, so the linked bit stays. *)
Lemma wp_fclose_with fr pre post fb freg fl md lb lbreg sb sreg fcp pin pout vb vreg (R R' : iProp Σ) Φ :
  let fp := mkPtr fb (Obj fb) in
  call_frame glibc__IO_new_fclose [WPtr fp] = Some fr ->
  lookup (TAtom "_IO_2_1_stdout_") (ge_globals ge) = Some pout ->
  (pout = fp \/ (ptr_addr pout <> fb /\ 0 <= ptr_addr pout < 2 ^ 64 /\
    lookup (TAtom "_IO_2_1_stderr_") (ge_globals ge) = Some fp)) ->
  lookup (TAtom "_IO_2_1_stdin_") (ge_globals ge) = Some pin -> ptr_addr pin <> fb ->
  0 <= ptr_addr pin < 2 ^ 64 ->
  lookup (TAtom "glibc_genops#flush_cleanup") (ge_globals ge) = Some fcp -> 0 <= ptr_addr fcp < 2 ^ 64 ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  0 <= fl < 2 ^ 32 -> has fl io_user_lock = false -> has fl io_linked = true -> has fl io_is_filebuf = true ->
  0 < lb -> md = 0 \/ md = 2 ^ 32 - 1 ->
  vtables_ro ge vb vreg -∗ single_ro ge sb sreg -∗ tcb_cleanup_inv (ow_self w0) -∗
  live fb freg -∗ int_cell fb off_flags fl -∗ pcell fb off_lock (mkPtr lb (Obj lb)) -∗
  lock_state lb lbreg 0 0 null -∗
  io_list_inv ge (pre ++ fp :: post) -∗ ([∗ list] g ∈ pre ++ post, stream_life g) -∗ R -∗
  (∀ fr' Ψ, ⌜call_frame glibc__IO_file_close_maybe_unlink [WPtr fp; WInt 0] = Some fr'⌝ -∗
     live fb freg -∗ int_cell fb off_flags fl -∗ R -∗
     ▷ (∀ k fl' f2, ⌜(k = 0 \/ k = 2 ^ 32 - 1) /\ Z.land fl' 128 = Z.land fl 128⌝ -∗
        live fb freg -∗ closed_it fb vb md f2 fl' -∗ R' -∗ Ψ (Ret (WInt k))) -∗
     WP (ERun fr' : sexpr) {{ Ψ }}) -∗
  ▷ (∀ k, ⌜k = 0 \/ k = 2 ^ 32 - 1⌝ -∗ tcb_cleanup_inv (ow_self w0) -∗
     io_list_inv ge (pre ++ post) -∗ ([∗ list] g ∈ pre ++ post, stream_life g) -∗
     closed_stdout fb freg vb lb lbreg -∗ R' -∗ Φ (Ret (WInt k))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof using Type*.
  intros fp Hfr Hgout Hout Hgin Hin Hinr Hfc Hfcr Hfb Hfal Hfend Hfreg Hfl Hul Hlnk Hfb8 Hlb Hmd.
  iIntros "#Hvt #Hs Htcb Hl Hfl Hlp Hlk Hio Hlives HR HCI HK".
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
  iApply ("HCI" with "[%] Hl Hfl HR"); [reflexivity|].
  iNext. iIntros (k fl' f2 [Hk Hlnk']) "Hl (Hfl & Hfl2 & Hfd & Hoff & Hmode & Hvtp & H8 & H16 & H24 & H32 & H40 &
    H48 & Hbb & Hbe & H80 & H96) HR'". resume.
  iDestruct "Hfl2" as "[%Hf2r' Hfl2]".
  step. check "Hl". load_s32 "Hl" "Hfl2". step. step. step. load_s32 "Hl" "Hfl2". step. step. step. check "Hl". store_int "Hl" "Hfl2". step.
  iDestruct "Hfl" as "[%Hclr Hfl]".
  iAssert (int_cell fb off_flags (closed_flags fl')) with "[Hfl]" as "Hfl"; [iSplit; [done | iExact "Hfl"]|].
  assert (Hcl : has (closed_flags fl') io_linked = true).
  { unfold has, io_linked in *. rewrite LibioFclose.closed_linked Hlnk'. exact Hlnk. }
  assert (Hcu : has (closed_flags fl') io_user_lock = false).
  { unfold has, io_user_lock. rewrite LibioFclose.closed_user_lock. reflexivity. }
  assert (Hkr : 0 <= k < 2 ^ 32) by (destruct Hk as [-> | ->]; lia).
  cbn [edge_label]. iApply (wp_fclose_L101_static_output Hff
    (LibioUnlink.wp_glibc__IO_un_link Hreg Hext) LibioUnlink.wp_glibc__IO_un_link_unlinked
    with "Hvt Hs Htcb Hl Hfl Hlp Hlk Hio Hlives Hfd Hmode Hvtp Hbb H80 H96 [-]");
    try close_side; try exact Hmd; try exact Hout.
  iNext. iIntros "Htcb Hl Hfl Hlp Hlk Hio Hlives _ _ _ Hvtp _ _ _".
  rewrite (Z.mod_small k (2 ^ 32) Hkr). rewrite stdout_closed_flags.
  iApply ("HK" $! k with "[%] Htcb Hio Hlives [-HR'] HR'"); [exact Hk|].
  unfold closed_stdout, closed_stdout_fields. iFrame.
Qed.
End fclose.
