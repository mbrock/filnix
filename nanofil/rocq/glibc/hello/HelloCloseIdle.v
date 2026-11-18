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
  LibioFclose LibioUnlink HelloClosedStdout LibioCloseItShort AllocLogic HiAtexitBase HiAtexitDoWrite
  HiAtexitSetb HiAtexitCloseIt.
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

(** ## Closing an idle stream

    An idle stream has one of three buffers, and only a heap buffer can
    hold output. This section picks the close rule for each buffer and
    each value of the putting bit, so a caller holding [file_idle] needs
    no case analysis of its own. *)

Section idle.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (Hreg : holds_os registry) (Hext : sys_external ge).
Context `{Hwrite : !Defines ge "__GI___write" glibc___libc_write}
  (Hfw : ge_fn ge "_IO_new_file_write" glibc__IO_new_file_write)
  `{Hfree_fn : !Defines ge "free" free_fn}
  (Hfh : frees_heap (ge_free ge))
  (Hzf : find_fn ge zgc_free_name = None)
  (Hzg : lookup zgc_free_name (ge_globals ge) = None)
  `{Hcn : !Defines ge "__GI___close_nocancel" glibc___close_nocancel}
  (Hfc : ge_fn ge "__GI__IO_file_close" glibc__IO_file_close)
  `{Hsetb : !Defines ge "__GI__IO_setb" glibc__IO_setb}
  `{Hdwf : !Defines ge "_IO_new_do_write" glibc__IO_new_do_write}
  `{Hfum : !Defines ge "__GI__IO_unsave_markers" glibc__IO_unsave_markers}.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** The close function closes an idle stream that writes to a standard
    output descriptor. It writes whatever the heap buffer holds, closes
    the descriptor and drops the buffer. Its flags change only by the
    write-error bit, and errno comes back. *)
Lemma wp_close_it_idle fr fb freg st nb fd vb vreg eb Ψ :
  call_frame glibc__IO_file_close_maybe_unlink [WPtr (mkPtr fb (Obj fb)); WInt 0] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  flags_ok st -> idle_ok fd st -> fd <> 0 -> In fd (ow_fds w0) ->
  fs_vtable st = mkPtr (vb + vt_file) (Ro vb) -> buf_ptrs_ok fb nb (fs_ptrs st) -> short_idle nb st ->
  length (fs_ptrs st) = 12%nat -> length (fs_column st) = 8%nat -> ow_errno w0 = Some (mkPtr eb (Obj eb)) ->
  vtables_ro ge vb vreg -∗ live fb freg -∗ int_cell fb off_flags (fs_flags st) -∗
  ([∗ list] i ↦ p ∈ fs_ptrs st, pcell fb (off_ptr i) p) -∗
  int_cell fb off_fileno (fs_fileno st) -∗ int_cell fb off_flags2 (fs_flags2 st) -∗
  bytes fb off_column (fs_column st) -∗ icell fb off_offset (fs_offset st) -∗
  int_cell fb off_mode (fs_mode st) -∗ icell fb off_total_written (fs_total st) -∗
  pcell fb off_vtable (fs_vtable st) -∗ buf_idle nb -∗ errno_any eb -∗
  ▷ (∀ k fl' f2, ⌜(k = 0 \/ k = 2 ^ 32 - 1) /\ Z.land fl' 128 = Z.land (fs_flags st) 128⌝ -∗
     live fb freg -∗ closed_it fb vb (fs_mode st) f2 fl' -∗ errno_any eb -∗ Ψ (Ret (WInt k))) -∗
  WP (ERun fr : sexpr) {{ Ψ }}.
Proof using Type*.
  intros Hfr Hfb Hfal Hfend Hfreg Hok Hidle Hfd0 Hfd Hvt Hbok Hshort Hlen Hcl He.
  iIntros "#Hvt Hl Hfl Hps Hfd Hf2 Hcol Hoff Hmd Htot Hvtp Hb Herr HK".
  destruct st as [fl ps fdd f2 oldoff col lk off cv wd frl frb md tw vt].
  cbn [fs_flags fs_ptrs fs_fileno fs_flags2 fs_old_offset fs_column fs_lock fs_offset fs_codecvt fs_wide
    fs_freeres_list fs_freeres_buf fs_mode fs_total fs_vtable] in *. subst vt.
  destruct ps as [|p0 [|p1 [|p2 [|p3 [|p4 [|p5 [|p6 [|p7 [|p8 [|p9 [|p10 [|p11 [|]]]]]]]]]]]]]; try discriminate Hlen.
  iDestruct "Hps" as "(P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & _)".
  pose proof Hok as (Hflr & Hmagic & Hfilebuf & Hbk & Hul & Hnl & Hunb).
  unfold idle_ok, fs_ptr in Hidle. cbn [nth fs_flags fs_ptrs fs_fileno fs_flags2 fs_column fs_mode] in Hidle.
  destruct Hidle as (Hfd012 & -> & Hmd & E8 & E9 & E11 & E01 & E13 & Hle34 & Hput & Hnw & Happ & Hlnk & Hf2a & Hf2b & Hcol2 & Hlk0).
  subst p0 p1 p8 p9 p11.
  specialize (Hnw Hfd0). unfold has in Hnw, Happ, Hbk.
  apply negb_false_iff, Z.eqb_eq in Hnw, Happ, Hbk.
  iDestruct "Hf2" as "[%Hf2r Hf2]". iAssert (int_cell fb off_flags2 f2) with "[Hf2]" as "Hf2"; [iSplit; done|].
  iDestruct "Hfd" as "[%Hfdr Hfd]". iAssert (int_cell fb off_fileno fd) with "[Hfd]" as "Hfd"; [iSplit; done|].
  assert (Hfdr' : 0 <= fd < 2 ^ 31) by lia.
  simpl in Hflr, Hmagic, Hfilebuf, Hbk, Hul, Hnl, Hunb.
  unfold short_idle, fs_ptr in Hshort. simpl in Hshort.
  destruct Hshort as [[Hub1 Hnw1] Hshort].
  destruct nb as [| |bb sz|bb]; cbn [buf_ptrs_ok take] in Hbok.
  4: { iDestruct "Hb" as "[]". }
  - (* No buffer: nothing was ever written. *)
    cbn in Hbok. injection Hbok; intros; subst.
    iApply (wp_close_it_quiet Hfc (fun _ => LibioCloseItEnd.old_base) (hi_close Hreg Hext) (hi_setb Hfh Hzf Hzg)
      with "Hvt Hl Hfl Hf2 Hfd Hoff Hmd Hvtp Herr P0 P1 P2 P3 P4 P5 P6 P7 P9 P11 Hb []");
      try first [exact Hfr | close_side | exact Hmd | reflexivity].
    all: try (unfold has in Hshort; apply negb_false_iff, Z.eqb_eq in Hshort; exact Hshort).
    { iIntros "_". iLeft. done. }
    iNext. iIntros (k Hk) "Hl Hfl Hf2 Hfd Hoff Hmd Hvtp Herr H8 H16 H24 H32 H40 H48 Hbb Hbe H80 H96".
    iApply ("HK" $! k fl f2 with "[%] Hl [$Hfl $Hf2 $Hfd $Hoff $Hmd $Hvtp $H8 $H16 $H24 $H32 $H40 $H48 $Hbb $Hbe
      $H80 $H96] Herr"). split; [exact Hk | reflexivity].
  - (* The short buffer: it holds nothing between calls. *)
    destruct Hbok as (E6 & E7 & Hall). cbn [nth] in E6, E7. subst p6 p7.
    destruct Hshort as (Hu & E43 & E54 & E36). subst p4 p5 p3.
    assert (Hub : Z.land fl io_user_buf <> 0).
    { destruct (Hunb Hu) as [H | H]; [unfold has in H; apply negb_true_iff, Z.eqb_neq in H; exact H|].
      cbn in H. discriminate H. }
    change (fb + 131) with (fb + off_shortbuf).
    destruct (Z.eq_dec (Z.land fl io_currently_putting) 0) as [Hcp | Hcp].
    + iApply (wp_close_it_quiet Hfc short_base (short_close_spec Hreg Hext) short_setb_spec
        with "Hvt Hl Hfl Hf2 Hfd Hoff Hmd Hvtp Herr P0 P1 P2 P3 P4 P5 P6 P7 P9 P11 Hb []");
        try first [exact Hfr | close_side | exact Hmd | reflexivity].
      { cbn. split; [reflexivity | unfold off_shortbuf; lia]. }
      { iIntros "_". iPureIntro. split; [reflexivity | exact Hub]. }
      iNext. iIntros (k Hk) "Hl Hfl Hf2 Hfd Hoff Hmd Hvtp Herr H8 H16 H24 H32 H40 H48 Hbb Hbe H80 H96".
      iApply ("HK" $! k fl f2 with "[%] Hl [$Hfl $Hf2 $Hfd $Hoff $Hmd $Hvtp $H8 $H16 $H24 $H32 $H40 $H48 $Hbb $Hbe
        $H80 $H96] Herr"). split; [exact Hk | reflexivity].
    + iApply (wp_glibc__IO_file_close_short_empty Hreg Hext Hfc
        with "Hvt Hl Hfl Hf2 Hfd Hoff Hmd Hvtp Herr P0 P1 P2 P3 P4 P5 P6 P7 P9 P11 Hb");
        try first [exact Hfr | close_side | exact Hmd | reflexivity].
      iNext. iIntros (k Hk) "Hl Hfl Hf2 Hfd Hoff Hmd Hvtp Herr H8 H16 H24 H32 H40 H48 Hbb Hbe H80 H96 _".
      iApply ("HK" $! k fl f2 with "[%] Hl [$Hfl $Hf2 $Hfd $Hoff $Hmd $Hvtp $H8 $H16 $H24 $H32 $H40 $H48 $Hbb $Hbe
        $H80 $H96] Herr"). split; [exact Hk | reflexivity].
  - (* A heap buffer: output may be pending. *)
    destruct Hbok as (E6 & E7 & Hall). cbn [nth] in E6, E7. subst p6 p7.
    destruct Hshort as (Hu & E26 & E36 & Hub & _). subst p2 p3.
    unfold has in Hub. apply negb_false_iff, Z.eqb_eq in Hub.
    repeat rewrite Forall_cons_iff in Hall.
    destruct Hall as (_ & _ & _ & _ & [Hc4 Ha4] & [Hc5 Ha5] & _).
    iDestruct "Hb" as (breg xs cs Hbp) "(Hbl & Hxs & Hcs)".
    pose proof Hbp as (Hk & Hbe & Hbreg & Hb0 & Hb8 & Hsz & Hlx & Hxr & Hlc).
    destruct (Z.eq_dec (Z.land fl io_currently_putting) 0) as [Hcp | Hcp].
    + iAssert (buf_idle (NbHeap bb sz)) with "[Hbl Hxs Hcs]" as "Hb"; [iExists breg, xs, cs; iFrame; done|].
      iApply (wp_close_it_quiet Hfc (fun _ => LibioCloseItEnd.old_base) (hi_close Hreg Hext) (hi_setb Hfh Hzf Hzg)
        with "Hvt Hl Hfl Hf2 Hfd Hoff Hmd Hvtp Herr P0 P1 P2 P3 P4 P5 P6 P7 P9 P11 Hb [] [HK]");
        try first [exact Hfr | close_side | exact Hmd | reflexivity].
      { cbn. split; [reflexivity | lia]. }
      { iIntros "(%breg' & %xs' & %cs' & %Hbp' & Hbl & _)". iRight. iExists bb, breg'. iFrame. iPureIntro.
        destruct Hbp' as (? & ? & ? & ? & _). split_and!; try done; lia. }
      iNext. iIntros (k Hk') "Hl Hfl Hf2 Hfd Hoff Hmd Hvtp Herr H8 H16 H24 H32 H40 H48 Hbb Hbe H80 H96".
      iApply ("HK" $! k fl f2 with "[%] Hl [$Hfl $Hf2 $Hfd $Hoff $Hmd $Hvtp $H8 $H16 $H24 $H32 $H40 $H48 $Hbb $Hbe
        $H80 $H96] Herr"). split; [exact Hk' | reflexivity].
    + destruct p4 as [a4 c4]. cbn [ptr_addr ptr_cap] in *. subst c4.
      set (ys := take (Z.to_nat (a4 - bb)) xs).
      iDestruct (bytes_take_drop bb 0 xs (Z.to_nat (a4 - bb)) with "Hxs") as "[Hys _]"; [lia|].
      assert (Hys : Z.of_nat (length ys) = a4 - bb) by (unfold ys; rewrite length_take; lia).
      iDestruct (bytes_take_drop fb off_column col 2 with "Hcol") as "[Hcol _]"; [lia|]. rewrite Hcol2.
      pose proof (hi_close_it Hreg Hext Hfw Hfh Hzf Hzg Hfc fr fb freg fl f2 fd tw off bb breg 0 ys
        (mkPtr bb (Obj bb)) (mkPtr bb (Obj bb)) p5 (mkPtr (bb + sz) (Obj bb)) eb vb vreg md Ψ) as Hci.
      cbv zeta in Hci. rewrite !Z.add_0_r in Hci. replace (bb + Z.of_nat (length ys)) with a4 in Hci by lia.
      iApply (Hci with "Hvt Hl Hfl Hf2 Hfd Htot Hoff Hbl Hys Herr P0 P1 P2 P3 P4 P5 P6 P7 Hcol Hmd Hvtp P9 P11");
        try first [exact Hfr | close_side | exact Hmd | reflexivity].
      { unfold ys. apply Forall_take, Hxr. }
      iNext. iIntros (r fl' k tw' [Hpost Hk']) "Hl Hfl Hf2 Hfd Htot Hoff Herr H8 H16 H24 H32 H40 H48 Hbb Hbe _ Hmd
        Hvtp H80 H96".
      assert (Hkr : (if k =? 0 then (if r =? Z.of_nat (length ys) then 0 else 2 ^ 32 - 1) else k) = 0 \/
                    (if k =? 0 then (if r =? Z.of_nat (length ys) then 0 else 2 ^ 32 - 1) else k) = 2 ^ 32 - 1).
      { destruct Hk' as [-> | ->]; cbn; [destruct (r =? _)|]; auto. }
      iApply ("HK" $! _ fl' f2 with "[%] Hl [$Hfl $Hf2 $Hfd $Hoff $Hmd $Hvtp $H8 $H16 $H24 $H32 $H40 $H48 $Hbb $Hbe
        $H80 $H96] Herr"). split; [exact Hkr|].
      destruct Hpost as [[_ ->] | [_ ->]]; [reflexivity | apply LibioFclose.lor32_linked].
Qed.
End idle.

(** ## Fclose of an idle stream

    Hello holds stdout and stderr as idle streams, so it needs fclose in
    the form that takes [file_idle]. The rule below opens the idle
    stream, hands its lock and flags to [wp_fclose_with] and lets
    [wp_close_it_idle] close the buffer and the descriptor. *)

Section fclose_idle.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (Hreg : holds_os registry) (Hext : sys_external ge).
Context `{Hunl : !Defines ge "__GI__IO_un_link" glibc__IO_un_link}
  `{Hpush : !Defines ge "__GI___libc_cleanup_push_defer" glibc___libc_cleanup_push_defer}
  `{Hpop : !Defines ge "__GI___libc_cleanup_pop_restore" glibc___libc_cleanup_pop_restore}
  `{Hdf : !Defines ge "__GI__IO_default_finish" glibc__IO_default_finish}
  (Hff : ge_fn ge "_IO_new_file_finish" glibc__IO_new_file_finish)
  `{Hcif : !Defines ge "_IO_file_close_maybe_unlink" glibc__IO_file_close_maybe_unlink}
  `{Hwrite : !Defines ge "__GI___write" glibc___libc_write}
  (Hfw : ge_fn ge "_IO_new_file_write" glibc__IO_new_file_write)
  `{Hfree_fn : !Defines ge "free" free_fn}
  (Hfh : frees_heap (ge_free ge))
  (Hzf : find_fn ge zgc_free_name = None)
  (Hzg : lookup zgc_free_name (ge_globals ge) = None)
  `{Hcn : !Defines ge "__GI___close_nocancel" glibc___close_nocancel}
  (Hfc : ge_fn ge "__GI__IO_file_close" glibc__IO_file_close)
  `{Hsetb : !Defines ge "__GI__IO_setb" glibc__IO_setb}
  `{Hdwf : !Defines ge "_IO_new_do_write" glibc__IO_new_do_write}
  `{Hfum : !Defines ge "__GI__IO_unsave_markers" glibc__IO_unsave_markers}.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** A call `c: fclose (fp)` on idle stdout or stderr writes what its
    heap buffer holds, closes its descriptor and unlinks it. It returns
    0, or `c: EOF` when the write or the close failed, and gives back
    errno. The closed object keeps the fields that [closed_stdout]
    describes, so error reporting can still flush it. *)
Lemma wp_fclose_idle fr pre post fp fd pin pout fcp vb vreg sb sreg eb Φ :
  call_frame glibc__IO_new_fclose [WPtr fp] = Some fr ->
  lookup (TAtom "_IO_2_1_stdout_") (ge_globals ge) = Some pout ->
  (pout = fp \/ (ptr_addr pout <> ptr_addr fp /\ 0 <= ptr_addr pout < 2 ^ 64 /\
    lookup (TAtom "_IO_2_1_stderr_") (ge_globals ge) = Some fp)) ->
  lookup (TAtom "_IO_2_1_stdin_") (ge_globals ge) = Some pin -> ptr_addr pin <> ptr_addr fp ->
  0 <= ptr_addr pin < 2 ^ 64 ->
  lookup (TAtom "glibc_genops#flush_cleanup") (ge_globals ge) = Some fcp -> 0 <= ptr_addr fcp < 2 ^ 64 ->
  fd <> 0 -> In fd (ow_fds w0) -> ow_errno w0 = Some (mkPtr eb (Obj eb)) ->
  vtables_ro ge vb vreg -∗ single_ro ge sb sreg -∗ tcb_cleanup_inv (ow_self w0) -∗
  file_idle vb (ow_self w0) fp fd -∗ errno_any eb -∗
  io_list_inv ge (pre ++ fp :: post) -∗ ([∗ list] g ∈ pre ++ post, stream_life g) -∗
  ▷ (∀ k, ⌜k = 0 \/ k = 2 ^ 32 - 1⌝ -∗ tcb_cleanup_inv (ow_self w0) -∗
     io_list_inv ge (pre ++ post) -∗ ([∗ list] g ∈ pre ++ post, stream_life g) -∗
     (∃ fb freg lb lbreg, ⌜fp = mkPtr fb (Obj fb) /\ fb mod 8 = 0 /\ fb + file_size <= r_end freg /\ r_end freg <= 2 ^ 63⌝ ∗
      closed_stdout fb freg vb lb lbreg) -∗
     errno_any eb -∗ Φ (Ret (WInt k))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof using Type*.
  intros Hfr Hgout Hout Hgin Hin Hinr Hfcg Hfcr Hfd0 Hfd He.
  iIntros "#Hvt #Hs Htcb Hf Herr Hio Hlives HK".
  iDestruct "Hf" as (fb freg st nb Hp) "(Hl & Hf & Hlk & Hb & _)".
  destruct Hp as (-> & Hal & Hfb & Hend & Hfreg & Hok & Hidle & Hvtb & Hbok & Hshort).
  iDestruct "Hf" as "(%Hlen & Hfl & Hps & Hfdc & Hf2 & _ & %Hcl & Hcol & Hlp & Hoff & _ & _ & _ & _ &
    Hmd & Htot & Hvtp)".
  iDestruct "Hlk" as (lb lreg Hlb) "Hlk". rewrite Hlb.
  pose proof Hidle as Hidle'. unfold idle_ok in Hidle'.
  destruct Hidle' as (_ & _ & Hmd0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hlnk & _ & _ & _ & Hlk0).
  rewrite Hlb in Hlk0. cbn [ptr_addr] in Hlk0.
  pose proof Hok as (Hflr & _ & Hfilebuf & _ & Hul & _ & _).
  cbn [ptr_addr] in Hout, Hin.
  iApply (wp_fclose_with Hreg Hext Hff fr pre post fb freg (fs_flags st) (fs_mode st) lb lreg sb sreg fcp pin
    pout vb vreg
    (([∗ list] i ↦ p ∈ fs_ptrs st, pcell fb (off_ptr i) p) ∗ int_cell fb off_fileno (fs_fileno st) ∗
     int_cell fb off_flags2 (fs_flags2 st) ∗ bytes fb off_column (fs_column st) ∗
     icell fb off_offset (fs_offset st) ∗ int_cell fb off_mode (fs_mode st) ∗
     icell fb off_total_written (fs_total st) ∗ pcell fb off_vtable (fs_vtable st) ∗ buf_idle nb ∗
     errno_any eb)%I
    (errno_any eb) Φ
    with "Hvt Hs Htcb Hl Hfl Hlp Hlk Hio Hlives [$Hps $Hfdc $Hf2 $Hcol $Hoff $Hmd $Htot $Hvtp $Hb $Herr] [] [HK]");
    try first [exact Hfr | eassumption | lia].
  - iIntros (fr' Ψ Hfr') "Hl Hfl (Hps & Hfd & Hf2 & Hcol & Hoff & Hmd & Htot & Hvtp & Hb & Herr) HK".
    iApply (wp_close_it_idle Hreg Hext Hfw Hfh Hzf Hzg Hfc fr' fb freg st nb fd vb vreg eb Ψ
      with "Hvt Hl Hfl Hps Hfd Hf2 Hcol Hoff Hmd Htot Hvtp Hb Herr HK"); assumption.
  - iNext. iIntros (k Hk) "Htcb Hio Hlives Hc Herr".
    iApply ("HK" with "[%] Htcb Hio Hlives [Hc] Herr"); [exact Hk|].
    iExists fb, freg, lb, lreg. iSplit; [iPureIntro; split_and!; done | iExact "Hc"].
Qed.
End fclose_idle.
