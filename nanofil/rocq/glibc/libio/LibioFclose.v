From Glibc Require Import GlibcProgram.
(** `c: _IO_new_fclose(stdout)` (LibioFcloseCode.v, libio/iofclose.c),
    as `c: close_stdout` calls it at exit in hi_atexit.c, on stdout
    holding n bytes `c: puts` left in its heap buffer: the single
    thread takes the free stream lock (LibioFcloseLock.v's
    [wp_fclose_start]); `c: _IO_file_close_maybe_unlink(fp, 0)`
    (LibioCloseIt.v's [wp_glibc__IO_file_close_maybe_unlink], whose
    triple is [close_it_spec]) writes the bytes and closes the
    descriptor; `c: _flags2 |= 32` runs; the lock is released and
    LibioFcloseTail.v's [wp_fclose_L8] unlinks the stream, runs its
    `c: __finish` and, stdout being static, does not free it
    (LibioFcloseLock.v's [wp_fclose_L101]); the whole is
    [wp_glibc__IO_new_fclose_stdout]. *)

From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry SysCode LibioUnlinkCode LibioCloseItCode
  LibioFcloseCode FileInv LibioLogic SysWrappers LibioCloseSteps LibioCloseItEnd LibioFinish LibioFcloseTail
  LibioFcloseLock.
From Glibc Require FileInv LibioCloseSteps LibioFcloseLock LibioFcloseTail LibioFinish LibioLogic OsWorld SysWrappers.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** [closed_flags] has `c: _IO_USER_LOCK` clear. *)
Lemma closed_user_lock x : Z.land (closed_flags x) 32768 = 0.
Proof.
  unfold closed_flags. rewrite Z.land_lor_distr_l. rewrite <- Z.land_assoc.
  change (Z.land 128 32768) with 0. change (Z.land 4222428172 32768) with 0.
  rewrite Z.land_0_r. reflexivity.
Qed.

(** [closed_flags] keeps `c: _IO_LINKED`. *)
Lemma closed_linked x : Z.land (closed_flags x) 128 = Z.land x 128.
Proof.
  unfold closed_flags. rewrite Z.land_lor_distr_l. rewrite <- Z.land_assoc.
  change (Z.land 128 128) with 128. change (Z.land 4222428172 128) with 0. apply Z.lor_0_r.
Qed.

(** `c: _IO_ERR_SEEN` leaves `c: _IO_LINKED` alone. *)
Lemma lor32_linked x : Z.land (Z.lor x io_err_seen) 128 = Z.land x 128.
Proof.
  unfold io_err_seen. rewrite Z.land_lor_distr_l. change (Z.land 32 128) with 0. apply Z.lor_0_r.
Qed.


Import LibioFcloseLock LibioFcloseTail LibioFinish SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic LibioCloseSteps.

Import ProgramAbbreviations.
Section rules_values.
Context {hlc : has_lc}
  {Σ : gFunctors}
  {invGS_gen0 : invGS_gen hlc Σ}
  {gen_heapGS0 : gen_heapGS piece pval Σ}
  (w0 : os_world)
  (registry : name -> option (contract os_world))
  (ge : genv).
Existing Instance invGS_gen0.
Existing Instance gen_heapGS0.
Local Instance fclose_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).
Definition close_it_spec : Prop :=
  forall fr fb freg fl f2 fd tw off bb breg i xs rp rb we be eb vb vreg md Φ,
  let n := Z.of_nat (length xs) in
  let wb := mkPtr (bb + i) (Obj bb) in
  let base := mkPtr bb (Obj bb) in
  call_frame glibc__IO_file_close_maybe_unlink [WPtr (mkPtr fb (Obj fb)); WInt 0] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  Z.land f2 2 = 0 -> Z.land f2 32 = 0 -> 0 <= f2 < 2 ^ 32 -> In fd (ow_fds w0) -> 0 <= fd < 2 ^ 31 ->
  0 <= fl < 2 ^ 32 -> Z.land fl io_is_appending = 0 -> Z.land fl io_no_writes = 0 ->
  Z.land fl io_currently_putting <> 0 -> Z.land fl io_user_buf = 0 ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> r_kind breg = Heap ->
  0 < bb -> 0 <= i -> bb + i + n <= r_end breg -> r_end breg <= 2 ^ 63 ->
  Forall (fun x => 0 <= x < 256) xs -> 0 <= ptr_addr be < 2 ^ 64 -> ptr_cap be = Obj bb ->
  md = 0 \/ md = 2 ^ 32 - 1 ->
  vtables_ro ge vb vreg -∗
  live fb freg -∗ int_cell fb off_flags fl -∗ int_cell fb off_flags2 f2 -∗ int_cell fb off_fileno fd -∗
  icell fb off_total_written tw -∗ icell fb off_offset off -∗ live bb breg -∗ bytes bb i xs -∗ errno_any eb -∗
  pcell fb off_read_ptr rp -∗ pcell fb 16 wb -∗ pcell fb 24 rb -∗ pcell fb off_write_base wb -∗
  pcell fb off_write_ptr (mkPtr (bb + i + n) (Obj bb)) -∗ pcell fb off_write_end we -∗
  pcell fb off_buf_base base -∗ pcell fb off_buf_end be -∗
  bytes fb off_column [0; 0] -∗ int_cell fb off_mode md -∗ pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗
  pcell fb 80 null -∗ pcell fb 96 null -∗
  ▷ (∀ r fl' k tw', ⌜fw_post n fl r fl' /\ (k = 0 \/ k = 2 ^ 32 - 1)⌝ -∗
     live fb freg -∗ int_cell fb off_flags (closed_flags fl') -∗ int_cell fb off_flags2 f2 -∗
     int_cell fb off_fileno (2 ^ 32 - 1) -∗ icell fb off_total_written tw' -∗ icell fb off_offset (2 ^ 64 - 1) -∗
     errno_any eb -∗
     pcell fb 8 null -∗ pcell fb 16 null -∗ pcell fb 24 null -∗ pcell fb 32 null -∗ pcell fb 40 null -∗
     pcell fb 48 null -∗ pcell fb off_buf_base null -∗ pcell fb off_buf_end null -∗
     bytes fb off_column [0; 0] -∗ int_cell fb off_mode md -∗ pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗
     pcell fb 80 null -∗ pcell fb 96 null -∗
     Φ (Ret (WInt (if k =? 0 then (if r =? n then 0 else 2 ^ 32 - 1) else k)))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
End rules_values.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (Hreg : holds_os registry)
  (Hext : sys_external ge).
Context `{Hunl : !Defines ge "__GI__IO_un_link" glibc__IO_un_link}.
Context `{Hdf : !Defines ge "__GI__IO_default_finish" glibc__IO_default_finish}.
Context (Hff : ge_fn ge "_IO_new_file_finish" glibc__IO_new_file_finish).
Context `{Hcif : !Defines ge "_IO_file_close_maybe_unlink" glibc__IO_file_close_maybe_unlink}.


(** Expressions of the language. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** `c: _IO_file_close_maybe_unlink`'s triple, as LibioCloseIt.v's
    [wp_glibc__IO_file_close_maybe_unlink] states it. *)

(** The callees' triples. *)
Context (Hci : (close_it_spec w0 registry ge))
  (Hunl_spec : unlink_spec w0 registry ge)
  (Hunl_unlinked : unlink_unlinked_spec w0 registry ge).

(** `c: fclose(stdout)` (`c: _IO_new_fclose`), stdout ge's
    `c: _IO_2_1_stdout_`, the stream fb of the list pre ++ fb :: post,
    open, un-oriented or narrow (`c: _mode` md 0 or -1, as `c: puts`
    leaves it), linked, its lock free, with n pending bytes, none or some,
    xs at offset i of its heap buffer bb: the bytes go to
    `c: _IO_new_do_write`, r of them written ([fw_post]); the
    descriptor is closed, k the result; the buffer is given up; the
    stream leaves the list and keeps its own links; `c: _flags` is
    [closed_flags] without `c: _IO_LINKED`, `c: _fileno` and
    `c: _offset` -1; stdout is not freed; the result is k if not 0,
    else `c: _IO_new_do_write`'s. *)
Lemma wp_glibc__IO_new_fclose_stdout fr pre post fb freg fl f2 fd tw off bb breg i xs rp rb we be eb vb vreg
    lb lbreg sb sreg fcp pin md Φ :
  let n := Z.of_nat (length xs) in
  let fp := mkPtr fb (Obj fb) in
  let wb := mkPtr (bb + i) (Obj bb) in
  let base := mkPtr bb (Obj bb) in
  call_frame glibc__IO_new_fclose [WPtr fp] = Some fr ->
  lookup (TAtom "_IO_2_1_stdout_") (ge_globals ge) = Some fp ->
  lookup (TAtom "_IO_2_1_stdin_") (ge_globals ge) = Some pin -> ptr_addr pin <> fb -> 0 <= ptr_addr pin < 2 ^ 64 ->
  lookup (TAtom "glibc_genops#flush_cleanup") (ge_globals ge) = Some fcp -> 0 <= ptr_addr fcp < 2 ^ 64 ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  Z.land f2 2 = 0 -> Z.land f2 32 = 0 -> 0 <= f2 < 2 ^ 32 -> In fd (ow_fds w0) -> 0 <= fd < 2 ^ 31 ->
  0 <= fl < 2 ^ 32 -> Z.land fl io_is_appending = 0 -> Z.land fl io_no_writes = 0 ->
  Z.land fl io_currently_putting <> 0 -> Z.land fl io_user_buf = 0 -> has fl io_user_lock = false ->
  has fl io_linked = true -> has fl io_is_filebuf = true ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> r_kind breg = Heap ->
  0 < bb -> 0 <= i -> bb + i + n <= r_end breg -> r_end breg <= 2 ^ 63 ->
  Forall (fun x => 0 <= x < 256) xs -> 0 <= ptr_addr be < 2 ^ 64 -> ptr_cap be = Obj bb -> 0 < lb ->
  md = 0 \/ md = 2 ^ 32 - 1 ->
  vtables_ro ge vb vreg -∗ single_ro ge sb sreg -∗ tcb_cleanup_inv (ow_self w0) -∗
  live fb freg -∗ int_cell fb off_flags fl -∗ int_cell fb off_flags2 f2 -∗ int_cell fb off_fileno fd -∗
  icell fb off_total_written tw -∗ icell fb off_offset off -∗ live bb breg -∗ bytes bb i xs -∗ errno_any eb -∗
  pcell fb off_read_ptr rp -∗ pcell fb 16 wb -∗ pcell fb 24 rb -∗ pcell fb off_write_base wb -∗
  pcell fb off_write_ptr (mkPtr (bb + i + n) (Obj bb)) -∗ pcell fb off_write_end we -∗
  pcell fb off_buf_base base -∗ pcell fb off_buf_end be -∗
  bytes fb off_column [0; 0] -∗ int_cell fb off_mode md -∗ pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗
  pcell fb 72 null -∗ pcell fb 80 null -∗ pcell fb 96 null -∗
  pcell fb off_lock (mkPtr lb (Obj lb)) -∗ lock_state lb lbreg 0 0 null -∗
  io_list_inv ge (pre ++ fp :: post) -∗ ([∗ list] g ∈ pre ++ post, stream_life g) -∗
  ▷ (∀ r fl' k tw', ⌜fw_post n fl r fl' /\ (k = 0 \/ k = 2 ^ 32 - 1)⌝ -∗
     tcb_cleanup_inv (ow_self w0) -∗
     live fb freg -∗ int_cell fb off_flags (Z.land (closed_flags fl') 4294967167) -∗
     (∃ f2', int_cell fb off_flags2 f2') -∗ int_cell fb off_fileno (2 ^ 32 - 1) -∗
     icell fb off_total_written tw' -∗ icell fb off_offset (2 ^ 64 - 1) -∗ errno_any eb -∗
     pcell fb 8 null -∗ pcell fb 16 null -∗ pcell fb 24 null -∗ pcell fb 32 null -∗ pcell fb 40 null -∗
     pcell fb 48 null -∗ pcell fb off_buf_base null -∗ pcell fb off_buf_end null -∗
     bytes fb off_column [0; 0] -∗ int_cell fb off_mode md -∗ pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗
     pcell fb 72 null -∗ pcell fb 80 null -∗ pcell fb 96 null -∗
     pcell fb off_lock (mkPtr lb (Obj lb)) -∗ lock_state lb lbreg 0 0 null -∗
     io_list_inv ge (pre ++ post) -∗ ([∗ list] g ∈ pre ++ post, stream_life g) -∗
     (∃ c p, pcell fb off_chain c ∗ pcell fb off_prevchain p) -∗
     Φ (Ret (WInt (if k =? 0 then (if r =? n then 0 else 2 ^ 32 - 1) else k)))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros n fp wb base Hfr Hgout Hgin Hin Hinr Hfc Hfcr Hfb Hfal Hfend Hfreg Hf22 Hf232 Hf2r Hfd Hfdr Hfl Happ
    Hnw Hcp Hub Hul Hlnk Hfb8 He Hbk Hb Hi Hbend Hbreg Hy Hbe Hbec Hlb Hmd. subst fp wb base.
  iIntros "#Hvt #Hs Htcb Hl Hfl Hfl2 Hfd Htw Hoff Hbl Hxs Herr Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend Hcol Hmode Hvtp
    H72 H80 H96 Hlp Hlk Hio Hlives HK".
  unfold file_size in Hfend.
  pose proof Hfb8 as Hfb8'. unfold has, io_is_filebuf in Hfb8'. apply negb_true_iff, Z.eqb_neq in Hfb8'.
  assert (0 <= Z.land fl 8192 < 2 ^ 32) by (apply land_lt32; lia).
  (* start: the stream's lock is taken. *)
  iApply (wp_fclose_start Hreg Hext _ _ _ _ _ _ _ _ _ Hfr with "Hs Htcb Hl Hfl Hlp Hlk"); try close_side.
  iIntros (e from [Hv0 Hc0]) "Htcb Hl Hfl Hlp Hlk".
  iApply (wp_live_fit1 with "Hl"). iIntros ([Hf0 Hf48]) "Hl".
  (* L13, L99: `c: _IO_file_close_it`, then `c: _flags2 |= 32`. *)
  iDestruct "Hfl" as "[_ Hfl]".
  step. check "Hl". load_s32 "Hl" "Hfl". step. branch_as false. step.
  iAssert (int_cell fb off_flags fl) with "[Hfl]" as "Hfl"; [iSplit; [done | iExact "Hfl"]|].
  iApply wp_call_bind; [vx | exact Hcif | reflexivity |]. iNext.
  iApply (Hci with "Hvt Hl Hfl Hfl2 Hfd Htw Hoff Hbl Hxs Herr Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend Hcol Hmode Hvtp
            H80 H96"); try close_side; try exact Hmd.
  iNext. iIntros (r fl' k tw' [Hpost Hk]) "Hl Hfl Hfl2 Hfd Htw Hoff Herr H8 H16 H24 H32 H40 H48 Hbb Hbe Hcol
    Hmode Hvtp H80 H96". resume.
  iDestruct "Hfl2" as "[%Hf2r' Hfl2]".
  step. check "Hl". load_s32 "Hl" "Hfl2". step. step. step. load_s32 "Hl" "Hfl2". step. step. step. check "Hl". store_int "Hl" "Hfl2". step.
  iAssert (∃ f2', int_cell fb off_flags2 f2')%I with "[Hfl2]" as "Hfl2".
  { iExists _. iSplit; [iPureIntro | iExact "Hfl2"].
    first [apply Z.mod_pos_bound; lia | apply lor_lt32; apply Z.mod_pos_bound; lia]. }
  (* L101 on: the unlock, then L8. *)
  iDestruct "Hfl" as "[%Hclr Hfl]".
  iAssert (int_cell fb off_flags (closed_flags fl')) with "[Hfl]" as "Hfl"; [iSplit; [done | iExact "Hfl"]|].
  assert (Hcl : has (closed_flags fl') io_linked = true).
  { revert Hlnk. unfold has, io_linked. rewrite closed_linked.
    destruct Hpost as [[_ ->] | [_ ->]]; [|rewrite lor32_linked]; tauto. }
  assert (Hcu2 : has (closed_flags fl') io_user_lock = false).
  { unfold has, io_user_lock. rewrite closed_user_lock. reflexivity. }
  cbn [edge_label]. iApply (wp_fclose_L101 Hff Hunl_spec Hunl_unlinked
               with "Hvt Hs Htcb Hl Hfl Hlp Hlk Hio Hlives Hfd Hmode Hvtp Hbb H80 H96 [-]"); try close_side; try exact Hmd.
  iNext. iIntros "Htcb Hl Hfl Hlp Hlk Hio Hlives Hlinks Hfd Hmode Hvtp Hbb H80 H96".
  iSpecialize ("HK" $! r fl' k tw' with "[%]"); [exact (conj Hpost Hk)|].
  assert (Hpr : 0 <= (if k =? 0 then (if r =? n then 0 else 2 ^ 32 - 1) else k) < 2 ^ 32).
  { destruct (k =? 0); [destruct (r =? n) | ]; lia. }
  rewrite (Z.mod_small _ (2 ^ 32) Hpr).
  iApply ("HK" with "Htcb Hl Hfl Hfl2 Hfd Htw Hoff Herr H8 H16 H24 H32 H40 H48 Hbb Hbe Hcol Hmode Hvtp H72 H80 H96
           Hlp Hlk Hio Hlives Hlinks").
Qed.

End rules.
