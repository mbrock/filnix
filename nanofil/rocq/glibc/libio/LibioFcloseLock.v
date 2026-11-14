(** The stream lock in `c: _IO_new_fclose(fp)` (LibioFcloseCode.v,
    libio/iofclose.c) for stdout: `c: _IO_acquire_lock(fp)`, the
    single thread taking the free lock, (0, 0, null) becoming
    (1, 0, self) ([wp_fclose_start]), and block `c: L101`,
    `c: _IO_funlockfile(fp)`, releasing it again, then
    LibioFcloseTail.v's [wp_fclose_L8] ([wp_fclose_L101]). *)

From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsThread OsRegistry SysCode LibioUnlinkCode LibioFcloseCode FileInv LibioLogic
  SysWrappers LibioCloseSteps LibioFinish LibioFcloseTail.
From Glibc Require FileInv LibioCloseSteps LibioFcloseTail LibioFinish LibioLogic OsThread OsWorld SysWrappers.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.


Import LibioFcloseTail LibioFinish SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic LibioCloseSteps.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
Context (Hreg : holds_os registry) (Hext : sys_external ge).
Context (Hunl : find_fn ge (TAtom "__GI__IO_un_link") = Some (Defined glibc__IO_un_link)).
Context (Hdf : find_fn ge (TAtom "__GI__IO_default_finish") = Some (Defined glibc__IO_default_finish)).
Context (Hff : ge_fn ge "_IO_new_file_finish" glibc__IO_new_file_finish).
Context (Hunl_spec : unlink_spec w0 registry ge) (Hunl_unlinked : unlink_unlinked_spec w0 registry ge).

(** The Iris instance for registry and [os_wi] w0. *)
Local Instance fclose_lock_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.

(** Expressions of the language. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** A branch whose condition H's left side decides. *)


(** The premises of `c: zthread_self_cookie`'s rule. *)
Ltac self_side := first [apply (reg_of registry Hreg); reflexivity | apply (ext_fn ge Hext); cbn; tauto
                        | apply (ext_data ge Hext); cbn; tauto].

(** `c: _IO_new_fclose(fp)`'s start for an open stream fb whose
    `c: _IO_USER_LOCK` is clear and whose lock lb is free: the single
    thread takes the lock, and block `c: L13` runs, with fp in
    `c: v0` and `c: chk0`. *)
Lemma wp_fclose_start fr fb freg fl lb lbreg sb sreg Φ :
  let fp := mkPtr fb (Obj fb) in
  call_frame glibc__IO_new_fclose [WPtr fp] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  0 <= fl < 2 ^ 32 -> has fl io_user_lock = false ->
  single_ro ge sb sreg -∗ tcb_cleanup_inv (ow_self w0) -∗
  live fb freg -∗ int_cell fb off_flags fl -∗ pcell fb off_lock (mkPtr lb (Obj lb)) -∗
  lock_state lb lbreg 0 0 null -∗
  (∀ e from, ⌜lookup (TAtom "v0") e = Some (WPtr fp) /\ lookup (TAtom "chk0") e = Some (WPtr fp)⌝ -∗
     tcb_cleanup_inv (ow_self w0) -∗ live fb freg -∗ int_cell fb off_flags fl -∗
     pcell fb off_lock (mkPtr lb (Obj lb)) -∗ lock_state lb lbreg 1 0 (ow_self w0) -∗
     WP (ERun (mkFrame glibc__IO_new_fclose e [] None (Enter (TAtom "L13") (Some from))) : sexpr) {{ Φ }}) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros fp Hfr. injection Hfr as <-. intros Hfb Hfal Hfend Hfreg Hfl Hul. subst fp.
  iIntros "#Hs Htcb Hl Hfl Hlp Hlk HK".
  unfold file_size in Hfend.
  pose proof Hul as Hul'. unfold has, io_user_lock in Hul'. apply negb_false_iff, Z.eqb_eq in Hul'.
  assert (0 <= Z.land fl 32768 < 2 ^ 32) by (rewrite Hul'; lia).
  iPoseProof "Hs" as "(%Hs' & Hsl & Hsb)". destruct Hs' as (Hgs & Hsend).
  iDestruct "Htcb" as (tb treg jb Ht) "Htcb". pose proof Ht as (Hself & Htb & _).
  iAssert (tcb_cleanup_inv (ow_self w0)) with "[Htcb]" as "Htcb".
  { iExists tb, treg, jb. iSplit; [iPureIntro; exact Ht | iExact "Htcb"]. }
  assert (Hsz : ptr_addr (ow_self w0) <> 0) by (rewrite Hself; cbn; lia).
  iDestruct "Hlk" as "(%Hk & Hbl' & [%Hb0r Hb0] & [%Hb4r Hb4] & Hbo)". destruct Hk as (Hkal & Hkend & Hkreg).
  iApply (wp_live_fit1 w0 registry ge with "Hl"). iIntros ([Hf0 Hf48]) "Hl".
  iApply (wp_live_fit1 w0 registry ge with "Hbl'"). iIntros ([Hl0 Hl48]) "Hbl'".
  iApply (wp_live_fit w0 registry ge with "Hsl"). iIntros ([Hsb0 Hsb48]) "_".
  iDestruct "Hfl" as "[%Hflr Hfl]".
  (* start, L18 to L23: the lock is free and the process single-threaded. *)
  step. check "Hl". load_s32 "Hl" "Hfl". step. step. branch_as false.
  step. iApply (OsThread.wp_zthread_self_cookie w0 registry ge); try self_side; [exact Hsz|]. iNext.
  step. check_persistent "Hsl". load_byte_persistent "Hsl Hsb". step. branch.
  step. step. check "Hl". load "Hl" "Hlp" "Hbl'". step. check "Hbl'". load_null "Hbl'" "Hbo". step. step. step. step. step. branch.
  step. step. check "Hl". load "Hl" "Hlp" "Hbl'". check "Hbl'". store_int "Hbl'" "Hb0". load "Hl" "Hlp" "Hbl'". step.
  check "Hbl'". store "Hbl'" "Hbo". step.
  iAssert (lock_state lb lbreg 1 0 (ow_self w0)) with "[Hbl' Hb0 Hb4 Hbo]" as "Hlk".
  { iSplit; [iPureIntro; lia|]. iFrame "Hbl'". iSplitL "Hb0"; [iSplit; [done | iExact "Hb0"]|].
    iSplitL "Hb4"; [iSplit; [done | iExact "Hb4"]|]. iExact "Hbo". }
  iAssert (int_cell fb off_flags fl) with "[Hfl]" as "Hfl"; [iSplit; [done | iExact "Hfl"]|].
  cbn [edge_label]. iApply ("HK" with "[%] Htcb Hl Hfl Hlp Hlk"). split; lk_prove.
Qed.

(** Block `c: L101` of `c: _IO_new_fclose(fp)` for stdout, entered
    from `c: L99` with the close's result p1 in `c: v107`: the stream
    lock lb, held by this thread, is released, and block `c: L8` runs
    as [wp_fclose_L8] says, the stream un-oriented or narrow
    (`c: _mode` md 0 or -1). *)
Lemma wp_fclose_L101 e p1 pre post fb freg fl lb lbreg sb sreg fcp vb vreg pin md Φ :
  let fp := mkPtr fb (Obj fb) in
  lookup (TAtom "v0") e = Some (WPtr fp) -> lookup (TAtom "chk0") e = Some (WPtr fp) ->
  lookup (TAtom "v107") e = Some (WInt p1) -> 0 <= p1 < 2 ^ 32 ->
  lookup (TAtom "_IO_2_1_stdout_") (ge_globals ge) = Some fp ->
  lookup (TAtom "_IO_2_1_stdin_") (ge_globals ge) = Some pin -> ptr_addr pin <> fb ->
  0 <= ptr_addr pin < 2 ^ 64 ->
  lookup (TAtom "glibc_genops#flush_cleanup") (ge_globals ge) = Some fcp -> 0 <= ptr_addr fcp < 2 ^ 64 ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  0 <= fl < 2 ^ 32 -> has fl io_user_lock = false -> has fl io_linked = true -> 0 < lb ->
  md = 0 \/ md = 2 ^ 32 - 1 ->
  vtables_ro ge vb vreg -∗ single_ro ge sb sreg -∗ tcb_cleanup_inv (ow_self w0) -∗
  live fb freg -∗ int_cell fb off_flags fl -∗ pcell fb off_lock (mkPtr lb (Obj lb)) -∗
  lock_state lb lbreg 1 0 (ow_self w0) -∗
  io_list_inv ge (pre ++ fp :: post) -∗ ([∗ list] g ∈ pre ++ post, stream_life g) -∗
  int_cell fb off_fileno (2 ^ 32 - 1) -∗ int_cell fb off_mode md -∗ pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗
  pcell fb off_buf_base null -∗ pcell fb 80 null -∗ pcell fb 96 null -∗
  ▷ (tcb_cleanup_inv (ow_self w0) -∗ live fb freg -∗ int_cell fb off_flags (Z.land fl 4294967167) -∗
     pcell fb off_lock (mkPtr lb (Obj lb)) -∗ lock_state lb lbreg 0 0 null -∗
     io_list_inv ge (pre ++ post) -∗ ([∗ list] g ∈ pre ++ post, stream_life g) -∗
     (∃ c p, pcell fb off_chain c ∗ pcell fb off_prevchain p) -∗
     int_cell fb off_fileno (2 ^ 32 - 1) -∗ int_cell fb off_mode md -∗
     pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗
     pcell fb off_buf_base null -∗ pcell fb 80 null -∗ pcell fb 96 null -∗ Φ (Ret (WInt p1))) -∗
  WP (ERun (mkFrame glibc__IO_new_fclose e [] None (Enter (TAtom "L101") (Some (TAtom "L99")))) : sexpr)
    {{ Φ }}.
Proof.
  intros fp Hv0 Hc0 Hp1 Hp1r Hgout Hgin Hin Hinr Hfc Hfcr Hfb Hfal Hfend Hfreg Hfl Hul Hlnk Hlb Hmd. subst fp.
  iIntros "#Hvt #Hs Htcb Hl Hfl Hlp Hlk Hio Hlives Hfd Hmode Hvtp Hbb H80 H96 HK".
  unfold file_size in Hfend.
  iPoseProof "Hs" as "(%Hs' & Hsl & Hsb)". destruct Hs' as (Hgs & Hsend).
  iDestruct "Hlk" as "(%Hk & Hbl' & [%Hb0r Hb0] & [%Hb4r Hb4] & Hbo)". destruct Hk as (Hkal & Hkend & Hkreg).
  iApply (wp_live_fit1 w0 registry ge with "Hl"). iIntros ([Hf0 Hf48]) "Hl".
  iApply (wp_live_fit1 w0 registry ge with "Hbl'"). iIntros ([Hl0 Hl48]) "Hbl'".
  iApply (wp_live_fit w0 registry ge with "Hsl"). iIntros ([Hsb0 Hsb48]) "_".
  pose proof Hul as Hcu. unfold has, io_user_lock in Hcu. apply negb_false_iff, Z.eqb_eq in Hcu.
  assert (Hcu' : Z.land (fl mod 2 ^ 32) (32768 mod 2 ^ 32) mod 2 ^ 32 = 0).
  { rewrite (Z.mod_small fl); [|lia]. change (32768 mod 2 ^ 32) with 32768. rewrite Hcu. reflexivity. }
  iDestruct "Hfl" as "[_ Hfl]".
  (* The user lock is clear, and the process single-threaded. *)
  step. check "Hl". load_s32 "Hl" "Hfl". step. step. branch_rewrite Hcu'.
  step. load_s32 "Hl" "Hfl". step. step. branch_rewrite Hcu'.
  step. step. check_persistent "Hsl". load_byte_persistent "Hsl Hsb". step. branch.
  (* The count is 0: the owner becomes null, then the lock word 0. *)
  step. step. check "Hl". load "Hl" "Hlp" "Hbl'". step. check "Hbl'". load_s32 "Hbl'" "Hb4". step. step. step. branch.
  step. step. check "Hl". load "Hl" "Hlp" "Hbl'". step. check "Hbl'". store "Hbl'" "Hbo".
  check "Hl". load "Hl" "Hlp" "Hbl'". check "Hbl'". store_int "Hbl'" "Hb0". step.
  iAssert (lock_state lb lbreg 0 0 null) with "[Hbl' Hb0 Hb4 Hbo]" as "Hlk".
  { iSplit; [iPureIntro; lia|]. iFrame "Hbl'". iSplitL "Hb0"; [iSplit; [done | iExact "Hb0"]|].
    iSplitL "Hb4"; [iSplit; [done | iExact "Hb4"]|]. iExact "Hbo". }
  iAssert (int_cell fb off_flags fl) with "[Hfl]" as "Hfl"; [iSplit; [done | iExact "Hfl"]|].
  rewrite (Z.mod_small p1 (2 ^ 32)); [|lia].
  iApply (wp_fclose_L8 w0 registry ge Hunl Hdf Hff Hunl_spec Hunl_unlinked
            with "Hvt Hs Htcb Hl Hfl Hlp Hlk Hio Hlives Hfd Hmode Hvtp Hbb H80 H96 HK"); try close_side; try exact Hmd.
Qed.

End rules.
