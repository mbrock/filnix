From Glibc Require Import GlibcProgram.
(** Fclose takes the stream lock before closing its descriptor and releases
    it before unlinking the stream. These rules follow the single-threaded
    path from a free lock and preserve the saved close result. The shared
    unlock proof supports either static output stream. *)

From Glibc Require Import GlibcTactics LibioTactics LibioFcloseAcquire.
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

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (Hreg : holds_os registry)
  (Hext : sys_external ge).
Context `{Hunl : !Defines ge "__GI__IO_un_link" glibc__IO_un_link}.
Context `{Hdf : !Defines ge "__GI__IO_default_finish" glibc__IO_default_finish}.
Context (Hff : ge_fn ge "_IO_new_file_finish" glibc__IO_new_file_finish).
Context (Hunl_spec : unlink_spec w0 registry ge)
  (Hunl_unlinked : unlink_unlinked_spec w0 registry ge).


(** Expressions use the caller's linked program and registry. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** The OS registry and external declarations supply the thread-cookie rule. *)
Ltac self_side := first [apply (reg_of registry Hreg); reflexivity | apply (ext_fn ge Hext); cbn; tauto
                        | apply (ext_data ge Hext); cbn; tauto].

(** Closing a stream begins by acquiring its lock. When the lock is free
    and the caller has not disabled locking, the single thread becomes its
    owner before execution reaches the descriptor-close branch. *)
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
Proof using Hext Hreg.
  apply (LibioFcloseAcquire.wp_fclose_start Hreg Hext).
Qed.

(** The unlock path releases this thread's stream lock before running the
    static-output tail. The saved descriptor result survives unlink and
    finish, including a failed close. The original stdout adapter needs no
    stderr lookup; stderr callers supply its distinct linked address. *)
Lemma wp_fclose_L101_static_output e p1 pre post fb freg fl lb lbreg sb sreg fcp vb vreg pin pout md Φ :
  let fp := mkPtr fb (Obj fb) in
  lookup (TAtom "v0") e = Some (WPtr fp) -> lookup (TAtom "chk0") e = Some (WPtr fp) ->
  lookup (TAtom "v107") e = Some (WInt p1) -> 0 <= p1 < 2 ^ 32 ->
  lookup (TAtom "_IO_2_1_stdout_") (ge_globals ge) = Some pout ->
  (pout = fp \/ (ptr_addr pout <> fb /\ 0 <= ptr_addr pout < 2 ^ 64 /\
    lookup (TAtom "_IO_2_1_stderr_") (ge_globals ge) = Some fp)) ->
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
  intros fp Hv0 Hc0 Hp1 Hp1r Hgout Hstatic Hgin Hin Hinr Hfc Hfcr Hfb Hfal Hfend Hfreg Hfl Hul Hlnk Hlb Hmd. subst fp.
  iIntros "#Hvt #Hs Htcb Hl Hfl Hlp Hlk Hio Hlives Hfd Hmode Hvtp Hbb H80 H96 HK".
  unfold file_size in Hfend.
  iPoseProof "Hs" as "(%Hs' & Hsl & Hsb)". destruct Hs' as (Hgs & Hsend).
  iDestruct "Hlk" as "(%Hk & Hbl' & [%Hb0r Hb0] & [%Hb4r Hb4] & Hbo)". destruct Hk as (Hkal & Hkend & Hkreg).
  iApply (wp_live_fit1 with "Hl"). iIntros ([Hf0 Hf48]) "Hl".
  iApply (wp_live_fit1 with "Hbl'"). iIntros ([Hl0 Hl48]) "Hbl'".
  iApply (wp_live_fit with "Hsl"). iIntros ([Hsb0 Hsb48]) "_".
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
  iApply (wp_fclose_L8_static_output Hff Hunl_spec Hunl_unlinked
            with "Hvt Hs Htcb Hl Hfl Hlp Hlk Hio Hlives Hfd Hmode Hvtp Hbb H80 H96 HK"); try close_side; try exact Hmd.
Qed.

(** Closing stdout returns without comparing its address with stderr.
    This rule therefore needs no stderr address and keeps the original
    stdout contract and saved return value. *)
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
Proof using Hdf Hff Hunl Hunl_spec Hunl_unlinked.
  intros fp Hv0 Hc0 Hp1 Hp1r Hgout Hgin Hin Hinr Hfc Hfcr Hfb Hfal Hfend Hfreg Hfl Hul Hlnk Hlb Hmd.
  apply (wp_fclose_L101_static_output e p1 pre post fb freg fl lb lbreg sb sreg fcp vb vreg pin fp md Φ);
    try assumption. left. reflexivity.
Qed.

End rules.
