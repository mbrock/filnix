(** Glibc dispatches a printf buffer flush according to the buffer's mode.
    A file-backed buffer has mode 4 until output fails. The dispatcher
    returns zero for a failed buffer without calling the stream again.
    On success it checks that the file backend left room for another byte.

    This module separates the dispatcher's proof from the file backend's
    contract. The function that finishes a file-backed print calls the
    backend directly and can use the same contract. *)

From Glibc Require Import Unit_stdioZ2dcommon_printf_buffer_flush_os.
From Glibc Require Import GlibcProgram GlibcSpec GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic MemLogic.
From Glibc Require Import Fix OsBlocks OsWorld FileInv LibioLogic CFrame CStruct CBlocks
  PrintfLayout PrintfOut PrintfSpec PrintfBufferIoSrc PrintfBufferIoNames.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.
Open Scope string_scope.
Open Scope list_scope.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

Module S := PrintfBufferIoSrc.fn___printf_buffer_flush.
Import PrintfBufferIoNames.fn___printf_buffer_flush.

Section dispatch.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (R : Z -> region -> Z * region * Z * Z -> iProp Σ).

(** Both callers of `c: __printf_buffer_flush_to_file` first check that the
    buffer has not failed. They may flush a partially filled window. The
    backend counts the pending bytes and either marks failure or leaves an
    empty window with room for the next byte. *)
Definition flush_to_file_spec : fspec Σ :=
  FSpec Z (fun bb => [WPtr (mkPtr bb (Obj bb))])
    (fun bb => ∃ br w written, printf_buf bb br w written 4 ∗ R bb br (pw_place w))%I
    (fun bb o => ∃ br w written mode,
       ⌜o = RetVoid /\ 0 <= written < 2 ^ 64 /\
        (mode = mode_failed \/ (mode = 4 /\ pw_base w = pw_ptr w /\ pw_ptr w < pw_end w))⌝ ∗
       printf_buf bb br w written mode ∗ R bb br (pw_place w))%I.

Context `{!HasSpec registry (os_wi w0) ge (TAtom "__printf_buffer_flush_to_file") flush_to_file_spec}.

(** The call to the file backend starts at a separate label in the mode
    switch. Both the parameter and the address of its mode field survive
    the switch, because the dispatcher reads the mode again after the call. *)
Definition flush_cuts : list (string * cut_sig) :=
  Eval vm_compute in cut_table S.temp_keys S.live_in.

Lemma file_call_cut : cut_in flush_cuts "iw_2.L12" = [(‹chk(buf+32)›, ("buf", 32)); (‹buf›, ("buf", 0))].
Proof using Type. reflexivity. Qed.

Definition flush_blocks : list bspec :=
  [BSpec "start" None (cut_in flush_cuts "start") Z (fun bb => [("buf", WPtr (mkPtr bb (Obj bb)))])
     (fs_pre (flush_spec 4 R)) (fs_post (flush_spec 4 R));
   BSpec "iw_2.L12" None (cut_in flush_cuts "iw_2.L12") Z (fun bb => [("buf", WPtr (mkPtr bb (Obj bb)))])
     (fs_pre flush_to_file_spec) (fs_post (flush_spec 4 R))].

(** After a successful flush, the next append needs somewhere to write its
    first byte. The dispatcher checks that the write pointer differs from
    the end before it returns one to the caller. *)
Lemma flush_table : ⊢ blocks_hold Unit_stdioZ2dcommon_printf_buffer_flush_os.fn___printf_buffer_flush flush_blocks.
Proof using Type*.
  apply blocks_close. iIntros "#IH". repeat iSplit; [| |done]; iModIntro;
    iIntros (bb e from Φ) "_ %He H HK"; cbn [bs_sig bs_vals bs_label bs_post] in *; c_env_open He.
  - iDestruct "H" as (br w written mode) "(%Hmd & Hbuf & HR)". buf_open "Hbuf".
    block_enter. step. check "Hl". load_mode "Hl" "Hmode". step. destruct Hmd as [-> | ->]; branch.
    + step. iApply wp_ret; [reflexivity | vx |]. iNext. iApply "HK".
      iExists 0, br, w, written, mode_failed. iFrame "HR". iSplit; [iPureIntro; intuition lia|]. buf_close. exact Hw.
    + clear Hmode_range. step. step. load_mode "Hl" "Hmode". step. branch.
      step. step. branch. step. step. branch. step. step. branch.
      goto_block "IH" "HK" 1%nat with bb. iExists br, w, written. iFrame "HR". buf_close. exact Hw.
  - block_enter. call_callee with bb giving "H"; first iExact "H".
    iDestruct "Hpost" as (br w written mode) "((-> & _ & %Hmd) & Hbuf & HR)". block_resume. buf_open "Hbuf".
    step. step. step. check "Hl". load_mode "Hl" "Hmode". step. destruct Hmd as [-> | (-> & _ & Hroom)]; branch.
    + step. iApply wp_ret; [reflexivity | vx |]. iNext. iApply "HK".
      iExists 0, br, w, written, mode_failed. iFrame "HR". iSplit; [iPureIntro; intuition lia|]. buf_close. exact Hw.
    + step. step. check "Hl". load_window "Hl" "Hptr" "Hwl". step. load_window "Hl" "Hend" "Hwl".
      step. step. step. unfold pwin_ok in Hw. branch_as false. step. iApply wp_ret; [reflexivity | vx |]. iNext. iApply "HK".
      iExists 1, br, w, written, 4. iFrame "HR". iSplit; [iPureIntro; intuition lia|]. buf_close. exact Hw.
Qed.

(** A caller of `c: __printf_buffer_write` can discharge the dispatcher's
    contract with the single backend that a file-backed buffer uses. *)
Lemma flush_dispatch_has_spec `{!Defines ge "__printf_buffer_flush" Unit_stdioZ2dcommon_printf_buffer_flush_os.fn___printf_buffer_flush} :
  HasSpec registry (os_wi w0) ge (TAtom "__printf_buffer_flush") (flush_spec 4 R).
Proof using Type*.
  eapply (blocks_has_spec _ _ _ flush_blocks); [exact defines | reflexivity | reflexivity | | exact flush_table].
  intros bb. eexists _, bb. split; [reflexivity|]. split; [c_env_close|]. cbn [bs_pre bs_post]. iIntros "$" (r) "$".
Qed.

End dispatch.
