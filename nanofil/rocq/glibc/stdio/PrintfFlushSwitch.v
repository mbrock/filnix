(** After the stream accepts staged output, printf needs a new place to
    write. A bulk write and a one-character overflow can both change the
    stream's buffer, so printf asks the stream for its current pointers
    after the call. It uses the stream's buffer only if there is room;
    otherwise it uses its own staging array. *)

From Glibc Require Import GlibcProgram GlibcSpec GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import Fix OsWorld FileInv LibioLogic CFrame CBlocks PrintfLayout PrintfOut PrintfSpec
  PrintfFileInit PrintfBufferFileCode PrintfBufferFileSrc PrintfBufferFileNames.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.
Open Scope string_scope.
Open Scope list_scope.
Open Scope Z_scope.

Module S := PrintfBufferFileSrc.fn___printf_buffer_flush_to_file.
Import PrintfBufferFileNames.fn___printf_buffer_flush_to_file.

Section selection.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context `{!Defines ge "__printf_buffer_to_file_switch" glibc___printf_buffer_to_file_switch}.

(** Both choices give the next append an empty window with room for at
    least one byte. A stream whose pointers are equal selects the staging
    array, as does a stream without a buffer. *)
Lemma flush_choice_room i :
  pw_base (fwin_choice i) = pw_ptr (fwin_choice i) /\ pw_ptr (fwin_choice i) < pw_end (fwin_choice i).
Proof using Type.
  unfold fwin_choice. destruct (fi_chars i) as [c|]; [destruct (Z.ltb_spec (fc_bo c) (fc_eo c))|];
    cbn [stage_win data_win pw_base pw_ptr pw_end]; unfold stage_off, stage_end; lia.
Qed.

(** The bulk write reaches one call site, and overflow reaches the other.
    Both sites pass just the buffer pointer they received at entry. *)
Definition select_cuts : list (string * cut_sig) := Eval vm_compute in cut_table S.temp_keys S.live_in.

Lemma select_cuts_read :
  cut_in select_cuts "L40" = [(‹buf›, ("buf", 0))] /\ cut_in select_cuts "L88" = [(‹buf›, ("buf", 0))].
Proof. split; reflexivity. Qed.

(** Each site returns the pointers that the switch wrote into the printf
    buffer. The caller can use those pointers to lend the next window. *)
Definition select_block (l : string) : bspec :=
  BSpec l None (cut_in select_cuts l) fwin_in (fun i => [("buf", WPtr (mkPtr (fi_buf i) (Obj (fi_buf i))))])
    (fs_pre switch_spec) (fs_post switch_spec).

Lemma flush_switch_block l : l = "L40" \/ l = "L88" ->
  ⊢ block_triple glibc___printf_buffer_flush_to_file (select_block l).
Proof using Type*.
  intros Hl. iModIntro. iIntros (i e from Φ) "_ %He H HK".
  assert (Hswitch : HasSpec registry (os_wi w0) ge (TAtom "__printf_buffer_to_file_switch") switch_spec)
    by apply switch_has_spec.
  destruct Hl as [-> | ->]; cbn [bs_sig bs_vals bs_pre bs_post bs_label select_block] in *; c_env_open He;
    block_enter; (call_callee with i giving "H"; [iExact "H"|]);
    iDestruct "Hpost" as "[-> Hpost]"; block_resume; steps;
    iApply wp_ret_void; iNext; iApply "HK"; iFrame "Hpost"; done.
Qed.

End selection.
