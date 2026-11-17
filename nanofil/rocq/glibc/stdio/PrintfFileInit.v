(** A formatter call that prints to a stream starts by setting up a
    file-backed buffer with `c: __printf_buffer_to_file_init`. The
    function stores the buffer's fields and calls
    `c: __printf_buffer_to_file_switch` to choose the window. This
    module proves that the compiled function meets [file_init_spec] of
    [PrintfSpec](PrintfSpec.v). It proves the same of the second
    function and [switch_spec]. *)

From Glibc Require Import GlibcProgram GlibcSpec GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import Fix OsBlocks OsWorld FileInv LibioLogic PrintfBufferFileCode PrintfBufferFileSrc
  PrintfBufferStage PrintfBufferDirect CFrame CStruct CBlocks PrintfLayout PrintfOut PrintfSpec.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.
Open Scope string_scope.
Open Scope list_scope.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

Module S := PrintfBufferFileSrc.fn___printf_buffer_to_file_init.

(** The table [init_cuts] gives, for each label, the temporaries that
    are live there and the C variable that each one holds. *)
Definition init_cuts : list (string * cut_sig) :=
  Eval vm_compute in cut_table glibc___printf_buffer_to_file_init S.temp_names S.live_in.

Section init.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context `{!Callees [(TAtom "__printf_buffer_to_file_switch", switch_spec)] }.

(** The function has one block, and the block's specification is the
    function's contract. *)
Definition init_blocks : list bspec :=
  [BSpec "start" (cut_in init_cuts "start") fwin_in
     (fun i => [("buf", WPtr (mkPtr (fi_buf i) (Obj (fi_buf i)))); ("fp", WPtr (mkPtr (fi_file i) (Obj (fi_file i))))])
     (fs_pre file_init_spec) (fs_post file_init_spec)].

Lemma init_table : ⊢ blocks_hold glibc___printf_buffer_to_file_init init_blocks.
Proof using Type*.
  apply blocks_close. iIntros "#IH". repeat iSplit; [|done]; iModIntro.
  iIntros (i e from Φ) "%He (Hs & Hbl & Hfp & Hb) HK". cbn [bs_sig bs_vals bs_label bs_post] in *. c_env_open He.
  cbn [fs_pre fs_post file_init_spec]. iDestruct "Hfp" as (ofp) "Hfp". iDestruct "Hb" as (ob op oe written mode) "Hb".
  struct_live_open "Hbl" as "[%Hbb Hl]". struct_open "Hfp" as "[Hfp _]".
  struct_open "Hb" as "(Hbase & Hptr & Hend & Hwr & [%Hm Hmode] & _)".
  block_enter. step. step. check "Hl". store "Hl" "Hbase". step. check "Hl". store "Hl" "Hptr".
  step. check "Hl". store "Hl" "Hend". step. check "Hl". store_long "Hl" "Hwr".
  step. check "Hl". store_int "Hl" "Hmode". step. check "Hl". store "Hl" "Hfp".
  call_callee with i giving "Hs Hl Hfp Hbase Hptr Hend".
  { iFrame "Hs". iSplitL "Hl"; [struct_live_close "Hl"|]. iSplitL "Hfp"; [struct_close|]. iExists _, _, _. struct_close. }
  iDestruct "Hpost" as "(-> & Hs & Hbl & Hfp & Hb)". block_resume. iApply wp_ret_void. iNext.
  iApply "HK". iSplit; [done|]. iFrame "Hs Hbl Hfp". struct_open "Hb" as "(Hbase & Hptr & Hend & _)".
  struct_close. iPureIntro. lia.
Qed.

(** A caller of `c: __printf_buffer_to_file_init` uses this lemma. It
    says that the compiled function meets the contract
    [file_init_spec] in any program that defines the function. *)
Lemma file_init_has_spec `{!Defines ge "__printf_buffer_to_file_init" glibc___printf_buffer_to_file_init} :
  HasSpec registry (os_wi w0) ge (TAtom "__printf_buffer_to_file_init") file_init_spec.
Proof using Type*.
  eapply (blocks_has_spec _ _ _ init_blocks); [exact defines | reflexivity | | exact init_table].
  intros i. eexists _, i. split; [reflexivity|]. split; [c_env_close|].
  cbn [bs_pre bs_post]. iIntros "$" (r) "$".
Qed.

End init.

(** ## The callee's contract from its older proofs *)

Section switch.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context `{Hswitch : !Defines ge "__printf_buffer_to_file_switch" glibc___printf_buffer_to_file_switch}.

(** The function `c: __printf_buffer_to_file_switch` chooses between
    the stream's buffer and the staging array, and an older lemma
    covers each case: [wp_printf_buffer_switch_direct] and
    [wp_printf_buffer_switch_staging]. This lemma joins the two into
    the contract [switch_spec]. The older lemmas take single cells, so
    the proof first splits the structures of the contract into their
    cells. *)
Lemma switch_has_spec : HasSpec registry (os_wi w0) ge (TAtom "__printf_buffer_to_file_switch") switch_spec.
Proof using Type*.
  intros i. exists glibc___printf_buffer_to_file_switch. split; [exact defines|]. split; [eexists; reflexivity|].
  intros fr Φ Hfr. cbn [fs_args fs_pre fs_post switch_spec] in *.
  iIntros "((%Hok & Hfl & Hd & Hfc) & Hbl & Hfp & Hb) HK". iDestruct "Hb" as (ob op oe) "Hb".
  struct_live_open "Hbl" as "[%Hbb Hl]". struct_live_open "Hfl" as "[%Hfb Hf]".
  struct_open "Hfp" as "[Hfp _]". struct_open "Hfc" as "(Hwp & Hwe & _)".
  struct_open "Hb" as "(Hbase & Hptr & Hend & _)".
  pose proof Hok as Hok'. unfold fwin_ok in Hok'. unfold fwin_choice.
  destruct (Z.ltb_spec (fi_bo i) (fi_eo i)).
  - iApply (wp_printf_buffer_switch_direct with "Hl Hf Hd Hfp Hwp Hwe Hbase Hptr Hend"); [exact Hfr | lia..|].
    iNext. iIntros "Hl Hf Hd Hfp Hwp Hwe Hbase Hptr Hend". iApply "HK". iSplit; [done|].
    iSplitL "Hf Hd Hwp Hwe"; [iSplit; [done|]; iSplitL "Hf"; [struct_live_close "Hf"|]; iFrame "Hd"; struct_close|].
    iSplitL "Hl"; [struct_live_close "Hl"|]. iSplitL "Hfp"; struct_close.
  - iApply (wp_printf_buffer_switch_staging with "Hl Hf Hd Hfp Hwp Hwe Hbase Hptr Hend"); [exact Hfr | lia..|].
    iNext. iIntros "Hl Hf Hd Hfp Hwp Hwe Hbase Hptr Hend". iApply "HK". iSplit; [done|].
    iSplitL "Hf Hd Hwp Hwe"; [iSplit; [done|]; iSplitL "Hf"; [struct_live_close "Hf"|]; iFrame "Hd"; struct_close|].
    iSplitL "Hl"; [struct_live_close "Hl"|]. iSplitL "Hfp"; struct_close.
Qed.

End switch.
