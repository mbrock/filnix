(** An empty in-object short buffer has equal write pointers.
    The actual pending-byte query loads both pointers with the stream's
    own lifetime and subtracts their addresses at L width. It needs no
    separate buffer object or ownership of the short byte. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import Unit_libio___fpending_os.
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics FileInv LibioLogic
  LibioPutsInv LibioCloseSteps.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic LibioCloseSteps.
Open Scope Z_scope.

Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** The query returns zero in either narrow mode and preserves all fields
    it reads. Self-pointer loads reuse the single stream lifetime. *)
Lemma wp_glibc___fpending_short_empty fr fb freg md Φ :
  let buf := mkPtr (fb + off_shortbuf) (Obj fb) in
  call_frame Unit_libio___fpending_os.fn___fpending [WPtr (mkPtr fb (Obj fb))] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  md = 0 \/ md = 2 ^ 32 - 1 ->
  live fb freg -∗ int_cell fb off_mode md -∗ pcell fb off_write_ptr buf -∗ pcell fb off_write_base buf -∗
  ▷ (live fb freg -∗ int_cell fb off_mode md -∗ pcell fb off_write_ptr buf -∗
     pcell fb off_write_base buf -∗ Φ (Ret (WInt 0))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof using Type.
  intros buf Hfr Hfb Hal Hend Hfreg Hmd. injection Hfr as <-. subst buf.
  iIntros "Hl [%Hm Hmode] Hwp Hwb HK". unfold file_size in Hend.
  iApply (wp_live_fit1 with "Hl"). iIntros ([Hf0 Hf48]) "Hl".
  step. step. norm. check "Hl". load_s32_group "Hl Hmode". step.
  destruct Hmd as [-> | ->]; closed_ints. 1: branch. 2: branch.
  all: step; step; norm; check "Hl";
    load_self_using (wp_raw_load_pointer_self) "Hl Hwp"; step; norm; check "Hl";
    load_self_using (wp_raw_load_pointer_self) "Hl Hwb"; step; step; step;
    (iApply wp_ret; [reflexivity | reflexivity |]); iNext;
    rewrite Z.sub_diag; cbn;
    iApply ("HK" with "Hl [Hmode] Hwp Hwb"); (iSplit; [iPureIntro; lia | iExact "Hmode"]).
Qed.
End rules.
