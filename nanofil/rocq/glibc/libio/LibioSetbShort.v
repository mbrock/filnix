(** A stream's short buffer belongs to the stream object itself.
    When USER_BUF is set, replacing that buffer must not free the
    object. This rule follows that branch with one stream lifetime;
    the short byte and its shadow capabilities remain with the caller. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import Unit_libio_genops_os.
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics FileInv LibioLogic
  LibioSetb LibioPutsInv LibioCloseSteps.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic LibioCloseSteps.
Open Scope Z_scope.

Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** Replacing the in-object buffer changes only the two buffer pointers
    and the flags. It needs no heap-buffer ownership or free rule. *)
Lemma wp_glibc__IO_setb_short fr fb freg fl oe nb ne a Φ :
  call_frame Unit_libio_genops_os.fn___GI__IO_setb [WPtr (mkPtr fb (Obj fb)); WPtr nb; WPtr ne; WInt a] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  0 <= a < 2 ^ 32 -> Z.land fl io_user_buf <> 0 ->
  live fb freg -∗ int_cell fb off_flags fl -∗
  pcell fb off_buf_base (mkPtr (fb + off_shortbuf) (Obj fb)) -∗ pcell fb off_buf_end oe -∗
  ▷ (live fb freg -∗ int_cell fb off_flags (setb_flags fl a) -∗ pcell fb off_buf_base nb -∗
     pcell fb off_buf_end ne -∗ Φ RetVoid) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof using Type.
  intros Hfr Hfb Hal Hend Hfreg Ha Huser. injection Hfr as <-.
  iIntros "Hl [%Hf Hfl] Hb He HK". unfold file_size in Hend.
  iApply (wp_live_fit1 with "Hl"). iIntros ([Hf0 Hf48]) "Hl".
  step. step. norm. check "Hl".
  load_self_using (wp_raw_load_pointer_self) "Hl Hb".
  step. step. branch_as false. step. check "Hl". load_s32_group "Hl Hfl". step. step. step.
  unfold io_user_buf in Huser.
  assert (Hmask : 0 <= Z.land fl 1 < 2 ^ 32) by (apply land_lt32; lia).
  step. branch_as true.
  iApply (wp_setb_tail with "Hl [$Hfl //] Hb He HK"); try libio_side.
Qed.
End rules.
