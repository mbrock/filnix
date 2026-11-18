(** To format an unknown error number, snprintf calls the same narrow
    formatter as fprintf. This time the buffer flush writes to memory.
    Neither the formatter nor its callees need an open stream. *)

From Glibc Require Import GlibcProgram GlibcSpec.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import weakestpre.
From Stdlib Require Import String ZArith List.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics ExternalCalls Pieces Heap.
From Glibc Require Import Fix OsWorld OsRegistry FileInv LibioLogic PrintfSpec
  StrlenWord PrintfStagingCopy PrintfCopy PrintfWrite PrintfSmall PrintfPutcSlow PrintfPutc
  PrintfFill PrintfPad ItoaWord CBlocks PrintfLoopState PrintfLoop
  HelloImageModule HelloImageLoad HelloCloseReportFlush.
Import ListNotations ProgramAbbreviations.
Open Scope Z_scope.

Section format.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ} (w : os_world).
Local Abbreviation hge := (mkGenv hello_image_module img_globals R.free).
#[local] Instance fmt_program : GlibcProgram Σ := program_of w glibc_os_registry hge.

Local Ltac linked := unfold Defines; vm_compute; reflexivity.

(** The formatter's character, padding and byte writers all flush to the
    same discard array once the caller's array fills. The other callees
    scan the format, measure strings and turn the integer into digits. *)
Lemma report_format_has_spec db dr eb :
  HasSpec registry (os_wi w) hge (TAtom "__printf_buffer") (printf_buffer_spec 2 (snprintf_R db dr eb)).
Proof using Type.
  set (B := snprintf_R db dr eb).
  assert (Hflush : HasSpec registry (os_wi w) hge (TAtom "__printf_buffer_flush") (flush_spec 2 B)).
  { apply (report_flush_has_spec (glibc_program := fmt_program)); linked. }
  assert (Hfill : HasSpec registry (os_wi w) hge (TAtom "__GI_memset") win_fill_spec).
  { apply (memset_window_has_spec (glibc_program := fmt_program)); [reflexivity|linked..]. }
  assert (Hw : Callees [(TAtom "__printf_buffer_flush", flush_spec 2 B); (TAtom "__GI_memcpy", win_copy_spec)]).
  { constructor; [exact Hflush|]. constructor; [|constructor].
    apply (win_copy_of_window (glibc_program := fmt_program)), (memcpy_window_spec_valid (glibc_program := fmt_program));
      [reflexivity|linked..]. }
  assert (Hc : Callees [(TAtom "__printf_buffer_putc_1", putc_spec 2 B)]).
  { constructor; [apply putc_one_has_spec; first [assumption|linked]|constructor]. }
  apply (printf_buffer_has_spec (glibc_program := fmt_program)); last linked.
  unfold Callees. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
  - apply write_has_spec; first [assumption|linked].
  - apply has_failed_has_spec; linked.
  - apply (@find_spec_has_spec _ _ fmt_program); linked.
  - apply (@strlen_has_spec _ _ _ _ _ _ _ (os_wi_stable w)); linked.
  - apply (@pad_has_spec _ _ fmt_program 2 B Hflush Hfill); linked.
  - apply putc_has_spec; first [assumption|linked].
  - apply write_bytes_has_spec; first [assumption|linked].
  - apply itoa_word_has_spec; linked.
Qed.
End format.
