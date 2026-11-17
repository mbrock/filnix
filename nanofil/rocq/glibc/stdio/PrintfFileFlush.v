(** Flushing a printf staging array either marks failure or selects another
    buffer. The count advances by the staged length in both cases, including
    unsigned wraparound. A count mismatch does not reset the staging pointers.

    A write may fail or change the stream's buffer. The caller must prove
    the stream write separately. This proof covers the buffer selection
    that follows it. *)
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import OsWorld OsRegistry FileInv LibioLogic LibioCloseSteps
  PrintfStreamHeap PrintfBufferFileCode PrintfBufferXsputnStaging
  PrintfBufferXsputnHeapBorrow PrintfBufferXsputnCall LibioXsputnCode PrintfFileSelect Fix.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L LibioLogic LibioCloseSteps.
Open Scope Z_scope.
Section flush.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (B : Z -> Z -> iProp Σ) (vb : Z) (self : ptr)
  (mode flags2 : Z) (held : option Z) (E : iProp Σ).
Let F fp := printf_heap_stream_with B w0 vb self fp mode flags2 held.
Context `{Hswitch : !Defines ge "__printf_buffer_to_file_switch" glibc___printf_buffer_to_file_switch}.
Context (Hfn : ge_fn ge "_IO_new_file_xsputn" glibc__IO_new_file_xsputn).
Context (Hcall : printf_xsputn_call_spec w0 registry ge F E).
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** Both outcomes retain the original staging bytes and updated count.
    Success returns equal base and current pointers; failure keeps both old
    pointers and needs no permission for a newly selected allocation. *)
Lemma wp_printf_file_flush fr bb br fb vr xs written :
  let n := Z.of_nat (length xs) in
  call_frame glibc___printf_buffer_flush_to_file [WPtr (mkPtr bb (Obj bb))] = Some fr ->
  0 < bb -> bb mod 8 = 0 -> bb+176 <= r_end br -> r_end br <= 2^63 ->
  0 < fb -> fb mod 8 = 0 -> n <= 128 -> Forall (fun x => 0 <= x < 256) xs ->
  0 <= written < 2^64 ->
  vtables_ro ge vb vr -∗ live bb br -∗
  pcell bb 0 (mkPtr (bb+48) (Obj bb)) -∗
  pcell bb 8 (mkPtr (bb+48+n) (Obj bb)) -∗
  pcell bb 16 (mkPtr (bb+176) (Obj bb)) -∗ icell bb 24 written -∗
  pcell bb 40 (mkPtr fb (Obj fb)) -∗ bytes bb 48 xs -∗ int_cell bb 32 4 -∗
  F (mkPtr fb (Obj fb)) -∗ E -∗
  WP (ERun fr : sexpr) {{ v, ⌜v = RetVoid⌝ ∗ live bb br ∗
    icell bb 24 ((written+n) mod 2^64) ∗ pcell bb 40 (mkPtr fb (Obj fb)) ∗
    bytes bb 48 xs ∗ E ∗
    ((int_cell bb 32 0 ∗ pcell bb 0 (mkPtr (bb+48) (Obj bb)) ∗
      pcell bb 8 (mkPtr (bb+48+n) (Obj bb)) ∗
      pcell bb 16 (mkPtr (bb+176) (Obj bb)) ∗ F (mkPtr fb (Obj fb))) ∨
     (∃ start stop, int_cell bb 32 4 ∗ pcell bb 0 start ∗ pcell bb 8 start ∗
      pcell bb 16 stop ∗ printf_selected bb start (F (mkPtr fb (Obj fb))))) }}.
Proof using Type*.
  cbn zeta. intros Hfr Hb Ha He Hr Hfb Hfa Hlen Hxs Hw.
  iIntros "#Hvt Hb Hbase Hcur Hend Hw Hfp Hxs Hmode HF HE".
  iApply (wp_printf_xsputn_staging F E Hfn Hcall fr bb br fb vb vr xs 4 written
    with "Hvt Hb Hbase Hcur Hend Hw Hfp Hxs Hmode HF HE [] []"); try assumption.
  - iIntros "HF". iApply (printf_heap_vtable_borrow B with "HF").
  - iIntros "Hb Hbase Hcur Hend Hw Hfp Hxs Hmode HF HE".
    iSplit; [done|]. iFrame "Hb Hw Hfp Hxs HE". iLeft. iFrame.
  - iIntros (e Hv) "Hb Hbase Hcur Hend Hw Hfp Hxs Hmode HF HE".
    iApply (wp_printf_file_select B e (Some (TAtom "iw_1.join")) bb br vb self
      (mkPtr fb (Obj fb)) mode flags2 held with "Hb Hfp HF Hbase Hcur Hend"); try assumption.
    iNext. iIntros (start stop) "Hb Hfp Hbase Hcur Hend Hselected".
    iSplit; [done|]. iFrame "Hb Hw Hfp Hxs HE". iRight. iExists start, stop. iFrame.
Qed.
End flush.
