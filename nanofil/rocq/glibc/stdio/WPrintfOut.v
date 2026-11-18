(** The format parser neither inspects the stream nor counts the characters
    already staged. It lends both to the buffer operations. Each call gives
    back a valid buffer, even when the stream accepted only a prefix. *)

From Glibc Require Import HelloImageTypedWP.
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic.
From Glibc Require Import CodePrelude Fix OsWorld OsRegistry FileInv LibioLogic
  LibioCloseSteps LibioPutsInv LibioWIdle MemFwdCode PrintfOut WPrintfFileFlush WPrintfDispatch
  WPrintfFill WPrintfPad WPrintfCopy WPrintfWrite.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic LibioCloseSteps OsWorld.
Open Scope Z_scope.

Definition wprintf_failed_fn := hello_image_fn_glibc_vfwprintf_internal'23__wprintf_buffer_has_failed.

Section out.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Abbreviation sexpr := (language.expr (nanofil_lang registry ge)).
Local Abbreviation obj b := (mkPtr b (Obj b)).
Context (vb : Z) (self : ptr) (E : iProp Σ).

(** The stream and its staging array have one owner throughout the
    conversion. A write may change the cursor, count and failure flag. *)
Definition wprintf_out bb br fp : iProp Σ :=
  (∃ vreg, vtables_ro ge vb vreg ∗ wvtables_ro ge vb) ∗ file_wide ge vb self fp 1 ∗ E ∗
  ∃ cs written active, wide_stage bb br fp cs written active.

(** The writer uses these definitions from the linked image and one
    stream rule for the wide xsputn slot. The stream rule returns the
    same private resources on a short write as on a complete write. *)
Class WideBufferCalls : Prop := {
  wbc_move : registry (TAtom "zmemmove") = Some (void_only (memmove_contract os_world));
  wbc_move_fn : find_fn ge (TAtom "zmemmove") = None;
  wbc_move_sym : lookup (TAtom "zmemmove") (ge_globals ge) = None;
  wbc_memcpy : Defines ge "__GI_memcpy" glibc_memcpy;
  wbc_copy : Defines ge "__wmemcpy" wprintf_copy_fn;
  wbc_fill : Defines ge "__GI___wmemset" wprintf_fill_fn;
  wbc_pad : Defines ge "__wprintf_buffer_pad_1" wprintf_pad_fn;
  wbc_flush : Defines ge "__wprintf_buffer_flush" wprintf_dispatch_fn;
  wbc_backend : Defines ge "__wprintf_buffer_flush_to_file" wprintf_file_flush_fn;
  wbc_xs_fn : ge_fn ge "__GI__IO_wfile_xsputn" wprintf_xsputn_fn;
  wbc_xs : wprintf_xsputn_call_spec vb self E
}.
Context `{!WideBufferCalls}.

(** The source loan is independent of the stream. It covers a slice
    of the read-only format or a slice of the mutable greeting. *)
Lemma wp_wprintf_out_write fr bb br fp dq sb sr so sc ys Φ :
  call_frame wprintf_write_fn [WPtr (obj bb); WPtr (mkPtr (sb+so) sc); WInt (Z.of_nat (length ys))] = Some fr ->
  0 < sb -> sb mod 8 = 0 -> 0 <= so -> sb+so+4*Z.of_nat (length ys) <= r_end sr -> r_end sr <= 2^63 ->
  sc = Obj sb \/ sc = Ro sb -> Forall (fun c => 0 <= c < 2^32) ys ->
  wprintf_out bb br fp -∗ liveq dq sb sr -∗ bytesq dq sb so (stage_bytes ys) -∗
  ▷ (wprintf_out bb br fp -∗ liveq dq sb sr -∗ bytesq dq sb so (stage_bytes ys) -∗ Φ RetVoid) -∗ WP (ERun fr : sexpr) {{ Φ }}.
Proof using Type*.
  intros. iIntros "((%vr & #Hvt & #Hwv) & HF & HE & %cs & %w & %ok & Hs) Hl Hb HK".
  iApply (wp_wprintf_write wbc_move wbc_move_fn wbc_move_sym wbc_memcpy wbc_copy vb self E
    wbc_xs_fn wbc_xs wbc_backend wbc_flush with "Hvt Hwv HF HE Hs Hl Hb"); try eassumption.
  iNext. iIntros (cs' w' ok') "HF HE Hs Hl Hb". iApply ("HK" with "[-Hl Hb] Hl Hb").
  iSplitR; [iExists vr; iFrame "#"|iFrame].
Qed.

(** Padding may use the whole stage many times. The parser only needs
    to know that it can still write or finish afterwards. *)
Lemma wp_wprintf_out_pad fr bb br fp n Φ :
  call_frame wprintf_pad_inline_fn [WPtr (obj bb); WInt 32; WInt n] = Some fr -> 0 <= n < 2^64 ->
  wprintf_out bb br fp -∗ ▷ (wprintf_out bb br fp -∗ Φ RetVoid) -∗ WP (ERun fr : sexpr) {{ Φ }}.
Proof using Type*.
  intros. iIntros "((%vr & #Hvt & #Hwv) & HF & HE & %cs & %w & %ok & Hs) HK".
  iApply (wp_wprintf_pad_spaces wbc_fill vb self E wbc_xs_fn wbc_xs wbc_backend wbc_flush with "Hvt Hwv HF HE Hs");
    [exact wbc_pad|eassumption|assumption|]. iNext. iIntros (cs' w' ok') "HF HE Hs". iApply "HK".
  iSplitR; [iExists vr; iFrame "#"|iFrame].
Qed.

(** The failure test reads only the buffer mode. It does not retry a
    failed flush or change any stream fields. *)
Lemma wp_wprintf_out_failed fr bb br fp Φ :
  call_frame wprintf_failed_fn [WPtr (obj bb)] = Some fr ->
  wprintf_out bb br fp -∗ ▷ (∀ failed : bool, wprintf_out bb br fp -∗ Φ (Ret (WInt (if failed then 1 else 0)))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof using Type.
  intros Hfr. injection Hfr as <-. iIntros "(Hvt & HF & HE & %cs & %w & %ok & %tail & %slots & %Hst & Hl & Hbase & Hcur & Hstop & Hw & Hm & Hfp & Hbs & Ha) HK".
  pose proof Hst as (Hbb & Hal & Hend & Hreg & _). step. step. check "Hl". load_mode "Hl" "Hm". step.
  iApply wp_ret; [reflexivity|vx|]. iNext. destruct ok; [iApply ("HK" $! false); iFrame "Hvt HF HE"; iExists cs, w, true|
    iApply ("HK" $! true); iFrame "Hvt HF HE"; iExists cs, w, false]; iExists tail, slots; by iFrame.
Qed.
End out.
