(** Hello prints its greeting by calling wprintf with a format and a
    string of wide characters. Glibc reads the string up to its first
    zero. When wprintf returns, the greeting and the bytes after that
    zero are unchanged. *)

From Glibc Require Import PrintfTables Unit_libio_wprintf_os GlibcProgram GlibcSpec GlibcTactics
  OsTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic VariadicLogic.
From Glibc Require Import CodePrelude Fix OsBlocks OsWorld FileInv FileIdle FileTidy
  LibioLogic LibioCloseSteps LibioWIdle LibioPutsInv PrintfSpec PrintfWrap WPrintfDispatch WPrintfParse
  WPrintfScan WPrintfFileFlush WPrintfOut WPrintfInternal HelloGlibcDebts HelloConvString
  HelloImageModule HelloImageLoad OsRegistry.
Import ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0 Fix.LG0.L FileInv LibioLogic LibioCloseSteps OsWorld WrapVL.
Open Scope Z_scope.
Local Abbreviation obj b := (mkPtr b (Obj b)).
Local Abbreviation ro b := (mkPtr b (Ro b)).

Definition wprintf_fn := Unit_libio_wprintf_os.fn___wprintf.

Section wrap.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.

(** The conversion and the formatter describe the same four bytes per
    character. The conversion uses one nonzero byte and three zero bytes;
    the formatter reads those bytes as a little-endian word. *)
Local Lemma wide_text_prefix ws : wide_text ws -> ∃ xs,
  Forall (fun c => 0 < c < 256) xs /\ (4*length xs+4 <= length ws)%nat /\
  take (4*length xs+4) ws = stage_bytes (xs++[0]).
Proof using Type.
  intros (xs & Hx & Hlen & P). exists xs. split; [done|]. split; [done|].
  rewrite P /stage_bytes flat_map_app. clear P Hlen. induction Hx; [reflexivity|].
  cbn [flat_map]. rewrite conv_le_byte; [simpl; by rewrite -IHHx|lia].
Qed.

Context (vb : Z) (self : ptr) (E W : iProp Σ) `{!WideFormatCode, !WideBufferCalls vb self E}.
Context (Hidle : wprintf_fwide_idle_spec vb self W) (Hwide : wprintf_fwide_wide_spec vb self W).
Context `{!Defines ge "wprintf" wprintf_fn, !Defines ge "__vfwprintf_internal" wprintf_internal_fn}.

(** The greeting may be longer than INT_MAX characters. The caller
    only needs to know where it allocated the greeting and how much
    room it has. If stdout has already written narrow characters,
    it refuses the wide print and stays narrow. *)
Lemma wprintf_has_spec bd n ws fp dq fmt rr vr eb :
  wide_text ws -> 0 < bd -> bd mod 16 = 0 -> bd + req_extent (wreq n) <= 2^48 ->
  ow_errno w0 = Some (obj eb) -> lookup (TAtom "__libc_errno") (ge_globals ge) = Some (obj eb) ->
  (E ⊢ errno_any eb ∗ (errno_any eb -∗ E)) -> (E ⊢ W ∗ (W -∗ E)) ->
  GlibcSpec.fn_triple registry (os_wi w0) ge (TAtom "wprintf") [WPtr (sym_ptr ge "hello#str.83"); WPtr (obj bd)]
    (wprintf_fmt_ro fmt rr ∗ wprintf_tables_ro ∗ printf_ro ∗ vtables_ro ge vb vr ∗ wvtables_ro ge vb ∗
     stdout_is dq fp ∗ file_idle vb self fp 1 ∗ E ∗ wbuf bd n ws)%I
    (ret_int (stdout_is dq fp ∗ (file_idle vb self fp 1 ∨ file_wide ge vb self fp 1) ∗ E ∗ wbuf bd n ws))%I.
Proof using Type*.
  intros Hws Hb Ha He Herr Hge Hlend Hconv. destruct (wide_text_prefix _ Hws) as (xs & V & L & P).
  exists wprintf_fn. split; [apply defines|]. split; [eexists; reflexivity|]. intros fr Φ Hfr.
  iIntros "(#Hfmt & #Ht & #Hro & #Hvt & #Hwv & Ho & HF & HE & Hbuf) HK".
  iPoseProof "Hfmt" as "((%Hg & _) & _)". unfold sym_ptr in Hfr. rewrite Hg in Hfr. injection Hfr as <-.
  iDestruct "Ho" as (so sr (Hgso & Hso8 & Hse)) "[Hsol Hsoc]". iApply (wp_live_fit with "Hsol"). iIntros ([Hso0 Hso48]) "Hsol".
  iApply WrapVL.wp_snapshot; [discriminate|reflexivity|intros ? ? ? ? Hf Hw; exact (FxprintfStream.os_wi_snapshot _ _ _ _ _ _ _ Hf Hw)|].
  iNext. iIntros (sb Hsnap) "Hsnap". step.
  iApply wp_alloc; [vm_compute; reflexivity|vm_compute; congruence|vm_compute; congruence|
    intros ? ? ? ? Hf Hw; exact (os_wi_alloc w0 _ _ _ _ _ Hf Hw)|].
  iNext. iIntros (cb Hc) "Hobj". change (0 < cb /\ cb mod 16 = 0 /\ cb+32 <= 2^48) in Hc.
  destruct Hc as (Hcb & Hc16 & Hce). assert (Hc8 : cb mod 8 = 0) by (Z.div_mod_to_equations; lia).
  iDestruct (obj_zero_block with "Hobj") as "(Hcl & Hx & Ha)"; [compute; discriminate|].
  iAssert (live cb (mkRegion cb (cb+32) Heap Live)) with "Hcl" as "Hcl".
  iDestruct (zero_cell_prefix cb 0 24 with "Hx Ha") as "(Hcc & _ & _)".
  iApply WrapVL.wp_va_args; [reflexivity|]. iNext. check "Hcl". store "Hcl" "Hcc".
  iDestruct (va_at_intro cb sb 8 [WPtr (ro fmt); WPtr (obj bd)] with "Hcl Hcc Hsnap") as "Hva";
    [split_and!; assumption|exact Hsnap|lia|cbn; lia|].
  step_global Hgso. check_read_dq "Hsol" by a2. iNext. iIntros "Hsol".
  iDestruct (file_idle_tidy with "HF") as (f2 Hbits) "HF".
  iDestruct (file_tidy_live with "HF") as (fb freg [-> Hfb]) "[Hfl Hclose]".
  iApply (wp_raw_load_pointer_dq with "Hsol Hsoc Hfl"); [reflexivity|vx|left; reflexivity|a2|a2|cbn; lia|].
  iNext. iIntros "Hsol Hsoc Hfl". iDestruct ("Hclose" with "Hfl") as "HF".
  iAssert (file_idle vb self (obj fb) 1) with "[HF]" as "HF"; [iApply file_idle_tidy; iExists f2; by iFrame|].
  iDestruct "Hbuf" as (caps [Lws Lcap]) "(Hl & Hbytes & Ha)".
  iDestruct (bytes_take_drop _ _ _ _ L with "Hbytes") as "[Hb Htail]". iEval (rewrite P) in "Hb".
  assert (Hb8 : bd mod 8 = 0) by (Z.div_mod_to_equations; lia).
  iApply wp_call_bind; [vx|apply defines|reflexivity|]. iNext.
  iApply (wp_wprintf_internal vb self E W Hidle Hwide with "Hfmt Ht Hro Hvt Hwv Hva HF HE Hl Hb");
    [reflexivity|exact Herr|exact Hge|exact Hlend|exact Hconv|assumption|assumption|cbn [r_end]; lia|cbn [r_end]; lia|exact V|].
  iNext. iIntros (v Hv) "HF HE Hl Hb". resume. iApply wp_ret; [reflexivity|vx|]. iNext. iApply "HK".
  iExists v. iSplit; [iPureIntro; rewrite !Z.mod_mod; try lia; rewrite (Z.mod_small v (2^32) Hv); done|].
  iFrame "HF HE". iSplitL "Hsol Hsoc"; [iExists so, sr; iFrame; done|].
  iExists caps. iFrame "Hl Ha". iSplit; [done|]. iApply (bytes_take_drop _ _ _ _ L). rewrite P. iFrame.
Qed.
End wrap.

Section image.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w : os_world) (fr : word -> mem -> option (res unit * mem)).
Local Abbreviation hge := (mkGenv hello_image_module img_globals fr).
#[local] Instance wrap_program : GlibcProgram Σ := program_of w glibc_os_registry hge.
Local Abbreviation vb := (img_a "__io_vtables").
Local Abbreviation eb := (img_a "errno").
Local Abbreviation fmt := (img_a "hello#str.83").

(** This proof checks that each call runs the function by that name in
    Hello's executable. It leaves two operations to the stream proofs:
    setting the stream's orientation and writing an array of characters. *)
Lemma hello_wprintf_has_spec (E W : iProp Σ) bd n ws fp dq rr vr :
  wprintf_fwide_idle_spec vb (ow_self w) W -> wprintf_fwide_wide_spec vb (ow_self w) W ->
  wprintf_xsputn_call_spec vb (ow_self w) E ->
  wide_text ws -> 0 < bd -> bd mod 16 = 0 -> bd + req_extent (wreq n) <= 2^48 ->
  ow_errno w = Some (obj eb) -> (E ⊢ errno_any eb ∗ (errno_any eb -∗ E)) -> (E ⊢ W ∗ (W -∗ E)) ->
  HelloGlibcDebts.fn_triple w hge (TAtom "wprintf") [WPtr (sym_ptr hge "hello#str.83"); WPtr (obj bd)]
    (wprintf_fmt_ro fmt rr ∗ wprintf_tables_ro ∗ printf_ro ∗ vtables_ro hge vb vr ∗ wvtables_ro hge vb ∗
     stdout_is dq fp ∗ file_idle vb (ow_self w) fp 1 ∗ E ∗ wbuf bd n ws)%I
    (ret_int (stdout_is dq fp ∗ (file_idle vb (ow_self w) fp 1 ∨ file_wide hge vb (ow_self w) fp 1) ∗ E ∗ wbuf bd n ws))%I.
Proof using Type*.
  intros Hi Hw Hxs V Hb Ha He Herr Hlend Hconv.
  assert (Hcode : WideFormatCode) by (constructor; vm_compute; reflexivity).
  assert (Hcalls : WideBufferCalls vb (ow_self w) E).
  { constructor; [reflexivity|vm_compute; reflexivity..| |exact Hxs].
    exists (img_a "__GI__IO_wfile_xsputn"). split; [vm_compute; reflexivity|].
    split; [vm_compute; reflexivity|lia]. }
  eapply (@wprintf_has_spec _ _ wrap_program vb (ow_self w) E W Hcode Hcalls Hi Hw);
    first [exact Herr|exact Hlend|assumption|vm_compute; reflexivity].
Qed.
End image.
