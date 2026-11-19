(** The formatter searches for a percent sign twice. The first search
    stops at the start of the format. The second skips the newline
    after the conversion and stops at the terminating wide zero. Neither
    search reads beyond the five wide characters in the literal. *)

From Glibc Require Import Unit_stdioZ2dcommon_vfwprintfZ2dinternal_os Unit_wcsmbs_wcschrnul_os.
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic.
From Glibc Require Import CodePrelude Fix OsWorld FileInv LibioLogic
  LibioCloseSteps WPrintfDispatch WPrintfLength.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic LibioCloseSteps.
Open Scope Z_scope.

Definition wprintf_chr_fn := Unit_wcsmbs_wcschrnul_os.fn___wcschrnul.
Definition wprintf_scan_fn := Unit_stdioZ2dcommon_vfwprintfZ2dinternal_os.fn_glibc_vfwprintf_internal'23__find_specwc'2egnu_inline.
Definition wprintf_format := [37;108;115;10;0].
Local Abbreviation fmtp b o := (mkPtr (b+o) (Ro b)).

Section scan.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Abbreviation sexpr := (language.expr (nanofil_lang registry ge)).

(** The greeting needs a read-only share of all twenty bytes of its
    format, not merely the bytes before its first narrow zero. *)
Definition wprintf_fmt_ro b br : iProp Σ :=
  ⌜lookup (TAtom "hello#str.83") (ge_globals ge) = Some (mkPtr b (Ro b)) /\
    0 < b /\ b mod 8 = 0 /\ b + 20 <= r_end br /\ r_end br <= 2^63⌝ ∗
  liveq DfracDiscarded b br ∗ bytesq DfracDiscarded b 0 (stage_bytes wprintf_format).

Global Instance wprintf_fmt_persistent b br : Persistent (wprintf_fmt_ro b br).
Proof using Type. rewrite /wprintf_fmt_ro. apply _. Qed.

Local Lemma char_search fr b br (suffix : bool) Φ :
  call_frame wprintf_chr_fn [WPtr (fmtp b (if suffix then 12 else 0)); WInt 37] = Some fr ->
  wprintf_fmt_ro b br -∗ ▷ Φ (Ret (WPtr (fmtp b (if suffix then 16 else 0)))) -∗ WP (ERun fr : sexpr) {{ Φ }}.
Proof using Type.
  intros Hfr. injection Hfr as <-. iIntros "#(%H & Hl & Hfmt) HK". destruct H as (_ & Hb & Ha & He & Hr).
  Local Ltac borrow i c := iDestruct (wchar_at _ _ 0 wprintf_format i c ltac:(reflexivity) with "Hfmt") as "[#Hc _]".
  Local Ltac check_char := check_read_dq "Hl" by (cbn [ptr_addr]; unfold raw_address; unwrap2; lia); iNext; iIntros "#Hl'"; iClear "Hl'".
  Local Ltac read_char := load_bytes_dq "Hl Hc" decode (reflexivity) by (cbn [ptr_addr]; unfold raw_address; unwrap2; lia);
    iNext; iIntros "#Hl' #Hc'"; iClear "Hl' Hc'".
  destruct suffix; do 3 step.
  - borrow 3%nat 10. check_char. read_char. step. branch. step. read_char. step. branch. step. step. step. step.
    iClear "Hc". borrow 4%nat 0. check_char. read_char. step. branch. step. iApply wp_ret; [reflexivity|vx|]. iNext.
    norm. unwrap2. replace (b+12+4) with (b+16) by lia. iExact "HK".
  - borrow 0%nat 37. check_char. read_char. step. branch. step. read_char. step. branch. step.
    iApply wp_ret; [reflexivity|vx|]. iNext. iExact "HK".
Qed.

(** The inline search wrapper returns the scan pointer without changing
    it. The formatter uses the distance to this pointer to count the
    literal characters it must write. *)
Lemma wp_wprintf_scan fr b br (suffix : bool) Φ :
  find_fn ge (TAtom "__wcschrnul") = Some (Defined wprintf_chr_fn) ->
  call_frame wprintf_scan_fn [WPtr (fmtp b (if suffix then 12 else 0))] = Some fr ->
  wprintf_fmt_ro b br -∗ ▷ Φ (Ret (WPtr (fmtp b (if suffix then 16 else 0)))) -∗ WP (ERun fr : sexpr) {{ Φ }}.
Proof using Type.
  intros Hchr Hfr. injection Hfr as <-. iIntros "#Hfmt HK". step.
  iApply wp_call_bind; [vx|exact Hchr|reflexivity|]. iNext.
  iApply (char_search _ b br suffix with "Hfmt"); [reflexivity|]. iNext. resume. iApply wp_ret; [reflexivity|vx|]. by iNext.
Qed.
End scan.
