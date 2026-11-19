(** The formatter finds its first conversion by calling the captured
    strchrnul helper with percent as the stopping byte. The scan preserves
    the supplied string ownership and leaves other resources in the [[frame]].

    The word-at-a-time search needs ownership of the padded words that it
    reads. Owning only the format bytes through NUL does not supply that
    padding. This rule scans a format; it does not interpret its directives. *)
From Glibc Require Import Unit_stdioZ2dcommon_vfprintfZ2dinternal_os Unit_string_strchrnul_os.
From Glibc Require Import GlibcProgram GlibcTactics OsTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import FormatterCode StrchrnulLogic WordString Fix.
Import ListNotations ProgramAbbreviations StrchrnulLogic.L StrchrnulLogic.LG WordString.
Open Scope Z_scope.

(** The complete captured module supplies the local scanning helper. *)
Definition glibc_find_specmb : func := Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn_glibc_vfprintf_internal'23__find_specmb'2egnu_inline.
(** Lookup finds the actual definition rather than the selector's fallback. *)
Lemma glibc_find_specmb_found :
  find_direct (TAtom "glibc_vfprintf_internal#__find_specmb.gnu_inline") formatter_module =
    Some (Defined glibc_find_specmb).
Proof. vm_compute. reflexivity. Qed.

Section scan.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** The real strchrnul call returns the first percent sign or terminating
    NUL, preserving the same string share and pointer capability. *)
Lemma wp_find_specmb dq p s Φ :
  find_fn ge (TAtom "__GI___strchrnul") = Some (Defined Unit_string_strchrnul_os.fn___GI___strchrnul) ->
  word_string dq p s -∗
  (word_string dq p s -∗ Φ (Ret (WPtr (ptr_add p (Z.of_nat (chr_idx 37 s)))))) -∗
  WP (ERun (mkFrame glibc_find_specmb [(TAtom "v0", WPtr p)] [] None
    (Enter (TAtom "start") None)) : gexpr) {{ Φ }}.
Proof using Type.
  intros Hg. iIntros "Hs HK". step.
  iApply (wp_call_glibc_strchrnul registry (OsWorld.os_wi w0) ge
    _ _ _ _ _ _ _ _ _ dq p s 37 with "Hs");
    [reflexivity | change (0 <= 37 < 4294967296); lia | exact Hg | reflexivity |].
  iNext. iIntros "Hs". cbn [fr_fn fr_env fr_locals fr_doomed fr_at].
  iApply wp_ret; [reflexivity | reflexivity |].
  iNext. iApply ("HK" with "Hs").
Qed.
End scan.
