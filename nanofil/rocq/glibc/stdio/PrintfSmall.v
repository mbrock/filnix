(** When glibc formats text, it walks the format string and appends
    what it finds to a buffer. This walk calls two small helper
    functions. The function `c: __printf_buffer_has_failed` reads one
    field of the buffer and says whether an earlier append failed. The
    function `c: __find_specmb` looks for the next percent sign of the
    format, where the next conversion starts.

    This module proves that the two compiled helpers are safe to call.
    It proves the contracts [has_failed_spec] and [find_spec_spec] of
    [PrintfSpec](PrintfSpec.v), which are the statements that a caller
    of the helpers needs. Each helper is only a few instructions long,
    so its proof goes through the instructions in order. *)

From Glibc Require Import GlibcProgram GlibcSpec GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import Fix OsBlocks OsWorld FileInv LibioLogic WordString StrchrCode StrchrnulLogic
  FormatterCode FormatterScan FormatterLiteral CStruct PrintfLayout PrintfOut PrintfSpec.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.
Open Scope string_scope.
Open Scope list_scope.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

Section small.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** A caller of `c: __printf_buffer_has_failed` uses this lemma. The
    lemma says that the compiled function is safe on a usable buffer
    and gives the buffer back. The function answers 1 when the buffer
    has failed and 0 otherwise. *)
Lemma has_failed_has_spec (k : Z) (R : Z -> region -> Z * region * Z * Z -> iProp Σ)
    `{!Defines ge "glibc_vfprintf_internal#__printf_buffer_has_failed" glibc_format_failed} :
  HasSpec registry (os_wi w0) ge (TAtom "glibc_vfprintf_internal#__printf_buffer_has_failed") (has_failed_spec k R).
Proof using Type.
  intros bb. exists glibc_format_failed. split; [exact defines|]. split; [eexists; reflexivity|].
  intros fr Φ Hfr. injection Hfr as <-. cbn [fs_pre fs_post has_failed_spec].
  iIntros "Hout HK". iDestruct "Hout" as (breg w written mode) "(%Hmd & Hbuf & HR)". buf_open "Hbuf".
  step. step. check "Hl". load_mode "Hl" "Hmode". step.
  iApply wp_ret; [reflexivity | vx |]. iNext. iApply "HK".
  iExists ((if mode mod 2 ^ 32 =? 0 mod 2 ^ 32 then 1 else 0) mod 2 ^ 32). iSplit.
  { iPureIntro. split; [reflexivity|]. destruct (_ =? _); [right | left]; reflexivity. }
  out_close "HR" with w. exact Hw.
Qed.

(** A caller of `c: __find_specmb` uses this lemma. The lemma says
    that the compiled function returns a pointer to the first percent
    sign of a string and gives the string back. The function calls
    `c: __strchrnul` to search the string, so the program must define
    that function too. *)
Lemma find_spec_has_spec
    `{!Defines ge "glibc_vfprintf_internal#__find_specmb.gnu_inline" glibc_find_specmb}
    `{!Defines ge "__GI___strchrnul" glibc_strchrnul} :
  HasSpec registry (os_wi w0) ge (TAtom "glibc_vfprintf_internal#__find_specmb.gnu_inline") find_spec_spec.
Proof using Type.
  intros [[dq p] s]. exists glibc_find_specmb. split; [exact defines|]. split; [eexists; reflexivity|].
  intros fr Φ Hfr. injection Hfr as <-. cbn [fs_pre fs_post find_spec_spec].
  iIntros "Hs HK". iApply (wp_find_specmb with "Hs"); [exact defines|].
  iIntros "Hs". iApply "HK". iFrame "Hs". done.
Qed.

End small.
