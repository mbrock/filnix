From Glibc Require Import GlibcProgram.
(** When getopt collects the candidates for an ambiguous long option, it
    calls malloc, and the parser's proofs take a rule for that call as a
    premise. This module proves the rule from glibc's own malloc, which
    AllocLogic.v captured and proved.

    The captured malloc reads glibc's thread cache, so the rule's resource
    is a share of the idle cache and its globals, and each call gives that
    share back. The call either stalls or returns a fresh heap object of
    the requested size rounded up to 16 bytes. It never returns null: in
    nanofil an allocation that cannot be met ends the run rather than
    returning. The rule still allows a null answer, so the parser's proofs
    keep their failure routes. *)
From Glibc Require Import GlibcTactics OsTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import OsWorld OsMemLogic AllocLogic AllocCall.
Import ListNotations.
Open Scope Z_scope.
Import Fix.ML0 Fix.LG0 Fix.LG0.L OsWorld OsMemLogic.

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.

(** The parser should not need a promise about malloc when the program
    links glibc's own. Given the bindings of malloc, its inner allocator
    and the cache globals, this lemma proves the rule, and every answer
    it gives is a fresh object. *)
Lemma getopt_malloc_rule_glibc `{!Defines ge "malloc" malloc_fn, !Defines ge "glibc_malloc#__libc_malloc2" malloc2_fn}
    dq mp tc dummy mpr tcr dr :
  lookup (TAtom "glibc_malloc#mp_") (ge_globals ge) = Some (mkPtr mp (Obj mp)) ->
  lookup (TAtom "tcache") (ge_globals ge) = Some (mkPtr tc (Obj tc)) ->
  getopt_malloc_rule w0 registry ge (malloc_call_state dq mp tc dummy mpr tcr dr).
Proof using Type.
  intros Hmp Htc f e ls l d v rest j n Φ Hx Hn. iIntros "HM HK".
  iApply (malloc_call_rule with "HM"); [exact Hmp | exact Htc | exact Hx | exact Hn |].
  iNext. iIntros (base Hb) "Ho HM". iApply ("HK" with "HM"). iRight. iExists base. iFrame. iPureIntro. tauto.
Qed.
End rules.

(** ## Controls

    The object that a call returns is the request rounded up to 16 bytes.
    A request of 0 bytes gets an object of 0 bytes, one byte gets 16, and
    17 bytes get 32. Every object starts on a 16-byte boundary. *)
Example malloc_extents :
  map (fun n => req_extent (heap_req 16 n)) [0; 1; 16; 17] = [0; 16; 16; 32] /\
  req_align (heap_req 16 1) = 16.
Proof. split; reflexivity. Qed.
