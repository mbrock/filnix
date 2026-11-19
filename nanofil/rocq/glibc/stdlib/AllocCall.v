From Glibc Require Import GlibcProgram.
(** The first write to stdout allocates its buffer with glibc's
    `c: malloc`. This file proves the allocation rule used by the
    buffer proofs from AllocLogic.v's triple. The allocator keeps its
    thread cache idle and returns a fresh heap object. *)

From Glibc Require Import GlibcTactics OsTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import Fix OsWorld GlibcSpec AllocLogic.
Import ListNotations Fix.ML0 Fix.LG0 Fix.LG0.L.
Open Scope Z_scope.

Import ProgramAbbreviations.
Section alloc_values.
Context {hlc : has_lc}
  {Σ : gFunctors}
  {invGS_gen0 : invGS_gen hlc Σ}
  {gen_heapGS0 : gen_heapGS piece pval Σ}
  (w0 : os_world)
  (registry : name -> option (contract os_world))
  (ge : genv).
Existing Instance invGS_gen0.
Existing Instance gen_heapGS0.
Local Instance alloc_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** The caller lends its allocator state and takes back either null or a fresh object. *)
Definition getopt_malloc_rule (M : iProp Σ) : Prop :=
  forall f e ls l d v rest j n Φ, arg_x ge e (Arg L v) = Some (WInt n) -> 0 <= n < 2 ^ 64 ->
  ⊢ M -∗ ▷ (∀ p, M -∗ (⌜p = null⌝ ∨ ∃ base, ⌜p = mkPtr base (Obj base) /\ 0 < base /\ base mod 16 = 0 /\
                 base + req_extent (heap_req 16 n) <= 2 ^ 48⌝ ∗ obj base (heap_req 16 n)) -∗
       WP (ERun (mkFrame f (put d (WPtr p) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
    WP (ERun (mkFrame f e ls None (Exec l (Call (CResult d P) (Global (TAtom "malloc")) [Arg L v] :: rest) j)) : gexpr)
      {{ Φ }}.
End alloc_values.

Section rules_values.
Context {Σ : gFunctors}
  {gen_heapGS0 : gen_heapGS piece pval Σ}
  (dq : dfrac)
  (mp : Z)
  (tc : Z)
  (dummy : Z)
  (mpr : region)
  (tcr : region)
  (dr : region).
Existing Instance gen_heapGS0.
Definition malloc_call_state : iProp Σ := AllocLogic.tcache_idle dq mp tc dummy mpr tcr dr.
End rules_values.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context `{Hmalloc_fn : !Defines ge "malloc" malloc_fn}
  `{Hmalloc2 : !Defines ge "glibc_malloc#__libc_malloc2" malloc2_fn}.
Context (dq : dfrac)
  (mp tc dummy : Z)
  (mpr tcr dr : region).
Context (Hmp : lookup (TAtom "glibc_malloc#mp_") (ge_globals ge) = Some (mkPtr mp (Obj mp)))
  (Htc : lookup (TAtom "tcache") (ge_globals ge) = Some (mkPtr tc (Obj tc))).


(** Buffer allocation preserves the idle thread cache. *)

(** A call of glibc's `c: malloc` in a buffer-allocation block returns
    a fresh object and preserves the idle thread cache. *)
Lemma malloc_call_rule f e ls lab d v rest j n Φ :
  arg_x ge e (Arg L v) = Some (WInt n) -> 0 <= n < 2 ^ 64 ->
  (malloc_call_state dq mp tc dummy mpr tcr dr) -∗
  ▷ (∀ base, ⌜0 < base /\ base mod 16 = 0 /\ base + req_extent (heap_req 16 n) <= 2 ^ 48⌝ -∗
       obj base (heap_req 16 n) -∗ (malloc_call_state dq mp tc dummy mpr tcr dr) -∗
       WP (ERun (mkFrame f (put d (WPtr (mkPtr base (Obj base))) e) ls None (Exec lab rest j))
             : language.expr (nanofil_lang registry ge)) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
    (Exec lab (Call (CResult d P) (Global (TAtom "malloc")) [Arg L v] :: rest) j))
        : language.expr (nanofil_lang registry ge)) {{ Φ }}.
Proof using Hmalloc2 Hmalloc_fn Hmp Htc.
  intros Hx Hn. iIntros "HM HK".
  iApply wp_call_bind; [cbn [map_option]; rewrite Hx; reflexivity | exact Hmalloc_fn | reflexivity |].
  iNext.
  iApply (AllocLogic.wp_glibc_malloc registry (os_wi w0) ge n dq mp tc dummy mpr tcr dr with "HM [HK]");
    [exact Hn | | exact Hmp | exact Htc | exact Hmalloc2 |].
  - intros m wd h base Hfresh Hw. exact (os_wi_alloc w0 m wd h (heap_req 16 n) base Hfresh Hw).
  - iIntros (base Hb) "Ho HM". iExists _. iSplit; [iPureIntro; reflexivity|].
    iApply ("HK" with "[%] Ho HM"). exact Hb.
Qed.

End rules.
