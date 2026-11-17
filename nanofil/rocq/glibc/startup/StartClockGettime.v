(** This module proves the contract of glibc's `c: clock_gettime`,
    stated in [StartClockGettimeSpec](StartClockGettimeSpec.v), over the
    compiled body of `c: __GI___clock_gettime`. The body makes one call
    to `c: zsys_clock_gettime` and returns what that call returns.

    ## Where the body lives

    The body is defined here, next to its only proof, rather than in a
    shared module. So adding it rebuilds only this file and the final
    startup assembly. *)

From Glibc Require Import GlibcProgram.
From Glibc Require Import GlibcTactics LibioTactics GlibcSpec.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import HiAtexitModule OsBlocks OsWorld FileInv LibioLogic LibioCloseSteps StartCode StartLogic OsClockGettime StartClockGettimeSpec.
From Glibc Require FileInv LibioCloseSteps LibioLogic OsWorld.
From Glibc Require Import Fix.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic LibioCloseSteps.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.

(** This constant is the body of `c: __GI___clock_gettime`. *)
Definition start_clock_gettime_fn : func := Eval vm_compute in start_fn "__GI___clock_gettime".

(** The image defines `c: __GI___clock_gettime` with that body. *)
Lemma start_clock_gettime_defined :
  find_direct (TAtom "__GI___clock_gettime") hi_module = Some (Defined start_clock_gettime_fn).
Proof. vm_compute. reflexivity. Qed.

(** ## The proof

    The wrapper forwards both arguments unchanged, so its contract is
    the runtime call's contract. The proof steps through the one call
    and the return. *)

Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** Any program whose image defines the wrapper with this body, and
    whose registry holds the runtime's clock contract, meets the
    contract. *)
Lemma clock_gettime_has_spec `{!Defines ge "__GI___clock_gettime" start_clock_gettime_fn} :
  registry (TAtom "zsys_clock_gettime") = Some os_clock_gettime_contract ->
  os_ext ge "zsys_clock_gettime" ->
  HasSpec registry (os_wi w0) ge (TAtom "__GI___clock_gettime") clock_gettime_spec.
Proof using Type.
  intros Hr [Hf Hg] [[[clk b] reg] eb]. exists start_clock_gettime_fn.
  split; [apply defines|]. split; [eexists; reflexivity|]. intros fr Φ Hfr. injection Hfr as <-.
  cbn [fs_pre fs_post fs_args clock_gettime_spec].
  iIntros "(%H & Hl & Hb & He) HK". destruct H as (Hclk & Heb & Hend).
  iApply (wp_live_fit1 with "Hl"). iIntros ([H0 H48]) "Hl".
  step. iApply (wp_zsys_clock_gettime _ _ _ _ _ _ _ _ _ clk b reg 0 eb with "Hl [Hb] He"); [exact Hr | exact Hf | exact Hg | (cbn; rewrite (Z.mod_small clk) ?Z.add_0_r; [reflexivity | lia]) | exact Heb | lia
    | unfold timespec_size in *; lia | iExact "Hb" |].
  iNext. iIntros (k Hk) "Hl Hb He". iApply wp_ret; [reflexivity | vx |]. iNext.
  iApply "HK". iExists k. iFrame. iPureIntro. split; [|exact Hk].
  f_equal. f_equal. destruct Hk as [-> | ->]; reflexivity.
Qed.

End rules.
