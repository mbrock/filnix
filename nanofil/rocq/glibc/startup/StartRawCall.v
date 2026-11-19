(** Startup calls two functions through pointers rather than by name.
    The constructor runner calls each constructor from its table, and
    `c: __libc_start_call_main` calls main. A contract in
    [GlibcSpec](../base/GlibcSpec.v) names its function, so this module
    proves a rule that uses such a contract at a call through a pointer.

    ## The rule

    A call through a pointer checks the pointer, converts the arguments
    to the callee's parameters and runs the callee's body. When the
    converted arguments are the ones the callee's contract expects, the
    caller uses the contract as it would at a call by name. *)

From Glibc Require Import GlibcProgram.
From Glibc Require Import GlibcTactics OsTactics GlibcSpec.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsWorld FileInv LibioLogic LibioCloseSteps.
From Glibc Require Import Fix.
Import ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0 Fix.LG0.L FileInv LibioLogic LibioCloseSteps.
Open Scope Z_scope.

Section raw_call.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** A call through a checked pointer to the function n runs n's body
    with the converted arguments. When those arguments are the ones that
    n's contract expects, the caller resumes with the contract's
    postcondition, as at a direct call. *)
Lemma wp_raw_call_spec n s `{Hs : !HasSpec registry (os_wi w0) ge n s} x f e ls lab r callee args rest j p gf xs ys words Ψ :
  value_x ge e F callee = Some (WPtr p) -> ptr_cap p = Fn n -> function_check_res ge p = Some ok ->
  map_option (arg_x ge e) args = Some xs -> find_fn ge n = Some (Defined gf) ->
  indirect_call_conv gf r args xs = Some (Converted ys words) ->
  (ys ++ (if variadic_func gf then skipn (length (fn_params gf)) xs else []))%list = fs_args s x ->
  fs_pre s x -∗
  (∀ v, fs_post s x v -∗ ∃ cf', ⌜resume (mkFrame f e ls None (Exec lab rest j)) (mkPending r words) v = Some cf'⌝ ∗
     ▷ WP (ERun cf' : sexpr) {{ Ψ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec lab (RawCall r callee args :: rest) j)) : sexpr) {{ Ψ }}.
Proof using Type.
  intros Hv Hp Hc Hx Hf Hcv Hys. iIntros "HP HK".
  destruct (Hs x) as (gf' & Hg & [fr Hfr] & Ht).
  rewrite Hf in Hg. injection Hg as <-. rewrite <- Hys in Hfr.
  iApply (wp_raw_call_bind with "[HP HK]"); [exact Hv | exact Hp | exact Hc | exact Hx | exact Hf | exact Hcv | exact Hfr |].
  iNext. rewrite Hys in Hfr. iApply (Ht fr _ Hfr with "HP"). iIntros (v) "HQ". iApply ("HK" with "HQ").
Qed.

End raw_call.
