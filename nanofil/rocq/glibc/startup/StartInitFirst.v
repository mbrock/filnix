(** This module proves the contract of `c: _init_first`, stated in
    [StartInitFirstSpec](StartInitFirstSpec.v), over the compiled body
    of the function. The body runs straight through. It stores the
    count, the argument array and the environment in their globals,
    and then it calls `c: __init_misc` with the same three arguments.

    ## Where the body lives

    The body is defined here, next to its only proof, rather than in a
    shared module. So adding it rebuilds only this file and the final
    startup assembly. *)

From Glibc Require Import Unit_csu_initZ2dfirst_os.
From Glibc Require Import GlibcProgram.
From Glibc Require Import GlibcTactics OsTactics GlibcSpec.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld FileInv LibioLogic LibioCloseSteps
  StartInitMiscSpec StartInitFirstSpec.
From Glibc Require Import Fix.
Import ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0 Fix.LG0.L FileInv LibioLogic LibioCloseSteps.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.

(** This constant is the body of `c: _init_first`. The function is
    private to its source file, so the linker gave it a longer name. *)
Definition start_init_first_fn : func := Unit_csu_initZ2dfirst_os.fn_glibc_init_first'23_init_first.

Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context `{Hmisc : !HasSpec registry (os_wi w0) ge (TAtom "__init_misc") init_misc_spec}.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** Any program whose image defines the function with this body meets
    the contract, provided that `c: __init_misc` meets its own. *)
Lemma init_first_has_spec `{!Defines ge "glibc_init_first#_init_first" start_init_first_fn} :
  HasSpec registry (os_wi w0) ge (TAtom "glibc_init_first#_init_first") init_first_spec.
Proof using Hmisc.
  intros [[[[[[[[[[f o] dq] argc] envp] a] s] x] y] u] v]. exists start_init_first_fn.
  split; [apply defines|]. split; [eexists; reflexivity|]. intros fr Φ Hfr. injection Hfr as <-.
  cbn [fs_pre fs_post fs_args init_first_spec].
  iIntros "(%H & Hl & Hac & Hlv & Hen & Hn & Ha) HK".
  destruct H as ((Gac & Glv & Gen & Hace & Hlva & Hlve & Hena & Hene) & Hargc & Hok).
  iDestruct "Hl" as "(Lac & Llv & Len)". iDestruct "Hac" as (xs Hxs) "Hac".
  iApply (wp_live_fit1 with "Lac"). iIntros ([Hac0 Hac48]) "Lac".
  iApply (wp_live_fit1 with "Llv"). iIntros ([Hlv0 Hlv48]) "Llv".
  iApply (wp_live_fit1 with "Len"). iIntros ([Hen0 Hen48]) "Len".
  (* The three stores. *)
  step. step_global Gac. check "Lac".
  rule2 "Lac" "Hac" ltac:(eapply wp_raw_store_w; inst; [vx | vx | reflexivity | a2 | exact Hxs | wi_store]).
  step_global Glv. check "Llv". store "Llv" "Hlv". step_global Gen. check "Len". store "Len" "Hen".
  (* The names of the program. *)
  call_spec with (o, dq, argc, envp, a, s, x, y); [cbn; rewrite Z.mod_small; [reflexivity | lia] | exact Hok |].
  cbn [fs_post init_misc_spec] in *. iDestruct "Hpost" as "(-> & Hn & Ha)".
  iExists _. iSplit; [done|]. iNext. cbn [fr_fn fr_env fr_locals fr_doomed fr_at].
  iApply wp_ret_void. iNext. iApply "HK". iSplit; [done|].
  rewrite (Z.mod_small argc); [|lia]. rewrite /if_lives /int_cell /int_bytes. iFrame. done.
Qed.

End rules.
