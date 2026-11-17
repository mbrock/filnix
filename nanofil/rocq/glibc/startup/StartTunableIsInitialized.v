(** This module proves the contract of `c: __tunable_is_initialized`,
    stated in [StartTunableIsInitializedSpec](StartTunableIsInitializedSpec.v),
    over the function's compiled body. The body finds the tunable's
    entry in the table and loads its initialized byte.

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
From Glibc Require Import HiAtexitModule OsBlocks OsWorld FileInv LibioLogic LibioCloseSteps StartCode StartLogic StartTunableGetValSpec StartTunableIsInitializedSpec.
From Glibc Require FileInv LibioCloseSteps LibioLogic OsWorld.
From Glibc Require Import Fix.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic LibioCloseSteps.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.

(** This constant is the body of `c: __tunable_is_initialized`. *)
Definition start_tunable_is_initialized_fn : func := Eval vm_compute in start_fn "__tunable_is_initialized".

(** The linked image contains that body under this name. *)
Lemma start_tunable_is_initialized_defined :
  find_direct (TAtom "__tunable_is_initialized") hi_module = Some (Defined start_tunable_is_initialized_fn).
Proof. vm_compute. reflexivity. Qed.

(** ## The proof

    The body computes the address of the initialized byte from the id
    and reads that one byte. The proof steps through those few
    instructions. *)

Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** Any program whose image defines the function with this body meets
    the contract. *)
#[global] Instance tunable_is_initialized_has_spec
    `{!Defines ge "__tunable_is_initialized" start_tunable_is_initialized_fn} :
  HasSpec registry (os_wi w0) ge (TAtom "__tunable_is_initialized") tunable_is_initialized_spec.
Proof using Type.
  intros [[[[id tl] tlreg] ty] v]. exists start_tunable_is_initialized_fn.
  split; [apply defines|]. split; [eexists; reflexivity|]. intros fr Φ Hfr. injection Hfr as <-.
  cbn [fs_pre fs_post fs_args tunable_is_initialized_spec].
  iIntros "(%H & Hl & (Hty & Hv & Hin)) HK". destruct H as (Htl & Hid & Hal & Hend).
  iApply (wp_live_fit1 with "Hl"). iIntros ([H0 H48]) "Hl".
  step. step_global Htl. step. step. step. step. norm. check "Hl".
  iApply (wp_raw_load_byte with "Hl Hin"); [reflexivity | vx | reflexivity | reflexivity | left; reflexivity | a2 |].
  iNext. iIntros "Hl Hin". iApply wp_ret; [reflexivity | vx |]. iNext. iApply "HK". iFrame. done.
Qed.

End rules.
