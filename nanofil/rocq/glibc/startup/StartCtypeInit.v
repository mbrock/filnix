(** This module proves the contract of `c: __ctype_init`, stated in
    [StartCtypeInitSpec](StartCtypeInitSpec.v), over the compiled body
    of `c: __GI___ctype_init`. The body runs straight through: three
    times it follows the locale pointer to the character type data,
    loads one table pointer, moves it into the table and stores it in a
    per-thread cell.

    ## Where the body lives

    The body is defined here, next to its only proof, rather than in a
    shared module. So adding it rebuilds only this file and the final
    startup assembly. *)

From Glibc Require Import Unit_ctype_ctypeZ2dinfo_os.
From Glibc Require Import GlibcProgram.
From Glibc Require Import GlibcTactics OsTactics GlibcSpec.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld FileInv LibioLogic LibioCloseSteps StartCode StartCtypeInitSpec.
From Glibc Require Import Fix.
Import ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0 Fix.LG0.L FileInv LibioLogic LibioCloseSteps.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.

(** This constant is the body of `c: __GI___ctype_init`. *)
Definition start_ctype_init_fn : func := Unit_ctype_ctypeZ2dinfo_os.fn___GI___ctype_init.

(** ## The proof

    The body reads the locale again before each of its three stores,
    since a store might in principle change it. The proof holds the
    locale's cells the whole time, so each read finds the same values. *)

Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** Any program whose image defines the function with this body meets
    the contract. *)
Lemma ctype_init_has_spec `{!Defines ge "__GI___ctype_init" start_ctype_init_fn} :
  HasSpec registry (os_wi w0) ge (TAtom "__GI___ctype_init") ctype_init_spec.
Proof using Type.
  intros [[[o x] y] z]. exists start_ctype_init_fn.
  split; [apply defines|]. split; [eexists; reflexivity|]. intros fr Φ Hfr. injection Hfr as <-.
  cbn [fs_pre fs_post fs_args ctype_init_spec].
  iIntros "(%H & #Hro & Hloc & Hlv & Hb & Hu & Hl) HK".
  destruct H as (Hlt & Hcb & Hcu & Hcl & Hlta & Hlte & Hgla & Hgle & Hcca & Hcce & Hcba & Hcbe & Hcua & Hcue &
    Hcla & Hcle & Hxc & Hxu & Hxl & Hxc0 & Hxu0 & Hxl0 & Hgl & Hcc).
  iDestruct "Hro" as "(#Hlcc & #H56 & #H64 & #H80 & #Hlxc & #Hlxu & #Hlxl)".
  iDestruct "Hloc" as "(Hllt & Hlt & Hlgl & Hgl)". iDestruct "Hlv" as "(Hlcb & Hlcu & Hlcl)".
  (* The class pointer. *)
  step. step_global Hcb. step_global Hlt.
  iApply (wp_live_fit1 with "Hllt"). iIntros ([Hlt0 Hlt48]) "Hllt". check "Hllt". load "Hllt" "Hlt" "Hlgl".
  iApply (wp_live_fit1 with "Hlgl"). iIntros ([Hgl0 Hgl48]) "Hlgl". check "Hlgl".
  iEval (rewrite /live pts_ptsq -/(liveq _ _ _)) in "Hlgl". iEval (rewrite /pcell pts_ptsq -/(pcellq _ _ _ _)) in "Hgl".
  load_pointer_dq "Hlgl Hgl Hlcc" by a2. iNext. iIntros "Hlgl Hgl _".
  iApply (wp_live_fit with "Hlcc"). iIntros ([Hcc0 Hcc48]) "_".
  step. check_read_dq "Hlcc" by a2. iNext. iIntros "_".
  load_pointer_dq "Hlcc H56 Hlxc" by a2. iNext. iIntros "_ _ _".
  step. iApply (wp_live_fit1 with "Hlcb"). iIntros ([Hcb0 Hcb48]) "Hlcb". check "Hlcb". store "Hlcb" "Hb".
  (* The upper-case pointer. *)
  iEval (rewrite /live pts_ptsq -/(liveq _ _ _)) in "Hllt". iEval (rewrite /pcell pts_ptsq -/(pcellq _ _ _ _)) in "Hlt".
  step_global Hcu. step_global Hlt. check_read_dq "Hllt" by a2. iNext. iIntros "Hllt".
  load_pointer_dq "Hllt Hlt Hlgl" by a2. iNext. iIntros "Hllt Hlt Hlgl".
  check_read_dq "Hlgl" by a2. iNext. iIntros "Hlgl". load_pointer_dq "Hlgl Hgl Hlcc" by a2. iNext. iIntros "Hlgl Hgl _".
  step. step. check_read_dq "Hlcc" by a2. iNext. iIntros "_".
  load_pointer_dq "Hlcc H64 Hlxu" by a2. iNext. iIntros "_ _ _".
  step. iApply (wp_live_fit1 with "Hlcu"). iIntros ([Hcu0 Hcu48]) "Hlcu". check "Hlcu". store "Hlcu" "Hu".
  (* The lower-case pointer. *)
  step_global Hcl. step_global Hlt. check_read_dq "Hllt" by a2. iNext. iIntros "Hllt".
  load_pointer_dq "Hllt Hlt Hlgl" by a2. iNext. iIntros "Hllt Hlt Hlgl".
  check_read_dq "Hlgl" by a2. iNext. iIntros "Hlgl". load_pointer_dq "Hlgl Hgl Hlcc" by a2. iNext. iIntros "Hlgl Hgl _".
  step. step. check_read_dq "Hlcc" by a2. iNext. iIntros "_".
  load_pointer_dq "Hlcc H80 Hlxl" by a2. iNext. iIntros "_ _ _".
  step. iApply (wp_live_fit1 with "Hlcl"). iIntros ([Hcl0 Hcl48]) "Hlcl". check "Hlcl". store "Hlcl" "Hl".
  iApply wp_ret_void. iNext. iApply "HK". iSplit; [done|].
  cbn [ptr_addr ptr_cap].
  rewrite !(Z.mod_small 256) ?(Z.mod_small 512) ?(Z.mod_small (ct_xc o)) ?(Z.mod_small (ct_xu o))
    ?(Z.mod_small (ct_xl o)) ?(Z.mod_small (ct_xc o + 256)) ?(Z.mod_small (ct_xu o + 512))
    ?(Z.mod_small (ct_xl o + 512)); try lia.
  iEval (rewrite /liveq /pcellq -!pts_ptsq) in "Hllt Hlt Hlgl Hgl".
  rewrite /ct_locale /ct_lives /live /pcell. iFrame.
Qed.

End rules.
