(** The constructor `c: _IO_stdfiles_init` links glibc's three standard
    streams backwards before `c: main` runs.
    [StartStdfilesInitSpec](StartStdfilesInitSpec.v) states its
    contract, and this module proves it. The work is already done in
    [LibioStdfiles](../libio/LibioStdfiles.v), whose rule runs the
    loop of the constructor. The proof here only puts that rule into
    the form of a contract. *)

From Glibc Require Import GlibcProgram GlibcSpec.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Pieces Heap Logic MemLogic.
From Glibc Require Import OsWorld FileInv LibioStdfiles StartStdfilesInitSpec.
Import ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0 Fix.LG0.L FileInv LibioStdfiles.
Open Scope Z_scope.

Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.

(** Any program whose image defines the constructor with this body
    meets the contract. *)
Lemma stdfiles_init_has_spec `{!Defines ge "glibc_stdfiles#_IO_stdfiles_init" glibc_stdfiles_init} :
  HasSpec registry (os_wi w0) ge (TAtom "glibc_stdfiles#_IO_stdfiles_init") stdfiles_init_spec.
Proof using Type.
  intros [[[[[[[[fe fo] fi] la] lareg] lk] lkreg] rf] rfreg]. exists glibc_stdfiles_init.
  split; [apply defines|]. split; [eexists; reflexivity|]. intros fr Φ Hfr.
  cbn [fs_pre fs_post fs_args stdfiles_init_spec].
  iIntros "(%H & Hla & Hc & He & Ho & Hi & Hlk & Hrf & Hrfc) HK".
  destruct H as (Hgla & Hglk & Hgrf & Hlal & Hlaend & Hrfal & Hrfend).
  iApply (wp_glibc_stdfiles_init fr fe fo fi la lareg lk lkreg rf rfreg Φ Hfr Hgla Hglk Hgrf Hlal Hlaend Hrfal Hrfend
            with "Hla Hc He Ho Hi Hlk Hrf Hrfc").
  iNext. iIntros "Hinv Hlives". iApply "HK". iFrame "Hinv Hlives". done.
Qed.

End rules.
