(** During early initialization glibc reads the mutex spin count, tunable
    27, through `c: __pthread_tunables_init`. Its caller needs to know
    only that the call reads that tunable and leaves the table as it was.
    This module states that contract, so that the caller can import it
    without the proof, which lives in
    [StartPthreadTunables](StartPthreadTunables.v). *)

From Glibc Require Import GlibcProgram GlibcSpec StartTunableGetValSpec.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From Stdlib Require Import String ZArith List.
From Nanofil Require Import Term Syntax Values Memory Semantics Pieces Heap Runtime Logic.
From Glibc Require Import FileInv.
Import ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0 Fix.LG0.L.
Open Scope Z_scope.

Section specs.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.

(** A call of `c: __pthread_tunables_init()` reads int tunable 27, whose
    value is v, and gives its entry back unchanged. *)
Definition pthread_tunables_init_spec : fspec Σ :=
  FSpec (Z * region * Z) (fun _ => [])
    (fun '(tl, tlreg, v) => ⌜tunable_slot_ok tl tlreg 27⌝ ∗ live tl tlreg ∗ tunable_entry tl 27 0 v)%I
    (fun '(tl, tlreg, v) o => ⌜o = RetVoid⌝ ∗ live tl tlreg ∗ tunable_entry tl 27 0 v)%I.

End specs.
