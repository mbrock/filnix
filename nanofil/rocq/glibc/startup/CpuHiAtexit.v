(** The startup code of glibc calls `c: init_cpu_features` in every
    program. [CpuSpec](CpuSpec.v) proves a contract for that call. The
    proof needs a few facts about the linked program that contains
    the call, and the class [CpuImage] of [CpuSound](CpuSound.v) lists
    them. This module proves those facts for the hi_atexit image, so
    the contract holds for hi_atexit.

    A proof about another program, such as Hello, repeats only this
    module. It proves the same facts for its own image, which is one
    computation, and then it has the contract. The long computations
    of the other modules are not run again. *)

From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import weakestpre.
From Stdlib Require Import String ZArith List.
From Nanofil Require Import Term Syntax Values Memory Semantics Pieces Heap.
From Glibc Require Import Fix GlibcProgram GlibcSpec OsWorld OsCpuid OsRegistry HiAtexitModule HiAtexitGe
  CpuSetup CpuSound CpuInitSpec CpuSpec.
Import ListNotations.
Open Scope string_scope.

(** The hi_atexit image contains the sixteen functions that
    `c: init_cpu_features` runs, with the code that the proofs were
    made for. It does not define the three CPU calls, and it has an
    address for the comparison function. Each fact is checked by
    computing with the image. *)
#[global] Instance hi_cpu_image : CpuImage hge.
Proof.
  split.
  - unfold cpu_fns. repeat (constructor; [vm_compute; reflexivity|]). constructor.
  - repeat (constructor; [split; vm_compute; reflexivity|]). constructor.
  - eexists. split; vm_compute; reflexivity.
Qed.

Section hi.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ} (w0 : os_world).

(** The function `c: init_cpu_features` of the hi_atexit image
    satisfies its contract in every world whose list of caches ends. *)
Theorem hi_init_cpu_features_has_spec :
  ow_leaf4_ends w0 = true ->
  HasSpec glibc_os_registry (os_wi w0) hge (TAtom "glibc_libc_start#init_cpu_features")
    (init_cpu_features_spec (glibc_program := program_of w0 glibc_os_registry hge)).
Proof using Type. exact (init_cpu_features_has_spec w0 hge). Qed.

End hi.
