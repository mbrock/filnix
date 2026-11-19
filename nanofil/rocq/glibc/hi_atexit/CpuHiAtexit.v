(** The startup code of glibc calls `c: init_cpu_features` in every
    program. [CpuSpec](../startup/CpuSpec.v) proves a contract for that call. The
    proof needs a few facts about the linked program that contains
    the call, and the class [CpuImage] of [CpuSound](../startup/CpuSound.v) lists
    them. This module proves those facts for the hi_atexit image, so
    the contract holds for hi_atexit.

    A proof about another program, such as Hello, repeats only this
    module. It proves the same facts for its own image, which is one
    computation, and then it has the contract. The long computations
    of the other modules are not run again. *)

From Glibc Require Import CpuInit.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import weakestpre.
From Stdlib Require Import String ZArith List.
From Nanofil Require Import Term Syntax Values Memory Semantics Pieces Heap.
From Glibc Require Import Fix GlibcProgram GlibcSpec OsWorld OsCpuid OsRegistry HiAtexitModule HiAtexitGe
  HiAtexitInitial CpuSetup CpuSound CpuInitSpec CpuSpec CpuPlace.
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

(** The contract names eighteen global objects, and its caller must
    say where they lie. This record gives the address and the region
    of each one in hi_atexit. It is computed from the memory that the
    loader builds for the image. *)
Definition hi_icf_objs : icf_objs := Eval vm_compute in
  match icf_objs_in hi_globals (m_regions hi_m0) with Some o => o | None => icf_no_objs end.

(** The record above is what the search returns for this program.
    The search returns a record only when each of the eighteen
    globals has the right kind of pointer, is aligned, and fits in
    its region. *)
Lemma hi_icf_found : icf_objs_in hi_globals (m_regions hi_m0) = Some hi_icf_objs.
Proof. vm_compute. reflexivity. Qed.

(** When the program starts, the loader has given every global a
    region of memory. The regions in the record are exactly those.
    A proof that owns the globals at the start can therefore hand
    them to the call without any change. *)
Lemma hi_icf_regions :
  Forall (fun q => object_region (fst q) (m_regions hi_m0) = Some (snd q)) (icf_regions hi_icf_objs).
Proof. exact (icf_objs_in_regions _ _ _ hi_icf_found). Qed.

Lemma icf_image_start : icf_start_ok hi_module = true.
Proof. vm_compute. reflexivity. Qed.

Section hi.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ} (w0 : os_world).

(** The function `c: init_cpu_features` of the hi_atexit image
    satisfies its contract in every world whose list of caches ends. *)
Theorem hi_init_cpu_features_has_spec :
  ow_leaf4_ends w0 = true ->
  HasSpec glibc_os_registry (os_wi w0) hge (TAtom "glibc_libc_start#init_cpu_features")
    (init_cpu_features_spec (glibc_program := program_of w0 glibc_os_registry hge)).
Proof using Type. exact (init_cpu_features_has_spec w0 hge). Qed.

(** The contract first asks that each global lies where the record
    says, is aligned, and fits in its region. The record of hi_atexit
    passes all of that. A caller in hi_atexit is left with one duty,
    which is to own the eighteen objects. *)
Lemma hi_icf_ok : icf_ok (glibc_program := program_of w0 glibc_os_registry hge) hi_icf_objs.
Proof using Type. exact (icf_objs_in_ok (glibc_program := program_of w0 glibc_os_registry hge) _ _ hi_icf_found). Qed.

End hi.
