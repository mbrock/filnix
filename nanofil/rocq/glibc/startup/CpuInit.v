(** The startup code of glibc calls
    `c: init_cpu_features (&_dl_x86_cpu_features)` before it does
    anything that depends on the processor. The function asks the
    processor and the kernel what they support through `c: zcpuid`,
    `c: zcpuid_count` and `c: zxgetbv`, and it computes with the
    answers. This module proves that the function never panics, for
    every answer.

    The code of the function is taken from the hi_atexit program.
    Other programs link the same code from glibc, and the theorem
    covers them too. Hello is one such program.

    The theorem assumes one thing about the processor. The list of
    caches that CPUID leaf 4 reports must end. A processor whose list
    never ended would make the function trap, as
    [CpuCache](CpuCache.v) explains. The theorem assumes nothing about
    XSAVE. The function reads the extended control register only after
    it has seen the XSAVE bit in the answer for leaf 1, and the
    processor sets that bit only when the kernel enabled XSAVE.

    The tunables stay at the values of the image, because nothing
    that startup reaches calls `c: __tunables_init`. The function
    writes six rows of the tunable table. The rows that later startup
    code reads keep their type codes and their cleared `initialized`
    flags, and [icf_tunables_kept] states that. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Bool.
From Nanofil Require Import Term Syntax Values Memory Ops Semantics Pieces Heap.
From Nanofil Require Import AbsRun AbsInfer AbsDen AbsSound.
From Glibc Require Import Fix OsWorld OsCpuid OsRegistry CpuHook CpuSetup CpuPlans CpuSound
  CpuTunables CpuParts.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.
Open Scope Z_scope.

Definition icf := Eval vm_compute in fn "glibc_libc_start#init_cpu_features".
Lemma icf_find : cpu_fn "glibc_libc_start#init_cpu_features" icf.
Proof. vm_compute. split; reflexivity. Qed.

(** Startup calls the function with the address of the feature
    structure. The feature structure and the small globals may hold
    any bytes at that point. The descriptor table holds the bytes of
    the image, and the tunable table holds the type codes and the
    flags that [CpuTunables](CpuTunables.v) lists. *)
Definition icf_pre : fspec := spec [glo cpu] gall [None].
(** A precondition is useful only when startup can meet it. The check
    [icf_start_ok] reads the initial data of a module and tests that
    each global object that the function touches starts with contents
    that the precondition allows. The hi_atexit image passes it. Its
    feature structure starts as zeros, and its tunable table starts
    with the type codes and the cleared flags. *)
Definition icf_start_ok (md : module) : bool :=
  forallb (fun p => match gobj_in md (fst p) with Some ob => obj_le (st0 false) ob (snd p) | None => false end) gall.
Definition icf_plans := somes [plan_of t6 icf [] [] icf_pre].
(** The call sets the low byte of _dl_hwcap to a value from two through six
    and clears its other seven bytes. The other objects keep their bounds. *)
Definition icf_spec : fspec :=
  let hwcap := with_bytes 0 (BIn 2 6 :: repeat (BK 0) 7) (weak 8 8) in
  cpu_result icf_pre (post_global icf_pre "_dl_hwcap" hwcap) None.

Lemma icf_certificate : certifies t6 icf [] icf_plans [icf_spec].
Proof. vm_compute. split; reflexivity. Qed.

Lemma icf_checked : forallb (verified t6 icf []) icf_plans = true.
Proof. exact (proj2 icf_certificate). Qed.

Lemma icf_spec_in : In icf_spec (map fst icf_plans).
Proof. rewrite (proj1 icf_certificate). left. reflexivity. Qed.

Lemma icf_spec_shape :
  sp_args icf_spec = sp_args icf_pre /\ sp_pre icf_spec = sp_pre icf_pre /\ sp_guard icf_spec = false /\
  sp_ret icf_spec = None /\ length (sp_post icf_spec) = length (sp_pre icf_pre).
Proof. vm_compute. auto. Qed.

(** After the call the tunable table still satisfies [tun0]. In
    particular each row that later startup code reads has its type
    code and a cleared `initialized` flag. *)
Lemma icf_tunables_kept :
  exists ob, nth_error (sp_post icf_spec) 1 = Some (Some ob) /\ obj_le (st0 false) ob tun0 = true /\
    map (fun id => (id, window (id * 136 + 48) 4 (o_bytes ob), window (id * 136 + 104) 1 (o_bytes ob))) later =
    [(14, le4 2, [BK 0]); (15, le4 2, [BK 0]); (17, le4 2, [BK 0]); (18, le4 0, [BK 0]); (19, le4 2, [BK 0]);
     (21, le4 0, [BK 0]); (22, le4 2, [BK 0]); (23, le4 2, [BK 0]); (24, le4 2, [BK 0]); (25, le4 2, [BK 0]);
     (27, le4 0, [BK 0])].
Proof. vm_compute. eexists. split; [reflexivity|]. split; reflexivity. Qed.

Section sound.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ} (w0 : os_world) (ge : genv) {Hge : CpuImage ge}.

(** This theorem is the result of the module. It assumes that the
    list of caches that the processor reports ends. A call of
    `c: init_cpu_features` in the linked program then runs without a
    panic, whatever the processor and the kernel answer. The call may
    start from any memory that the precondition allows. When it
    returns, it gives the global objects back with the contents that
    the postcondition describes. *)
Theorem init_cpu_features_safe :
  ow_leaf4_ends w0 = true -> holds w0 ge (TAtom "glibc_libc_start#init_cpu_features") icf_spec.
Proof using Hge.
  intros Hends.
  exact (verified_holds w0 ge Hends t6 _ icf [] icf_plans icf_find (t6_holds w0 ge Hends) icf_checked icf_spec icf_spec_in).
Qed.

End sound.
