(** `c: get_common_cache_info` walks the list of caches that CPUID
    leaf 4 reports. It asks for subleaf 0, 1, 2 and so on, and it stops
    when an answer has cache type zero. It counts the subleaves in a
    signed 32-bit integer and uses fields of each answer as shift
    counts, as divisors and as an index into a table of sixteen rows.

    A processor decides when the list ends. Suppose that no subleaf up
    to 0x7fffffff reported cache type zero. The counter would then
    wrap to a negative number, and the index computed from it would
    fail its bounds check. That is a real trap, so the proof assumes
    that the list ends. The assumption is used at one place only,
    which is the answer for subleaf 0x7fffffff. The last lemma of this
    module is a control. It shows that the check fails without the
    assumption. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Bool.
From Nanofil Require Import Term Syntax Values Memory Ops Semantics Pieces Heap.
From Nanofil Require Import AbsRun AbsInfer.
From Glibc Require Import OsWorld OsCpuid HiAtexitModule CpuRules CpuSetup CpuPlans CpuSound CpuIntelWord.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.
Open Scope Z_scope.

Definition gcc := Eval vm_compute in fn "glibc_libc_start#get_common_cache_info".
Lemma gcc_find : cpu_fn "glibc_libc_start#get_common_cache_info" gcc.
Proof. vm_compute. split; reflexivity. Qed.

(** The Intel path passes its cache record, and the Zhaoxin path
    passes a null pointer in its place. *)
Definition gcc_i := spec [par 0; par 1; par 2; CI 0 18446744073709551615; par 4] [(cpu, cpu1)]
  [Some (weak 16 16); Some (weak 16 16); Some (weak 16 16); None; Some cache0].
Definition gcc_z := spec [par 0; par 1; par 2; CI 0 18446744073709551615; CN 0 0] [(cpu, cpu0)]
  [Some (weak 16 16); Some (weak 16 16); Some (weak 16 16); None; None].
Definition gcc_nc := [TAtom "L92"; TAtom "L98"; TAtom "L148"; TAtom "L160"].

Definition gcc_i_plans := somes [plan_of [] gcc gcc_nc [] gcc_i].
Definition gcc_z_plans := somes [plan_of [] gcc [] [] gcc_z].
Definition gcc_i_specs : list fspec := [cpu_result gcc_i (sp_pre gcc_i) None].
Lemma gcc_i_certificate : certifies [] gcc gcc_nc gcc_i_plans gcc_i_specs.
Proof. vm_compute. split; reflexivity. Qed.
Lemma gcc_i_checked : forallb (verified [] gcc gcc_nc) gcc_i_plans = true.
Proof. exact (proj2 gcc_i_certificate). Qed.
Definition gcc_z_specs : list fspec := [cpu_result gcc_z (sp_pre gcc_z) None].
Lemma gcc_z_certificate : certifies [] gcc [] gcc_z_plans gcc_z_specs.
Proof. vm_compute. split; reflexivity. Qed.
Lemma gcc_z_checked : forallb (verified [] gcc []) gcc_z_plans = true.
Proof. exact (proj2 gcc_z_certificate). Qed.

Definition gcc_table : table :=
  [("glibc_libc_start#get_common_cache_info", gcc_i_specs ++ gcc_z_specs)].

Lemma gcc_counts : (length gcc_i_plans, length gcc_z_plans) = (1, 1)%nat.
Proof.
  exact (f_equal2 pair (certified_count gcc_i_certificate) (certified_count gcc_z_certificate)).
Qed.

(** The proof needs the assumption that the list of caches ends. This
    lemma runs the checker on the Intel path without the assumption,
    and the checker stops at the block that indexes the table of
    sixteen rows. *)
Lemma gcc_needs_leaf4 :
  map fst (a_fail (plan (cpu_builtin false) gobjs fnames (specs_of []) gcc gcc_nc [] 3000 20000 3 gcc_i))
  = [TAtom "L90"].
Proof. vm_compute. reflexivity. Qed.

Section sound.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ} (w0 : os_world) (ge : genv) {Hge : CpuImage ge}.
Hypothesis Hends : ow_leaf4_ends w0 = true.

(** `c: get_common_cache_info` satisfies both specifications. *)
Lemma gcc_table_holds : table_holds w0 ge gcc_table.
Proof using Hends Hge.
  apply table_cons; [|apply table_nil]. intros sp Hin. apply in_app_or in Hin as [Hin|Hin].
  - exact (certified_holds w0 ge Hends gcc_find (table_nil w0 ge) gcc_i_certificate sp Hin).
  - exact (certified_holds w0 ge Hends gcc_find (table_nil w0 ge) gcc_z_certificate sp Hin).
Qed.

End sound.
