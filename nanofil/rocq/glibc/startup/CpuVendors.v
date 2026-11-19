(** `c: init_cpu_features` asks one of four vendor handlers for each
    cache parameter. The Intel handler walks the descriptor bytes of
    CPUID leaf 2 and looks each word up with `c: intel_check_word`.
    The AMD, Zhaoxin and Hygon handlers read the cache leaves directly
    and compute sizes from fields of the answers. Those computations
    shift and divide by numbers that the processor chose. The checker
    shows that no answer makes any of the four handlers trap, for each
    of the twelve cache parameters that startup asks for. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Bool.
From Nanofil Require Import Term Syntax Values Memory Ops Semantics Pieces Heap.
From Nanofil Require Import AbsRun AbsInfer.
From Glibc Require Import OsWorld OsCpuid CpuSetup CpuPlans CpuSound CpuIntelWord.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.
Open Scope Z_scope.

Definition hi := Eval vm_compute in fn "glibc_libc_start#handle_intel".
Definition am := Eval vm_compute in fn "glibc_libc_start#handle_amd".
Definition zh := Eval vm_compute in fn "glibc_libc_start#handle_zhaoxin".
Definition hy := Eval vm_compute in fn "glibc_libc_start#handle_hygon".

Lemma hi_find : cpu_fn "glibc_libc_start#handle_intel" hi.
Proof. vm_compute. split; reflexivity. Qed.
Lemma am_find : cpu_fn "glibc_libc_start#handle_amd" am.
Proof. vm_compute. split; reflexivity. Qed.
Lemma zh_find : cpu_fn "glibc_libc_start#handle_zhaoxin" zh.
Proof. vm_compute. split; reflexivity. Qed.
Lemma hy_find : cpu_fn "glibc_libc_start#handle_hygon" hy.
Proof. vm_compute. split; reflexivity. Qed.

(** The Intel handler takes the parameter's number, the feature
    structure and the caller's cache record. *)
Definition hi_pre (n : Z) := spec [CI n n; glo cpu; par 2] [(cpu, cpu1); (kn, known)] [None; None; Some cache0].
Definition hi_plans := Eval vm_compute in somes (map (fun n => plan_of t2 hi [] [] (hi_pre n)) names).
Lemma hi_checked : forallb (verified t2 hi []) hi_plans = true.
Proof. vm_compute. reflexivity. Qed.

(** The other three handlers take only the parameter's number. *)
Definition leaf_pre (n : Z) := spec [CI n n] [(cpu, cpu0)] [None].
(** Each pair joins a cache parameter to the largest result allowed by the
    inferred interval. AMD and Hygon share their limits. Zhaoxin uses its
    own encoding for the cache leaves. *)
Definition vendor_specs limits :=
  map (fun pair => let sp := leaf_pre (fst pair) in
    cpu_result sp (sp_pre sp) (Some (CI 0 (snd pair)))) (combine names limits).
Definition amd_limits : list Z :=
  [4294967295; 4096; 4294967295; 261120; 4096; 4294967295;
   67107840; 4096; 8793945538560; 2146959360; 4096; 0].
Definition zhaoxin_limits : list Z :=
  [4294967295; 4096; 4294967295; 1024; 4096; 4294967295; 1024; 4096; 4294967295; 1024; 4096; 0].

Definition am_plans := somes (map (fun n => plan_of [] am [] [] (leaf_pre n)) names).
Definition zh_plans := somes (map (fun n => plan_of [] zh [] [] (leaf_pre n)) names).
Definition hy_plans := somes (map (fun n => plan_of [] hy [] [] (leaf_pre n)) names).
Definition am_specs : list fspec := vendor_specs amd_limits.
Lemma am_certificate : certifies [] am [] am_plans am_specs.
Proof. vm_compute. split; reflexivity. Qed.
Lemma am_checked : forallb (verified [] am []) am_plans = true.
Proof. exact (proj2 am_certificate). Qed.
Definition zh_specs : list fspec := vendor_specs zhaoxin_limits.
Lemma zh_certificate : certifies [] zh [] zh_plans zh_specs.
Proof. vm_compute. split; reflexivity. Qed.
Lemma zh_checked : forallb (verified [] zh []) zh_plans = true.
Proof. exact (proj2 zh_certificate). Qed.
Definition hy_specs : list fspec := vendor_specs amd_limits.
Lemma hy_certificate : certifies [] hy [] hy_plans hy_specs.
Proof. vm_compute. split; reflexivity. Qed.
Lemma hy_checked : forallb (verified [] hy []) hy_plans = true.
Proof. exact (proj2 hy_certificate). Qed.

Definition t3 : table :=
  [("glibc_libc_start#handle_intel", map fst hi_plans); ("glibc_libc_start#handle_amd", am_specs);
   ("glibc_libc_start#handle_zhaoxin", zh_specs); ("glibc_libc_start#handle_hygon", hy_specs)] ++ t2.

(** Every handler was checked for all twelve parameters. *)
Lemma vendor_counts :
  (length hi_plans, length am_plans, length zh_plans, length hy_plans) = (12, 12, 12, 12)%nat.
Proof.
  exact (f_equal2 pair (f_equal2 pair (f_equal2 pair eq_refl (certified_count am_certificate))
    (certified_count zh_certificate)) (certified_count hy_certificate)).
Qed.

Section sound.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ} (w0 : os_world) (ge : genv) {Hge : CpuImage ge}.
Hypothesis Hends : ow_leaf4_ends w0 = true.

(** The four vendor handlers satisfy their specifications. *)
Lemma t3_holds : table_holds w0 ge t3.
Proof using Hends Hge.
  apply table_cons; [exact (verified_holds w0 ge Hends t2 _ hi [] hi_plans hi_find (t2_holds w0 ge Hends) hi_checked)|].
  apply table_cons; [exact (certified_holds w0 ge Hends am_find (table_nil w0 ge) am_certificate)|].
  apply table_cons; [exact (certified_holds w0 ge Hends zh_find (table_nil w0 ge) zh_certificate)|].
  apply table_cons; [|exact (t2_holds w0 ge Hends)].
  exact (certified_holds w0 ge Hends hy_find (table_nil w0 ge) hy_certificate).
Qed.

End sound.
