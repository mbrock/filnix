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
From Glibc Require Import OsWorld OsCpuid HiAtexitModule HiAtexitGe CpuRules CpuSetup CpuSound CpuIntelWord.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.
Open Scope Z_scope.

Definition hi := Eval vm_compute in fn "glibc_libc_start#handle_intel".
Definition am := Eval vm_compute in fn "glibc_libc_start#handle_amd".
Definition zh := Eval vm_compute in fn "glibc_libc_start#handle_zhaoxin".
Definition hy := Eval vm_compute in fn "glibc_libc_start#handle_hygon".

Lemma hi_find : find_fn hge (TAtom "glibc_libc_start#handle_intel") = Some (Defined hi).
Proof. vm_compute. reflexivity. Qed.
Lemma am_find : find_fn hge (TAtom "glibc_libc_start#handle_amd") = Some (Defined am).
Proof. vm_compute. reflexivity. Qed.
Lemma zh_find : find_fn hge (TAtom "glibc_libc_start#handle_zhaoxin") = Some (Defined zh).
Proof. vm_compute. reflexivity. Qed.
Lemma hy_find : find_fn hge (TAtom "glibc_libc_start#handle_hygon") = Some (Defined hy).
Proof. vm_compute. reflexivity. Qed.

(** The Intel handler takes the parameter's number, the feature
    structure and the caller's cache record. *)
Definition hi_pre (n : Z) := spec [CI n n; glo cpu; par 2] [(cpu, cpu1); (kn, known)] [None; None; Some cache0].
Definition hi_plans := Eval vm_compute in somes (map (fun n => plan_of t2 hi [] [] (hi_pre n)) names).
Lemma hi_checked : forallb (verified t2 hi []) hi_plans = true.
Proof. vm_compute. reflexivity. Qed.

(** The other three handlers take only the parameter's number. *)
Definition leaf_pre (n : Z) := spec [CI n n] [(cpu, cpu0)] [None].
Definition am_plans := Eval vm_compute in somes (map (fun n => plan_of [] am [] [] (leaf_pre n)) names).
Definition zh_plans := Eval vm_compute in somes (map (fun n => plan_of [] zh [] [] (leaf_pre n)) names).
Definition hy_plans := Eval vm_compute in somes (map (fun n => plan_of [] hy [] [] (leaf_pre n)) names).
Lemma am_checked : forallb (verified [] am []) am_plans = true.
Proof. vm_compute. reflexivity. Qed.
Lemma zh_checked : forallb (verified [] zh []) zh_plans = true.
Proof. vm_compute. reflexivity. Qed.
Lemma hy_checked : forallb (verified [] hy []) hy_plans = true.
Proof. vm_compute. reflexivity. Qed.

Definition t3 : table :=
  [("glibc_libc_start#handle_intel", map fst hi_plans); ("glibc_libc_start#handle_amd", map fst am_plans);
   ("glibc_libc_start#handle_zhaoxin", map fst zh_plans); ("glibc_libc_start#handle_hygon", map fst hy_plans)] ++ t2.

(** Every handler was checked for all twelve parameters. *)
Lemma vendor_counts :
  (length hi_plans, length am_plans, length zh_plans, length hy_plans) = (12, 12, 12, 12)%nat.
Proof. reflexivity. Qed.

Section sound.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ} (w0 : os_world).
Hypothesis Hends : ow_leaf4_ends w0 = true.

(** The four vendor handlers satisfy their specifications. *)
Lemma t3_holds : table_holds w0 t3.
Proof using Hends.
  apply table_cons; [exact (verified_holds w0 Hends t2 _ hi [] hi_plans hi_find (t2_holds w0 Hends) hi_checked)|].
  apply table_cons; [exact (verified_holds w0 Hends [] _ am [] am_plans am_find (table_nil w0) am_checked)|].
  apply table_cons; [exact (verified_holds w0 Hends [] _ zh [] zh_plans zh_find (table_nil w0) zh_checked)|].
  apply table_cons; [|exact (t2_holds w0 Hends)].
  exact (verified_holds w0 Hends [] _ hy [] hy_plans hy_find (table_nil w0) hy_checked).
Qed.

End sound.
