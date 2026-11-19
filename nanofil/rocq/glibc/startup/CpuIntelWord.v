(** On an Intel processor, `c: handle_intel` decodes the cache
    descriptors of CPUID leaf 2. Each register of the answer holds up
    to four descriptor bytes, and `c: intel_check_word` looks each of
    them up in the sorted table `c: intel_02_known` with a binary
    search. The table index comes from the processor's answer, so this
    is one of the places where a bad answer could trap. The checker
    shows that it cannot. The search stays inside the table for every
    descriptor byte, and the comparison function it calls through a
    pointer reads only the two rows it is given. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Bool.
From Nanofil Require Import Term Syntax Values Memory Ops Semantics Pieces Heap.
From Nanofil Require Import AbsRun AbsInfer.
From Glibc Require Import OsWorld OsCpuid HiAtexitModule CpuRules CpuSetup CpuSound.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.
Open Scope Z_scope.

(** * The comparison *)

Definition cmp := Eval vm_compute in fn "glibc_libc_start#intel_02_known_compare".
Lemma cmp_find : cpu_fn "glibc_libc_start#intel_02_known_compare" cmp.
Proof. vm_compute. split; reflexivity. Qed.

(** The search passes a key on its stack and a row of the table. *)
Definition cmp_pre := spec [par 0; CP 2 0 536] [(kn, known)] [Some (loc 16)].
Definition cmp_plans := Eval vm_compute in somes [plan_of [] cmp [] [] cmp_pre].
Lemma cmp_checked : forallb (verified [] cmp []) cmp_plans = true.
Proof. vm_compute. reflexivity. Qed.
Definition t1 : table := [("glibc_libc_start#intel_02_known_compare", map fst cmp_plans)].

(** * The descriptor word *)

Definition icw := Eval vm_compute in fn "glibc_libc_start#intel_check_word".
Lemma icw_find : cpu_fn "glibc_libc_start#intel_check_word" icw.
Proof. vm_compute. split; reflexivity. Qed.

(** The caller keeps two small fields in front of its cache record: a
    flag and a count of at most sixteen. *)
Definition cache0 : aobj := with_bytes 0 [BIn 0 1; BIn 0 16] (weak 16 288).

(** `c: handle_intel` is asked for one of twelve cache parameters, and
    it passes the parameter's number on. The descriptor word is any
    32-bit number. *)
Definition names : list Z := [185; 187; 188; 189; 190; 191; 192; 193; 194; 195; 196; 197].
Definition icw_pre (n : Z) := spec [CI n n; CI 0 4294967295; par 2; par 3; glo cpu; par 5]
  [(cpu, cpu1); (kn, known)]
  [None; None; Some (loc 16); Some (loc 16); None; Some cache0].
Definition icw_nc := [TAtom "iw_1.L12"; TAtom "iw_1.L36"; TAtom "iw_1.join"].
Definition icw_sv := [TAtom "pr.6"; TAtom "pr.7"; TAtom "pr.9"].
(** The descriptor lookup returns a machine word and preserves every
    abstract bound that the caller supplied for its objects. *)
Definition icw_spec n : fspec :=
  let sp := icw_pre n in
  mkSpec (sp_args sp) (sp_pre sp) false (sp_pre sp) false (Some (CI 0 18446744073709551615)).

(** The search supplies the loop invariants when Rocq checks the proof.
    Importers can read the completed specifications directly from the table. *)
Definition icw_plans := somes (map (fun n => plan_of t1 icw icw_nc icw_sv (icw_pre n)) names).
Lemma icw_certificate :
  let plans := icw_plans in
  map fst plans = map icw_spec names /\ forallb (verified t1 icw icw_nc) plans = true.
Proof. vm_compute. split; reflexivity. Qed.

Lemma icw_checked : forallb (verified t1 icw icw_nc) icw_plans = true.
Proof. exact (proj2 icw_certificate). Qed.
Definition t2 : table := ("glibc_libc_start#intel_check_word", map icw_spec names) :: t1.

Lemma icw_counts : (length cmp_plans, length icw_plans) = (1, 12)%nat.
Proof.
  refine (f_equal (pair (length cmp_plans)) _).
  exact (eq_trans (eq_sym (length_map fst icw_plans))
    (eq_trans (f_equal (@length fspec) (proj1 icw_certificate)) (length_map icw_spec names))).
Qed.

Section sound.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ} (w0 : os_world) (ge : genv) {Hge : CpuImage ge}.
Hypothesis Hends : ow_leaf4_ends w0 = true.

Lemma t1_holds : table_holds w0 ge t1.
Proof using Hends Hge.
  apply table_cons; [|apply table_nil].
  exact (verified_holds w0 ge Hends [] _ cmp [] cmp_plans cmp_find (table_nil w0 ge) cmp_checked).
Qed.

(** The comparison and the descriptor lookup satisfy their
    specifications. *)
Lemma t2_holds : table_holds w0 ge t2.
Proof using Hends Hge.
  apply table_cons; [|apply t1_holds].
  rewrite <- (proj1 icw_certificate).
  exact (verified_holds w0 ge Hends t1 _ icw icw_nc icw_plans icw_find t1_holds icw_checked).
Qed.

End sound.
