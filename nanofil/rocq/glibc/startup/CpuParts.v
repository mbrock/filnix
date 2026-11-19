(** `c: init_cpu_features` does most of its work in four helper
    functions. One asks the processor for its family, its model and
    its feature bits. One reads the feature bits back. One decides
    which features a program may use. One computes the cache sizes and
    the thresholds of the string functions.

    The last two divide and shift by numbers that the processor and
    the tunables supply, so a bad number could make them trap. This
    module runs the checker on all four helpers. Every run passes, so
    no answer of the processor makes a helper trap. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Bool.
From Nanofil Require Import Term Syntax Values Memory Ops Semantics Pieces Heap.
From Nanofil Require Import AbsRun AbsInfer.
From Glibc Require Import OsWorld OsCpuid HiAtexitModule CpuRules CpuSetup CpuPlans CpuSound
  CpuTunables CpuIntelWord CpuVendors CpuCache.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.
Open Scope Z_scope.

(** The table [t4] collects the specifications of every function that
    the four helpers call. *)
Definition t4 : table := gcc_table ++ t3 ++ tun_table.

Definition isa := Eval vm_compute in fn "glibc_libc_start#get_isa_level".
Definition gci := Eval vm_compute in fn "glibc_libc_start#get_common_indices".
Definition upa := Eval vm_compute in fn "glibc_libc_start#update_active".
Definition dic := Eval vm_compute in fn "glibc_libc_start#dl_init_cacheinfo".

Lemma isa_find : cpu_fn "glibc_libc_start#get_isa_level" isa.
Proof. vm_compute. split; reflexivity. Qed.
Lemma gci_find : cpu_fn "glibc_libc_start#get_common_indices" gci.
Proof. vm_compute. split; reflexivity. Qed.
Lemma upa_find : cpu_fn "glibc_libc_start#update_active" upa.
Proof. vm_compute. split; reflexivity. Qed.
Lemma dic_find : cpu_fn "glibc_libc_start#dl_init_cacheinfo" dic.
Proof. vm_compute. split; reflexivity. Qed.

(** The fifteen small globals that startup writes may hold anything. *)
Definition small : list (string * aobj) :=
  map (fun g => (g, weak 8 8)) ["_dl_hwcap"; "_dl_hwcap2"; "_dl_platform"; "_dl_minsigstacksize"; "_dl_x86_features_tlsdesc_state_size";
   "__x86_data_cache_size_half"; "__x86_data_cache_size"; "__x86_shared_cache_size_half"; "__x86_shared_cache_size";
   "__x86_shared_non_temporal_threshold"; "__x86_memset_non_temporal_threshold"; "__x86_rep_movsb_threshold";
   "__x86_rep_stosb_threshold"; "__x86_rep_movsb_stop_threshold"] ++ [("__x86_string_control", weak 4 4)].

(** `c: init_cpu_features` starts from this memory. It holds the
    feature structure, the tunable table, the descriptor table and the
    small globals. *)
Definition gall : list (string * aobj) := [(cpu, cpu0); (tl, tun0); (kn, known)] ++ small.

Definition isa_plans := Eval vm_compute in somes [plan_of [] isa [] [] (spec [glo cpu] [(cpu, cpu0)] [None])].
Lemma isa_checked : forallb (verified [] isa []) isa_plans = true.
Proof. vm_compute. reflexivity. Qed.

(** `c: get_common_indices` is called once with four result pointers
    and once with four null pointers. *)
Definition gci_a := spec [glo cpu; par 1; par 2; par 3; par 4] gall [None; Some (loc 16); Some (loc 16); Some (loc 16); Some (loc 16)].
Definition gci_b := spec [glo cpu; CN 0 0; CN 0 0; CN 0 0; CN 0 0] gall [None; None; None; None; None].
Definition gci_plans := Eval vm_compute in somes [plan_of [] gci [] [] gci_a; plan_of [] gci [] [] gci_b].
Lemma gci_checked : forallb (verified [] gci []) gci_plans = true.
Proof. vm_compute. reflexivity. Qed.

Definition t5 : table :=
  [("glibc_libc_start#get_isa_level", map fst isa_plans); ("glibc_libc_start#get_common_indices", map fst gci_plans)] ++ t4.

Definition upa_plans := somes [plan_of t5 upa [] [] (spec [glo cpu] gall [None])].
(** update_active bounds the ISA level byte in the feature structure. *)
Definition upa_specs : list fspec :=
  let sp := spec [glo cpu] gall [None] in
  [cpu_result sp (post_global sp cpu (with_bytes 344 [BIn 0 15] cpu0)) None].
Lemma upa_certificate : certifies t5 upa [] upa_plans upa_specs.
Proof. vm_compute. split; reflexivity. Qed.
Lemma upa_checked : forallb (verified t5 upa []) upa_plans = true.
Proof. exact (proj2 upa_certificate). Qed.

Definition dic_plans := somes [plan_of t5 dic [] [] (spec [glo cpu] gall [None])].
(** Cache initialization records a byte in row seven of the tunable table. *)
Definition dic_specs : list fspec :=
  let sp := spec [glo cpu] gall [None] in
  [cpu_result sp (post_global sp tl (with_bytes (7 * 136 + 105) [BIn 0 255] tun0)) None].
Lemma dic_certificate : certifies t5 dic [] dic_plans dic_specs.
Proof. vm_compute. split; reflexivity. Qed.
Lemma dic_checked : forallb (verified t5 dic []) dic_plans = true.
Proof. exact (proj2 dic_certificate). Qed.

Definition t6 : table :=
  [("glibc_libc_start#update_active", upa_specs); ("glibc_libc_start#dl_init_cacheinfo", dic_specs)] ++ t5.

Lemma parts_counts :
  (length isa_plans, length gci_plans, length upa_plans, length dic_plans) = (1, 2, 1, 1)%nat.
Proof.
  exact (f_equal2 pair
    (f_equal2 pair eq_refl (certified_count upa_certificate)) (certified_count dic_certificate)).
Qed.

Section sound.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ} (w0 : os_world) (ge : genv) {Hge : CpuImage ge}.
Hypothesis Hends : ow_leaf4_ends w0 = true.

Lemma t4_holds : table_holds w0 ge t4.
Proof using Hends Hge.
  apply table_app; [exact (gcc_table_holds w0 ge Hends)|].
  apply table_app; [exact (t3_holds w0 ge Hends) | exact (tun_table_holds w0 ge Hends)].
Qed.

Lemma t5_holds : table_holds w0 ge t5.
Proof using Hends Hge.
  apply table_cons; [exact (verified_holds w0 ge Hends [] _ isa [] isa_plans isa_find (table_nil w0 ge) isa_checked)|].
  apply table_cons; [|exact t4_holds].
  exact (verified_holds w0 ge Hends [] _ gci [] gci_plans gci_find (table_nil w0 ge) gci_checked).
Qed.

(** The four helpers and everything below them satisfy their
    specifications. *)
Lemma t6_holds : table_holds w0 ge t6.
Proof using Hends Hge.
  apply table_cons; [exact (certified_holds w0 ge Hends upa_find t5_holds upa_certificate)|].
  apply table_cons; [|exact t5_holds].
  exact (certified_holds w0 ge Hends dic_find t5_holds dic_certificate).
Qed.

End sound.
