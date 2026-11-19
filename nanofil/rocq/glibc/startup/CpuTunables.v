(** glibc keeps its tunables in a table of 136-byte rows.
    `c: init_cpu_features` reads nine rows and writes six of them
    back. The function that reads a row branches on the type code of
    the row, so the checker can follow it only when it knows the type
    code.

    The function `c: __tunables_init` would change the table. The
    linked image does not contain it, because nothing that startup
    reaches calls it. The table therefore still holds the bytes of the
    image when `c: init_cpu_features` runs. The specifications below
    assume less than that. They take any bytes for the table, except
    the type codes of the rows that startup reads and the cleared
    `initialized` flags of the rows that later startup code asks
    about. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Nanofil Require Import Pieces Heap.
From Stdlib Require Import String ZArith List Bool.
From Nanofil Require Import Term Syntax Values Memory Ops Semantics.
From Nanofil Require Import AbsRun AbsInfer.
From Glibc Require Import OsWorld OsCpuid HiAtexitModule CpuRules CpuSetup CpuPlans CpuSound.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.
Open Scope Z_scope.

(** * The table *)

Definition tl : string := "glibc_dl_tunables#tunable_list".
Definition le4 (z : Z) : list abyte := map (fun i => BK (byte_of z i)) [0; 1; 2; 3].

(** Later startup code reads the rows of [later]. Their type codes and
    their cleared `initialized` flags must survive the call. *)
Definition later0 : list Z := [18; 21; 27].
Definition later : list Z := [14; 15; 17; 18; 19; 21; 22; 23; 24; 25; 27].

(** The type code of a row is at offset 48 and its `initialized` flag
    is at offset 104. *)
Definition tun0 : aobj :=
  fold_left (fun ob it => with_bytes (fst it * 136 + 48) (le4 (snd it)) ob)
    ([(0, 3); (1, 0); (2, 0); (3, 2); (5, 2); (6, 2); (7, 2); (8, 2); (9, 2)]
     ++ map (fun i => (i, 2)) [14; 15; 17; 19; 22; 23; 24; 25] ++ map (fun i => (i, 0)) later0)
    (fold_left (fun ob i => with_bytes (i * 136 + 104) [BK 0] ob) ([0; 1; 2] ++ later) (weak 8 4896)).

(** * The four functions *)

Definition upd := Eval vm_compute in fn "glibc_dl_tunables#do_tunable_update_val".
Definition setv := Eval vm_compute in fn "__tunable_set_val".
Definition getv := Eval vm_compute in fn "__tunable_get_val".
Definition isin := Eval vm_compute in fn "__tunable_is_initialized".

Lemma upd_find : cpu_fn "glibc_dl_tunables#do_tunable_update_val" upd.
Proof. vm_compute. split; reflexivity. Qed.
Lemma setv_find : cpu_fn "__tunable_set_val" setv.
Proof. vm_compute. split; reflexivity. Qed.
Lemma getv_find : cpu_fn "__tunable_get_val" getv.
Proof. vm_compute. split; reflexivity. Qed.
Lemma isin_find : cpu_fn "__tunable_is_initialized" isin.
Proof. vm_compute. split; reflexivity. Qed.

(** Startup writes the six rows of [ids_set]. *)
Definition ids_set : list Z := [3; 5; 6; 7; 8; 9].
Definition upd_pre (id : Z) := spec [CP 1 (id * 136) (id * 136); par 1; par 2; par 3] [(tl, tun0)]
  [None; Some (loc 16); Some (loc 16); Some (loc 16)].
Definition upd_plans := somes (map (fun id => plan_of [] upd [] [] (upd_pre id)) ids_set).
Definition upd_specs : list fspec :=
  map (fun id => let sp := upd_pre id in
    cpu_result sp (post_global sp tl (with_bytes (id * 136 + 105) [BIn 0 255] tun0)) None) ids_set.
Lemma upd_certificate : certifies [] upd [] upd_plans upd_specs.
Proof. vm_compute. split; reflexivity. Qed.
Lemma upd_checked : forallb (verified [] upd []) upd_plans = true.
Proof. exact (proj2 upd_certificate). Qed.
Definition u1 : table := [("glibc_dl_tunables#do_tunable_update_val", upd_specs)].

Definition set_pre (id : Z) := spec [CI id id; par 1; par 2; par 3] [(tl, tun0)]
  [None; Some (loc 16); Some (loc 16); Some (loc 16)].
Definition set_plans := somes (map (fun id => plan_of u1 setv [] [] (set_pre id)) ids_set).
Definition set_specs : list fspec :=
  map (fun id => let sp := set_pre id in
    cpu_result sp (post_global sp tl (with_bytes (id * 136 + 105) [BIn 0 255] tun0)) None) ids_set.
Lemma set_certificate : certifies u1 setv [] set_plans set_specs.
Proof. vm_compute. split; reflexivity. Qed.
Lemma set_checked : forallb (verified u1 setv []) set_plans = true.
Proof. exact (proj2 set_certificate). Qed.

(** Startup reads nine rows. The first three pass a callback, and the
    others pass a null callback. *)
Definition get_pre (id : Z) (cb : cval) := spec [CI id id; par 1; cb] [(tl, tun0)] [None; Some (loc 16); None].
Definition gets : list (Z * cval) :=
  [(0, CA); (1, CA); (2, CA); (3, CN 0 0); (5, CN 0 0); (6, CN 0 0); (7, CN 0 0); (8, CN 0 0); (9, CN 0 0)].
Definition get_plans := Eval vm_compute in
  somes (map (fun ic => plan_of [] getv [] [] (get_pre (fst ic) (snd ic))) gets).
Lemma get_checked : forallb (verified [] getv []) get_plans = true.
Proof. vm_compute. reflexivity. Qed.

Definition isin_plans := Eval vm_compute in somes [plan_of [] isin [] [] (spec [CI 8 8] [(tl, tun0)] [None])].
Lemma isin_checked : forallb (verified [] isin []) isin_plans = true.
Proof. vm_compute. reflexivity. Qed.

Definition tun_table : table :=
  [("__tunable_set_val", set_specs); ("__tunable_get_val", map fst get_plans);
   ("__tunable_is_initialized", map fst isin_plans)].

Lemma tun_counts :
  (length upd_plans, length set_plans, length get_plans, length isin_plans) = (6, 6, 9, 1)%nat.
Proof.
  exact (f_equal2 pair (f_equal2 pair (f_equal2 pair (certified_count upd_certificate)
    (certified_count set_certificate)) eq_refl) eq_refl).
Qed.

Section sound.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ} (w0 : os_world) (ge : genv) {Hge : CpuImage ge}.
Hypothesis Hends : ow_leaf4_ends w0 = true.

Lemma u1_holds : table_holds w0 ge u1.
Proof using Hends Hge.
  apply table_cons; [|apply table_nil].
  exact (certified_holds w0 ge Hends upd_find (table_nil w0 ge) upd_certificate).
Qed.

(** The three tunable functions that `c: init_cpu_features` calls
    satisfy their specifications. *)
Lemma tun_table_holds : table_holds w0 ge tun_table.
Proof using Hends Hge.
  apply table_cons; [exact (certified_holds w0 ge Hends setv_find u1_holds set_certificate)|].
  apply table_cons; [exact (verified_holds w0 ge Hends [] _ getv [] get_plans getv_find (table_nil w0 ge) get_checked)|].
  apply table_cons; [|apply table_nil].
  exact (verified_holds w0 ge Hends [] _ isin [] isin_plans isin_find (table_nil w0 ge) isin_checked).
Qed.

End sound.
