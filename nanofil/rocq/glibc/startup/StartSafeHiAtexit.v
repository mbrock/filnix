(** This module states hi_atexit's safety theorem from the moment the
    runtime calls `c: __libc_start_main`, rather than from main. In
    every state that [StartState](../zsys/StartState.v) allows for the
    image, no run of hi_atexit panics, gets stuck or breaks a contract.
    Startup never returns to the runtime, so the theorem also says that
    no run returns normally.

    A start state leaves most things open, and the theorem covers all
    of them: any arguments, any environment, any auxiliary vector, and
    the constructors in any order. It assumes only that the process can
    write to standard output, that the processor reports its caches in
    the way glibc reads them, and that the allocator is ready. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia Permutation.
From Nanofil Require Import Term Syntax Values Memory Runtime Run Semantics Pieces Heap Language Logic HelloLeaf.
From Glibc Require Import GlibcTactics FileInv OsWorld OsRegistry OsStart OsCpuid StartCode StartCtors StartState
  StartOwn StartJoin StartLibcStartMain HiAtexitGe HiAtexitModule HiAtexitInitial StartImageEarly
  StartOwnHiAtexit StartWpHiAtexit.
From Glibc Require Fix.
Import ListNotations FileInv.ML FileInv.LG FileInv.L.
Open Scope Z_scope.

(** The adequacy construction uses only invariant and heap resources. *)
Definition hi_startΣ : gFunctors := #[invΣ; gen_heapΣ piece pval].

(** This resource universe supports Iris invariants. *)
#[local] Instance hi_start_inv : invGpreS hi_startΣ.
Proof. apply subG_invΣ. apply _. Qed.

(** Iris can record ownership of the start memory in this universe. *)
#[local] Instance hi_start_heap : gen_heapGpreS piece pval hi_startΣ.
Proof. apply subG_gen_heapGpreS. apply _. Qed.

(** The startup body takes its five arguments into a frame. *)
Lemma hi_start_frame a b c d e :
  exists fr, call_frame start_libc_start_main_fn [WPtr a; WInt b; WPtr c; WPtr d; WPtr e] = Some fr.
Proof. eexists. reflexivity. Qed.

(** Every run of hi_atexit from a state in which the runtime can start
    it avoids panics, stuck steps and contract failures, and never
    returns. *)
Theorem hi_atexit_never_panics w0 m s w xs fuel :
  start_state hi_module w0 m w xs ->
  In 1 (ow_fds w0) -> ow_leaf4_ends w0 = true -> Fix.R.ready s m ->
  labelled_safe glibc_os_registry hge (invocation start_libc_start_main_fn xs) m s w fuel (fun _ => False).
Proof.
  intros Hst Hfd Hleaf Hr. pose proof (hi_start_agree w0 m w xs Hst) as Hag.
  destruct Hst as (g & m0 & mainp & tb & argc & argv & env & av & ps & order & Hi & Hm & Ht & Hxs & Hargc & Hargc2 &
    Ha & He & Hv & Hd & Hk & Hord & Hct & Hos & Hnd).
  assert (Eg : g = hi_globals /\ m0 = hi_m0) by (rewrite hi_initial in Hi; split; congruence).
  destruct Eg as [-> ->]. clear Hi.
  assert (Etb : tb = hi_runner_objs.2.1).
  { assert (L : lookup ctor_table_name hi_globals = Some (mkPtr hi_runner_objs.2.1 (Ro hi_runner_objs.2.1)))
      by (vm_compute; reflexivity).
    rewrite L in Ht. injection Ht as E. symmetry. exact E. }
  subst tb.
  assert (Emain : mainp = mkPtr 65552 (Fn (TAtom "main"))).
  { assert (L : lookup (TAtom "main") hi_globals = Some (mkPtr 65552 (Fn (TAtom "main")))) by (vm_compute; reflexivity).
    rewrite L in Hm. injection Hm as E. symmetry. exact E. }
  subst mainp xs.
  destruct (hi_start_frame (mkPtr 65552 (Fn (TAtom "main"))) argc (mkPtr argv.1 (Obj argv.1)) (mkPtr env.1 (Obj env.1))
    (mkPtr av (Obj av))) as [fr Hfr].
  unfold invocation. rewrite Hfr.
  assert (Hlen : length order = length (ctor_names hi_module)) by exact (Permutation_length Hord).
  destruct (start_ps_ok hi_m0 m hi_globals w0 w hi_runner_objs.2.1 hi_runner_objs.2.2
    (ctor_table_size (length (ctor_names hi_module))) argc argv env av ps order hi_start_all_ps 0)
    as (Nd & Agr & Wi).
  - exact Hk.
  - exact hi_no_heap_regions.
  - split; [vm_compute; reflexivity | vm_compute; reflexivity].
  - vm_compute. discriminate.
  - rewrite Hlen. apply Z.leb_le. vm_cast_no_check (eq_refl true).
  - exact Ha.
  - exact He.
  - exact Hv.
  - exact Hnd.
  - exact Hct.
  - exact Hos.
  - exact hi_start_all_agree.
  - exact Hag.
  - exact hi_start_all_nodup.
  - exact hi_start_all_off.
  - exact (hi_start_key_apart 0).
  - destruct Hos as (Herr & _ & _).
    apply (heap_labelled_safe hi_startΣ glibc_os_registry (os_wi_start w0 0) hge fr m s w _ (fun _ => False)
      Hr Hd Agr Wi).
    intros HinvG HheapG. iIntros "H".
    iDestruct (start_ps_own with "H") as "(L & T & A & E & V & K)"; [exact Nd|].
    iApply (hi_start_wp w0 0 fr m argv env av ps order argc Hfd Hleaf Herr Hfr Ha He Hv Hargc Hargc2 Hord
      with "L T A E V K").
Qed.
