(** This file states Hello's safety theorem from the point where the
    runtime calls into glibc, rather than from main. GNU Hello, linked
    with userland glibc, never panics, gets stuck or breaks a contract
    in any state that [StartState](../zsys/StartState.v) allows for its
    image. In those states the caller no longer describes main's memory,
    because the loader's image and the startup code supply it. Startup
    never returns to the runtime, so the theorem also says that no run
    returns normally.

    Some parts of the proof are still missing, so the theorem assumes
    them. A few assumptions describe the machine that runs Hello. Its
    standard output and standard error are open, its environment asks
    for the C locale, and its processor reports caches the way glibc
    expects. Its runtime also has a ready allocator.

    The rest are promises about glibc calls that nobody has proved yet.
    They cover setting the locale, printing and closing standard output.
    A script in nanofil/tests lists these assumptions, says which ones
    can hold, and counts them for CI.

    The proof divides the start memory into the objects that each part
    of startup uses, as [HelloStartAssembly](HelloStartAssembly.v)
    lists them, and then runs the startup body and main with
    [HelloStartWp](HelloStartWp.v). *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia Permutation.
From stdpp Require Import list.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Run Pieces Heap Language Logic HelloLeaf.
From Glibc Require Import LocaleEnv GlibcProgram OsWorld OsRegistry OsStart OsCpuid FileInv GetoptDiag GetoptLongDiag
  HelloGlibcDebts StartCode StartState StartJoin StartLibcStartMain HelloImageModule HelloImageLoad HelloImageLayout
  HelloImageEarly HelloStartAssembly HelloStartFacts HelloStartWp.
Import ListNotations FileInv.ML FileInv.LG FileInv.L.
Open Scope Z_scope.

(** This is the linked Hello program. It frees memory with the
    runtime's own `c: free`, which every runtime promises frees heap
    objects ([R.free_succeeds]). *)
Definition hello_start_ge : genv := mkGenv hello_image_module img_globals R.free.

(** The startup body takes its five arguments into a frame. *)
Lemma hello_start_frame a b c d e :
  exists fr, call_frame start_libc_start_main_fn [WPtr a; WInt b; WPtr c; WPtr d; WPtr e] = Some fr.
Proof. eexists. reflexivity. Qed.

(** ## The theorem *)

(** Every run of Hello from a state in which the runtime can start it
    avoids panics, stuck steps and contract failures, and it never
    returns. The last premise gives the open contracts. For each ghost
    state, it chooses the library calls of [HelloCore]. For every
    environment array and thread object, it gives the contracts that
    [hello_tb_contracts] states: the private state's shape. *)
Theorem hello_never_panics Σ {HinvP : invGpreS Σ} {HheapP : gen_heapGpreS piece pval Σ}
    w0 m s w xs fuel :
  start_state hello_image_module w0 m w xs ->
  In 1 (ow_fds w0) -> In 2 (ow_fds w0) -> start_c_locale m xs ->
  ow_leaf4_ends w0 = true ->
  R.ready s m ->
  (forall (HinvG : invGS_gen HasNoLc Σ) (HheapG : gen_heapGS piece pval Σ),
    exists (debt : forall tb, HelloCore (final_world w0 tb) hello_start_ge hello_image_objs),
    forall b ss, nth_error xs 3 = Some (WPtr (mkPtr b (Obj b))) -> string_array m b ss ->
    forall tb, 0 < tb -> tb + 2496 <= 2 ^ 48 -> hello_tb_contracts w0 m R.free debt (b, ss) tb) ->
  labelled_safe glibc_os_registry hello_start_ge (invocation start_libc_start_main_fn xs)
    m s w fuel (fun _ => False).
Proof.
  intros Hst Hfd1 Hfd2 _ Hleaf Hr Hc.
  destruct Hst as (g & m0 & mainp & tb & argc & argv & env & av & aps & order & Hi & Hm & Ht & Hxs & Hargc & Hargc2 &
    Ha & He & Hv & Hd & Hk & Hord & Hct & Hos & Hnd).
  destruct (hello_first_heap g m0 m w0 w tb argc argv env av aps order 0 Hi Ht Ha He Hv Hd Hk Hord Hct Hos Hnd)
    as (Nd & Agr & Wi).
  destruct (hello_loaded_tables g m0 Hi) as [-> _].
  assert (Etb : tb = hello_runner_objs.2.1) by (vm_compute in Ht; injection Ht as E _; symmetry; exact E).
  subst tb. rewrite hello_main_sym in Hm. injection Hm as <-. subst xs.
  destruct (hello_start_frame (mkPtr (img_a "main") (Fn (TAtom "main"))) argc (mkPtr argv.1 (Obj argv.1))
    (mkPtr env.1 (Obj env.1)) (mkPtr av (Obj av))) as [fr Hfr].
  unfold invocation. rewrite Hfr. destruct Hos as (Herr & _ & _).
  apply (heap_labelled_safe Σ glibc_os_registry (os_wi_start w0 0) hello_start_ge fr m s w _ (fun _ => False)
    Hr Hd Agr Wi).
  intros HinvG HheapG. destruct (Hc HinvG HheapG) as [debt Hdebt]. iIntros "H".
  iDestruct (start_ps_own with "H") as "(L & T & A & E & V & K)"; [exact Nd|].
  iApply (hello_start_wp w0 0 m0 m R.free Hi debt fr argv env av aps order argc Hleaf eq_refl Hfd2 Hfd1 Herr Hfr Ha He Hv
    Hargc Hargc2 Hord with "L T A E V K").
  intros tb Htb Htb2. destruct env as [b ss]. exact (Hdebt b ss eq_refl He tb Htb Htb2).
Qed.
