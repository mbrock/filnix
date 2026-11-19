(** This file states Hello's safety theorem from the point where the
    runtime calls into glibc, rather than from main. GNU Hello, linked
    with userland glibc, never panics, gets stuck or breaks a contract
    in any state that [StartState](../zsys/StartState.v) allows for its
    image. In those states the caller no longer describes main's memory,
    because the loader's image and the startup code supply it. Startup
    never returns to the runtime, so the theorem also says that no run
    returns normally.

    The theorem assumes that standard output and standard error are
    open. The environment must select the C locale, the processor must
    report its caches the way glibc expects, and the runtime must have
    a ready allocator. Printing and closing stdout use the code in the
    image; the caller need not supply contracts for these calls.

    The proof divides the start memory into the objects that each part
    of startup uses, as [HelloStartAssembly](HelloStartAssembly.v)
    lists them, and then runs the startup body and main with
    [HelloStartWp](HelloStartWp.v). *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia Permutation.
From stdpp Require Import list.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Run Pieces Heap Language Logic.
From Glibc Require Fix.
From Glibc Require Import IRFrames.
From Glibc Require Import LocaleEnv GlibcProgram GlibcLogic OsWorld OsRegistry OsStart OsCpuid FileInv
  HelloGlibcDebts StartState StartJoin StartLibcStartMain HelloImageModule HelloImageLoad
  HelloImageEarly HelloStartAssembly HelloStartFacts HelloStartWp.
Import ListNotations Fix.ML0 Fix.LG0 Fix.LG0.L.
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
    returns. Startup builds the library's private state from the
    environment array and the loaded image. *)
Theorem hello_never_panics w0 m s w xs fuel :
  start_state hello_image_module w0 m w xs ->
  In 1 (ow_fds w0) -> In 2 (ow_fds w0) -> start_c_locale m xs ->
  ow_leaf4_ends w0 = true ->
  R.ready s m ->
  labelled_safe glibc_os_registry hello_start_ge (invocation start_libc_start_main_fn xs)
    m s w fuel (fun _ => False).
Proof.
  intros Hst Hfd1 Hfd2 Hloc Hleaf Hr.
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
  apply (heap_labelled_safe glibcΣ glibc_os_registry (os_wi_start w0 0) hello_start_ge fr m s w _ (fun _ => False)
    Hr Hd Agr Wi).
  intros HinvG HheapG. iIntros "H".
  iDestruct (start_ps_own with "H") as "(L & T & A & E & V & K)"; [exact Nd|].
  iApply (hello_start_wp w0 0 m0 m Hi fr argv env av aps order argc Hleaf Hfd2 Hfd1 Herr Hfr Ha He (Hloc env.1 env.2 eq_refl He) Hv
    Hargc Hargc2 Hord with "L T A E V K").
Qed.
