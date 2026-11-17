(** We want to prove that hi_atexit never panics from the moment the
    runtime calls `c: __libc_start_main`, in every state that
    [StartState](../zsys/StartState.v) allows. The proof of the startup
    body takes the memory that startup reads and writes as separate
    resources, and earlier modules list that memory as seven lists of
    pieces of the loader's image. This module shows that every start
    state holds all seven lists, and turns them into owned resources.

    A start state keeps every object of the loader's image, except that
    it fills in the constructor table. The step from a kept image to
    agreeing pieces is the same for every program, and
    [StartOwn](StartOwn.v) proves it once. Hello's version of this
    module is [HelloStartAssembly](../hello/HelloStartAssembly.v). *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From Stdlib Require Import String ZArith List Bool Lia.
From stdpp Require Import list fin_maps.
From Nanofil Require Import Term Syntax Values Memory Run Runtime Semantics Pieces Heap.
From Glibc Require Import OsWorld StartCtors StartState StartOwn HiAtexitModule HiAtexitInitial
  HiAtexitInitialList StartInitFirstImage StartImageCpu StartVtablesImage StartImageEarly
  HiAtexitStartBridge StartImageDisjoint.
Import ListNotations.
Open Scope Z_scope.

(** ## The seven lists in every start state

    The lists are the CPU globals, the memory of early init and of the
    constructor runner, the inputs of the three constructors, and the
    frame that startup hands to main unchanged. The loader's image
    holds all of them, and none is a byte of the constructor table. *)

(** These are all the pieces that hi_atexit's startup owns or hands to
    main unchanged. *)
Definition hi_start_all_ps : list (piece * pval) :=
  hi_cpu_globals_ps ++ hi_early_ps ++ hi_runner_ps ++ hi_initial_list_ps ++ hi_init_first_ps ++
  hi_vtables_ps ++ hi_start_kept_ps.

(** The loader's image holds every one of those pieces. Each step names
    its left list, because rewriting the whole sum at once is slow. *)
Lemma hi_start_all_agree : all_agree hi_m0 hi_start_all_ps.
Proof.
  unfold hi_start_all_ps.
  apply (proj2 (all_agree_app _ hi_cpu_globals_ps _)). split; [exact hi_cpu_globals_agree|].
  apply (proj2 (all_agree_app _ hi_early_ps _)). split; [exact hi_early_agree|].
  apply (proj2 (all_agree_app _ hi_runner_ps _)). split; [exact hi_runner_agree|].
  apply (proj2 (all_agree_app _ hi_initial_list_ps _)). split; [exact hi_initial_list_agree|].
  apply (proj2 (all_agree_app _ hi_init_first_ps _)). split; [exact hi_init_first_agree|].
  apply (proj2 (all_agree_app _ hi_vtables_ps _)). split; [exact hi_vtables_agree|].
  exact hi_start_kept_agree.
Qed.

(** This test says that a piece is no byte or capability slot of the
    object at tb. *)
Definition hi_piece_offb (tb : Z) (l : piece) : bool :=
  match l with PByte b _ | PAux b _ => negb (b =? tb) | _ => true end.

(** The start state rewrites the constructor table, so a piece that sat
    inside the table could change. None of these pieces does: the
    runner's list holds only the table's life, which stays the same. *)
Lemma hi_start_all_off : Forall (fun lv => piece_off hi_runner_objs.2.1 lv.1) hi_start_all_ps.
Proof.
  assert (C : forallb (fun lv => hi_piece_offb hi_runner_objs.2.1 lv.1) hi_start_all_ps = true)
    by (vm_cast_no_check (eq_refl true)).
  apply List.Forall_forall. intros [l v] Hin. rewrite forallb_forall in C. specialize (C _ Hin).
  destruct l as [b|b o|b o|k]; cbn in C |- *; try exact I;
    apply negb_true_iff, Z.eqb_neq in C; exact C.
Qed.

(** Every state in which the runtime can start hi_atexit holds all
    seven lists. *)
Theorem hi_start_agree w0 m w xs :
  start_state hi_module w0 m w xs -> all_agree m hi_start_all_ps.
Proof.
  intros (g & m0 & mainp & tb & argc & argv & env & av & ps & order & Hi & _ & Ht & _ & _ & _ & _ & _ & _ &
    Hd & Hk & _).
  assert (Eg : g = hi_globals /\ m0 = hi_m0) by (rewrite hi_initial in Hi; split; congruence).
  destruct Eg as [-> ->]. clear Hi.
  assert (Etb : tb = hi_runner_objs.2.1).
  { assert (L : lookup ctor_table_name hi_globals = Some (mkPtr hi_runner_objs.2.1 (Ro hi_runner_objs.2.1)))
      by (vm_compute; reflexivity).
    rewrite L in Ht. injection Ht as E. symmetry. exact E. }
  subst tb.
  apply (keeps_image_agree hi_m0 m _ _ hi_runner_objs.2.2 _ Hk Hd).
  - split; [vm_compute; reflexivity | vm_compute; reflexivity].
  - apply Z.leb_le. vm_cast_no_check (eq_refl true).
  - exact hi_start_all_agree.
  - exact hi_start_all_off.
Qed.

(** ## Owning the seven lists

    Each startup call needs to own the memory it touches, apart from
    what the other calls touch. The whole run starts by owning every
    piece of the start memory, and since no piece appears twice, that
    ownership splits into the seven lists, one separate
    [[separation-logic]] resource each. *)

Section own.
Context `{!gen_heapGS piece pval Σ}.

(** The heap of all seven lists is the seven lists' points-to
    assertions side by side. *)
Lemma hi_start_own :
  ([∗ map] l ↦ v ∈ list_to_map hi_start_all_ps, pointsto l (DfracOwn 1) v) ⊣⊢
  pts hi_cpu_globals_ps ∗ pts hi_early_ps ∗ pts hi_runner_ps ∗ pts hi_initial_list_ps ∗
  pts hi_init_first_ps ∗ pts hi_vtables_ps ∗ pts hi_start_kept_ps.
Proof using Type.
  etrans; [exact (pts_map hi_start_all_ps hi_start_nodup)|].
  unfold hi_start_all_ps.
  rewrite (pts_app hi_cpu_globals_ps) (pts_app hi_early_ps) (pts_app hi_runner_ps)
    (pts_app hi_initial_list_ps) (pts_app hi_init_first_ps) (pts_app hi_vtables_ps).
  done.
Qed.

End own.
