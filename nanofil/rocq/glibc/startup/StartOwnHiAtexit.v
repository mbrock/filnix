(** We want to prove that hi_atexit never panics from the moment the
    runtime calls `c: __libc_start_main`, in every state that
    [StartState](../zsys/StartState.v) allows. The proof of the startup
    body takes the memory that startup reads and writes as separate
    resources, and earlier modules list that memory as eight lists of
    pieces of the loader's image. This module shows that every start
    state holds all eight lists, and turns them into owned resources.

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
  HiAtexitStartBridge StartImageDisjoint StartImageUnique StartLsmImage.
Import ListNotations.
Open Scope Z_scope.

(** ## The globals of the startup body

    The body of `c: __libc_start_main` itself reads and writes five
    globals that no startup call owns: the pointer to the auxiliary
    vector, the secure-mode flag, the debug mask, the flag that asks for
    thread events and the saved stack end. This list holds each one's
    life and its bytes as the image leaves them. *)

(** This list gives each of the five globals its region and its bytes
    in the image. Only `c: __libc_enable_secure` starts nonzero. *)
Definition hi_lsm_ps : list (piece * pval) :=
  obj_ps (lo_dx hi_lsm_objs, lo_dxreg hi_lsm_objs) (repeat 0 8%nat) ++
  obj_ps (lo_es hi_lsm_objs, lo_esreg hi_lsm_objs) [1; 0; 0; 0] ++
  obj_ps (lo_dm hi_lsm_objs, lo_dmreg hi_lsm_objs) (repeat 0 4%nat) ++
  obj_ps (lo_re hi_lsm_objs, lo_rereg hi_lsm_objs) [0] ++
  obj_ps (lo_se hi_lsm_objs, lo_sereg hi_lsm_objs) (repeat 0 8%nat).

(** The loader's image holds those five globals with those bytes. *)
Lemma hi_lsm_agree : all_agree hi_m0 hi_lsm_ps.
Proof. apply hi_m0_pieces. vm_cast_no_check (eq_refl true). Qed.

(** ## The eight lists in every start state

    The lists are the CPU globals, the memory of early init and of the
    constructor runner, the inputs of the three constructors, the
    frame that startup hands to main unchanged, and the globals of the
    startup body. The loader's image
    holds all of them, and none is a byte of the constructor table. *)

(** These are all the pieces that hi_atexit's startup owns or hands to
    main unchanged. *)
Definition hi_start_all_ps : list (piece * pval) :=
  hi_cpu_globals_ps ++ hi_early_ps ++ hi_runner_ps ++ hi_initial_list_ps ++ hi_init_first_ps ++
  hi_vtables_ps ++ hi_start_kept_ps ++ hi_lsm_ps.

(** No object and no byte occurs twice in the eight lists. *)
Lemma hi_start_all_nodup : NoDup hi_start_all_ps.*1.
Proof. apply pieces_unique_sound. vm_cast_no_check (eq_refl true). Qed.

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
  apply (proj2 (all_agree_app _ hi_start_kept_ps _)). split; [exact hi_start_kept_agree|].
  exact hi_lsm_agree.
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
    eight lists. *)
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

(** ## Owning the eight lists

    Each startup call needs to own the memory it touches, apart from
    what the other calls touch. The whole run starts by owning every
    piece of the start memory, and since no piece appears twice, that
    ownership splits into the eight lists, one separate
    [[separation-logic]] resource each. *)

Section own.
Context `{!gen_heapGS piece pval Σ}.

(** The heap of all eight lists is the eight lists' points-to
    assertions side by side. *)
Lemma hi_start_own :
  ([∗ map] l ↦ v ∈ list_to_map hi_start_all_ps, pointsto l (DfracOwn 1) v) ⊣⊢
  pts hi_cpu_globals_ps ∗ pts hi_early_ps ∗ pts hi_runner_ps ∗ pts hi_initial_list_ps ∗
  pts hi_init_first_ps ∗ pts hi_vtables_ps ∗ pts hi_start_kept_ps ∗ pts hi_lsm_ps.
Proof using Type.
  etrans; [exact (pts_map hi_start_all_ps hi_start_all_nodup)|].
  unfold hi_start_all_ps.
  rewrite (pts_app hi_cpu_globals_ps) (pts_app hi_early_ps) (pts_app hi_runner_ps)
    (pts_app hi_initial_list_ps) (pts_app hi_init_first_ps) (pts_app hi_vtables_ps)
    (pts_app hi_start_kept_ps).
  done.
Qed.

End own.

(** ## The image has no heap objects

    The runtime's own objects, argv, environ and the auxiliary vector,
    are heap objects. The image of hi_atexit has none, so the runtime's
    objects never share a piece with the eight lists. *)

(** No region of hi_atexit's initial memory is a heap region. *)
Lemma hi_no_heap_regions : no_heap_regions hi_m0.
Proof.
  assert (C : forallb (fun r => match r_kind r with Heap => false | _ => true end) (m_regions hi_m0) = true)
    by (vm_cast_no_check (eq_refl true)).
  apply List.Forall_forall. intros r Hr E. rewrite forallb_forall in C. specialize (C r Hr).
  rewrite E in C. discriminate.
Qed.

(** The run must own the image's memory and the startup key at once,
    so they must not collide. They cannot, because the image's lists
    hold only memory, and the key is not memory. *)
Lemma hi_start_key_apart k : forall l, l ∈ (start_key_ps k).*1 -> l ∉ hi_start_all_ps.*1.
Proof.
  assert (C : forallb (fun lv => match lv.1 with PName _ => false | _ => true end) hi_start_all_ps = true)
    by (vm_cast_no_check (eq_refl true)).
  intros l Hl Hin. cbn in Hl. apply list_elem_of_singleton in Hl as ->.
  apply list_elem_of_fmap in Hin as ([l v] & E & Hin). cbn in E. subst l.
  rewrite forallb_forall in C. specialize (C _ (proj1 (list_elem_of_In _ _) Hin)). discriminate C.
Qed.
