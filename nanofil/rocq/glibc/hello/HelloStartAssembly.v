(** We want to prove that GNU Hello never panics from the moment the
    runtime calls `c: __libc_start_main`, in every state that
    [StartState](../zsys/StartState.v) allows. The proof of the startup
    body in [StartLibcStartMain](../startup/StartLibcStartMain.v) takes
    the memory that startup reads and writes as separate resources, and
    earlier modules list that memory for Hello as six lists of pieces
    of the loader's image. This module shows that every start state
    holds all six lists, and turns them into owned resources.

    A start state keeps every object of the loader's image, except that
    it fills in the constructor table. The step from a kept image to
    agreeing pieces is the same for every program, and
    [StartOwn](../startup/StartOwn.v) proves it once. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From Stdlib Require Import String ZArith List Bool Lia.
From stdpp Require Import list fin_maps.
From Nanofil Require Import Term Syntax Values Memory Run Runtime Semantics Pieces Heap.
From Glibc Require Import OsWorld OsStart StartCtors StartState StartOwn HelloImageModule HelloImageLoad HelloImageCtors
  HelloImageCpu HelloImageEarly HelloStartKept HelloImageDisjoint HelloImageLsm StartImageUnique.
Import ListNotations.
Open Scope Z_scope.

(** ## The six lists in every start state

    The lists are the CPU globals, the memory of early init and of the
    constructor runner, the inputs of the constructors, the frame that
    startup hands to main unchanged, and the globals of the startup
    body. The loader's image holds all
    of them, and none is a byte of the constructor table. *)

(** These are all the pieces that Hello's startup owns or hands to main
    unchanged. *)
Definition hello_start_all_ps : list (piece * pval) :=
  hello_cpu_globals_ps ++ hello_early_ps ++ hello_runner_ps ++ hello_ctor_ps ++ hello_start_kept_ps ++
  hello_lsm_ps.

(** No object and no byte occurs twice in the six lists. *)
Lemma hello_start_all_nodup : NoDup hello_start_all_ps.*1.
Proof. apply pieces_unique_sound. vm_cast_no_check (eq_refl true). Qed.

(** The loader's image holds every one of those pieces. *)
Lemma hello_start_all_agree g m0 : initial_memory hello_image_module = Some (g, m0) ->
  all_agree m0 hello_start_all_ps.
Proof.
  intros Hi. unfold hello_start_all_ps.
  apply (proj2 (all_agree_app _ _ _)). split; [exact (hello_cpu_globals_agree g m0 Hi)|].
  apply (proj2 (all_agree_app _ _ _)). split; [exact (hello_early_agree g m0 Hi)|].
  apply (proj2 (all_agree_app _ _ _)). split; [exact (hello_runner_agree g m0 Hi)|].
  apply (proj2 (all_agree_app _ _ _)). split; [exact (proj1 (proj2 (hello_image_ctors g m0 Hi)))|].
  apply (proj2 (all_agree_app _ _ _)). split; [exact (hello_start_kept_agree g m0 Hi)|].
  exact (hello_lsm_agree g m0 Hi).
Qed.

(** This test says that a piece is no byte or capability slot of the
    object at tb. *)
Definition piece_offb (tb : Z) (l : piece) : bool :=
  match l with PByte b _ | PAux b _ => negb (b =? tb) | _ => true end.

(** No piece is a byte or capability slot of Hello's constructor table.
    The runner's list holds the table's life, which the start state
    keeps. *)
Lemma hello_start_all_off : Forall (fun lv => piece_off hello_runner_objs.2.1 lv.1) hello_start_all_ps.
Proof.
  assert (C : forallb (fun lv => piece_offb hello_runner_objs.2.1 lv.1) hello_start_all_ps = true)
    by (vm_cast_no_check (eq_refl true)).
  apply List.Forall_forall. intros [l v] Hin. rewrite forallb_forall in C. specialize (C _ Hin).
  destruct l as [b|b o|b o|k]; cbn in C |- *; try exact I;
    apply negb_true_iff, Z.eqb_neq in C; exact C.
Qed.

(** Hello's image has this many constructors, and the number fixes the
    size of its table. *)
Definition hello_ctor_count : nat := Eval vm_compute in length (ctor_names hello_image_module).

Lemma hello_ctor_count_eq : length (ctor_names hello_image_module) = hello_ctor_count.
Proof. vm_compute. reflexivity. Qed.

(** Every state in which the runtime can start Hello holds all six
    lists. *)
Theorem hello_start_agree w0 m w xs :
  start_state hello_image_module w0 m w xs -> all_agree m hello_start_all_ps.
Proof.
  intros (g & m0 & mainp & tb & argc & argv & env & av & ps & order & Hi & _ & Ht & _ & _ & _ & _ & _ & _ &
    Hd & Hk & _).
  destruct (hello_loaded_tables g m0 Hi) as [-> Hr].
  assert (Etb : tb = hello_runner_objs.2.1).
  { vm_compute in Ht. injection Ht as E _. symmetry. exact E. }
  subst tb. rewrite hello_ctor_count_eq in Hk.
  apply (keeps_image_agree m0 m _ _ hello_runner_objs.2.2 _ Hk Hd).
  - unfold live_at. rewrite Hr. split; vm_compute; reflexivity.
  - apply Z.leb_le. vm_compute. reflexivity.
  - exact (hello_start_all_agree _ _ Hi).
  - exact hello_start_all_off.
Qed.

(** The loader registers no heap object for Hello, so the objects that
    the runtime allocates for the arguments and the auxiliary vector are
    none of the image's objects. *)
Lemma hello_no_heap_regions g m0 : initial_memory hello_image_module = Some (g, m0) ->
  no_heap_regions m0.
Proof.
  intros Hi. unfold no_heap_regions. destruct (hello_loaded_tables g m0 Hi) as [_ ->].
  assert (C : forallb (fun r => match r_kind r with Heap => false | _ => true end) img_regions = true)
    by (vm_compute; reflexivity).
  apply List.Forall_forall. intros r Hr. rewrite forallb_forall in C. specialize (C r Hr).
  destruct (r_kind r); congruence.
Qed.

(** The run must own the image's memory and the startup key at once,
    so they must not collide. They cannot, because Hello's lists hold
    only memory, and the key is not memory. *)
Lemma hello_start_key_apart k : forall l, l ∈ (start_key_ps k).*1 -> l ∉ hello_start_all_ps.*1.
Proof.
  assert (C : forallb (fun lv => match lv.1 with PName _ => false | _ => true end) hello_start_all_ps = true)
    by (vm_cast_no_check (eq_refl true)).
  intros l Hl Hin. cbn in Hl. apply list_elem_of_singleton in Hl as ->.
  apply list_elem_of_fmap in Hin as ([l v] & E & Hin). cbn in E. subst l.
  rewrite forallb_forall in C. specialize (C _ (proj1 (list_elem_of_In _ _) Hin)). discriminate C.
Qed.

(** ## Owning the six lists

    The proof of a whole run begins from a heap whose points-to
    assertions are the start memory's pieces. Since no piece appears
    twice, that heap splits into the six lists, one separate
    [[separation-logic]] resource each. *)

Section own.
Context `{!gen_heapGS piece pval Σ}.

Lemma hello_start_own :
  ([∗ map] l ↦ v ∈ list_to_map hello_start_all_ps, pointsto l (DfracOwn 1) v) ⊣⊢
  pts hello_cpu_globals_ps ∗ pts hello_early_ps ∗ pts hello_runner_ps ∗ pts hello_ctor_ps ∗
  pts hello_start_kept_ps ∗ pts hello_lsm_ps.
Proof using Type.
  etrans; [exact (pts_map hello_start_all_ps hello_start_all_nodup)|].
  unfold hello_start_all_ps.
  rewrite (pts_app hello_cpu_globals_ps) (pts_app hello_early_ps) (pts_app hello_runner_ps)
    (pts_app hello_ctor_ps) (pts_app hello_start_kept_ps).
  done.
Qed.

End own.

(** ## The whole start heap

    A run of Hello owns three things when it begins: the six lists of
    the image, the objects that the runtime allocates for the arguments,
    the environment and the auxiliary vector, and the ghost key that
    records which startup calls have happened. This section joins them
    into the one heap that the adequacy theorem starts from, and shows
    that the heap agrees with the start memory and with startup's world
    interpretation. *)

(** These are all the pieces of a run's first heap, for the runtime's
    objects argv, env and av, and the ghost key k. *)
Definition hello_heap_ps (m : mem) argv env av aps (k : Z) : list (piece * pval) :=
  hello_start_all_ps ++ start_heap_ps m argv env av aps ++ start_key_ps k.

(** A run's first heap has no repeated piece. It agrees with the start
    memory, and the world check of startup accepts it with key k. *)
Lemma hello_heap_ok g m0 m w0 w tb argv env av aps k :
  initial_memory hello_image_module = Some (g, m0) ->
  keeps_image m0 m tb (ctor_table_size (length (ctor_names hello_image_module))) ->
  string_array m argv.1 argv.2 -> string_array m env.1 env.2 -> auxv_array m av aps ->
  start_os g w0 w ->
  List.NoDup (argv.1 :: env.1 :: av :: map fst argv.2 ++ map fst env.2) ->
  all_agree m hello_start_all_ps ->
  NoDup (hello_heap_ps m argv env av aps k).*1 /\
  agrees m (list_to_map (hello_heap_ps m argv env av aps k)) /\
  os_wi_start w0 k m w (list_to_map (hello_heap_ps m argv env av aps k)).
Proof.
  intros Hi Hk Ha He Hv Hos Hn Hag.
  assert (Nd : NoDup (hello_heap_ps m argv env av aps k).*1).
  { unfold hello_heap_ps. apply nodup_join; [exact hello_start_all_nodup | apply nodup_join |].
    - exact (start_heap_nodup m argv env av aps Hn).
    - apply List.NoDup_cons; [intros []|apply List.NoDup_nil] || (cbn; apply NoDup_singleton).
    - intros l Hl Hl'. apply (start_key_heap_apart k m argv env av aps l Hl' Hl).
    - intros l Hl Hin. rewrite fmap_app in Hin. apply elem_of_app in Hin as [Hin|Hin].
      + exact (image_heap_apart m0 m tb _ _ argv env av aps Hk (hello_no_heap_regions g m0 Hi)
                 (hello_start_all_agree g m0 Hi) Ha He Hv l Hl Hin).
      + exact (hello_start_key_apart k l Hin Hl). }
  split; [exact Nd|]. split.
  - apply all_agree_map. unfold hello_heap_ps.
    apply (proj2 (all_agree_app _ _ _)). split; [exact Hag|].
    apply (proj2 (all_agree_app _ _ _)). split; [exact (start_heap_agree m argv env av aps Ha He Hv)|].
    apply start_key_agree.
  - apply (start_os_wi g w0 w k m _ Hos). apply elem_of_list_to_map_1; [exact Nd|].
    unfold hello_heap_ps. apply elem_of_app. right. apply elem_of_app. right. left.
Qed.

Section heap_own.
Context `{!gen_heapGS piece pval Σ}.

(** A proof can own the first heap as three separate parts: the image
    lists, the runtime's objects and the ghost key. *)
Lemma hello_heap_own m argv env av aps k :
  NoDup (hello_heap_ps m argv env av aps k).*1 ->
  ([∗ map] l ↦ v ∈ list_to_map (hello_heap_ps m argv env av aps k), pointsto l (DfracOwn 1) v) ⊣⊢
  pts hello_start_all_ps ∗ pts (start_heap_ps m argv env av aps) ∗ pts (start_key_ps k).
Proof using Type.
  intros Nd. etrans; [exact (pts_map _ Nd)|]. unfold hello_heap_ps.
  rewrite (pts_app hello_start_all_ps) (pts_app (start_heap_ps m argv env av aps)). done.
Qed.

End heap_own.
