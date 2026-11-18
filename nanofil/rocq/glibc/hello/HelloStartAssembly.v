(** We want to prove that GNU Hello never panics from the moment the
    runtime calls `c: __libc_start_main`, in every state that
    [StartState](../zsys/StartState.v) allows. The proof of the startup
    body in [StartLibcStartMain](../startup/StartLibcStartMain.v) takes
    the memory that startup reads and writes as separate resources, and
    earlier modules list that memory for Hello as nine lists of pieces
    of the loader's image. This module shows that every start state
    holds all nine lists, and turns them into owned resources.

    A start state keeps every object of the loader's image, except that
    it fills in the constructor table. The step from a kept image to
    agreeing pieces is the same for every program, and
    [StartOwn](../startup/StartOwn.v) proves it once. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From Stdlib Require Import String ZArith List Bool Lia.
From stdpp Require Import list fin_maps.
From Nanofil Require Import Term Syntax Values Memory Run Runtime Semantics Pieces Heap.
From Glibc Require Import OsWorld OsStart StartCtors StartState StartOwn StartJoin HelloImageModule HelloImageLoad HelloImageCtors
  HelloImageDiagObjs HelloImageCloseObjs HelloImageLocaleObjs HelloImageMbsObjs HelloImageWideObjs HelloImageCLocaleObjs
  HelloCloseReportImage HelloImageCpu HelloImageEarly HelloStartKept HelloImageDisjoint HelloImageLsm HelloImageEnviron StartImageUnique.
Import ListNotations.
Open Scope Z_scope.

(** ## The nine lists in every start state

    The lists are the CPU globals, the memory of early init and of the
    constructor runner, the inputs of the constructors, the frame that
    startup hands to main unchanged, and the globals of the startup
    body. The loader's image holds all
    of them, and none is a byte of the constructor table. *)

(** The constructor `c: _IO_stdfiles_init` links stdout into the list of
    streams, so it needs stdout's life. No other list holds that life:
    the list of initial streams leaves stdout's object out, and the kept
    frame holds only its fields. *)
Definition hello_stdout_life_ps : list (piece * pval) :=
  [(PLive (img_a "_IO_2_1_stdout_"), VLive hello_stdout_reg)].

(** The loader registers stdout's region. *)
Lemma hello_stdout_life_agree g m0 : initial_memory hello_image_module = Some (g, m0) ->
  all_agree m0 hello_stdout_life_ps.
Proof.
  intros Hi. destruct (hello_loaded_tables g m0 Hi) as [_ Hr].
  cbn [all_agree hello_stdout_life_ps fst snd agree_piece]. split; [|exact I].
  unfold live_at. rewrite Hr. split; vm_compute; reflexivity.
Qed.

(** Some library calls in Hello read globals that neither startup nor
    main touches. Hello's private state owns those globals from the
    start, and this list names them. It holds what getopt's warnings
    read, what close_stdout and its error report read, and the cells of
    the global locale that setlocale writes, and the constant data that
    the conversion to wide characters reads. Beside those it holds the
    constants that the wide print call reads to make stdout wide, to
    convert wide characters back to bytes and to close a wide stream.
    It also holds the two globals of `c: error` for now. *)
Definition hello_priv_ps : list (piece * pval) :=
  hello_getopt_priv_ps ++ hello_close_objs_ps ++ hello_locale_objs_ps ++ (hello_mbs_objs_ps ++ hello_wide_objs_ps) ++
  hello_clocale_objs_ps ++ hello_errlist_ps ++ hello_error_objs_ps.

(** These are all the pieces that Hello's startup owns or hands to main
    unchanged. *)
Definition hello_start_all_ps : list (piece * pval) :=
  hello_cpu_globals_ps ++ hello_early_ps ++ hello_runner_ps ++ hello_ctor_ps ++ hello_start_kept_ps ++
  hello_lsm_ps ++ hello_stdout_life_ps ++ hello_environ_counter_ps ++ hello_priv_ps.

(** No object and no byte occurs twice in the nine lists. *)
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
  apply (proj2 (all_agree_app _ _ _)). split; [exact (hello_lsm_agree g m0 Hi)|].
  apply (proj2 (all_agree_app _ _ _)). split; [exact (hello_stdout_life_agree g m0 Hi)|].
  apply (proj2 (all_agree_app _ _ _)). split; [exact (hello_environ_counter_agree g m0 Hi)|].
  apply (proj2 (all_agree_app _ _ _)). split; [exact (hello_getopt_priv_agree g m0 Hi)|].
  apply (proj2 (all_agree_app _ _ _)). split; [exact (hello_close_objs_agree g m0 Hi)|].
  apply (proj2 (all_agree_app _ _ _)). split; [exact (hello_locale_objs_agree g m0 Hi)|].
  apply (proj2 (all_agree_app _ _ _)). split;
    [exact (proj2 (all_agree_app _ _ _) (conj (hello_mbs_objs_agree g m0 Hi) (hello_wide_objs_agree g m0 Hi)))|].
  apply (proj2 (all_agree_app _ _ _)). split; [exact (hello_clocale_objs_agree g m0 Hi)|].
  apply (proj2 (all_agree_app _ _ _)). split; [exact (hello_errlist_agree g m0 Hi)|].
  exact (hello_error_objs_agree g m0 Hi).
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

(** Every state in which the runtime can start Hello holds all nine
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

(** ## Owning the nine lists

    The proof of a whole run begins from a heap whose points-to
    assertions are the start memory's pieces. Since no piece appears
    twice, that heap splits into the nine lists, one separate
    [[separation-logic]] resource each. *)

Section own.
Context `{!gen_heapGS piece pval Σ}.

Lemma hello_start_own :
  pts hello_start_all_ps ⊣⊢
  pts hello_cpu_globals_ps ∗ pts hello_early_ps ∗ pts hello_runner_ps ∗ pts hello_ctor_ps ∗
  pts hello_start_kept_ps ∗ pts hello_lsm_ps ∗ pts hello_stdout_life_ps ∗ pts hello_environ_counter_ps ∗
  pts hello_priv_ps.
Proof using Type.
  rewrite /hello_start_all_ps. iSplit.
  - iIntros "H".
    iDestruct (pts_app with "H") as "[A H]". iDestruct (pts_app with "H") as "[B H]".
    iDestruct (pts_app with "H") as "[C H]". iDestruct (pts_app with "H") as "[D H]".
    iDestruct (pts_app with "H") as "[E H]". iDestruct (pts_app with "H") as "[F H]".
    iDestruct (pts_app with "H") as "[G H]". iDestruct (pts_app with "H") as "[I H]".
    iSplitL "A"; [iExact "A"|]. iSplitL "B"; [iExact "B"|]. iSplitL "C"; [iExact "C"|].
    iSplitL "D"; [iExact "D"|]. iSplitL "E"; [iExact "E"|]. iSplitL "F"; [iExact "F"|].
    iSplitL "G"; [iExact "G"|]. iSplitL "I"; [iExact "I"|iExact "H"].
  - iIntros "(A & B & C & D & E & F & G & H & I)".
    iApply pts_app; iSplitL "A"; [iExact "A"|]. iApply pts_app; iSplitL "B"; [iExact "B"|].
    iApply pts_app; iSplitL "C"; [iExact "C"|]. iApply pts_app; iSplitL "D"; [iExact "D"|].
    iApply pts_app; iSplitL "E"; [iExact "E"|]. iApply pts_app; iSplitL "F"; [iExact "F"|].
    iApply pts_app; iSplitL "G"; [iExact "G"|]. iApply pts_app; iSplitL "H"; [iExact "H"|iExact "I"].
Qed.

End own.

(** ## The first heap

    When a run of Hello begins, it owns more than the nine lists. The
    runtime has filled in the constructor table and has allocated the
    arguments, the environment and the auxiliary vector, and startup
    keeps a ghost key. [StartJoin](../startup/StartJoin.v) joins all of
    these into one heap for any image. This section shows that Hello
    meets the premises of that join. *)

(** Every start state of Hello gives a first heap. The heap names each
    piece once and agrees with the start memory, and the world check of
    startup accepts it with any key k. *)
Theorem hello_first_heap g m0 m w0 w tb argc argv env av aps order k :
  initial_memory hello_image_module = Some (g, m0) ->
  lookup ctor_table_name g = Some (mkPtr tb (Ro tb)) ->
  string_array m argv.1 argv.2 -> string_array m env.1 env.2 -> auxv_array m av aps ->
  live_disjoint m ->
  keeps_image m0 m tb (ctor_table_size (length (ctor_names hello_image_module))) ->
  Permutation order (ctor_names hello_image_module) ->
  ctor_table m g tb argc (mkPtr argv.1 (Obj argv.1)) (mkPtr env.1 (Obj env.1)) order ->
  start_os g w0 w ->
  List.NoDup (fst argv :: fst env :: av :: map fst (snd argv) ++ map fst (snd env)) ->
  let H := start_ps hello_start_all_ps m g tb argc argv env av aps order k in
  NoDup H.*1 /\ agrees m (list_to_map H) /\ os_wi_start w0 k m w (list_to_map H).
Proof.
  intros Hi Ht Ha He Hv Hd Hk Hp Hc Hos Hn.
  destruct (hello_loaded_tables g m0 Hi) as [Eg Hr]. subst g.
  assert (Etb : tb = hello_runner_objs.2.1).
  { vm_compute in Ht. injection Ht as E _. symmetry. exact E. }
  subst tb.
  assert (Lt : live_at m0 hello_runner_objs.2.1 hello_runner_objs.2.2)
    by (unfold live_at; rewrite Hr; split; vm_compute; reflexivity).
  assert (Et : hello_runner_objs.2.1 + ctor_table_size (length (ctor_names hello_image_module)) <=
               r_end hello_runner_objs.2.2) by (apply Z.leb_le; vm_compute; reflexivity).
  apply (start_ps_ok m0 m _ w0 w _ hello_runner_objs.2.2 _ argc argv env av aps order _ k Hk
    (hello_no_heap_regions _ m0 Hi) Lt ltac:(vm_compute; discriminate)); try assumption.
  - rewrite (Permutation_length Hp). exact Et.
  - exact (hello_start_all_agree _ _ Hi).
  - exact (keeps_image_agree m0 m _ _ hello_runner_objs.2.2 _ Hk Hd Lt Et (hello_start_all_agree _ _ Hi)
      hello_start_all_off).
  - exact hello_start_all_nodup.
  - exact hello_start_all_off.
  - exact (hello_start_key_apart k).
Qed.
