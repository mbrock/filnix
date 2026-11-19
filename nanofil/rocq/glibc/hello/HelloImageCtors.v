(** Before `c: main` runs, glibc runs two constructors that read
    globals the linker set up. One stores the arguments of the program
    and its name, and the other links the three standard streams. Each
    constructor has a contract that asks for these globals in the state
    that the linker leaves them in. The proof of the startup of Hello
    must show that state before it can call them. This module shows
    it, as [StartInitFirstImage](../hi_atexit/StartInitFirstImage.v) and
    [StartStdfilesImage](../hi_atexit/StartStdfilesImage.v) show it for
    the hi_atexit image.

    The memory of the whole image is too large to compute, so the proof
    takes the route of [HelloImageStart](HelloImageStart.v). It loads a
    copy of the image in which every other object is blank, checks the
    pieces there, and carries them over to the real memory. Every
    address is read from the image's symbols by name, so a relink
    changes only generated files.

    This module does not show that Hello starts from this memory or that
    the startup proof calls the constructors. It gives the startup
    assembly the pieces it owns at the start and the preconditions it
    builds from them. *)

From stdpp Require Import list.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith Bool Lia.
From Nanofil Require Import Term Syntax Values Memory Run Runtime Semantics Pieces Heap Logic StringLogic MemLogic.
From Glibc Require Import ImageData ImageObjectPieces.
From Glibc Require Import GlibcProgram GlibcSpec OsWorld OsRegistry FileInv LibioStdfiles
  StartInitMiscSpec StartInitFirstSpec StartStdfilesInitSpec StartCtorVtablesSpec.
From Glibc Require Import ImageErase ImageEraseMem ImagePieces HelloImageModule HelloImageLoad.
Import ListNotations Fix.ML0 Fix.LG0 Fix.LG0.L FileInv LibioStdfiles.
Open Scope Z_scope.

(** ## The globals and their starting values

    The two constructors read twelve objects. The first one writes the
    count, the two argument pointers and the two names of the program.
    Both names start as pointers to an empty string. The second one
    reads the three streams, the head of their list, the lock of the
    list and one more pointer. The lists below state the values that the
    linker gives these objects, at the addresses that the symbols of the
    image give. *)

(** The constructors read these objects and nothing else from the image. *)
Definition hello_ctor_names : list string :=
  ["__libc_argc"; "__libc_argv"; "__environ"; "__progname"; "__progname_full"; "glibc_init_misc#str.61";
   "_IO_2_1_stderr_"; "_IO_2_1_stdout_"; "_IO_2_1_stdin_";
   "__GI__IO_list_all"; "glibc_genops#list_all_lock"; "glibc_genops#run_fp"; "__io_vtables"]%string.

Definition hello_ctor_keep (n : name) : bool := existsb (name_eqb n) (map TAtom hello_ctor_names).

(** Both names of the program start as pointers to this empty string,
    which is read-only data of the image. *)
Definition hello_empty_name : ptr := mkPtr (img_a "glibc_init_misc#str.61") (Ro (img_a "glibc_init_misc#str.61")).

(** This list is the part of the initial memory that `c: _init_first`
    writes: the lifetime and the contents of the count, of the two
    argument pointers and of the two names. *)
Definition hello_init_first_ps : list (piece * pval) :=
  List.concat [[(PLive (img_a "__libc_argc"), VLive (img_gd "__libc_argc"))]; byte_ps (img_a "__libc_argc") 0 (int_bytes 0);
    [(PLive (img_a "__libc_argv"), VLive (img_gd "__libc_argv"))]; ptr_ps (img_a "__libc_argv") 0 null;
    [(PLive (img_a "__environ"), VLive (img_gd "__environ"))]; ptr_ps (img_a "__environ") 0 null;
    [(PLive (img_a "__progname"), VLive (img_gd "__progname"))]; ptr_ps (img_a "__progname") 0 hello_empty_name;
    [(PLive (img_a "__progname_full"), VLive (img_gd "__progname_full"))];
    ptr_ps (img_a "__progname_full") 0 hello_empty_name].

(** This list is the one above without `c: __environ`. The body of
    `c: __libc_start_main` stores the environment pointer there before
    the constructors run, so a proof of startup lends that global to the
    body first. *)
Definition hello_init_first_core_ps : list (piece * pval) :=
  List.concat [[(PLive (img_a "__libc_argc"), VLive (img_gd "__libc_argc"))]; byte_ps (img_a "__libc_argc") 0 (int_bytes 0);
    [(PLive (img_a "__libc_argv"), VLive (img_gd "__libc_argv"))]; ptr_ps (img_a "__libc_argv") 0 null;
    [(PLive (img_a "__progname"), VLive (img_gd "__progname"))]; ptr_ps (img_a "__progname") 0 hello_empty_name;
    [(PLive (img_a "__progname_full"), VLive (img_gd "__progname_full"))];
    ptr_ps (img_a "__progname_full") 0 hello_empty_name].

(** The streams constructor reads this list. In it, stderr points at
    stdout, stdout points at stdin, and no stream points back. The head
    of the list points at stderr, the lock is free, and the last pointer
    is null. The list leaves out the lifetime of stdout, because the
    proofs about output own that lifetime themselves. *)
Definition hello_initial_list_ps : list (piece * pval) :=
  let fe := img_a "_IO_2_1_stderr_" in let fo := img_a "_IO_2_1_stdout_" in let fi := img_a "_IO_2_1_stdin_" in
  List.concat [[(PLive fe, VLive (img_gd "_IO_2_1_stderr_"))];
    [(PLive fi, VLive (img_gd "_IO_2_1_stdin_"))];
    ptr_ps fe 184 null; ptr_ps fe 104 (mkPtr fo (Obj fo));
    ptr_ps fo 184 null; ptr_ps fo 104 (mkPtr fi (Obj fi));
    ptr_ps fi 184 null; ptr_ps fi 104 null;
    [(PLive (img_a "__GI__IO_list_all"), VLive (img_gd "__GI__IO_list_all"))];
    ptr_ps (img_a "__GI__IO_list_all") 0 (mkPtr fe (Obj fe));
    [(PLive (img_a "glibc_genops#list_all_lock"), VLive (img_gd "glibc_genops#list_all_lock"))];
    byte_ps (img_a "glibc_genops#list_all_lock") 0 (int_bytes 0); byte_ps (img_a "glibc_genops#list_all_lock") 4 (int_bytes 0);
    ptr_ps (img_a "glibc_genops#list_all_lock") 8 null;
    [(PLive (img_a "glibc_genops#run_fp"), VLive (img_gd "glibc_genops#run_fp"))];
    ptr_ps (img_a "glibc_genops#run_fp") 0 null].

(** The check of the stream tables reads the table pointer of each
    stream, which lands 336 bytes into the read-only array of tables, and
    it needs the array to be alive. The lifetimes of the streams come
    from the list above. *)
Definition hello_vtables_ps : list (piece * pval) :=
  let vb := img_a "__io_vtables" in
  let vt f := (PAux f 216, VAux (Ro vb)) :: cell f 216 (vb + 336) in
  vt (img_a "_IO_2_1_stdin_") ++ vt (img_a "_IO_2_1_stdout_") ++ vt (img_a "_IO_2_1_stderr_") ++
  [(PLive vb, VLive (img_gd "__io_vtables"))].

(** The three constructors read these pieces. *)
Definition hello_ctor_ps : list (piece * pval) := hello_initial_list_ps ++ hello_init_first_ps ++ hello_vtables_ps.

(** These are the eleven writable objects with their addresses. *)
Definition hello_ctor_objs : list (string * Z) :=
  [(img_sym "__libc_argc"); (img_sym "__libc_argv"); (img_sym "__environ"); (img_sym "__progname");
   (img_sym "__progname_full"); (img_sym "_IO_2_1_stderr_"); (img_sym "_IO_2_1_stdout_"); (img_sym "_IO_2_1_stdin_");
   (img_sym "__GI__IO_list_all"); (img_sym "glibc_genops#list_all_lock"); (img_sym "glibc_genops#run_fp")]%string.

(** The symbols of the image name each of them at its address, and they
    name the array of tables as read-only data. *)
Definition hello_ctor_places (g : list (name * ptr)) : bool :=
  forallb (fun nb : string * Z => lookup_obj g nb.1 nb.2) hello_ctor_objs &&
  lookup_ro g "__io_vtables" (img_a "__io_vtables").

(** ## The check on the erased image

    A piece only carries over to the genuine memory when it lies inside
    an object that the copy keeps whole. The check asks that each piece
    holds its value in the copy, that each lies in a kept object, and
    that each symbol names the expected object. *)

Definition hello_ctor_skel : module := Eval vm_compute in erase hello_ctor_keep hello_image_module.

Lemma hello_ctor_skel_eq : erase hello_ctor_keep hello_image_module = hello_ctor_skel.
Proof. vm_compute. reflexivity. Qed.

Definition hello_ctor_kept : module := Eval vm_compute in kept_objects hello_ctor_keep hello_image_module.

Lemma hello_ctor_kept_incl : incl hello_ctor_kept hello_image_module.
Proof.
  assert (E : kept_objects hello_ctor_keep hello_image_module = hello_ctor_kept) by (vm_compute; reflexivity).
  rewrite <- E. apply kept_objects_incl.
Qed.

Lemma hello_ctor_check :
  match initial_memory hello_ctor_skel with
  | Some (g, m') => pieces_ok hello_ctor_keep hello_ctor_kept g m' hello_ctor_ps && hello_ctor_places g
  | None => false
  end = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

(** ## The pieces in the genuine memory *)

(** The loader builds one memory for Hello, and the startup proof owns
    the pieces of both constructors in it. This theorem shows that the
    memory holds those pieces and that no piece appears twice. It also
    shows that the symbols name the eleven writable objects at the
    addresses that the lists use. *)
Theorem hello_image_ctors g m : initial_memory hello_image_module = Some (g, m) ->
  Forall (fun nb : string * Z => Term.lookup (TAtom nb.1) g = Some (mkPtr nb.2 (Obj nb.2))) hello_ctor_objs /\
  all_agree m hello_ctor_ps /\ NoDup hello_ctor_ps.*1 /\
  Term.lookup (TAtom "__io_vtables") g = Some (mkPtr (img_a "__io_vtables") (Ro (img_a "__io_vtables"))).
Proof.
  intros E.
  destruct (image_pieces hello_ctor_keep hello_ctor_kept hello_image_module g m hello_ctor_ps
    hello_ctor_kept_incl E hello_image_names hello_image_zero) as (m' & E' & _ & P).
  pose proof hello_ctor_check as C. rewrite <- hello_ctor_skel_eq, E' in C.
  apply andb_true_iff in C as [Cp Cg]. split_and!.
  - unfold hello_ctor_places in Cg. apply andb_true_iff in Cg as [Cg _].
    rewrite forallb_forall in Cg. apply List.Forall_forall.
    intros nb Hnb. exact (lookup_obj_ok _ _ _ (Cg nb Hnb)).
  - exact (P Cp).
  - apply (NoDup_fmap_1 (fun p => match p with
      | PLive b => 4 * 512 * b | PByte b o => 4 * (512 * b + o) + 1
      | PAux b o => 4 * (512 * b + o) + 2 | _ => 3 end)).
    apply (bool_decide_unpack _). vm_compute. exact I.
  - unfold hello_ctor_places in Cg. apply andb_true_iff in Cg as [_ Cv]. exact (lookup_ro_ok _ _ _ Cv).
Qed.

(** ## The records of the contracts *)

(** The three globals that hold the arguments lie here in Hello. *)
Definition hello_init_first_objs : if_objs :=
  {| if_ac := img_a "__libc_argc"; if_acreg := img_gd "__libc_argc";
     if_lv := img_a "__libc_argv"; if_lvreg := img_gd "__libc_argv";
     if_en := img_a "__environ"; if_enreg := img_gd "__environ" |}.

(** The two names of the program lie at fixed addresses in this image.
    The argument array does not, because the system places it when the
    program starts. The caller gives its address av and its region. *)
Definition hello_init_misc_objs (av : Z) (avreg : region) : im_objs :=
  {| im_pn := img_a "__progname"; im_pnreg := img_gd "__progname";
     im_pf := img_a "__progname_full"; im_pfreg := img_gd "__progname_full";
     im_av := av; im_avreg := avreg |}.

(** This tuple holds the inputs of `c: _IO_stdfiles_init` in the order
    of its contract: stderr, stdout, stdin, the head of the list, the
    lock and `c: run_fp`. *)
Definition hello_stdfiles_inputs : ptr * ptr * ptr * Z * region * Z * region * Z * region :=
  (mkPtr (img_a "_IO_2_1_stderr_") (Obj (img_a "_IO_2_1_stderr_")),
   mkPtr (img_a "_IO_2_1_stdout_") (Obj (img_a "_IO_2_1_stdout_")),
   mkPtr (img_a "_IO_2_1_stdin_") (Obj (img_a "_IO_2_1_stdin_")),
   img_a "__GI__IO_list_all", img_gd "__GI__IO_list_all",
   img_a "glibc_genops#list_all_lock", img_gd "glibc_genops#list_all_lock",
   img_a "glibc_genops#run_fp", img_gd "glibc_genops#run_fp").

(** Stdout lies in this region, and the caller supplies its lifetime. *)
Definition hello_stdout_reg : region := img_gd "_IO_2_1_stdout_".

Lemma hello_pts_concat `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ} pss :
  pts (List.concat pss) ⊣⊢ [∗ list] ps ∈ pss, pts ps.
Proof using Type. induction pss as [|ps pss IH]; cbn [List.concat]; rewrite ?pts_app ?IH; done. Qed.

(** The list of `c: _init_first` is its core and `c: __environ`, which
    starts null. *)
Lemma hello_init_first_split `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ} :
  pts hello_init_first_ps ⊣⊢
  pts hello_init_first_core_ps ∗ live (img_a "__environ") (img_gd "__environ") ∗ pcell (img_a "__environ") 0 null.
Proof using Type.
  rewrite /hello_init_first_ps /hello_init_first_core_ps !hello_pts_concat. cbn [big_opL].
  iSplit.
  - iIntros "(A & B & C & D & E & F & G & H & I & J & _)". iFrame.
  - iIntros "((A & B & C & D & G & H & I & J & _) & E & F)". iFrame.
Qed.

Section image.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ} (w0 : os_world).
Context (g : list (name * ptr)) (m : mem) (fr : word -> mem -> option (res unit * mem)).
Hypothesis Hi : initial_memory hello_image_module = Some (g, m).
Local Notation hello_program := (program_of w0 glibc_os_registry (mkGenv hello_image_module g fr)).

(** The symbols of the loaded image are the ones the records use. *)
Local Lemma hello_ctor_lookups :
  Forall (fun nb : string * Z => Term.lookup (TAtom nb.1) g = Some (mkPtr nb.2 (Obj nb.2))) hello_ctor_objs.
Proof using Hi. exact (proj1 (hello_image_ctors g m Hi)). Qed.

(** Hello may call `c: _init_first` at its start. The call needs the five
    globals as they are in the initial memory and a share of the
    argument array, whose first slot points at the name of the program.
    The count must fit in an `c: int`, and the argument array must be
    aligned and must not lie at address zero. *)
Lemma hello_init_first_pre av avreg dq argc envp a s v :
  0 <= argc < 2 ^ 32 -> 0 < av -> av mod 8 = 0 -> av + 8 <= r_end avreg ->
  pts hello_init_first_core_ps -∗ live (img_a "__environ") (img_gd "__environ") -∗ pcell (img_a "__environ") 0 v -∗
  im_args (glibc_program := hello_program) (hello_init_misc_objs av avreg) dq a s -∗
  fs_pre (init_first_spec (glibc_program := hello_program))
    (hello_init_first_objs, hello_init_misc_objs av avreg, dq, argc, envp, a, s,
     hello_empty_name, hello_empty_name, null, v).
Proof using Hi.
  intros Hargc Hav0 Hava Have. pose proof hello_ctor_lookups as L.
  unfold hello_ctor_objs in L. repeat (apply Forall_cons_1 in L as [? L]). cbn [fst snd] in *.
  rewrite /hello_init_first_core_ps hello_pts_concat. cbn [big_opL fs_pre init_first_spec].
  iIntros "(Lac & Hac & Llv & Hlv & Lpn & Hpn & Lpf & Hpf & _) Len Hen Ha".
  iSplit.
  { iPureIntro. unfold if_ok, im_ok. cbn [ge_globals if_ac if_acreg if_lv if_lvreg if_en if_enreg
      im_pn im_pnreg im_pf im_pfreg im_av im_avreg hello_init_first_objs hello_init_misc_objs].
    unfold program_ge. cbn [program_of ge_globals].
    split_and!; first [eassumption | reflexivity | cbn [r_end]; lia]. }
  iSplitL "Lac Llv Len"; [rewrite /if_lives; iFrame "Lac Llv Len"|].
  iSplitL "Hac"; [iExists (int_bytes 0); iSplit; [done|iExact "Hac"]|].
  iSplitL "Hlv"; [iExact "Hlv"|]. iSplitL "Hen"; [iExact "Hen"|].
  iSplitR "Ha"; [|iExact "Ha"]. rewrite /im_names. iFrame "Lpn Hpn Lpf Hpf".
Qed.

(** When Hello starts, each of its three streams points at the next one
    and none points back, which is what `c: _IO_stdfiles_init` expects.
    The call also needs stdout to be alive, and the caller supplies that
    lifetime separately. *)
Lemma hello_stdfiles_init_pre :
  pts hello_initial_list_ps -∗ live (img_a "_IO_2_1_stdout_") hello_stdout_reg -∗
  fs_pre (stdfiles_init_spec (glibc_program := hello_program)) hello_stdfiles_inputs.
Proof using Hi.
  pose proof hello_ctor_lookups as L. unfold hello_ctor_objs in L. repeat (apply Forall_cons_1 in L as [? L]). cbn [fst snd] in *.
  rewrite /hello_initial_list_ps hello_pts_concat. cbn [big_opL fs_pre stdfiles_init_spec hello_stdfiles_inputs].
  iIntros "(He & Hi & Hep & Hec & Hop & Hoc & Hip & Hic & Hla & Hlac & Hlk & Hlk0 & Hlk4 & Hlk8 & Hrf & Hrfc & _) Ho".
  iSplit; [iPureIntro; unfold stdfiles_init_ok, program_ge; cbn [program_of ge_globals];
           split_and!; first [eassumption | reflexivity | cbn [r_end]; lia]|].
  iSplitL "Hla"; [iExact "Hla"|]. iSplitL "Hlac"; [iExact "Hlac"|].
  iSplitL "He Hep Hec"; [|iSplitL "Ho Hop Hoc"; [|iSplitL "Hi Hip Hic"; [|iSplitR "Hrf Hrfc"]]].
  - iExists (img_a "_IO_2_1_stderr_"), (img_gd "_IO_2_1_stderr_"). iFrame "He Hep Hec".
    iPureIntro. vm_compute. intuition congruence.
  - iExists (img_a "_IO_2_1_stdout_"), hello_stdout_reg. iFrame "Ho Hop Hoc". iPureIntro. vm_compute. intuition congruence.
  - iExists (img_a "_IO_2_1_stdin_"), (img_gd "_IO_2_1_stdin_"). iFrame "Hi Hip Hic".
    iPureIntro. vm_compute. intuition congruence.
  - unfold lock_state, int_cell. iFrame "Hlk Hlk0 Hlk4 Hlk8". iPureIntro. vm_compute. intuition congruence.
  - iFrame "Hrf Hrfc".
Qed.

(** The check of the stream tables asks that the program names the three
    streams and the array of tables, and that each stream is aligned and
    large enough. Hello meets that. The caller builds the precondition
    from these facts, the pieces of [hello_vtables_ps] and the lifetimes
    of the streams. *)
Lemma hello_vtables_ok :
  vtables_globals (glibc_program := hello_program)
    (img_a "_IO_2_1_stdin_") (img_a "_IO_2_1_stdout_") (img_a "_IO_2_1_stderr_") (img_a "__io_vtables") /\
  stream_ok (img_a "_IO_2_1_stdin_") (img_gd "_IO_2_1_stdin_") /\
  stream_ok (img_a "_IO_2_1_stdout_") hello_stdout_reg /\
  stream_ok (img_a "_IO_2_1_stderr_") (img_gd "_IO_2_1_stderr_").
Proof using Hi.
  pose proof hello_ctor_lookups as L. unfold hello_ctor_objs in L.
  repeat (apply Forall_cons_1 in L as [? L]). cbn [fst snd] in *.
  pose proof (proj2 (proj2 (proj2 (hello_image_ctors g m Hi)))) as Lv.
  unfold vtables_globals, stream_ok, hello_stdout_reg, program_ge. cbn [program_of ge_globals].
  split_and!; first [eassumption | reflexivity | cbn [r_end]; lia].
Qed.

End image.
