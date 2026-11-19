(** Hello's safety proof takes as parameters the objects that the
    linked program supplies, together with facts about where those
    objects are and how large they are. Those facts describe the real
    program only if one choice of objects makes them true of the memory
    that the loader builds for the whole linked image. This file gives
    such a choice and checks it against the loader's symbols, regions
    and stored words.

    Every address below is the one the linker chose for the whole image.
    One computation over the loaded image confirms them all, and the
    theorems read their facts from that computation.

    These are facts about the memory that the loader builds, before the
    program runs. They do not show that Hello starts from this memory,
    that a constructor leaves these objects alone, or who owns any of
    them. In particular, the flag that tells glibc the program has one
    thread holds 0 here, but the stream proofs need it to hold 1, so a
    proof of startup has to set it. The linking facts also ask that the
    environment's free behave as the runtime's free does, and this file
    leaves that to the caller. *)

From stdpp Require Import list.
From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Run Heap.
From Glibc Require Import HelloObjects.
From Glibc Require Import HelloLiterals ImageData FileInv AtexitLogic ImageEraseMem
  HelloImageModule HelloImageLoad.
Import ListNotations.
Open Scope Z_scope.

(** ## The objects

    Each writable object gets a capability of its own object, each
    string and table a read-only one, and each function pointer the
    capability of its function. The regions are the ones the loader
    registers, which the theorem hello_image_regions confirms. *)

(** This is the choice of objects for the linked image. The three
    streams are glibc's static FILE objects for stderr, stdout and
    stdin, and the exit objects are those of atexit and exit. *)
Definition hello_image_objs : hello_objs :=
  mkHelloObjs (mkPtr (img_a "_IO_2_1_stdout_") (Obj (img_a "_IO_2_1_stdout_"))) (mkPtr (img_a "_IO_2_1_stderr_") (Obj (img_a "_IO_2_1_stderr_"))) (mkPtr (img_a "_IO_2_1_stdin_") (Obj (img_a "_IO_2_1_stdin_")))
    (img_a "stdout") (img_gd "stdout") (img_a "stderr") (img_gd "stderr")
    (img_a "optarg") (img_gd "optarg") (img_a "optind") (img_gd "optind")
    (img_a "__io_vtables") (img_gd "__io_vtables") (img_a "__libc_single_threaded") (img_gd "__libc_single_threaded") (img_a "errno") (img_gd "errno")
    (mkExitObjs (img_a "__exit_funcs_lock") (img_gd "__exit_funcs_lock") (img_a "__exit_funcs_done") (img_gd "__exit_funcs_done") (img_a "__new_exitfn_called") (img_gd "__new_exitfn_called")
       (img_a "__exit_funcs") (img_gd "__exit_funcs") (img_a "glibc_cxa_atexit#initial") (img_gd "glibc_cxa_atexit#initial"))
    (img_a "glibc_exit#__exit_lock") (img_gd "glibc_exit#__exit_lock") (mkPtr (img_a "close_stdout") (Fn (TAtom "close_stdout")))
    (mkPtr (img_a "glibc_genops#flush_cleanup") (Fn (TAtom "glibc_genops#flush_cleanup")))
    (img_a "glibc_malloc#mp_") (img_gd "glibc_malloc#mp_") (img_a "tcache") (img_gd "tcache") (img_a "glibc_malloc#__tcache_dummy") (img_gd "glibc_malloc#__tcache_dummy")
    (img_a "program_name") (img_a "__progname_full") (img_a "__progname") (img_gd "program_name") (img_gd "__progname_full") (img_gd "__progname")
    (mkPtr (img_a "progname#str.3") (Ro (img_a "progname#str.3"))) (mkPtr (img_a "progname#str.4") (Ro (img_a "progname#str.4"))).

(** These symbols name writable objects at the given bases. *)
Definition hello_image_obj_syms : list (string * Z) :=
  [(img_sym "stdout"); (img_sym "stderr"); (img_sym "optarg"); (img_sym "optind");
   (img_sym "program_name"); ("program_invocation_name", (img_a "__progname_full"));
   ("program_invocation_short_name", (img_a "__progname")); ("__libc_errno", (img_a "errno"));
   (img_sym "glibc_malloc#mp_"); (img_sym "tcache"); (img_sym "__exit_funcs_lock");
   (img_sym "__exit_funcs_done"); (img_sym "__new_exitfn_called"); (img_sym "__exit_funcs");
   (img_sym "glibc_exit#__exit_lock"); ("__libc_single_threaded_internal", (img_a "__libc_single_threaded"));
   (img_sym "__GI__IO_list_all"); (img_sym "_IO_2_1_stderr_"); (img_sym "_IO_2_1_stdout_");
   (img_sym "_IO_2_1_stdin_")]%string.

(** These symbols name read-only objects at the given bases. *)
Definition hello_image_ro_syms : list (string * Z) :=
  [(img_sym "progname#str.3"); (img_sym "progname#str.4"); (img_sym "__io_vtables");
   (img_sym "glibc_malloc#__tcache_dummy")]%string.

(** These are the literals that main passes to its callees, each with
    the base of its read-only object. *)
Definition hello_image_lits : list (string * Z) :=
  [(img_sym "hello#str.54"); (img_sym "hello#str.55"); (img_sym "hello#str.56"); (img_sym "hello#str.57");
   (img_sym "hello#str.58"); (img_sym "hello#str.59"); (img_sym "hello#str.60"); (img_sym "hello#str.61");
   (img_sym "hello#str.62"); (img_sym "hello#str.63"); (img_sym "hello#str.69");
   (img_sym "hello#parse_options.longopts.64"); (img_sym "hello#str.70"); (img_sym "hello#str.71");
   (img_sym "hello#str.72"); (img_sym "hello#str.73"); (img_sym "hello#str.74"); (img_sym "hello#str.75");
   (img_sym "hello#str.76"); (img_sym "hello#str.77"); (img_sym "hello#str.78"); (img_sym "hello#str.79");
   (img_sym "hello#str.80"); (img_sym "hello#str.81"); (img_sym "hello#str.82");
   (img_sym "hello#str.83")]%string.

(** The list names exactly the literals of hello_layout, in order. *)
Lemma hello_image_lits_names : map fst hello_image_lits = hello_lits.
Proof. reflexivity. Qed.

(** These symbols name functions at the given addresses. *)
Definition hello_image_fn_syms : list (string * Z) :=
  [(img_sym "close_stdout"); (img_sym "glibc_genops#flush_cleanup")]%string.

(** These are the objects of the record and the three streams, each
    with the end of its region. *)
Definition hello_image_regs : list (Z * Z) :=
  [((img_a "stdout"), (img_e "stdout")); ((img_a "stderr"), (img_e "stderr")); ((img_a "optarg"), (img_e "optarg")); ((img_a "optind"), (img_e "optind")); ((img_a "__io_vtables"), (img_e "__io_vtables"));
   ((img_a "__libc_single_threaded"), (img_e "__libc_single_threaded")); ((img_a "errno"), (img_e "errno")); ((img_a "__exit_funcs_lock"), (img_e "__exit_funcs_lock")); ((img_a "__exit_funcs_done"), (img_e "__exit_funcs_done")); ((img_a "__new_exitfn_called"), (img_e "__new_exitfn_called"));
   ((img_a "__exit_funcs"), (img_e "__exit_funcs")); ((img_a "glibc_cxa_atexit#initial"), (img_e "glibc_cxa_atexit#initial")); ((img_a "glibc_exit#__exit_lock"), (img_e "glibc_exit#__exit_lock")); ((img_a "glibc_malloc#mp_"), (img_e "glibc_malloc#mp_")); ((img_a "tcache"), (img_e "tcache"));
   ((img_a "glibc_malloc#__tcache_dummy"), (img_e "glibc_malloc#__tcache_dummy")); ((img_a "program_name"), (img_e "program_name")); ((img_a "__progname_full"), (img_e "__progname_full")); ((img_a "__progname"), (img_e "__progname"));
   ((img_a "_IO_2_1_stderr_"), (img_e "_IO_2_1_stderr_")); ((img_a "_IO_2_1_stdout_"), (img_e "_IO_2_1_stdout_")); ((img_a "_IO_2_1_stdin_"), (img_e "_IO_2_1_stdin_"))].

(** These words of the initialized image hold pointers, each with its
    capability: stdout and stderr hold their streams, the list of all
    streams starts at stderr, and each stream's chain field, 104 bytes
    in, points to the next one, ending with a null after stdin. *)
Definition hello_image_cells : list (Z * Z * cap) :=
  [((img_a "stdout"), (img_a "_IO_2_1_stdout_"), Obj (img_a "_IO_2_1_stdout_")); ((img_a "stderr"), (img_a "_IO_2_1_stderr_"), Obj (img_a "_IO_2_1_stderr_")); ((img_a "__GI__IO_list_all"), (img_a "_IO_2_1_stderr_"), Obj (img_a "_IO_2_1_stderr_"));
   ((img_a "_IO_2_1_stderr_") + 104, (img_a "_IO_2_1_stdout_"), Obj (img_a "_IO_2_1_stdout_")); ((img_a "_IO_2_1_stdout_") + 104, (img_a "_IO_2_1_stdin_"), Obj (img_a "_IO_2_1_stdin_")); ((img_a "_IO_2_1_stdin_") + 104, 0, CNone)].

(** ## The check *)

(** A symbol names the function f at address a. *)
Definition lookup_fn (g : list (name * ptr)) (n : string) (a : Z) : bool :=
  match Term.lookup (TAtom n) g with
  | Some p => (ptr_addr p =? a) && match ptr_cap p with Fn f => name_eqb f (TAtom n) | _ => false end
  | None => false
  end.

Lemma lookup_fn_ok g n a : lookup_fn g n a = true -> Term.lookup (TAtom n) g = Some (mkPtr a (Fn (TAtom n))).
Proof.
  unfold lookup_fn. destruct (Term.lookup (TAtom n) g) as [[b c]|]; [|discriminate]. cbn [ptr_addr ptr_cap].
  destruct c; try (rewrite andb_false_r; discriminate). intros H. apply andb_true_iff in H as [Ha Hc].
  apply Z.eqb_eq in Ha. apply term_eqb_eq in Hc. subst. reflexivity.
Qed.

Local Instance region_eq_dec : EqDecision region.
Proof. intros x y. change ({x = y} + {x <> y}). decide equality; try apply Z.eq_dec; decide equality. Defined.

Local Instance cap_eq_dec : EqDecision cap.
Proof.
  intros x y. change ({x = y} + {x <> y}). decide equality; try apply Z.eq_dec.
  destruct (term_eqb f f0) eqn:E;
    [left; apply term_eqb_eq; exact E | right; intros ->; rewrite term_eqb_refl in E; discriminate].
  destruct (term_eqb n n0) eqn:E;
    [left; apply term_eqb_eq; exact E | right; intros ->; rewrite term_eqb_refl in E; discriminate].
Defined.

(** The check holds when every symbol, region and word is as listed. *)
Definition hello_layout_ok (g : list (name * ptr)) (m : mem) : bool :=
  forallb (fun nb : string * Z => lookup_obj g nb.1 nb.2) hello_image_obj_syms &&
  forallb (fun nb : string * Z => lookup_ro g nb.1 nb.2) (hello_image_ro_syms ++ hello_image_lits) &&
  forallb (fun nb : string * Z => lookup_fn g nb.1 nb.2) hello_image_fn_syms &&
  forallb (fun be : Z * Z => bool_decide (object_region be.1 (m_regions m) = Some (gd be.1 be.2)))
    hello_image_regs &&
  forallb (fun c : Z * Z * cap => (load_bytes m c.1.1 8 =? c.1.2) && bool_decide (m_aux m c.1.1 = c.2))
    hello_image_cells.

(** The loaded image passes the check. *)
Lemma hello_layout_check g m : initial_memory hello_image_module = Some (g, m) -> hello_layout_ok g m = true.
Proof.
  intros Hi.
  assert (C : option_map (fun gm => hello_layout_ok gm.1 gm.2) (initial_memory hello_image_module) =
    Some true) by (rewrite HelloImageLoad.hello_loaded_eq; vm_cast_no_check (eq_refl (Some true))).
  rewrite Hi in C. injection C as C. exact C.
Qed.

(** ## The facts *)

Section facts.
Context (g : list (name * ptr)) (m : mem) (fr : word -> mem -> option (res unit * mem))
  (Hi : initial_memory hello_image_module = Some (g, m)).
Local Notation ge := (mkGenv hello_image_module g fr).

Local Lemma parts : hello_layout_ok g m = true.
Proof using Type*. exact (hello_layout_check g m Hi). Qed.

Lemma hello_image_obj_sym n b : In (n, b) hello_image_obj_syms ->
  Term.lookup (TAtom n) g = Some (mkPtr b (Obj b)).
Proof using Type*.
  intros Hin. pose proof parts as H. unfold hello_layout_ok in H. repeat rewrite andb_true_iff in H.
  apply lookup_obj_ok. exact (proj1 (forallb_forall _ _) (proj1 (proj1 (proj1 (proj1 H)))) (n, b) Hin).
Qed.

Lemma hello_image_ro_sym n b : In (n, b) (hello_image_ro_syms ++ hello_image_lits) ->
  Term.lookup (TAtom n) g = Some (mkPtr b (Ro b)).
Proof using Type*.
  intros Hin. pose proof parts as H. unfold hello_layout_ok in H. repeat rewrite andb_true_iff in H.
  apply lookup_ro_ok. exact (proj1 (forallb_forall _ _) (proj2 (proj1 (proj1 (proj1 H)))) (n, b) Hin).
Qed.

Lemma hello_image_fn_sym n a : In (n, a) hello_image_fn_syms ->
  Term.lookup (TAtom n) g = Some (mkPtr a (Fn (TAtom n))).
Proof using Type*.
  intros Hin. pose proof parts as H. unfold hello_layout_ok in H. repeat rewrite andb_true_iff in H.
  apply lookup_fn_ok. exact (proj1 (forallb_forall _ _) (proj2 (proj1 (proj1 H))) (n, a) Hin).
Qed.

(** Every object of the record and every stream has exactly the region
    that the loader registers, so no proof can enlarge one. *)
Theorem hello_image_regions :
  Forall (fun be : Z * Z => object_region be.1 (m_regions m) = Some (gd be.1 be.2)) hello_image_regs.
Proof using Type*.
  pose proof parts as H. unfold hello_layout_ok in H. repeat rewrite andb_true_iff in H.
  apply List.Forall_forall. intros be Hin.
  exact (bool_decide_eq_true_1 _ (proj1 (forallb_forall _ _) (proj2 (proj1 H)) be Hin)).
Qed.

(** The initialized words hold the listed pointers and capabilities.
    This says what the loader wrote, not who owns the words. *)
Theorem hello_image_stream_cells :
  Forall (fun c : Z * Z * cap => load_bytes m c.1.1 8 = c.1.2 /\ m_aux m c.1.1 = c.2) hello_image_cells.
Proof using Type*.
  pose proof parts as H. unfold hello_layout_ok in H. repeat rewrite andb_true_iff in H.
  apply List.Forall_forall. intros c Hin.
  pose proof (proj1 (forallb_forall _ _) (proj2 H) c Hin) as Hc. apply andb_true_iff in Hc as [Hb Ha].
  split; [exact (proj1 (Z.eqb_eq _ _) Hb) | exact (bool_decide_eq_true_1 _ Ha)].
Qed.

(** Each literal of main has a read-only capability to its object. The
    record hello_layout asks only that the literal has a symbol. *)
Theorem hello_image_lits_ro :
  Forall (fun nb : string * Z => Term.lookup (TAtom nb.1) g = Some (mkPtr nb.2 (Ro nb.2))) hello_image_lits.
Proof using Type*.
  apply List.Forall_forall. intros [n b] Hin. apply hello_image_ro_sym. apply in_or_app. right. exact Hin.
Qed.

Local Ltac inl := cbn [In app hello_image_obj_syms hello_image_ro_syms hello_image_lits];
  repeat first [left; reflexivity | right].
Local Ltac obj := apply hello_image_obj_sym; inl.
Local Ltac ro := apply hello_image_ro_sym; inl.

(** The choice of objects satisfies hello_layout in the loaded image. *)
Theorem hello_image_layout : hello_layout ge hello_image_objs.
Proof using Hi.
  constructor; cbn [ge_globals hello_image_objs ho_cp ho_so ho_soreg ho_se ho_sereg ho_oa ho_oareg
    ho_oi ho_oireg ho_pb ho_preg ho_eb ho_ereg gd r_end]; try (split_and!; first [lia | reflexivity]); try obj.
  - intros s Hs. rewrite <- hello_image_lits_names in Hs. apply in_map_iff in Hs as [[n b] [<- Hin]].
    unfold sym_ptr. cbn [ge_globals fst]. rewrite (hello_image_ro_sym n b); [reflexivity|].
    apply in_or_app. right. exact Hin.
  - exact (hello_image_fn_sym "close_stdout" (img_a "close_stdout") (or_introl eq_refl)).
Qed.

(** The choice also satisfies the object and layout fields of
    hello_link, stated here as they appear in that record. *)
Theorem hello_image_link_objects : let o := hello_image_objs in
  lookup (TAtom "program_name") (ge_globals ge) = Some (mkPtr (ho_pb o) (Obj (ho_pb o))) /\
  lookup (TAtom "program_invocation_name") (ge_globals ge) = Some (mkPtr (ho_nb o) (Obj (ho_nb o))) /\
  lookup (TAtom "program_invocation_short_name") (ge_globals ge) = Some (mkPtr (ho_nsb o) (Obj (ho_nsb o))) /\
  lookup (TAtom "progname#str.3") (ge_globals ge) = Some (ho_lp o) /\
  lookup (TAtom "progname#str.4") (ge_globals ge) = Some (ho_tp o) /\
  (0 <= ho_pb o /\ ho_pb o mod 8 = 0 /\ ho_pb o + 8 <= r_end (ho_preg o) /\ r_end (ho_preg o) <= 2 ^ 48) /\
  (0 <= ho_nb o /\ ho_nb o mod 8 = 0 /\ ho_nb o + 8 <= r_end (ho_nreg o) /\ r_end (ho_nreg o) <= 2 ^ 48) /\
  (0 <= ho_nsb o /\ ho_nsb o mod 8 = 0 /\ ho_nsb o + 8 <= r_end (ho_nsreg o) /\ r_end (ho_nsreg o) <= 2 ^ 48) /\
  lookup (TAtom "__libc_errno") (ge_globals ge) = Some (mkPtr (ho_eb o) (Obj (ho_eb o))) /\
  lookup (TAtom "glibc_malloc#mp_") (ge_globals ge) = Some (mkPtr (ho_mp o) (Obj (ho_mp o))) /\
  lookup (TAtom "tcache") (ge_globals ge) = Some (mkPtr (ho_tc o) (Obj (ho_tc o))) /\
  exit_layout (ho_x o) /\ exit_globals ge (ho_x o) /\
  (0 < ho_el o /\ ho_el o mod 8 = 0 /\ ho_el o + 16 <= r_end (ho_elr o) <= 2 ^ 64 /\
   lookup (TAtom "glibc_exit#__exit_lock") (ge_globals ge) = Some (mkPtr (ho_el o) (Obj (ho_el o)))) /\
  (lookup (TAtom "glibc_genops#flush_cleanup") (ge_globals ge) = Some (ho_fcp o) /\
   0 <= ptr_addr (ho_fcp o) < 2 ^ 64) /\
  (ptr_cap (ho_cp o) = Fn (TAtom "close_stdout") /\ function_check_res ge (ho_cp o) = Some ok /\
   0 < ptr_addr (ho_cp o) < 2 ^ 64).
Proof using Hi.
  cbv zeta. unfold exit_layout, exit_globals.
  cbn [ge_globals hello_image_objs ho_pb ho_nb ho_nsb ho_preg ho_nreg ho_nsreg ho_lp ho_tp ho_eb ho_mp ho_tc
    ho_x ho_el ho_elr ho_fcp ho_cp xo_lock xo_lock_reg xo_done xo_done_reg xo_called xo_called_reg
    xo_funcs xo_funcs_reg xo_init xo_init_reg gd r_end ptr_addr ptr_cap].
  assert (Hc : Term.lookup (TAtom "close_stdout") g = Some (mkPtr (img_a "close_stdout") (Fn (TAtom "close_stdout"))))
    by exact (hello_image_fn_sym _ _ (or_introl eq_refl)).
  split_and!; try lia; try obj; try ro; try reflexivity.
  - exact (hello_image_fn_sym _ _ (or_intror (or_introl eq_refl))).
  - unfold function_check_res. cbn [ptr_cap ptr_addr ge_globals]. rewrite Hc. reflexivity.
Qed.

End facts.
