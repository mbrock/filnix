(** These tables connect checked function bodies to C declarations and source lines.
    Names and locations support annotations and diagnostic messages, not soundness premises.
    Natural-loop headers provide optional cuts for symbolic execution; any cut list is sound.
    Computation checks that every recorded block label belongs to the decoded function.
    The code generator reproduces this file from the capture; do not edit it. *)

From Stdlib Require Import String List Bool.
From Glibc Require Import CodePrelude ExitRunCode.
Import ListNotations.
Open Scope string_scope.

Module ExitRunSrc.

Module fn___run_exit_handlers.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("exit.c", 42%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("exit.c", 48%nat)); ((TAtom "L13"), ("exit.c", 48%nat)); ((TAtom "L33"), ("exit.c", 48%nat)); ((TAtom "L34"), ("exit.c", 48%nat)); ((TAtom "L38"), ("exit.c", 48%nat)); ((TAtom "L27"), ("exit.c", 48%nat)); ((TAtom "L15"), ("exit.c", 48%nat)); ((TAtom "L55"), ("exit.c", 52%nat)); ((TAtom "L57"), ("exit.c", 54%nat)); ((TAtom "L69"), ("exit.c", 54%nat)); ((TAtom "L70"), ("exit.c", 54%nat)); ((TAtom "L74"), ("exit.c", 54%nat)); ((TAtom "L88"), ("exit.c", 65%nat)); ((TAtom "L91"), ("exit.c", 71%nat)); ((TAtom "L101"), ("exit.c", 75%nat)); ((TAtom "L102"), ("exit.c", 77%nat)); ((TAtom "L130"), ("exit.c", 91%nat)); ((TAtom "L145"), ("exit.c", 96%nat)); ((TAtom "L146"), ("exit.c", 96%nat)); ((TAtom "L157"), ("exit.c", 96%nat)); ((TAtom "L152"), ("exit.c", 97%nat)); ((TAtom "L181"), ("exit.c", 98%nat)); ((TAtom "L182"), ("exit.c", 98%nat)); ((TAtom "L186"), ("exit.c", 98%nat)); ((TAtom "L196"), ("exit.c", 101%nat)); ((TAtom "L207"), ("exit.c", 105%nat)); ((TAtom "L208"), ("exit.c", 105%nat)); ((TAtom "L219"), ("exit.c", 105%nat)); ((TAtom "L214"), ("exit.c", 106%nat)); ((TAtom "L241"), ("exit.c", 107%nat)); ((TAtom "L242"), ("exit.c", 107%nat)); ((TAtom "L246"), ("exit.c", 107%nat)); ((TAtom "L256"), ("exit.c", 112%nat)); ((TAtom "L272"), ("exit.c", 118%nat)); ((TAtom "L273"), ("exit.c", 118%nat)); ((TAtom "L284"), ("exit.c", 118%nat)); ((TAtom "L279"), ("exit.c", 119%nat)); ((TAtom "L308"), ("exit.c", 120%nat)); ((TAtom "L309"), ("exit.c", 120%nat)); ((TAtom "L313"), ("exit.c", 120%nat)); ((TAtom "L325"), ("exit.c", 80%nat)); ((TAtom "L328"), ("exit.c", 80%nat)); ((TAtom "L330"), ("exit.c", 80%nat)); ((TAtom "L326"), ("exit.c", 80%nat)); ((TAtom "L332"), ("exit.c", 80%nat)); ((TAtom "L334"), ("exit.c", 80%nat)); ((TAtom "L123"), ("exit.c", 124%nat)); ((TAtom "L103"), ("exit.c", 130%nat)); ((TAtom "L350"), ("exit.c", 134%nat)); ((TAtom "L365"), ("exit.c", 137%nat)); ((TAtom "L366"), ("exit.c", 137%nat)); ((TAtom "L377"), ("exit.c", 137%nat)); ((TAtom "L372"), ("exit.c", 139%nat)); ((TAtom "L388"), ("exit.c", 140%nat)); ((TAtom "L390"), ("exit.c", 143%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "status"); ((TAtom "v104"), "cur"); ((TAtom "v109"), "cur"); ((TAtom "v111"), "cur"); ((TAtom "v116"), "f"); ((TAtom "v119"), "__new_exitfn_called"); ((TAtom "v12"), "self"); ((TAtom "v120"), "f"); ((TAtom "v131"), "f"); ((TAtom "v133"), "onfct"); ((TAtom "v134"), "f"); ((TAtom "v137"), "arg"); ((TAtom "v138"), "onfct"); ((TAtom "v143"), "__futex"); ((TAtom "v147"), "__oldval"); ((TAtom "v153"), "__oldval"); ((TAtom "v165"), "__futex"); ((TAtom "v166"), "__futex"); ((TAtom "v167"), "__private"); ((TAtom "v168"), "onfct"); ((TAtom "v169"), "status"); ((TAtom "v170"), "arg"); ((TAtom "v177"), "__futex"); ((TAtom "v178"), "__atg3_old"); ((TAtom "v179"), "__atg3_old"); ((TAtom "v19"), "self"); ((TAtom "v194"), "__futex"); ((TAtom "v195"), "__futex"); ((TAtom "v197"), "f"); ((TAtom "v199"), "atfct"); ((TAtom "v2"), "listp"); ((TAtom "v200"), "atfct"); ((TAtom "v205"), "__futex"); ((TAtom "v209"), "__oldval"); ((TAtom "v215"), "__oldval"); ((TAtom "v227"), "__futex"); ((TAtom "v228"), "__futex"); ((TAtom "v229"), "__private"); ((TAtom "v230"), "atfct"); ((TAtom "v237"), "__futex"); ((TAtom "v238"), "__atg3_old"); ((TAtom "v239"), "__atg3_old"); ((TAtom "v254"), "__futex"); ((TAtom "v255"), "__futex"); ((TAtom "v257"), "f"); ((TAtom "v258"), "f"); ((TAtom "v260"), "cxafct"); ((TAtom "v261"), "f"); ((TAtom "v264"), "arg"); ((TAtom "v265"), "cxafct"); ((TAtom "v270"), "__futex"); ((TAtom "v274"), "__oldval"); ((TAtom "v280"), "__oldval"); ((TAtom "v29"), "__futex"); ((TAtom "v292"), "__futex"); ((TAtom "v293"), "__futex"); ((TAtom "v294"), "__private"); ((TAtom "v295"), "cxafct"); ((TAtom "v296"), "arg"); ((TAtom "v297"), "status"); ((TAtom "v30"), "__atg3_old"); ((TAtom "v304"), "__futex"); ((TAtom "v305"), "__atg3_old"); ((TAtom "v306"), "__atg3_old"); ((TAtom "v31"), "__atg3_old"); ((TAtom "v321"), "__futex"); ((TAtom "v322"), "__futex"); ((TAtom "v340"), "new_exitfn_called"); ((TAtom "v342"), "__new_exitfn_called"); ((TAtom "v347"), "listp"); ((TAtom "v348"), "cur"); ((TAtom "v353"), "listp"); ((TAtom "v358"), "cur"); ((TAtom "v363"), "__futex"); ((TAtom "v367"), "__oldval"); ((TAtom "v373"), "__oldval"); ((TAtom "v385"), "__futex"); ((TAtom "v386"), "__futex"); ((TAtom "v387"), "__private"); ((TAtom "v391"), "run_list_atexit"); ((TAtom "v393"), "status"); ((TAtom "v4"), "run_list_atexit"); ((TAtom "v46"), "__futex"); ((TAtom "v47"), "__futex"); ((TAtom "v50"), "self"); ((TAtom "v58"), "run_dtors"); ((TAtom "v6"), "run_dtors"); ((TAtom "v65"), "__futex"); ((TAtom "v66"), "__atg3_old"); ((TAtom "v67"), "__atg3_old"); ((TAtom "v82"), "__futex"); ((TAtom "v83"), "__futex"); ((TAtom "v89"), "listp"); ((TAtom "v90"), "cur"); ((TAtom "v94"), "cur"); ((TAtom "v99"), "__exit_funcs_done")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L101"); (TAtom "L145"); (TAtom "L207"); (TAtom "L272"); (TAtom "L365"); (TAtom "L88")].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__run_exit_handlers") (code_module exitrun_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___run_exit_handlers.

Module fn___GI_exit.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("exit.c", 147%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("exit.c", 150%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "status"); ((TAtom "v2"), "status")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__GI_exit") (code_module exitrun_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___GI_exit.

End ExitRunSrc.
