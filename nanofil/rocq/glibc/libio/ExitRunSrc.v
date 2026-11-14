(** These tables connect checked function bodies to C declarations and source lines.
    Names and locations support annotations and diagnostic messages, not soundness premises.
    Natural-loop headers provide optional cuts for symbolic execution; any cut list is sound.
    Computation checks that every recorded block label belongs to the decoded function.
    The code generator reproduces this file from the capture; do not edit it. *)

From Stdlib Require Import String List Bool NArith.
From Glibc Require Import CodePrelude.
Import ListNotations.
Open Scope string_scope.


From Glibc Require Import ExitRunCode.
Module ExitRunSrc.

Definition file_0 : string := "exit.c".

Module fn___run_exit_handlers.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_0, 42%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_0, 48%N)); ((TAtom "L13"), (file_0, 48%N)); ((TAtom "L33"), (file_0, 48%N)); ((TAtom "L34"), (file_0, 48%N)); ((TAtom "L38"), (file_0, 48%N)); ((TAtom "L27"), (file_0, 48%N)); ((TAtom "L15"), (file_0, 48%N)); ((TAtom "L55"), (file_0, 52%N)); ((TAtom "L57"), (file_0, 54%N)); ((TAtom "L69"), (file_0, 54%N)); ((TAtom "L70"), (file_0, 54%N)); ((TAtom "L74"), (file_0, 54%N)); ((TAtom "L88"), (file_0, 65%N)); ((TAtom "L91"), (file_0, 71%N)); ((TAtom "L101"), (file_0, 75%N)); ((TAtom "L102"), (file_0, 77%N)); ((TAtom "L130"), (file_0, 91%N)); ((TAtom "L145"), (file_0, 96%N)); ((TAtom "L146"), (file_0, 96%N)); ((TAtom "L157"), (file_0, 96%N)); ((TAtom "L152"), (file_0, 97%N)); ((TAtom "L181"), (file_0, 98%N)); ((TAtom "L182"), (file_0, 98%N)); ((TAtom "L186"), (file_0, 98%N)); ((TAtom "L196"), (file_0, 101%N)); ((TAtom "L207"), (file_0, 105%N)); ((TAtom "L208"), (file_0, 105%N)); ((TAtom "L219"), (file_0, 105%N)); ((TAtom "L214"), (file_0, 106%N)); ((TAtom "L241"), (file_0, 107%N)); ((TAtom "L242"), (file_0, 107%N)); ((TAtom "L246"), (file_0, 107%N)); ((TAtom "L256"), (file_0, 112%N)); ((TAtom "L272"), (file_0, 118%N)); ((TAtom "L273"), (file_0, 118%N)); ((TAtom "L284"), (file_0, 118%N)); ((TAtom "L279"), (file_0, 119%N)); ((TAtom "L308"), (file_0, 120%N)); ((TAtom "L309"), (file_0, 120%N)); ((TAtom "L313"), (file_0, 120%N)); ((TAtom "L325"), (file_0, 80%N)); ((TAtom "L328"), (file_0, 80%N)); ((TAtom "L330"), (file_0, 80%N)); ((TAtom "L326"), (file_0, 80%N)); ((TAtom "L332"), (file_0, 80%N)); ((TAtom "L334"), (file_0, 80%N)); ((TAtom "L123"), (file_0, 124%N)); ((TAtom "L103"), (file_0, 130%N)); ((TAtom "L350"), (file_0, 134%N)); ((TAtom "L365"), (file_0, 137%N)); ((TAtom "L366"), (file_0, 137%N)); ((TAtom "L377"), (file_0, 137%N)); ((TAtom "L372"), (file_0, 139%N)); ((TAtom "L388"), (file_0, 140%N)); ((TAtom "L390"), (file_0, 143%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "status"); ((TAtom "v104"), "cur"); ((TAtom "v109"), "cur"); ((TAtom "v111"), "cur"); ((TAtom "v116"), "f"); ((TAtom "v119"), "__new_exitfn_called"); ((TAtom "v12"), "self"); ((TAtom "v120"), "f"); ((TAtom "v131"), "f"); ((TAtom "v133"), "onfct"); ((TAtom "v134"), "f"); ((TAtom "v137"), "arg"); ((TAtom "v138"), "onfct"); ((TAtom "v143"), "__futex"); ((TAtom "v147"), "__oldval"); ((TAtom "v153"), "__oldval"); ((TAtom "v165"), "__futex"); ((TAtom "v166"), "__futex"); ((TAtom "v167"), "__private"); ((TAtom "v168"), "onfct"); ((TAtom "v169"), "status"); ((TAtom "v170"), "arg"); ((TAtom "v177"), "__futex"); ((TAtom "v178"), "__atg3_old"); ((TAtom "v179"), "__atg3_old"); ((TAtom "v19"), "self"); ((TAtom "v194"), "__futex"); ((TAtom "v195"), "__futex"); ((TAtom "v197"), "f"); ((TAtom "v199"), "atfct"); ((TAtom "v2"), "listp"); ((TAtom "v200"), "atfct"); ((TAtom "v205"), "__futex"); ((TAtom "v209"), "__oldval"); ((TAtom "v215"), "__oldval"); ((TAtom "v227"), "__futex"); ((TAtom "v228"), "__futex"); ((TAtom "v229"), "__private"); ((TAtom "v230"), "atfct"); ((TAtom "v237"), "__futex"); ((TAtom "v238"), "__atg3_old"); ((TAtom "v239"), "__atg3_old"); ((TAtom "v254"), "__futex"); ((TAtom "v255"), "__futex"); ((TAtom "v257"), "f"); ((TAtom "v258"), "f"); ((TAtom "v260"), "cxafct"); ((TAtom "v261"), "f"); ((TAtom "v264"), "arg"); ((TAtom "v265"), "cxafct"); ((TAtom "v270"), "__futex"); ((TAtom "v274"), "__oldval"); ((TAtom "v280"), "__oldval"); ((TAtom "v29"), "__futex"); ((TAtom "v292"), "__futex"); ((TAtom "v293"), "__futex"); ((TAtom "v294"), "__private"); ((TAtom "v295"), "cxafct"); ((TAtom "v296"), "arg"); ((TAtom "v297"), "status"); ((TAtom "v30"), "__atg3_old"); ((TAtom "v304"), "__futex"); ((TAtom "v305"), "__atg3_old"); ((TAtom "v306"), "__atg3_old"); ((TAtom "v31"), "__atg3_old"); ((TAtom "v321"), "__futex"); ((TAtom "v322"), "__futex"); ((TAtom "v340"), "new_exitfn_called"); ((TAtom "v342"), "__new_exitfn_called"); ((TAtom "v347"), "listp"); ((TAtom "v348"), "cur"); ((TAtom "v353"), "listp"); ((TAtom "v358"), "cur"); ((TAtom "v363"), "__futex"); ((TAtom "v367"), "__oldval"); ((TAtom "v373"), "__oldval"); ((TAtom "v385"), "__futex"); ((TAtom "v386"), "__futex"); ((TAtom "v387"), "__private"); ((TAtom "v391"), "run_list_atexit"); ((TAtom "v393"), "status"); ((TAtom "v4"), "run_list_atexit"); ((TAtom "v46"), "__futex"); ((TAtom "v47"), "__futex"); ((TAtom "v50"), "self"); ((TAtom "v58"), "run_dtors"); ((TAtom "v6"), "run_dtors"); ((TAtom "v65"), "__futex"); ((TAtom "v66"), "__atg3_old"); ((TAtom "v67"), "__atg3_old"); ((TAtom "v82"), "__futex"); ((TAtom "v83"), "__futex"); ((TAtom "v89"), "listp"); ((TAtom "v90"), "cur"); ((TAtom "v94"), "cur"); ((TAtom "v99"), "__exit_funcs_done")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L101"); (TAtom "L145"); (TAtom "L207"); (TAtom "L272"); (TAtom "L365"); (TAtom "L88")].

End fn___run_exit_handlers.

Module fn___GI_exit.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_0, 147%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_0, 150%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "status"); ((TAtom "v2"), "status")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

End fn___GI_exit.

(** Projection keeps instruction bodies out of the VM code used by the membership check. *)
Definition source_blocks : list (string * option (list name)) := Eval lazy in
  map (fun n => (n,
    match find_direct (TAtom n) exitrun_module with
    | Some (Defined f) => Some (map b_label (fn_blocks f))
    | _ => None
    end)) ["__run_exit_handlers"; "__GI_exit"].

(** One computation rejects missing functions and stale labels across all tables in this fixture. *)
Lemma labels_valid :
  forallb (fun row =>
  match find (fun entry => String.eqb (fst entry) (fst row)) source_blocks with
  | Some (_, Some labels) =>
      forallb (fun l => existsb (name_eqb l) labels)
        (snd row)
  | _ => false
  end) [("__run_exit_handlers", app (map fst fn___run_exit_handlers.block_src) fn___run_exit_handlers.loop_heads); ("__GI_exit", app (map fst fn___GI_exit.block_src) fn___GI_exit.loop_heads)] = true.
Proof. vm_compute. reflexivity. Qed.

End ExitRunSrc.
