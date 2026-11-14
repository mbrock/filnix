(** These tables connect checked function bodies to C declarations and source lines.
    Names and locations support annotations and diagnostic messages, not soundness premises.
    Natural-loop headers provide optional cuts for symbolic execution; any cut list is sound.
    Computation checks that every recorded block label belongs to the decoded function.
    The code generator reproduces this file from the capture; do not edit it. *)

From Stdlib Require Import String List Bool.
From Glibc Require Import CodePrelude LibioCleanupCode.
Import ListNotations.
Open Scope string_scope.

Module LibioCleanupSrc.

Module fn__IO_cleanup.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("genops.c", 886%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("genops.c", 889%nat)); ((TAtom "iw_1.L23"), ("genops.c", 817%nat)); ((TAtom "iw_1.L24"), ("genops.c", 817%nat)); ((TAtom "iw_1.L17"), ("genops.c", 817%nat)); ((TAtom "iw_1.L18"), ("genops.c", 817%nat)); ((TAtom "iw_1.L37"), ("genops.c", 817%nat)); ((TAtom "iw_1.L57"), ("genops.c", 817%nat)); ((TAtom "iw_1.L58"), ("genops.c", 817%nat)); ((TAtom "iw_1.L62"), ("genops.c", 817%nat)); ((TAtom "iw_1.L51"), ("genops.c", 817%nat)); ((TAtom "iw_1.L38"), ("genops.c", 817%nat)); ((TAtom "iw_1.L14"), ("genops.c", 820%nat)); ((TAtom "iw_1.L81"), ("genops.c", 813%nat)); ((TAtom "iw_1.L82"), ("genops.c", 824%nat)); ((TAtom "iw_1.L98"), ("genops.c", 825%nat)); ((TAtom "iw_1.L109"), ("genops.c", 825%nat)); ((TAtom "iw_1.L110"), ("genops.c", 825%nat)); ((TAtom "iw_1.L103"), ("genops.c", 825%nat)); ((TAtom "iw_1.L104"), ("genops.c", 825%nat)); ((TAtom "iw_1.L129"), ("genops.c", 825%nat)); ((TAtom "iw_1.L153"), ("genops.c", 825%nat)); ((TAtom "iw_1.L154"), ("genops.c", 825%nat)); ((TAtom "iw_1.L158"), ("genops.c", 825%nat)); ((TAtom "iw_1.L147"), ("genops.c", 825%nat)); ((TAtom "iw_1.L130"), ("genops.c", 825%nat)); ((TAtom "iw_1.L93"), ("genops.c", 833%nat)); ((TAtom "iw_1.L179"), ("genops.c", 834%nat)); ((TAtom "iw_1.L194"), ("genops.c", 835%nat)); ((TAtom "iw_1.L202"), ("genops.c", 835%nat)); ((TAtom "iw_1.L203"), ("genops.c", 835%nat)); ((TAtom "iw_1.L189"), ("genops.c", 836%nat)); ((TAtom "iw_1.L191"), ("genops.c", 838%nat)); ((TAtom "iw_1.L225"), ("genops.c", 838%nat)); ((TAtom "iw_1.L223"), ("genops.c", 838%nat)); ((TAtom "iw_1.L240"), ("genops.c", 842%nat)); ((TAtom "iw_1.L247"), ("genops.c", 842%nat)); ((TAtom "iw_1.L248"), ("genops.c", 842%nat)); ((TAtom "iw_1.L235"), ("genops.c", 844%nat)); ((TAtom "iw_1.L237"), ("genops.c", 851%nat)); ((TAtom "iw_1.iw_1.L10"), ("./libioP.h", 1049%nat)); ((TAtom "iw_1.iw_1.join"), ("genops.c", 851%nat)); ((TAtom "iw_1.L277"), ("genops.c", 854%nat)); ((TAtom "iw_1.L291"), ("genops.c", 860%nat)); ((TAtom "iw_1.L306"), ("genops.c", 862%nat)); ((TAtom "iw_1.L315"), ("genops.c", 862%nat)); ((TAtom "iw_1.L316"), ("genops.c", 862%nat)); ((TAtom "iw_1.L309"), ("genops.c", 862%nat)); ((TAtom "iw_1.L310"), ("genops.c", 862%nat)); ((TAtom "iw_1.L332"), ("genops.c", 862%nat)); ((TAtom "iw_1.L353"), ("genops.c", 862%nat)); ((TAtom "iw_1.L354"), ("genops.c", 862%nat)); ((TAtom "iw_1.L365"), ("genops.c", 862%nat)); ((TAtom "iw_1.L333"), ("genops.c", 862%nat)); ((TAtom "iw_1.L301"), ("genops.c", 863%nat)); ((TAtom "iw_1.L386"), ("genops.c", 867%nat)); ((TAtom "iw_1.L395"), ("genops.c", 867%nat)); ((TAtom "iw_1.L396"), ("genops.c", 867%nat)); ((TAtom "iw_1.L389"), ("genops.c", 867%nat)); ((TAtom "iw_1.L390"), ("genops.c", 867%nat)); ((TAtom "iw_1.L406"), ("genops.c", 867%nat)); ((TAtom "iw_1.L421"), ("genops.c", 867%nat)); ((TAtom "iw_1.L422"), ("genops.c", 867%nat)); ((TAtom "iw_1.L433"), ("genops.c", 867%nat)); ((TAtom "iw_1.L407"), ("genops.c", 867%nat)); ((TAtom "iw_1.L448"), ("genops.c", 868%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.iw_1.v0"), "vtable"); ((TAtom "iw_1.iw_1.v13"), "offset"); ((TAtom "iw_1.iw_1.v18"), "vtable"); ((TAtom "iw_1.iw_1.v3"), "vtable"); ((TAtom "iw_1.iw_1.v4"), "ptr"); ((TAtom "iw_1.iw_1.v6"), "ptr"); ((TAtom "iw_1.iw_1.v9"), "offset"); ((TAtom "iw_1.pr.1"), "fp"); ((TAtom "iw_1.pr.2"), "_cleanup_start_doit"); ((TAtom "iw_1.v10"), "_cleanup_routine"); ((TAtom "iw_1.v102"), "__self"); ((TAtom "iw_1.v107"), "__libc_single_threaded_internal"); ((TAtom "iw_1.v11"), "_cleanup_start_doit"); ((TAtom "iw_1.v111"), "fp"); ((TAtom "iw_1.v121"), "fp"); ((TAtom "iw_1.v124"), "fp"); ((TAtom "iw_1.v128"), "__self"); ((TAtom "iw_1.v132"), "fp"); ((TAtom "iw_1.v137"), "__self"); ((TAtom "iw_1.v142"), "fp"); ((TAtom "iw_1.v144"), "__futex"); ((TAtom "iw_1.v149"), "__futex"); ((TAtom "iw_1.v150"), "__atg3_old"); ((TAtom "iw_1.v151"), "__atg3_old"); ((TAtom "iw_1.v16"), "__self"); ((TAtom "iw_1.v166"), "__futex"); ((TAtom "iw_1.v167"), "__futex"); ((TAtom "iw_1.v168"), "fp"); ((TAtom "iw_1.v172"), "__self"); ((TAtom "iw_1.v173"), "fp"); ((TAtom "iw_1.v182"), "fp"); ((TAtom "iw_1.v188"), "fp"); ((TAtom "iw_1.v192"), "legacy"); ((TAtom "iw_1.v196"), "fp"); ((TAtom "iw_1.v204"), "fp"); ((TAtom "iw_1.v21"), "__libc_single_threaded_internal"); ((TAtom "iw_1.v214"), "fp"); ((TAtom "iw_1.v218"), "fp"); ((TAtom "iw_1.v224"), "legacy"); ((TAtom "iw_1.v227"), "fp"); ((TAtom "iw_1.v238"), "legacy"); ((TAtom "iw_1.v243"), "dealloc_buffers"); ((TAtom "iw_1.v249"), "fp"); ((TAtom "iw_1.v255"), "fp"); ((TAtom "iw_1.v258"), "fp"); ((TAtom "iw_1.v261"), "freeres_list"); ((TAtom "iw_1.v263"), "fp"); ((TAtom "iw_1.v264"), "fp"); ((TAtom "iw_1.v266"), "fp"); ((TAtom "iw_1.v269"), "fp"); ((TAtom "iw_1.v275"), "fp"); ((TAtom "iw_1.v280"), "legacy"); ((TAtom "iw_1.v284"), "fp"); ((TAtom "iw_1.v290"), "fp"); ((TAtom "iw_1.v294"), "legacy"); ((TAtom "iw_1.v296"), "fp"); ((TAtom "iw_1.v302"), "fp"); ((TAtom "iw_1.v313"), "__libc_single_threaded_internal"); ((TAtom "iw_1.v317"), "fp"); ((TAtom "iw_1.v325"), "fp"); ((TAtom "iw_1.v329"), "fp"); ((TAtom "iw_1.v335"), "fp"); ((TAtom "iw_1.v341"), "fp"); ((TAtom "iw_1.v346"), "fp"); ((TAtom "iw_1.v348"), "__futex"); ((TAtom "iw_1.v351"), "__futex"); ((TAtom "iw_1.v355"), "__oldval"); ((TAtom "iw_1.v36"), "__self"); ((TAtom "iw_1.v361"), "__oldval"); ((TAtom "iw_1.v373"), "__futex"); ((TAtom "iw_1.v374"), "__futex"); ((TAtom "iw_1.v375"), "__private"); ((TAtom "iw_1.v376"), "fp"); ((TAtom "iw_1.v383"), "fp"); ((TAtom "iw_1.v385"), "fp"); ((TAtom "iw_1.v393"), "__libc_single_threaded_internal"); ((TAtom "iw_1.v4"), "_cleanup_routine"); ((TAtom "iw_1.v419"), "__futex"); ((TAtom "iw_1.v423"), "__oldval"); ((TAtom "iw_1.v429"), "__oldval"); ((TAtom "iw_1.v43"), "__self"); ((TAtom "iw_1.v441"), "__futex"); ((TAtom "iw_1.v442"), "__futex"); ((TAtom "iw_1.v443"), "__private"); ((TAtom "iw_1.v451"), "_cleanup_start_doit"); ((TAtom "iw_1.v455"), "_cleanup_routine"); ((TAtom "iw_1.v53"), "__futex"); ((TAtom "iw_1.v54"), "__atg3_old"); ((TAtom "iw_1.v55"), "__atg3_old"); ((TAtom "iw_1.v70"), "__futex"); ((TAtom "iw_1.v71"), "__futex"); ((TAtom "iw_1.v74"), "__self"); ((TAtom "iw_1.v80"), "_IO_list_all"); ((TAtom "iw_1.v85"), "fp"); ((TAtom "iw_1.v9"), "_cleanup_start_doit"); ((TAtom "iw_1.v90"), "fp"); ((TAtom "iw_1.v94"), "fp"); ((TAtom "v1"), "result"); ((TAtom "v2"), "result")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "iw_1.L353"); (TAtom "iw_1.L421"); (TAtom "iw_1.L81")].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "_IO_cleanup") (code_module libiocleanup_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn__IO_cleanup.

End LibioCleanupSrc.
