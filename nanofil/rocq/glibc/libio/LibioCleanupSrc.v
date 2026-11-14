(** These tables connect checked function bodies to C declarations and source lines.
    Names and locations support annotations and diagnostic messages, not soundness premises.
    Natural-loop headers provide optional cuts for symbolic execution; any cut list is sound.
    Computation checks that every recorded block label belongs to the decoded function.
    The code generator reproduces this file from the capture; do not edit it. *)

From Stdlib Require Import String List Bool NArith.
From Glibc Require Import CodePrelude.
Import ListNotations.
Open Scope string_scope.


From Glibc Require Import LibioCleanupCode.
Module LibioCleanupSrc.

Definition file_0 : string := "./libioP.h".

Definition file_1 : string := "genops.c".

Module fn__IO_cleanup.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_1, 886%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_1, 889%N)); ((TAtom "iw_1.L23"), (file_1, 817%N)); ((TAtom "iw_1.L24"), (file_1, 817%N)); ((TAtom "iw_1.L17"), (file_1, 817%N)); ((TAtom "iw_1.L18"), (file_1, 817%N)); ((TAtom "iw_1.L37"), (file_1, 817%N)); ((TAtom "iw_1.L57"), (file_1, 817%N)); ((TAtom "iw_1.L58"), (file_1, 817%N)); ((TAtom "iw_1.L62"), (file_1, 817%N)); ((TAtom "iw_1.L51"), (file_1, 817%N)); ((TAtom "iw_1.L38"), (file_1, 817%N)); ((TAtom "iw_1.L14"), (file_1, 820%N)); ((TAtom "iw_1.L81"), (file_1, 813%N)); ((TAtom "iw_1.L82"), (file_1, 824%N)); ((TAtom "iw_1.L98"), (file_1, 825%N)); ((TAtom "iw_1.L109"), (file_1, 825%N)); ((TAtom "iw_1.L110"), (file_1, 825%N)); ((TAtom "iw_1.L103"), (file_1, 825%N)); ((TAtom "iw_1.L104"), (file_1, 825%N)); ((TAtom "iw_1.L129"), (file_1, 825%N)); ((TAtom "iw_1.L153"), (file_1, 825%N)); ((TAtom "iw_1.L154"), (file_1, 825%N)); ((TAtom "iw_1.L158"), (file_1, 825%N)); ((TAtom "iw_1.L147"), (file_1, 825%N)); ((TAtom "iw_1.L130"), (file_1, 825%N)); ((TAtom "iw_1.L93"), (file_1, 833%N)); ((TAtom "iw_1.L179"), (file_1, 834%N)); ((TAtom "iw_1.L194"), (file_1, 835%N)); ((TAtom "iw_1.L202"), (file_1, 835%N)); ((TAtom "iw_1.L203"), (file_1, 835%N)); ((TAtom "iw_1.L189"), (file_1, 836%N)); ((TAtom "iw_1.L191"), (file_1, 838%N)); ((TAtom "iw_1.L225"), (file_1, 838%N)); ((TAtom "iw_1.L223"), (file_1, 838%N)); ((TAtom "iw_1.L240"), (file_1, 842%N)); ((TAtom "iw_1.L247"), (file_1, 842%N)); ((TAtom "iw_1.L248"), (file_1, 842%N)); ((TAtom "iw_1.L235"), (file_1, 844%N)); ((TAtom "iw_1.L237"), (file_1, 851%N)); ((TAtom "iw_1.iw_1.L10"), (file_0, 1049%N)); ((TAtom "iw_1.iw_1.join"), (file_1, 851%N)); ((TAtom "iw_1.L277"), (file_1, 854%N)); ((TAtom "iw_1.L291"), (file_1, 860%N)); ((TAtom "iw_1.L306"), (file_1, 862%N)); ((TAtom "iw_1.L315"), (file_1, 862%N)); ((TAtom "iw_1.L316"), (file_1, 862%N)); ((TAtom "iw_1.L309"), (file_1, 862%N)); ((TAtom "iw_1.L310"), (file_1, 862%N)); ((TAtom "iw_1.L332"), (file_1, 862%N)); ((TAtom "iw_1.L353"), (file_1, 862%N)); ((TAtom "iw_1.L354"), (file_1, 862%N)); ((TAtom "iw_1.L365"), (file_1, 862%N)); ((TAtom "iw_1.L333"), (file_1, 862%N)); ((TAtom "iw_1.L301"), (file_1, 863%N)); ((TAtom "iw_1.L386"), (file_1, 867%N)); ((TAtom "iw_1.L395"), (file_1, 867%N)); ((TAtom "iw_1.L396"), (file_1, 867%N)); ((TAtom "iw_1.L389"), (file_1, 867%N)); ((TAtom "iw_1.L390"), (file_1, 867%N)); ((TAtom "iw_1.L406"), (file_1, 867%N)); ((TAtom "iw_1.L421"), (file_1, 867%N)); ((TAtom "iw_1.L422"), (file_1, 867%N)); ((TAtom "iw_1.L433"), (file_1, 867%N)); ((TAtom "iw_1.L407"), (file_1, 867%N)); ((TAtom "iw_1.L448"), (file_1, 868%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.iw_1.v0"), "vtable"); ((TAtom "iw_1.iw_1.v13"), "offset"); ((TAtom "iw_1.iw_1.v18"), "vtable"); ((TAtom "iw_1.iw_1.v3"), "vtable"); ((TAtom "iw_1.iw_1.v4"), "ptr"); ((TAtom "iw_1.iw_1.v6"), "ptr"); ((TAtom "iw_1.iw_1.v9"), "offset"); ((TAtom "iw_1.pr.1"), "fp"); ((TAtom "iw_1.pr.2"), "_cleanup_start_doit"); ((TAtom "iw_1.v10"), "_cleanup_routine"); ((TAtom "iw_1.v102"), "__self"); ((TAtom "iw_1.v107"), "__libc_single_threaded_internal"); ((TAtom "iw_1.v11"), "_cleanup_start_doit"); ((TAtom "iw_1.v111"), "fp"); ((TAtom "iw_1.v121"), "fp"); ((TAtom "iw_1.v124"), "fp"); ((TAtom "iw_1.v128"), "__self"); ((TAtom "iw_1.v132"), "fp"); ((TAtom "iw_1.v137"), "__self"); ((TAtom "iw_1.v142"), "fp"); ((TAtom "iw_1.v144"), "__futex"); ((TAtom "iw_1.v149"), "__futex"); ((TAtom "iw_1.v150"), "__atg3_old"); ((TAtom "iw_1.v151"), "__atg3_old"); ((TAtom "iw_1.v16"), "__self"); ((TAtom "iw_1.v166"), "__futex"); ((TAtom "iw_1.v167"), "__futex"); ((TAtom "iw_1.v168"), "fp"); ((TAtom "iw_1.v172"), "__self"); ((TAtom "iw_1.v173"), "fp"); ((TAtom "iw_1.v182"), "fp"); ((TAtom "iw_1.v188"), "fp"); ((TAtom "iw_1.v192"), "legacy"); ((TAtom "iw_1.v196"), "fp"); ((TAtom "iw_1.v204"), "fp"); ((TAtom "iw_1.v21"), "__libc_single_threaded_internal"); ((TAtom "iw_1.v214"), "fp"); ((TAtom "iw_1.v218"), "fp"); ((TAtom "iw_1.v224"), "legacy"); ((TAtom "iw_1.v227"), "fp"); ((TAtom "iw_1.v238"), "legacy"); ((TAtom "iw_1.v243"), "dealloc_buffers"); ((TAtom "iw_1.v249"), "fp"); ((TAtom "iw_1.v255"), "fp"); ((TAtom "iw_1.v258"), "fp"); ((TAtom "iw_1.v261"), "freeres_list"); ((TAtom "iw_1.v263"), "fp"); ((TAtom "iw_1.v264"), "fp"); ((TAtom "iw_1.v266"), "fp"); ((TAtom "iw_1.v269"), "fp"); ((TAtom "iw_1.v275"), "fp"); ((TAtom "iw_1.v280"), "legacy"); ((TAtom "iw_1.v284"), "fp"); ((TAtom "iw_1.v290"), "fp"); ((TAtom "iw_1.v294"), "legacy"); ((TAtom "iw_1.v296"), "fp"); ((TAtom "iw_1.v302"), "fp"); ((TAtom "iw_1.v313"), "__libc_single_threaded_internal"); ((TAtom "iw_1.v317"), "fp"); ((TAtom "iw_1.v325"), "fp"); ((TAtom "iw_1.v329"), "fp"); ((TAtom "iw_1.v335"), "fp"); ((TAtom "iw_1.v341"), "fp"); ((TAtom "iw_1.v346"), "fp"); ((TAtom "iw_1.v348"), "__futex"); ((TAtom "iw_1.v351"), "__futex"); ((TAtom "iw_1.v355"), "__oldval"); ((TAtom "iw_1.v36"), "__self"); ((TAtom "iw_1.v361"), "__oldval"); ((TAtom "iw_1.v373"), "__futex"); ((TAtom "iw_1.v374"), "__futex"); ((TAtom "iw_1.v375"), "__private"); ((TAtom "iw_1.v376"), "fp"); ((TAtom "iw_1.v383"), "fp"); ((TAtom "iw_1.v385"), "fp"); ((TAtom "iw_1.v393"), "__libc_single_threaded_internal"); ((TAtom "iw_1.v4"), "_cleanup_routine"); ((TAtom "iw_1.v419"), "__futex"); ((TAtom "iw_1.v423"), "__oldval"); ((TAtom "iw_1.v429"), "__oldval"); ((TAtom "iw_1.v43"), "__self"); ((TAtom "iw_1.v441"), "__futex"); ((TAtom "iw_1.v442"), "__futex"); ((TAtom "iw_1.v443"), "__private"); ((TAtom "iw_1.v451"), "_cleanup_start_doit"); ((TAtom "iw_1.v455"), "_cleanup_routine"); ((TAtom "iw_1.v53"), "__futex"); ((TAtom "iw_1.v54"), "__atg3_old"); ((TAtom "iw_1.v55"), "__atg3_old"); ((TAtom "iw_1.v70"), "__futex"); ((TAtom "iw_1.v71"), "__futex"); ((TAtom "iw_1.v74"), "__self"); ((TAtom "iw_1.v80"), "_IO_list_all"); ((TAtom "iw_1.v85"), "fp"); ((TAtom "iw_1.v9"), "_cleanup_start_doit"); ((TAtom "iw_1.v90"), "fp"); ((TAtom "iw_1.v94"), "fp"); ((TAtom "v1"), "result"); ((TAtom "v2"), "result")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "iw_1.L353"); (TAtom "iw_1.L421"); (TAtom "iw_1.L81")].

End fn__IO_cleanup.

(** Projection keeps instruction bodies out of the VM code used by the membership check. *)
Definition source_blocks : list (string * option (list name)) := Eval lazy in
  map (fun n => (n,
    match find_direct (TAtom n) libiocleanup_module with
    | Some (Defined f) => Some (map b_label (fn_blocks f))
    | _ => None
    end)) ["_IO_cleanup"].

(** One computation rejects missing functions and stale labels across all tables in this fixture. *)
Lemma labels_valid :
  forallb (fun row =>
  match find (fun entry => String.eqb (fst entry) (fst row)) source_blocks with
  | Some (_, Some labels) =>
      forallb (fun l => existsb (name_eqb l) labels)
        (snd row)
  | _ => false
  end) [("_IO_cleanup", app (map fst fn__IO_cleanup.block_src) fn__IO_cleanup.loop_heads)] = true.
Proof. vm_compute. reflexivity. Qed.

End LibioCleanupSrc.
