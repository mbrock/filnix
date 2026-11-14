(** These tables connect checked function bodies to C declarations and source lines.
    Names and locations support annotations and diagnostic messages, not soundness premises.
    Natural-loop headers provide optional cuts for symbolic execution; any cut list is sound.
    Computation checks that every recorded block label belongs to the decoded function.
    The code generator reproduces this file from the capture; do not edit it. *)

From Stdlib Require Import String List Bool.
From Glibc Require Import CodePrelude LibioFlushCode.
Import ListNotations.
Open Scope string_scope.

Module LibioFlushSrc.

Module fn___GI__IO_flush_all.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("genops.c", 708%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("genops.c", 715%nat)); ((TAtom "L24"), ("genops.c", 716%nat)); ((TAtom "L25"), ("genops.c", 716%nat)); ((TAtom "L18"), ("genops.c", 716%nat)); ((TAtom "L19"), ("genops.c", 716%nat)); ((TAtom "L38"), ("genops.c", 716%nat)); ((TAtom "L58"), ("genops.c", 716%nat)); ((TAtom "L59"), ("genops.c", 716%nat)); ((TAtom "L63"), ("genops.c", 716%nat)); ((TAtom "L52"), ("genops.c", 716%nat)); ((TAtom "L39"), ("genops.c", 716%nat)); ((TAtom "L15"), ("genops.c", 719%nat)); ((TAtom "L82"), ("genops.c", 712%nat)); ((TAtom "L83"), ("genops.c", 721%nat)); ((TAtom "L99"), ("genops.c", 722%nat)); ((TAtom "L110"), ("genops.c", 722%nat)); ((TAtom "L111"), ("genops.c", 722%nat)); ((TAtom "L104"), ("genops.c", 722%nat)); ((TAtom "L105"), ("genops.c", 722%nat)); ((TAtom "L130"), ("genops.c", 722%nat)); ((TAtom "L154"), ("genops.c", 722%nat)); ((TAtom "L155"), ("genops.c", 722%nat)); ((TAtom "L159"), ("genops.c", 722%nat)); ((TAtom "L148"), ("genops.c", 722%nat)); ((TAtom "L131"), ("genops.c", 722%nat)); ((TAtom "L94"), ("genops.c", 726%nat)); ((TAtom "L180"), ("genops.c", 728%nat)); ((TAtom "L197"), ("genops.c", 728%nat)); ((TAtom "L198"), ("genops.c", 728%nat)); ((TAtom "L213"), ("genops.c", 728%nat)); ((TAtom "L221"), ("genops.c", 728%nat)); ((TAtom "L211"), ("genops.c", 728%nat)); ((TAtom "L240"), ("genops.c", 728%nat)); ((TAtom "iw_1.L10"), ("./libioP.h", 1049%nat)); ((TAtom "iw_1.join"), ("genops.c", 728%nat)); ((TAtom "L241"), ("genops.c", 728%nat)); ((TAtom "L191"), ("genops.c", 728%nat)); ((TAtom "L192"), ("genops.c", 711%nat)); ((TAtom "L263"), ("genops.c", 735%nat)); ((TAtom "L269"), ("genops.c", 735%nat)); ((TAtom "L270"), ("genops.c", 735%nat)); ((TAtom "L285"), ("genops.c", 735%nat)); ((TAtom "L293"), ("genops.c", 735%nat)); ((TAtom "L264"), ("genops.c", 735%nat)); ((TAtom "L313"), ("genops.c", 735%nat)); ((TAtom "iw_2.L10"), ("./libioP.h", 1049%nat)); ((TAtom "iw_2.join"), ("genops.c", 735%nat)); ((TAtom "L314"), ("genops.c", 735%nat)); ((TAtom "L257"), ("genops.c", 735%nat)); ((TAtom "L182"), ("genops.c", 711%nat)); ((TAtom "L334"), ("genops.c", 744%nat)); ((TAtom "L343"), ("genops.c", 744%nat)); ((TAtom "L344"), ("genops.c", 744%nat)); ((TAtom "L337"), ("genops.c", 744%nat)); ((TAtom "L338"), ("genops.c", 744%nat)); ((TAtom "L360"), ("genops.c", 744%nat)); ((TAtom "L381"), ("genops.c", 744%nat)); ((TAtom "L382"), ("genops.c", 744%nat)); ((TAtom "L393"), ("genops.c", 744%nat)); ((TAtom "L361"), ("genops.c", 744%nat)); ((TAtom "L329"), ("genops.c", 745%nat)); ((TAtom "L414"), ("genops.c", 749%nat)); ((TAtom "L423"), ("genops.c", 749%nat)); ((TAtom "L424"), ("genops.c", 749%nat)); ((TAtom "L417"), ("genops.c", 749%nat)); ((TAtom "L418"), ("genops.c", 749%nat)); ((TAtom "L434"), ("genops.c", 749%nat)); ((TAtom "L449"), ("genops.c", 749%nat)); ((TAtom "L450"), ("genops.c", 749%nat)); ((TAtom "L461"), ("genops.c", 749%nat)); ((TAtom "L435"), ("genops.c", 749%nat)); ((TAtom "L476"), ("genops.c", 750%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "vtable"); ((TAtom "iw_1.v13"), "offset"); ((TAtom "iw_1.v18"), "vtable"); ((TAtom "iw_1.v3"), "vtable"); ((TAtom "iw_1.v4"), "ptr"); ((TAtom "iw_1.v6"), "ptr"); ((TAtom "iw_1.v9"), "offset"); ((TAtom "iw_2.v0"), "vtable"); ((TAtom "iw_2.v13"), "offset"); ((TAtom "iw_2.v18"), "vtable"); ((TAtom "iw_2.v3"), "vtable"); ((TAtom "iw_2.v4"), "ptr"); ((TAtom "iw_2.v6"), "ptr"); ((TAtom "iw_2.v9"), "offset"); ((TAtom "pr.1"), "result"); ((TAtom "pr.2"), "result"); ((TAtom "pr.3"), "result"); ((TAtom "pr.4"), "result"); ((TAtom "pr.5"), "fp"); ((TAtom "pr.6"), "_cleanup_start_doit"); ((TAtom "v10"), "_cleanup_start_doit"); ((TAtom "v103"), "__self"); ((TAtom "v108"), "__libc_single_threaded_internal"); ((TAtom "v11"), "_cleanup_routine"); ((TAtom "v112"), "fp"); ((TAtom "v12"), "_cleanup_start_doit"); ((TAtom "v122"), "fp"); ((TAtom "v125"), "fp"); ((TAtom "v129"), "__self"); ((TAtom "v133"), "fp"); ((TAtom "v138"), "__self"); ((TAtom "v143"), "fp"); ((TAtom "v145"), "__futex"); ((TAtom "v150"), "__futex"); ((TAtom "v151"), "__atg3_old"); ((TAtom "v152"), "__atg3_old"); ((TAtom "v167"), "__futex"); ((TAtom "v168"), "__futex"); ((TAtom "v169"), "fp"); ((TAtom "v17"), "__self"); ((TAtom "v173"), "__self"); ((TAtom "v174"), "fp"); ((TAtom "v183"), "fp"); ((TAtom "v193"), "fp"); ((TAtom "v199"), "fp"); ((TAtom "v202"), "fp"); ((TAtom "v215"), "fp"); ((TAtom "v22"), "__libc_single_threaded_internal"); ((TAtom "v223"), "fp"); ((TAtom "v228"), "fp"); ((TAtom "v242"), "fp"); ((TAtom "v248"), "fp"); ((TAtom "v255"), "result"); ((TAtom "v259"), "fp"); ((TAtom "v265"), "fp"); ((TAtom "v271"), "fp"); ((TAtom "v274"), "fp"); ((TAtom "v287"), "fp"); ((TAtom "v295"), "fp"); ((TAtom "v299"), "fp"); ((TAtom "v315"), "fp"); ((TAtom "v321"), "fp"); ((TAtom "v326"), "result"); ((TAtom "v330"), "fp"); ((TAtom "v341"), "__libc_single_threaded_internal"); ((TAtom "v345"), "fp"); ((TAtom "v353"), "fp"); ((TAtom "v357"), "fp"); ((TAtom "v363"), "fp"); ((TAtom "v369"), "fp"); ((TAtom "v37"), "__self"); ((TAtom "v374"), "fp"); ((TAtom "v376"), "__futex"); ((TAtom "v379"), "__futex"); ((TAtom "v383"), "__oldval"); ((TAtom "v389"), "__oldval"); ((TAtom "v401"), "__futex"); ((TAtom "v402"), "__futex"); ((TAtom "v403"), "__private"); ((TAtom "v404"), "fp"); ((TAtom "v411"), "fp"); ((TAtom "v413"), "fp"); ((TAtom "v421"), "__libc_single_threaded_internal"); ((TAtom "v44"), "__self"); ((TAtom "v447"), "__futex"); ((TAtom "v451"), "__oldval"); ((TAtom "v457"), "__oldval"); ((TAtom "v469"), "__futex"); ((TAtom "v470"), "__futex"); ((TAtom "v471"), "__private"); ((TAtom "v479"), "_cleanup_start_doit"); ((TAtom "v483"), "_cleanup_routine"); ((TAtom "v486"), "result"); ((TAtom "v5"), "_cleanup_routine"); ((TAtom "v54"), "__futex"); ((TAtom "v55"), "__atg3_old"); ((TAtom "v56"), "__atg3_old"); ((TAtom "v71"), "__futex"); ((TAtom "v72"), "__futex"); ((TAtom "v75"), "__self"); ((TAtom "v81"), "_IO_list_all"); ((TAtom "v86"), "fp"); ((TAtom "v91"), "fp"); ((TAtom "v95"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L381"); (TAtom "L449"); (TAtom "L82")].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__GI__IO_flush_all") (code_module libioflush_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___GI__IO_flush_all.

End LibioFlushSrc.
