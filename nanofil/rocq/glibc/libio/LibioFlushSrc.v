(** These tables connect checked function bodies to C declarations and source lines.
    Names and locations support annotations and diagnostic messages, not soundness premises.
    Natural-loop headers provide optional cuts for symbolic execution; any cut list is sound.
    Computation checks that every recorded block label belongs to the decoded function.
    The code generator reproduces this file from the capture; do not edit it. *)

From Stdlib Require Import String List Bool NArith.
From Glibc Require Import CodePrelude.
Import ListNotations.
Open Scope string_scope.


From Glibc Require Import LibioFlushCode.
Module LibioFlushSrc.

Definition file_0 : string := "./libioP.h".

Definition file_1 : string := "genops.c".

Module fn___GI__IO_flush_all.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_1, 708%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_1, 715%N)); ((TAtom "L24"), (file_1, 716%N)); ((TAtom "L25"), (file_1, 716%N)); ((TAtom "L18"), (file_1, 716%N)); ((TAtom "L19"), (file_1, 716%N)); ((TAtom "L38"), (file_1, 716%N)); ((TAtom "L58"), (file_1, 716%N)); ((TAtom "L59"), (file_1, 716%N)); ((TAtom "L63"), (file_1, 716%N)); ((TAtom "L52"), (file_1, 716%N)); ((TAtom "L39"), (file_1, 716%N)); ((TAtom "L15"), (file_1, 719%N)); ((TAtom "L82"), (file_1, 712%N)); ((TAtom "L83"), (file_1, 721%N)); ((TAtom "L99"), (file_1, 722%N)); ((TAtom "L110"), (file_1, 722%N)); ((TAtom "L111"), (file_1, 722%N)); ((TAtom "L104"), (file_1, 722%N)); ((TAtom "L105"), (file_1, 722%N)); ((TAtom "L130"), (file_1, 722%N)); ((TAtom "L154"), (file_1, 722%N)); ((TAtom "L155"), (file_1, 722%N)); ((TAtom "L159"), (file_1, 722%N)); ((TAtom "L148"), (file_1, 722%N)); ((TAtom "L131"), (file_1, 722%N)); ((TAtom "L94"), (file_1, 726%N)); ((TAtom "L180"), (file_1, 728%N)); ((TAtom "L197"), (file_1, 728%N)); ((TAtom "L198"), (file_1, 728%N)); ((TAtom "L213"), (file_1, 728%N)); ((TAtom "L221"), (file_1, 728%N)); ((TAtom "L211"), (file_1, 728%N)); ((TAtom "L240"), (file_1, 728%N)); ((TAtom "iw_1.L10"), (file_0, 1049%N)); ((TAtom "iw_1.join"), (file_1, 728%N)); ((TAtom "L241"), (file_1, 728%N)); ((TAtom "L191"), (file_1, 728%N)); ((TAtom "L192"), (file_1, 711%N)); ((TAtom "L263"), (file_1, 735%N)); ((TAtom "L269"), (file_1, 735%N)); ((TAtom "L270"), (file_1, 735%N)); ((TAtom "L285"), (file_1, 735%N)); ((TAtom "L293"), (file_1, 735%N)); ((TAtom "L264"), (file_1, 735%N)); ((TAtom "L313"), (file_1, 735%N)); ((TAtom "iw_2.L10"), (file_0, 1049%N)); ((TAtom "iw_2.join"), (file_1, 735%N)); ((TAtom "L314"), (file_1, 735%N)); ((TAtom "L257"), (file_1, 735%N)); ((TAtom "L182"), (file_1, 711%N)); ((TAtom "L334"), (file_1, 744%N)); ((TAtom "L343"), (file_1, 744%N)); ((TAtom "L344"), (file_1, 744%N)); ((TAtom "L337"), (file_1, 744%N)); ((TAtom "L338"), (file_1, 744%N)); ((TAtom "L360"), (file_1, 744%N)); ((TAtom "L381"), (file_1, 744%N)); ((TAtom "L382"), (file_1, 744%N)); ((TAtom "L393"), (file_1, 744%N)); ((TAtom "L361"), (file_1, 744%N)); ((TAtom "L329"), (file_1, 745%N)); ((TAtom "L414"), (file_1, 749%N)); ((TAtom "L423"), (file_1, 749%N)); ((TAtom "L424"), (file_1, 749%N)); ((TAtom "L417"), (file_1, 749%N)); ((TAtom "L418"), (file_1, 749%N)); ((TAtom "L434"), (file_1, 749%N)); ((TAtom "L449"), (file_1, 749%N)); ((TAtom "L450"), (file_1, 749%N)); ((TAtom "L461"), (file_1, 749%N)); ((TAtom "L435"), (file_1, 749%N)); ((TAtom "L476"), (file_1, 750%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "vtable"); ((TAtom "iw_1.v13"), "offset"); ((TAtom "iw_1.v18"), "vtable"); ((TAtom "iw_1.v3"), "vtable"); ((TAtom "iw_1.v4"), "ptr"); ((TAtom "iw_1.v6"), "ptr"); ((TAtom "iw_1.v9"), "offset"); ((TAtom "iw_2.v0"), "vtable"); ((TAtom "iw_2.v13"), "offset"); ((TAtom "iw_2.v18"), "vtable"); ((TAtom "iw_2.v3"), "vtable"); ((TAtom "iw_2.v4"), "ptr"); ((TAtom "iw_2.v6"), "ptr"); ((TAtom "iw_2.v9"), "offset"); ((TAtom "pr.1"), "result"); ((TAtom "pr.2"), "result"); ((TAtom "pr.3"), "result"); ((TAtom "pr.4"), "result"); ((TAtom "pr.5"), "fp"); ((TAtom "pr.6"), "_cleanup_start_doit"); ((TAtom "v10"), "_cleanup_start_doit"); ((TAtom "v103"), "__self"); ((TAtom "v108"), "__libc_single_threaded_internal"); ((TAtom "v11"), "_cleanup_routine"); ((TAtom "v112"), "fp"); ((TAtom "v12"), "_cleanup_start_doit"); ((TAtom "v122"), "fp"); ((TAtom "v125"), "fp"); ((TAtom "v129"), "__self"); ((TAtom "v133"), "fp"); ((TAtom "v138"), "__self"); ((TAtom "v143"), "fp"); ((TAtom "v145"), "__futex"); ((TAtom "v150"), "__futex"); ((TAtom "v151"), "__atg3_old"); ((TAtom "v152"), "__atg3_old"); ((TAtom "v167"), "__futex"); ((TAtom "v168"), "__futex"); ((TAtom "v169"), "fp"); ((TAtom "v17"), "__self"); ((TAtom "v173"), "__self"); ((TAtom "v174"), "fp"); ((TAtom "v183"), "fp"); ((TAtom "v193"), "fp"); ((TAtom "v199"), "fp"); ((TAtom "v202"), "fp"); ((TAtom "v215"), "fp"); ((TAtom "v22"), "__libc_single_threaded_internal"); ((TAtom "v223"), "fp"); ((TAtom "v228"), "fp"); ((TAtom "v242"), "fp"); ((TAtom "v248"), "fp"); ((TAtom "v255"), "result"); ((TAtom "v259"), "fp"); ((TAtom "v265"), "fp"); ((TAtom "v271"), "fp"); ((TAtom "v274"), "fp"); ((TAtom "v287"), "fp"); ((TAtom "v295"), "fp"); ((TAtom "v299"), "fp"); ((TAtom "v315"), "fp"); ((TAtom "v321"), "fp"); ((TAtom "v326"), "result"); ((TAtom "v330"), "fp"); ((TAtom "v341"), "__libc_single_threaded_internal"); ((TAtom "v345"), "fp"); ((TAtom "v353"), "fp"); ((TAtom "v357"), "fp"); ((TAtom "v363"), "fp"); ((TAtom "v369"), "fp"); ((TAtom "v37"), "__self"); ((TAtom "v374"), "fp"); ((TAtom "v376"), "__futex"); ((TAtom "v379"), "__futex"); ((TAtom "v383"), "__oldval"); ((TAtom "v389"), "__oldval"); ((TAtom "v401"), "__futex"); ((TAtom "v402"), "__futex"); ((TAtom "v403"), "__private"); ((TAtom "v404"), "fp"); ((TAtom "v411"), "fp"); ((TAtom "v413"), "fp"); ((TAtom "v421"), "__libc_single_threaded_internal"); ((TAtom "v44"), "__self"); ((TAtom "v447"), "__futex"); ((TAtom "v451"), "__oldval"); ((TAtom "v457"), "__oldval"); ((TAtom "v469"), "__futex"); ((TAtom "v470"), "__futex"); ((TAtom "v471"), "__private"); ((TAtom "v479"), "_cleanup_start_doit"); ((TAtom "v483"), "_cleanup_routine"); ((TAtom "v486"), "result"); ((TAtom "v5"), "_cleanup_routine"); ((TAtom "v54"), "__futex"); ((TAtom "v55"), "__atg3_old"); ((TAtom "v56"), "__atg3_old"); ((TAtom "v71"), "__futex"); ((TAtom "v72"), "__futex"); ((TAtom "v75"), "__self"); ((TAtom "v81"), "_IO_list_all"); ((TAtom "v86"), "fp"); ((TAtom "v91"), "fp"); ((TAtom "v95"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L381"); (TAtom "L449"); (TAtom "L82")].

End fn___GI__IO_flush_all.

(** Projection keeps instruction bodies out of the VM code used by the membership check. *)
Definition source_blocks : list (string * option (list name)) := Eval lazy in
  map (fun n => (n,
    match find_direct (TAtom n) libioflush_module with
    | Some (Defined f) => Some (map b_label (fn_blocks f))
    | _ => None
    end)) ["__GI__IO_flush_all"].

(** One computation rejects missing functions and stale labels across all tables in this fixture. *)
Lemma labels_valid :
  forallb (fun row =>
  match find (fun entry => String.eqb (fst entry) (fst row)) source_blocks with
  | Some (_, Some labels) =>
      forallb (fun l => existsb (name_eqb l) labels)
        (snd row)
  | _ => false
  end) [("__GI__IO_flush_all", app (map fst fn___GI__IO_flush_all.block_src) fn___GI__IO_flush_all.loop_heads)] = true.
Proof. vm_compute. reflexivity. Qed.

End LibioFlushSrc.
