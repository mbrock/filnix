(** These tables connect checked function bodies to C declarations and source lines.
    Names and locations support annotations and diagnostic messages, not soundness premises.
    Natural-loop headers provide optional cuts for symbolic execution; any cut list is sound.
    Computation checks that every recorded block label belongs to the decoded function.
    The code generator reproduces this file from the capture; do not edit it. *)

From Stdlib Require Import String List Bool.
From Glibc Require Import CodePrelude LibioPutsCode.
Import ListNotations.
Open Scope string_scope.

Module LibioPutsSrc.

Module fn___GI__IO_fputs.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("iofputs.c", 30%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("iofputs.c", 33%nat)); ((TAtom "L24"), ("iofputs.c", 36%nat)); ((TAtom "L35"), ("iofputs.c", 36%nat)); ((TAtom "L36"), ("iofputs.c", 36%nat)); ((TAtom "L29"), ("iofputs.c", 36%nat)); ((TAtom "L30"), ("iofputs.c", 36%nat)); ((TAtom "L55"), ("iofputs.c", 36%nat)); ((TAtom "L79"), ("iofputs.c", 36%nat)); ((TAtom "L80"), ("iofputs.c", 36%nat)); ((TAtom "L84"), ("iofputs.c", 36%nat)); ((TAtom "L73"), ("iofputs.c", 36%nat)); ((TAtom "L56"), ("iofputs.c", 36%nat)); ((TAtom "L113"), ("iofputs.c", 37%nat)); ((TAtom "L123"), ("iofputs.c", 37%nat)); ((TAtom "L125"), ("iofputs.c", 37%nat)); ((TAtom "L161"), ("iofputs.c", 37%nat)); ((TAtom "iw_1.L10"), ("./libioP.h", 1049%nat)); ((TAtom "iw_1.join"), ("iofputs.c", 37%nat)); ((TAtom "L162"), ("iofputs.c", 37%nat)); ((TAtom "L106"), ("iofputs.c", 37%nat)); ((TAtom "L107"), ("iofputs.c", 34%nat)); ((TAtom "iw_2.L5"), ("./libioP.h", 1000%nat)); ((TAtom "iw_2.L19"), ("./libioP.h", 1000%nat)); ((TAtom "iw_2.L28"), ("./libioP.h", 1000%nat)); ((TAtom "iw_2.L29"), ("./libioP.h", 1000%nat)); ((TAtom "iw_2.L22"), ("./libioP.h", 1000%nat)); ((TAtom "iw_2.L23"), ("./libioP.h", 1000%nat)); ((TAtom "iw_2.L45"), ("./libioP.h", 1000%nat)); ((TAtom "iw_2.L66"), ("./libioP.h", 1000%nat)); ((TAtom "iw_2.L67"), ("./libioP.h", 1000%nat)); ((TAtom "iw_2.L78"), ("./libioP.h", 1000%nat)); ((TAtom "iw_2.L46"), ("./libioP.h", 1000%nat)); ((TAtom "L14"), ("iofputs.c", 41%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "vtable"); ((TAtom "iw_1.v13"), "offset"); ((TAtom "iw_1.v18"), "vtable"); ((TAtom "iw_1.v3"), "vtable"); ((TAtom "iw_1.v4"), "ptr"); ((TAtom "iw_1.v6"), "ptr"); ((TAtom "iw_1.v9"), "offset"); ((TAtom "iw_2.v0"), "p"); ((TAtom "iw_2.v15"), "fp"); ((TAtom "iw_2.v26"), "__libc_single_threaded_internal"); ((TAtom "iw_2.v3"), "p"); ((TAtom "iw_2.v30"), "fp"); ((TAtom "iw_2.v38"), "fp"); ((TAtom "iw_2.v4"), "fp"); ((TAtom "iw_2.v42"), "fp"); ((TAtom "iw_2.v48"), "fp"); ((TAtom "iw_2.v54"), "fp"); ((TAtom "iw_2.v59"), "fp"); ((TAtom "iw_2.v61"), "__futex"); ((TAtom "iw_2.v64"), "__futex"); ((TAtom "iw_2.v68"), "__oldval"); ((TAtom "iw_2.v74"), "__oldval"); ((TAtom "iw_2.v8"), "fp"); ((TAtom "iw_2.v86"), "__futex"); ((TAtom "iw_2.v87"), "__futex"); ((TAtom "iw_2.v88"), "__private"); ((TAtom "iw_2.v89"), "fp"); ((TAtom "pr.1"), "result"); ((TAtom "pr.2"), "result"); ((TAtom "pr.3"), "__result"); ((TAtom "pr.4"), "__result"); ((TAtom "v0"), "str"); ((TAtom "v112"), "__result"); ((TAtom "v116"), "__result"); ((TAtom "v126"), "fp"); ((TAtom "v130"), "fp"); ((TAtom "v133"), "fp"); ((TAtom "v135"), "__result"); ((TAtom "v149"), "fp"); ((TAtom "v152"), "__result"); ((TAtom "v153"), "fp"); ((TAtom "v154"), "__result"); ((TAtom "v155"), "__result"); ((TAtom "v156"), "__result"); ((TAtom "v16"), "fp"); ((TAtom "v163"), "fp"); ((TAtom "v169"), "fp"); ((TAtom "v170"), "str"); ((TAtom "v171"), "len"); ((TAtom "v173"), "len"); ((TAtom "v177"), "result"); ((TAtom "v2"), "fp"); ((TAtom "v20"), "_IO_acquire_lock_file"); ((TAtom "v28"), "__self"); ((TAtom "v33"), "__libc_single_threaded_internal"); ((TAtom "v37"), "_IO_acquire_lock_file"); ((TAtom "v47"), "_IO_acquire_lock_file"); ((TAtom "v5"), "str"); ((TAtom "v50"), "_IO_acquire_lock_file"); ((TAtom "v54"), "__self"); ((TAtom "v58"), "_IO_acquire_lock_file"); ((TAtom "v6"), "len"); ((TAtom "v63"), "__self"); ((TAtom "v68"), "_IO_acquire_lock_file"); ((TAtom "v70"), "__futex"); ((TAtom "v75"), "__futex"); ((TAtom "v76"), "__atg3_old"); ((TAtom "v77"), "__atg3_old"); ((TAtom "v8"), "result"); ((TAtom "v92"), "__futex"); ((TAtom "v93"), "__futex"); ((TAtom "v94"), "_IO_acquire_lock_file"); ((TAtom "v98"), "__self"); ((TAtom "v99"), "_IO_acquire_lock_file")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "iw_2.L66")].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__GI__IO_fputs") (code_module libioputs_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___GI__IO_fputs.

Module fn___GI__IO_puts.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("ioputs.c", 31%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("ioputs.c", 35%nat)); ((TAtom "L20"), ("ioputs.c", 36%nat)); ((TAtom "L31"), ("ioputs.c", 36%nat)); ((TAtom "L32"), ("ioputs.c", 36%nat)); ((TAtom "L25"), ("ioputs.c", 36%nat)); ((TAtom "L26"), ("ioputs.c", 36%nat)); ((TAtom "L51"), ("ioputs.c", 36%nat)); ((TAtom "L75"), ("ioputs.c", 36%nat)); ((TAtom "L76"), ("ioputs.c", 36%nat)); ((TAtom "L80"), ("ioputs.c", 36%nat)); ((TAtom "L69"), ("ioputs.c", 36%nat)); ((TAtom "L52"), ("ioputs.c", 36%nat)); ((TAtom "L109"), ("ioputs.c", 39%nat)); ((TAtom "L119"), ("ioputs.c", 39%nat)); ((TAtom "L121"), ("ioputs.c", 39%nat)); ((TAtom "L162"), ("ioputs.c", 38%nat)); ((TAtom "iw_1.L10"), ("./libioP.h", 1049%nat)); ((TAtom "iw_1.join"), ("ioputs.c", 38%nat)); ((TAtom "L163"), ("ioputs.c", 38%nat)); ((TAtom "L180"), ("ioputs.c", 38%nat)); ((TAtom "L182"), ("ioputs.c", 38%nat)); ((TAtom "L183"), ("ioputs.c", 38%nat)); ((TAtom "L184"), ("ioputs.c", 38%nat)); ((TAtom "L181"), ("ioputs.c", 38%nat)); ((TAtom "L101"), ("ioputs.c", 42%nat)); ((TAtom "L212"), ("ioputs.c", 42%nat)); ((TAtom "L103"), ("ioputs.c", 34%nat)); ((TAtom "iw_2.L5"), ("./libioP.h", 1000%nat)); ((TAtom "iw_2.L19"), ("./libioP.h", 1000%nat)); ((TAtom "iw_2.L28"), ("./libioP.h", 1000%nat)); ((TAtom "iw_2.L29"), ("./libioP.h", 1000%nat)); ((TAtom "iw_2.L22"), ("./libioP.h", 1000%nat)); ((TAtom "iw_2.L23"), ("./libioP.h", 1000%nat)); ((TAtom "iw_2.L45"), ("./libioP.h", 1000%nat)); ((TAtom "iw_2.L66"), ("./libioP.h", 1000%nat)); ((TAtom "iw_2.L67"), ("./libioP.h", 1000%nat)); ((TAtom "iw_2.L78"), ("./libioP.h", 1000%nat)); ((TAtom "iw_2.L46"), ("./libioP.h", 1000%nat)); ((TAtom "L9"), ("ioputs.c", 45%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "vtable"); ((TAtom "iw_1.v13"), "offset"); ((TAtom "iw_1.v18"), "vtable"); ((TAtom "iw_1.v3"), "vtable"); ((TAtom "iw_1.v4"), "ptr"); ((TAtom "iw_1.v6"), "ptr"); ((TAtom "iw_1.v9"), "offset"); ((TAtom "iw_2.v0"), "p"); ((TAtom "iw_2.v15"), "fp"); ((TAtom "iw_2.v26"), "__libc_single_threaded_internal"); ((TAtom "iw_2.v3"), "p"); ((TAtom "iw_2.v30"), "fp"); ((TAtom "iw_2.v38"), "fp"); ((TAtom "iw_2.v4"), "fp"); ((TAtom "iw_2.v42"), "fp"); ((TAtom "iw_2.v48"), "fp"); ((TAtom "iw_2.v54"), "fp"); ((TAtom "iw_2.v59"), "fp"); ((TAtom "iw_2.v61"), "__futex"); ((TAtom "iw_2.v64"), "__futex"); ((TAtom "iw_2.v68"), "__oldval"); ((TAtom "iw_2.v74"), "__oldval"); ((TAtom "iw_2.v8"), "fp"); ((TAtom "iw_2.v86"), "__futex"); ((TAtom "iw_2.v87"), "__futex"); ((TAtom "iw_2.v88"), "__private"); ((TAtom "iw_2.v89"), "fp"); ((TAtom "pr.1"), "result"); ((TAtom "pr.2"), "result"); ((TAtom "pr.3"), "__result"); ((TAtom "pr.4"), "__result"); ((TAtom "v0"), "str"); ((TAtom "v108"), "__result"); ((TAtom "v112"), "__result"); ((TAtom "v12"), "stdout"); ((TAtom "v123"), "stdout"); ((TAtom "v128"), "stdout"); ((TAtom "v132"), "stdout"); ((TAtom "v134"), "__result"); ((TAtom "v149"), "stdout"); ((TAtom "v152"), "__result"); ((TAtom "v154"), "stdout"); ((TAtom "v155"), "__result"); ((TAtom "v156"), "__result"); ((TAtom "v157"), "__result"); ((TAtom "v16"), "_IO_acquire_lock_file"); ((TAtom "v165"), "stdout"); ((TAtom "v172"), "stdout"); ((TAtom "v173"), "str"); ((TAtom "v174"), "len"); ((TAtom "v176"), "len"); ((TAtom "v186"), "stdout"); ((TAtom "v190"), "stdout"); ((TAtom "v199"), "stdout"); ((TAtom "v202"), "stdout"); ((TAtom "v214"), "len"); ((TAtom "v217"), "len"); ((TAtom "v219"), "result"); ((TAtom "v220"), "result"); ((TAtom "v24"), "__self"); ((TAtom "v29"), "__libc_single_threaded_internal"); ((TAtom "v3"), "result"); ((TAtom "v33"), "_IO_acquire_lock_file"); ((TAtom "v43"), "_IO_acquire_lock_file"); ((TAtom "v46"), "_IO_acquire_lock_file"); ((TAtom "v5"), "str"); ((TAtom "v50"), "__self"); ((TAtom "v54"), "_IO_acquire_lock_file"); ((TAtom "v59"), "__self"); ((TAtom "v6"), "len"); ((TAtom "v64"), "_IO_acquire_lock_file"); ((TAtom "v66"), "__futex"); ((TAtom "v71"), "__futex"); ((TAtom "v72"), "__atg3_old"); ((TAtom "v73"), "__atg3_old"); ((TAtom "v88"), "__futex"); ((TAtom "v89"), "__futex"); ((TAtom "v90"), "_IO_acquire_lock_file"); ((TAtom "v94"), "__self"); ((TAtom "v95"), "_IO_acquire_lock_file")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "iw_2.L66")].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__GI__IO_puts") (code_module libioputs_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___GI__IO_puts.

End LibioPutsSrc.
