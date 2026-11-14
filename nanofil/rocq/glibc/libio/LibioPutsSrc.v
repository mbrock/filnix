(** These tables connect checked function bodies to C declarations and source lines.
    Names and locations support annotations and diagnostic messages, not soundness premises.
    Natural-loop headers provide optional cuts for symbolic execution; any cut list is sound.
    Computation checks that every recorded block label belongs to the decoded function.
    The code generator reproduces this file from the capture; do not edit it. *)

From Stdlib Require Import String List Bool NArith.
From Glibc Require Import CodePrelude.
Import ListNotations.
Open Scope string_scope.


From Glibc Require Import LibioPutsCode.
Module LibioPutsSrc.

Definition file_0 : string := "./libioP.h".

Definition file_1 : string := "iofputs.c".

Definition file_2 : string := "ioputs.c".

Module fn___GI__IO_fputs.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_1, 30%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_1, 33%N)); ((TAtom "L24"), (file_1, 36%N)); ((TAtom "L35"), (file_1, 36%N)); ((TAtom "L36"), (file_1, 36%N)); ((TAtom "L29"), (file_1, 36%N)); ((TAtom "L30"), (file_1, 36%N)); ((TAtom "L55"), (file_1, 36%N)); ((TAtom "L79"), (file_1, 36%N)); ((TAtom "L80"), (file_1, 36%N)); ((TAtom "L84"), (file_1, 36%N)); ((TAtom "L73"), (file_1, 36%N)); ((TAtom "L56"), (file_1, 36%N)); ((TAtom "L113"), (file_1, 37%N)); ((TAtom "L123"), (file_1, 37%N)); ((TAtom "L125"), (file_1, 37%N)); ((TAtom "L161"), (file_1, 37%N)); ((TAtom "iw_1.L10"), (file_0, 1049%N)); ((TAtom "iw_1.join"), (file_1, 37%N)); ((TAtom "L162"), (file_1, 37%N)); ((TAtom "L106"), (file_1, 37%N)); ((TAtom "L107"), (file_1, 34%N)); ((TAtom "iw_2.L5"), (file_0, 1000%N)); ((TAtom "iw_2.L19"), (file_0, 1000%N)); ((TAtom "iw_2.L28"), (file_0, 1000%N)); ((TAtom "iw_2.L29"), (file_0, 1000%N)); ((TAtom "iw_2.L22"), (file_0, 1000%N)); ((TAtom "iw_2.L23"), (file_0, 1000%N)); ((TAtom "iw_2.L45"), (file_0, 1000%N)); ((TAtom "iw_2.L66"), (file_0, 1000%N)); ((TAtom "iw_2.L67"), (file_0, 1000%N)); ((TAtom "iw_2.L78"), (file_0, 1000%N)); ((TAtom "iw_2.L46"), (file_0, 1000%N)); ((TAtom "L14"), (file_1, 41%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "vtable"); ((TAtom "iw_1.v13"), "offset"); ((TAtom "iw_1.v18"), "vtable"); ((TAtom "iw_1.v3"), "vtable"); ((TAtom "iw_1.v4"), "ptr"); ((TAtom "iw_1.v6"), "ptr"); ((TAtom "iw_1.v9"), "offset"); ((TAtom "iw_2.v0"), "p"); ((TAtom "iw_2.v15"), "fp"); ((TAtom "iw_2.v26"), "__libc_single_threaded_internal"); ((TAtom "iw_2.v3"), "p"); ((TAtom "iw_2.v30"), "fp"); ((TAtom "iw_2.v38"), "fp"); ((TAtom "iw_2.v4"), "fp"); ((TAtom "iw_2.v42"), "fp"); ((TAtom "iw_2.v48"), "fp"); ((TAtom "iw_2.v54"), "fp"); ((TAtom "iw_2.v59"), "fp"); ((TAtom "iw_2.v61"), "__futex"); ((TAtom "iw_2.v64"), "__futex"); ((TAtom "iw_2.v68"), "__oldval"); ((TAtom "iw_2.v74"), "__oldval"); ((TAtom "iw_2.v8"), "fp"); ((TAtom "iw_2.v86"), "__futex"); ((TAtom "iw_2.v87"), "__futex"); ((TAtom "iw_2.v88"), "__private"); ((TAtom "iw_2.v89"), "fp"); ((TAtom "pr.1"), "result"); ((TAtom "pr.2"), "result"); ((TAtom "pr.3"), "__result"); ((TAtom "pr.4"), "__result"); ((TAtom "v0"), "str"); ((TAtom "v112"), "__result"); ((TAtom "v116"), "__result"); ((TAtom "v126"), "fp"); ((TAtom "v130"), "fp"); ((TAtom "v133"), "fp"); ((TAtom "v135"), "__result"); ((TAtom "v149"), "fp"); ((TAtom "v152"), "__result"); ((TAtom "v153"), "fp"); ((TAtom "v154"), "__result"); ((TAtom "v155"), "__result"); ((TAtom "v156"), "__result"); ((TAtom "v16"), "fp"); ((TAtom "v163"), "fp"); ((TAtom "v169"), "fp"); ((TAtom "v170"), "str"); ((TAtom "v171"), "len"); ((TAtom "v173"), "len"); ((TAtom "v177"), "result"); ((TAtom "v2"), "fp"); ((TAtom "v20"), "_IO_acquire_lock_file"); ((TAtom "v28"), "__self"); ((TAtom "v33"), "__libc_single_threaded_internal"); ((TAtom "v37"), "_IO_acquire_lock_file"); ((TAtom "v47"), "_IO_acquire_lock_file"); ((TAtom "v5"), "str"); ((TAtom "v50"), "_IO_acquire_lock_file"); ((TAtom "v54"), "__self"); ((TAtom "v58"), "_IO_acquire_lock_file"); ((TAtom "v6"), "len"); ((TAtom "v63"), "__self"); ((TAtom "v68"), "_IO_acquire_lock_file"); ((TAtom "v70"), "__futex"); ((TAtom "v75"), "__futex"); ((TAtom "v76"), "__atg3_old"); ((TAtom "v77"), "__atg3_old"); ((TAtom "v8"), "result"); ((TAtom "v92"), "__futex"); ((TAtom "v93"), "__futex"); ((TAtom "v94"), "_IO_acquire_lock_file"); ((TAtom "v98"), "__self"); ((TAtom "v99"), "_IO_acquire_lock_file")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "iw_2.L66")].

End fn___GI__IO_fputs.

Module fn___GI__IO_puts.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_2, 31%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_2, 35%N)); ((TAtom "L20"), (file_2, 36%N)); ((TAtom "L31"), (file_2, 36%N)); ((TAtom "L32"), (file_2, 36%N)); ((TAtom "L25"), (file_2, 36%N)); ((TAtom "L26"), (file_2, 36%N)); ((TAtom "L51"), (file_2, 36%N)); ((TAtom "L75"), (file_2, 36%N)); ((TAtom "L76"), (file_2, 36%N)); ((TAtom "L80"), (file_2, 36%N)); ((TAtom "L69"), (file_2, 36%N)); ((TAtom "L52"), (file_2, 36%N)); ((TAtom "L109"), (file_2, 39%N)); ((TAtom "L119"), (file_2, 39%N)); ((TAtom "L121"), (file_2, 39%N)); ((TAtom "L162"), (file_2, 38%N)); ((TAtom "iw_1.L10"), (file_0, 1049%N)); ((TAtom "iw_1.join"), (file_2, 38%N)); ((TAtom "L163"), (file_2, 38%N)); ((TAtom "L180"), (file_2, 38%N)); ((TAtom "L182"), (file_2, 38%N)); ((TAtom "L183"), (file_2, 38%N)); ((TAtom "L184"), (file_2, 38%N)); ((TAtom "L181"), (file_2, 38%N)); ((TAtom "L101"), (file_2, 42%N)); ((TAtom "L212"), (file_2, 42%N)); ((TAtom "L103"), (file_2, 34%N)); ((TAtom "iw_2.L5"), (file_0, 1000%N)); ((TAtom "iw_2.L19"), (file_0, 1000%N)); ((TAtom "iw_2.L28"), (file_0, 1000%N)); ((TAtom "iw_2.L29"), (file_0, 1000%N)); ((TAtom "iw_2.L22"), (file_0, 1000%N)); ((TAtom "iw_2.L23"), (file_0, 1000%N)); ((TAtom "iw_2.L45"), (file_0, 1000%N)); ((TAtom "iw_2.L66"), (file_0, 1000%N)); ((TAtom "iw_2.L67"), (file_0, 1000%N)); ((TAtom "iw_2.L78"), (file_0, 1000%N)); ((TAtom "iw_2.L46"), (file_0, 1000%N)); ((TAtom "L9"), (file_2, 45%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "vtable"); ((TAtom "iw_1.v13"), "offset"); ((TAtom "iw_1.v18"), "vtable"); ((TAtom "iw_1.v3"), "vtable"); ((TAtom "iw_1.v4"), "ptr"); ((TAtom "iw_1.v6"), "ptr"); ((TAtom "iw_1.v9"), "offset"); ((TAtom "iw_2.v0"), "p"); ((TAtom "iw_2.v15"), "fp"); ((TAtom "iw_2.v26"), "__libc_single_threaded_internal"); ((TAtom "iw_2.v3"), "p"); ((TAtom "iw_2.v30"), "fp"); ((TAtom "iw_2.v38"), "fp"); ((TAtom "iw_2.v4"), "fp"); ((TAtom "iw_2.v42"), "fp"); ((TAtom "iw_2.v48"), "fp"); ((TAtom "iw_2.v54"), "fp"); ((TAtom "iw_2.v59"), "fp"); ((TAtom "iw_2.v61"), "__futex"); ((TAtom "iw_2.v64"), "__futex"); ((TAtom "iw_2.v68"), "__oldval"); ((TAtom "iw_2.v74"), "__oldval"); ((TAtom "iw_2.v8"), "fp"); ((TAtom "iw_2.v86"), "__futex"); ((TAtom "iw_2.v87"), "__futex"); ((TAtom "iw_2.v88"), "__private"); ((TAtom "iw_2.v89"), "fp"); ((TAtom "pr.1"), "result"); ((TAtom "pr.2"), "result"); ((TAtom "pr.3"), "__result"); ((TAtom "pr.4"), "__result"); ((TAtom "v0"), "str"); ((TAtom "v108"), "__result"); ((TAtom "v112"), "__result"); ((TAtom "v12"), "stdout"); ((TAtom "v123"), "stdout"); ((TAtom "v128"), "stdout"); ((TAtom "v132"), "stdout"); ((TAtom "v134"), "__result"); ((TAtom "v149"), "stdout"); ((TAtom "v152"), "__result"); ((TAtom "v154"), "stdout"); ((TAtom "v155"), "__result"); ((TAtom "v156"), "__result"); ((TAtom "v157"), "__result"); ((TAtom "v16"), "_IO_acquire_lock_file"); ((TAtom "v165"), "stdout"); ((TAtom "v172"), "stdout"); ((TAtom "v173"), "str"); ((TAtom "v174"), "len"); ((TAtom "v176"), "len"); ((TAtom "v186"), "stdout"); ((TAtom "v190"), "stdout"); ((TAtom "v199"), "stdout"); ((TAtom "v202"), "stdout"); ((TAtom "v214"), "len"); ((TAtom "v217"), "len"); ((TAtom "v219"), "result"); ((TAtom "v220"), "result"); ((TAtom "v24"), "__self"); ((TAtom "v29"), "__libc_single_threaded_internal"); ((TAtom "v3"), "result"); ((TAtom "v33"), "_IO_acquire_lock_file"); ((TAtom "v43"), "_IO_acquire_lock_file"); ((TAtom "v46"), "_IO_acquire_lock_file"); ((TAtom "v5"), "str"); ((TAtom "v50"), "__self"); ((TAtom "v54"), "_IO_acquire_lock_file"); ((TAtom "v59"), "__self"); ((TAtom "v6"), "len"); ((TAtom "v64"), "_IO_acquire_lock_file"); ((TAtom "v66"), "__futex"); ((TAtom "v71"), "__futex"); ((TAtom "v72"), "__atg3_old"); ((TAtom "v73"), "__atg3_old"); ((TAtom "v88"), "__futex"); ((TAtom "v89"), "__futex"); ((TAtom "v90"), "_IO_acquire_lock_file"); ((TAtom "v94"), "__self"); ((TAtom "v95"), "_IO_acquire_lock_file")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "iw_2.L66")].

End fn___GI__IO_puts.

(** Projection keeps instruction bodies out of the VM code used by the membership check. *)
Definition source_blocks : list (string * option (list name)) := Eval lazy in
  map (fun n => (n,
    match find_direct (TAtom n) libioputs_module with
    | Some (Defined f) => Some (map b_label (fn_blocks f))
    | _ => None
    end)) ["__GI__IO_fputs"; "__GI__IO_puts"].

(** One computation rejects missing functions and stale labels across all tables in this fixture. *)
Lemma labels_valid :
  forallb (fun row =>
  match find (fun entry => String.eqb (fst entry) (fst row)) source_blocks with
  | Some (_, Some labels) =>
      forallb (fun l => existsb (name_eqb l) labels)
        (snd row)
  | _ => false
  end) [("__GI__IO_fputs", app (map fst fn___GI__IO_fputs.block_src) fn___GI__IO_fputs.loop_heads); ("__GI__IO_puts", app (map fst fn___GI__IO_puts.block_src) fn___GI__IO_puts.loop_heads)] = true.
Proof. vm_compute. reflexivity. Qed.

End LibioPutsSrc.
