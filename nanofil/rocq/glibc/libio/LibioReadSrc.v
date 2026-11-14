(** These tables connect checked function bodies to C declarations and source lines.
    Names and locations support annotations and diagnostic messages, not soundness premises.
    Natural-loop headers provide optional cuts for symbolic execution; any cut list is sound.
    Computation checks that every recorded block label belongs to the decoded function.
    The code generator reproduces this file from the capture; do not edit it. *)

From Stdlib Require Import String List Bool.
From Glibc Require Import CodePrelude LibioReadCode.
Import ListNotations.
Open Scope string_scope.

Module LibioReadSrc.

Module fn___fpending.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("__fpending.c", 20%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("__fpending.c", 23%nat)); ((TAtom "L2"), ("__fpending.c", 24%nat)); ((TAtom "L3"), ("__fpending.c", 26%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fp"); ((TAtom "v14"), "fp"); ((TAtom "v24"), "fp"); ((TAtom "v27"), "fp"); ((TAtom "v5"), "fp"); ((TAtom "v9"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__fpending") (code_module libioread_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___fpending.

Module fn__IO_ferror.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("ferror.c", 30%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("ferror.c", 35%nat)); ((TAtom "L6"), ("ferror.c", 36%nat)); ((TAtom "L8"), ("ferror.c", 37%nat)); ((TAtom "L29"), ("ferror.c", 37%nat)); ((TAtom "L40"), ("ferror.c", 37%nat)); ((TAtom "L41"), ("ferror.c", 37%nat)); ((TAtom "L34"), ("ferror.c", 37%nat)); ((TAtom "L35"), ("ferror.c", 37%nat)); ((TAtom "L60"), ("ferror.c", 37%nat)); ((TAtom "L84"), ("ferror.c", 37%nat)); ((TAtom "L85"), ("ferror.c", 37%nat)); ((TAtom "L89"), ("ferror.c", 37%nat)); ((TAtom "L78"), ("ferror.c", 37%nat)); ((TAtom "L61"), ("ferror.c", 37%nat)); ((TAtom "L24"), ("ferror.c", 38%nat)); ((TAtom "L121"), ("ferror.c", 39%nat)); ((TAtom "L130"), ("ferror.c", 39%nat)); ((TAtom "L131"), ("ferror.c", 39%nat)); ((TAtom "L124"), ("ferror.c", 39%nat)); ((TAtom "L125"), ("ferror.c", 39%nat)); ((TAtom "L147"), ("ferror.c", 39%nat)); ((TAtom "L168"), ("ferror.c", 39%nat)); ((TAtom "L169"), ("ferror.c", 39%nat)); ((TAtom "L180"), ("ferror.c", 39%nat)); ((TAtom "L148"), ("ferror.c", 39%nat)); ((TAtom "L116"), ("ferror.c", 40%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fp"); ((TAtom "v103"), "__self"); ((TAtom "v104"), "fp"); ((TAtom "v110"), "fp"); ((TAtom "v113"), "result"); ((TAtom "v117"), "fp"); ((TAtom "v128"), "__libc_single_threaded_internal"); ((TAtom "v132"), "fp"); ((TAtom "v140"), "fp"); ((TAtom "v144"), "fp"); ((TAtom "v150"), "fp"); ((TAtom "v156"), "fp"); ((TAtom "v161"), "fp"); ((TAtom "v163"), "__futex"); ((TAtom "v166"), "__futex"); ((TAtom "v17"), "fp"); ((TAtom "v170"), "__oldval"); ((TAtom "v176"), "__oldval"); ((TAtom "v188"), "__futex"); ((TAtom "v189"), "__futex"); ((TAtom "v190"), "__private"); ((TAtom "v191"), "fp"); ((TAtom "v197"), "result"); ((TAtom "v25"), "fp"); ((TAtom "v33"), "__self"); ((TAtom "v38"), "__libc_single_threaded_internal"); ((TAtom "v42"), "fp"); ((TAtom "v52"), "fp"); ((TAtom "v55"), "fp"); ((TAtom "v59"), "__self"); ((TAtom "v63"), "fp"); ((TAtom "v68"), "__self"); ((TAtom "v73"), "fp"); ((TAtom "v75"), "__futex"); ((TAtom "v80"), "__futex"); ((TAtom "v81"), "__atg3_old"); ((TAtom "v82"), "__atg3_old"); ((TAtom "v9"), "fp"); ((TAtom "v97"), "__futex"); ((TAtom "v98"), "__futex"); ((TAtom "v99"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L168")].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "_IO_ferror") (code_module libioread_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn__IO_ferror.

Module fn___GI__IO_file_doallocate.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("filedoalloc.c", 66%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("filedoalloc.c", 71%nat)); ((TAtom "L12"), ("filedoalloc.c", 74%nat)); ((TAtom "iw_1.L10"), ("./libioP.h", 1049%nat)); ((TAtom "iw_1.join"), ("filedoalloc.c", 74%nat)); ((TAtom "L13"), ("filedoalloc.c", 74%nat)); ((TAtom "L5"), ("filedoalloc.c", 76%nat)); ((TAtom "L26"), ("filedoalloc.c", 81%nat)); ((TAtom "L42"), ("filedoalloc.c", 81%nat)); ((TAtom "L43"), ("filedoalloc.c", 81%nat)); ((TAtom "L48"), ("filedoalloc.c", 79%nat)); ((TAtom "L49"), ("filedoalloc.c", 79%nat)); ((TAtom "L33"), ("filedoalloc.c", 84%nat)); ((TAtom "L28"), ("filedoalloc.c", 87%nat)); ((TAtom "L65"), ("filedoalloc.c", 87%nat)); ((TAtom "L66"), ("filedoalloc.c", 87%nat)); ((TAtom "L59"), ("filedoalloc.c", 88%nat)); ((TAtom "L7"), ("filedoalloc.c", 69%nat)); ((TAtom "L76"), ("filedoalloc.c", 93%nat)); ((TAtom "L78"), ("filedoalloc.c", 94%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "vtable"); ((TAtom "iw_1.v13"), "offset"); ((TAtom "iw_1.v18"), "vtable"); ((TAtom "iw_1.v3"), "vtable"); ((TAtom "iw_1.v4"), "ptr"); ((TAtom "iw_1.v6"), "ptr"); ((TAtom "iw_1.v9"), "offset"); ((TAtom "pr.1"), "size"); ((TAtom "pr.2"), "size"); ((TAtom "v0"), "fp"); ((TAtom "v14"), "fp"); ((TAtom "v20"), "fp"); ((TAtom "v39"), "__dev_major"); ((TAtom "v40"), "__dev_major"); ((TAtom "v44"), "__dev_major"); ((TAtom "v50"), "fp"); ((TAtom "v56"), "fp"); ((TAtom "v73"), "size"); ((TAtom "v74"), "size"); ((TAtom "v75"), "p"); ((TAtom "v79"), "p"); ((TAtom "v8"), "fp"); ((TAtom "v87"), "fp"); ((TAtom "v88"), "p"); ((TAtom "v89"), "p"); ((TAtom "v90"), "size")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__GI__IO_file_doallocate") (code_module libioread_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___GI__IO_file_doallocate.

Module fn___GI__IO_file_stat.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("fileops.c", 1221%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("fileops.c", 1224%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fp"); ((TAtom "v2"), "st"); ((TAtom "v4"), "fp"); ((TAtom "v7"), "st")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__GI__IO_file_stat") (code_module libioread_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___GI__IO_file_stat.

Module fn___GI__IO_file_close.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("fileops.c", 1239%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("fileops.c", 1244%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fp"); ((TAtom "v2"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__GI__IO_file_close") (code_module libioread_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___GI__IO_file_close.

Module fn__IO_new_file_write.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("fileops.c", 1248%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("fileops.c", 1252%nat)); ((TAtom "L8"), ("fileops.c", 1251%nat)); ((TAtom "L9"), ("fileops.c", 1254%nat)); ((TAtom "L14"), ("fileops.c", 1254%nat)); ((TAtom "L15"), ("fileops.c", 1254%nat)); ((TAtom "L16"), ("fileops.c", 1254%nat)); ((TAtom "L38"), ("fileops.c", 1260%nat)); ((TAtom "L40"), ("fileops.c", 1263%nat)); ((TAtom "L10"), ("fileops.c", 1267%nat)); ((TAtom "L61"), ("fileops.c", 1269%nat)); ((TAtom "L63"), ("fileops.c", 1270%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "pr.1"), "data"); ((TAtom "pr.2"), "to_do"); ((TAtom "v0"), "f"); ((TAtom "v11"), "to_do"); ((TAtom "v17"), "f"); ((TAtom "v2"), "data"); ((TAtom "v25"), "f"); ((TAtom "v28"), "data"); ((TAtom "v29"), "to_do"); ((TAtom "v31"), "f"); ((TAtom "v34"), "data"); ((TAtom "v35"), "to_do"); ((TAtom "v37"), "count"); ((TAtom "v4"), "n"); ((TAtom "v41"), "count"); ((TAtom "v43"), "f"); ((TAtom "v47"), "f"); ((TAtom "v50"), "count"); ((TAtom "v52"), "to_do"); ((TAtom "v53"), "count"); ((TAtom "v54"), "to_do"); ((TAtom "v55"), "data"); ((TAtom "v56"), "count"); ((TAtom "v57"), "data"); ((TAtom "v58"), "n"); ((TAtom "v59"), "to_do"); ((TAtom "v60"), "n"); ((TAtom "v64"), "f"); ((TAtom "v68"), "f"); ((TAtom "v7"), "n"); ((TAtom "v71"), "n"); ((TAtom "v73"), "n")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L8")].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "_IO_new_file_write") (code_module libioread_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn__IO_new_file_write.

Module fn___GI__IO_setb.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("genops.c", 353%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("genops.c", 356%nat)); ((TAtom "L16"), ("genops.c", 356%nat)); ((TAtom "L17"), ("genops.c", 356%nat)); ((TAtom "L8"), ("genops.c", 357%nat)); ((TAtom "L10"), ("genops.c", 358%nat)); ((TAtom "L33"), ("genops.c", 361%nat)); ((TAtom "L34"), ("genops.c", 363%nat)); ((TAtom "L35"), ("genops.c", 353%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "f"); ((TAtom "v11"), "f"); ((TAtom "v18"), "f"); ((TAtom "v2"), "b"); ((TAtom "v24"), "f"); ((TAtom "v27"), "f"); ((TAtom "v29"), "b"); ((TAtom "v30"), "f"); ((TAtom "v32"), "eb"); ((TAtom "v36"), "a"); ((TAtom "v37"), "f"); ((TAtom "v4"), "eb"); ((TAtom "v41"), "f"); ((TAtom "v6"), "a")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__GI__IO_setb") (code_module libioread_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___GI__IO_setb.

Module fn___GI__IO_doallocbuf.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("genops.c", 367%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("genops.c", 370%nat)); ((TAtom "L2"), ("genops.c", 371%nat)); ((TAtom "L4"), ("genops.c", 372%nat)); ((TAtom "L18"), ("genops.c", 372%nat)); ((TAtom "L19"), ("genops.c", 372%nat)); ((TAtom "L11"), ("genops.c", 373%nat)); ((TAtom "iw_1.L10"), ("./libioP.h", 1049%nat)); ((TAtom "iw_1.join"), ("genops.c", 373%nat)); ((TAtom "L26"), ("genops.c", 374%nat)); ((TAtom "L13"), ("genops.c", 375%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "vtable"); ((TAtom "iw_1.v13"), "offset"); ((TAtom "iw_1.v18"), "vtable"); ((TAtom "iw_1.v3"), "vtable"); ((TAtom "iw_1.v4"), "ptr"); ((TAtom "iw_1.v6"), "ptr"); ((TAtom "iw_1.v9"), "offset"); ((TAtom "v0"), "fp"); ((TAtom "v14"), "fp"); ((TAtom "v20"), "fp"); ((TAtom "v29"), "fp"); ((TAtom "v35"), "fp"); ((TAtom "v40"), "fp"); ((TAtom "v41"), "fp"); ((TAtom "v43"), "fp"); ((TAtom "v5"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__GI__IO_doallocbuf") (code_module libioread_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___GI__IO_doallocbuf.

Module fn___gnu_dev_major.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("makedev.c", 28%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("makedev.c", 28%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "__dev"); ((TAtom "v11"), "__major"); ((TAtom "v12"), "__major"); ((TAtom "v3"), "__dev"); ((TAtom "v5"), "__major"); ((TAtom "v6"), "__major"); ((TAtom "v7"), "__dev")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__gnu_dev_major") (code_module libioread_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___gnu_dev_major.

End LibioReadSrc.
