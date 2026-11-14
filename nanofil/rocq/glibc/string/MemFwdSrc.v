(** These tables connect checked function bodies to C declarations and source lines.
    Names and locations support annotations and diagnostic messages, not soundness premises.
    Natural-loop headers provide optional cuts for symbolic execution; any cut list is sound.
    Computation checks that every recorded block label belongs to the decoded function.
    The code generator reproduces this file from the capture; do not edit it. *)

From Stdlib Require Import String List Bool.
From Glibc Require Import CodePrelude MemFwdCode.
Import ListNotations.
Open Scope string_scope.

Module MemFwdSrc.

Module fn___GI_memcpy.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("memcpy.c", 28%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("memcpy.c", 37%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "dstpp"); ((TAtom "v2"), "srcpp"); ((TAtom "v4"), "len"); ((TAtom "v6"), "dstpp"); ((TAtom "v7"), "srcpp"); ((TAtom "v8"), "len"); ((TAtom "v9"), "dstpp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__GI_memcpy") (code_module memfwd_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___GI_memcpy.

Module fn___GI___mempcpy.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("mempcpy.c", 32%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("mempcpy.c", 35%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "dest"); ((TAtom "v10"), "len"); ((TAtom "v2"), "src"); ((TAtom "v4"), "len"); ((TAtom "v6"), "dest"); ((TAtom "v7"), "src"); ((TAtom "v8"), "len")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__GI___mempcpy") (code_module memfwd_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___GI___mempcpy.

Module fn___GI_memset.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("memset.c", 26%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("memset.c", 29%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "dstpp"); ((TAtom "v2"), "c"); ((TAtom "v4"), "len"); ((TAtom "v6"), "dstpp"); ((TAtom "v7"), "c"); ((TAtom "v8"), "len"); ((TAtom "v9"), "dstpp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__GI_memset") (code_module memfwd_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___GI_memset.

Module fn___GI___strdup.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("strdup.c", 38%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("strdup.c", 41%nat)); ((TAtom "L9"), ("strdup.c", 45%nat)); ((TAtom "L11"), ("strdup.c", 47%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "s"); ((TAtom "v12"), "new"); ((TAtom "v17"), "new"); ((TAtom "v18"), "s"); ((TAtom "v19"), "len"); ((TAtom "v3"), "s"); ((TAtom "v5"), "len"); ((TAtom "v7"), "len"); ((TAtom "v8"), "new")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__GI___strdup") (code_module memfwd_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___GI___strdup.

Module fn___GI___errno_location.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("errno-loc.c", 23%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("errno-loc.c", 26%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__GI___errno_location") (code_module memfwd_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___GI___errno_location.

Module fn___mbsinit.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("mbsinit.c", 32%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("mbsinit.c", 35%nat)); ((TAtom "L6"), ("mbsinit.c", 35%nat)); ((TAtom "L7"), ("mbsinit.c", 35%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "ps"); ((TAtom "v2"), "ps"); ((TAtom "v8"), "ps")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__mbsinit") (code_module memfwd_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___mbsinit.

Module fn___GI___towlower.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("wcfuncs.c", 73%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("wcfuncs.c", 76%nat)); ((TAtom "iw_1.L16"), ("./wchar-lookup.h", 124%nat)); ((TAtom "iw_1.L30"), ("./wchar-lookup.h", 127%nat)); ((TAtom "iw_1.L59"), ("./wchar-lookup.h", 133%nat)); ((TAtom "iw_1.join"), ("wcfuncs.c", 78%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "table"); ((TAtom "iw_1.v10"), "shift1"); ((TAtom "iw_1.v11"), "index1"); ((TAtom "iw_1.v13"), "table"); ((TAtom "iw_1.v15"), "bound"); ((TAtom "iw_1.v19"), "index1"); ((TAtom "iw_1.v2"), "wc"); ((TAtom "iw_1.v20"), "bound"); ((TAtom "iw_1.v23"), "table"); ((TAtom "iw_1.v24"), "index1"); ((TAtom "iw_1.v29"), "lookup1"); ((TAtom "iw_1.v33"), "lookup1"); ((TAtom "iw_1.v36"), "table"); ((TAtom "iw_1.v38"), "shift2"); ((TAtom "iw_1.v40"), "table"); ((TAtom "iw_1.v42"), "mask2"); ((TAtom "iw_1.v44"), "wc"); ((TAtom "iw_1.v45"), "shift2"); ((TAtom "iw_1.v47"), "mask2"); ((TAtom "iw_1.v48"), "index2"); ((TAtom "iw_1.v5"), "table"); ((TAtom "iw_1.v50"), "table"); ((TAtom "iw_1.v51"), "lookup1"); ((TAtom "iw_1.v54"), "index2"); ((TAtom "iw_1.v58"), "lookup2"); ((TAtom "iw_1.v62"), "lookup2"); ((TAtom "iw_1.v65"), "table"); ((TAtom "iw_1.v67"), "mask3"); ((TAtom "iw_1.v69"), "wc"); ((TAtom "iw_1.v7"), "shift1"); ((TAtom "iw_1.v70"), "mask3"); ((TAtom "iw_1.v71"), "index3"); ((TAtom "iw_1.v73"), "table"); ((TAtom "iw_1.v74"), "lookup2"); ((TAtom "iw_1.v77"), "index3"); ((TAtom "iw_1.v81"), "lookup3"); ((TAtom "iw_1.v82"), "wc"); ((TAtom "iw_1.v83"), "lookup3"); ((TAtom "iw_1.v86"), "wc"); ((TAtom "iw_1.v9"), "wc"); ((TAtom "v0"), "wc"); ((TAtom "v14"), "i"); ((TAtom "v17"), "__libc_tsd_LOCALE"); ((TAtom "v21"), "i"); ((TAtom "v26"), "desc"); ((TAtom "v27"), "desc"); ((TAtom "v28"), "wc"); ((TAtom "v4"), "__libc_tsd_LOCALE")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__GI___towlower") (code_module memfwd_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___GI___towlower.

Module fn___GI___towupper.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("wcfuncs.c", 85%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("wcfuncs.c", 88%nat)); ((TAtom "iw_1.L16"), ("./wchar-lookup.h", 124%nat)); ((TAtom "iw_1.L30"), ("./wchar-lookup.h", 127%nat)); ((TAtom "iw_1.L59"), ("./wchar-lookup.h", 133%nat)); ((TAtom "iw_1.join"), ("wcfuncs.c", 90%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "table"); ((TAtom "iw_1.v10"), "shift1"); ((TAtom "iw_1.v11"), "index1"); ((TAtom "iw_1.v13"), "table"); ((TAtom "iw_1.v15"), "bound"); ((TAtom "iw_1.v19"), "index1"); ((TAtom "iw_1.v2"), "wc"); ((TAtom "iw_1.v20"), "bound"); ((TAtom "iw_1.v23"), "table"); ((TAtom "iw_1.v24"), "index1"); ((TAtom "iw_1.v29"), "lookup1"); ((TAtom "iw_1.v33"), "lookup1"); ((TAtom "iw_1.v36"), "table"); ((TAtom "iw_1.v38"), "shift2"); ((TAtom "iw_1.v40"), "table"); ((TAtom "iw_1.v42"), "mask2"); ((TAtom "iw_1.v44"), "wc"); ((TAtom "iw_1.v45"), "shift2"); ((TAtom "iw_1.v47"), "mask2"); ((TAtom "iw_1.v48"), "index2"); ((TAtom "iw_1.v5"), "table"); ((TAtom "iw_1.v50"), "table"); ((TAtom "iw_1.v51"), "lookup1"); ((TAtom "iw_1.v54"), "index2"); ((TAtom "iw_1.v58"), "lookup2"); ((TAtom "iw_1.v62"), "lookup2"); ((TAtom "iw_1.v65"), "table"); ((TAtom "iw_1.v67"), "mask3"); ((TAtom "iw_1.v69"), "wc"); ((TAtom "iw_1.v7"), "shift1"); ((TAtom "iw_1.v70"), "mask3"); ((TAtom "iw_1.v71"), "index3"); ((TAtom "iw_1.v73"), "table"); ((TAtom "iw_1.v74"), "lookup2"); ((TAtom "iw_1.v77"), "index3"); ((TAtom "iw_1.v81"), "lookup3"); ((TAtom "iw_1.v82"), "wc"); ((TAtom "iw_1.v83"), "lookup3"); ((TAtom "iw_1.v86"), "wc"); ((TAtom "iw_1.v9"), "wc"); ((TAtom "v0"), "wc"); ((TAtom "v14"), "i"); ((TAtom "v17"), "__libc_tsd_LOCALE"); ((TAtom "v21"), "i"); ((TAtom "v26"), "desc"); ((TAtom "v27"), "desc"); ((TAtom "v28"), "wc"); ((TAtom "v4"), "__libc_tsd_LOCALE")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__GI___towupper") (code_module memfwd_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___GI___towupper.

Module fn___ctype_b_loc.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("../include/ctype.h", 40%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("../include/ctype.h", 43%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__ctype_b_loc") (code_module memfwd_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___ctype_b_loc.

Module fn___ctype_toupper_loc.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("../include/ctype.h", 46%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("../include/ctype.h", 49%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__ctype_toupper_loc") (code_module memfwd_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___ctype_toupper_loc.

Module fn___ctype_tolower_loc.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("../include/ctype.h", 52%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("../include/ctype.h", 55%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__ctype_tolower_loc") (code_module memfwd_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___ctype_tolower_loc.

Module fn___GI___ctype_init.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("ctype-info.c", 35%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("ctype-info.c", 38%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v11"), "__libc_tsd_CTYPE_B"); ((TAtom "v14"), "__libc_tsd_LOCALE"); ((TAtom "v2"), "__libc_tsd_LOCALE"); ((TAtom "v23"), "__libc_tsd_CTYPE_TOUPPER"); ((TAtom "v26"), "__libc_tsd_LOCALE"); ((TAtom "v35"), "__libc_tsd_CTYPE_TOLOWER")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__GI___ctype_init") (code_module memfwd_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___GI___ctype_init.

Module fn___ctype_get_mb_cur_max.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("mb_cur_max.c", 26%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("mb_cur_max.c", 30%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v1"), "__libc_tsd_LOCALE")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__ctype_get_mb_cur_max") (code_module memfwd_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___ctype_get_mb_cur_max.

End MemFwdSrc.
