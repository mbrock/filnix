(** These tables connect checked function bodies to C declarations and source lines.
    Names and locations support annotations and diagnostic messages, not soundness premises.
    Natural-loop headers provide optional cuts for symbolic execution; any cut list is sound.
    Computation checks that every recorded block label belongs to the decoded function.
    The code generator reproduces this file from the capture; do not edit it. *)

From Stdlib Require Import String List Bool NArith.
From Glibc Require Import CodePrelude.
Import ListNotations.
Open Scope string_scope.


From Glibc Require Import MemFwdCode.
Module MemFwdSrc.

Definition file_0 : string := "../include/ctype.h".

Definition file_1 : string := "./wchar-lookup.h".

Definition file_2 : string := "ctype-info.c".

Definition file_3 : string := "errno-loc.c".

Definition file_4 : string := "mb_cur_max.c".

Definition file_5 : string := "mbsinit.c".

Definition file_6 : string := "memcpy.c".

Definition file_7 : string := "mempcpy.c".

Definition file_8 : string := "memset.c".

Definition file_9 : string := "strdup.c".

Definition file_10 : string := "wcfuncs.c".

Module fn___GI_memcpy.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_6, 28%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_6, 37%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "dstpp"); ((TAtom "v2"), "srcpp"); ((TAtom "v4"), "len"); ((TAtom "v6"), "dstpp"); ((TAtom "v7"), "srcpp"); ((TAtom "v8"), "len"); ((TAtom "v9"), "dstpp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

End fn___GI_memcpy.

Module fn___GI___mempcpy.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_7, 32%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_7, 35%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "dest"); ((TAtom "v10"), "len"); ((TAtom "v2"), "src"); ((TAtom "v4"), "len"); ((TAtom "v6"), "dest"); ((TAtom "v7"), "src"); ((TAtom "v8"), "len")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

End fn___GI___mempcpy.

Module fn___GI_memset.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_8, 26%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_8, 29%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "dstpp"); ((TAtom "v2"), "c"); ((TAtom "v4"), "len"); ((TAtom "v6"), "dstpp"); ((TAtom "v7"), "c"); ((TAtom "v8"), "len"); ((TAtom "v9"), "dstpp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

End fn___GI_memset.

Module fn___GI___strdup.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_9, 38%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_9, 41%N)); ((TAtom "L9"), (file_9, 45%N)); ((TAtom "L11"), (file_9, 47%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "s"); ((TAtom "v12"), "new"); ((TAtom "v17"), "new"); ((TAtom "v18"), "s"); ((TAtom "v19"), "len"); ((TAtom "v3"), "s"); ((TAtom "v5"), "len"); ((TAtom "v7"), "len"); ((TAtom "v8"), "new")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

End fn___GI___strdup.

Module fn___GI___errno_location.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_3, 23%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_3, 26%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

End fn___GI___errno_location.

Module fn___mbsinit.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_5, 32%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_5, 35%N)); ((TAtom "L6"), (file_5, 35%N)); ((TAtom "L7"), (file_5, 35%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "ps"); ((TAtom "v2"), "ps"); ((TAtom "v8"), "ps")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

End fn___mbsinit.

Module fn___GI___towlower.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_10, 73%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_10, 76%N)); ((TAtom "iw_1.L16"), (file_1, 124%N)); ((TAtom "iw_1.L30"), (file_1, 127%N)); ((TAtom "iw_1.L59"), (file_1, 133%N)); ((TAtom "iw_1.join"), (file_10, 78%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "table"); ((TAtom "iw_1.v10"), "shift1"); ((TAtom "iw_1.v11"), "index1"); ((TAtom "iw_1.v13"), "table"); ((TAtom "iw_1.v15"), "bound"); ((TAtom "iw_1.v19"), "index1"); ((TAtom "iw_1.v2"), "wc"); ((TAtom "iw_1.v20"), "bound"); ((TAtom "iw_1.v23"), "table"); ((TAtom "iw_1.v24"), "index1"); ((TAtom "iw_1.v29"), "lookup1"); ((TAtom "iw_1.v33"), "lookup1"); ((TAtom "iw_1.v36"), "table"); ((TAtom "iw_1.v38"), "shift2"); ((TAtom "iw_1.v40"), "table"); ((TAtom "iw_1.v42"), "mask2"); ((TAtom "iw_1.v44"), "wc"); ((TAtom "iw_1.v45"), "shift2"); ((TAtom "iw_1.v47"), "mask2"); ((TAtom "iw_1.v48"), "index2"); ((TAtom "iw_1.v5"), "table"); ((TAtom "iw_1.v50"), "table"); ((TAtom "iw_1.v51"), "lookup1"); ((TAtom "iw_1.v54"), "index2"); ((TAtom "iw_1.v58"), "lookup2"); ((TAtom "iw_1.v62"), "lookup2"); ((TAtom "iw_1.v65"), "table"); ((TAtom "iw_1.v67"), "mask3"); ((TAtom "iw_1.v69"), "wc"); ((TAtom "iw_1.v7"), "shift1"); ((TAtom "iw_1.v70"), "mask3"); ((TAtom "iw_1.v71"), "index3"); ((TAtom "iw_1.v73"), "table"); ((TAtom "iw_1.v74"), "lookup2"); ((TAtom "iw_1.v77"), "index3"); ((TAtom "iw_1.v81"), "lookup3"); ((TAtom "iw_1.v82"), "wc"); ((TAtom "iw_1.v83"), "lookup3"); ((TAtom "iw_1.v86"), "wc"); ((TAtom "iw_1.v9"), "wc"); ((TAtom "v0"), "wc"); ((TAtom "v14"), "i"); ((TAtom "v17"), "__libc_tsd_LOCALE"); ((TAtom "v21"), "i"); ((TAtom "v26"), "desc"); ((TAtom "v27"), "desc"); ((TAtom "v28"), "wc"); ((TAtom "v4"), "__libc_tsd_LOCALE")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

End fn___GI___towlower.

Module fn___GI___towupper.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_10, 85%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_10, 88%N)); ((TAtom "iw_1.L16"), (file_1, 124%N)); ((TAtom "iw_1.L30"), (file_1, 127%N)); ((TAtom "iw_1.L59"), (file_1, 133%N)); ((TAtom "iw_1.join"), (file_10, 90%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "table"); ((TAtom "iw_1.v10"), "shift1"); ((TAtom "iw_1.v11"), "index1"); ((TAtom "iw_1.v13"), "table"); ((TAtom "iw_1.v15"), "bound"); ((TAtom "iw_1.v19"), "index1"); ((TAtom "iw_1.v2"), "wc"); ((TAtom "iw_1.v20"), "bound"); ((TAtom "iw_1.v23"), "table"); ((TAtom "iw_1.v24"), "index1"); ((TAtom "iw_1.v29"), "lookup1"); ((TAtom "iw_1.v33"), "lookup1"); ((TAtom "iw_1.v36"), "table"); ((TAtom "iw_1.v38"), "shift2"); ((TAtom "iw_1.v40"), "table"); ((TAtom "iw_1.v42"), "mask2"); ((TAtom "iw_1.v44"), "wc"); ((TAtom "iw_1.v45"), "shift2"); ((TAtom "iw_1.v47"), "mask2"); ((TAtom "iw_1.v48"), "index2"); ((TAtom "iw_1.v5"), "table"); ((TAtom "iw_1.v50"), "table"); ((TAtom "iw_1.v51"), "lookup1"); ((TAtom "iw_1.v54"), "index2"); ((TAtom "iw_1.v58"), "lookup2"); ((TAtom "iw_1.v62"), "lookup2"); ((TAtom "iw_1.v65"), "table"); ((TAtom "iw_1.v67"), "mask3"); ((TAtom "iw_1.v69"), "wc"); ((TAtom "iw_1.v7"), "shift1"); ((TAtom "iw_1.v70"), "mask3"); ((TAtom "iw_1.v71"), "index3"); ((TAtom "iw_1.v73"), "table"); ((TAtom "iw_1.v74"), "lookup2"); ((TAtom "iw_1.v77"), "index3"); ((TAtom "iw_1.v81"), "lookup3"); ((TAtom "iw_1.v82"), "wc"); ((TAtom "iw_1.v83"), "lookup3"); ((TAtom "iw_1.v86"), "wc"); ((TAtom "iw_1.v9"), "wc"); ((TAtom "v0"), "wc"); ((TAtom "v14"), "i"); ((TAtom "v17"), "__libc_tsd_LOCALE"); ((TAtom "v21"), "i"); ((TAtom "v26"), "desc"); ((TAtom "v27"), "desc"); ((TAtom "v28"), "wc"); ((TAtom "v4"), "__libc_tsd_LOCALE")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

End fn___GI___towupper.

Module fn___ctype_b_loc.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_0, 40%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_0, 43%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

End fn___ctype_b_loc.

Module fn___ctype_toupper_loc.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_0, 46%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_0, 49%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

End fn___ctype_toupper_loc.

Module fn___ctype_tolower_loc.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_0, 52%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_0, 55%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

End fn___ctype_tolower_loc.

Module fn___GI___ctype_init.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_2, 35%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_2, 38%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v11"), "__libc_tsd_CTYPE_B"); ((TAtom "v14"), "__libc_tsd_LOCALE"); ((TAtom "v2"), "__libc_tsd_LOCALE"); ((TAtom "v23"), "__libc_tsd_CTYPE_TOUPPER"); ((TAtom "v26"), "__libc_tsd_LOCALE"); ((TAtom "v35"), "__libc_tsd_CTYPE_TOLOWER")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

End fn___GI___ctype_init.

Module fn___ctype_get_mb_cur_max.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_4, 26%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_4, 30%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v1"), "__libc_tsd_LOCALE")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

End fn___ctype_get_mb_cur_max.

(** Projection keeps instruction bodies out of the VM code used by the membership check. *)
Definition source_blocks : list (string * option (list name)) := Eval lazy in
  map (fun n => (n,
    match find_direct (TAtom n) memfwd_module with
    | Some (Defined f) => Some (map b_label (fn_blocks f))
    | _ => None
    end)) ["__GI_memcpy"; "__GI___mempcpy"; "__GI_memset"; "__GI___strdup"; "__GI___errno_location"; "__mbsinit"; "__GI___towlower"; "__GI___towupper"; "__ctype_b_loc"; "__ctype_toupper_loc"; "__ctype_tolower_loc"; "__GI___ctype_init"; "__ctype_get_mb_cur_max"].

(** One computation rejects missing functions and stale labels across all tables in this fixture. *)
Lemma labels_valid :
  forallb (fun row =>
  match find (fun entry => String.eqb (fst entry) (fst row)) source_blocks with
  | Some (_, Some labels) =>
      forallb (fun l => existsb (name_eqb l) labels)
        (snd row)
  | _ => false
  end) [("__GI_memcpy", app (map fst fn___GI_memcpy.block_src) fn___GI_memcpy.loop_heads); ("__GI___mempcpy", app (map fst fn___GI___mempcpy.block_src) fn___GI___mempcpy.loop_heads); ("__GI_memset", app (map fst fn___GI_memset.block_src) fn___GI_memset.loop_heads); ("__GI___strdup", app (map fst fn___GI___strdup.block_src) fn___GI___strdup.loop_heads); ("__GI___errno_location", app (map fst fn___GI___errno_location.block_src) fn___GI___errno_location.loop_heads); ("__mbsinit", app (map fst fn___mbsinit.block_src) fn___mbsinit.loop_heads); ("__GI___towlower", app (map fst fn___GI___towlower.block_src) fn___GI___towlower.loop_heads); ("__GI___towupper", app (map fst fn___GI___towupper.block_src) fn___GI___towupper.loop_heads); ("__ctype_b_loc", app (map fst fn___ctype_b_loc.block_src) fn___ctype_b_loc.loop_heads); ("__ctype_toupper_loc", app (map fst fn___ctype_toupper_loc.block_src) fn___ctype_toupper_loc.loop_heads); ("__ctype_tolower_loc", app (map fst fn___ctype_tolower_loc.block_src) fn___ctype_tolower_loc.loop_heads); ("__GI___ctype_init", app (map fst fn___GI___ctype_init.block_src) fn___GI___ctype_init.loop_heads); ("__ctype_get_mb_cur_max", app (map fst fn___ctype_get_mb_cur_max.block_src) fn___ctype_get_mb_cur_max.loop_heads)] = true.
Proof. vm_compute. reflexivity. Qed.

End MemFwdSrc.
