(** These tables connect checked function bodies to C declarations and source lines.
    Names and locations support annotations and diagnostic messages, not soundness premises.
    Natural-loop headers provide optional cuts for symbolic execution; any cut list is sound.
    Live sets and memory footprints guide execution but cannot justify a memory access.
    Computation checks that every recorded block label belongs to the decoded function.
    The code generator reproduces this file from the capture; do not edit it. *)

From Stdlib Require Import String List Bool NArith ZArith.
From Glibc Require Import CodePrelude.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.


From Glibc Require Import FflushCode.
Module FflushSrc.

Definition file_0 : string := "./libioP.h".

Definition file_1 : string := "iofflush.c".

Module fn___GI__IO_fflush.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_1, 30%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_1, 33%N)); ((TAtom "L2"), (file_1, 34%N)); ((TAtom "L15"), (file_1, 39%N)); ((TAtom "L27"), (file_1, 39%N)); ((TAtom "L38"), (file_1, 39%N)); ((TAtom "L39"), (file_1, 39%N)); ((TAtom "L32"), (file_1, 39%N)); ((TAtom "L33"), (file_1, 39%N)); ((TAtom "L58"), (file_1, 39%N)); ((TAtom "L82"), (file_1, 39%N)); ((TAtom "L83"), (file_1, 39%N)); ((TAtom "L87"), (file_1, 39%N)); ((TAtom "L76"), (file_1, 39%N)); ((TAtom "L59"), (file_1, 39%N)); ((TAtom "L22"), (file_1, 40%N)); ((TAtom "iw_1.L10"), (file_0, 1049%N)); ((TAtom "iw_1.join"), (file_1, 40%N)); ((TAtom "L109"), (file_1, 40%N)); ((TAtom "L110"), (file_1, 40%N)); ((TAtom "iw_2.L5"), (file_0, 1000%N)); ((TAtom "iw_2.L19"), (file_0, 1000%N)); ((TAtom "iw_2.L28"), (file_0, 1000%N)); ((TAtom "iw_2.L29"), (file_0, 1000%N)); ((TAtom "iw_2.L22"), (file_0, 1000%N)); ((TAtom "iw_2.L23"), (file_0, 1000%N)); ((TAtom "iw_2.L45"), (file_0, 1000%N)); ((TAtom "iw_2.L66"), (file_0, 1000%N)); ((TAtom "iw_2.L67"), (file_0, 1000%N)); ((TAtom "iw_2.L78"), (file_0, 1000%N)); ((TAtom "iw_2.L46"), (file_0, 1000%N)); ((TAtom "L17"), (file_1, 42%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "vtable"); ((TAtom "iw_1.v13"), "offset"); ((TAtom "iw_1.v18"), "vtable"); ((TAtom "iw_1.v3"), "vtable"); ((TAtom "iw_1.v4"), "ptr"); ((TAtom "iw_1.v6"), "ptr"); ((TAtom "iw_1.v9"), "offset"); ((TAtom "iw_2.v0"), "p"); ((TAtom "iw_2.v15"), "fp"); ((TAtom "iw_2.v26"), "__libc_single_threaded_internal"); ((TAtom "iw_2.v3"), "p"); ((TAtom "iw_2.v30"), "fp"); ((TAtom "iw_2.v38"), "fp"); ((TAtom "iw_2.v4"), "fp"); ((TAtom "iw_2.v42"), "fp"); ((TAtom "iw_2.v48"), "fp"); ((TAtom "iw_2.v54"), "fp"); ((TAtom "iw_2.v59"), "fp"); ((TAtom "iw_2.v61"), "__futex"); ((TAtom "iw_2.v64"), "__futex"); ((TAtom "iw_2.v68"), "__oldval"); ((TAtom "iw_2.v74"), "__oldval"); ((TAtom "iw_2.v8"), "fp"); ((TAtom "iw_2.v86"), "__futex"); ((TAtom "iw_2.v87"), "__futex"); ((TAtom "iw_2.v88"), "__private"); ((TAtom "iw_2.v89"), "fp"); ((TAtom "v0"), "fp"); ((TAtom "v101"), "__self"); ((TAtom "v102"), "_IO_acquire_lock_file"); ((TAtom "v111"), "fp"); ((TAtom "v117"), "fp"); ((TAtom "v120"), "result"); ((TAtom "v121"), "result"); ((TAtom "v19"), "fp"); ((TAtom "v23"), "_IO_acquire_lock_file"); ((TAtom "v31"), "__self"); ((TAtom "v36"), "__libc_single_threaded_internal"); ((TAtom "v40"), "_IO_acquire_lock_file"); ((TAtom "v5"), "fp"); ((TAtom "v50"), "_IO_acquire_lock_file"); ((TAtom "v53"), "_IO_acquire_lock_file"); ((TAtom "v57"), "__self"); ((TAtom "v61"), "_IO_acquire_lock_file"); ((TAtom "v66"), "__self"); ((TAtom "v71"), "_IO_acquire_lock_file"); ((TAtom "v73"), "__futex"); ((TAtom "v78"), "__futex"); ((TAtom "v79"), "__atg3_old"); ((TAtom "v80"), "__atg3_old"); ((TAtom "v95"), "__futex"); ((TAtom "v96"), "__futex"); ((TAtom "v97"), "_IO_acquire_lock_file")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "iw_2.L66")].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "L2"), []); ((TAtom "L15"), [(TAtom "v0"); (TAtom "v7")]); ((TAtom "L27"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v7")]); ((TAtom "L38"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v31"); (TAtom "v7")]); ((TAtom "L39"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v31")]); ((TAtom "L32"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v31")]); ((TAtom "L33"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v31")]); ((TAtom "L58"), [(TAtom "chk0"); (TAtom "chk8"); (TAtom "v0"); (TAtom "v31")]); ((TAtom "L82"), [(TAtom "chk0"); (TAtom "chk8"); (TAtom "v0"); (TAtom "v31"); (TAtom "v73"); (TAtom "v80")]); ((TAtom "L83"), [(TAtom "chk0"); (TAtom "chk8"); (TAtom "v0"); (TAtom "v31"); (TAtom "v73"); (TAtom "v80")]); ((TAtom "L87"), [(TAtom "chk0"); (TAtom "chk8"); (TAtom "v0"); (TAtom "v31"); (TAtom "v73")]); ((TAtom "L76"), [(TAtom "chk0"); (TAtom "chk8"); (TAtom "v0"); (TAtom "v31")]); ((TAtom "L59"), [(TAtom "chk0"); (TAtom "chk8"); (TAtom "v0")]); ((TAtom "L22"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "iw_1.L10"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v113")]); ((TAtom "iw_1.join"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v113")]); ((TAtom "L109"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L110"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "iw_2.L5"), [(TAtom "chk0"); (TAtom "chk20"); (TAtom "v0"); (TAtom "v120")]); ((TAtom "iw_2.L19"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v120")]); ((TAtom "iw_2.L28"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v120")]); ((TAtom "iw_2.L29"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v120")]); ((TAtom "iw_2.L22"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v120")]); ((TAtom "iw_2.L23"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v120")]); ((TAtom "iw_2.L45"), [(TAtom "chk29"); (TAtom "v0"); (TAtom "v120")]); ((TAtom "iw_2.L66"), [(TAtom "chk34"); (TAtom "iw_2.v61"); (TAtom "v120")]); ((TAtom "iw_2.L67"), [(TAtom "iw_2.v61"); (TAtom "iw_2.v68"); (TAtom "v120")]); ((TAtom "iw_2.L78"), [(TAtom "iw_2.v61"); (TAtom "v120")]); ((TAtom "iw_2.L46"), [(TAtom "chk29"); (TAtom "v0"); (TAtom "v120")]); ((TAtom "L17"), [(TAtom "v120")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v7")]); ((TAtom "L2"), []); ((TAtom "L15"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v7")]); ((TAtom "L27"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v31"); (TAtom "v7")]); ((TAtom "L38"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v31"); (TAtom "v47")]); ((TAtom "L39"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v31")]); ((TAtom "L32"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L33"), [(TAtom "chk0"); (TAtom "chk8"); (TAtom "v0"); (TAtom "v31")]); ((TAtom "L58"), [(TAtom "chk0"); (TAtom "chk8"); (TAtom "v0"); (TAtom "v31"); (TAtom "v73"); (TAtom "v80")]); ((TAtom "L82"), [(TAtom "chk0"); (TAtom "chk8"); (TAtom "v0"); (TAtom "v31"); (TAtom "v73"); (TAtom "v80")]); ((TAtom "L83"), [(TAtom "chk0"); (TAtom "chk8"); (TAtom "v0"); (TAtom "v31"); (TAtom "v73")]); ((TAtom "L87"), [(TAtom "chk0"); (TAtom "chk8"); (TAtom "v0"); (TAtom "v31")]); ((TAtom "L76"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L59"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L22"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v113")]); ((TAtom "iw_1.L10"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v113")]); ((TAtom "iw_1.join"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L109"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L110"), [(TAtom "chk0"); (TAtom "chk20"); (TAtom "v0"); (TAtom "v120")]); ((TAtom "iw_2.L5"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v120")]); ((TAtom "iw_2.L19"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v120")]); ((TAtom "iw_2.L28"), [(TAtom "chk0"); (TAtom "iw_2.v35"); (TAtom "v0"); (TAtom "v120")]); ((TAtom "iw_2.L29"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v120")]); ((TAtom "iw_2.L22"), [(TAtom "v120")]); ((TAtom "iw_2.L23"), [(TAtom "chk29"); (TAtom "v0"); (TAtom "v120")]); ((TAtom "iw_2.L45"), [(TAtom "chk34"); (TAtom "iw_2.v61"); (TAtom "iw_2.v65"); (TAtom "v120")]); ((TAtom "iw_2.L66"), [(TAtom "chk34"); (TAtom "iw_2.v61"); (TAtom "iw_2.v68"); (TAtom "iw_2.v69"); (TAtom "v120")]); ((TAtom "iw_2.L67"), [(TAtom "iw_2.v61"); (TAtom "v120")]); ((TAtom "iw_2.L78"), [(TAtom "v120")]); ((TAtom "iw_2.L46"), [(TAtom "v120")]); ((TAtom "L17"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), []); ((TAtom "L2"), []); ((TAtom "L15"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0)), "_IO_acquire_lock_file->_flags")]); ((TAtom "L27"), [(3%N, (TApp "tmp" [(TAtom "v35")]), (0), (Some 1), true, false, (Some (TAtom "v35")), (Some (0)), "opaque")]); ((TAtom "L38"), [(2%N, (TApp "tmp" [(TAtom "v41")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136)), "_IO_acquire_lock_file->_lock"); (5%N, (TApp "tmp" [(TAtom "v43")]), (0), (Some 8), true, false, (Some (TAtom "v42")), (Some (8)), "_IO_acquire_lock_file->_lock->owner")]); ((TAtom "L39"), []); ((TAtom "L32"), [(2%N, (TApp "tmp" [(TAtom "v51")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136)), "_IO_acquire_lock_file->_lock"); (4%N, (TApp "tmp" [(TAtom "v52")]), (0), (Some 4), false, true, (Some (TAtom "v52")), (Some (0)), "_IO_acquire_lock_file->_lock->lock"); (5%N, (TApp "tmp" [(TAtom "v51")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136)), "_IO_acquire_lock_file->_lock"); (8%N, (TApp "tmp" [(TAtom "v56")]), (0), (Some 8), false, true, (Some (TAtom "v55")), (Some (8)), "_IO_acquire_lock_file->_lock->owner")]); ((TAtom "L33"), [(2%N, (TApp "tmp" [(TAtom "v62")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136)), "_IO_acquire_lock_file->_lock"); (5%N, (TApp "tmp" [(TAtom "v64")]), (0), (Some 8), true, false, (Some (TAtom "v63")), (Some (8)), "_IO_acquire_lock_file->_lock->owner")]); ((TAtom "L58"), [(1%N, (TApp "tmp" [(TAtom "v62")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136)), "_IO_acquire_lock_file->_lock"); (3%N, (TApp "tmp" [(TAtom "v73")]), (0), (Some 4), true, true, (Some (TAtom "v73")), (Some (0)), "opaque")]); ((TAtom "L82"), []); ((TAtom "L83"), []); ((TAtom "L87"), []); ((TAtom "L76"), [(2%N, (TApp "tmp" [(TAtom "v98")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136)), "_IO_acquire_lock_file->_lock"); (5%N, (TApp "tmp" [(TAtom "v100")]), (0), (Some 8), false, true, (Some (TAtom "v99")), (Some (8)), "_IO_acquire_lock_file->_lock->owner")]); ((TAtom "L59"), [(1%N, (TApp "tmp" [(TAtom "v62")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136)), "_IO_acquire_lock_file->_lock"); (4%N, (TApp "tmp" [(TAtom "v105")]), (0), (Some 4), true, false, (Some (TAtom "v104")), (Some (4)), "_IO_acquire_lock_file->_lock->cnt"); (7%N, (TApp "tmp" [(TAtom "v105")]), (0), (Some 4), false, true, (Some (TAtom "v104")), (Some (4)), "_IO_acquire_lock_file->_lock->cnt")]); ((TAtom "L22"), [(2%N, (TApp "tmp" [(TAtom "v112")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (216)), "opaque")]); ((TAtom "iw_1.L10"), []); ((TAtom "iw_1.join"), [(2%N, (TApp "tmp" [(TAtom "v115")]), (0), (Some 8), true, false, (Some (TAtom "v113")), (Some (96)), "opaque")]); ((TAtom "L109"), []); ((TAtom "L110"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0)), "fp->_flags")]); ((TAtom "iw_2.L5"), [(0%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0)), "fp->_flags")]); ((TAtom "iw_2.L19"), [(2%N, (TApp "tmp" [(TAtom "iw_2.v25")]), (0), (Some 1), true, false, (Some (TAtom "iw_2.v25")), (Some (0)), "opaque")]); ((TAtom "iw_2.L28"), [(2%N, (TApp "tmp" [(TAtom "iw_2.v31")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136)), "fp->_lock"); (5%N, (TApp "tmp" [(TAtom "iw_2.v33")]), (0), (Some 4), true, false, (Some (TAtom "iw_2.v32")), (Some (4)), "opaque")]); ((TAtom "iw_2.L29"), []); ((TAtom "iw_2.L22"), [(2%N, (TApp "tmp" [(TAtom "iw_2.v39")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136)), "fp->_lock"); (5%N, (TApp "tmp" [(TAtom "iw_2.v41")]), (0), (Some 8), false, true, (Some (TAtom "iw_2.v40")), (Some (8)), "opaque"); (7%N, (TApp "tmp" [(TAtom "iw_2.v39")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136)), "fp->_lock"); (9%N, (TApp "tmp" [(TAtom "iw_2.v44")]), (0), (Some 4), false, true, (Some (TAtom "iw_2.v44")), (Some (0)), "opaque")]); ((TAtom "iw_2.L23"), [(2%N, (TApp "tmp" [(TAtom "iw_2.v49")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136)), "fp->_lock"); (5%N, (TApp "tmp" [(TAtom "iw_2.v51")]), (0), (Some 4), true, false, (Some (TAtom "iw_2.v50")), (Some (4)), "opaque")]); ((TAtom "iw_2.L45"), [(1%N, (TApp "tmp" [(TAtom "iw_2.v49")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136)), "fp->_lock"); (4%N, (TApp "tmp" [(TAtom "iw_2.v57")]), (0), (Some 8), false, true, (Some (TAtom "iw_2.v56")), (Some (8)), "opaque"); (6%N, (TApp "tmp" [(TAtom "iw_2.v55")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136)), "fp->_lock"); (8%N, (TApp "tmp" [(TAtom "iw_2.v61")]), (0), (Some 4), true, false, (Some (TAtom "iw_2.v61")), (Some (0)), "opaque")]); ((TAtom "iw_2.L66"), [(1%N, (TApp "tmp" [(TAtom "iw_2.v61")]), (0), (Some 4), true, true, (Some (TAtom "iw_2.v61")), (Some (0)), "opaque")]); ((TAtom "iw_2.L67"), []); ((TAtom "iw_2.L78"), []); ((TAtom "iw_2.L46"), [(1%N, (TApp "tmp" [(TAtom "iw_2.v49")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136)), "fp->_lock"); (4%N, (TApp "tmp" [(TAtom "iw_2.v92")]), (0), (Some 4), true, false, (Some (TAtom "iw_2.v91")), (Some (4)), "opaque"); (7%N, (TApp "tmp" [(TAtom "iw_2.v92")]), (0), (Some 4), false, true, (Some (TAtom "iw_2.v91")), (Some (4)), "opaque")]); ((TAtom "L17"), [])].


End fn___GI__IO_fflush.

(** Projection keeps instruction bodies out of the VM code used by the membership check. *)
Definition source_blocks : list (string * option (list name)) := Eval lazy in
  map (fun n => (n,
    match find_direct (TAtom n) fflush_module with
    | Some (Defined f) => Some (map b_label (fn_blocks f))
    | _ => None
    end)) ["__GI__IO_fflush"].

(** Projection keeps live sets and memory access records out of the membership computation. *)
Definition table_labels : list (string * list name) := Eval lazy in
  [("__GI__IO_fflush", app (map fst fn___GI__IO_fflush.block_src) (app (map fst fn___GI__IO_fflush.live_in) (app (map fst fn___GI__IO_fflush.live_out) (app (map fst fn___GI__IO_fflush.footprint) (fn___GI__IO_fflush.loop_heads)))))].

(** One computation rejects missing functions and stale labels across all tables in this fixture. *)
Lemma labels_valid :
  forallb (fun row =>
  match find (fun entry => String.eqb (fst entry) (fst row)) source_blocks with
  | Some (_, Some labels) =>
      forallb (fun l => existsb (name_eqb l) labels)
        (snd row)
  | _ => false
  end) table_labels = true.
Proof. vm_compute. reflexivity. Qed.

End FflushSrc.
