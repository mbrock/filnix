(** These tables connect checked function bodies to C declarations and source lines.
    Names and locations support annotations and diagnostic messages, not soundness premises.
    Natural-loop headers provide optional cuts for symbolic execution; any cut list is sound.
    Live sets and memory footprints guide execution but cannot justify a memory access.
    Computation checks that every recorded block label belongs to its function.
    The code generator reproduces this file from the capture; do not edit it. *)

From Stdlib Require Import String List Bool NArith ZArith.
From Glibc Require Import CodePrelude.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

From Glibc Require Import Unit_libio___fpending_os Unit_libio_ferror_os Unit_libio_filedoalloc_os Unit_libio_fileops_os Unit_libio_genops_os Unit_misc_makedev_os.

Module LibioReadSrc.

Definition file_0 : string := "./libioP.h".

Definition file_1 : string := "__fpending.c".

Definition file_2 : string := "ferror.c".

Definition file_3 : string := "filedoalloc.c".

Definition file_4 : string := "fileops.c".

Definition file_5 : string := "genops.c".

Definition file_6 : string := "makedev.c".

Module fn___fpending.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_1, 20%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_1, 23%N)); ((TAtom "L2"), (file_1, 24%N)); ((TAtom "L3"), (file_1, 26%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fp"); ((TAtom "v14"), "fp"); ((TAtom "v24"), "fp"); ((TAtom "v27"), "fp"); ((TAtom "v5"), "fp"); ((TAtom "v9"), "fp")].

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  [((TAtom "chk0"), ((TAtom "v0"), "fp", 192)); ((TAtom "chk1"), ((TAtom "v0"), "fp", 160)); ((TAtom "chk2"), ((TAtom "v11"), "v11", 32)); ((TAtom "chk4"), ((TAtom "v16"), "v16", 24)); ((TAtom "chk5"), ((TAtom "v0"), "fp", 40)); ((TAtom "chk6"), ((TAtom "v0"), "fp", 32)); ((TAtom "v0"), ((TAtom "v0"), "fp", 0)); ((TAtom "v10"), ((TAtom "v0"), "fp", 160)); ((TAtom "v12"), ((TAtom "v11"), "v11", 32)); ((TAtom "v17"), ((TAtom "v16"), "v16", 24)); ((TAtom "v25"), ((TAtom "v0"), "fp", 40)); ((TAtom "v28"), ((TAtom "v0"), "fp", 32)); ((TAtom "v6"), ((TAtom "v0"), "fp", 192))].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "L2"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L3"), [(TAtom "chk0"); (TAtom "v0")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L2"), []); ((TAtom "L3"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "v6")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (192)), "fp->_mode")]); ((TAtom "L2"), [(2%N, (TApp "tmp" [(TAtom "v10")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (160)), "fp->_wide_data"); (5%N, (TApp "tmp" [(TAtom "v12")]), (0), (Some 8), true, false, (Some (TAtom "v11")), (Some (32)), "fp->_wide_data->_IO_write_ptr"); (6%N, (TApp "tmp" [(TAtom "v10")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (160)), "fp->_wide_data"); (9%N, (TApp "tmp" [(TAtom "v17")]), (0), (Some 8), true, false, (Some (TAtom "v16")), (Some (24)), "fp->_wide_data->_IO_write_base")]); ((TAtom "L3"), [(2%N, (TApp "tmp" [(TAtom "v25")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (40)), "fp->_IO_write_ptr"); (5%N, (TApp "tmp" [(TAtom "v28")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (32)), "fp->_IO_write_base")])].


End fn___fpending.

Module fn__IO_ferror.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_2, 30%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_2, 35%N)); ((TAtom "L6"), (file_2, 36%N)); ((TAtom "L8"), (file_2, 37%N)); ((TAtom "L29"), (file_2, 37%N)); ((TAtom "L40"), (file_2, 37%N)); ((TAtom "L41"), (file_2, 37%N)); ((TAtom "L34"), (file_2, 37%N)); ((TAtom "L35"), (file_2, 37%N)); ((TAtom "L60"), (file_2, 37%N)); ((TAtom "L84"), (file_2, 37%N)); ((TAtom "L85"), (file_2, 37%N)); ((TAtom "L89"), (file_2, 37%N)); ((TAtom "L78"), (file_2, 37%N)); ((TAtom "L61"), (file_2, 37%N)); ((TAtom "L24"), (file_2, 38%N)); ((TAtom "L121"), (file_2, 39%N)); ((TAtom "L130"), (file_2, 39%N)); ((TAtom "L131"), (file_2, 39%N)); ((TAtom "L124"), (file_2, 39%N)); ((TAtom "L125"), (file_2, 39%N)); ((TAtom "L147"), (file_2, 39%N)); ((TAtom "L168"), (file_2, 39%N)); ((TAtom "L169"), (file_2, 39%N)); ((TAtom "L180"), (file_2, 39%N)); ((TAtom "L148"), (file_2, 39%N)); ((TAtom "L116"), (file_2, 40%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fp"); ((TAtom "v103"), "__self"); ((TAtom "v104"), "fp"); ((TAtom "v110"), "fp"); ((TAtom "v113"), "result"); ((TAtom "v117"), "fp"); ((TAtom "v128"), "__libc_single_threaded_internal"); ((TAtom "v132"), "fp"); ((TAtom "v140"), "fp"); ((TAtom "v144"), "fp"); ((TAtom "v150"), "fp"); ((TAtom "v156"), "fp"); ((TAtom "v161"), "fp"); ((TAtom "v163"), "__futex"); ((TAtom "v166"), "__futex"); ((TAtom "v17"), "fp"); ((TAtom "v170"), "__oldval"); ((TAtom "v176"), "__oldval"); ((TAtom "v188"), "__futex"); ((TAtom "v189"), "__futex"); ((TAtom "v190"), "__private"); ((TAtom "v191"), "fp"); ((TAtom "v197"), "result"); ((TAtom "v25"), "fp"); ((TAtom "v33"), "__self"); ((TAtom "v38"), "__libc_single_threaded_internal"); ((TAtom "v42"), "fp"); ((TAtom "v52"), "fp"); ((TAtom "v55"), "fp"); ((TAtom "v59"), "__self"); ((TAtom "v63"), "fp"); ((TAtom "v68"), "__self"); ((TAtom "v73"), "fp"); ((TAtom "v75"), "__futex"); ((TAtom "v80"), "__futex"); ((TAtom "v81"), "__atg3_old"); ((TAtom "v82"), "__atg3_old"); ((TAtom "v9"), "fp"); ((TAtom "v97"), "__futex"); ((TAtom "v98"), "__futex"); ((TAtom "v99"), "fp")].

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  [((TAtom "chk0"), ((TAtom "v0"), "fp", 116)); ((TAtom "chk1"), ((TAtom "v0"), "fp", 0)); ((TAtom "chk10"), ((TAtom "v0"), "fp", 136)); ((TAtom "chk11"), ((TAtom "v65"), "v65", 8)); ((TAtom "chk13"), ((TAtom "v75"), "__futex", 0)); ((TAtom "chk14"), ((TAtom "v0"), "fp", 136)); ((TAtom "chk15"), ((TAtom "v101"), "v101", 8)); ((TAtom "chk17"), ((TAtom "v106"), "v106", 4)); ((TAtom "chk18"), ((TAtom "v106"), "v106", 4)); ((TAtom "chk19"), ((TAtom "v0"), "fp", 0)); ((TAtom "chk2"), ((TAtom "v0"), "fp", 0)); ((TAtom "chk21"), ((TAtom "v127"), "&__libc_single_threaded_internal", 0)); ((TAtom "chk22"), ((TAtom "v0"), "fp", 136)); ((TAtom "chk23"), ((TAtom "v134"), "v134", 4)); ((TAtom "chk24"), ((TAtom "v0"), "fp", 136)); ((TAtom "chk25"), ((TAtom "v142"), "v142", 8)); ((TAtom "chk26"), ((TAtom "v0"), "fp", 136)); ((TAtom "chk27"), ((TAtom "v146"), "v146", 0)); ((TAtom "chk28"), ((TAtom "v0"), "fp", 136)); ((TAtom "chk29"), ((TAtom "v152"), "v152", 4)); ((TAtom "chk3"), ((TAtom "v37"), "&__libc_single_threaded_internal", 0)); ((TAtom "chk31"), ((TAtom "v158"), "v158", 8)); ((TAtom "chk32"), ((TAtom "v0"), "fp", 136)); ((TAtom "chk33"), ((TAtom "v163"), "__futex", 0)); ((TAtom "chk34"), ((TAtom "v163"), "__futex", 0)); ((TAtom "chk36"), ((TAtom "v193"), "v193", 4)); ((TAtom "chk37"), ((TAtom "v193"), "v193", 4)); ((TAtom "chk4"), ((TAtom "v0"), "fp", 136)); ((TAtom "chk5"), ((TAtom "v44"), "v44", 8)); ((TAtom "chk6"), ((TAtom "v0"), "fp", 136)); ((TAtom "chk7"), ((TAtom "v54"), "v54", 0)); ((TAtom "chk9"), ((TAtom "v57"), "v57", 8)); ((TAtom "v0"), ((TAtom "v0"), "fp", 0)); ((TAtom "v10"), ((TAtom "v0"), "fp", 116)); ((TAtom "v100"), ((TAtom "v0"), "fp", 136)); ((TAtom "v102"), ((TAtom "v101"), "v101", 8)); ((TAtom "v105"), ((TAtom "v0"), "fp", 136)); ((TAtom "v107"), ((TAtom "v106"), "v106", 4)); ((TAtom "v113"), ((TAtom "v113"), "result", 0)); ((TAtom "v127"), ((TAtom "v127"), "&__libc_single_threaded_internal", 0)); ((TAtom "v128"), ((TAtom "v128"), "__libc_single_threaded_internal", 0)); ((TAtom "v133"), ((TAtom "v0"), "fp", 136)); ((TAtom "v135"), ((TAtom "v134"), "v134", 4)); ((TAtom "v141"), ((TAtom "v0"), "fp", 136)); ((TAtom "v143"), ((TAtom "v142"), "v142", 8)); ((TAtom "v151"), ((TAtom "v0"), "fp", 136)); ((TAtom "v153"), ((TAtom "v152"), "v152", 4)); ((TAtom "v157"), ((TAtom "v0"), "fp", 136)); ((TAtom "v159"), ((TAtom "v158"), "v158", 8)); ((TAtom "v163"), ((TAtom "v163"), "__futex", 0)); ((TAtom "v170"), ((TAtom "v170"), "__oldval", 0)); ((TAtom "v192"), ((TAtom "v0"), "fp", 136)); ((TAtom "v194"), ((TAtom "v193"), "v193", 4)); ((TAtom "v33"), ((TAtom "v33"), "__self", 0)); ((TAtom "v37"), ((TAtom "v37"), "&__libc_single_threaded_internal", 0)); ((TAtom "v38"), ((TAtom "v38"), "__libc_single_threaded_internal", 0)); ((TAtom "v43"), ((TAtom "v0"), "fp", 136)); ((TAtom "v45"), ((TAtom "v44"), "v44", 8)); ((TAtom "v53"), ((TAtom "v0"), "fp", 136)); ((TAtom "v58"), ((TAtom "v57"), "v57", 8)); ((TAtom "v64"), ((TAtom "v0"), "fp", 136)); ((TAtom "v66"), ((TAtom "v65"), "v65", 8)); ((TAtom "v74"), ((TAtom "v0"), "fp", 136)); ((TAtom "v75"), ((TAtom "v75"), "__futex", 0)); ((TAtom "v82"), ((TAtom "v82"), "__atg3_old", 0))].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L168")].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "L6"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L8"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L29"), [(TAtom "chk0"); (TAtom "chk2"); (TAtom "v0")]); ((TAtom "L40"), [(TAtom "chk0"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v33")]); ((TAtom "L41"), [(TAtom "chk0"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v33")]); ((TAtom "L34"), [(TAtom "chk0"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v33")]); ((TAtom "L35"), [(TAtom "chk0"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v33")]); ((TAtom "L60"), [(TAtom "chk0"); (TAtom "chk10"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v33")]); ((TAtom "L84"), [(TAtom "chk0"); (TAtom "chk10"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v33"); (TAtom "v75"); (TAtom "v82")]); ((TAtom "L85"), [(TAtom "chk0"); (TAtom "chk10"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v33"); (TAtom "v75"); (TAtom "v82")]); ((TAtom "L89"), [(TAtom "chk0"); (TAtom "chk10"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v33"); (TAtom "v75")]); ((TAtom "L78"), [(TAtom "chk0"); (TAtom "chk10"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v33")]); ((TAtom "L61"), [(TAtom "chk0"); (TAtom "chk10"); (TAtom "chk2"); (TAtom "v0")]); ((TAtom "L24"), [(TAtom "chk0"); (TAtom "chk2"); (TAtom "v0")]); ((TAtom "L121"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v113")]); ((TAtom "L130"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v113")]); ((TAtom "L131"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v113")]); ((TAtom "L124"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v113")]); ((TAtom "L125"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v113")]); ((TAtom "L147"), [(TAtom "chk28"); (TAtom "v0"); (TAtom "v113")]); ((TAtom "L168"), [(TAtom "chk33"); (TAtom "v113"); (TAtom "v163")]); ((TAtom "L169"), [(TAtom "v113"); (TAtom "v163"); (TAtom "v170")]); ((TAtom "L180"), [(TAtom "v113"); (TAtom "v163")]); ((TAtom "L148"), [(TAtom "chk28"); (TAtom "v0"); (TAtom "v113")]); ((TAtom "L116"), [(TAtom "v113")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L6"), []); ((TAtom "L8"), [(TAtom "chk0"); (TAtom "chk2"); (TAtom "v0")]); ((TAtom "L29"), [(TAtom "chk0"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v33")]); ((TAtom "L40"), [(TAtom "chk0"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v33"); (TAtom "v49")]); ((TAtom "L41"), [(TAtom "chk0"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v33")]); ((TAtom "L34"), [(TAtom "chk0"); (TAtom "chk2"); (TAtom "v0")]); ((TAtom "L35"), [(TAtom "chk0"); (TAtom "chk10"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v33")]); ((TAtom "L60"), [(TAtom "chk0"); (TAtom "chk10"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v33"); (TAtom "v75"); (TAtom "v82")]); ((TAtom "L84"), [(TAtom "chk0"); (TAtom "chk10"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v33"); (TAtom "v75"); (TAtom "v82")]); ((TAtom "L85"), [(TAtom "chk0"); (TAtom "chk10"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v33"); (TAtom "v75")]); ((TAtom "L89"), [(TAtom "chk0"); (TAtom "chk10"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v33")]); ((TAtom "L78"), [(TAtom "chk0"); (TAtom "chk2"); (TAtom "v0")]); ((TAtom "L61"), [(TAtom "chk0"); (TAtom "chk2"); (TAtom "v0")]); ((TAtom "L24"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v113")]); ((TAtom "L121"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v113")]); ((TAtom "L130"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v113"); (TAtom "v137")]); ((TAtom "L131"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v113")]); ((TAtom "L124"), [(TAtom "v113")]); ((TAtom "L125"), [(TAtom "chk28"); (TAtom "v0"); (TAtom "v113")]); ((TAtom "L147"), [(TAtom "chk33"); (TAtom "v113"); (TAtom "v163"); (TAtom "v167")]); ((TAtom "L168"), [(TAtom "chk33"); (TAtom "v113"); (TAtom "v163"); (TAtom "v170"); (TAtom "v171")]); ((TAtom "L169"), [(TAtom "v113"); (TAtom "v163")]); ((TAtom "L180"), [(TAtom "v113")]); ((TAtom "L148"), [(TAtom "v113")]); ((TAtom "L116"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "v10")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (116)), "fp->_flags2")]); ((TAtom "L6"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0)), "fp->_flags")]); ((TAtom "L8"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0)), "fp->_flags")]); ((TAtom "L29"), [(3%N, (TApp "tmp" [(TAtom "v37")]), (0), (Some 1), true, false, (Some (TAtom "v37")), (Some (0)), "opaque")]); ((TAtom "L40"), [(2%N, (TApp "tmp" [(TAtom "v43")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136)), "fp->_lock"); (5%N, (TApp "tmp" [(TAtom "v45")]), (0), (Some 8), true, false, (Some (TAtom "v44")), (Some (8)), "fp->_lock->owner")]); ((TAtom "L41"), []); ((TAtom "L34"), [(2%N, (TApp "tmp" [(TAtom "v53")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136)), "fp->_lock"); (4%N, (TApp "tmp" [(TAtom "v54")]), (0), (Some 4), false, true, (Some (TAtom "v54")), (Some (0)), "fp->_lock->lock"); (5%N, (TApp "tmp" [(TAtom "v53")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136)), "fp->_lock"); (8%N, (TApp "tmp" [(TAtom "v58")]), (0), (Some 8), false, true, (Some (TAtom "v57")), (Some (8)), "fp->_lock->owner")]); ((TAtom "L35"), [(2%N, (TApp "tmp" [(TAtom "v64")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136)), "fp->_lock"); (5%N, (TApp "tmp" [(TAtom "v66")]), (0), (Some 8), true, false, (Some (TAtom "v65")), (Some (8)), "fp->_lock->owner")]); ((TAtom "L60"), [(1%N, (TApp "tmp" [(TAtom "v64")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136)), "fp->_lock"); (3%N, (TApp "tmp" [(TAtom "v75")]), (0), (Some 4), true, true, (Some (TAtom "v75")), (Some (0)), "opaque")]); ((TAtom "L84"), []); ((TAtom "L85"), []); ((TAtom "L89"), []); ((TAtom "L78"), [(2%N, (TApp "tmp" [(TAtom "v100")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136)), "fp->_lock"); (5%N, (TApp "tmp" [(TAtom "v102")]), (0), (Some 8), false, true, (Some (TAtom "v101")), (Some (8)), "fp->_lock->owner")]); ((TAtom "L61"), [(1%N, (TApp "tmp" [(TAtom "v64")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136)), "fp->_lock"); (4%N, (TApp "tmp" [(TAtom "v107")]), (0), (Some 4), true, false, (Some (TAtom "v106")), (Some (4)), "fp->_lock->cnt"); (7%N, (TApp "tmp" [(TAtom "v107")]), (0), (Some 4), false, true, (Some (TAtom "v106")), (Some (4)), "fp->_lock->cnt")]); ((TAtom "L24"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0)), "fp->_flags"); (4%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0)), "fp->_flags")]); ((TAtom "L121"), [(2%N, (TApp "tmp" [(TAtom "v127")]), (0), (Some 1), true, false, (Some (TAtom "v127")), (Some (0)), "opaque")]); ((TAtom "L130"), [(2%N, (TApp "tmp" [(TAtom "v133")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136)), "fp->_lock"); (5%N, (TApp "tmp" [(TAtom "v135")]), (0), (Some 4), true, false, (Some (TAtom "v134")), (Some (4)), "fp->_lock->cnt")]); ((TAtom "L131"), []); ((TAtom "L124"), [(2%N, (TApp "tmp" [(TAtom "v141")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136)), "fp->_lock"); (5%N, (TApp "tmp" [(TAtom "v143")]), (0), (Some 8), false, true, (Some (TAtom "v142")), (Some (8)), "fp->_lock->owner"); (7%N, (TApp "tmp" [(TAtom "v141")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136)), "fp->_lock"); (9%N, (TApp "tmp" [(TAtom "v146")]), (0), (Some 4), false, true, (Some (TAtom "v146")), (Some (0)), "fp->_lock->lock")]); ((TAtom "L125"), [(2%N, (TApp "tmp" [(TAtom "v151")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136)), "fp->_lock"); (5%N, (TApp "tmp" [(TAtom "v153")]), (0), (Some 4), true, false, (Some (TAtom "v152")), (Some (4)), "fp->_lock->cnt")]); ((TAtom "L147"), [(1%N, (TApp "tmp" [(TAtom "v151")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136)), "fp->_lock"); (4%N, (TApp "tmp" [(TAtom "v159")]), (0), (Some 8), false, true, (Some (TAtom "v158")), (Some (8)), "fp->_lock->owner"); (6%N, (TApp "tmp" [(TAtom "v157")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136)), "fp->_lock"); (8%N, (TApp "tmp" [(TAtom "v163")]), (0), (Some 4), true, false, (Some (TAtom "v163")), (Some (0)), "opaque")]); ((TAtom "L168"), [(1%N, (TApp "tmp" [(TAtom "v163")]), (0), (Some 4), true, true, (Some (TAtom "v163")), (Some (0)), "opaque")]); ((TAtom "L169"), []); ((TAtom "L180"), []); ((TAtom "L148"), [(1%N, (TApp "tmp" [(TAtom "v151")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136)), "fp->_lock"); (4%N, (TApp "tmp" [(TAtom "v194")]), (0), (Some 4), true, false, (Some (TAtom "v193")), (Some (4)), "fp->_lock->cnt"); (7%N, (TApp "tmp" [(TAtom "v194")]), (0), (Some 4), false, true, (Some (TAtom "v193")), (Some (4)), "fp->_lock->cnt")]); ((TAtom "L116"), [])].


End fn__IO_ferror.

Module fn___GI__IO_file_doallocate.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_3, 66%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_3, 71%N)); ((TAtom "L12"), (file_3, 74%N)); ((TAtom "iw_1.L10"), (file_0, 1049%N)); ((TAtom "iw_1.join"), (file_3, 74%N)); ((TAtom "L13"), (file_3, 74%N)); ((TAtom "L5"), (file_3, 76%N)); ((TAtom "L26"), (file_3, 81%N)); ((TAtom "L42"), (file_3, 81%N)); ((TAtom "L43"), (file_3, 81%N)); ((TAtom "L48"), (file_3, 79%N)); ((TAtom "L49"), (file_3, 79%N)); ((TAtom "L33"), (file_3, 84%N)); ((TAtom "L28"), (file_3, 87%N)); ((TAtom "L65"), (file_3, 87%N)); ((TAtom "L66"), (file_3, 87%N)); ((TAtom "L59"), (file_3, 88%N)); ((TAtom "L7"), (file_3, 69%N)); ((TAtom "L76"), (file_3, 93%N)); ((TAtom "L78"), (file_3, 94%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "vtable"); ((TAtom "iw_1.v13"), "offset"); ((TAtom "iw_1.v18"), "vtable"); ((TAtom "iw_1.v3"), "vtable"); ((TAtom "iw_1.v4"), "ptr"); ((TAtom "iw_1.v6"), "ptr"); ((TAtom "iw_1.v9"), "offset"); ((TAtom "pr.1"), "size"); ((TAtom "pr.2"), "size"); ((TAtom "v0"), "fp"); ((TAtom "v14"), "fp"); ((TAtom "v20"), "fp"); ((TAtom "v39"), "__dev_major"); ((TAtom "v40"), "__dev_major"); ((TAtom "v44"), "__dev_major"); ((TAtom "v50"), "fp"); ((TAtom "v56"), "fp"); ((TAtom "v73"), "size"); ((TAtom "v74"), "size"); ((TAtom "v75"), "p"); ((TAtom "v79"), "p"); ((TAtom "v8"), "fp"); ((TAtom "v87"), "fp"); ((TAtom "v88"), "p"); ((TAtom "v89"), "p"); ((TAtom "v90"), "size")].

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  [((TAtom "chk0"), ((TAtom "v0"), "fp", 112)); ((TAtom "chk1"), ((TAtom "v0"), "fp", 216)); ((TAtom "chk2"), ((TAtom "v16"), "v16", 144)); ((TAtom "chk4"), ((TAtom "v4"), "&st", 24)); ((TAtom "chk5"), ((TAtom "v4"), "&st", 40)); ((TAtom "chk6"), ((TAtom "v0"), "fp", 112)); ((TAtom "chk7"), ((TAtom "v0"), "fp", 0)); ((TAtom "chk8"), ((TAtom "v0"), "fp", 0)); ((TAtom "chk9"), ((TAtom "v4"), "&st", 56)); ((TAtom "iw_1.v4"), ((TAtom "iw_1.v4"), "ptr", 0)); ((TAtom "iw_1.v7"), ((TAtom "iw_1.v7"), "&__io_vtables", 0)); ((TAtom "iw_1.v9"), ((TAtom "iw_1.v9"), "offset", 0)); ((TAtom "pr.2"), ((TAtom "pr.2"), "size", 0)); ((TAtom "v0"), ((TAtom "v0"), "fp", 0)); ((TAtom "v15"), ((TAtom "v0"), "fp", 216)); ((TAtom "v18"), ((TAtom "v16"), "v16", 144)); ((TAtom "v29"), ((TAtom "v4"), "&st", 24)); ((TAtom "v37"), ((TAtom "v4"), "&st", 40)); ((TAtom "v39"), ((TAtom "v39"), "__dev_major", 0)); ((TAtom "v4"), ((TAtom "v4"), "&st", 0)); ((TAtom "v51"), ((TAtom "v0"), "fp", 112)); ((TAtom "v62"), ((TAtom "v4"), "&st", 56)); ((TAtom "v67"), ((TAtom "v4"), "&st", 56)); ((TAtom "v72"), ((TAtom "v4"), "&st", 56)); ((TAtom "v73"), ((TAtom "v73"), "size", 0)); ((TAtom "v75"), ((TAtom "v75"), "p", 0)); ((TAtom "v9"), ((TAtom "v0"), "fp", 112))].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "L12"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "iw_1.L10"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v16"); (TAtom "v4")]); ((TAtom "iw_1.join"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v16"); (TAtom "v4")]); ((TAtom "L13"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L5"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L26"), [(TAtom "chk0"); (TAtom "chk4"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L42"), [(TAtom "chk0"); (TAtom "chk4"); (TAtom "v0"); (TAtom "v39"); (TAtom "v4")]); ((TAtom "L43"), [(TAtom "chk0"); (TAtom "chk4"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L48"), [(TAtom "chk0"); (TAtom "chk4"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L49"), [(TAtom "chk0"); (TAtom "chk4"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L33"), [(TAtom "chk0"); (TAtom "chk4"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L28"), [(TAtom "chk4"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L65"), [(TAtom "chk9"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L66"), [(TAtom "chk9"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L59"), [(TAtom "chk9"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L7"), [(TAtom "v0")]); ((TAtom "L76"), []); ((TAtom "L78"), [(TAtom "pr.2"); (TAtom "v0"); (TAtom "v75")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L12"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v16"); (TAtom "v4")]); ((TAtom "iw_1.L10"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v16"); (TAtom "v4")]); ((TAtom "iw_1.join"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v23"); (TAtom "v4")]); ((TAtom "L13"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L5"), [(TAtom "chk0"); (TAtom "chk4"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L26"), [(TAtom "chk0"); (TAtom "chk4"); (TAtom "v0"); (TAtom "v39"); (TAtom "v4")]); ((TAtom "L42"), [(TAtom "chk0"); (TAtom "chk4"); (TAtom "v0"); (TAtom "v4"); (TAtom "v45")]); ((TAtom "L43"), [(TAtom "chk0"); (TAtom "chk4"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L48"), [(TAtom "chk0"); (TAtom "chk4"); (TAtom "v0"); (TAtom "v4"); (TAtom "v54")]); ((TAtom "L49"), [(TAtom "chk0"); (TAtom "chk4"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L33"), [(TAtom "chk4"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L28"), [(TAtom "chk9"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L65"), [(TAtom "chk9"); (TAtom "v0"); (TAtom "v4"); (TAtom "v69")]); ((TAtom "L66"), [(TAtom "chk9"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L59"), [(TAtom "v0"); (TAtom "v73")]); ((TAtom "L7"), [(TAtom "pr.2"); (TAtom "v0"); (TAtom "v75")]); ((TAtom "L76"), []); ((TAtom "L78"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), [(3%N, (TApp "tmp" [(TAtom "v9")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (112)), "fp->_fileno")]); ((TAtom "L12"), [(2%N, (TApp "tmp" [(TAtom "v15")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (216)), "opaque")]); ((TAtom "iw_1.L10"), []); ((TAtom "iw_1.join"), [(2%N, (TApp "tmp" [(TAtom "v18")]), (0), (Some 8), true, false, (Some (TAtom "v16")), (Some (144)), "opaque")]); ((TAtom "L13"), []); ((TAtom "L5"), [(2%N, (TApp "tmp" [(TAtom "v29")]), (0), (Some 4), true, false, (Some (TAtom "v4")), (Some (24)), "st.st_mode")]); ((TAtom "L26"), [(2%N, (TApp "tmp" [(TAtom "v37")]), (0), (Some 8), true, false, (Some (TAtom "v4")), (Some (40)), "st.st_rdev")]); ((TAtom "L42"), []); ((TAtom "L43"), []); ((TAtom "L48"), [(2%N, (TApp "tmp" [(TAtom "v51")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (112)), "fp->_fileno")]); ((TAtom "L49"), []); ((TAtom "L33"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0)), "fp->_flags"); (4%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), false, true, (Some (TAtom "v0")), (Some (0)), "fp->_flags")]); ((TAtom "L28"), [(2%N, (TApp "tmp" [(TAtom "v62")]), (0), (Some 8), true, false, (Some (TAtom "v4")), (Some (56)), "st.st_blksize")]); ((TAtom "L65"), [(1%N, (TApp "tmp" [(TAtom "v62")]), (0), (Some 8), true, false, (Some (TAtom "v4")), (Some (56)), "st.st_blksize")]); ((TAtom "L66"), []); ((TAtom "L59"), [(1%N, (TApp "tmp" [(TAtom "v62")]), (0), (Some 8), true, false, (Some (TAtom "v4")), (Some (56)), "st.st_blksize")]); ((TAtom "L7"), []); ((TAtom "L76"), []); ((TAtom "L78"), [])].


End fn___GI__IO_file_doallocate.

Module fn___GI__IO_file_stat.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_4, 1221%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_4, 1224%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fp"); ((TAtom "v2"), "st"); ((TAtom "v4"), "fp"); ((TAtom "v7"), "st")].

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  [((TAtom "chk0"), ((TAtom "v0"), "fp", 112)); ((TAtom "v0"), ((TAtom "v0"), "fp", 0)); ((TAtom "v2"), ((TAtom "v2"), "st", 0)); ((TAtom "v5"), ((TAtom "v0"), "fp", 112))].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "v5")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (112)), "fp->_fileno")])].


End fn___GI__IO_file_stat.

Module fn___GI__IO_file_close.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_4, 1239%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_4, 1244%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fp"); ((TAtom "v2"), "fp")].

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  [((TAtom "chk0"), ((TAtom "v0"), "fp", 112)); ((TAtom "v0"), ((TAtom "v0"), "fp", 0)); ((TAtom "v3"), ((TAtom "v0"), "fp", 112))].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "v3")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (112)), "fp->_fileno")])].


End fn___GI__IO_file_close.

Module fn__IO_new_file_write.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_4, 1248%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_4, 1252%N)); ((TAtom "L8"), (file_4, 1251%N)); ((TAtom "L9"), (file_4, 1254%N)); ((TAtom "L14"), (file_4, 1254%N)); ((TAtom "L15"), (file_4, 1254%N)); ((TAtom "L16"), (file_4, 1254%N)); ((TAtom "L38"), (file_4, 1260%N)); ((TAtom "L40"), (file_4, 1263%N)); ((TAtom "L10"), (file_4, 1267%N)); ((TAtom "L61"), (file_4, 1269%N)); ((TAtom "L63"), (file_4, 1270%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "pr.1"), "data"); ((TAtom "pr.2"), "to_do"); ((TAtom "v0"), "f"); ((TAtom "v11"), "to_do"); ((TAtom "v17"), "f"); ((TAtom "v2"), "data"); ((TAtom "v25"), "f"); ((TAtom "v28"), "data"); ((TAtom "v29"), "to_do"); ((TAtom "v31"), "f"); ((TAtom "v34"), "data"); ((TAtom "v35"), "to_do"); ((TAtom "v37"), "count"); ((TAtom "v4"), "n"); ((TAtom "v41"), "count"); ((TAtom "v43"), "f"); ((TAtom "v47"), "f"); ((TAtom "v50"), "count"); ((TAtom "v52"), "to_do"); ((TAtom "v53"), "count"); ((TAtom "v54"), "to_do"); ((TAtom "v55"), "data"); ((TAtom "v56"), "count"); ((TAtom "v57"), "data"); ((TAtom "v58"), "n"); ((TAtom "v59"), "to_do"); ((TAtom "v60"), "n"); ((TAtom "v64"), "f"); ((TAtom "v68"), "f"); ((TAtom "v7"), "n"); ((TAtom "v71"), "n"); ((TAtom "v73"), "n")].

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  [((TAtom "chk0"), ((TAtom "v0"), "f", 116)); ((TAtom "chk1"), ((TAtom "v0"), "f", 112)); ((TAtom "chk2"), ((TAtom "v0"), "f", 112)); ((TAtom "chk3"), ((TAtom "v0"), "f", 0)); ((TAtom "chk4"), ((TAtom "v0"), "f", 0)); ((TAtom "chk5"), ((TAtom "v0"), "f", 200)); ((TAtom "chk6"), ((TAtom "v0"), "f", 200)); ((TAtom "chk7"), ((TAtom "v0"), "f", 144)); ((TAtom "chk9"), ((TAtom "v0"), "f", 144)); ((TAtom "pr.1"), ((TAtom "pr.1"), "data", 0)); ((TAtom "pr.2"), ((TAtom "pr.2"), "to_do", 0)); ((TAtom "v0"), ((TAtom "v0"), "f", 0)); ((TAtom "v18"), ((TAtom "v0"), "f", 116)); ((TAtom "v2"), ((TAtom "v2"), "data", 0)); ((TAtom "v26"), ((TAtom "v0"), "f", 112)); ((TAtom "v32"), ((TAtom "v0"), "f", 112)); ((TAtom "v37"), ((TAtom "v37"), "count", 0)); ((TAtom "v4"), ((TAtom "v4"), "n", 0)); ((TAtom "v48"), ((TAtom "v0"), "f", 200)); ((TAtom "v54"), ((TAtom "v54"), "to_do", 0)); ((TAtom "v57"), ((TAtom "v57"), "data", 0)); ((TAtom "v60"), ((TAtom "v60"), "n", 0)); ((TAtom "v65"), ((TAtom "v0"), "f", 144)); ((TAtom "v69"), ((TAtom "v0"), "f", 144))].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L8")].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L8"), [(TAtom "v0"); (TAtom "v4")]); ((TAtom "L9"), [(TAtom "pr.1"); (TAtom "pr.2"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L14"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "pr.2"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L15"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "pr.2"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L16"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "pr.2"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L38"), [(TAtom "chk0"); (TAtom "pr.2"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L40"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "pr.2"); (TAtom "v0"); (TAtom "v37"); (TAtom "v4")]); ((TAtom "L10"), [(TAtom "pr.2"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L61"), [(TAtom "chk7"); (TAtom "v0"); (TAtom "v60")]); ((TAtom "L63"), [(TAtom "v60")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L8"), [(TAtom "pr.1"); (TAtom "pr.2"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L9"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "pr.2"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L14"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "pr.2"); (TAtom "v0"); (TAtom "v30"); (TAtom "v4")]); ((TAtom "L15"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "pr.2"); (TAtom "v0"); (TAtom "v36"); (TAtom "v4")]); ((TAtom "L16"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "pr.2"); (TAtom "v0"); (TAtom "v37"); (TAtom "v4")]); ((TAtom "L38"), [(TAtom "pr.2"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L40"), [(TAtom "v0"); (TAtom "v4"); (TAtom "v54"); (TAtom "v57")]); ((TAtom "L10"), [(TAtom "chk7"); (TAtom "v0"); (TAtom "v60")]); ((TAtom "L61"), [(TAtom "v60")]); ((TAtom "L63"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), []); ((TAtom "L8"), []); ((TAtom "L9"), [(2%N, (TApp "tmp" [(TAtom "v18")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (116)), "f->_flags2")]); ((TAtom "L14"), [(2%N, (TApp "tmp" [(TAtom "v26")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (112)), "f->_fileno")]); ((TAtom "L15"), [(2%N, (TApp "tmp" [(TAtom "v32")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (112)), "f->_fileno")]); ((TAtom "L16"), []); ((TAtom "L38"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0)), "f->_flags"); (4%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), false, true, (Some (TAtom "v0")), (Some (0)), "f->_flags")]); ((TAtom "L40"), [(2%N, (TApp "tmp" [(TAtom "v48")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (200)), "f->_total_written"); (5%N, (TApp "tmp" [(TAtom "v48")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (200)), "f->_total_written")]); ((TAtom "L10"), [(3%N, (TApp "tmp" [(TAtom "v65")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (144)), "f->_offset")]); ((TAtom "L61"), [(1%N, (TApp "tmp" [(TAtom "v65")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (144)), "f->_offset"); (4%N, (TApp "tmp" [(TAtom "v69")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (144)), "f->_offset")]); ((TAtom "L63"), [])].


End fn__IO_new_file_write.

Module fn___GI__IO_setb.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_5, 353%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_5, 356%N)); ((TAtom "L16"), (file_5, 356%N)); ((TAtom "L17"), (file_5, 356%N)); ((TAtom "L8"), (file_5, 357%N)); ((TAtom "L10"), (file_5, 358%N)); ((TAtom "L33"), (file_5, 361%N)); ((TAtom "L34"), (file_5, 363%N)); ((TAtom "L35"), (file_5, 353%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "f"); ((TAtom "v11"), "f"); ((TAtom "v18"), "f"); ((TAtom "v2"), "b"); ((TAtom "v24"), "f"); ((TAtom "v27"), "f"); ((TAtom "v29"), "b"); ((TAtom "v30"), "f"); ((TAtom "v32"), "eb"); ((TAtom "v36"), "a"); ((TAtom "v37"), "f"); ((TAtom "v4"), "eb"); ((TAtom "v41"), "f"); ((TAtom "v6"), "a")].

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  [((TAtom "chk0"), ((TAtom "v0"), "f", 56)); ((TAtom "chk1"), ((TAtom "v0"), "f", 0)); ((TAtom "chk3"), ((TAtom "v0"), "f", 56)); ((TAtom "chk4"), ((TAtom "v0"), "f", 64)); ((TAtom "chk5"), ((TAtom "v0"), "f", 0)); ((TAtom "chk6"), ((TAtom "v0"), "f", 0)); ((TAtom "chk7"), ((TAtom "v0"), "f", 0)); ((TAtom "chk8"), ((TAtom "v0"), "f", 0)); ((TAtom "v0"), ((TAtom "v0"), "f", 0)); ((TAtom "v12"), ((TAtom "v0"), "f", 56)); ((TAtom "v2"), ((TAtom "v2"), "b", 0)); ((TAtom "v25"), ((TAtom "v0"), "f", 56)); ((TAtom "v28"), ((TAtom "v0"), "f", 56)); ((TAtom "v31"), ((TAtom "v0"), "f", 64)); ((TAtom "v4"), ((TAtom "v4"), "eb", 0)); ((TAtom "v6"), ((TAtom "v6"), "a", 0))].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L16"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L17"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L8"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L10"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L33"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L34"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L35"), [])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L16"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2"); (TAtom "v21"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L17"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L8"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L10"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L33"), []); ((TAtom "L34"), []); ((TAtom "L35"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "v12")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (56)), "f->_IO_buf_base")]); ((TAtom "L16"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0)), "f->_flags")]); ((TAtom "L17"), []); ((TAtom "L8"), [(1%N, (TApp "tmp" [(TAtom "v12")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (56)), "f->_IO_buf_base")]); ((TAtom "L10"), [(2%N, (TApp "tmp" [(TAtom "v28")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (56)), "f->_IO_buf_base"); (5%N, (TApp "tmp" [(TAtom "v31")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (64)), "f->_IO_buf_end")]); ((TAtom "L33"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0)), "f->_flags"); (4%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), false, true, (Some (TAtom "v0")), (Some (0)), "f->_flags")]); ((TAtom "L34"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0)), "f->_flags"); (4%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), false, true, (Some (TAtom "v0")), (Some (0)), "f->_flags")]); ((TAtom "L35"), [])].


End fn___GI__IO_setb.

Module fn___GI__IO_doallocbuf.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_5, 367%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_5, 370%N)); ((TAtom "L2"), (file_5, 371%N)); ((TAtom "L4"), (file_5, 372%N)); ((TAtom "L18"), (file_5, 372%N)); ((TAtom "L19"), (file_5, 372%N)); ((TAtom "L11"), (file_5, 373%N)); ((TAtom "iw_1.L10"), (file_0, 1049%N)); ((TAtom "iw_1.join"), (file_5, 373%N)); ((TAtom "L26"), (file_5, 374%N)); ((TAtom "L13"), (file_5, 375%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "vtable"); ((TAtom "iw_1.v13"), "offset"); ((TAtom "iw_1.v18"), "vtable"); ((TAtom "iw_1.v3"), "vtable"); ((TAtom "iw_1.v4"), "ptr"); ((TAtom "iw_1.v6"), "ptr"); ((TAtom "iw_1.v9"), "offset"); ((TAtom "v0"), "fp"); ((TAtom "v14"), "fp"); ((TAtom "v20"), "fp"); ((TAtom "v29"), "fp"); ((TAtom "v35"), "fp"); ((TAtom "v40"), "fp"); ((TAtom "v41"), "fp"); ((TAtom "v43"), "fp"); ((TAtom "v5"), "fp")].

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  [((TAtom "chk0"), ((TAtom "v0"), "fp", 56)); ((TAtom "chk1"), ((TAtom "v0"), "fp", 0)); ((TAtom "chk2"), ((TAtom "v0"), "fp", 192)); ((TAtom "chk3"), ((TAtom "v0"), "fp", 216)); ((TAtom "chk4"), ((TAtom "v31"), "v31", 104)); ((TAtom "iw_1.v4"), ((TAtom "iw_1.v4"), "ptr", 0)); ((TAtom "iw_1.v7"), ((TAtom "iw_1.v7"), "&__io_vtables", 0)); ((TAtom "iw_1.v9"), ((TAtom "iw_1.v9"), "offset", 0)); ((TAtom "v0"), ((TAtom "v0"), "fp", 0)); ((TAtom "v21"), ((TAtom "v0"), "fp", 192)); ((TAtom "v30"), ((TAtom "v0"), "fp", 216)); ((TAtom "v33"), ((TAtom "v31"), "v31", 104)); ((TAtom "v42"), ((TAtom "v0"), "fp", 131)); ((TAtom "v45"), ((TAtom "v0"), "fp", 132)); ((TAtom "v6"), ((TAtom "v0"), "fp", 56))].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "L2"), []); ((TAtom "L4"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L18"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L19"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L11"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "iw_1.L10"), [(TAtom "v0"); (TAtom "v31")]); ((TAtom "iw_1.join"), [(TAtom "v0"); (TAtom "v31")]); ((TAtom "L26"), []); ((TAtom "L13"), [(TAtom "v0")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L2"), []); ((TAtom "L4"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L18"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v23")]); ((TAtom "L19"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L11"), [(TAtom "v0"); (TAtom "v31")]); ((TAtom "iw_1.L10"), [(TAtom "v0"); (TAtom "v31")]); ((TAtom "iw_1.join"), [(TAtom "v0")]); ((TAtom "L26"), []); ((TAtom "L13"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "v6")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (56)), "fp->_IO_buf_base")]); ((TAtom "L2"), []); ((TAtom "L4"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0)), "fp->_flags")]); ((TAtom "L18"), [(2%N, (TApp "tmp" [(TAtom "v21")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (192)), "fp->_mode")]); ((TAtom "L19"), []); ((TAtom "L11"), [(2%N, (TApp "tmp" [(TAtom "v30")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (216)), "opaque")]); ((TAtom "iw_1.L10"), []); ((TAtom "iw_1.join"), [(2%N, (TApp "tmp" [(TAtom "v33")]), (0), (Some 8), true, false, (Some (TAtom "v31")), (Some (104)), "opaque")]); ((TAtom "L26"), []); ((TAtom "L13"), [])].


End fn___GI__IO_doallocbuf.

Module fn___gnu_dev_major.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_6, 28%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_6, 28%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "__dev"); ((TAtom "v11"), "__major"); ((TAtom "v12"), "__major"); ((TAtom "v3"), "__dev"); ((TAtom "v5"), "__major"); ((TAtom "v6"), "__major"); ((TAtom "v7"), "__dev")].

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  [((TAtom "v0"), ((TAtom "v0"), "__dev", 0)); ((TAtom "v11"), ((TAtom "v11"), "__major", 0)); ((TAtom "v12"), ((TAtom "v12"), "__major", 0)); ((TAtom "v5"), ((TAtom "v5"), "__major", 0)); ((TAtom "v6"), ((TAtom "v6"), "__major", 0))].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), [])].


End fn___gnu_dev_major.

(** Projection keeps instruction bodies out of the VM code used by the membership check. *)
Definition source_blocks : list (string * list name) := Eval lazy in
  [("__fpending", map b_label (fn_blocks Unit_libio___fpending_os.fn___fpending)); ("_IO_ferror", map b_label (fn_blocks Unit_libio_ferror_os.fn__IO_ferror)); ("__GI__IO_file_doallocate", map b_label (fn_blocks Unit_libio_filedoalloc_os.fn___GI__IO_file_doallocate)); ("__GI__IO_file_stat", map b_label (fn_blocks Unit_libio_fileops_os.fn___GI__IO_file_stat)); ("__GI__IO_file_close", map b_label (fn_blocks Unit_libio_fileops_os.fn___GI__IO_file_close)); ("_IO_new_file_write", map b_label (fn_blocks Unit_libio_fileops_os.fn__IO_new_file_write)); ("__GI__IO_setb", map b_label (fn_blocks Unit_libio_genops_os.fn___GI__IO_setb)); ("__GI__IO_doallocbuf", map b_label (fn_blocks Unit_libio_genops_os.fn___GI__IO_doallocbuf)); ("__gnu_dev_major", map b_label (fn_blocks Unit_misc_makedev_os.fn___gnu_dev_major))].

(** Projection keeps live sets and memory access records out of the membership computation. *)
Definition table_labels : list (string * list name) := Eval lazy in
  [("__fpending", app (map fst fn___fpending.block_src) (app (map fst fn___fpending.live_in) (app (map fst fn___fpending.live_out) (app (map fst fn___fpending.footprint) (fn___fpending.loop_heads))))); ("_IO_ferror", app (map fst fn__IO_ferror.block_src) (app (map fst fn__IO_ferror.live_in) (app (map fst fn__IO_ferror.live_out) (app (map fst fn__IO_ferror.footprint) (fn__IO_ferror.loop_heads))))); ("__GI__IO_file_doallocate", app (map fst fn___GI__IO_file_doallocate.block_src) (app (map fst fn___GI__IO_file_doallocate.live_in) (app (map fst fn___GI__IO_file_doallocate.live_out) (app (map fst fn___GI__IO_file_doallocate.footprint) (fn___GI__IO_file_doallocate.loop_heads))))); ("__GI__IO_file_stat", app (map fst fn___GI__IO_file_stat.block_src) (app (map fst fn___GI__IO_file_stat.live_in) (app (map fst fn___GI__IO_file_stat.live_out) (app (map fst fn___GI__IO_file_stat.footprint) (fn___GI__IO_file_stat.loop_heads))))); ("__GI__IO_file_close", app (map fst fn___GI__IO_file_close.block_src) (app (map fst fn___GI__IO_file_close.live_in) (app (map fst fn___GI__IO_file_close.live_out) (app (map fst fn___GI__IO_file_close.footprint) (fn___GI__IO_file_close.loop_heads))))); ("_IO_new_file_write", app (map fst fn__IO_new_file_write.block_src) (app (map fst fn__IO_new_file_write.live_in) (app (map fst fn__IO_new_file_write.live_out) (app (map fst fn__IO_new_file_write.footprint) (fn__IO_new_file_write.loop_heads))))); ("__GI__IO_setb", app (map fst fn___GI__IO_setb.block_src) (app (map fst fn___GI__IO_setb.live_in) (app (map fst fn___GI__IO_setb.live_out) (app (map fst fn___GI__IO_setb.footprint) (fn___GI__IO_setb.loop_heads))))); ("__GI__IO_doallocbuf", app (map fst fn___GI__IO_doallocbuf.block_src) (app (map fst fn___GI__IO_doallocbuf.live_in) (app (map fst fn___GI__IO_doallocbuf.live_out) (app (map fst fn___GI__IO_doallocbuf.footprint) (fn___GI__IO_doallocbuf.loop_heads))))); ("__gnu_dev_major", app (map fst fn___gnu_dev_major.block_src) (app (map fst fn___gnu_dev_major.live_in) (app (map fst fn___gnu_dev_major.live_out) (app (map fst fn___gnu_dev_major.footprint) (fn___gnu_dev_major.loop_heads)))))].

(** One computation rejects missing functions and stale labels across all tables in this fixture. *)
Lemma labels_valid :
  forallb (fun row =>
  match find (fun entry => String.eqb (fst entry) (fst row)) source_blocks with
  | Some (_, labels) =>
      forallb (fun l => existsb (name_eqb l) labels)
        (snd row)
  | _ => false
  end) table_labels = true.
Proof. vm_compute. reflexivity. Qed.

End LibioReadSrc.
