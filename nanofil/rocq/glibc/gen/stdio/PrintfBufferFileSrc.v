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

From Glibc Require Import Unit_stdioZ2dcommon_printf_buffer_to_file_os.

Module PrintfBufferFileSrc.

Definition file_0 : string := "../include/printf_buffer.h".

Definition file_1 : string := "../libio/libioP.h".

Definition file_2 : string := "printf_buffer_to_file.c".

Module fn___printf_buffer_to_file_switch.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_2, 27%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_2, 30%N)); ((TAtom "L2"), (file_2, 34%N)); ((TAtom "L3"), (file_2, 40%N)); ((TAtom "L4"), (file_2, 44%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "buf"); ((TAtom "v10"), "buf"); ((TAtom "v18"), "buf"); ((TAtom "v20"), "buf"); ((TAtom "v25"), "buf"); ((TAtom "v27"), "buf"); ((TAtom "v32"), "buf"); ((TAtom "v34"), "buf"); ((TAtom "v36"), "buf"); ((TAtom "v38"), "buf"); ((TAtom "v44"), "buf"); ((TAtom "v45"), "buf"); ((TAtom "v5"), "buf")].

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  [((TAtom "chk0"), ((TAtom "v0"), "buf", 40)); ((TAtom "chk1"), ((TAtom "v7"), "v7", 40)); ((TAtom "chk10"), ((TAtom "v0"), "buf", 8)); ((TAtom "chk11"), ((TAtom "v0"), "buf", 16)); ((TAtom "chk12"), ((TAtom "v0"), "buf", 8)); ((TAtom "chk13"), ((TAtom "v0"), "buf", 0)); ((TAtom "chk3"), ((TAtom "v12"), "v12", 48)); ((TAtom "chk5"), ((TAtom "v22"), "v22", 40)); ((TAtom "chk6"), ((TAtom "v0"), "buf", 8)); ((TAtom "chk7"), ((TAtom "v0"), "buf", 40)); ((TAtom "chk8"), ((TAtom "v29"), "v29", 48)); ((TAtom "chk9"), ((TAtom "v0"), "buf", 16)); ((TAtom "v0"), ((TAtom "v0"), "buf", 0)); ((TAtom "v13"), ((TAtom "v12"), "v12", 48)); ((TAtom "v19"), ((TAtom "v0"), "buf", 8)); ((TAtom "v21"), ((TAtom "v0"), "buf", 40)); ((TAtom "v23"), ((TAtom "v22"), "v22", 40)); ((TAtom "v26"), ((TAtom "v0"), "buf", 16)); ((TAtom "v30"), ((TAtom "v29"), "v29", 48)); ((TAtom "v33"), ((TAtom "v0"), "buf", 8)); ((TAtom "v35"), ((TAtom "v0"), "buf", 48)); ((TAtom "v37"), ((TAtom "v0"), "buf", 16)); ((TAtom "v43"), ((TAtom "v0"), "buf", 176)); ((TAtom "v46"), ((TAtom "v0"), "buf", 8)); ((TAtom "v6"), ((TAtom "v0"), "buf", 40)); ((TAtom "v8"), ((TAtom "v7"), "v7", 40))].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "L2"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L3"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L4"), [(TAtom "chk0"); (TAtom "v0")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L2"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L3"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L4"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "v6")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (40)), "buf->fp"); (5%N, (TApp "tmp" [(TAtom "v8")]), (0), (Some 8), true, false, (Some (TAtom "v7")), (Some (40)), "buf->fp->_IO_write_ptr"); (6%N, (TApp "tmp" [(TAtom "v6")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (40)), "buf->fp"); (9%N, (TApp "tmp" [(TAtom "v13")]), (0), (Some 8), true, false, (Some (TAtom "v12")), (Some (48)), "buf->fp->_IO_write_end")]); ((TAtom "L2"), [(2%N, (TApp "tmp" [(TAtom "v6")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (40)), "buf->fp"); (5%N, (TApp "tmp" [(TAtom "v23")]), (0), (Some 8), true, false, (Some (TAtom "v22")), (Some (40)), "buf->fp->_IO_write_ptr"); (7%N, (TApp "tmp" [(TAtom "v19")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (8)), "buf->base.write_ptr"); (10%N, (TApp "tmp" [(TAtom "v21")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (40)), "buf->fp"); (13%N, (TApp "tmp" [(TAtom "v30")]), (0), (Some 8), true, false, (Some (TAtom "v29")), (Some (48)), "buf->fp->_IO_write_end"); (15%N, (TApp "tmp" [(TAtom "v26")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (16)), "buf->base.write_end")]); ((TAtom "L3"), [(3%N, (TApp "tmp" [(TAtom "v33")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (8)), "buf->base.write_ptr"); (7%N, (TApp "tmp" [(TAtom "v37")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (16)), "buf->base.write_end")]); ((TAtom "L4"), [(2%N, (TApp "tmp" [(TAtom "v46")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (8)), "buf->base.write_ptr"); (4%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (0)), "buf->base.write_base")])].


End fn___printf_buffer_to_file_switch.

Module fn___printf_buffer_flush_to_file.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_2, 47%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_2, 51%N)); ((TAtom "L14"), (file_2, 58%N)); ((TAtom "iw_1.L10"), (file_1, 1049%N)); ((TAtom "iw_1.join"), (file_2, 59%N)); ((TAtom "iw_2.start"), (file_0, 107%N)); ((TAtom "L40"), (file_2, 65%N)); ((TAtom "L15"), (file_2, 68%N)); ((TAtom "L62"), (file_2, 72%N)); ((TAtom "L74"), (file_2, 74%N)); ((TAtom "iw_3.start"), (file_0, 107%N)); ((TAtom "L88"), (file_2, 79%N)); ((TAtom "L76"), (file_2, 82%N)); ((TAtom "L16"), (file_2, 86%N)); ((TAtom "L104"), (file_2, 86%N)); ((TAtom "L105"), (file_2, 89%N)); ((TAtom "L127"), (file_2, 98%N)); ((TAtom "L129"), (file_2, 103%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "vtable"); ((TAtom "iw_1.v13"), "offset"); ((TAtom "iw_1.v18"), "vtable"); ((TAtom "iw_1.v3"), "vtable"); ((TAtom "iw_1.v4"), "ptr"); ((TAtom "iw_1.v6"), "ptr"); ((TAtom "iw_1.v9"), "offset"); ((TAtom "iw_2.v0"), "buf"); ((TAtom "iw_2.v2"), "buf"); ((TAtom "iw_3.v0"), "buf"); ((TAtom "iw_3.v2"), "buf"); ((TAtom "v0"), "buf"); ((TAtom "v101"), "buf"); ((TAtom "v106"), "buf"); ((TAtom "v109"), "buf"); ((TAtom "v120"), "buf"); ((TAtom "v124"), "buf"); ((TAtom "v130"), "buf"); ((TAtom "v133"), "buf"); ((TAtom "v139"), "buf"); ((TAtom "v141"), "buf"); ((TAtom "v143"), "buf"); ((TAtom "v145"), "buf"); ((TAtom "v148"), "buf"); ((TAtom "v149"), "buf"); ((TAtom "v17"), "buf"); ((TAtom "v2"), "buf"); ((TAtom "v20"), "buf"); ((TAtom "v30"), "buf"); ((TAtom "v33"), "buf"); ((TAtom "v37"), "count"); ((TAtom "v41"), "buf"); ((TAtom "v49"), "buf"); ((TAtom "v5"), "buf"); ((TAtom "v52"), "buf"); ((TAtom "v54"), "count"); ((TAtom "v56"), "count"); ((TAtom "v58"), "buf"); ((TAtom "v60"), "buf"); ((TAtom "v65"), "buf"); ((TAtom "v68"), "buf"); ((TAtom "v77"), "buf"); ((TAtom "v8"), "buf"); ((TAtom "v80"), "buf"); ((TAtom "v89"), "buf"); ((TAtom "v92"), "buf"); ((TAtom "v99"), "buf")].

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  [((TAtom "chk0"), ((TAtom "v0"), "buf", 24)); ((TAtom "chk1"), ((TAtom "v0"), "buf", 8)); ((TAtom "chk11"), ((TAtom "v0"), "buf", 32)); ((TAtom "chk15"), ((TAtom "v0"), "buf", 40)); ((TAtom "chk16"), ((TAtom "v0"), "buf", 48)); ((TAtom "chk17"), ((TAtom "v0"), "buf", 32)); ((TAtom "chk19"), ((TAtom "v0"), "buf", 40)); ((TAtom "chk2"), ((TAtom "v0"), "buf", 0)); ((TAtom "chk20"), ((TAtom "v111"), "v111", 48)); ((TAtom "chk21"), ((TAtom "v0"), "buf", 40)); ((TAtom "chk22"), ((TAtom "v0"), "buf", 8)); ((TAtom "chk23"), ((TAtom "v122"), "v122", 40)); ((TAtom "chk24"), ((TAtom "v0"), "buf", 8)); ((TAtom "chk25"), ((TAtom "v0"), "buf", 16)); ((TAtom "chk26"), ((TAtom "v0"), "buf", 8)); ((TAtom "chk27"), ((TAtom "v0"), "buf", 16)); ((TAtom "chk28"), ((TAtom "v0"), "buf", 8)); ((TAtom "chk29"), ((TAtom "v0"), "buf", 0)); ((TAtom "chk3"), ((TAtom "v0"), "buf", 24)); ((TAtom "chk6"), ((TAtom "v0"), "buf", 40)); ((TAtom "chk7"), ((TAtom "v43"), "v43", 216)); ((TAtom "chk8"), ((TAtom "v45"), "v45", 56)); ((TAtom "chk9"), ((TAtom "v0"), "buf", 40)); ((TAtom "iw_1.v4"), ((TAtom "iw_1.v4"), "ptr", 0)); ((TAtom "iw_1.v7"), ((TAtom "iw_1.v7"), "&__io_vtables", 0)); ((TAtom "iw_1.v9"), ((TAtom "iw_1.v9"), "offset", 0)); ((TAtom "iw_2.v3"), ((TAtom "v0"), "buf", 32)); ((TAtom "iw_3.v3"), ((TAtom "v0"), "buf", 32)); ((TAtom "v0"), ((TAtom "v0"), "buf", 0)); ((TAtom "v107"), ((TAtom "v0"), "buf", 16)); ((TAtom "v110"), ((TAtom "v0"), "buf", 40)); ((TAtom "v112"), ((TAtom "v111"), "v111", 48)); ((TAtom "v121"), ((TAtom "v0"), "buf", 40)); ((TAtom "v123"), ((TAtom "v122"), "v122", 40)); ((TAtom "v125"), ((TAtom "v0"), "buf", 8)); ((TAtom "v134"), ((TAtom "v0"), "buf", 16)); ((TAtom "v140"), ((TAtom "v0"), "buf", 8)); ((TAtom "v142"), ((TAtom "v0"), "buf", 48)); ((TAtom "v144"), ((TAtom "v0"), "buf", 16)); ((TAtom "v147"), ((TAtom "v0"), "buf", 49)); ((TAtom "v150"), ((TAtom "v0"), "buf", 8)); ((TAtom "v18"), ((TAtom "v0"), "buf", 16)); ((TAtom "v21"), ((TAtom "v0"), "buf", 48)); ((TAtom "v25"), ((TAtom "v0"), "buf", 176)); ((TAtom "v3"), ((TAtom "v0"), "buf", 24)); ((TAtom "v31"), ((TAtom "v0"), "buf", 8)); ((TAtom "v34"), ((TAtom "v0"), "buf", 48)); ((TAtom "v37"), ((TAtom "v37"), "count", 0)); ((TAtom "v42"), ((TAtom "v0"), "buf", 40)); ((TAtom "v44"), ((TAtom "v43"), "v43", 216)); ((TAtom "v47"), ((TAtom "v45"), "v45", 56)); ((TAtom "v50"), ((TAtom "v0"), "buf", 40)); ((TAtom "v53"), ((TAtom "v0"), "buf", 48)); ((TAtom "v6"), ((TAtom "v0"), "buf", 8)); ((TAtom "v66"), ((TAtom "v0"), "buf", 16)); ((TAtom "v69"), ((TAtom "v0"), "buf", 48)); ((TAtom "v70"), ((TAtom "v0"), "buf", 49)); ((TAtom "v78"), ((TAtom "v0"), "buf", 8)); ((TAtom "v81"), ((TAtom "v0"), "buf", 16)); ((TAtom "v90"), ((TAtom "v0"), "buf", 40)); ((TAtom "v93"), ((TAtom "v0"), "buf", 48))].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "L14"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0")]); ((TAtom "iw_1.L10"), [(TAtom "chk0"); (TAtom "chk6"); (TAtom "v0"); (TAtom "v37"); (TAtom "v45")]); ((TAtom "iw_1.join"), [(TAtom "chk0"); (TAtom "chk6"); (TAtom "v0"); (TAtom "v37"); (TAtom "v45")]); ((TAtom "iw_2.start"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L40"), [(TAtom "v0")]); ((TAtom "L15"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk2"); (TAtom "v0")]); ((TAtom "L62"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0")]); ((TAtom "L74"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "iw_3.start"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L88"), [(TAtom "v0")]); ((TAtom "L76"), []); ((TAtom "L16"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk2"); (TAtom "v0")]); ((TAtom "L104"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk19"); (TAtom "chk2"); (TAtom "v0")]); ((TAtom "L105"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk19"); (TAtom "chk2"); (TAtom "v0")]); ((TAtom "L127"), [(TAtom "chk1"); (TAtom "chk2"); (TAtom "chk25"); (TAtom "v0")]); ((TAtom "L129"), [(TAtom "chk1"); (TAtom "chk2"); (TAtom "v0")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk2"); (TAtom "v0")]); ((TAtom "L14"), [(TAtom "chk0"); (TAtom "chk6"); (TAtom "v0"); (TAtom "v37"); (TAtom "v45")]); ((TAtom "iw_1.L10"), [(TAtom "chk0"); (TAtom "chk6"); (TAtom "v0"); (TAtom "v37"); (TAtom "v45")]); ((TAtom "iw_1.join"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "iw_2.start"), []); ((TAtom "L40"), []); ((TAtom "L15"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk2"); (TAtom "v0")]); ((TAtom "L62"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L74"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "iw_3.start"), []); ((TAtom "L88"), []); ((TAtom "L76"), []); ((TAtom "L16"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk19"); (TAtom "chk2"); (TAtom "v0")]); ((TAtom "L104"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk19"); (TAtom "chk2"); (TAtom "v0")]); ((TAtom "L105"), [(TAtom "chk1"); (TAtom "chk2"); (TAtom "chk25"); (TAtom "v0")]); ((TAtom "L127"), [(TAtom "chk1"); (TAtom "chk2"); (TAtom "v0")]); ((TAtom "L129"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "v3")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (24)), "buf->base.written"); (5%N, (TApp "tmp" [(TAtom "v6")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (8)), "buf->base.write_ptr"); (7%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (0)), "buf->base.write_base"); (13%N, (TApp "tmp" [(TAtom "v3")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (24)), "buf->base.written"); (15%N, (TApp "tmp" [(TAtom "v6")]), (8), (Some 8), true, false, (Some (TAtom "v0")), (Some (16)), "buf->base.write_end")]); ((TAtom "L14"), [(1%N, (TApp "tmp" [(TAtom "v6")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (8)), "buf->base.write_ptr"); (8%N, (TApp "tmp" [(TAtom "v42")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (40)), "buf->fp"); (11%N, (TApp "tmp" [(TAtom "v44")]), (0), (Some 8), true, false, (Some (TAtom "v43")), (Some (216)), "opaque")]); ((TAtom "iw_1.L10"), []); ((TAtom "iw_1.join"), [(2%N, (TApp "tmp" [(TAtom "v47")]), (0), (Some 8), true, false, (Some (TAtom "v45")), (Some (56)), "opaque"); (5%N, (TApp "tmp" [(TAtom "v50")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (40)), "buf->fp")]); ((TAtom "iw_2.start"), [(2%N, (TApp "tmp" [(TAtom "iw_2.v3")]), (0), (Some 4), false, true, (Some (TAtom "v0")), (Some (32)), "buf->mode")]); ((TAtom "L40"), []); ((TAtom "L15"), [(1%N, (TApp "tmp" [(TAtom "v6")]), (8), (Some 8), true, false, (Some (TAtom "v0")), (Some (16)), "buf->base.write_end")]); ((TAtom "L62"), [(1%N, (TApp "tmp" [(TAtom "v6")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (8)), "buf->base.write_ptr"); (3%N, (TApp "tmp" [(TAtom "v6")]), (8), (Some 8), true, false, (Some (TAtom "v0")), (Some (16)), "buf->base.write_end")]); ((TAtom "L74"), [(2%N, (TApp "tmp" [(TAtom "v90")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (40)), "buf->fp"); (5%N, (TApp "tmp" [(TAtom "v93")]), (0), (Some 1), true, false, (Some (TAtom "v0")), (Some (48)), "buf->stage")]); ((TAtom "iw_3.start"), [(2%N, (TApp "tmp" [(TAtom "iw_3.v3")]), (0), (Some 4), false, true, (Some (TAtom "v0")), (Some (32)), "buf->mode")]); ((TAtom "L88"), []); ((TAtom "L76"), []); ((TAtom "L16"), [(1%N, (TApp "tmp" [(TAtom "v6")]), (8), (Some 8), true, false, (Some (TAtom "v0")), (Some (16)), "buf->base.write_end"); (4%N, (TApp "tmp" [(TAtom "v110")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (40)), "buf->fp"); (7%N, (TApp "tmp" [(TAtom "v112")]), (0), (Some 8), true, false, (Some (TAtom "v111")), (Some (48)), "buf->fp->_IO_write_end")]); ((TAtom "L104"), []); ((TAtom "L105"), [(2%N, (TApp "tmp" [(TAtom "v121")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (40)), "buf->fp"); (6%N, (TApp "tmp" [(TAtom "v125")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (8)), "buf->base.write_ptr"); (8%N, (TApp "tmp" [(TAtom "v123")]), (0), (Some 8), false, true, (Some (TAtom "v122")), (Some (40)), "buf->fp->_IO_write_ptr"); (10%N, (TApp "tmp" [(TAtom "v125")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (8)), "buf->base.write_ptr"); (13%N, (TApp "tmp" [(TAtom "v134")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (16)), "buf->base.write_end")]); ((TAtom "L127"), [(3%N, (TApp "tmp" [(TAtom "v140")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (8)), "buf->base.write_ptr"); (7%N, (TApp "tmp" [(TAtom "v144")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (16)), "buf->base.write_end")]); ((TAtom "L129"), [(2%N, (TApp "tmp" [(TAtom "v150")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (8)), "buf->base.write_ptr"); (4%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (0)), "buf->base.write_base")])].


End fn___printf_buffer_flush_to_file.

Module fn___printf_buffer_to_file_init.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_2, 106%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_2, 109%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.iw_1.v0"), "buf"); ((TAtom "iw_1.iw_1.v10"), "buf"); ((TAtom "iw_1.iw_1.v12"), "base"); ((TAtom "iw_1.iw_1.v13"), "buf"); ((TAtom "iw_1.iw_1.v15"), "end"); ((TAtom "iw_1.iw_1.v16"), "buf"); ((TAtom "iw_1.iw_1.v18"), "buf"); ((TAtom "iw_1.iw_1.v2"), "base"); ((TAtom "iw_1.iw_1.v20"), "mode"); ((TAtom "iw_1.iw_1.v4"), "end"); ((TAtom "iw_1.iw_1.v6"), "mode"); ((TAtom "iw_1.iw_1.v8"), "buf"); ((TAtom "iw_1.iw_1.v9"), "base"); ((TAtom "iw_1.v0"), "buf"); ((TAtom "iw_1.v10"), "base"); ((TAtom "iw_1.v11"), "len"); ((TAtom "iw_1.v13"), "mode"); ((TAtom "iw_1.v2"), "base"); ((TAtom "iw_1.v4"), "len"); ((TAtom "iw_1.v6"), "mode"); ((TAtom "iw_1.v8"), "buf"); ((TAtom "iw_1.v9"), "base"); ((TAtom "v0"), "buf"); ((TAtom "v10"), "buf"); ((TAtom "v12"), "fp"); ((TAtom "v13"), "buf"); ((TAtom "v2"), "fp"); ((TAtom "v4"), "buf"); ((TAtom "v5"), "buf")].

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  [((TAtom "chk0"), ((TAtom "v0"), "buf", 0)); ((TAtom "chk1"), ((TAtom "v0"), "buf", 8)); ((TAtom "chk2"), ((TAtom "v0"), "buf", 16)); ((TAtom "chk3"), ((TAtom "v0"), "buf", 24)); ((TAtom "chk4"), ((TAtom "v0"), "buf", 32)); ((TAtom "chk5"), ((TAtom "v0"), "buf", 40)); ((TAtom "iw_1.iw_1.v11"), ((TAtom "v0"), "buf", 8)); ((TAtom "iw_1.iw_1.v14"), ((TAtom "v0"), "buf", 16)); ((TAtom "iw_1.iw_1.v17"), ((TAtom "v0"), "buf", 24)); ((TAtom "iw_1.iw_1.v19"), ((TAtom "v0"), "buf", 32)); ((TAtom "iw_1.v12"), ((TAtom "v0"), "buf", 176)); ((TAtom "v0"), ((TAtom "v0"), "buf", 0)); ((TAtom "v11"), ((TAtom "v0"), "buf", 40)); ((TAtom "v2"), ((TAtom "v2"), "fp", 0)); ((TAtom "v6"), ((TAtom "v0"), "buf", 48))].

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
  [((TAtom "start"), [(3%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (0)), "buf->write_base"); (6%N, (TApp "tmp" [(TAtom "iw_1.iw_1.v11")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (8)), "buf->write_ptr"); (9%N, (TApp "tmp" [(TAtom "iw_1.iw_1.v14")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (16)), "buf->write_end"); (12%N, (TApp "tmp" [(TAtom "iw_1.iw_1.v17")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (24)), "buf->written"); (15%N, (TApp "tmp" [(TAtom "iw_1.iw_1.v19")]), (0), (Some 4), false, true, (Some (TAtom "v0")), (Some (32)), "buf->mode"); (18%N, (TApp "tmp" [(TAtom "v11")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (40)), "buf->fp")])].


End fn___printf_buffer_to_file_init.

Module fn___printf_buffer_to_file_done.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_2, 115%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_0, 115%N)); ((TAtom "L2"), (file_2, 119%N)); ((TAtom "L4"), (file_2, 120%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "buf"); ((TAtom "iw_1.v2"), "buf"); ((TAtom "v0"), "buf"); ((TAtom "v10"), "buf"); ((TAtom "v11"), "buf"); ((TAtom "v5"), "buf")].

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  [((TAtom "chk0"), ((TAtom "v0"), "buf", 32)); ((TAtom "iw_1.v3"), ((TAtom "v0"), "buf", 32)); ((TAtom "v0"), ((TAtom "v0"), "buf", 0))].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "L2"), []); ((TAtom "L4"), [(TAtom "v0")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "L2"), []); ((TAtom "L4"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "iw_1.v3")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (32)), "buf->mode")]); ((TAtom "L2"), []); ((TAtom "L4"), [])].


End fn___printf_buffer_to_file_done.

(** Projection keeps instruction bodies out of the VM code used by the membership check. *)
Definition source_blocks : list (string * list name) := Eval lazy in
  [("__printf_buffer_to_file_switch", map b_label (fn_blocks Unit_stdioZ2dcommon_printf_buffer_to_file_os.fn___printf_buffer_to_file_switch)); ("__printf_buffer_flush_to_file", map b_label (fn_blocks Unit_stdioZ2dcommon_printf_buffer_to_file_os.fn___printf_buffer_flush_to_file)); ("__printf_buffer_to_file_init", map b_label (fn_blocks Unit_stdioZ2dcommon_printf_buffer_to_file_os.fn___printf_buffer_to_file_init)); ("__printf_buffer_to_file_done", map b_label (fn_blocks Unit_stdioZ2dcommon_printf_buffer_to_file_os.fn___printf_buffer_to_file_done))].

(** Projection keeps live sets and memory access records out of the membership computation. *)
Definition table_labels : list (string * list name) := Eval lazy in
  [("__printf_buffer_to_file_switch", app (map fst fn___printf_buffer_to_file_switch.block_src) (app (map fst fn___printf_buffer_to_file_switch.live_in) (app (map fst fn___printf_buffer_to_file_switch.live_out) (app (map fst fn___printf_buffer_to_file_switch.footprint) (fn___printf_buffer_to_file_switch.loop_heads))))); ("__printf_buffer_flush_to_file", app (map fst fn___printf_buffer_flush_to_file.block_src) (app (map fst fn___printf_buffer_flush_to_file.live_in) (app (map fst fn___printf_buffer_flush_to_file.live_out) (app (map fst fn___printf_buffer_flush_to_file.footprint) (fn___printf_buffer_flush_to_file.loop_heads))))); ("__printf_buffer_to_file_init", app (map fst fn___printf_buffer_to_file_init.block_src) (app (map fst fn___printf_buffer_to_file_init.live_in) (app (map fst fn___printf_buffer_to_file_init.live_out) (app (map fst fn___printf_buffer_to_file_init.footprint) (fn___printf_buffer_to_file_init.loop_heads))))); ("__printf_buffer_to_file_done", app (map fst fn___printf_buffer_to_file_done.block_src) (app (map fst fn___printf_buffer_to_file_done.live_in) (app (map fst fn___printf_buffer_to_file_done.live_out) (app (map fst fn___printf_buffer_to_file_done.footprint) (fn___printf_buffer_to_file_done.loop_heads)))))].

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

End PrintfBufferFileSrc.
