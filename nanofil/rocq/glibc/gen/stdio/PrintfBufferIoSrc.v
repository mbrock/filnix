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

From Glibc Require Import Unit_stdioZ2dcommon_printf_buffer_flush_os Unit_stdioZ2dcommon_printf_buffer_write_os.

Module PrintfBufferIoSrc.

Definition file_0 : string := "../include/printf_buffer.h".

Definition file_1 : string := "./Xprintf_buffer_flush.c".

Definition file_2 : string := "./Xprintf_buffer_write.c".

Definition file_3 : string := "printf_buffer_flush.c".

Module fn___printf_buffer_write.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_2, 24%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_0, 115%N)); ((TAtom "L6"), (file_2, 29%N)); ((TAtom "L15"), (file_2, 24%N)); ((TAtom "L16"), (file_2, 33%N)); ((TAtom "L32"), (file_2, 33%N)); ((TAtom "L33"), (file_2, 33%N)); ((TAtom "L20"), (file_2, 34%N)); ((TAtom "L22"), (file_2, 35%N)); ((TAtom "L42"), (file_2, 35%N)); ((TAtom "L43"), (file_2, 36%N)); ((TAtom "L67"), (file_2, 37%N)); ((TAtom "L68"), (file_2, 36%N)); ((TAtom "L17"), (file_2, 24%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "buf"); ((TAtom "iw_1.v2"), "buf"); ((TAtom "pr.1"), "s"); ((TAtom "pr.2"), "count"); ((TAtom "pr.3"), "to_copy"); ((TAtom "v0"), "buf"); ((TAtom "v18"), "count"); ((TAtom "v2"), "s"); ((TAtom "v23"), "buf"); ((TAtom "v26"), "buf"); ((TAtom "v34"), "buf"); ((TAtom "v4"), "count"); ((TAtom "v44"), "buf"); ((TAtom "v47"), "buf"); ((TAtom "v57"), "buf"); ((TAtom "v60"), "buf"); ((TAtom "v65"), "to_copy"); ((TAtom "v69"), "to_copy"); ((TAtom "v70"), "count"); ((TAtom "v72"), "count"); ((TAtom "v73"), "buf"); ((TAtom "v76"), "s"); ((TAtom "v77"), "to_copy"); ((TAtom "v79"), "buf"); ((TAtom "v82"), "to_copy"); ((TAtom "v84"), "s"); ((TAtom "v85"), "to_copy"); ((TAtom "v86"), "s"); ((TAtom "v87"), "count"); ((TAtom "v88"), "to_copy"); ((TAtom "v89"), "count"); ((TAtom "v9"), "buf")].

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  [((TAtom "chk0"), ((TAtom "v0"), "buf", 32)); ((TAtom "chk1"), ((TAtom "v0"), "buf", 8)); ((TAtom "chk2"), ((TAtom "v0"), "buf", 16)); ((TAtom "chk3"), ((TAtom "v0"), "buf", 8)); ((TAtom "chk4"), ((TAtom "v0"), "buf", 16)); ((TAtom "chk5"), ((TAtom "v0"), "buf", 16)); ((TAtom "chk6"), ((TAtom "v0"), "buf", 8)); ((TAtom "chk8"), ((TAtom "v0"), "buf", 8)); ((TAtom "chk9"), ((TAtom "v0"), "buf", 8)); ((TAtom "iw_1.v3"), ((TAtom "v0"), "buf", 32)); ((TAtom "pr.1"), ((TAtom "pr.1"), "s", 0)); ((TAtom "pr.2"), ((TAtom "pr.2"), "count", 0)); ((TAtom "pr.3"), ((TAtom "pr.3"), "to_copy", 0)); ((TAtom "v0"), ((TAtom "v0"), "buf", 0)); ((TAtom "v2"), ((TAtom "v2"), "s", 0)); ((TAtom "v24"), ((TAtom "v0"), "buf", 8)); ((TAtom "v27"), ((TAtom "v0"), "buf", 16)); ((TAtom "v4"), ((TAtom "v4"), "count", 0)); ((TAtom "v45"), ((TAtom "v0"), "buf", 8)); ((TAtom "v48"), ((TAtom "v0"), "buf", 16)); ((TAtom "v58"), ((TAtom "v0"), "buf", 16)); ((TAtom "v61"), ((TAtom "v0"), "buf", 8)); ((TAtom "v65"), ((TAtom "v65"), "to_copy", 0)); ((TAtom "v74"), ((TAtom "v0"), "buf", 8)); ((TAtom "v86"), ((TAtom "v86"), "s", 0)); ((TAtom "v89"), ((TAtom "v89"), "count", 0))].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L15")].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L6"), []); ((TAtom "L15"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L16"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "pr.2"); (TAtom "v0")]); ((TAtom "L32"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk2"); (TAtom "pr.1"); (TAtom "pr.2"); (TAtom "v0")]); ((TAtom "L33"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk2"); (TAtom "pr.1"); (TAtom "pr.2"); (TAtom "v0")]); ((TAtom "L20"), []); ((TAtom "L22"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk2"); (TAtom "pr.1"); (TAtom "pr.2"); (TAtom "v0")]); ((TAtom "L42"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk2"); (TAtom "pr.1"); (TAtom "pr.2"); (TAtom "v0")]); ((TAtom "L43"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk2"); (TAtom "pr.1"); (TAtom "pr.2"); (TAtom "v0")]); ((TAtom "L67"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk6"); (TAtom "pr.1"); (TAtom "pr.2"); (TAtom "v0"); (TAtom "v65")]); ((TAtom "L68"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk6"); (TAtom "pr.1"); (TAtom "pr.2"); (TAtom "v0")]); ((TAtom "L17"), [])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L6"), []); ((TAtom "L15"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "pr.2"); (TAtom "v0")]); ((TAtom "L16"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk2"); (TAtom "pr.1"); (TAtom "pr.2"); (TAtom "v0")]); ((TAtom "L32"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk2"); (TAtom "pr.1"); (TAtom "pr.2"); (TAtom "v0"); (TAtom "v37")]); ((TAtom "L33"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk2"); (TAtom "pr.1"); (TAtom "pr.2"); (TAtom "v0")]); ((TAtom "L20"), []); ((TAtom "L22"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk2"); (TAtom "pr.1"); (TAtom "pr.2"); (TAtom "v0")]); ((TAtom "L42"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk2"); (TAtom "pr.1"); (TAtom "pr.2"); (TAtom "v0")]); ((TAtom "L43"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk6"); (TAtom "pr.1"); (TAtom "pr.2"); (TAtom "v0"); (TAtom "v65")]); ((TAtom "L67"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk6"); (TAtom "pr.1"); (TAtom "pr.2"); (TAtom "v0"); (TAtom "v65")]); ((TAtom "L68"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v86"); (TAtom "v89")]); ((TAtom "L17"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "iw_1.v3")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (32)), "buf->mode")]); ((TAtom "L6"), []); ((TAtom "L15"), []); ((TAtom "L16"), [(2%N, (TApp "tmp" [(TAtom "v24")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (8)), "buf->write_ptr"); (5%N, (TApp "tmp" [(TAtom "v27")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (16)), "buf->write_end")]); ((TAtom "L32"), []); ((TAtom "L33"), []); ((TAtom "L20"), []); ((TAtom "L22"), [(2%N, (TApp "tmp" [(TAtom "v45")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (8)), "buf->write_ptr"); (5%N, (TApp "tmp" [(TAtom "v48")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (16)), "buf->write_end")]); ((TAtom "L42"), []); ((TAtom "L43"), [(2%N, (TApp "tmp" [(TAtom "v58")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (16)), "buf->write_end"); (5%N, (TApp "tmp" [(TAtom "v61")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (8)), "buf->write_ptr")]); ((TAtom "L67"), []); ((TAtom "L68"), [(1%N, (TApp "tmp" [(TAtom "v61")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (8)), "buf->write_ptr"); (4%N, (TApp "tmp" [(TAtom "v74")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (8)), "buf->write_ptr"); (7%N, (TApp "tmp" [(TAtom "v74")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (8)), "buf->write_ptr")]); ((TAtom "L17"), [])].


End fn___printf_buffer_write.

Module fn___printf_buffer_flush.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_1, 59%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_0, 115%N)); ((TAtom "L2"), (file_1, 63%N)); ((TAtom "iw_2.start"), (file_3, 41%N)); ((TAtom "iw_2.L9"), (file_3, 47%N)); ((TAtom "iw_2.L11"), (file_3, 50%N)); ((TAtom "iw_2.L12"), (file_3, 53%N)); ((TAtom "iw_2.L14"), (file_3, 56%N)); ((TAtom "iw_2.L16"), (file_3, 59%N)); ((TAtom "iw_2.L18"), (file_3, 62%N)); ((TAtom "iw_2.L21"), (file_3, 66%N)); ((TAtom "iw_2.L23"), (file_3, 69%N)); ((TAtom "iw_2.L25"), (file_3, 73%N)); ((TAtom "iw_2.L27"), (file_3, 77%N)); ((TAtom "iw_2.L31"), (file_3, 41%N)); ((TAtom "iw_2.L34"), (file_3, 41%N)); ((TAtom "iw_2.L37"), (file_3, 41%N)); ((TAtom "iw_2.L39"), (file_3, 41%N)); ((TAtom "iw_2.L35"), (file_3, 41%N)); ((TAtom "iw_2.L43"), (file_3, 41%N)); ((TAtom "iw_2.L45"), (file_3, 41%N)); ((TAtom "iw_2.L32"), (file_3, 41%N)); ((TAtom "iw_2.L49"), (file_3, 41%N)); ((TAtom "iw_2.L52"), (file_3, 41%N)); ((TAtom "iw_2.L54"), (file_3, 41%N)); ((TAtom "iw_2.L50"), (file_3, 41%N)); ((TAtom "iw_2.L58"), (file_3, 41%N)); ((TAtom "iw_2.L60"), (file_3, 41%N)); ((TAtom "iw_2.L6"), (file_3, 80%N)); ((TAtom "iw_3.start"), (file_0, 115%N)); ((TAtom "L13"), (file_1, 67%N)); ((TAtom "L15"), (file_1, 70%N)); ((TAtom "L22"), (file_1, 70%N)); ((TAtom "L23"), (file_1, 71%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "buf"); ((TAtom "iw_1.v2"), "buf"); ((TAtom "iw_2.iw_1.v0"), "buf"); ((TAtom "iw_2.iw_1.v2"), "buf"); ((TAtom "iw_2.v0"), "buf"); ((TAtom "iw_2.v10"), "buf"); ((TAtom "iw_2.v13"), "buf"); ((TAtom "iw_2.v15"), "buf"); ((TAtom "iw_2.v17"), "buf"); ((TAtom "iw_2.v2"), "buf"); ((TAtom "iw_2.v20"), "buf"); ((TAtom "iw_2.v22"), "buf"); ((TAtom "iw_2.v24"), "buf"); ((TAtom "iw_2.v26"), "buf"); ((TAtom "iw_2.v28"), "buf"); ((TAtom "iw_3.v0"), "buf"); ((TAtom "iw_3.v2"), "buf"); ((TAtom "v0"), "buf"); ((TAtom "v12"), "buf"); ((TAtom "v16"), "buf"); ((TAtom "v24"), "buf"); ((TAtom "v27"), "buf"); ((TAtom "v5"), "buf")].

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  [((TAtom "chk0"), ((TAtom "v0"), "buf", 32)); ((TAtom "chk2"), ((TAtom "iw_2.v19"), "&__libc_errno", 0)); ((TAtom "chk3"), ((TAtom "v0"), "buf", 32)); ((TAtom "chk4"), ((TAtom "v0"), "buf", 32)); ((TAtom "chk5"), ((TAtom "v0"), "buf", 8)); ((TAtom "iw_1.v3"), ((TAtom "v0"), "buf", 32)); ((TAtom "iw_2.iw_1.v3"), ((TAtom "v0"), "buf", 32)); ((TAtom "iw_2.v19"), ((TAtom "iw_2.v19"), "&__libc_errno", 0)); ((TAtom "iw_2.v3"), ((TAtom "v0"), "buf", 32)); ((TAtom "iw_3.v3"), ((TAtom "v0"), "buf", 32)); ((TAtom "v0"), ((TAtom "v0"), "buf", 0)); ((TAtom "v25"), ((TAtom "v0"), "buf", 8)); ((TAtom "v28"), ((TAtom "v0"), "buf", 16))].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "L2"), []); ((TAtom "iw_2.start"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "iw_2.L9"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "iw_2.L11"), []); ((TAtom "iw_2.L12"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "iw_2.L14"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "iw_2.L16"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "iw_2.L18"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "iw_2.L21"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "iw_2.L23"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "iw_2.L25"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "iw_2.L27"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "iw_2.L31"), [(TAtom "chk0"); (TAtom "iw_2.v4"); (TAtom "v0")]); ((TAtom "iw_2.L34"), [(TAtom "chk0"); (TAtom "iw_2.v4"); (TAtom "v0")]); ((TAtom "iw_2.L37"), [(TAtom "chk0"); (TAtom "iw_2.v4"); (TAtom "v0")]); ((TAtom "iw_2.L39"), [(TAtom "chk0"); (TAtom "iw_2.v4"); (TAtom "v0")]); ((TAtom "iw_2.L35"), [(TAtom "chk0"); (TAtom "iw_2.v4"); (TAtom "v0")]); ((TAtom "iw_2.L43"), [(TAtom "chk0"); (TAtom "iw_2.v4"); (TAtom "v0")]); ((TAtom "iw_2.L45"), [(TAtom "chk0"); (TAtom "iw_2.v4"); (TAtom "v0")]); ((TAtom "iw_2.L32"), [(TAtom "chk0"); (TAtom "iw_2.v4"); (TAtom "v0")]); ((TAtom "iw_2.L49"), [(TAtom "chk0"); (TAtom "iw_2.v4"); (TAtom "v0")]); ((TAtom "iw_2.L52"), [(TAtom "chk0"); (TAtom "iw_2.v4"); (TAtom "v0")]); ((TAtom "iw_2.L54"), [(TAtom "chk0"); (TAtom "iw_2.v4"); (TAtom "v0")]); ((TAtom "iw_2.L50"), [(TAtom "chk0"); (TAtom "iw_2.v4"); (TAtom "v0")]); ((TAtom "iw_2.L58"), [(TAtom "chk0"); (TAtom "iw_2.v4"); (TAtom "v0")]); ((TAtom "iw_2.L60"), [(TAtom "chk0"); (TAtom "iw_2.v4"); (TAtom "v0")]); ((TAtom "iw_2.L6"), []); ((TAtom "iw_3.start"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L13"), []); ((TAtom "L15"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L22"), []); ((TAtom "L23"), [])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L2"), []); ((TAtom "iw_2.start"), [(TAtom "chk0"); (TAtom "iw_2.v4"); (TAtom "v0")]); ((TAtom "iw_2.L9"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "iw_2.L11"), []); ((TAtom "iw_2.L12"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "iw_2.L14"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "iw_2.L16"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "iw_2.L18"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "iw_2.L21"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "iw_2.L23"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "iw_2.L25"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "iw_2.L27"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "iw_2.L31"), [(TAtom "chk0"); (TAtom "iw_2.v4"); (TAtom "v0")]); ((TAtom "iw_2.L34"), [(TAtom "chk0"); (TAtom "iw_2.v4"); (TAtom "v0")]); ((TAtom "iw_2.L37"), [(TAtom "chk0"); (TAtom "iw_2.v4"); (TAtom "v0")]); ((TAtom "iw_2.L39"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "iw_2.L35"), [(TAtom "chk0"); (TAtom "iw_2.v4"); (TAtom "v0")]); ((TAtom "iw_2.L43"), [(TAtom "chk0"); (TAtom "iw_2.v4"); (TAtom "v0")]); ((TAtom "iw_2.L45"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "iw_2.L32"), [(TAtom "chk0"); (TAtom "iw_2.v4"); (TAtom "v0")]); ((TAtom "iw_2.L49"), [(TAtom "chk0"); (TAtom "iw_2.v4"); (TAtom "v0")]); ((TAtom "iw_2.L52"), [(TAtom "chk0"); (TAtom "iw_2.v4"); (TAtom "v0")]); ((TAtom "iw_2.L54"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "iw_2.L50"), [(TAtom "chk0"); (TAtom "iw_2.v4"); (TAtom "v0")]); ((TAtom "iw_2.L58"), [(TAtom "chk0"); (TAtom "iw_2.v4"); (TAtom "v0")]); ((TAtom "iw_2.L60"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "iw_2.L6"), []); ((TAtom "iw_3.start"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L13"), []); ((TAtom "L15"), []); ((TAtom "L22"), []); ((TAtom "L23"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "iw_1.v3")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (32)), "buf->mode")]); ((TAtom "L2"), []); ((TAtom "iw_2.start"), [(1%N, (TApp "tmp" [(TAtom "iw_1.v3")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (32)), "buf->mode")]); ((TAtom "iw_2.L9"), []); ((TAtom "iw_2.L11"), []); ((TAtom "iw_2.L12"), []); ((TAtom "iw_2.L14"), []); ((TAtom "iw_2.L16"), []); ((TAtom "iw_2.L18"), [(2%N, (TApp "tmp" [(TAtom "iw_2.v19")]), (0), (Some 4), false, true, (Some (TAtom "iw_2.v19")), (Some (0)), "opaque"); (5%N, (TApp "tmp" [(TAtom "iw_2.iw_1.v3")]), (0), (Some 4), false, true, (Some (TAtom "v0")), (Some (32)), "buf->mode")]); ((TAtom "iw_2.L21"), []); ((TAtom "iw_2.L23"), []); ((TAtom "iw_2.L25"), []); ((TAtom "iw_2.L27"), []); ((TAtom "iw_2.L31"), []); ((TAtom "iw_2.L34"), []); ((TAtom "iw_2.L37"), []); ((TAtom "iw_2.L39"), []); ((TAtom "iw_2.L35"), []); ((TAtom "iw_2.L43"), []); ((TAtom "iw_2.L45"), []); ((TAtom "iw_2.L32"), []); ((TAtom "iw_2.L49"), []); ((TAtom "iw_2.L52"), []); ((TAtom "iw_2.L54"), []); ((TAtom "iw_2.L50"), []); ((TAtom "iw_2.L58"), []); ((TAtom "iw_2.L60"), []); ((TAtom "iw_2.L6"), []); ((TAtom "iw_3.start"), [(2%N, (TApp "tmp" [(TAtom "iw_3.v3")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (32)), "buf->mode")]); ((TAtom "L13"), []); ((TAtom "L15"), [(2%N, (TApp "tmp" [(TAtom "v25")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (8)), "buf->write_ptr"); (4%N, (TApp "tmp" [(TAtom "v25")]), (8), (Some 8), true, false, (Some (TAtom "v0")), (Some (16)), "buf->write_end")]); ((TAtom "L22"), []); ((TAtom "L23"), [])].


End fn___printf_buffer_flush.

(** Projection keeps instruction bodies out of the VM code used by the membership check. *)
Definition source_blocks : list (string * list name) := Eval lazy in
  [("__printf_buffer_write", map b_label (fn_blocks Unit_stdioZ2dcommon_printf_buffer_write_os.fn___printf_buffer_write)); ("__printf_buffer_flush", map b_label (fn_blocks Unit_stdioZ2dcommon_printf_buffer_flush_os.fn___printf_buffer_flush))].

(** Projection keeps live sets and memory access records out of the membership computation. *)
Definition table_labels : list (string * list name) := Eval lazy in
  [("__printf_buffer_write", app (map fst fn___printf_buffer_write.block_src) (app (map fst fn___printf_buffer_write.live_in) (app (map fst fn___printf_buffer_write.live_out) (app (map fst fn___printf_buffer_write.footprint) (fn___printf_buffer_write.loop_heads))))); ("__printf_buffer_flush", app (map fst fn___printf_buffer_flush.block_src) (app (map fst fn___printf_buffer_flush.live_in) (app (map fst fn___printf_buffer_flush.live_out) (app (map fst fn___printf_buffer_flush.footprint) (fn___printf_buffer_flush.loop_heads)))))].

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

End PrintfBufferIoSrc.
