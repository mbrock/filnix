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


From Glibc Require Import SysCode.
Module SysSrc.

Definition file_0 : string := "../nptl/descr.h".

Definition file_1 : string := "../sysdeps/nptl/pthreadP.h".

Definition file_2 : string := "../sysdeps/unix/sysv/linux/_exit.c".

Definition file_3 : string := "../sysdeps/unix/sysv/linux/close_nocancel.c".

Definition file_4 : string := "../sysdeps/unix/sysv/linux/close_nocancel_nostatus.c".

Definition file_5 : string := "../sysdeps/unix/sysv/linux/fstat64.c".

Definition file_6 : string := "../sysdeps/unix/sysv/linux/isatty_nostatus.c".

Definition file_7 : string := "../sysdeps/unix/sysv/linux/lseek64.c".

Definition file_8 : string := "../sysdeps/unix/sysv/linux/write.c".

Definition file_9 : string := "../sysdeps/unix/sysv/linux/write_nocancel.c".

Definition file_10 : string := "libc-cleanup.c".

Module fn___isatty_nostatus.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_6, 22%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_6, 25%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fd"); ((TAtom "v3"), "fd")].

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  [((TAtom "v0"), ((TAtom "v0"), "fd", 0)); ((TAtom "v2"), ((TAtom "v2"), "&k_termios", 0))].

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


End fn___isatty_nostatus.

Module fn___GI___libc_write.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_8, 24%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_8, 27%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fd"); ((TAtom "v2"), "buf"); ((TAtom "v4"), "nbytes"); ((TAtom "v6"), "fd"); ((TAtom "v7"), "buf"); ((TAtom "v8"), "nbytes")].

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  [((TAtom "v0"), ((TAtom "v0"), "fd", 0)); ((TAtom "v2"), ((TAtom "v2"), "buf", 0)); ((TAtom "v4"), ((TAtom "v4"), "nbytes", 0))].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), [])].


End fn___GI___libc_write.

Module fn___lseek64.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_7, 27%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_7, 30%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fd"); ((TAtom "v2"), "offset"); ((TAtom "v4"), "whence"); ((TAtom "v6"), "fd"); ((TAtom "v7"), "offset"); ((TAtom "v8"), "whence")].

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  [((TAtom "v0"), ((TAtom "v0"), "fd", 0)); ((TAtom "v2"), ((TAtom "v2"), "offset", 0)); ((TAtom "v4"), ((TAtom "v4"), "whence", 0))].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), [])].


End fn___lseek64.

Module fn___GI___fstat64.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_5, 29%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_5, 32%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fd"); ((TAtom "v2"), "buf"); ((TAtom "v4"), "fd"); ((TAtom "v5"), "buf")].

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  [((TAtom "v0"), ((TAtom "v0"), "fd", 0)); ((TAtom "v2"), ((TAtom "v2"), "buf", 0))].

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
  [((TAtom "start"), [])].


End fn___GI___fstat64.

Module fn___GI___close_nocancel.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_3, 24%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_3, 27%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fd"); ((TAtom "v2"), "fd")].

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  [((TAtom "v0"), ((TAtom "v0"), "fd", 0))].

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


End fn___GI___close_nocancel.

Module fn___GI___close_nocancel_nostatus.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_4, 24%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_4, 27%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fd"); ((TAtom "v2"), "fd")].

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  [((TAtom "v0"), ((TAtom "v0"), "fd", 0))].

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


End fn___GI___close_nocancel_nostatus.

Module fn___GI__exit.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_2, 26%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_2, 30%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "status"); ((TAtom "v2"), "status")].

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  [((TAtom "v0"), ((TAtom "v0"), "status", 0))].

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


End fn___GI__exit.

Module fn___GI___libc_cleanup_push_defer.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_10, 22%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_10, 25%N)); ((TAtom "L22"), (file_10, 29%N)); ((TAtom "L35"), (file_10, 39%N)); ((TAtom "L36"), (file_10, 29%N)); ((TAtom "L15"), (file_10, 29%N)); ((TAtom "L41"), (file_10, 44%N)); ((TAtom "L42"), (file_10, 44%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "pr.1"), "cancelhandling"); ((TAtom "pr.2"), "cancelhandling"); ((TAtom "pr.3"), "cancelhandling"); ((TAtom "v0"), "buffer"); ((TAtom "v10"), "self"); ((TAtom "v12"), "cancelhandling"); ((TAtom "v16"), "cancelhandling"); ((TAtom "v25"), "cancelhandling"); ((TAtom "v28"), "newval"); ((TAtom "v29"), "self"); ((TAtom "v3"), "self"); ((TAtom "v31"), "newval"); ((TAtom "v32"), "cancelhandling"); ((TAtom "v33"), "cancelhandling"); ((TAtom "v38"), "buffer"); ((TAtom "v4"), "buffer"); ((TAtom "v43"), "cancelhandling"); ((TAtom "v47"), "self"); ((TAtom "v49"), "buffer"); ((TAtom "v6"), "self")].

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  [((TAtom "chk0"), ((TAtom "v3"), "self", 776)); ((TAtom "chk1"), ((TAtom "v0"), "buffer", 24)); ((TAtom "chk2"), ((TAtom "v3"), "self", 792)); ((TAtom "chk3"), ((TAtom "v3"), "self", 792)); ((TAtom "chk4"), ((TAtom "v0"), "buffer", 16)); ((TAtom "chk5"), ((TAtom "v3"), "self", 776)); ((TAtom "pr.1"), ((TAtom "pr.1"), "cancelhandling", 0)); ((TAtom "pr.2"), ((TAtom "pr.2"), "cancelhandling", 0)); ((TAtom "pr.3"), ((TAtom "pr.3"), "cancelhandling", 0)); ((TAtom "v0"), ((TAtom "v0"), "buffer", 0)); ((TAtom "v11"), ((TAtom "v3"), "self", 792)); ((TAtom "v12"), ((TAtom "v12"), "cancelhandling", 0)); ((TAtom "v28"), ((TAtom "v28"), "newval", 0)); ((TAtom "v3"), ((TAtom "v3"), "self", 0)); ((TAtom "v30"), ((TAtom "v3"), "self", 792)); ((TAtom "v33"), ((TAtom "v33"), "cancelhandling", 0)); ((TAtom "v39"), ((TAtom "v0"), "buffer", 16)); ((TAtom "v48"), ((TAtom "v3"), "self", 776)); ((TAtom "v5"), ((TAtom "v0"), "buffer", 24)); ((TAtom "v7"), ((TAtom "v3"), "self", 776))].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L22")].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "L22"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v3")]); ((TAtom "L35"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "pr.2"); (TAtom "v0"); (TAtom "v3"); (TAtom "v33")]); ((TAtom "L36"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "pr.2"); (TAtom "v0"); (TAtom "v3"); (TAtom "v33")]); ((TAtom "L15"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v3")]); ((TAtom "L41"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v3"); (TAtom "v39")]); ((TAtom "L42"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v3"); (TAtom "v39")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v12"); (TAtom "v3")]); ((TAtom "L22"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "pr.2"); (TAtom "v0"); (TAtom "v3"); (TAtom "v33")]); ((TAtom "L35"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "pr.2"); (TAtom "v0"); (TAtom "v3"); (TAtom "v33")]); ((TAtom "L36"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v3")]); ((TAtom "L15"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v3"); (TAtom "v39")]); ((TAtom "L41"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v3"); (TAtom "v39")]); ((TAtom "L42"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), [(4%N, (TApp "tmp" [(TAtom "v7")]), (0), (Some 8), true, false, (Some (TAtom "v3")), (Some (776)), "self->cleanup"); (6%N, (TApp "tmp" [(TAtom "v5")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (24)), "buffer->__prev"); (9%N, (TApp "tmp" [(TAtom "v11")]), (0), (Some 4), true, false, (Some (TAtom "v3")), (Some (792)), "self->cancelhandling")]); ((TAtom "L22"), [(3%N, (TApp "tmp" [(TAtom "v30")]), (0), (Some 4), true, true, (Some (TAtom "v3")), (Some (792)), "self->cancelhandling")]); ((TAtom "L35"), []); ((TAtom "L36"), []); ((TAtom "L15"), []); ((TAtom "L41"), []); ((TAtom "L42"), [(1%N, (TApp "tmp" [(TAtom "v39")]), (0), (Some 4), false, true, (Some (TAtom "v0")), (Some (16)), "buffer->__canceltype"); (4%N, (TApp "tmp" [(TAtom "v48")]), (0), (Some 8), false, true, (Some (TAtom "v3")), (Some (776)), "self->cleanup")])].


End fn___GI___libc_cleanup_push_defer.

Module fn___GI___libc_cleanup_pop_restore.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_10, 52%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_10, 55%N)); ((TAtom "L20"), (file_10, 60%N)); ((TAtom "L21"), (file_10, 60%N)); ((TAtom "L29"), (file_10, 59%N)); ((TAtom "L41"), (file_10, 68%N)); ((TAtom "L42"), (file_10, 59%N)); ((TAtom "iw_1.start"), (file_0, 463%N)); ((TAtom "L44"), (file_10, 72%N)); ((TAtom "iw_2.L12"), (file_1, 256%N)); ((TAtom "iw_2.L13"), (file_1, 268%N)); ((TAtom "iw_2.L37"), (file_1, 268%N)); ((TAtom "iw_2.L38"), (file_1, 256%N)); ((TAtom "iw_2.L14"), (file_1, 271%N)); ((TAtom "L15"), (file_10, 52%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "value"); ((TAtom "iw_1.v2"), "value"); ((TAtom "iw_2.pr.1"), "oldval"); ((TAtom "iw_2.pr.2"), "oldval"); ((TAtom "iw_2.v0"), "result"); ((TAtom "iw_2.v10"), "oldval"); ((TAtom "iw_2.v15"), "oldval"); ((TAtom "iw_2.v19"), "newval"); ((TAtom "iw_2.v20"), "newval"); ((TAtom "iw_2.v23"), "newval"); ((TAtom "iw_2.v27"), "oldval"); ((TAtom "iw_2.v28"), "newval"); ((TAtom "iw_2.v3"), "self"); ((TAtom "iw_2.v31"), "self"); ((TAtom "iw_2.v33"), "newval"); ((TAtom "iw_2.v34"), "oldval"); ((TAtom "iw_2.v35"), "oldval"); ((TAtom "iw_2.v4"), "self"); ((TAtom "iw_2.v40"), "self"); ((TAtom "iw_2.v6"), "result"); ((TAtom "iw_2.v8"), "self"); ((TAtom "pr.1"), "cancelhandling"); ((TAtom "pr.2"), "cancelhandling"); ((TAtom "v0"), "buffer"); ((TAtom "v10"), "self"); ((TAtom "v12"), "cancelhandling"); ((TAtom "v16"), "buffer"); ((TAtom "v22"), "cancelhandling"); ((TAtom "v3"), "self"); ((TAtom "v32"), "cancelhandling"); ((TAtom "v34"), "newval"); ((TAtom "v35"), "self"); ((TAtom "v37"), "newval"); ((TAtom "v38"), "cancelhandling"); ((TAtom "v39"), "cancelhandling"); ((TAtom "v4"), "self"); ((TAtom "v47"), "cancelhandling"); ((TAtom "v6"), "buffer")].

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  [((TAtom "chk0"), ((TAtom "v0"), "buffer", 24)); ((TAtom "chk1"), ((TAtom "v3"), "self", 776)); ((TAtom "chk2"), ((TAtom "v3"), "self", 792)); ((TAtom "chk3"), ((TAtom "v0"), "buffer", 16)); ((TAtom "chk4"), ((TAtom "v3"), "self", 792)); ((TAtom "chk5"), ((TAtom "iw_2.v3"), "self", 1608)); ((TAtom "chk6"), ((TAtom "iw_2.v3"), "self", 792)); ((TAtom "chk7"), ((TAtom "iw_2.v3"), "self", 792)); ((TAtom "chk8"), ((TAtom "iw_2.v3"), "self", 784)); ((TAtom "iw_2.pr.1"), ((TAtom "iw_2.pr.1"), "oldval", 0)); ((TAtom "iw_2.pr.2"), ((TAtom "iw_2.pr.2"), "oldval", 0)); ((TAtom "iw_2.v10"), ((TAtom "iw_2.v10"), "oldval", 0)); ((TAtom "iw_2.v19"), ((TAtom "iw_2.v19"), "newval", 0)); ((TAtom "iw_2.v23"), ((TAtom "iw_2.v23"), "newval", 0)); ((TAtom "iw_2.v3"), ((TAtom "iw_2.v3"), "self", 0)); ((TAtom "iw_2.v32"), ((TAtom "iw_2.v3"), "self", 792)); ((TAtom "iw_2.v35"), ((TAtom "iw_2.v35"), "oldval", 0)); ((TAtom "iw_2.v41"), ((TAtom "iw_2.v3"), "self", 784)); ((TAtom "iw_2.v5"), ((TAtom "iw_2.v3"), "self", 1608)); ((TAtom "iw_2.v9"), ((TAtom "iw_2.v3"), "self", 792)); ((TAtom "pr.1"), ((TAtom "pr.1"), "cancelhandling", 0)); ((TAtom "pr.2"), ((TAtom "pr.2"), "cancelhandling", 0)); ((TAtom "v0"), ((TAtom "v0"), "buffer", 0)); ((TAtom "v11"), ((TAtom "v3"), "self", 792)); ((TAtom "v12"), ((TAtom "v12"), "cancelhandling", 0)); ((TAtom "v17"), ((TAtom "v0"), "buffer", 16)); ((TAtom "v3"), ((TAtom "v3"), "self", 0)); ((TAtom "v34"), ((TAtom "v34"), "newval", 0)); ((TAtom "v36"), ((TAtom "v3"), "self", 792)); ((TAtom "v39"), ((TAtom "v39"), "cancelhandling", 0)); ((TAtom "v5"), ((TAtom "v3"), "self", 776)); ((TAtom "v7"), ((TAtom "v0"), "buffer", 24))].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L29"); (TAtom "iw_2.L12")].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "L20"), [(TAtom "chk1"); (TAtom "v12"); (TAtom "v3")]); ((TAtom "L21"), [(TAtom "chk1"); (TAtom "v12"); (TAtom "v3")]); ((TAtom "L29"), [(TAtom "chk1"); (TAtom "v3")]); ((TAtom "L41"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "v3"); (TAtom "v39")]); ((TAtom "L42"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "v3"); (TAtom "v39")]); ((TAtom "iw_1.start"), [(TAtom "pr.2")]); ((TAtom "L44"), []); ((TAtom "iw_2.L12"), [(TAtom "chk5"); (TAtom "iw_2.v3")]); ((TAtom "iw_2.L13"), [(TAtom "chk5"); (TAtom "iw_2.pr.1"); (TAtom "iw_2.v23"); (TAtom "iw_2.v3")]); ((TAtom "iw_2.L37"), [(TAtom "chk5"); (TAtom "iw_2.pr.1"); (TAtom "iw_2.v3"); (TAtom "iw_2.v35")]); ((TAtom "iw_2.L38"), [(TAtom "chk5"); (TAtom "iw_2.pr.1"); (TAtom "iw_2.v3"); (TAtom "iw_2.v35")]); ((TAtom "iw_2.L14"), [(TAtom "chk5"); (TAtom "iw_2.v3")]); ((TAtom "L15"), [])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "chk1"); (TAtom "v12"); (TAtom "v3")]); ((TAtom "L20"), [(TAtom "chk1"); (TAtom "v12"); (TAtom "v25"); (TAtom "v3")]); ((TAtom "L21"), [(TAtom "chk1"); (TAtom "v12"); (TAtom "v3")]); ((TAtom "L29"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "v3"); (TAtom "v39")]); ((TAtom "L41"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "v3"); (TAtom "v39")]); ((TAtom "L42"), [(TAtom "chk1"); (TAtom "pr.2"); (TAtom "v3")]); ((TAtom "iw_1.start"), []); ((TAtom "L44"), [(TAtom "chk5"); (TAtom "iw_2.v10"); (TAtom "iw_2.v3")]); ((TAtom "iw_2.L12"), [(TAtom "chk5"); (TAtom "iw_2.pr.1"); (TAtom "iw_2.v23"); (TAtom "iw_2.v3")]); ((TAtom "iw_2.L13"), [(TAtom "chk5"); (TAtom "iw_2.pr.1"); (TAtom "iw_2.v3"); (TAtom "iw_2.v35")]); ((TAtom "iw_2.L37"), [(TAtom "chk5"); (TAtom "iw_2.pr.1"); (TAtom "iw_2.v3"); (TAtom "iw_2.v35")]); ((TAtom "iw_2.L38"), [(TAtom "chk5"); (TAtom "iw_2.pr.2"); (TAtom "iw_2.v3")]); ((TAtom "iw_2.L14"), []); ((TAtom "L15"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), [(4%N, (TApp "tmp" [(TAtom "v7")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (24)), "buffer->__prev"); (6%N, (TApp "tmp" [(TAtom "v5")]), (0), (Some 8), false, true, (Some (TAtom "v3")), (Some (776)), "self->cleanup"); (9%N, (TApp "tmp" [(TAtom "v11")]), (0), (Some 4), true, false, (Some (TAtom "v3")), (Some (792)), "self->cancelhandling"); (12%N, (TApp "tmp" [(TAtom "v17")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (16)), "buffer->__canceltype")]); ((TAtom "L20"), []); ((TAtom "L21"), []); ((TAtom "L29"), [(3%N, (TApp "tmp" [(TAtom "v36")]), (0), (Some 4), true, true, (Some (TAtom "v3")), (Some (792)), "self->cancelhandling")]); ((TAtom "L41"), []); ((TAtom "L42"), []); ((TAtom "iw_1.start"), []); ((TAtom "L44"), [(4%N, (TApp "tmp" [(TAtom "iw_2.v5")]), (0), (Some 8), false, true, (Some (TAtom "iw_2.v3")), (Some (1608)), "self->result"); (7%N, (TApp "tmp" [(TAtom "iw_2.v9")]), (0), (Some 4), true, false, (Some (TAtom "iw_2.v3")), (Some (792)), "self->cancelhandling")]); ((TAtom "iw_2.L12"), []); ((TAtom "iw_2.L13"), [(2%N, (TApp "tmp" [(TAtom "iw_2.v32")]), (0), (Some 4), true, true, (Some (TAtom "iw_2.v3")), (Some (792)), "self->cancelhandling")]); ((TAtom "iw_2.L37"), []); ((TAtom "iw_2.L38"), []); ((TAtom "iw_2.L14"), [(2%N, (TApp "tmp" [(TAtom "iw_2.v41")]), (0), (Some 8), true, false, (Some (TAtom "iw_2.v3")), (Some (784)), "self->cleanup_jmp_buf")]); ((TAtom "L15"), [])].


End fn___GI___libc_cleanup_pop_restore.

Module fn___GI___write_nocancel.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_9, 24%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_9, 27%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fd"); ((TAtom "v2"), "buf"); ((TAtom "v4"), "nbytes"); ((TAtom "v6"), "fd"); ((TAtom "v7"), "buf"); ((TAtom "v8"), "nbytes")].

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  [((TAtom "v0"), ((TAtom "v0"), "fd", 0)); ((TAtom "v2"), ((TAtom "v2"), "buf", 0)); ((TAtom "v4"), ((TAtom "v4"), "nbytes", 0))].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), [])].


End fn___GI___write_nocancel.

(** Projection keeps instruction bodies out of the VM code used by the membership check. *)
Definition source_blocks : list (string * option (list name)) := Eval lazy in
  map (fun n => (n,
    match find_direct (TAtom n) sys_module with
    | Some (Defined f) => Some (map b_label (fn_blocks f))
    | _ => None
    end)) ["__isatty_nostatus"; "__GI___libc_write"; "__lseek64"; "__GI___fstat64"; "__GI___close_nocancel"; "__GI___close_nocancel_nostatus"; "__GI__exit"; "__GI___libc_cleanup_push_defer"; "__GI___libc_cleanup_pop_restore"; "__GI___write_nocancel"].

(** Projection keeps live sets and memory access records out of the membership computation. *)
Definition table_labels : list (string * list name) := Eval lazy in
  [("__isatty_nostatus", app (map fst fn___isatty_nostatus.block_src) (app (map fst fn___isatty_nostatus.live_in) (app (map fst fn___isatty_nostatus.live_out) (app (map fst fn___isatty_nostatus.footprint) (fn___isatty_nostatus.loop_heads))))); ("__GI___libc_write", app (map fst fn___GI___libc_write.block_src) (app (map fst fn___GI___libc_write.live_in) (app (map fst fn___GI___libc_write.live_out) (app (map fst fn___GI___libc_write.footprint) (fn___GI___libc_write.loop_heads))))); ("__lseek64", app (map fst fn___lseek64.block_src) (app (map fst fn___lseek64.live_in) (app (map fst fn___lseek64.live_out) (app (map fst fn___lseek64.footprint) (fn___lseek64.loop_heads))))); ("__GI___fstat64", app (map fst fn___GI___fstat64.block_src) (app (map fst fn___GI___fstat64.live_in) (app (map fst fn___GI___fstat64.live_out) (app (map fst fn___GI___fstat64.footprint) (fn___GI___fstat64.loop_heads))))); ("__GI___close_nocancel", app (map fst fn___GI___close_nocancel.block_src) (app (map fst fn___GI___close_nocancel.live_in) (app (map fst fn___GI___close_nocancel.live_out) (app (map fst fn___GI___close_nocancel.footprint) (fn___GI___close_nocancel.loop_heads))))); ("__GI___close_nocancel_nostatus", app (map fst fn___GI___close_nocancel_nostatus.block_src) (app (map fst fn___GI___close_nocancel_nostatus.live_in) (app (map fst fn___GI___close_nocancel_nostatus.live_out) (app (map fst fn___GI___close_nocancel_nostatus.footprint) (fn___GI___close_nocancel_nostatus.loop_heads))))); ("__GI__exit", app (map fst fn___GI__exit.block_src) (app (map fst fn___GI__exit.live_in) (app (map fst fn___GI__exit.live_out) (app (map fst fn___GI__exit.footprint) (fn___GI__exit.loop_heads))))); ("__GI___libc_cleanup_push_defer", app (map fst fn___GI___libc_cleanup_push_defer.block_src) (app (map fst fn___GI___libc_cleanup_push_defer.live_in) (app (map fst fn___GI___libc_cleanup_push_defer.live_out) (app (map fst fn___GI___libc_cleanup_push_defer.footprint) (fn___GI___libc_cleanup_push_defer.loop_heads))))); ("__GI___libc_cleanup_pop_restore", app (map fst fn___GI___libc_cleanup_pop_restore.block_src) (app (map fst fn___GI___libc_cleanup_pop_restore.live_in) (app (map fst fn___GI___libc_cleanup_pop_restore.live_out) (app (map fst fn___GI___libc_cleanup_pop_restore.footprint) (fn___GI___libc_cleanup_pop_restore.loop_heads))))); ("__GI___write_nocancel", app (map fst fn___GI___write_nocancel.block_src) (app (map fst fn___GI___write_nocancel.live_in) (app (map fst fn___GI___write_nocancel.live_out) (app (map fst fn___GI___write_nocancel.footprint) (fn___GI___write_nocancel.loop_heads)))))].

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

End SysSrc.
