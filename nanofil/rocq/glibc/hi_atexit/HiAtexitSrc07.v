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


From Glibc Require Import HiAtexitSrcFiles.
Import HiAtexitSrcFiles.
Module HiAtexitSrc07.

Module fn___GI___write_nocancel.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_9, 24%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_9, 27%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fd"); ((TAtom "v2"), "buf"); ((TAtom "v4"), "nbytes"); ((TAtom "v6"), "fd"); ((TAtom "v7"), "buf"); ((TAtom "v8"), "nbytes")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [])].


End fn___GI___write_nocancel.

Module fn___lseek64.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_7, 27%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_7, 30%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fd"); ((TAtom "v2"), "offset"); ((TAtom "v4"), "whence"); ((TAtom "v6"), "fd"); ((TAtom "v7"), "offset"); ((TAtom "v8"), "whence")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
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

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [])].


End fn___GI___fstat64.

Module fn___GI___close_nocancel.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_4, 24%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_4, 27%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fd"); ((TAtom "v2"), "fd")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [])].


End fn___GI___close_nocancel.

Module fn___GI__exit.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_3, 26%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_3, 30%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "status"); ((TAtom "v2"), "status")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [])].


End fn___GI__exit.

Module fn___run_exit_handlers.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_16, 42%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_16, 48%N)); ((TAtom "L13"), (file_16, 48%N)); ((TAtom "L33"), (file_16, 48%N)); ((TAtom "L34"), (file_16, 48%N)); ((TAtom "L38"), (file_16, 48%N)); ((TAtom "L27"), (file_16, 48%N)); ((TAtom "L15"), (file_16, 48%N)); ((TAtom "L55"), (file_16, 52%N)); ((TAtom "L57"), (file_16, 54%N)); ((TAtom "L69"), (file_16, 54%N)); ((TAtom "L70"), (file_16, 54%N)); ((TAtom "L74"), (file_16, 54%N)); ((TAtom "L88"), (file_16, 65%N)); ((TAtom "L91"), (file_16, 71%N)); ((TAtom "L101"), (file_16, 75%N)); ((TAtom "L102"), (file_16, 77%N)); ((TAtom "L130"), (file_16, 91%N)); ((TAtom "L145"), (file_16, 96%N)); ((TAtom "L146"), (file_16, 96%N)); ((TAtom "L157"), (file_16, 96%N)); ((TAtom "L152"), (file_16, 97%N)); ((TAtom "L181"), (file_16, 98%N)); ((TAtom "L182"), (file_16, 98%N)); ((TAtom "L186"), (file_16, 98%N)); ((TAtom "L196"), (file_16, 101%N)); ((TAtom "L207"), (file_16, 105%N)); ((TAtom "L208"), (file_16, 105%N)); ((TAtom "L219"), (file_16, 105%N)); ((TAtom "L214"), (file_16, 106%N)); ((TAtom "L241"), (file_16, 107%N)); ((TAtom "L242"), (file_16, 107%N)); ((TAtom "L246"), (file_16, 107%N)); ((TAtom "L256"), (file_16, 112%N)); ((TAtom "L272"), (file_16, 118%N)); ((TAtom "L273"), (file_16, 118%N)); ((TAtom "L284"), (file_16, 118%N)); ((TAtom "L279"), (file_16, 119%N)); ((TAtom "L308"), (file_16, 120%N)); ((TAtom "L309"), (file_16, 120%N)); ((TAtom "L313"), (file_16, 120%N)); ((TAtom "L325"), (file_16, 80%N)); ((TAtom "L328"), (file_16, 80%N)); ((TAtom "L330"), (file_16, 80%N)); ((TAtom "L326"), (file_16, 80%N)); ((TAtom "L332"), (file_16, 80%N)); ((TAtom "L334"), (file_16, 80%N)); ((TAtom "L123"), (file_16, 124%N)); ((TAtom "L103"), (file_16, 130%N)); ((TAtom "L350"), (file_16, 134%N)); ((TAtom "L365"), (file_16, 137%N)); ((TAtom "L366"), (file_16, 137%N)); ((TAtom "L377"), (file_16, 137%N)); ((TAtom "L372"), (file_16, 139%N)); ((TAtom "L388"), (file_16, 140%N)); ((TAtom "L390"), (file_16, 143%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "status"); ((TAtom "v104"), "cur"); ((TAtom "v109"), "cur"); ((TAtom "v111"), "cur"); ((TAtom "v116"), "f"); ((TAtom "v119"), "__new_exitfn_called"); ((TAtom "v12"), "self"); ((TAtom "v120"), "f"); ((TAtom "v131"), "f"); ((TAtom "v133"), "onfct"); ((TAtom "v134"), "f"); ((TAtom "v137"), "arg"); ((TAtom "v138"), "onfct"); ((TAtom "v143"), "__futex"); ((TAtom "v147"), "__oldval"); ((TAtom "v153"), "__oldval"); ((TAtom "v165"), "__futex"); ((TAtom "v166"), "__futex"); ((TAtom "v167"), "__private"); ((TAtom "v168"), "onfct"); ((TAtom "v169"), "status"); ((TAtom "v170"), "arg"); ((TAtom "v177"), "__futex"); ((TAtom "v178"), "__atg3_old"); ((TAtom "v179"), "__atg3_old"); ((TAtom "v19"), "self"); ((TAtom "v194"), "__futex"); ((TAtom "v195"), "__futex"); ((TAtom "v197"), "f"); ((TAtom "v199"), "atfct"); ((TAtom "v2"), "listp"); ((TAtom "v200"), "atfct"); ((TAtom "v205"), "__futex"); ((TAtom "v209"), "__oldval"); ((TAtom "v215"), "__oldval"); ((TAtom "v227"), "__futex"); ((TAtom "v228"), "__futex"); ((TAtom "v229"), "__private"); ((TAtom "v230"), "atfct"); ((TAtom "v237"), "__futex"); ((TAtom "v238"), "__atg3_old"); ((TAtom "v239"), "__atg3_old"); ((TAtom "v254"), "__futex"); ((TAtom "v255"), "__futex"); ((TAtom "v257"), "f"); ((TAtom "v258"), "f"); ((TAtom "v260"), "cxafct"); ((TAtom "v261"), "f"); ((TAtom "v264"), "arg"); ((TAtom "v265"), "cxafct"); ((TAtom "v270"), "__futex"); ((TAtom "v274"), "__oldval"); ((TAtom "v280"), "__oldval"); ((TAtom "v29"), "__futex"); ((TAtom "v292"), "__futex"); ((TAtom "v293"), "__futex"); ((TAtom "v294"), "__private"); ((TAtom "v295"), "cxafct"); ((TAtom "v296"), "arg"); ((TAtom "v297"), "status"); ((TAtom "v30"), "__atg3_old"); ((TAtom "v304"), "__futex"); ((TAtom "v305"), "__atg3_old"); ((TAtom "v306"), "__atg3_old"); ((TAtom "v31"), "__atg3_old"); ((TAtom "v321"), "__futex"); ((TAtom "v322"), "__futex"); ((TAtom "v340"), "new_exitfn_called"); ((TAtom "v342"), "__new_exitfn_called"); ((TAtom "v347"), "listp"); ((TAtom "v348"), "cur"); ((TAtom "v353"), "listp"); ((TAtom "v358"), "cur"); ((TAtom "v363"), "__futex"); ((TAtom "v367"), "__oldval"); ((TAtom "v373"), "__oldval"); ((TAtom "v385"), "__futex"); ((TAtom "v386"), "__futex"); ((TAtom "v387"), "__private"); ((TAtom "v391"), "run_list_atexit"); ((TAtom "v393"), "status"); ((TAtom "v4"), "run_list_atexit"); ((TAtom "v46"), "__futex"); ((TAtom "v47"), "__futex"); ((TAtom "v50"), "self"); ((TAtom "v58"), "run_dtors"); ((TAtom "v6"), "run_dtors"); ((TAtom "v65"), "__futex"); ((TAtom "v66"), "__atg3_old"); ((TAtom "v67"), "__atg3_old"); ((TAtom "v82"), "__futex"); ((TAtom "v83"), "__futex"); ((TAtom "v89"), "listp"); ((TAtom "v90"), "cur"); ((TAtom "v94"), "cur"); ((TAtom "v99"), "__exit_funcs_done")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L101"); (TAtom "L145"); (TAtom "L207"); (TAtom "L272"); (TAtom "L365"); (TAtom "L88")].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L13"), [(TAtom "v0"); (TAtom "v12"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L33"), [(TAtom "v0"); (TAtom "v12"); (TAtom "v2"); (TAtom "v24"); (TAtom "v31"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L34"), [(TAtom "v0"); (TAtom "v12"); (TAtom "v2"); (TAtom "v24"); (TAtom "v31"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L38"), [(TAtom "v0"); (TAtom "v12"); (TAtom "v2"); (TAtom "v24"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L27"), [(TAtom "v0"); (TAtom "v12"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L15"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L55"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L57"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L69"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v60"); (TAtom "v67")]); ((TAtom "L70"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v60"); (TAtom "v67")]); ((TAtom "L74"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v60")]); ((TAtom "L88"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L91"), [(TAtom "v0"); (TAtom "v4")]); ((TAtom "L101"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L102"), [(TAtom "chk6"); (TAtom "chk9"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L130"), [(TAtom "chk13"); (TAtom "chk6"); (TAtom "v0"); (TAtom "v116"); (TAtom "v119"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L145"), [(TAtom "chk16"); (TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v133"); (TAtom "v137"); (TAtom "v140"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L146"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v133"); (TAtom "v137"); (TAtom "v140"); (TAtom "v147"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L157"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v133"); (TAtom "v137"); (TAtom "v140"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L152"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v133"); (TAtom "v137"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L181"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v172"); (TAtom "v179"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L182"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v172"); (TAtom "v179"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L186"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v172"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L196"), [(TAtom "chk13"); (TAtom "chk6"); (TAtom "v0"); (TAtom "v116"); (TAtom "v119"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L207"), [(TAtom "chk21"); (TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v199"); (TAtom "v2"); (TAtom "v202"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L208"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v199"); (TAtom "v2"); (TAtom "v202"); (TAtom "v209"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L219"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v199"); (TAtom "v2"); (TAtom "v202"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L214"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v199"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L241"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v2"); (TAtom "v232"); (TAtom "v239"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L242"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v2"); (TAtom "v232"); (TAtom "v239"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L246"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v2"); (TAtom "v232"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L256"), [(TAtom "chk13"); (TAtom "chk6"); (TAtom "v0"); (TAtom "v116"); (TAtom "v119"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L272"), [(TAtom "chk28"); (TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v2"); (TAtom "v260"); (TAtom "v264"); (TAtom "v267"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L273"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v2"); (TAtom "v260"); (TAtom "v264"); (TAtom "v267"); (TAtom "v274"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L284"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v2"); (TAtom "v260"); (TAtom "v264"); (TAtom "v267"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L279"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v2"); (TAtom "v260"); (TAtom "v264"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L308"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v2"); (TAtom "v299"); (TAtom "v306"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L309"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v2"); (TAtom "v299"); (TAtom "v306"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L313"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v2"); (TAtom "v299"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L325"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v121"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L328"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v121"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L330"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L326"), [(TAtom "chk13"); (TAtom "chk6"); (TAtom "v0"); (TAtom "v116"); (TAtom "v119"); (TAtom "v121"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L332"), [(TAtom "chk13"); (TAtom "chk6"); (TAtom "v0"); (TAtom "v116"); (TAtom "v119"); (TAtom "v121"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L334"), [(TAtom "chk13"); (TAtom "chk6"); (TAtom "v0"); (TAtom "v116"); (TAtom "v119"); (TAtom "v121"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L123"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L103"), [(TAtom "chk6"); (TAtom "chk9"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L350"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90")]); ((TAtom "L365"), [(TAtom "chk8"); (TAtom "v0"); (TAtom "v360"); (TAtom "v4")]); ((TAtom "L366"), [(TAtom "v0"); (TAtom "v360"); (TAtom "v367"); (TAtom "v4")]); ((TAtom "L377"), [(TAtom "v0"); (TAtom "v360"); (TAtom "v4")]); ((TAtom "L372"), [(TAtom "v0"); (TAtom "v4")]); ((TAtom "L388"), [(TAtom "v0")]); ((TAtom "L390"), [(TAtom "v0")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v12"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L13"), [(TAtom "v0"); (TAtom "v12"); (TAtom "v2"); (TAtom "v24"); (TAtom "v31"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L33"), [(TAtom "v0"); (TAtom "v12"); (TAtom "v2"); (TAtom "v24"); (TAtom "v31"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L34"), [(TAtom "v0"); (TAtom "v12"); (TAtom "v2"); (TAtom "v24"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L38"), [(TAtom "v0"); (TAtom "v12"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L27"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L15"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L55"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L57"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v60"); (TAtom "v67")]); ((TAtom "L69"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v60"); (TAtom "v67")]); ((TAtom "L70"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v60")]); ((TAtom "L74"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L88"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L91"), [(TAtom "chk8"); (TAtom "v0"); (TAtom "v360"); (TAtom "v364"); (TAtom "v4")]); ((TAtom "L101"), [(TAtom "chk6"); (TAtom "chk9"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L102"), [(TAtom "chk13"); (TAtom "chk6"); (TAtom "v0"); (TAtom "v116"); (TAtom "v119"); (TAtom "v121"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L130"), [(TAtom "chk16"); (TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v133"); (TAtom "v137"); (TAtom "v140"); (TAtom "v144"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L145"), [(TAtom "chk16"); (TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v133"); (TAtom "v137"); (TAtom "v140"); (TAtom "v147"); (TAtom "v148"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L146"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v133"); (TAtom "v137"); (TAtom "v140"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L157"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v133"); (TAtom "v137"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L152"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v172"); (TAtom "v179"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L181"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v172"); (TAtom "v179"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L182"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v172"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L186"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L196"), [(TAtom "chk21"); (TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v199"); (TAtom "v2"); (TAtom "v202"); (TAtom "v206"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L207"), [(TAtom "chk21"); (TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v199"); (TAtom "v2"); (TAtom "v202"); (TAtom "v209"); (TAtom "v210"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L208"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v199"); (TAtom "v2"); (TAtom "v202"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L219"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v199"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L214"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v2"); (TAtom "v232"); (TAtom "v239"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L241"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v2"); (TAtom "v232"); (TAtom "v239"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L242"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v2"); (TAtom "v232"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L246"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L256"), [(TAtom "chk28"); (TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v2"); (TAtom "v260"); (TAtom "v264"); (TAtom "v267"); (TAtom "v271"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L272"), [(TAtom "chk28"); (TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v2"); (TAtom "v260"); (TAtom "v264"); (TAtom "v267"); (TAtom "v274"); (TAtom "v275"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L273"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v2"); (TAtom "v260"); (TAtom "v264"); (TAtom "v267"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L284"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v2"); (TAtom "v260"); (TAtom "v264"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L279"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v2"); (TAtom "v299"); (TAtom "v306"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L308"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v2"); (TAtom "v299"); (TAtom "v306"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L309"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v2"); (TAtom "v299"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L313"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L325"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v121"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L328"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L330"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L326"), [(TAtom "chk13"); (TAtom "chk6"); (TAtom "v0"); (TAtom "v116"); (TAtom "v119"); (TAtom "v121"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L332"), [(TAtom "chk13"); (TAtom "chk6"); (TAtom "v0"); (TAtom "v116"); (TAtom "v119"); (TAtom "v121"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L334"), [(TAtom "chk13"); (TAtom "chk6"); (TAtom "v0"); (TAtom "v116"); (TAtom "v119"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L123"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L103"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90")]); ((TAtom "L350"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L365"), [(TAtom "chk8"); (TAtom "v0"); (TAtom "v360"); (TAtom "v367"); (TAtom "v368"); (TAtom "v4")]); ((TAtom "L366"), [(TAtom "v0"); (TAtom "v360"); (TAtom "v4")]); ((TAtom "L377"), [(TAtom "v0"); (TAtom "v4")]); ((TAtom "L372"), [(TAtom "v0")]); ((TAtom "L388"), [(TAtom "v0")]); ((TAtom "L390"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [(4%N, (TApp "tmp" [(TAtom "v17")]), (0), (Some 8), true, false, (Some (TAtom "v16")), (Some (8)))]); ((TAtom "L13"), [(2%N, (TApp "tmp" [(TAtom "v24")]), (0), (Some 4), true, true, (Some (TAtom "v24")), (Some (0)))]); ((TAtom "L33"), []); ((TAtom "L34"), []); ((TAtom "L38"), []); ((TAtom "L27"), [(3%N, (TApp "tmp" [(TAtom "v49")]), (0), (Some 8), false, true, (Some (TAtom "v48")), (Some (8)))]); ((TAtom "L15"), [(3%N, (TApp "tmp" [(TAtom "v52")]), (0), (Some 4), true, false, (Some (TAtom "v51")), (Some (4))); (6%N, (TApp "tmp" [(TAtom "v52")]), (0), (Some 4), false, true, (Some (TAtom "v51")), (Some (4)))]); ((TAtom "L55"), []); ((TAtom "L57"), [(2%N, (TApp "tmp" [(TAtom "v60")]), (0), (Some 4), true, true, (Some (TAtom "v60")), (Some (0)))]); ((TAtom "L69"), []); ((TAtom "L70"), []); ((TAtom "L74"), []); ((TAtom "L88"), [(1%N, (TApp "tmp" [(TAtom "v2")]), (0), (Some 8), true, false, (Some (TAtom "v2")), (Some (0)))]); ((TAtom "L91"), [(2%N, (TApp "tmp" [(TAtom "v98")]), (0), (Some 1), false, true, (Some (TAtom "v98")), (Some (0))); (5%N, (TApp "tmp" [(TAtom "v360")]), (0), (Some 4), true, false, (Some (TAtom "v360")), (Some (0)))]); ((TAtom "L101"), [(2%N, (TApp "tmp" [(TAtom "v105")]), (0), (Some 8), true, false, (Some (TAtom "v90")), (Some (8)))]); ((TAtom "L102"), [(2%N, (TApp "tmp" [(TAtom "v105")]), (0), (Some 8), true, false, (Some (TAtom "v90")), (Some (8))); (5%N, (TApp "tmp" [(TAtom "v112")]), (0), (Some 8), false, true, (Some (TAtom "v90")), (Some (8))); (10%N, (TApp "tmp" [(TAtom "v118")]), (0), (Some 8), true, false, (Some (TAtom "v118")), (Some (0))); (12%N, (TApp "tmp" [(TAtom "v116")]), (0), (Some 8), true, false, (Some (TAtom "v90")), None)]); ((TAtom "L130"), [(2%N, (TApp "tmp" [(TAtom "v132")]), (0), (Some 8), true, false, (Some (TAtom "v90")), None); (5%N, (TApp "tmp" [(TAtom "v136")]), (0), (Some 8), true, false, (Some (TAtom "v90")), None); (8%N, (TApp "tmp" [(TAtom "v140")]), (0), (Some 4), true, false, (Some (TAtom "v140")), (Some (0)))]); ((TAtom "L145"), [(1%N, (TApp "tmp" [(TAtom "v140")]), (0), (Some 4), true, true, (Some (TAtom "v140")), (Some (0)))]); ((TAtom "L146"), []); ((TAtom "L157"), []); ((TAtom "L152"), [(4%N, (TApp "tmp" [(TAtom "v172")]), (0), (Some 4), true, true, (Some (TAtom "v172")), (Some (0)))]); ((TAtom "L181"), []); ((TAtom "L182"), []); ((TAtom "L186"), []); ((TAtom "L196"), [(2%N, (TApp "tmp" [(TAtom "v198")]), (0), (Some 8), true, false, (Some (TAtom "v90")), None); (5%N, (TApp "tmp" [(TAtom "v202")]), (0), (Some 4), true, false, (Some (TAtom "v202")), (Some (0)))]); ((TAtom "L207"), [(1%N, (TApp "tmp" [(TAtom "v202")]), (0), (Some 4), true, true, (Some (TAtom "v202")), (Some (0)))]); ((TAtom "L208"), []); ((TAtom "L219"), []); ((TAtom "L214"), [(4%N, (TApp "tmp" [(TAtom "v232")]), (0), (Some 4), true, true, (Some (TAtom "v232")), (Some (0)))]); ((TAtom "L241"), []); ((TAtom "L242"), []); ((TAtom "L246"), []); ((TAtom "L256"), [(1%N, (TApp "tmp" [(TAtom "v116")]), (0), (Some 8), false, true, (Some (TAtom "v90")), None); (4%N, (TApp "tmp" [(TAtom "v259")]), (0), (Some 8), true, false, (Some (TAtom "v90")), None); (7%N, (TApp "tmp" [(TAtom "v263")]), (0), (Some 8), true, false, (Some (TAtom "v90")), None); (10%N, (TApp "tmp" [(TAtom "v267")]), (0), (Some 4), true, false, (Some (TAtom "v267")), (Some (0)))]); ((TAtom "L272"), [(1%N, (TApp "tmp" [(TAtom "v267")]), (0), (Some 4), true, true, (Some (TAtom "v267")), (Some (0)))]); ((TAtom "L273"), []); ((TAtom "L284"), []); ((TAtom "L279"), [(4%N, (TApp "tmp" [(TAtom "v299")]), (0), (Some 4), true, true, (Some (TAtom "v299")), (Some (0)))]); ((TAtom "L308"), []); ((TAtom "L309"), []); ((TAtom "L313"), []); ((TAtom "L325"), []); ((TAtom "L328"), []); ((TAtom "L330"), []); ((TAtom "L326"), []); ((TAtom "L332"), []); ((TAtom "L334"), []); ((TAtom "L123"), [(2%N, (TApp "tmp" [(TAtom "v341")]), (0), (Some 8), true, false, (Some (TAtom "v341")), (Some (0)))]); ((TAtom "L103"), [(1%N, (TApp "tmp" [(TAtom "v90")]), (0), (Some 8), true, false, (Some (TAtom "v90")), (Some (0))); (3%N, (TApp "tmp" [(TAtom "v2")]), (0), (Some 8), false, true, (Some (TAtom "v2")), (Some (0))); (5%N, (TApp "tmp" [(TAtom "v2")]), (0), (Some 8), true, false, (Some (TAtom "v2")), (Some (0)))]); ((TAtom "L350"), []); ((TAtom "L365"), [(1%N, (TApp "tmp" [(TAtom "v360")]), (0), (Some 4), true, true, (Some (TAtom "v360")), (Some (0)))]); ((TAtom "L366"), []); ((TAtom "L377"), []); ((TAtom "L372"), []); ((TAtom "L388"), []); ((TAtom "L390"), [])].


End fn___run_exit_handlers.

Module fn___GI_exit.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_16, 147%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_16, 150%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "status"); ((TAtom "v2"), "status")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [])].


End fn___GI_exit.

Module fn___GI___call_tls_dtors.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_15, 80%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_15, 80%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [])].


End fn___GI___call_tls_dtors.

Module fn___GI___libc_cleanup_push_defer.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_23, 22%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_23, 25%N)); ((TAtom "L22"), (file_23, 29%N)); ((TAtom "L35"), (file_23, 39%N)); ((TAtom "L36"), (file_23, 29%N)); ((TAtom "L15"), (file_23, 29%N)); ((TAtom "L41"), (file_23, 44%N)); ((TAtom "L42"), (file_23, 44%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "pr.1"), "cancelhandling"); ((TAtom "pr.2"), "cancelhandling"); ((TAtom "pr.3"), "cancelhandling"); ((TAtom "v0"), "buffer"); ((TAtom "v10"), "self"); ((TAtom "v12"), "cancelhandling"); ((TAtom "v16"), "cancelhandling"); ((TAtom "v25"), "cancelhandling"); ((TAtom "v28"), "newval"); ((TAtom "v29"), "self"); ((TAtom "v3"), "self"); ((TAtom "v31"), "newval"); ((TAtom "v32"), "cancelhandling"); ((TAtom "v33"), "cancelhandling"); ((TAtom "v38"), "buffer"); ((TAtom "v4"), "buffer"); ((TAtom "v43"), "cancelhandling"); ((TAtom "v47"), "self"); ((TAtom "v49"), "buffer"); ((TAtom "v6"), "self")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L22")].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "L22"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v3")]); ((TAtom "L35"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "pr.2"); (TAtom "v0"); (TAtom "v3"); (TAtom "v33")]); ((TAtom "L36"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "pr.2"); (TAtom "v0"); (TAtom "v3"); (TAtom "v33")]); ((TAtom "L15"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v3")]); ((TAtom "L41"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v3"); (TAtom "v39")]); ((TAtom "L42"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v3"); (TAtom "v39")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v12"); (TAtom "v3")]); ((TAtom "L22"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "pr.2"); (TAtom "v0"); (TAtom "v3"); (TAtom "v33")]); ((TAtom "L35"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "pr.2"); (TAtom "v0"); (TAtom "v3"); (TAtom "v33")]); ((TAtom "L36"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v3")]); ((TAtom "L15"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v3"); (TAtom "v39")]); ((TAtom "L41"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v3"); (TAtom "v39")]); ((TAtom "L42"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [(4%N, (TApp "tmp" [(TAtom "v7")]), (0), (Some 8), true, false, (Some (TAtom "v3")), (Some (776))); (6%N, (TApp "tmp" [(TAtom "v5")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (24))); (9%N, (TApp "tmp" [(TAtom "v11")]), (0), (Some 4), true, false, (Some (TAtom "v3")), (Some (792)))]); ((TAtom "L22"), [(3%N, (TApp "tmp" [(TAtom "v30")]), (0), (Some 4), true, true, (Some (TAtom "v3")), (Some (792)))]); ((TAtom "L35"), []); ((TAtom "L36"), []); ((TAtom "L15"), []); ((TAtom "L41"), []); ((TAtom "L42"), [(1%N, (TApp "tmp" [(TAtom "v39")]), (0), (Some 4), false, true, (Some (TAtom "v0")), (Some (16))); (4%N, (TApp "tmp" [(TAtom "v48")]), (0), (Some 8), false, true, (Some (TAtom "v3")), (Some (776)))])].


End fn___GI___libc_cleanup_push_defer.

Module fn___GI___libc_cleanup_pop_restore.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_23, 52%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_23, 55%N)); ((TAtom "L20"), (file_23, 60%N)); ((TAtom "L21"), (file_23, 60%N)); ((TAtom "L29"), (file_23, 59%N)); ((TAtom "L41"), (file_23, 68%N)); ((TAtom "L42"), (file_23, 59%N)); ((TAtom "iw_1.start"), (file_0, 463%N)); ((TAtom "L44"), (file_23, 72%N)); ((TAtom "iw_2.L12"), (file_2, 256%N)); ((TAtom "iw_2.L13"), (file_2, 268%N)); ((TAtom "iw_2.L37"), (file_2, 268%N)); ((TAtom "iw_2.L38"), (file_2, 256%N)); ((TAtom "iw_2.L14"), (file_2, 271%N)); ((TAtom "L15"), (file_23, 52%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "value"); ((TAtom "iw_1.v2"), "value"); ((TAtom "iw_2.pr.1"), "oldval"); ((TAtom "iw_2.pr.2"), "oldval"); ((TAtom "iw_2.v0"), "result"); ((TAtom "iw_2.v10"), "oldval"); ((TAtom "iw_2.v15"), "oldval"); ((TAtom "iw_2.v19"), "newval"); ((TAtom "iw_2.v20"), "newval"); ((TAtom "iw_2.v23"), "newval"); ((TAtom "iw_2.v27"), "oldval"); ((TAtom "iw_2.v28"), "newval"); ((TAtom "iw_2.v3"), "self"); ((TAtom "iw_2.v31"), "self"); ((TAtom "iw_2.v33"), "newval"); ((TAtom "iw_2.v34"), "oldval"); ((TAtom "iw_2.v35"), "oldval"); ((TAtom "iw_2.v4"), "self"); ((TAtom "iw_2.v40"), "self"); ((TAtom "iw_2.v6"), "result"); ((TAtom "iw_2.v8"), "self"); ((TAtom "pr.1"), "cancelhandling"); ((TAtom "pr.2"), "cancelhandling"); ((TAtom "v0"), "buffer"); ((TAtom "v10"), "self"); ((TAtom "v12"), "cancelhandling"); ((TAtom "v16"), "buffer"); ((TAtom "v22"), "cancelhandling"); ((TAtom "v3"), "self"); ((TAtom "v32"), "cancelhandling"); ((TAtom "v34"), "newval"); ((TAtom "v35"), "self"); ((TAtom "v37"), "newval"); ((TAtom "v38"), "cancelhandling"); ((TAtom "v39"), "cancelhandling"); ((TAtom "v4"), "self"); ((TAtom "v47"), "cancelhandling"); ((TAtom "v6"), "buffer")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L29"); (TAtom "iw_2.L12")].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "L20"), [(TAtom "chk1"); (TAtom "v12"); (TAtom "v3")]); ((TAtom "L21"), [(TAtom "chk1"); (TAtom "v12"); (TAtom "v3")]); ((TAtom "L29"), [(TAtom "chk1"); (TAtom "v3")]); ((TAtom "L41"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "v3"); (TAtom "v39")]); ((TAtom "L42"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "v3"); (TAtom "v39")]); ((TAtom "iw_1.start"), [(TAtom "pr.2")]); ((TAtom "L44"), []); ((TAtom "iw_2.L12"), [(TAtom "chk5"); (TAtom "iw_2.v3")]); ((TAtom "iw_2.L13"), [(TAtom "chk5"); (TAtom "iw_2.pr.1"); (TAtom "iw_2.v23"); (TAtom "iw_2.v3")]); ((TAtom "iw_2.L37"), [(TAtom "chk5"); (TAtom "iw_2.pr.1"); (TAtom "iw_2.v3"); (TAtom "iw_2.v35")]); ((TAtom "iw_2.L38"), [(TAtom "chk5"); (TAtom "iw_2.pr.1"); (TAtom "iw_2.v3"); (TAtom "iw_2.v35")]); ((TAtom "iw_2.L14"), [(TAtom "chk5"); (TAtom "iw_2.v3")]); ((TAtom "L15"), [])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "chk1"); (TAtom "v12"); (TAtom "v3")]); ((TAtom "L20"), [(TAtom "chk1"); (TAtom "v12"); (TAtom "v25"); (TAtom "v3")]); ((TAtom "L21"), [(TAtom "chk1"); (TAtom "v12"); (TAtom "v3")]); ((TAtom "L29"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "v3"); (TAtom "v39")]); ((TAtom "L41"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "v3"); (TAtom "v39")]); ((TAtom "L42"), [(TAtom "chk1"); (TAtom "pr.2"); (TAtom "v3")]); ((TAtom "iw_1.start"), []); ((TAtom "L44"), [(TAtom "chk5"); (TAtom "iw_2.v10"); (TAtom "iw_2.v3")]); ((TAtom "iw_2.L12"), [(TAtom "chk5"); (TAtom "iw_2.pr.1"); (TAtom "iw_2.v23"); (TAtom "iw_2.v3")]); ((TAtom "iw_2.L13"), [(TAtom "chk5"); (TAtom "iw_2.pr.1"); (TAtom "iw_2.v3"); (TAtom "iw_2.v35")]); ((TAtom "iw_2.L37"), [(TAtom "chk5"); (TAtom "iw_2.pr.1"); (TAtom "iw_2.v3"); (TAtom "iw_2.v35")]); ((TAtom "iw_2.L38"), [(TAtom "chk5"); (TAtom "iw_2.pr.2"); (TAtom "iw_2.v3")]); ((TAtom "iw_2.L14"), []); ((TAtom "L15"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [(4%N, (TApp "tmp" [(TAtom "v7")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (24))); (6%N, (TApp "tmp" [(TAtom "v5")]), (0), (Some 8), false, true, (Some (TAtom "v3")), (Some (776))); (9%N, (TApp "tmp" [(TAtom "v11")]), (0), (Some 4), true, false, (Some (TAtom "v3")), (Some (792))); (12%N, (TApp "tmp" [(TAtom "v17")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (16)))]); ((TAtom "L20"), []); ((TAtom "L21"), []); ((TAtom "L29"), [(3%N, (TApp "tmp" [(TAtom "v36")]), (0), (Some 4), true, true, (Some (TAtom "v3")), (Some (792)))]); ((TAtom "L41"), []); ((TAtom "L42"), []); ((TAtom "iw_1.start"), []); ((TAtom "L44"), [(4%N, (TApp "tmp" [(TAtom "iw_2.v5")]), (0), (Some 8), false, true, (Some (TAtom "iw_2.v3")), (Some (1608))); (7%N, (TApp "tmp" [(TAtom "iw_2.v9")]), (0), (Some 4), true, false, (Some (TAtom "iw_2.v3")), (Some (792)))]); ((TAtom "iw_2.L12"), []); ((TAtom "iw_2.L13"), [(2%N, (TApp "tmp" [(TAtom "iw_2.v32")]), (0), (Some 4), true, true, (Some (TAtom "iw_2.v3")), (Some (792)))]); ((TAtom "iw_2.L37"), []); ((TAtom "iw_2.L38"), []); ((TAtom "iw_2.L14"), [(2%N, (TApp "tmp" [(TAtom "iw_2.v41")]), (0), (Some 8), true, false, (Some (TAtom "iw_2.v3")), (Some (784)))]); ((TAtom "L15"), [])].


End fn___GI___libc_cleanup_pop_restore.

Module fn___gnu_dev_major.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_24, 28%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_24, 28%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "__dev"); ((TAtom "v11"), "__major"); ((TAtom "v12"), "__major"); ((TAtom "v3"), "__dev"); ((TAtom "v5"), "__major"); ((TAtom "v6"), "__major"); ((TAtom "v7"), "__dev")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [])].


End fn___gnu_dev_major.

Module fn___strlen.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_29, 31%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_29, 35%N)); ((TAtom "iw_3.start"), (file_1, 193%N)); ((TAtom "iw_3.iw_1.iw_1.L3"), (file_1, 193%N)); ((TAtom "iw_3.iw_1.iw_1.L4"), (file_1, 193%N)); ((TAtom "L28"), (file_29, 36%N)); ((TAtom "iw_5.start"), (file_1, 193%N)); ((TAtom "iw_5.iw_3.iw_1.iw_1.L3"), (file_1, 193%N)); ((TAtom "iw_5.iw_3.iw_1.iw_1.L4"), (file_1, 193%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.iw_1.v0"), "c_in"); ((TAtom "iw_1.iw_1.v5"), "c_in"); ((TAtom "iw_1.v0"), "x"); ((TAtom "iw_1.v11"), "m"); ((TAtom "iw_1.v3"), "m"); ((TAtom "iw_1.v4"), "x"); ((TAtom "iw_1.v5"), "m"); ((TAtom "iw_1.v7"), "m"); ((TAtom "iw_1.v9"), "x"); ((TAtom "iw_2.v0"), "word"); ((TAtom "iw_2.v14"), "word"); ((TAtom "iw_2.v15"), "s"); ((TAtom "iw_2.v2"), "s"); ((TAtom "iw_2.v8"), "word"); ((TAtom "iw_2.v9"), "s"); ((TAtom "iw_3.iw_1.iw_1.v0"), "__x"); ((TAtom "iw_3.iw_1.iw_1.v5"), "__x"); ((TAtom "iw_3.iw_1.iw_1.v7"), "__x"); ((TAtom "iw_3.iw_1.iw_2.v0"), "__x"); ((TAtom "iw_3.iw_1.iw_2.v5"), "__x"); ((TAtom "iw_3.iw_1.iw_2.v7"), "__x"); ((TAtom "iw_3.iw_1.iw_3.v0"), "__x"); ((TAtom "iw_3.iw_1.iw_3.v5"), "__x"); ((TAtom "iw_3.iw_1.iw_3.v7"), "__x"); ((TAtom "iw_3.iw_1.iw_4.v0"), "__x"); ((TAtom "iw_3.iw_1.iw_4.v5"), "__x"); ((TAtom "iw_3.iw_1.iw_4.v7"), "__x"); ((TAtom "iw_3.iw_1.v0"), "c"); ((TAtom "iw_3.iw_1.v12"), "c"); ((TAtom "iw_3.iw_1.v18"), "c"); ((TAtom "iw_3.iw_1.v21"), "c"); ((TAtom "iw_3.iw_1.v6"), "c"); ((TAtom "iw_3.iw_2.iw_1.v0"), "__x"); ((TAtom "iw_3.iw_2.iw_1.v5"), "__x"); ((TAtom "iw_3.iw_2.iw_1.v7"), "__x"); ((TAtom "iw_3.iw_2.v0"), "c"); ((TAtom "iw_3.iw_2.v2"), "c"); ((TAtom "iw_3.pr.1"), "r"); ((TAtom "iw_3.v0"), "c"); ((TAtom "iw_3.v10"), "r"); ((TAtom "iw_3.v11"), "r"); ((TAtom "iw_3.v7"), "c"); ((TAtom "iw_3.v8"), "r"); ((TAtom "iw_3.v9"), "c"); ((TAtom "iw_4.iw_1.iw_1.v0"), "c_in"); ((TAtom "iw_4.iw_1.iw_1.v5"), "c_in"); ((TAtom "iw_4.iw_1.iw_2.v0"), "c_in"); ((TAtom "iw_4.iw_1.iw_2.v5"), "c_in"); ((TAtom "iw_4.iw_1.v0"), "x"); ((TAtom "iw_4.iw_1.v12"), "msb"); ((TAtom "iw_4.iw_1.v3"), "lsb"); ((TAtom "iw_4.iw_1.v5"), "msb"); ((TAtom "iw_4.iw_1.v6"), "x"); ((TAtom "iw_4.iw_1.v7"), "lsb"); ((TAtom "iw_4.iw_1.v9"), "x"); ((TAtom "iw_4.v0"), "x"); ((TAtom "iw_4.v2"), "x"); ((TAtom "iw_5.iw_1.iw_1.v0"), "c_in"); ((TAtom "iw_5.iw_1.iw_1.v5"), "c_in"); ((TAtom "iw_5.iw_1.iw_2.v0"), "c_in"); ((TAtom "iw_5.iw_1.iw_2.v5"), "c_in"); ((TAtom "iw_5.iw_1.v0"), "x"); ((TAtom "iw_5.iw_1.v12"), "msb"); ((TAtom "iw_5.iw_1.v3"), "lsb"); ((TAtom "iw_5.iw_1.v5"), "msb"); ((TAtom "iw_5.iw_1.v6"), "x"); ((TAtom "iw_5.iw_1.v7"), "lsb"); ((TAtom "iw_5.iw_1.v9"), "x"); ((TAtom "iw_5.iw_2.iw_1.v0"), "c_in"); ((TAtom "iw_5.iw_2.iw_1.v5"), "c_in"); ((TAtom "iw_5.iw_2.v0"), "x"); ((TAtom "iw_5.iw_2.v11"), "m"); ((TAtom "iw_5.iw_2.v3"), "m"); ((TAtom "iw_5.iw_2.v4"), "x"); ((TAtom "iw_5.iw_2.v5"), "m"); ((TAtom "iw_5.iw_2.v7"), "m"); ((TAtom "iw_5.iw_2.v9"), "x"); ((TAtom "iw_5.iw_3.iw_1.iw_1.v0"), "__x"); ((TAtom "iw_5.iw_3.iw_1.iw_1.v5"), "__x"); ((TAtom "iw_5.iw_3.iw_1.iw_1.v7"), "__x"); ((TAtom "iw_5.iw_3.iw_1.iw_2.v0"), "__x"); ((TAtom "iw_5.iw_3.iw_1.iw_2.v5"), "__x"); ((TAtom "iw_5.iw_3.iw_1.iw_2.v7"), "__x"); ((TAtom "iw_5.iw_3.iw_1.iw_3.v0"), "__x"); ((TAtom "iw_5.iw_3.iw_1.iw_3.v5"), "__x"); ((TAtom "iw_5.iw_3.iw_1.iw_3.v7"), "__x"); ((TAtom "iw_5.iw_3.iw_1.iw_4.v0"), "__x"); ((TAtom "iw_5.iw_3.iw_1.iw_4.v5"), "__x"); ((TAtom "iw_5.iw_3.iw_1.iw_4.v7"), "__x"); ((TAtom "iw_5.iw_3.iw_1.v0"), "c"); ((TAtom "iw_5.iw_3.iw_1.v12"), "c"); ((TAtom "iw_5.iw_3.iw_1.v18"), "c"); ((TAtom "iw_5.iw_3.iw_1.v21"), "c"); ((TAtom "iw_5.iw_3.iw_1.v6"), "c"); ((TAtom "iw_5.iw_3.iw_2.iw_1.v0"), "__x"); ((TAtom "iw_5.iw_3.iw_2.iw_1.v5"), "__x"); ((TAtom "iw_5.iw_3.iw_2.iw_1.v7"), "__x"); ((TAtom "iw_5.iw_3.iw_2.v0"), "c"); ((TAtom "iw_5.iw_3.iw_2.v2"), "c"); ((TAtom "iw_5.iw_3.pr.1"), "r"); ((TAtom "iw_5.iw_3.v0"), "c"); ((TAtom "iw_5.iw_3.v10"), "r"); ((TAtom "iw_5.iw_3.v11"), "r"); ((TAtom "iw_5.iw_3.v7"), "c"); ((TAtom "iw_5.iw_3.v8"), "r"); ((TAtom "iw_5.iw_3.v9"), "c"); ((TAtom "iw_5.pr.1"), "x"); ((TAtom "iw_5.v0"), "x"); ((TAtom "iw_5.v10"), "x"); ((TAtom "iw_5.v6"), "x"); ((TAtom "iw_5.v7"), "x"); ((TAtom "iw_5.v8"), "x"); ((TAtom "iw_5.v9"), "x"); ((TAtom "pr.1"), "word_ptr"); ((TAtom "v0"), "str"); ((TAtom "v10"), "word_ptr"); ((TAtom "v12"), "word_ptr"); ((TAtom "v13"), "word"); ((TAtom "v15"), "word"); ((TAtom "v17"), "s_int"); ((TAtom "v18"), "mask"); ((TAtom "v22"), "mask"); ((TAtom "v24"), "mask"); ((TAtom "v3"), "str"); ((TAtom "v31"), "word_ptr"); ((TAtom "v32"), "word_ptr"); ((TAtom "v33"), "word"); ((TAtom "v34"), "word"); ((TAtom "v38"), "word_ptr"); ((TAtom "v39"), "word"); ((TAtom "v4"), "s_int"); ((TAtom "v43"), "str"); ((TAtom "v6"), "str")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L28")].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "iw_3.start"), [(TAtom "iw_2.v12")]); ((TAtom "iw_3.iw_1.iw_1.L3"), [(TAtom "iw_2.v12")]); ((TAtom "iw_3.iw_1.iw_1.L4"), []); ((TAtom "L28"), [(TAtom "v4")]); ((TAtom "iw_5.start"), [(TAtom "iw_4.iw_1.v13"); (TAtom "v32"); (TAtom "v37"); (TAtom "v4")]); ((TAtom "iw_5.iw_3.iw_1.iw_1.L3"), [(TAtom "iw_4.iw_1.v13"); (TAtom "v32"); (TAtom "v4")]); ((TAtom "iw_5.iw_3.iw_1.iw_1.L4"), [(TAtom "v32"); (TAtom "v4")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "iw_2.v12"); (TAtom "v10"); (TAtom "v4")]); ((TAtom "iw_3.start"), [(TAtom "iw_2.v12")]); ((TAtom "iw_3.iw_1.iw_1.L3"), [(TAtom "iw_3.iw_1.iw_1.v22")]); ((TAtom "iw_3.iw_1.iw_1.L4"), []); ((TAtom "L28"), [(TAtom "iw_4.iw_1.v13"); (TAtom "v32"); (TAtom "v37"); (TAtom "v4")]); ((TAtom "iw_5.start"), [(TAtom "iw_4.iw_1.v13"); (TAtom "v32"); (TAtom "v4")]); ((TAtom "iw_5.iw_3.iw_1.iw_1.L3"), [(TAtom "iw_5.iw_3.iw_1.iw_1.v22"); (TAtom "v32"); (TAtom "v4")]); ((TAtom "iw_5.iw_3.iw_1.iw_1.L4"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [(5%N, (TApp "tmp" [(TAtom "v10")]), (0), (Some 8), true, false, (Some (TAtom "v0")), None)]); ((TAtom "iw_3.start"), []); ((TAtom "iw_3.iw_1.iw_1.L3"), []); ((TAtom "iw_3.iw_1.iw_1.L4"), []); ((TAtom "L28"), [(2%N, (TApp "tmp" [(TAtom "v32")]), (0), (Some 8), true, false, (Some (TAtom "pr.1")), (Some (8)))]); ((TAtom "iw_5.start"), []); ((TAtom "iw_5.iw_3.iw_1.iw_1.L3"), []); ((TAtom "iw_5.iw_3.iw_1.iw_1.L4"), [])].


End fn___strlen.

Module fn___GI___mempcpy.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_27, 32%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_27, 35%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "dest"); ((TAtom "v10"), "len"); ((TAtom "v2"), "src"); ((TAtom "v4"), "len"); ((TAtom "v6"), "dest"); ((TAtom "v7"), "src"); ((TAtom "v8"), "len")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [])].


End fn___GI___mempcpy.

Module fn___GI_memcpy.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_26, 28%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_26, 37%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "dstpp"); ((TAtom "v2"), "srcpp"); ((TAtom "v4"), "len"); ((TAtom "v6"), "dstpp"); ((TAtom "v7"), "srcpp"); ((TAtom "v8"), "len"); ((TAtom "v9"), "dstpp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [])].


End fn___GI_memcpy.

End HiAtexitSrc07.
