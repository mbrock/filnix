(** These tables connect checked function bodies to C declarations and source lines.
    Names and locations support annotations and diagnostic messages, not soundness premises.
    Natural-loop headers provide optional cuts for symbolic execution; any cut list is sound.
    Computation checks that every recorded block label belongs to the decoded function.
    The code generator reproduces this file from the capture; do not edit it. *)

From Stdlib Require Import String List Bool NArith.
From Glibc Require Import CodePrelude.
Import ListNotations.
Open Scope string_scope.


From Glibc Require Import HiAtexitSrcFiles.
Import HiAtexitSrcFiles.
Module HiAtexitSrc03.

Module fn___GI___underflow.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_20, 293%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_20, 296%N)); ((TAtom "L20"), (file_20, 296%N)); ((TAtom "L22"), (file_20, 296%N)); ((TAtom "L2"), (file_20, 297%N)); ((TAtom "L4"), (file_20, 299%N)); ((TAtom "L69"), (file_20, 300%N)); ((TAtom "L79"), (file_20, 300%N)); ((TAtom "L81"), (file_20, 300%N)); ((TAtom "L62"), (file_20, 301%N)); ((TAtom "L113"), (file_20, 302%N)); ((TAtom "L119"), (file_20, 303%N)); ((TAtom "L115"), (file_20, 304%N)); ((TAtom "L128"), (file_20, 305%N)); ((TAtom "L130"), (file_20, 306%N)); ((TAtom "L145"), (file_20, 308%N)); ((TAtom "L152"), (file_20, 310%N)); ((TAtom "L147"), (file_20, 312%N)); ((TAtom "L169"), (file_20, 314%N)); ((TAtom "L178"), (file_20, 315%N)); ((TAtom "L170"), (file_20, 317%N)); ((TAtom "L188"), (file_20, 318%N)); ((TAtom "L171"), (file_20, 319%N)); ((TAtom "iw_1.L10"), (file_10, 1049%N)); ((TAtom "iw_1.join"), (file_20, 319%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "vtable"); ((TAtom "iw_1.v13"), "offset"); ((TAtom "iw_1.v18"), "vtable"); ((TAtom "iw_1.v3"), "vtable"); ((TAtom "iw_1.v4"), "ptr"); ((TAtom "iw_1.v6"), "ptr"); ((TAtom "iw_1.v9"), "offset"); ((TAtom "pr.1"), "__result"); ((TAtom "pr.2"), "__result"); ((TAtom "pr.3"), "__result"); ((TAtom "pr.4"), "__result"); ((TAtom "v0"), "fp"); ((TAtom "v105"), "fp"); ((TAtom "v108"), "__result"); ((TAtom "v109"), "fp"); ((TAtom "v110"), "__result"); ((TAtom "v111"), "__result"); ((TAtom "v112"), "__result"); ((TAtom "v116"), "fp"); ((TAtom "v122"), "fp"); ((TAtom "v13"), "__result"); ((TAtom "v131"), "fp"); ((TAtom "v134"), "fp"); ((TAtom "v140"), "fp"); ((TAtom "v148"), "fp"); ((TAtom "v151"), "fp"); ((TAtom "v155"), "fp"); ((TAtom "v158"), "fp"); ((TAtom "v164"), "fp"); ((TAtom "v172"), "fp"); ((TAtom "v181"), "fp"); ((TAtom "v182"), "fp"); ((TAtom "v191"), "fp"); ((TAtom "v197"), "fp"); ((TAtom "v198"), "fp"); ((TAtom "v204"), "fp"); ((TAtom "v23"), "fp"); ((TAtom "v27"), "fp"); ((TAtom "v30"), "fp"); ((TAtom "v32"), "__result"); ((TAtom "v46"), "fp"); ((TAtom "v49"), "__result"); ((TAtom "v50"), "fp"); ((TAtom "v51"), "__result"); ((TAtom "v52"), "__result"); ((TAtom "v53"), "__result"); ((TAtom "v63"), "fp"); ((TAtom "v68"), "__result"); ((TAtom "v72"), "__result"); ((TAtom "v82"), "fp"); ((TAtom "v86"), "fp"); ((TAtom "v89"), "fp"); ((TAtom "v9"), "__result"); ((TAtom "v91"), "__result")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

End fn___GI___underflow.

Module fn___GI__IO_setb.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_20, 353%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_20, 356%N)); ((TAtom "L16"), (file_20, 356%N)); ((TAtom "L17"), (file_20, 356%N)); ((TAtom "L8"), (file_20, 357%N)); ((TAtom "L10"), (file_20, 358%N)); ((TAtom "L33"), (file_20, 361%N)); ((TAtom "L34"), (file_20, 363%N)); ((TAtom "L35"), (file_20, 353%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "f"); ((TAtom "v11"), "f"); ((TAtom "v18"), "f"); ((TAtom "v2"), "b"); ((TAtom "v24"), "f"); ((TAtom "v27"), "f"); ((TAtom "v29"), "b"); ((TAtom "v30"), "f"); ((TAtom "v32"), "eb"); ((TAtom "v36"), "a"); ((TAtom "v37"), "f"); ((TAtom "v4"), "eb"); ((TAtom "v41"), "f"); ((TAtom "v6"), "a")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

End fn___GI__IO_setb.

Module fn___GI__IO_doallocbuf.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_20, 367%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_20, 370%N)); ((TAtom "L2"), (file_20, 371%N)); ((TAtom "L4"), (file_20, 372%N)); ((TAtom "L18"), (file_20, 372%N)); ((TAtom "L19"), (file_20, 372%N)); ((TAtom "L11"), (file_20, 373%N)); ((TAtom "iw_1.L10"), (file_10, 1049%N)); ((TAtom "iw_1.join"), (file_20, 373%N)); ((TAtom "L26"), (file_20, 374%N)); ((TAtom "L13"), (file_20, 375%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "vtable"); ((TAtom "iw_1.v13"), "offset"); ((TAtom "iw_1.v18"), "vtable"); ((TAtom "iw_1.v3"), "vtable"); ((TAtom "iw_1.v4"), "ptr"); ((TAtom "iw_1.v6"), "ptr"); ((TAtom "iw_1.v9"), "offset"); ((TAtom "v0"), "fp"); ((TAtom "v14"), "fp"); ((TAtom "v20"), "fp"); ((TAtom "v29"), "fp"); ((TAtom "v35"), "fp"); ((TAtom "v40"), "fp"); ((TAtom "v41"), "fp"); ((TAtom "v43"), "fp"); ((TAtom "v5"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

End fn___GI__IO_doallocbuf.

Module fn___GI__IO_default_uflow.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_20, 385%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_20, 388%N)); ((TAtom "iw_1.L10"), (file_10, 1049%N)); ((TAtom "iw_1.join"), (file_20, 388%N)); ((TAtom "L11"), (file_20, 390%N)); ((TAtom "L13"), (file_20, 391%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "vtable"); ((TAtom "iw_1.v13"), "offset"); ((TAtom "iw_1.v18"), "vtable"); ((TAtom "iw_1.v3"), "vtable"); ((TAtom "iw_1.v4"), "ptr"); ((TAtom "iw_1.v6"), "ptr"); ((TAtom "iw_1.v9"), "offset"); ((TAtom "v0"), "fp"); ((TAtom "v10"), "ch"); ((TAtom "v14"), "ch"); ((TAtom "v19"), "fp"); ((TAtom "v3"), "fp"); ((TAtom "v9"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

End fn___GI__IO_default_uflow.

Module fn___GI__IO_default_xsputn.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_20, 395%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_20, 400%N)); ((TAtom "L10"), (file_20, 401%N)); ((TAtom "L16"), (file_20, 399%N)); ((TAtom "L20"), (file_20, 407%N)); ((TAtom "L43"), (file_20, 408%N)); ((TAtom "L44"), (file_20, 407%N)); ((TAtom "L49"), (file_20, 412%N)); ((TAtom "L50"), (file_20, 415%N)); ((TAtom "L65"), (file_20, 417%N)); ((TAtom "L76"), (file_20, 418%N)); ((TAtom "L77"), (file_20, 420%N)); ((TAtom "L79"), (file_20, 421%N)); ((TAtom "L51"), (file_20, 398%N)); ((TAtom "L22"), (file_20, 399%N)); ((TAtom "L99"), (file_20, 425%N)); ((TAtom "iw_1.L10"), (file_10, 1049%N)); ((TAtom "iw_1.join"), (file_20, 425%N)); ((TAtom "L100"), (file_20, 425%N)); ((TAtom "L96"), (file_20, 427%N)); ((TAtom "L19"), (file_20, 429%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "vtable"); ((TAtom "iw_1.v13"), "offset"); ((TAtom "iw_1.v18"), "vtable"); ((TAtom "iw_1.v3"), "vtable"); ((TAtom "iw_1.v4"), "ptr"); ((TAtom "iw_1.v6"), "ptr"); ((TAtom "iw_1.v9"), "offset"); ((TAtom "pr.1"), "s"); ((TAtom "pr.10"), "p"); ((TAtom "pr.11"), "i"); ((TAtom "pr.2"), "s"); ((TAtom "pr.3"), "s"); ((TAtom "pr.4"), "s"); ((TAtom "pr.5"), "s"); ((TAtom "pr.6"), "s"); ((TAtom "pr.7"), "more"); ((TAtom "pr.8"), "more"); ((TAtom "pr.9"), "count"); ((TAtom "v0"), "f"); ((TAtom "v101"), "f"); ((TAtom "v107"), "f"); ((TAtom "v108"), "s"); ((TAtom "v109"), "s"); ((TAtom "v118"), "more"); ((TAtom "v119"), "more"); ((TAtom "v120"), "n"); ((TAtom "v121"), "more"); ((TAtom "v13"), "more"); ((TAtom "v2"), "data"); ((TAtom "v23"), "f"); ((TAtom "v26"), "f"); ((TAtom "v33"), "f"); ((TAtom "v36"), "f"); ((TAtom "v4"), "n"); ((TAtom "v41"), "count"); ((TAtom "v45"), "count"); ((TAtom "v46"), "more"); ((TAtom "v48"), "more"); ((TAtom "v52"), "count"); ((TAtom "v54"), "f"); ((TAtom "v56"), "f"); ((TAtom "v59"), "s"); ((TAtom "v60"), "count"); ((TAtom "v62"), "s"); ((TAtom "v63"), "count"); ((TAtom "v64"), "s"); ((TAtom "v68"), "count"); ((TAtom "v7"), "data"); ((TAtom "v71"), "f"); ((TAtom "v73"), "p"); ((TAtom "v75"), "count"); ((TAtom "v80"), "i"); ((TAtom "v81"), "i"); ((TAtom "v83"), "p"); ((TAtom "v84"), "p"); ((TAtom "v85"), "s"); ((TAtom "v86"), "s"); ((TAtom "v88"), "f"); ((TAtom "v9"), "n"); ((TAtom "v90"), "p"); ((TAtom "v91"), "more"); ((TAtom "v92"), "count"); ((TAtom "v93"), "more"); ((TAtom "v97"), "more")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L16"); (TAtom "L76")].

End fn___GI__IO_default_xsputn.

Module fn___GI__IO_default_xsgetn.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_20, 441%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_20, 446%N)); ((TAtom "L10"), (file_20, 445%N)); ((TAtom "L14"), (file_20, 451%N)); ((TAtom "L37"), (file_20, 452%N)); ((TAtom "L38"), (file_20, 451%N)); ((TAtom "L43"), (file_20, 456%N)); ((TAtom "L44"), (file_20, 459%N)); ((TAtom "L59"), (file_20, 461%N)); ((TAtom "L70"), (file_20, 462%N)); ((TAtom "L71"), (file_20, 464%N)); ((TAtom "L72"), (file_20, 465%N)); ((TAtom "L45"), (file_20, 445%N)); ((TAtom "L16"), (file_20, 445%N)); ((TAtom "L92"), (file_20, 469%N)); ((TAtom "L93"), (file_20, 469%N)); ((TAtom "L13"), (file_20, 472%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "pr.1"), "more"); ((TAtom "pr.10"), "i"); ((TAtom "pr.2"), "more"); ((TAtom "pr.3"), "s"); ((TAtom "pr.4"), "s"); ((TAtom "pr.5"), "s"); ((TAtom "pr.6"), "s"); ((TAtom "pr.7"), "s"); ((TAtom "pr.8"), "count"); ((TAtom "pr.9"), "p"); ((TAtom "v0"), "fp"); ((TAtom "v101"), "n"); ((TAtom "v102"), "more"); ((TAtom "v17"), "fp"); ((TAtom "v2"), "data"); ((TAtom "v20"), "fp"); ((TAtom "v27"), "fp"); ((TAtom "v30"), "fp"); ((TAtom "v35"), "count"); ((TAtom "v39"), "count"); ((TAtom "v4"), "n"); ((TAtom "v40"), "more"); ((TAtom "v42"), "more"); ((TAtom "v46"), "count"); ((TAtom "v48"), "s"); ((TAtom "v49"), "fp"); ((TAtom "v52"), "count"); ((TAtom "v53"), "s"); ((TAtom "v54"), "fp"); ((TAtom "v57"), "count"); ((TAtom "v62"), "count"); ((TAtom "v65"), "fp"); ((TAtom "v67"), "p"); ((TAtom "v69"), "count"); ((TAtom "v7"), "n"); ((TAtom "v73"), "i"); ((TAtom "v74"), "i"); ((TAtom "v76"), "s"); ((TAtom "v77"), "s"); ((TAtom "v78"), "p"); ((TAtom "v79"), "p"); ((TAtom "v81"), "fp"); ((TAtom "v83"), "p"); ((TAtom "v84"), "more"); ((TAtom "v85"), "count"); ((TAtom "v86"), "more"); ((TAtom "v9"), "data"); ((TAtom "v90"), "more"); ((TAtom "v94"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L10"); (TAtom "L70")].

End fn___GI__IO_default_xsgetn.

Module fn__IO_default_setbuf.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_20, 476%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_20, 479%N)); ((TAtom "iw_1.L10"), (file_10, 1049%N)); ((TAtom "iw_1.join"), (file_20, 479%N)); ((TAtom "L6"), (file_20, 480%N)); ((TAtom "L8"), (file_20, 481%N)); ((TAtom "L27"), (file_20, 481%N)); ((TAtom "L28"), (file_20, 481%N)); ((TAtom "L20"), (file_20, 483%N)); ((TAtom "L21"), (file_20, 488%N)); ((TAtom "L22"), (file_20, 491%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "vtable"); ((TAtom "iw_1.v13"), "offset"); ((TAtom "iw_1.v18"), "vtable"); ((TAtom "iw_1.v3"), "vtable"); ((TAtom "iw_1.v4"), "ptr"); ((TAtom "iw_1.v6"), "ptr"); ((TAtom "iw_1.v9"), "offset"); ((TAtom "v0"), "fp"); ((TAtom "v15"), "fp"); ((TAtom "v2"), "p"); ((TAtom "v23"), "p"); ((TAtom "v29"), "len"); ((TAtom "v33"), "fp"); ((TAtom "v36"), "fp"); ((TAtom "v37"), "fp"); ((TAtom "v39"), "fp"); ((TAtom "v4"), "len"); ((TAtom "v42"), "fp"); ((TAtom "v46"), "fp"); ((TAtom "v47"), "p"); ((TAtom "v48"), "p"); ((TAtom "v49"), "len"); ((TAtom "v51"), "fp"); ((TAtom "v53"), "fp"); ((TAtom "v55"), "fp"); ((TAtom "v57"), "fp"); ((TAtom "v59"), "fp"); ((TAtom "v61"), "fp"); ((TAtom "v63"), "fp"); ((TAtom "v9"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

End fn__IO_default_setbuf.

Module fn__IO_default_seekpos.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_20, 496%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_20, 499%N)); ((TAtom "iw_1.L10"), (file_10, 1049%N)); ((TAtom "iw_1.join"), (file_20, 499%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "vtable"); ((TAtom "iw_1.v13"), "offset"); ((TAtom "iw_1.v18"), "vtable"); ((TAtom "iw_1.v3"), "vtable"); ((TAtom "iw_1.v4"), "ptr"); ((TAtom "iw_1.v6"), "ptr"); ((TAtom "iw_1.v9"), "offset"); ((TAtom "v0"), "fp"); ((TAtom "v12"), "fp"); ((TAtom "v13"), "pos"); ((TAtom "v14"), "mode"); ((TAtom "v2"), "pos"); ((TAtom "v4"), "mode"); ((TAtom "v6"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

End fn__IO_default_seekpos.

Module fn___GI__IO_default_doallocate.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_20, 502%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_20, 507%N)); ((TAtom "L4"), (file_20, 509%N)); ((TAtom "L6"), (file_20, 511%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fp"); ((TAtom "v15"), "fp"); ((TAtom "v16"), "buf"); ((TAtom "v17"), "buf"); ((TAtom "v3"), "buf"); ((TAtom "v7"), "buf")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

End fn___GI__IO_default_doallocate.

Module fn__IO_default_sync.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_20, 617%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_20, 620%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

End fn__IO_default_sync.

Module fn___GI__IO_default_finish.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_20, 626%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_20, 630%N)); ((TAtom "L13"), (file_20, 630%N)); ((TAtom "L14"), (file_20, 630%N)); ((TAtom "L5"), (file_20, 632%N)); ((TAtom "L7"), (file_20, 636%N)); ((TAtom "L31"), (file_20, 629%N)); ((TAtom "L32"), (file_20, 637%N)); ((TAtom "L34"), (file_20, 639%N)); ((TAtom "L43"), (file_20, 640%N)); ((TAtom "L45"), (file_20, 642%N)); ((TAtom "L55"), (file_20, 645%N)); ((TAtom "L56"), (file_20, 626%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "pr.1"), "mark"); ((TAtom "v0"), "fp"); ((TAtom "v15"), "fp"); ((TAtom "v2"), "dummy"); ((TAtom "v21"), "fp"); ((TAtom "v24"), "fp"); ((TAtom "v26"), "fp"); ((TAtom "v28"), "fp"); ((TAtom "v30"), "mark"); ((TAtom "v35"), "mark"); ((TAtom "v39"), "mark"); ((TAtom "v41"), "mark"); ((TAtom "v42"), "mark"); ((TAtom "v46"), "fp"); ((TAtom "v52"), "fp"); ((TAtom "v53"), "fp"); ((TAtom "v57"), "fp"); ((TAtom "v8"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L31")].

End fn___GI__IO_default_finish.

Module fn___GI__IO_adjust_column.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_20, 697%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_20, 700%N)); ((TAtom "L11"), (file_20, 700%N)); ((TAtom "L12"), (file_20, 702%N)); ((TAtom "L19"), (file_20, 703%N)); ((TAtom "L13"), (file_20, 704%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "pr.1"), "ptr"); ((TAtom "v0"), "start"); ((TAtom "v10"), "ptr"); ((TAtom "v14"), "ptr"); ((TAtom "v15"), "line"); ((TAtom "v2"), "line"); ((TAtom "v22"), "ptr"); ((TAtom "v23"), "ptr"); ((TAtom "v26"), "line"); ((TAtom "v27"), "count"); ((TAtom "v30"), "ptr"); ((TAtom "v36"), "start"); ((TAtom "v37"), "count"); ((TAtom "v4"), "count"); ((TAtom "v7"), "line"); ((TAtom "v8"), "count")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L11")].

End fn___GI__IO_adjust_column.

Module fn___GI__IO_flush_all.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_20, 708%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_20, 715%N)); ((TAtom "L24"), (file_20, 716%N)); ((TAtom "L25"), (file_20, 716%N)); ((TAtom "L18"), (file_20, 716%N)); ((TAtom "L19"), (file_20, 716%N)); ((TAtom "L38"), (file_20, 716%N)); ((TAtom "L58"), (file_20, 716%N)); ((TAtom "L59"), (file_20, 716%N)); ((TAtom "L63"), (file_20, 716%N)); ((TAtom "L52"), (file_20, 716%N)); ((TAtom "L39"), (file_20, 716%N)); ((TAtom "L15"), (file_20, 719%N)); ((TAtom "L82"), (file_20, 712%N)); ((TAtom "L83"), (file_20, 721%N)); ((TAtom "L99"), (file_20, 722%N)); ((TAtom "L110"), (file_20, 722%N)); ((TAtom "L111"), (file_20, 722%N)); ((TAtom "L104"), (file_20, 722%N)); ((TAtom "L105"), (file_20, 722%N)); ((TAtom "L130"), (file_20, 722%N)); ((TAtom "L154"), (file_20, 722%N)); ((TAtom "L155"), (file_20, 722%N)); ((TAtom "L159"), (file_20, 722%N)); ((TAtom "L148"), (file_20, 722%N)); ((TAtom "L131"), (file_20, 722%N)); ((TAtom "L94"), (file_20, 726%N)); ((TAtom "L180"), (file_20, 728%N)); ((TAtom "L197"), (file_20, 728%N)); ((TAtom "L198"), (file_20, 728%N)); ((TAtom "L213"), (file_20, 728%N)); ((TAtom "L221"), (file_20, 728%N)); ((TAtom "L211"), (file_20, 728%N)); ((TAtom "L240"), (file_20, 728%N)); ((TAtom "iw_1.L10"), (file_10, 1049%N)); ((TAtom "iw_1.join"), (file_20, 728%N)); ((TAtom "L241"), (file_20, 728%N)); ((TAtom "L191"), (file_20, 728%N)); ((TAtom "L192"), (file_20, 711%N)); ((TAtom "L263"), (file_20, 735%N)); ((TAtom "L269"), (file_20, 735%N)); ((TAtom "L270"), (file_20, 735%N)); ((TAtom "L285"), (file_20, 735%N)); ((TAtom "L293"), (file_20, 735%N)); ((TAtom "L264"), (file_20, 735%N)); ((TAtom "L313"), (file_20, 735%N)); ((TAtom "iw_2.L10"), (file_10, 1049%N)); ((TAtom "iw_2.join"), (file_20, 735%N)); ((TAtom "L314"), (file_20, 735%N)); ((TAtom "L257"), (file_20, 735%N)); ((TAtom "L182"), (file_20, 711%N)); ((TAtom "L334"), (file_20, 744%N)); ((TAtom "L343"), (file_20, 744%N)); ((TAtom "L344"), (file_20, 744%N)); ((TAtom "L337"), (file_20, 744%N)); ((TAtom "L338"), (file_20, 744%N)); ((TAtom "L360"), (file_20, 744%N)); ((TAtom "L381"), (file_20, 744%N)); ((TAtom "L382"), (file_20, 744%N)); ((TAtom "L393"), (file_20, 744%N)); ((TAtom "L361"), (file_20, 744%N)); ((TAtom "L329"), (file_20, 745%N)); ((TAtom "L414"), (file_20, 749%N)); ((TAtom "L423"), (file_20, 749%N)); ((TAtom "L424"), (file_20, 749%N)); ((TAtom "L417"), (file_20, 749%N)); ((TAtom "L418"), (file_20, 749%N)); ((TAtom "L434"), (file_20, 749%N)); ((TAtom "L449"), (file_20, 749%N)); ((TAtom "L450"), (file_20, 749%N)); ((TAtom "L461"), (file_20, 749%N)); ((TAtom "L435"), (file_20, 749%N)); ((TAtom "L476"), (file_20, 750%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "vtable"); ((TAtom "iw_1.v13"), "offset"); ((TAtom "iw_1.v18"), "vtable"); ((TAtom "iw_1.v3"), "vtable"); ((TAtom "iw_1.v4"), "ptr"); ((TAtom "iw_1.v6"), "ptr"); ((TAtom "iw_1.v9"), "offset"); ((TAtom "iw_2.v0"), "vtable"); ((TAtom "iw_2.v13"), "offset"); ((TAtom "iw_2.v18"), "vtable"); ((TAtom "iw_2.v3"), "vtable"); ((TAtom "iw_2.v4"), "ptr"); ((TAtom "iw_2.v6"), "ptr"); ((TAtom "iw_2.v9"), "offset"); ((TAtom "pr.1"), "result"); ((TAtom "pr.2"), "result"); ((TAtom "pr.3"), "result"); ((TAtom "pr.4"), "result"); ((TAtom "pr.5"), "fp"); ((TAtom "pr.6"), "_cleanup_start_doit"); ((TAtom "v10"), "_cleanup_start_doit"); ((TAtom "v103"), "__self"); ((TAtom "v108"), "__libc_single_threaded_internal"); ((TAtom "v11"), "_cleanup_routine"); ((TAtom "v112"), "fp"); ((TAtom "v12"), "_cleanup_start_doit"); ((TAtom "v122"), "fp"); ((TAtom "v125"), "fp"); ((TAtom "v129"), "__self"); ((TAtom "v133"), "fp"); ((TAtom "v138"), "__self"); ((TAtom "v143"), "fp"); ((TAtom "v145"), "__futex"); ((TAtom "v150"), "__futex"); ((TAtom "v151"), "__atg3_old"); ((TAtom "v152"), "__atg3_old"); ((TAtom "v167"), "__futex"); ((TAtom "v168"), "__futex"); ((TAtom "v169"), "fp"); ((TAtom "v17"), "__self"); ((TAtom "v173"), "__self"); ((TAtom "v174"), "fp"); ((TAtom "v183"), "fp"); ((TAtom "v193"), "fp"); ((TAtom "v199"), "fp"); ((TAtom "v202"), "fp"); ((TAtom "v215"), "fp"); ((TAtom "v22"), "__libc_single_threaded_internal"); ((TAtom "v223"), "fp"); ((TAtom "v228"), "fp"); ((TAtom "v242"), "fp"); ((TAtom "v248"), "fp"); ((TAtom "v255"), "result"); ((TAtom "v259"), "fp"); ((TAtom "v265"), "fp"); ((TAtom "v271"), "fp"); ((TAtom "v274"), "fp"); ((TAtom "v287"), "fp"); ((TAtom "v295"), "fp"); ((TAtom "v299"), "fp"); ((TAtom "v315"), "fp"); ((TAtom "v321"), "fp"); ((TAtom "v326"), "result"); ((TAtom "v330"), "fp"); ((TAtom "v341"), "__libc_single_threaded_internal"); ((TAtom "v345"), "fp"); ((TAtom "v353"), "fp"); ((TAtom "v357"), "fp"); ((TAtom "v363"), "fp"); ((TAtom "v369"), "fp"); ((TAtom "v37"), "__self"); ((TAtom "v374"), "fp"); ((TAtom "v376"), "__futex"); ((TAtom "v379"), "__futex"); ((TAtom "v383"), "__oldval"); ((TAtom "v389"), "__oldval"); ((TAtom "v401"), "__futex"); ((TAtom "v402"), "__futex"); ((TAtom "v403"), "__private"); ((TAtom "v404"), "fp"); ((TAtom "v411"), "fp"); ((TAtom "v413"), "fp"); ((TAtom "v421"), "__libc_single_threaded_internal"); ((TAtom "v44"), "__self"); ((TAtom "v447"), "__futex"); ((TAtom "v451"), "__oldval"); ((TAtom "v457"), "__oldval"); ((TAtom "v469"), "__futex"); ((TAtom "v470"), "__futex"); ((TAtom "v471"), "__private"); ((TAtom "v479"), "_cleanup_start_doit"); ((TAtom "v483"), "_cleanup_routine"); ((TAtom "v486"), "result"); ((TAtom "v5"), "_cleanup_routine"); ((TAtom "v54"), "__futex"); ((TAtom "v55"), "__atg3_old"); ((TAtom "v56"), "__atg3_old"); ((TAtom "v71"), "__futex"); ((TAtom "v72"), "__futex"); ((TAtom "v75"), "__self"); ((TAtom "v81"), "_IO_list_all"); ((TAtom "v86"), "fp"); ((TAtom "v91"), "fp"); ((TAtom "v95"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L381"); (TAtom "L449"); (TAtom "L82")].

End fn___GI__IO_flush_all.

Module fn__IO_cleanup.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_20, 886%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_20, 889%N)); ((TAtom "iw_1.L23"), (file_20, 817%N)); ((TAtom "iw_1.L24"), (file_20, 817%N)); ((TAtom "iw_1.L17"), (file_20, 817%N)); ((TAtom "iw_1.L18"), (file_20, 817%N)); ((TAtom "iw_1.L37"), (file_20, 817%N)); ((TAtom "iw_1.L57"), (file_20, 817%N)); ((TAtom "iw_1.L58"), (file_20, 817%N)); ((TAtom "iw_1.L62"), (file_20, 817%N)); ((TAtom "iw_1.L51"), (file_20, 817%N)); ((TAtom "iw_1.L38"), (file_20, 817%N)); ((TAtom "iw_1.L14"), (file_20, 820%N)); ((TAtom "iw_1.L81"), (file_20, 813%N)); ((TAtom "iw_1.L82"), (file_20, 824%N)); ((TAtom "iw_1.L98"), (file_20, 825%N)); ((TAtom "iw_1.L109"), (file_20, 825%N)); ((TAtom "iw_1.L110"), (file_20, 825%N)); ((TAtom "iw_1.L103"), (file_20, 825%N)); ((TAtom "iw_1.L104"), (file_20, 825%N)); ((TAtom "iw_1.L129"), (file_20, 825%N)); ((TAtom "iw_1.L153"), (file_20, 825%N)); ((TAtom "iw_1.L154"), (file_20, 825%N)); ((TAtom "iw_1.L158"), (file_20, 825%N)); ((TAtom "iw_1.L147"), (file_20, 825%N)); ((TAtom "iw_1.L130"), (file_20, 825%N)); ((TAtom "iw_1.L93"), (file_20, 833%N)); ((TAtom "iw_1.L179"), (file_20, 834%N)); ((TAtom "iw_1.L194"), (file_20, 835%N)); ((TAtom "iw_1.L202"), (file_20, 835%N)); ((TAtom "iw_1.L203"), (file_20, 835%N)); ((TAtom "iw_1.L189"), (file_20, 836%N)); ((TAtom "iw_1.L191"), (file_20, 838%N)); ((TAtom "iw_1.L225"), (file_20, 838%N)); ((TAtom "iw_1.L223"), (file_20, 838%N)); ((TAtom "iw_1.L240"), (file_20, 842%N)); ((TAtom "iw_1.L247"), (file_20, 842%N)); ((TAtom "iw_1.L248"), (file_20, 842%N)); ((TAtom "iw_1.L235"), (file_20, 844%N)); ((TAtom "iw_1.L237"), (file_20, 851%N)); ((TAtom "iw_1.iw_1.L10"), (file_10, 1049%N)); ((TAtom "iw_1.iw_1.join"), (file_20, 851%N)); ((TAtom "iw_1.L277"), (file_20, 854%N)); ((TAtom "iw_1.L291"), (file_20, 860%N)); ((TAtom "iw_1.L306"), (file_20, 862%N)); ((TAtom "iw_1.L315"), (file_20, 862%N)); ((TAtom "iw_1.L316"), (file_20, 862%N)); ((TAtom "iw_1.L309"), (file_20, 862%N)); ((TAtom "iw_1.L310"), (file_20, 862%N)); ((TAtom "iw_1.L332"), (file_20, 862%N)); ((TAtom "iw_1.L353"), (file_20, 862%N)); ((TAtom "iw_1.L354"), (file_20, 862%N)); ((TAtom "iw_1.L365"), (file_20, 862%N)); ((TAtom "iw_1.L333"), (file_20, 862%N)); ((TAtom "iw_1.L301"), (file_20, 863%N)); ((TAtom "iw_1.L386"), (file_20, 867%N)); ((TAtom "iw_1.L395"), (file_20, 867%N)); ((TAtom "iw_1.L396"), (file_20, 867%N)); ((TAtom "iw_1.L389"), (file_20, 867%N)); ((TAtom "iw_1.L390"), (file_20, 867%N)); ((TAtom "iw_1.L406"), (file_20, 867%N)); ((TAtom "iw_1.L421"), (file_20, 867%N)); ((TAtom "iw_1.L422"), (file_20, 867%N)); ((TAtom "iw_1.L433"), (file_20, 867%N)); ((TAtom "iw_1.L407"), (file_20, 867%N)); ((TAtom "iw_1.L448"), (file_20, 868%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.iw_1.v0"), "vtable"); ((TAtom "iw_1.iw_1.v13"), "offset"); ((TAtom "iw_1.iw_1.v18"), "vtable"); ((TAtom "iw_1.iw_1.v3"), "vtable"); ((TAtom "iw_1.iw_1.v4"), "ptr"); ((TAtom "iw_1.iw_1.v6"), "ptr"); ((TAtom "iw_1.iw_1.v9"), "offset"); ((TAtom "iw_1.pr.1"), "fp"); ((TAtom "iw_1.pr.2"), "_cleanup_start_doit"); ((TAtom "iw_1.v10"), "_cleanup_routine"); ((TAtom "iw_1.v102"), "__self"); ((TAtom "iw_1.v107"), "__libc_single_threaded_internal"); ((TAtom "iw_1.v11"), "_cleanup_start_doit"); ((TAtom "iw_1.v111"), "fp"); ((TAtom "iw_1.v121"), "fp"); ((TAtom "iw_1.v124"), "fp"); ((TAtom "iw_1.v128"), "__self"); ((TAtom "iw_1.v132"), "fp"); ((TAtom "iw_1.v137"), "__self"); ((TAtom "iw_1.v142"), "fp"); ((TAtom "iw_1.v144"), "__futex"); ((TAtom "iw_1.v149"), "__futex"); ((TAtom "iw_1.v150"), "__atg3_old"); ((TAtom "iw_1.v151"), "__atg3_old"); ((TAtom "iw_1.v16"), "__self"); ((TAtom "iw_1.v166"), "__futex"); ((TAtom "iw_1.v167"), "__futex"); ((TAtom "iw_1.v168"), "fp"); ((TAtom "iw_1.v172"), "__self"); ((TAtom "iw_1.v173"), "fp"); ((TAtom "iw_1.v182"), "fp"); ((TAtom "iw_1.v188"), "fp"); ((TAtom "iw_1.v192"), "legacy"); ((TAtom "iw_1.v196"), "fp"); ((TAtom "iw_1.v204"), "fp"); ((TAtom "iw_1.v21"), "__libc_single_threaded_internal"); ((TAtom "iw_1.v214"), "fp"); ((TAtom "iw_1.v218"), "fp"); ((TAtom "iw_1.v224"), "legacy"); ((TAtom "iw_1.v227"), "fp"); ((TAtom "iw_1.v238"), "legacy"); ((TAtom "iw_1.v243"), "dealloc_buffers"); ((TAtom "iw_1.v249"), "fp"); ((TAtom "iw_1.v255"), "fp"); ((TAtom "iw_1.v258"), "fp"); ((TAtom "iw_1.v261"), "freeres_list"); ((TAtom "iw_1.v263"), "fp"); ((TAtom "iw_1.v264"), "fp"); ((TAtom "iw_1.v266"), "fp"); ((TAtom "iw_1.v269"), "fp"); ((TAtom "iw_1.v275"), "fp"); ((TAtom "iw_1.v280"), "legacy"); ((TAtom "iw_1.v284"), "fp"); ((TAtom "iw_1.v290"), "fp"); ((TAtom "iw_1.v294"), "legacy"); ((TAtom "iw_1.v296"), "fp"); ((TAtom "iw_1.v302"), "fp"); ((TAtom "iw_1.v313"), "__libc_single_threaded_internal"); ((TAtom "iw_1.v317"), "fp"); ((TAtom "iw_1.v325"), "fp"); ((TAtom "iw_1.v329"), "fp"); ((TAtom "iw_1.v335"), "fp"); ((TAtom "iw_1.v341"), "fp"); ((TAtom "iw_1.v346"), "fp"); ((TAtom "iw_1.v348"), "__futex"); ((TAtom "iw_1.v351"), "__futex"); ((TAtom "iw_1.v355"), "__oldval"); ((TAtom "iw_1.v36"), "__self"); ((TAtom "iw_1.v361"), "__oldval"); ((TAtom "iw_1.v373"), "__futex"); ((TAtom "iw_1.v374"), "__futex"); ((TAtom "iw_1.v375"), "__private"); ((TAtom "iw_1.v376"), "fp"); ((TAtom "iw_1.v383"), "fp"); ((TAtom "iw_1.v385"), "fp"); ((TAtom "iw_1.v393"), "__libc_single_threaded_internal"); ((TAtom "iw_1.v4"), "_cleanup_routine"); ((TAtom "iw_1.v419"), "__futex"); ((TAtom "iw_1.v423"), "__oldval"); ((TAtom "iw_1.v429"), "__oldval"); ((TAtom "iw_1.v43"), "__self"); ((TAtom "iw_1.v441"), "__futex"); ((TAtom "iw_1.v442"), "__futex"); ((TAtom "iw_1.v443"), "__private"); ((TAtom "iw_1.v451"), "_cleanup_start_doit"); ((TAtom "iw_1.v455"), "_cleanup_routine"); ((TAtom "iw_1.v53"), "__futex"); ((TAtom "iw_1.v54"), "__atg3_old"); ((TAtom "iw_1.v55"), "__atg3_old"); ((TAtom "iw_1.v70"), "__futex"); ((TAtom "iw_1.v71"), "__futex"); ((TAtom "iw_1.v74"), "__self"); ((TAtom "iw_1.v80"), "_IO_list_all"); ((TAtom "iw_1.v85"), "fp"); ((TAtom "iw_1.v9"), "_cleanup_start_doit"); ((TAtom "iw_1.v90"), "fp"); ((TAtom "iw_1.v94"), "fp"); ((TAtom "v1"), "result"); ((TAtom "v2"), "result")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "iw_1.L353"); (TAtom "iw_1.L421"); (TAtom "iw_1.L81")].

End fn__IO_cleanup.

Module fn___GI__IO_unsave_markers.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_20, 981%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_20, 984%N)); ((TAtom "L6"), (file_20, 987%N)); ((TAtom "L8"), (file_20, 990%N)); ((TAtom "L14"), (file_20, 991%N)); ((TAtom "L16"), (file_20, 981%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fp"); ((TAtom "v12"), "fp"); ((TAtom "v17"), "fp"); ((TAtom "v23"), "fp"); ((TAtom "v3"), "fp"); ((TAtom "v5"), "mark"); ((TAtom "v9"), "mark")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

End fn___GI__IO_unsave_markers.

Module fn___GI__IO_default_pbackfail.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_20, 995%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_20, 998%N)); ((TAtom "L16"), (file_20, 998%N)); ((TAtom "L17"), (file_20, 998%N)); ((TAtom "L24"), (file_20, 998%N)); ((TAtom "L25"), (file_20, 998%N)); ((TAtom "L4"), (file_20, 1000%N)); ((TAtom "L5"), (file_20, 1004%N)); ((TAtom "L42"), (file_20, 1008%N)); ((TAtom "L61"), (file_20, 1008%N)); ((TAtom "L62"), (file_20, 1008%N)); ((TAtom "L49"), (file_20, 1010%N)); ((TAtom "L71"), (file_20, 1011%N)); ((TAtom "L50"), (file_20, 1013%N)); ((TAtom "L81"), (file_20, 1017%N)); ((TAtom "L96"), (file_20, 1021%N)); ((TAtom "L98"), (file_20, 1017%N)); ((TAtom "L51"), (file_20, 1028%N)); ((TAtom "L43"), (file_20, 1031%N)); ((TAtom "L127"), (file_20, 1035%N)); ((TAtom "L155"), (file_20, 1040%N)); ((TAtom "L157"), (file_20, 1041%N)); ((TAtom "iw_1.L4"), (file_10, 1059%N)); ((TAtom "iw_1.join"), (file_20, 1044%N)); ((TAtom "L44"), (file_20, 1049%N)); ((TAtom "L6"), (file_20, 1051%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "fp"); ((TAtom "iw_1.v13"), "ptr"); ((TAtom "iw_1.v2"), "ptr"); ((TAtom "iw_1.v7"), "ptr"); ((TAtom "iw_1.v8"), "fp"); ((TAtom "pr.1"), "backup_size"); ((TAtom "pr.2"), "bbuf"); ((TAtom "v0"), "fp"); ((TAtom "v10"), "fp"); ((TAtom "v103"), "fp"); ((TAtom "v104"), "bbuf"); ((TAtom "v105"), "fp"); ((TAtom "v107"), "bbuf"); ((TAtom "v108"), "fp"); ((TAtom "v110"), "fp"); ((TAtom "v113"), "backup_size"); ((TAtom "v116"), "fp"); ((TAtom "v118"), "fp"); ((TAtom "v121"), "fp"); ((TAtom "v123"), "fp"); ((TAtom "v126"), "fp"); ((TAtom "v130"), "fp"); ((TAtom "v133"), "fp"); ((TAtom "v141"), "fp"); ((TAtom "v144"), "fp"); ((TAtom "v149"), "old_size"); ((TAtom "v151"), "old_size"); ((TAtom "v152"), "new_size"); ((TAtom "v153"), "new_size"); ((TAtom "v154"), "new_buf"); ((TAtom "v158"), "new_buf"); ((TAtom "v164"), "new_buf"); ((TAtom "v165"), "new_size"); ((TAtom "v166"), "old_size"); ((TAtom "v169"), "fp"); ((TAtom "v172"), "old_size"); ((TAtom "v174"), "fp"); ((TAtom "v175"), "fp"); ((TAtom "v178"), "fp"); ((TAtom "v18"), "fp"); ((TAtom "v180"), "new_buf"); ((TAtom "v181"), "fp"); ((TAtom "v183"), "new_buf"); ((TAtom "v184"), "new_size"); ((TAtom "v185"), "old_size"); ((TAtom "v188"), "fp"); ((TAtom "v190"), "new_buf"); ((TAtom "v191"), "new_size"); ((TAtom "v193"), "fp"); ((TAtom "v195"), "fp"); ((TAtom "v198"), "fp"); ((TAtom "v2"), "c"); ((TAtom "v202"), "c"); ((TAtom "v204"), "c"); ((TAtom "v26"), "fp"); ((TAtom "v34"), "c"); ((TAtom "v38"), "fp"); ((TAtom "v45"), "fp"); ((TAtom "v52"), "fp"); ((TAtom "v55"), "fp"); ((TAtom "v63"), "fp"); ((TAtom "v7"), "fp"); ((TAtom "v74"), "fp"); ((TAtom "v75"), "fp"); ((TAtom "v84"), "fp"); ((TAtom "v93"), "backup_size"); ((TAtom "v95"), "bbuf"); ((TAtom "v99"), "bbuf")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

End fn___GI__IO_default_pbackfail.

Module fn__IO_default_seek.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_20, 1055%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_20, 1058%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fp"); ((TAtom "v2"), "offset"); ((TAtom "v4"), "dir")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

End fn__IO_default_seek.

Module fn__IO_default_stat.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_20, 1061%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_20, 1064%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fp"); ((TAtom "v2"), "st")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

End fn__IO_default_stat.

Module fn__IO_default_read.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_20, 1067%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_20, 1070%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fp"); ((TAtom "v2"), "data"); ((TAtom "v4"), "n")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

End fn__IO_default_read.

Module fn__IO_default_write.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_20, 1073%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_20, 1076%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fp"); ((TAtom "v2"), "data"); ((TAtom "v4"), "n")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

End fn__IO_default_write.

Module fn__IO_default_showmanyc.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_20, 1079%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_20, 1082%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

End fn__IO_default_showmanyc.

Module fn__IO_default_imbue.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_20, 1085%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_20, 1085%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fp"); ((TAtom "v2"), "locale")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

End fn__IO_default_imbue.

Module fn__IO_new_fclose.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_21, 32%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_21, 47%N)); ((TAtom "L18"), (file_21, 47%N)); ((TAtom "L29"), (file_21, 47%N)); ((TAtom "L30"), (file_21, 47%N)); ((TAtom "L23"), (file_21, 47%N)); ((TAtom "L24"), (file_21, 47%N)); ((TAtom "L49"), (file_21, 47%N)); ((TAtom "L73"), (file_21, 47%N)); ((TAtom "L74"), (file_21, 47%N)); ((TAtom "L78"), (file_21, 47%N)); ((TAtom "L67"), (file_21, 47%N)); ((TAtom "L50"), (file_21, 47%N)); ((TAtom "L13"), (file_21, 48%N)); ((TAtom "L99"), (file_21, 50%N)); ((TAtom "L100"), (file_21, 55%N)); ((TAtom "L121"), (file_21, 55%N)); ((TAtom "L101"), (file_21, 35%N)); ((TAtom "iw_1.L5"), (file_10, 1000%N)); ((TAtom "iw_1.L19"), (file_10, 1000%N)); ((TAtom "iw_1.L28"), (file_10, 1000%N)); ((TAtom "iw_1.L29"), (file_10, 1000%N)); ((TAtom "iw_1.L22"), (file_10, 1000%N)); ((TAtom "iw_1.L23"), (file_10, 1000%N)); ((TAtom "iw_1.L45"), (file_10, 1000%N)); ((TAtom "iw_1.L66"), (file_10, 1000%N)); ((TAtom "iw_1.L67"), (file_10, 1000%N)); ((TAtom "iw_1.L78"), (file_10, 1000%N)); ((TAtom "iw_1.L46"), (file_10, 1000%N)); ((TAtom "L8"), (file_21, 65%N)); ((TAtom "iw_2.L10"), (file_10, 1049%N)); ((TAtom "iw_2.join"), (file_21, 67%N)); ((TAtom "L136"), (file_21, 70%N)); ((TAtom "L143"), (file_21, 71%N)); ((TAtom "L145"), (file_21, 74%N)); ((TAtom "L169"), (file_21, 76%N)); ((TAtom "L170"), (file_21, 76%N)); ((TAtom "L174"), (file_21, 76%N)); ((TAtom "L163"), (file_21, 77%N)); ((TAtom "L195"), (file_21, 79%N)); ((TAtom "L196"), (file_21, 79%N)); ((TAtom "L207"), (file_21, 79%N)); ((TAtom "L137"), (file_21, 83%N)); ((TAtom "L218"), (file_21, 84%N)); ((TAtom "iw_3.start"), (file_10, 971%N)); ((TAtom "iw_3.L10"), (file_10, 971%N)); ((TAtom "iw_3.L11"), (file_10, 971%N)); ((TAtom "iw_3.L19"), (file_10, 971%N)); ((TAtom "iw_3.L20"), (file_10, 971%N)); ((TAtom "iw_3.L4"), (file_10, 978%N)); ((TAtom "iw_3.join"), (file_21, 87%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "p"); ((TAtom "iw_1.v15"), "fp"); ((TAtom "iw_1.v26"), "__libc_single_threaded_internal"); ((TAtom "iw_1.v3"), "p"); ((TAtom "iw_1.v30"), "fp"); ((TAtom "iw_1.v38"), "fp"); ((TAtom "iw_1.v4"), "fp"); ((TAtom "iw_1.v42"), "fp"); ((TAtom "iw_1.v48"), "fp"); ((TAtom "iw_1.v54"), "fp"); ((TAtom "iw_1.v59"), "fp"); ((TAtom "iw_1.v61"), "__futex"); ((TAtom "iw_1.v64"), "__futex"); ((TAtom "iw_1.v68"), "__oldval"); ((TAtom "iw_1.v74"), "__oldval"); ((TAtom "iw_1.v8"), "fp"); ((TAtom "iw_1.v86"), "__futex"); ((TAtom "iw_1.v87"), "__futex"); ((TAtom "iw_1.v88"), "__private"); ((TAtom "iw_1.v89"), "fp"); ((TAtom "iw_2.v0"), "vtable"); ((TAtom "iw_2.v13"), "offset"); ((TAtom "iw_2.v18"), "vtable"); ((TAtom "iw_2.v3"), "vtable"); ((TAtom "iw_2.v4"), "ptr"); ((TAtom "iw_2.v6"), "ptr"); ((TAtom "iw_2.v9"), "offset"); ((TAtom "iw_3.v0"), "fp"); ((TAtom "iw_3.v12"), "fp"); ((TAtom "iw_3.v21"), "fp"); ((TAtom "iw_3.v29"), "fp"); ((TAtom "iw_3.v5"), "fp"); ((TAtom "pr.1"), "status"); ((TAtom "v0"), "fp"); ((TAtom "v10"), "fp"); ((TAtom "v102"), "fp"); ((TAtom "v105"), "fp"); ((TAtom "v107"), "status"); ((TAtom "v108"), "fp"); ((TAtom "v123"), "fp"); ((TAtom "v127"), "status"); ((TAtom "v128"), "fp"); ((TAtom "v129"), "fp"); ((TAtom "v135"), "fp"); ((TAtom "v139"), "fp"); ((TAtom "v14"), "_IO_acquire_lock_file"); ((TAtom "v146"), "fp"); ((TAtom "v154"), "fp"); ((TAtom "v156"), "fp"); ((TAtom "v158"), "cc"); ((TAtom "v165"), "__futex"); ((TAtom "v166"), "__atg3_old"); ((TAtom "v167"), "__atg3_old"); ((TAtom "v182"), "__futex"); ((TAtom "v183"), "__futex"); ((TAtom "v184"), "cc"); ((TAtom "v186"), "cc"); ((TAtom "v193"), "__futex"); ((TAtom "v197"), "__oldval"); ((TAtom "v203"), "__oldval"); ((TAtom "v215"), "__futex"); ((TAtom "v216"), "__futex"); ((TAtom "v217"), "__private"); ((TAtom "v22"), "__self"); ((TAtom "v221"), "fp"); ((TAtom "v227"), "fp"); ((TAtom "v228"), "fp"); ((TAtom "v229"), "status"); ((TAtom "v27"), "__libc_single_threaded_internal"); ((TAtom "v31"), "_IO_acquire_lock_file"); ((TAtom "v41"), "_IO_acquire_lock_file"); ((TAtom "v44"), "_IO_acquire_lock_file"); ((TAtom "v48"), "__self"); ((TAtom "v52"), "_IO_acquire_lock_file"); ((TAtom "v57"), "__self"); ((TAtom "v62"), "_IO_acquire_lock_file"); ((TAtom "v64"), "__futex"); ((TAtom "v69"), "__futex"); ((TAtom "v70"), "__atg3_old"); ((TAtom "v71"), "__atg3_old"); ((TAtom "v86"), "__futex"); ((TAtom "v87"), "__futex"); ((TAtom "v88"), "_IO_acquire_lock_file"); ((TAtom "v92"), "__self"); ((TAtom "v93"), "_IO_acquire_lock_file")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L195"); (TAtom "iw_1.L66")].

End fn__IO_new_fclose.

Module fn___GI__IO_puts.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_22, 31%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_22, 35%N)); ((TAtom "L20"), (file_22, 36%N)); ((TAtom "L31"), (file_22, 36%N)); ((TAtom "L32"), (file_22, 36%N)); ((TAtom "L25"), (file_22, 36%N)); ((TAtom "L26"), (file_22, 36%N)); ((TAtom "L51"), (file_22, 36%N)); ((TAtom "L75"), (file_22, 36%N)); ((TAtom "L76"), (file_22, 36%N)); ((TAtom "L80"), (file_22, 36%N)); ((TAtom "L69"), (file_22, 36%N)); ((TAtom "L52"), (file_22, 36%N)); ((TAtom "L109"), (file_22, 39%N)); ((TAtom "L119"), (file_22, 39%N)); ((TAtom "L121"), (file_22, 39%N)); ((TAtom "L162"), (file_22, 38%N)); ((TAtom "iw_1.L10"), (file_10, 1049%N)); ((TAtom "iw_1.join"), (file_22, 38%N)); ((TAtom "L163"), (file_22, 38%N)); ((TAtom "L180"), (file_22, 38%N)); ((TAtom "L182"), (file_22, 38%N)); ((TAtom "L183"), (file_22, 38%N)); ((TAtom "L184"), (file_22, 38%N)); ((TAtom "L181"), (file_22, 38%N)); ((TAtom "L101"), (file_22, 42%N)); ((TAtom "L212"), (file_22, 42%N)); ((TAtom "L103"), (file_22, 34%N)); ((TAtom "iw_2.L5"), (file_10, 1000%N)); ((TAtom "iw_2.L19"), (file_10, 1000%N)); ((TAtom "iw_2.L28"), (file_10, 1000%N)); ((TAtom "iw_2.L29"), (file_10, 1000%N)); ((TAtom "iw_2.L22"), (file_10, 1000%N)); ((TAtom "iw_2.L23"), (file_10, 1000%N)); ((TAtom "iw_2.L45"), (file_10, 1000%N)); ((TAtom "iw_2.L66"), (file_10, 1000%N)); ((TAtom "iw_2.L67"), (file_10, 1000%N)); ((TAtom "iw_2.L78"), (file_10, 1000%N)); ((TAtom "iw_2.L46"), (file_10, 1000%N)); ((TAtom "L9"), (file_22, 45%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "vtable"); ((TAtom "iw_1.v13"), "offset"); ((TAtom "iw_1.v18"), "vtable"); ((TAtom "iw_1.v3"), "vtable"); ((TAtom "iw_1.v4"), "ptr"); ((TAtom "iw_1.v6"), "ptr"); ((TAtom "iw_1.v9"), "offset"); ((TAtom "iw_2.v0"), "p"); ((TAtom "iw_2.v15"), "fp"); ((TAtom "iw_2.v26"), "__libc_single_threaded_internal"); ((TAtom "iw_2.v3"), "p"); ((TAtom "iw_2.v30"), "fp"); ((TAtom "iw_2.v38"), "fp"); ((TAtom "iw_2.v4"), "fp"); ((TAtom "iw_2.v42"), "fp"); ((TAtom "iw_2.v48"), "fp"); ((TAtom "iw_2.v54"), "fp"); ((TAtom "iw_2.v59"), "fp"); ((TAtom "iw_2.v61"), "__futex"); ((TAtom "iw_2.v64"), "__futex"); ((TAtom "iw_2.v68"), "__oldval"); ((TAtom "iw_2.v74"), "__oldval"); ((TAtom "iw_2.v8"), "fp"); ((TAtom "iw_2.v86"), "__futex"); ((TAtom "iw_2.v87"), "__futex"); ((TAtom "iw_2.v88"), "__private"); ((TAtom "iw_2.v89"), "fp"); ((TAtom "pr.1"), "result"); ((TAtom "pr.2"), "result"); ((TAtom "pr.3"), "__result"); ((TAtom "pr.4"), "__result"); ((TAtom "v0"), "str"); ((TAtom "v108"), "__result"); ((TAtom "v112"), "__result"); ((TAtom "v12"), "stdout"); ((TAtom "v123"), "stdout"); ((TAtom "v128"), "stdout"); ((TAtom "v132"), "stdout"); ((TAtom "v134"), "__result"); ((TAtom "v149"), "stdout"); ((TAtom "v152"), "__result"); ((TAtom "v154"), "stdout"); ((TAtom "v155"), "__result"); ((TAtom "v156"), "__result"); ((TAtom "v157"), "__result"); ((TAtom "v16"), "_IO_acquire_lock_file"); ((TAtom "v165"), "stdout"); ((TAtom "v172"), "stdout"); ((TAtom "v173"), "str"); ((TAtom "v174"), "len"); ((TAtom "v176"), "len"); ((TAtom "v186"), "stdout"); ((TAtom "v190"), "stdout"); ((TAtom "v199"), "stdout"); ((TAtom "v202"), "stdout"); ((TAtom "v214"), "len"); ((TAtom "v217"), "len"); ((TAtom "v219"), "result"); ((TAtom "v220"), "result"); ((TAtom "v24"), "__self"); ((TAtom "v29"), "__libc_single_threaded_internal"); ((TAtom "v3"), "result"); ((TAtom "v33"), "_IO_acquire_lock_file"); ((TAtom "v43"), "_IO_acquire_lock_file"); ((TAtom "v46"), "_IO_acquire_lock_file"); ((TAtom "v5"), "str"); ((TAtom "v50"), "__self"); ((TAtom "v54"), "_IO_acquire_lock_file"); ((TAtom "v59"), "__self"); ((TAtom "v6"), "len"); ((TAtom "v64"), "_IO_acquire_lock_file"); ((TAtom "v66"), "__futex"); ((TAtom "v71"), "__futex"); ((TAtom "v72"), "__atg3_old"); ((TAtom "v73"), "__atg3_old"); ((TAtom "v88"), "__futex"); ((TAtom "v89"), "__futex"); ((TAtom "v90"), "_IO_acquire_lock_file"); ((TAtom "v94"), "__self"); ((TAtom "v95"), "_IO_acquire_lock_file")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "iw_2.L66")].

End fn___GI__IO_puts.

End HiAtexitSrc03.
