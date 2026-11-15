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


From Glibc Require Import FxprintfNormalCode.
Module FxprintfNormalSrc.

Definition file_0 : string := "../include/scratch_buffer.h".

Definition file_1 : string := "fxprintf.c".

Module fn___vfxprintf.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_1, 62%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_1, 66%N)); ((TAtom "L8"), (file_1, 67%N)); ((TAtom "L10"), (file_1, 62%N)); ((TAtom "L24"), (file_1, 68%N)); ((TAtom "L35"), (file_1, 68%N)); ((TAtom "L36"), (file_1, 68%N)); ((TAtom "L29"), (file_1, 68%N)); ((TAtom "L30"), (file_1, 68%N)); ((TAtom "L55"), (file_1, 68%N)); ((TAtom "L79"), (file_1, 68%N)); ((TAtom "L80"), (file_1, 68%N)); ((TAtom "L84"), (file_1, 68%N)); ((TAtom "L73"), (file_1, 68%N)); ((TAtom "L56"), (file_1, 68%N)); ((TAtom "iw_1.start"), (file_1, 26%N)); ((TAtom "iw_1.L8"), (file_1, 31%N)); ((TAtom "iw_1.L10"), (file_1, 38%N)); ((TAtom "iw_1.L70"), (file_1, 44%N)); ((TAtom "iw_1.iw_2.start"), (file_0, 131%N)); ((TAtom "iw_1.L83"), (file_1, 49%N)); ((TAtom "iw_1.L95"), (file_1, 55%N)); ((TAtom "iw_1.L97"), (file_1, 37%N)); ((TAtom "iw_1.iw_3.L2"), (file_0, 86%N)); ((TAtom "iw_1.join"), (file_1, 70%N)); ((TAtom "L118"), (file_1, 70%N)); ((TAtom "L127"), (file_1, 70%N)); ((TAtom "L128"), (file_1, 70%N)); ((TAtom "L121"), (file_1, 70%N)); ((TAtom "L122"), (file_1, 70%N)); ((TAtom "L144"), (file_1, 70%N)); ((TAtom "L165"), (file_1, 70%N)); ((TAtom "L166"), (file_1, 70%N)); ((TAtom "L177"), (file_1, 70%N)); ((TAtom "L145"), (file_1, 70%N)); ((TAtom "L113"), (file_1, 71%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.iw_1.v0"), "buffer"); ((TAtom "iw_1.iw_1.v2"), "buffer"); ((TAtom "iw_1.iw_1.v3"), "buffer"); ((TAtom "iw_1.iw_1.v5"), "buffer"); ((TAtom "iw_1.iw_2.v0"), "buffer"); ((TAtom "iw_1.iw_2.v2"), "nelem"); ((TAtom "iw_1.iw_2.v4"), "size"); ((TAtom "iw_1.iw_2.v6"), "buffer"); ((TAtom "iw_1.iw_2.v7"), "nelem"); ((TAtom "iw_1.iw_2.v8"), "size"); ((TAtom "iw_1.iw_3.v0"), "buffer"); ((TAtom "iw_1.iw_3.v12"), "buffer"); ((TAtom "iw_1.iw_3.v5"), "buffer"); ((TAtom "iw_1.iw_3.v7"), "buffer"); ((TAtom "iw_1.pr.1"), "__result"); ((TAtom "iw_1.pr.2"), "__result"); ((TAtom "iw_1.pr.3"), "res"); ((TAtom "iw_1.v0"), "fp"); ((TAtom "iw_1.v101"), "fp"); ((TAtom "iw_1.v102"), "wfmt"); ((TAtom "iw_1.v103"), "ap"); ((TAtom "iw_1.v104"), "mode_flags"); ((TAtom "iw_1.v105"), "res"); ((TAtom "iw_1.v106"), "res"); ((TAtom "iw_1.v15"), "__result"); ((TAtom "iw_1.v2"), "fmt"); ((TAtom "iw_1.v25"), "fp"); ((TAtom "iw_1.v29"), "fp"); ((TAtom "iw_1.v32"), "fp"); ((TAtom "iw_1.v34"), "__result"); ((TAtom "iw_1.v4"), "ap"); ((TAtom "iw_1.v47"), "fp"); ((TAtom "iw_1.v50"), "__result"); ((TAtom "iw_1.v51"), "fp"); ((TAtom "iw_1.v52"), "__result"); ((TAtom "iw_1.v53"), "__result"); ((TAtom "iw_1.v54"), "__result"); ((TAtom "iw_1.v56"), "fp"); ((TAtom "iw_1.v57"), "fmt"); ((TAtom "iw_1.v58"), "ap"); ((TAtom "iw_1.v59"), "mode_flags"); ((TAtom "iw_1.v6"), "mode_flags"); ((TAtom "iw_1.v66"), "fmt"); ((TAtom "iw_1.v68"), "len"); ((TAtom "iw_1.v73"), "len"); ((TAtom "iw_1.v84"), "len"); ((TAtom "iw_1.v90"), "wfmt"); ((TAtom "iw_1.v92"), "wfmt"); ((TAtom "iw_1.v93"), "len"); ((TAtom "iw_1.v94"), "res"); ((TAtom "iw_1.v98"), "res"); ((TAtom "pr.1"), "fp"); ((TAtom "v0"), "fp"); ((TAtom "v106"), "fp"); ((TAtom "v107"), "fmt"); ((TAtom "v108"), "ap"); ((TAtom "v109"), "mode_flags"); ((TAtom "v11"), "fp"); ((TAtom "v110"), "res"); ((TAtom "v114"), "fp"); ((TAtom "v125"), "__libc_single_threaded_internal"); ((TAtom "v129"), "fp"); ((TAtom "v137"), "fp"); ((TAtom "v141"), "fp"); ((TAtom "v147"), "fp"); ((TAtom "v153"), "fp"); ((TAtom "v158"), "fp"); ((TAtom "v16"), "stderr"); ((TAtom "v160"), "__futex"); ((TAtom "v163"), "__futex"); ((TAtom "v167"), "__oldval"); ((TAtom "v173"), "__oldval"); ((TAtom "v185"), "__futex"); ((TAtom "v186"), "__futex"); ((TAtom "v187"), "__private"); ((TAtom "v188"), "fp"); ((TAtom "v194"), "res"); ((TAtom "v2"), "fmt"); ((TAtom "v20"), "fp"); ((TAtom "v28"), "__self"); ((TAtom "v33"), "__libc_single_threaded_internal"); ((TAtom "v37"), "fp"); ((TAtom "v4"), "ap"); ((TAtom "v47"), "fp"); ((TAtom "v50"), "fp"); ((TAtom "v54"), "__self"); ((TAtom "v58"), "fp"); ((TAtom "v6"), "mode_flags"); ((TAtom "v63"), "__self"); ((TAtom "v68"), "fp"); ((TAtom "v70"), "__futex"); ((TAtom "v75"), "__futex"); ((TAtom "v76"), "__atg3_old"); ((TAtom "v77"), "__atg3_old"); ((TAtom "v92"), "__futex"); ((TAtom "v93"), "__futex"); ((TAtom "v94"), "fp"); ((TAtom "v98"), "__self"); ((TAtom "v99"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L165")].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L8"), [(TAtom "v13"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L10"), [(TAtom "v13"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L24"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "v13"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L35"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "v13"); (TAtom "v2"); (TAtom "v28"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L36"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "v2"); (TAtom "v28"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L29"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "v2"); (TAtom "v28"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L30"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "v2"); (TAtom "v28"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L55"), [(TAtom "chk1"); (TAtom "chk9"); (TAtom "pr.1"); (TAtom "v2"); (TAtom "v28"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L79"), [(TAtom "chk1"); (TAtom "chk9"); (TAtom "pr.1"); (TAtom "v2"); (TAtom "v28"); (TAtom "v4"); (TAtom "v6"); (TAtom "v70"); (TAtom "v77")]); ((TAtom "L80"), [(TAtom "chk1"); (TAtom "chk9"); (TAtom "pr.1"); (TAtom "v2"); (TAtom "v28"); (TAtom "v4"); (TAtom "v6"); (TAtom "v70"); (TAtom "v77")]); ((TAtom "L84"), [(TAtom "chk1"); (TAtom "chk9"); (TAtom "pr.1"); (TAtom "v2"); (TAtom "v28"); (TAtom "v4"); (TAtom "v6"); (TAtom "v70")]); ((TAtom "L73"), [(TAtom "chk1"); (TAtom "chk9"); (TAtom "pr.1"); (TAtom "v2"); (TAtom "v28"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L56"), [(TAtom "chk1"); (TAtom "chk9"); (TAtom "pr.1"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "iw_1.start"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "iw_1.L8"), [(TAtom "chk1"); (TAtom "chk18"); (TAtom "iw_1.v3"); (TAtom "pr.1"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "iw_1.L10"), [(TAtom "chk1"); (TAtom "chk18"); (TAtom "iw_1.v3"); (TAtom "iw_1.v63"); (TAtom "iw_1.v69"); (TAtom "pr.1"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "iw_1.L70"), [(TAtom "chk1"); (TAtom "pr.1")]); ((TAtom "iw_1.iw_2.start"), [(TAtom "chk1"); (TAtom "chk22"); (TAtom "iw_1.v3"); (TAtom "iw_1.v63"); (TAtom "iw_1.v68"); (TAtom "iw_1.v69"); (TAtom "pr.1"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "iw_1.L83"), [(TAtom "chk1"); (TAtom "chk22"); (TAtom "iw_1.v3"); (TAtom "iw_1.v63"); (TAtom "iw_1.v68"); (TAtom "iw_1.v69"); (TAtom "pr.1"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "iw_1.L95"), [(TAtom "chk1"); (TAtom "chk22"); (TAtom "iw_1.v69"); (TAtom "iw_1.v90"); (TAtom "pr.1"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "iw_1.L97"), [(TAtom "chk1"); (TAtom "chk22"); (TAtom "iw_1.v69"); (TAtom "pr.1")]); ((TAtom "iw_1.iw_3.L2"), [(TAtom "chk1"); (TAtom "chk26"); (TAtom "iw_1.pr.3"); (TAtom "pr.1")]); ((TAtom "iw_1.join"), [(TAtom "chk1"); (TAtom "pr.1")]); ((TAtom "L118"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "v110")]); ((TAtom "L127"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "v110")]); ((TAtom "L128"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "v110")]); ((TAtom "L121"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "v110")]); ((TAtom "L122"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "v110")]); ((TAtom "L144"), [(TAtom "chk36"); (TAtom "pr.1"); (TAtom "v110")]); ((TAtom "L165"), [(TAtom "chk41"); (TAtom "v110"); (TAtom "v160")]); ((TAtom "L166"), [(TAtom "v110"); (TAtom "v160"); (TAtom "v167")]); ((TAtom "L177"), [(TAtom "v110"); (TAtom "v160")]); ((TAtom "L145"), [(TAtom "chk36"); (TAtom "pr.1"); (TAtom "v110")]); ((TAtom "L113"), [(TAtom "v110")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v13"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L8"), [(TAtom "v13"); (TAtom "v16"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L10"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "v13"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L24"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "v13"); (TAtom "v2"); (TAtom "v28"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L35"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "v2"); (TAtom "v28"); (TAtom "v4"); (TAtom "v44"); (TAtom "v6")]); ((TAtom "L36"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "v2"); (TAtom "v28"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L29"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L30"), [(TAtom "chk1"); (TAtom "chk9"); (TAtom "pr.1"); (TAtom "v2"); (TAtom "v28"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L55"), [(TAtom "chk1"); (TAtom "chk9"); (TAtom "pr.1"); (TAtom "v2"); (TAtom "v28"); (TAtom "v4"); (TAtom "v6"); (TAtom "v70"); (TAtom "v77")]); ((TAtom "L79"), [(TAtom "chk1"); (TAtom "chk9"); (TAtom "pr.1"); (TAtom "v2"); (TAtom "v28"); (TAtom "v4"); (TAtom "v6"); (TAtom "v70"); (TAtom "v77")]); ((TAtom "L80"), [(TAtom "chk1"); (TAtom "chk9"); (TAtom "pr.1"); (TAtom "v2"); (TAtom "v28"); (TAtom "v4"); (TAtom "v6"); (TAtom "v70")]); ((TAtom "L84"), [(TAtom "chk1"); (TAtom "chk9"); (TAtom "pr.1"); (TAtom "v2"); (TAtom "v28"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L73"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L56"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "iw_1.start"), [(TAtom "chk1"); (TAtom "chk18"); (TAtom "iw_1.v3"); (TAtom "iw_1.v63"); (TAtom "iw_1.v69"); (TAtom "pr.1"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "iw_1.L8"), [(TAtom "chk1"); (TAtom "iw_1.v60"); (TAtom "pr.1")]); ((TAtom "iw_1.L10"), [(TAtom "chk1"); (TAtom "chk22"); (TAtom "iw_1.v3"); (TAtom "iw_1.v63"); (TAtom "iw_1.v68"); (TAtom "iw_1.v69"); (TAtom "pr.1"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "iw_1.L70"), [(TAtom "chk1"); (TAtom "pr.1")]); ((TAtom "iw_1.iw_2.start"), [(TAtom "chk1"); (TAtom "chk22"); (TAtom "iw_1.v3"); (TAtom "iw_1.v63"); (TAtom "iw_1.v68"); (TAtom "iw_1.v69"); (TAtom "pr.1"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "iw_1.L83"), [(TAtom "chk1"); (TAtom "chk22"); (TAtom "iw_1.v69"); (TAtom "iw_1.v90"); (TAtom "iw_1.v94"); (TAtom "pr.1"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "iw_1.L95"), [(TAtom "chk1"); (TAtom "chk22"); (TAtom "iw_1.v105"); (TAtom "iw_1.v69"); (TAtom "pr.1")]); ((TAtom "iw_1.L97"), [(TAtom "chk1"); (TAtom "chk26"); (TAtom "iw_1.pr.3"); (TAtom "pr.1")]); ((TAtom "iw_1.iw_3.L2"), [(TAtom "chk1"); (TAtom "iw_1.pr.3"); (TAtom "pr.1")]); ((TAtom "iw_1.join"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "v110")]); ((TAtom "L118"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "v110")]); ((TAtom "L127"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "v110"); (TAtom "v134")]); ((TAtom "L128"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "v110")]); ((TAtom "L121"), [(TAtom "v110")]); ((TAtom "L122"), [(TAtom "chk36"); (TAtom "pr.1"); (TAtom "v110")]); ((TAtom "L144"), [(TAtom "chk41"); (TAtom "v110"); (TAtom "v160"); (TAtom "v164")]); ((TAtom "L165"), [(TAtom "chk41"); (TAtom "v110"); (TAtom "v160"); (TAtom "v167"); (TAtom "v168")]); ((TAtom "L166"), [(TAtom "v110"); (TAtom "v160")]); ((TAtom "L177"), [(TAtom "v110")]); ((TAtom "L145"), [(TAtom "v110")]); ((TAtom "L113"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), []); ((TAtom "L8"), [(2%N, (TApp "tmp" [(TAtom "v15")]), (0), (Some 8), true, false, (Some (TAtom "v15")), (Some (0)), "opaque")]); ((TAtom "L10"), [(1%N, (TApp "tmp" [(TAtom "pr.1")]), (0), (Some 4), true, false, (Some (TAtom "pr.1")), (Some (0)), "fp->_flags")]); ((TAtom "L24"), [(3%N, (TApp "tmp" [(TAtom "v32")]), (0), (Some 1), true, false, (Some (TAtom "v32")), (Some (0)), "opaque")]); ((TAtom "L35"), [(2%N, (TApp "tmp" [(TAtom "v38")]), (0), (Some 8), true, false, (Some (TAtom "pr.1")), (Some (136)), "fp->_lock"); (5%N, (TApp "tmp" [(TAtom "v40")]), (0), (Some 8), true, false, (Some (TAtom "v39")), (Some (8)), "fp->_lock->owner")]); ((TAtom "L36"), []); ((TAtom "L29"), [(2%N, (TApp "tmp" [(TAtom "v48")]), (0), (Some 8), true, false, (Some (TAtom "pr.1")), (Some (136)), "fp->_lock"); (4%N, (TApp "tmp" [(TAtom "v49")]), (0), (Some 4), false, true, (Some (TAtom "v49")), (Some (0)), "fp->_lock->lock"); (5%N, (TApp "tmp" [(TAtom "v48")]), (0), (Some 8), true, false, (Some (TAtom "pr.1")), (Some (136)), "fp->_lock"); (8%N, (TApp "tmp" [(TAtom "v53")]), (0), (Some 8), false, true, (Some (TAtom "v52")), (Some (8)), "fp->_lock->owner")]); ((TAtom "L30"), [(2%N, (TApp "tmp" [(TAtom "v59")]), (0), (Some 8), true, false, (Some (TAtom "pr.1")), (Some (136)), "fp->_lock"); (5%N, (TApp "tmp" [(TAtom "v61")]), (0), (Some 8), true, false, (Some (TAtom "v60")), (Some (8)), "fp->_lock->owner")]); ((TAtom "L55"), [(1%N, (TApp "tmp" [(TAtom "v59")]), (0), (Some 8), true, false, (Some (TAtom "pr.1")), (Some (136)), "fp->_lock"); (3%N, (TApp "tmp" [(TAtom "v70")]), (0), (Some 4), true, true, (Some (TAtom "v70")), (Some (0)), "opaque")]); ((TAtom "L79"), []); ((TAtom "L80"), []); ((TAtom "L84"), []); ((TAtom "L73"), [(2%N, (TApp "tmp" [(TAtom "v95")]), (0), (Some 8), true, false, (Some (TAtom "pr.1")), (Some (136)), "fp->_lock"); (5%N, (TApp "tmp" [(TAtom "v97")]), (0), (Some 8), false, true, (Some (TAtom "v96")), (Some (8)), "fp->_lock->owner")]); ((TAtom "L56"), [(1%N, (TApp "tmp" [(TAtom "v59")]), (0), (Some 8), true, false, (Some (TAtom "pr.1")), (Some (136)), "fp->_lock"); (4%N, (TApp "tmp" [(TAtom "v102")]), (0), (Some 4), true, false, (Some (TAtom "v101")), (Some (4)), "fp->_lock->cnt"); (7%N, (TApp "tmp" [(TAtom "v102")]), (0), (Some 4), false, true, (Some (TAtom "v101")), (Some (4)), "fp->_lock->cnt")]); ((TAtom "iw_1.start"), [(4%N, (TApp "tmp" [(TAtom "iw_1.v3")]), (0), (Some 8), false, true, (Some (TAtom "iw_1.v3")), (Some (0)), "opaque"); (7%N, (TApp "tmp" [(TAtom "iw_1.v48")]), (0), (Some 4), true, false, (Some (TAtom "pr.1")), (Some (192)), "fp->_mode")]); ((TAtom "iw_1.L8"), [(1%N, (TApp "tmp" [(TAtom "iw_1.v3")]), (0), (Some 8), true, false, (Some (TAtom "iw_1.v3")), (Some (0)), "opaque")]); ((TAtom "iw_1.L10"), [(1%N, (TApp "tmp" [(TAtom "iw_1.v3")]), (0), (Some 8), true, false, (Some (TAtom "iw_1.v3")), (Some (0)), "opaque"); (6%N, (TApp "tmp" [(TAtom "iw_1.v69")]), (0), (Some 8), false, true, (Some (TAtom "iw_1.v69")), (Some (0)), "fp->data"); (9%N, (TApp "tmp" [(TAtom "iw_1.iw_1.v6")]), (0), (Some 8), false, true, (Some (TAtom "iw_1.v69")), (Some (8)), "fp->length")]); ((TAtom "iw_1.L70"), [(2%N, (TApp "tmp" [(TAtom "iw_1.v78")]), (0), (Some 4), false, true, (Some (TAtom "iw_1.v78")), (Some (0)), "opaque")]); ((TAtom "iw_1.iw_2.start"), []); ((TAtom "iw_1.L83"), [(1%N, (TApp "tmp" [(TAtom "iw_1.v69")]), (0), (Some 8), true, false, (Some (TAtom "iw_1.v69")), (Some (0)), "buf.data")]); ((TAtom "iw_1.L95"), []); ((TAtom "iw_1.L97"), [(1%N, (TApp "tmp" [(TAtom "iw_1.v69")]), (0), (Some 8), true, false, (Some (TAtom "iw_1.v69")), (Some (0)), "fp->data")]); ((TAtom "iw_1.iw_3.L2"), [(0%N, (TApp "tmp" [(TAtom "iw_1.v69")]), (0), (Some 8), true, false, (Some (TAtom "iw_1.v69")), (Some (0)), "fp->data")]); ((TAtom "iw_1.join"), [(1%N, (TApp "tmp" [(TAtom "pr.1")]), (0), (Some 4), true, false, (Some (TAtom "pr.1")), (Some (0)), "fp->_flags")]); ((TAtom "L118"), [(2%N, (TApp "tmp" [(TAtom "v124")]), (0), (Some 1), true, false, (Some (TAtom "v124")), (Some (0)), "opaque")]); ((TAtom "L127"), [(2%N, (TApp "tmp" [(TAtom "v130")]), (0), (Some 8), true, false, (Some (TAtom "pr.1")), (Some (136)), "fp->_lock"); (5%N, (TApp "tmp" [(TAtom "v132")]), (0), (Some 4), true, false, (Some (TAtom "v131")), (Some (4)), "fp->_lock->cnt")]); ((TAtom "L128"), []); ((TAtom "L121"), [(2%N, (TApp "tmp" [(TAtom "v138")]), (0), (Some 8), true, false, (Some (TAtom "pr.1")), (Some (136)), "fp->_lock"); (5%N, (TApp "tmp" [(TAtom "v140")]), (0), (Some 8), false, true, (Some (TAtom "v139")), (Some (8)), "fp->_lock->owner"); (7%N, (TApp "tmp" [(TAtom "v138")]), (0), (Some 8), true, false, (Some (TAtom "pr.1")), (Some (136)), "fp->_lock"); (9%N, (TApp "tmp" [(TAtom "v143")]), (0), (Some 4), false, true, (Some (TAtom "v143")), (Some (0)), "fp->_lock->lock")]); ((TAtom "L122"), [(2%N, (TApp "tmp" [(TAtom "v148")]), (0), (Some 8), true, false, (Some (TAtom "pr.1")), (Some (136)), "fp->_lock"); (5%N, (TApp "tmp" [(TAtom "v150")]), (0), (Some 4), true, false, (Some (TAtom "v149")), (Some (4)), "fp->_lock->cnt")]); ((TAtom "L144"), [(1%N, (TApp "tmp" [(TAtom "v148")]), (0), (Some 8), true, false, (Some (TAtom "pr.1")), (Some (136)), "fp->_lock"); (4%N, (TApp "tmp" [(TAtom "v156")]), (0), (Some 8), false, true, (Some (TAtom "v155")), (Some (8)), "fp->_lock->owner"); (6%N, (TApp "tmp" [(TAtom "v154")]), (0), (Some 8), true, false, (Some (TAtom "pr.1")), (Some (136)), "fp->_lock"); (8%N, (TApp "tmp" [(TAtom "v160")]), (0), (Some 4), true, false, (Some (TAtom "v160")), (Some (0)), "opaque")]); ((TAtom "L165"), [(1%N, (TApp "tmp" [(TAtom "v160")]), (0), (Some 4), true, true, (Some (TAtom "v160")), (Some (0)), "opaque")]); ((TAtom "L166"), []); ((TAtom "L177"), []); ((TAtom "L145"), [(1%N, (TApp "tmp" [(TAtom "v148")]), (0), (Some 8), true, false, (Some (TAtom "pr.1")), (Some (136)), "fp->_lock"); (4%N, (TApp "tmp" [(TAtom "v191")]), (0), (Some 4), true, false, (Some (TAtom "v190")), (Some (4)), "fp->_lock->cnt"); (7%N, (TApp "tmp" [(TAtom "v191")]), (0), (Some 4), false, true, (Some (TAtom "v190")), (Some (4)), "fp->_lock->cnt")]); ((TAtom "L113"), [])].


End fn___vfxprintf.

Module fn___fxprintf.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_1, 74%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_1, 77%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fp"); ((TAtom "v2"), "fmt"); ((TAtom "v6"), "fp"); ((TAtom "v7"), "fmt"); ((TAtom "v8"), "res"); ((TAtom "v9"), "res")].

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
  [((TAtom "start"), [(3%N, (TApp "tmp" [(TAtom "v4")]), (0), (Some 8), false, true, (Some (TAtom "v4")), (Some (0)), "opaque")])].


End fn___fxprintf.

(** Projection keeps instruction bodies out of the VM code used by the membership check. *)
Definition source_blocks : list (string * option (list name)) := Eval lazy in
  map (fun n => (n,
    match find_direct (TAtom n) fxprintfnormal_module with
    | Some (Defined f) => Some (map b_label (fn_blocks f))
    | _ => None
    end)) ["__vfxprintf"; "__fxprintf"].

(** Projection keeps live sets and memory access records out of the membership computation. *)
Definition table_labels : list (string * list name) := Eval lazy in
  [("__vfxprintf", app (map fst fn___vfxprintf.block_src) (app (map fst fn___vfxprintf.live_in) (app (map fst fn___vfxprintf.live_out) (app (map fst fn___vfxprintf.footprint) (fn___vfxprintf.loop_heads))))); ("__fxprintf", app (map fst fn___fxprintf.block_src) (app (map fst fn___fxprintf.live_in) (app (map fst fn___fxprintf.live_out) (app (map fst fn___fxprintf.footprint) (fn___fxprintf.loop_heads)))))].

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

End FxprintfNormalSrc.
