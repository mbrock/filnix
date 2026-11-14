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


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "L18"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L29"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v22")]); ((TAtom "L30"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v22")]); ((TAtom "L23"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v22")]); ((TAtom "L24"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v22")]); ((TAtom "L49"), [(TAtom "chk0"); (TAtom "chk8"); (TAtom "v0"); (TAtom "v22")]); ((TAtom "L73"), [(TAtom "chk0"); (TAtom "chk8"); (TAtom "v0"); (TAtom "v22"); (TAtom "v64"); (TAtom "v71")]); ((TAtom "L74"), [(TAtom "chk0"); (TAtom "chk8"); (TAtom "v0"); (TAtom "v22"); (TAtom "v64"); (TAtom "v71")]); ((TAtom "L78"), [(TAtom "chk0"); (TAtom "chk8"); (TAtom "v0"); (TAtom "v22"); (TAtom "v64")]); ((TAtom "L67"), [(TAtom "chk0"); (TAtom "chk8"); (TAtom "v0"); (TAtom "v22")]); ((TAtom "L50"), [(TAtom "chk0"); (TAtom "chk8"); (TAtom "v0")]); ((TAtom "L13"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L99"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L100"), [(TAtom "chk0"); (TAtom "chk17"); (TAtom "v0")]); ((TAtom "L121"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L101"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "iw_1.L5"), [(TAtom "chk0"); (TAtom "chk22"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_1.L19"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_1.L28"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_1.L29"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_1.L22"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_1.L23"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_1.L45"), [(TAtom "chk0"); (TAtom "chk31"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_1.L66"), [(TAtom "chk0"); (TAtom "chk36"); (TAtom "iw_1.v61"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_1.L67"), [(TAtom "chk0"); (TAtom "iw_1.v61"); (TAtom "iw_1.v68"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_1.L78"), [(TAtom "chk0"); (TAtom "iw_1.v61"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_1.L46"), [(TAtom "chk0"); (TAtom "chk31"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "L8"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_2.L10"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v131")]); ((TAtom "iw_2.join"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v131")]); ((TAtom "L136"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "L143"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "L145"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "L169"), [(TAtom "pr.1"); (TAtom "v0"); (TAtom "v158"); (TAtom "v160"); (TAtom "v167")]); ((TAtom "L170"), [(TAtom "pr.1"); (TAtom "v0"); (TAtom "v158"); (TAtom "v160"); (TAtom "v167")]); ((TAtom "L174"), [(TAtom "pr.1"); (TAtom "v0"); (TAtom "v158"); (TAtom "v160")]); ((TAtom "L163"), [(TAtom "pr.1"); (TAtom "v0"); (TAtom "v158")]); ((TAtom "L195"), [(TAtom "chk51"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v190")]); ((TAtom "L196"), [(TAtom "pr.1"); (TAtom "v0"); (TAtom "v190"); (TAtom "v197")]); ((TAtom "L207"), [(TAtom "pr.1"); (TAtom "v0"); (TAtom "v190")]); ((TAtom "L137"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "L218"), [(TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_3.start"), [(TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_3.L10"), [(TAtom "iw_3.v7"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_3.L11"), [(TAtom "iw_3.v7"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_3.L19"), [(TAtom "iw_3.v7"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_3.L20"), [(TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_3.L4"), [(TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_3.join"), [(TAtom "pr.1")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L18"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v22")]); ((TAtom "L29"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v22"); (TAtom "v38")]); ((TAtom "L30"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v22")]); ((TAtom "L23"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L24"), [(TAtom "chk0"); (TAtom "chk8"); (TAtom "v0"); (TAtom "v22")]); ((TAtom "L49"), [(TAtom "chk0"); (TAtom "chk8"); (TAtom "v0"); (TAtom "v22"); (TAtom "v64"); (TAtom "v71")]); ((TAtom "L73"), [(TAtom "chk0"); (TAtom "chk8"); (TAtom "v0"); (TAtom "v22"); (TAtom "v64"); (TAtom "v71")]); ((TAtom "L74"), [(TAtom "chk0"); (TAtom "chk8"); (TAtom "v0"); (TAtom "v22"); (TAtom "v64")]); ((TAtom "L78"), [(TAtom "chk0"); (TAtom "chk8"); (TAtom "v0"); (TAtom "v22")]); ((TAtom "L67"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L50"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L13"), [(TAtom "chk0"); (TAtom "chk17"); (TAtom "v0")]); ((TAtom "L99"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v107")]); ((TAtom "L100"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L121"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L101"), [(TAtom "chk0"); (TAtom "chk22"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_1.L5"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_1.L19"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_1.L28"), [(TAtom "chk0"); (TAtom "iw_1.v35"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_1.L29"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_1.L22"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_1.L23"), [(TAtom "chk0"); (TAtom "chk31"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_1.L45"), [(TAtom "chk0"); (TAtom "chk36"); (TAtom "iw_1.v61"); (TAtom "iw_1.v65"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_1.L66"), [(TAtom "chk0"); (TAtom "chk36"); (TAtom "iw_1.v61"); (TAtom "iw_1.v68"); (TAtom "iw_1.v69"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_1.L67"), [(TAtom "chk0"); (TAtom "iw_1.v61"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_1.L78"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_1.L46"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "L8"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v131")]); ((TAtom "iw_2.L10"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v131")]); ((TAtom "iw_2.join"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "L136"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "L143"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "L145"), [(TAtom "pr.1"); (TAtom "v0"); (TAtom "v158"); (TAtom "v160"); (TAtom "v167")]); ((TAtom "L169"), [(TAtom "pr.1"); (TAtom "v0"); (TAtom "v158"); (TAtom "v160"); (TAtom "v167")]); ((TAtom "L170"), [(TAtom "pr.1"); (TAtom "v0"); (TAtom "v158"); (TAtom "v160")]); ((TAtom "L174"), [(TAtom "pr.1"); (TAtom "v0"); (TAtom "v158")]); ((TAtom "L163"), [(TAtom "chk51"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v190"); (TAtom "v194")]); ((TAtom "L195"), [(TAtom "chk51"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v190"); (TAtom "v197"); (TAtom "v198")]); ((TAtom "L196"), [(TAtom "pr.1"); (TAtom "v0"); (TAtom "v190")]); ((TAtom "L207"), [(TAtom "pr.1"); (TAtom "v0")]); ((TAtom "L137"), [(TAtom "pr.1"); (TAtom "v0")]); ((TAtom "L218"), [(TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_3.start"), [(TAtom "iw_3.v7"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_3.L10"), [(TAtom "iw_3.v16"); (TAtom "iw_3.v7"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_3.L11"), [(TAtom "iw_3.v7"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_3.L19"), [(TAtom "iw_3.v25"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_3.L20"), [(TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_3.L4"), [(TAtom "pr.1")]); ((TAtom "iw_3.join"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0)), "_IO_acquire_lock_file->_flags")]); ((TAtom "L18"), [(3%N, (TApp "tmp" [(TAtom "v26")]), (0), (Some 1), true, false, (Some (TAtom "v26")), (Some (0)), "opaque")]); ((TAtom "L29"), [(2%N, (TApp "tmp" [(TAtom "v32")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136)), "_IO_acquire_lock_file->_lock"); (5%N, (TApp "tmp" [(TAtom "v34")]), (0), (Some 8), true, false, (Some (TAtom "v33")), (Some (8)), "_IO_acquire_lock_file->_lock->owner")]); ((TAtom "L30"), []); ((TAtom "L23"), [(2%N, (TApp "tmp" [(TAtom "v42")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136)), "_IO_acquire_lock_file->_lock"); (4%N, (TApp "tmp" [(TAtom "v43")]), (0), (Some 4), false, true, (Some (TAtom "v43")), (Some (0)), "_IO_acquire_lock_file->_lock->lock"); (5%N, (TApp "tmp" [(TAtom "v42")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136)), "_IO_acquire_lock_file->_lock"); (8%N, (TApp "tmp" [(TAtom "v47")]), (0), (Some 8), false, true, (Some (TAtom "v46")), (Some (8)), "_IO_acquire_lock_file->_lock->owner")]); ((TAtom "L24"), [(2%N, (TApp "tmp" [(TAtom "v53")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136)), "_IO_acquire_lock_file->_lock"); (5%N, (TApp "tmp" [(TAtom "v55")]), (0), (Some 8), true, false, (Some (TAtom "v54")), (Some (8)), "_IO_acquire_lock_file->_lock->owner")]); ((TAtom "L49"), [(1%N, (TApp "tmp" [(TAtom "v53")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136)), "_IO_acquire_lock_file->_lock"); (3%N, (TApp "tmp" [(TAtom "v64")]), (0), (Some 4), true, true, (Some (TAtom "v64")), (Some (0)), "opaque")]); ((TAtom "L73"), []); ((TAtom "L74"), []); ((TAtom "L78"), []); ((TAtom "L67"), [(2%N, (TApp "tmp" [(TAtom "v89")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136)), "_IO_acquire_lock_file->_lock"); (5%N, (TApp "tmp" [(TAtom "v91")]), (0), (Some 8), false, true, (Some (TAtom "v90")), (Some (8)), "_IO_acquire_lock_file->_lock->owner")]); ((TAtom "L50"), [(1%N, (TApp "tmp" [(TAtom "v53")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136)), "_IO_acquire_lock_file->_lock"); (4%N, (TApp "tmp" [(TAtom "v96")]), (0), (Some 4), true, false, (Some (TAtom "v95")), (Some (4)), "_IO_acquire_lock_file->_lock->cnt"); (7%N, (TApp "tmp" [(TAtom "v96")]), (0), (Some 4), false, true, (Some (TAtom "v95")), (Some (4)), "_IO_acquire_lock_file->_lock->cnt")]); ((TAtom "L13"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0)), "fp->_flags")]); ((TAtom "L99"), [(3%N, (TApp "tmp" [(TAtom "v109")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (116)), "fp->_flags2"); (7%N, (TApp "tmp" [(TAtom "v109")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (116)), "fp->_flags2"); (12%N, (TApp "tmp" [(TAtom "v109")]), (0), (Some 4), false, true, (Some (TAtom "v0")), (Some (116)), "fp->_flags2")]); ((TAtom "L100"), [(0%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0)), "fp->_flags")]); ((TAtom "L121"), []); ((TAtom "L101"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0)), "status->_flags")]); ((TAtom "iw_1.L5"), [(0%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0)), "status->_flags")]); ((TAtom "iw_1.L19"), [(2%N, (TApp "tmp" [(TAtom "iw_1.v25")]), (0), (Some 1), true, false, (Some (TAtom "iw_1.v25")), (Some (0)), "opaque")]); ((TAtom "iw_1.L28"), [(2%N, (TApp "tmp" [(TAtom "iw_1.v31")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136)), "status->_lock"); (5%N, (TApp "tmp" [(TAtom "iw_1.v33")]), (0), (Some 4), true, false, (Some (TAtom "iw_1.v32")), (Some (4)), "status->_lock->cnt")]); ((TAtom "iw_1.L29"), []); ((TAtom "iw_1.L22"), [(2%N, (TApp "tmp" [(TAtom "iw_1.v39")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136)), "status->_lock"); (5%N, (TApp "tmp" [(TAtom "iw_1.v41")]), (0), (Some 8), false, true, (Some (TAtom "iw_1.v40")), (Some (8)), "status->_lock->owner"); (7%N, (TApp "tmp" [(TAtom "iw_1.v39")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136)), "status->_lock"); (9%N, (TApp "tmp" [(TAtom "iw_1.v44")]), (0), (Some 4), false, true, (Some (TAtom "iw_1.v44")), (Some (0)), "status->_lock->lock")]); ((TAtom "iw_1.L23"), [(2%N, (TApp "tmp" [(TAtom "iw_1.v49")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136)), "status->_lock"); (5%N, (TApp "tmp" [(TAtom "iw_1.v51")]), (0), (Some 4), true, false, (Some (TAtom "iw_1.v50")), (Some (4)), "status->_lock->cnt")]); ((TAtom "iw_1.L45"), [(1%N, (TApp "tmp" [(TAtom "iw_1.v49")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136)), "status->_lock"); (4%N, (TApp "tmp" [(TAtom "iw_1.v57")]), (0), (Some 8), false, true, (Some (TAtom "iw_1.v56")), (Some (8)), "status->_lock->owner"); (6%N, (TApp "tmp" [(TAtom "iw_1.v55")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136)), "status->_lock"); (8%N, (TApp "tmp" [(TAtom "iw_1.v61")]), (0), (Some 4), true, false, (Some (TAtom "iw_1.v61")), (Some (0)), "opaque")]); ((TAtom "iw_1.L66"), [(1%N, (TApp "tmp" [(TAtom "iw_1.v61")]), (0), (Some 4), true, true, (Some (TAtom "iw_1.v61")), (Some (0)), "opaque")]); ((TAtom "iw_1.L67"), []); ((TAtom "iw_1.L78"), []); ((TAtom "iw_1.L46"), [(1%N, (TApp "tmp" [(TAtom "iw_1.v49")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136)), "status->_lock"); (4%N, (TApp "tmp" [(TAtom "iw_1.v92")]), (0), (Some 4), true, false, (Some (TAtom "iw_1.v91")), (Some (4)), "status->_lock->cnt"); (7%N, (TApp "tmp" [(TAtom "iw_1.v92")]), (0), (Some 4), false, true, (Some (TAtom "iw_1.v91")), (Some (4)), "status->_lock->cnt")]); ((TAtom "L8"), [(3%N, (TApp "tmp" [(TAtom "v130")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (216)), "opaque")]); ((TAtom "iw_2.L10"), []); ((TAtom "iw_2.join"), [(2%N, (TApp "tmp" [(TAtom "v133")]), (0), (Some 8), true, false, (Some (TAtom "v131")), (Some (16)), "opaque"); (7%N, (TApp "tmp" [(TAtom "v140")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (192)), "fp->_mode")]); ((TAtom "L136"), [(2%N, (TApp "tmp" [(TAtom "v147")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (160)), "fp->_wide_data"); (5%N, (TApp "tmp" [(TAtom "v149")]), (0), (Some 8), true, false, (Some (TAtom "v148")), (Some (72)), "fp->_wide_data->_IO_backup_base")]); ((TAtom "L143"), []); ((TAtom "L145"), [(2%N, (TApp "tmp" [(TAtom "v157")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (152)), "fp->_codecvt"); (5%N, (TApp "tmp" [(TAtom "v160")]), (0), (Some 4), true, true, (Some (TAtom "v160")), (Some (0)), "opaque")]); ((TAtom "L169"), []); ((TAtom "L170"), []); ((TAtom "L174"), []); ((TAtom "L163"), [(1%N, (TApp "tmp" [(TAtom "v158")]), (0), (Some 8), true, false, (Some (TAtom "v158")), (Some (0)), "cc->__cd_in.step"); (5%N, (TApp "tmp" [(TAtom "v187")]), (0), (Some 8), true, false, (Some (TAtom "v158")), (Some (56)), "cc->__cd_out.step"); (9%N, (TApp "tmp" [(TAtom "v190")]), (0), (Some 4), true, false, (Some (TAtom "v190")), (Some (0)), "opaque")]); ((TAtom "L195"), [(1%N, (TApp "tmp" [(TAtom "v190")]), (0), (Some 4), true, true, (Some (TAtom "v190")), (Some (0)), "opaque")]); ((TAtom "L196"), []); ((TAtom "L207"), []); ((TAtom "L137"), [(2%N, (TApp "tmp" [(TAtom "v222")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (80)), "fp->_IO_backup_base")]); ((TAtom "L218"), []); ((TAtom "iw_3.start"), []); ((TAtom "iw_3.L10"), []); ((TAtom "iw_3.L11"), []); ((TAtom "iw_3.L19"), []); ((TAtom "iw_3.L20"), []); ((TAtom "iw_3.L4"), []); ((TAtom "iw_3.join"), [])].


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


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "L20"), [(TAtom "chk1"); (TAtom "v0"); (TAtom "v12"); (TAtom "v6")]); ((TAtom "L31"), [(TAtom "chk1"); (TAtom "v0"); (TAtom "v12"); (TAtom "v24"); (TAtom "v6")]); ((TAtom "L32"), [(TAtom "chk1"); (TAtom "v0"); (TAtom "v12"); (TAtom "v24"); (TAtom "v6")]); ((TAtom "L25"), [(TAtom "chk1"); (TAtom "v0"); (TAtom "v12"); (TAtom "v24"); (TAtom "v6")]); ((TAtom "L26"), [(TAtom "chk1"); (TAtom "v0"); (TAtom "v12"); (TAtom "v24"); (TAtom "v6")]); ((TAtom "L51"), [(TAtom "chk1"); (TAtom "chk9"); (TAtom "v0"); (TAtom "v12"); (TAtom "v24"); (TAtom "v6")]); ((TAtom "L75"), [(TAtom "chk1"); (TAtom "chk9"); (TAtom "v0"); (TAtom "v12"); (TAtom "v24"); (TAtom "v6"); (TAtom "v66"); (TAtom "v73")]); ((TAtom "L76"), [(TAtom "chk1"); (TAtom "chk9"); (TAtom "v0"); (TAtom "v12"); (TAtom "v24"); (TAtom "v6"); (TAtom "v66"); (TAtom "v73")]); ((TAtom "L80"), [(TAtom "chk1"); (TAtom "chk9"); (TAtom "v0"); (TAtom "v12"); (TAtom "v24"); (TAtom "v6"); (TAtom "v66")]); ((TAtom "L69"), [(TAtom "chk1"); (TAtom "chk9"); (TAtom "v0"); (TAtom "v12"); (TAtom "v24"); (TAtom "v6")]); ((TAtom "L52"), [(TAtom "chk1"); (TAtom "chk9"); (TAtom "v0"); (TAtom "v12"); (TAtom "v6")]); ((TAtom "L109"), [(TAtom "chk1"); (TAtom "v0"); (TAtom "v12"); (TAtom "v6")]); ((TAtom "L119"), [(TAtom "chk1"); (TAtom "v0"); (TAtom "v12"); (TAtom "v6")]); ((TAtom "L121"), [(TAtom "chk1"); (TAtom "v0"); (TAtom "v12"); (TAtom "v6")]); ((TAtom "L162"), [(TAtom "chk1"); (TAtom "v0"); (TAtom "v12"); (TAtom "v6")]); ((TAtom "iw_1.L10"), [(TAtom "chk1"); (TAtom "v0"); (TAtom "v12"); (TAtom "v167"); (TAtom "v6")]); ((TAtom "iw_1.join"), [(TAtom "chk1"); (TAtom "v0"); (TAtom "v12"); (TAtom "v167"); (TAtom "v6")]); ((TAtom "L163"), [(TAtom "chk1"); (TAtom "v12"); (TAtom "v6")]); ((TAtom "L180"), [(TAtom "chk1"); (TAtom "v12"); (TAtom "v6")]); ((TAtom "L182"), [(TAtom "chk1"); (TAtom "v12"); (TAtom "v6")]); ((TAtom "L183"), [(TAtom "chk1"); (TAtom "v12"); (TAtom "v6")]); ((TAtom "L184"), [(TAtom "chk1"); (TAtom "v12"); (TAtom "v6")]); ((TAtom "L181"), [(TAtom "chk1"); (TAtom "v12"); (TAtom "v6")]); ((TAtom "L101"), [(TAtom "chk1"); (TAtom "v12"); (TAtom "v6")]); ((TAtom "L212"), [(TAtom "chk1"); (TAtom "v12"); (TAtom "v215")]); ((TAtom "L103"), [(TAtom "chk1"); (TAtom "v12")]); ((TAtom "iw_2.L5"), [(TAtom "chk1"); (TAtom "chk38"); (TAtom "pr.1"); (TAtom "v12")]); ((TAtom "iw_2.L19"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "v12")]); ((TAtom "iw_2.L28"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "v12")]); ((TAtom "iw_2.L29"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "v12")]); ((TAtom "iw_2.L22"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "v12")]); ((TAtom "iw_2.L23"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "v12")]); ((TAtom "iw_2.L45"), [(TAtom "chk47"); (TAtom "pr.1"); (TAtom "v12")]); ((TAtom "iw_2.L66"), [(TAtom "chk52"); (TAtom "iw_2.v61"); (TAtom "pr.1")]); ((TAtom "iw_2.L67"), [(TAtom "iw_2.v61"); (TAtom "iw_2.v68"); (TAtom "pr.1")]); ((TAtom "iw_2.L78"), [(TAtom "iw_2.v61"); (TAtom "pr.1")]); ((TAtom "iw_2.L46"), [(TAtom "chk47"); (TAtom "pr.1"); (TAtom "v12")]); ((TAtom "L9"), [(TAtom "pr.1")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "chk1"); (TAtom "v0"); (TAtom "v12"); (TAtom "v6")]); ((TAtom "L20"), [(TAtom "chk1"); (TAtom "v0"); (TAtom "v12"); (TAtom "v24"); (TAtom "v6")]); ((TAtom "L31"), [(TAtom "chk1"); (TAtom "v0"); (TAtom "v12"); (TAtom "v24"); (TAtom "v40"); (TAtom "v6")]); ((TAtom "L32"), [(TAtom "chk1"); (TAtom "v0"); (TAtom "v12"); (TAtom "v24"); (TAtom "v6")]); ((TAtom "L25"), [(TAtom "chk1"); (TAtom "v0"); (TAtom "v12"); (TAtom "v6")]); ((TAtom "L26"), [(TAtom "chk1"); (TAtom "chk9"); (TAtom "v0"); (TAtom "v12"); (TAtom "v24"); (TAtom "v6")]); ((TAtom "L51"), [(TAtom "chk1"); (TAtom "chk9"); (TAtom "v0"); (TAtom "v12"); (TAtom "v24"); (TAtom "v6"); (TAtom "v66"); (TAtom "v73")]); ((TAtom "L75"), [(TAtom "chk1"); (TAtom "chk9"); (TAtom "v0"); (TAtom "v12"); (TAtom "v24"); (TAtom "v6"); (TAtom "v66"); (TAtom "v73")]); ((TAtom "L76"), [(TAtom "chk1"); (TAtom "chk9"); (TAtom "v0"); (TAtom "v12"); (TAtom "v24"); (TAtom "v6"); (TAtom "v66")]); ((TAtom "L80"), [(TAtom "chk1"); (TAtom "chk9"); (TAtom "v0"); (TAtom "v12"); (TAtom "v24"); (TAtom "v6")]); ((TAtom "L69"), [(TAtom "chk1"); (TAtom "v0"); (TAtom "v12"); (TAtom "v6")]); ((TAtom "L52"), [(TAtom "chk1"); (TAtom "v0"); (TAtom "v12"); (TAtom "v6")]); ((TAtom "L109"), [(TAtom "chk1"); (TAtom "v0"); (TAtom "v12"); (TAtom "v6")]); ((TAtom "L119"), [(TAtom "chk1"); (TAtom "v0"); (TAtom "v12"); (TAtom "v6")]); ((TAtom "L121"), [(TAtom "chk1"); (TAtom "v0"); (TAtom "v12"); (TAtom "v6")]); ((TAtom "L162"), [(TAtom "chk1"); (TAtom "v0"); (TAtom "v12"); (TAtom "v167"); (TAtom "v6")]); ((TAtom "iw_1.L10"), [(TAtom "chk1"); (TAtom "v0"); (TAtom "v12"); (TAtom "v167"); (TAtom "v6")]); ((TAtom "iw_1.join"), [(TAtom "chk1"); (TAtom "v12"); (TAtom "v177"); (TAtom "v6")]); ((TAtom "L163"), [(TAtom "chk1"); (TAtom "v12"); (TAtom "v6")]); ((TAtom "L180"), [(TAtom "chk1"); (TAtom "v12"); (TAtom "v6")]); ((TAtom "L182"), [(TAtom "chk1"); (TAtom "v12"); (TAtom "v200"); (TAtom "v6")]); ((TAtom "L183"), [(TAtom "chk1"); (TAtom "v12"); (TAtom "v6")]); ((TAtom "L184"), [(TAtom "chk1"); (TAtom "v12"); (TAtom "v208"); (TAtom "v6")]); ((TAtom "L181"), [(TAtom "chk1"); (TAtom "v12"); (TAtom "v6")]); ((TAtom "L101"), [(TAtom "chk1"); (TAtom "v12"); (TAtom "v215")]); ((TAtom "L212"), [(TAtom "chk1"); (TAtom "v12"); (TAtom "v215")]); ((TAtom "L103"), [(TAtom "chk1"); (TAtom "chk38"); (TAtom "pr.1"); (TAtom "v12")]); ((TAtom "iw_2.L5"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "v12")]); ((TAtom "iw_2.L19"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "v12")]); ((TAtom "iw_2.L28"), [(TAtom "chk1"); (TAtom "iw_2.v35"); (TAtom "pr.1"); (TAtom "v12")]); ((TAtom "iw_2.L29"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "v12")]); ((TAtom "iw_2.L22"), [(TAtom "pr.1")]); ((TAtom "iw_2.L23"), [(TAtom "chk47"); (TAtom "pr.1"); (TAtom "v12")]); ((TAtom "iw_2.L45"), [(TAtom "chk52"); (TAtom "iw_2.v61"); (TAtom "iw_2.v65"); (TAtom "pr.1")]); ((TAtom "iw_2.L66"), [(TAtom "chk52"); (TAtom "iw_2.v61"); (TAtom "iw_2.v68"); (TAtom "iw_2.v69"); (TAtom "pr.1")]); ((TAtom "iw_2.L67"), [(TAtom "iw_2.v61"); (TAtom "pr.1")]); ((TAtom "iw_2.L78"), [(TAtom "pr.1")]); ((TAtom "iw_2.L46"), [(TAtom "pr.1")]); ((TAtom "L9"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), [(3%N, (TApp "tmp" [(TAtom "v11")]), (0), (Some 8), true, false, (Some (TAtom "v11")), (Some (0)), "opaque"); (5%N, (TApp "tmp" [(TAtom "v12")]), (0), (Some 4), true, false, (Some (TAtom "v12")), (Some (0)), "_IO_acquire_lock_file->_flags")]); ((TAtom "L20"), [(3%N, (TApp "tmp" [(TAtom "v28")]), (0), (Some 1), true, false, (Some (TAtom "v28")), (Some (0)), "opaque")]); ((TAtom "L31"), [(2%N, (TApp "tmp" [(TAtom "v34")]), (0), (Some 8), true, false, (Some (TAtom "v12")), (Some (136)), "_IO_acquire_lock_file->_lock"); (5%N, (TApp "tmp" [(TAtom "v36")]), (0), (Some 8), true, false, (Some (TAtom "v35")), (Some (8)), "_IO_acquire_lock_file->_lock->owner")]); ((TAtom "L32"), []); ((TAtom "L25"), [(2%N, (TApp "tmp" [(TAtom "v44")]), (0), (Some 8), true, false, (Some (TAtom "v12")), (Some (136)), "_IO_acquire_lock_file->_lock"); (4%N, (TApp "tmp" [(TAtom "v45")]), (0), (Some 4), false, true, (Some (TAtom "v45")), (Some (0)), "_IO_acquire_lock_file->_lock->lock"); (5%N, (TApp "tmp" [(TAtom "v44")]), (0), (Some 8), true, false, (Some (TAtom "v12")), (Some (136)), "_IO_acquire_lock_file->_lock"); (8%N, (TApp "tmp" [(TAtom "v49")]), (0), (Some 8), false, true, (Some (TAtom "v48")), (Some (8)), "_IO_acquire_lock_file->_lock->owner")]); ((TAtom "L26"), [(2%N, (TApp "tmp" [(TAtom "v55")]), (0), (Some 8), true, false, (Some (TAtom "v12")), (Some (136)), "_IO_acquire_lock_file->_lock"); (5%N, (TApp "tmp" [(TAtom "v57")]), (0), (Some 8), true, false, (Some (TAtom "v56")), (Some (8)), "_IO_acquire_lock_file->_lock->owner")]); ((TAtom "L51"), [(1%N, (TApp "tmp" [(TAtom "v55")]), (0), (Some 8), true, false, (Some (TAtom "v12")), (Some (136)), "_IO_acquire_lock_file->_lock"); (3%N, (TApp "tmp" [(TAtom "v66")]), (0), (Some 4), true, true, (Some (TAtom "v66")), (Some (0)), "opaque")]); ((TAtom "L75"), []); ((TAtom "L76"), []); ((TAtom "L80"), []); ((TAtom "L69"), [(2%N, (TApp "tmp" [(TAtom "v91")]), (0), (Some 8), true, false, (Some (TAtom "v12")), (Some (136)), "_IO_acquire_lock_file->_lock"); (5%N, (TApp "tmp" [(TAtom "v93")]), (0), (Some 8), false, true, (Some (TAtom "v92")), (Some (8)), "_IO_acquire_lock_file->_lock->owner")]); ((TAtom "L52"), [(1%N, (TApp "tmp" [(TAtom "v55")]), (0), (Some 8), true, false, (Some (TAtom "v12")), (Some (136)), "_IO_acquire_lock_file->_lock"); (4%N, (TApp "tmp" [(TAtom "v98")]), (0), (Some 4), true, false, (Some (TAtom "v97")), (Some (4)), "_IO_acquire_lock_file->_lock->cnt"); (7%N, (TApp "tmp" [(TAtom "v98")]), (0), (Some 4), false, true, (Some (TAtom "v97")), (Some (4)), "_IO_acquire_lock_file->_lock->cnt")]); ((TAtom "L109"), [(2%N, (TApp "tmp" [(TAtom "v122")]), (0), (Some 8), true, false, (Some (TAtom "v122")), (Some (0)), "opaque"); (5%N, (TApp "tmp" [(TAtom "v124")]), (0), (Some 4), true, false, (Some (TAtom "v123")), (Some (192)), "stdout->_mode")]); ((TAtom "L119"), [(2%N, (TApp "tmp" [(TAtom "v127")]), (0), (Some 8), true, false, (Some (TAtom "v127")), (Some (0)), "opaque"); (5%N, (TApp "tmp" [(TAtom "v129")]), (0), (Some 4), false, true, (Some (TAtom "v128")), (Some (192)), "stdout->_mode")]); ((TAtom "L121"), [(2%N, (TApp "tmp" [(TAtom "v131")]), (0), (Some 8), true, false, (Some (TAtom "v131")), (Some (0)), "opaque"); (5%N, (TApp "tmp" [(TAtom "v133")]), (0), (Some 4), true, false, (Some (TAtom "v132")), (Some (192)), "stdout->_mode")]); ((TAtom "L162"), [(2%N, (TApp "tmp" [(TAtom "v164")]), (0), (Some 8), true, false, (Some (TAtom "v164")), (Some (0)), "opaque"); (5%N, (TApp "tmp" [(TAtom "v166")]), (0), (Some 8), true, false, (Some (TAtom "v165")), (Some (216)), "opaque")]); ((TAtom "iw_1.L10"), []); ((TAtom "iw_1.join"), [(2%N, (TApp "tmp" [(TAtom "v169")]), (0), (Some 8), true, false, (Some (TAtom "v167")), (Some (56)), "opaque"); (5%N, (TApp "tmp" [(TAtom "v171")]), (0), (Some 8), true, false, (Some (TAtom "v171")), (Some (0)), "opaque")]); ((TAtom "L163"), []); ((TAtom "L180"), [(2%N, (TApp "tmp" [(TAtom "v185")]), (0), (Some 8), true, false, (Some (TAtom "v185")), (Some (0)), "opaque"); (5%N, (TApp "tmp" [(TAtom "v187")]), (0), (Some 8), true, false, (Some (TAtom "v186")), (Some (40)), "stdout->_IO_write_ptr"); (8%N, (TApp "tmp" [(TAtom "v189")]), (0), (Some 8), true, false, (Some (TAtom "v189")), (Some (0)), "opaque"); (11%N, (TApp "tmp" [(TAtom "v191")]), (0), (Some 8), true, false, (Some (TAtom "v190")), (Some (48)), "stdout->_IO_write_end")]); ((TAtom "L182"), [(2%N, (TApp "tmp" [(TAtom "v198")]), (0), (Some 8), true, false, (Some (TAtom "v198")), (Some (0)), "opaque")]); ((TAtom "L183"), [(2%N, (TApp "tmp" [(TAtom "v201")]), (0), (Some 8), true, false, (Some (TAtom "v201")), (Some (0)), "opaque"); (5%N, (TApp "tmp" [(TAtom "v203")]), (0), (Some 8), true, false, (Some (TAtom "v202")), (Some (40)), "stdout->_IO_write_ptr"); (8%N, (TApp "tmp" [(TAtom "v203")]), (0), (Some 8), false, true, (Some (TAtom "v202")), (Some (40)), "stdout->_IO_write_ptr"); (10%N, (TApp "tmp" [(TAtom "v204")]), (0), (Some 1), false, true, (Some (TAtom "v204")), (Some (0)), "opaque")]); ((TAtom "L184"), []); ((TAtom "L181"), []); ((TAtom "L101"), []); ((TAtom "L212"), []); ((TAtom "L103"), [(1%N, (TApp "tmp" [(TAtom "v12")]), (0), (Some 4), true, false, (Some (TAtom "v12")), (Some (0)), "result->_flags")]); ((TAtom "iw_2.L5"), [(0%N, (TApp "tmp" [(TAtom "v12")]), (0), (Some 4), true, false, (Some (TAtom "v12")), (Some (0)), "result->_flags")]); ((TAtom "iw_2.L19"), [(2%N, (TApp "tmp" [(TAtom "iw_2.v25")]), (0), (Some 1), true, false, (Some (TAtom "iw_2.v25")), (Some (0)), "opaque")]); ((TAtom "iw_2.L28"), [(2%N, (TApp "tmp" [(TAtom "iw_2.v31")]), (0), (Some 8), true, false, (Some (TAtom "v12")), (Some (136)), "result->_lock"); (5%N, (TApp "tmp" [(TAtom "iw_2.v33")]), (0), (Some 4), true, false, (Some (TAtom "iw_2.v32")), (Some (4)), "result->_lock->cnt")]); ((TAtom "iw_2.L29"), []); ((TAtom "iw_2.L22"), [(2%N, (TApp "tmp" [(TAtom "iw_2.v39")]), (0), (Some 8), true, false, (Some (TAtom "v12")), (Some (136)), "result->_lock"); (5%N, (TApp "tmp" [(TAtom "iw_2.v41")]), (0), (Some 8), false, true, (Some (TAtom "iw_2.v40")), (Some (8)), "result->_lock->owner"); (7%N, (TApp "tmp" [(TAtom "iw_2.v39")]), (0), (Some 8), true, false, (Some (TAtom "v12")), (Some (136)), "result->_lock"); (9%N, (TApp "tmp" [(TAtom "iw_2.v44")]), (0), (Some 4), false, true, (Some (TAtom "iw_2.v44")), (Some (0)), "result->_lock->lock")]); ((TAtom "iw_2.L23"), [(2%N, (TApp "tmp" [(TAtom "iw_2.v49")]), (0), (Some 8), true, false, (Some (TAtom "v12")), (Some (136)), "result->_lock"); (5%N, (TApp "tmp" [(TAtom "iw_2.v51")]), (0), (Some 4), true, false, (Some (TAtom "iw_2.v50")), (Some (4)), "result->_lock->cnt")]); ((TAtom "iw_2.L45"), [(1%N, (TApp "tmp" [(TAtom "iw_2.v49")]), (0), (Some 8), true, false, (Some (TAtom "v12")), (Some (136)), "result->_lock"); (4%N, (TApp "tmp" [(TAtom "iw_2.v57")]), (0), (Some 8), false, true, (Some (TAtom "iw_2.v56")), (Some (8)), "result->_lock->owner"); (6%N, (TApp "tmp" [(TAtom "iw_2.v55")]), (0), (Some 8), true, false, (Some (TAtom "v12")), (Some (136)), "result->_lock"); (8%N, (TApp "tmp" [(TAtom "iw_2.v61")]), (0), (Some 4), true, false, (Some (TAtom "iw_2.v61")), (Some (0)), "opaque")]); ((TAtom "iw_2.L66"), [(1%N, (TApp "tmp" [(TAtom "iw_2.v61")]), (0), (Some 4), true, true, (Some (TAtom "iw_2.v61")), (Some (0)), "opaque")]); ((TAtom "iw_2.L67"), []); ((TAtom "iw_2.L78"), []); ((TAtom "iw_2.L46"), [(1%N, (TApp "tmp" [(TAtom "iw_2.v49")]), (0), (Some 8), true, false, (Some (TAtom "v12")), (Some (136)), "result->_lock"); (4%N, (TApp "tmp" [(TAtom "iw_2.v92")]), (0), (Some 4), true, false, (Some (TAtom "iw_2.v91")), (Some (4)), "result->_lock->cnt"); (7%N, (TApp "tmp" [(TAtom "iw_2.v92")]), (0), (Some 4), false, true, (Some (TAtom "iw_2.v91")), (Some (4)), "result->_lock->cnt")]); ((TAtom "L9"), [])].


End fn___GI__IO_puts.

Module fn_glibc_stdfiles__IO_stdfiles_init.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_28, 61%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_28, 66%N)); ((TAtom "L2"), (file_28, 65%N)); ((TAtom "L3"), (file_28, 69%N)); ((TAtom "L5"), (file_28, 61%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "pr.1"), "f"); ((TAtom "v11"), "f"); ((TAtom "v14"), "f"); ((TAtom "v15"), "f"); ((TAtom "v17"), "f"); ((TAtom "v6"), "f")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L2")].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), []); ((TAtom "L2"), []); ((TAtom "L3"), [(TAtom "chk0"); (TAtom "pr.1")]); ((TAtom "L5"), [])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v1")]); ((TAtom "L2"), [(TAtom "chk0"); (TAtom "pr.1")]); ((TAtom "L3"), [(TAtom "v17")]); ((TAtom "L5"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), []); ((TAtom "L2"), [(1%N, (TApp "tmp" [(TAtom "pr.1")]), (0), (Some 8), true, false, (Some (TAtom "pr.1")), (Some (0)), "opaque")]); ((TAtom "L3"), [(0%N, (TApp "tmp" [(TAtom "pr.1")]), (0), (Some 8), true, false, (Some (TAtom "pr.1")), (Some (0)), "opaque"); (3%N, (TApp "tmp" [(TAtom "v13")]), (0), (Some 8), false, true, (Some (TAtom "v12")), (Some (184)), "(*f)->_prevchain"); (5%N, (TApp "tmp" [(TAtom "pr.1")]), (0), (Some 8), true, false, (Some (TAtom "pr.1")), (Some (0)), "opaque")]); ((TAtom "L5"), [])].


End fn_glibc_stdfiles__IO_stdfiles_init.

Module fn__IO_vtable_check.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_30, 507%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_30, 510%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), [])].


End fn__IO_vtable_check.

Module fn_glibc_vtables_check_stdfiles_vtables.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_30, 518%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_30, 522%N)); ((TAtom "L11"), (file_30, 522%N)); ((TAtom "L12"), (file_30, 522%N)); ((TAtom "L23"), (file_30, 522%N)); ((TAtom "L24"), (file_30, 522%N)); ((TAtom "L0"), (file_30, 525%N)); ((TAtom "L2"), (file_30, 518%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "flag"); ((TAtom "iw_1.v2"), "flag"); ((TAtom "iw_1.v7"), "flag")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), []); ((TAtom "L11"), []); ((TAtom "L12"), []); ((TAtom "L23"), []); ((TAtom "L24"), []); ((TAtom "L0"), []); ((TAtom "L2"), [])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), []); ((TAtom "L11"), [(TAtom "v20")]); ((TAtom "L12"), []); ((TAtom "L23"), [(TAtom "v32")]); ((TAtom "L24"), []); ((TAtom "L0"), []); ((TAtom "L2"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), [(3%N, (TApp "tmp" [(TAtom "v4")]), (0), (Some 8), true, false, (Some (TAtom "v3")), (Some (216)), "_IO_2_1_stdin_.vtable")]); ((TAtom "L11"), [(3%N, (TApp "tmp" [(TAtom "v14")]), (0), (Some 8), true, false, (Some (TAtom "v13")), (Some (216)), "_IO_2_1_stdout_.vtable")]); ((TAtom "L12"), []); ((TAtom "L23"), [(3%N, (TApp "tmp" [(TAtom "v26")]), (0), (Some 8), true, false, (Some (TAtom "v25")), (Some (216)), "_IO_2_1_stderr_.vtable")]); ((TAtom "L24"), []); ((TAtom "L0"), [(3%N, (TApp "tmp" [(TAtom "iw_1.v6")]), (0), (Some 8), false, true, (Some (TAtom "iw_1.v6")), (Some (0)), "opaque")]); ((TAtom "L2"), [])].


End fn_glibc_vtables_check_stdfiles_vtables.

Module fn___isatty_nostatus.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_6, 22%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_6, 25%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fd"); ((TAtom "v3"), "fd")].

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

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
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

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
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

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
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

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), [(4%N, (TApp "tmp" [(TAtom "v17")]), (0), (Some 8), true, false, (Some (TAtom "v16")), (Some (8)), "__exit_lock.owner")]); ((TAtom "L13"), [(2%N, (TApp "tmp" [(TAtom "v24")]), (0), (Some 4), true, true, (Some (TAtom "v24")), (Some (0)), "__exit_lock.lock")]); ((TAtom "L33"), []); ((TAtom "L34"), []); ((TAtom "L38"), []); ((TAtom "L27"), [(3%N, (TApp "tmp" [(TAtom "v49")]), (0), (Some 8), false, true, (Some (TAtom "v48")), (Some (8)), "__exit_lock.owner")]); ((TAtom "L15"), [(3%N, (TApp "tmp" [(TAtom "v52")]), (0), (Some 4), true, false, (Some (TAtom "v51")), (Some (4)), "__exit_lock.cnt"); (6%N, (TApp "tmp" [(TAtom "v52")]), (0), (Some 4), false, true, (Some (TAtom "v51")), (Some (4)), "__exit_lock.cnt")]); ((TAtom "L55"), []); ((TAtom "L57"), [(2%N, (TApp "tmp" [(TAtom "v60")]), (0), (Some 4), true, true, (Some (TAtom "v60")), (Some (0)), "opaque")]); ((TAtom "L69"), []); ((TAtom "L70"), []); ((TAtom "L74"), []); ((TAtom "L88"), [(1%N, (TApp "tmp" [(TAtom "v2")]), (0), (Some 8), true, false, (Some (TAtom "v2")), (Some (0)), "opaque")]); ((TAtom "L91"), [(2%N, (TApp "tmp" [(TAtom "v98")]), (0), (Some 1), false, true, (Some (TAtom "v98")), (Some (0)), "opaque"); (5%N, (TApp "tmp" [(TAtom "v360")]), (0), (Some 4), true, false, (Some (TAtom "v360")), (Some (0)), "opaque")]); ((TAtom "L101"), [(2%N, (TApp "tmp" [(TAtom "v105")]), (0), (Some 8), true, false, (Some (TAtom "v90")), (Some (8)), "cur->idx")]); ((TAtom "L102"), [(2%N, (TApp "tmp" [(TAtom "v105")]), (0), (Some 8), true, false, (Some (TAtom "v90")), (Some (8)), "cur->idx"); (5%N, (TApp "tmp" [(TAtom "v112")]), (0), (Some 8), false, true, (Some (TAtom "v90")), (Some (8)), "cur->idx"); (10%N, (TApp "tmp" [(TAtom "v118")]), (0), (Some 8), true, false, (Some (TAtom "v118")), (Some (0)), "opaque"); (12%N, (TApp "tmp" [(TAtom "v116")]), (0), (Some 8), true, false, (Some (TAtom "v90")), None, "f->flavor")]); ((TAtom "L130"), [(2%N, (TApp "tmp" [(TAtom "v132")]), (0), (Some 8), true, false, (Some (TAtom "v90")), None, "opaque"); (5%N, (TApp "tmp" [(TAtom "v136")]), (0), (Some 8), true, false, (Some (TAtom "v90")), None, "f->func.on.arg"); (8%N, (TApp "tmp" [(TAtom "v140")]), (0), (Some 4), true, false, (Some (TAtom "v140")), (Some (0)), "opaque")]); ((TAtom "L145"), [(1%N, (TApp "tmp" [(TAtom "v140")]), (0), (Some 4), true, true, (Some (TAtom "v140")), (Some (0)), "opaque")]); ((TAtom "L146"), []); ((TAtom "L157"), []); ((TAtom "L152"), [(4%N, (TApp "tmp" [(TAtom "v172")]), (0), (Some 4), true, true, (Some (TAtom "v172")), (Some (0)), "opaque")]); ((TAtom "L181"), []); ((TAtom "L182"), []); ((TAtom "L186"), []); ((TAtom "L196"), [(2%N, (TApp "tmp" [(TAtom "v198")]), (0), (Some 8), true, false, (Some (TAtom "v90")), None, "opaque"); (5%N, (TApp "tmp" [(TAtom "v202")]), (0), (Some 4), true, false, (Some (TAtom "v202")), (Some (0)), "opaque")]); ((TAtom "L207"), [(1%N, (TApp "tmp" [(TAtom "v202")]), (0), (Some 4), true, true, (Some (TAtom "v202")), (Some (0)), "opaque")]); ((TAtom "L208"), []); ((TAtom "L219"), []); ((TAtom "L214"), [(4%N, (TApp "tmp" [(TAtom "v232")]), (0), (Some 4), true, true, (Some (TAtom "v232")), (Some (0)), "opaque")]); ((TAtom "L241"), []); ((TAtom "L242"), []); ((TAtom "L246"), []); ((TAtom "L256"), [(1%N, (TApp "tmp" [(TAtom "v116")]), (0), (Some 8), false, true, (Some (TAtom "v90")), None, "f->flavor"); (4%N, (TApp "tmp" [(TAtom "v259")]), (0), (Some 8), true, false, (Some (TAtom "v90")), None, "opaque"); (7%N, (TApp "tmp" [(TAtom "v263")]), (0), (Some 8), true, false, (Some (TAtom "v90")), None, "f->func.cxa.arg"); (10%N, (TApp "tmp" [(TAtom "v267")]), (0), (Some 4), true, false, (Some (TAtom "v267")), (Some (0)), "opaque")]); ((TAtom "L272"), [(1%N, (TApp "tmp" [(TAtom "v267")]), (0), (Some 4), true, true, (Some (TAtom "v267")), (Some (0)), "opaque")]); ((TAtom "L273"), []); ((TAtom "L284"), []); ((TAtom "L279"), [(4%N, (TApp "tmp" [(TAtom "v299")]), (0), (Some 4), true, true, (Some (TAtom "v299")), (Some (0)), "opaque")]); ((TAtom "L308"), []); ((TAtom "L309"), []); ((TAtom "L313"), []); ((TAtom "L325"), []); ((TAtom "L328"), []); ((TAtom "L330"), []); ((TAtom "L326"), []); ((TAtom "L332"), []); ((TAtom "L334"), []); ((TAtom "L123"), [(2%N, (TApp "tmp" [(TAtom "v341")]), (0), (Some 8), true, false, (Some (TAtom "v341")), (Some (0)), "opaque")]); ((TAtom "L103"), [(1%N, (TApp "tmp" [(TAtom "v90")]), (0), (Some 8), true, false, (Some (TAtom "v90")), (Some (0)), "cur->next"); (3%N, (TApp "tmp" [(TAtom "v2")]), (0), (Some 8), false, true, (Some (TAtom "v2")), (Some (0)), "opaque"); (5%N, (TApp "tmp" [(TAtom "v2")]), (0), (Some 8), true, false, (Some (TAtom "v2")), (Some (0)), "opaque")]); ((TAtom "L350"), []); ((TAtom "L365"), [(1%N, (TApp "tmp" [(TAtom "v360")]), (0), (Some 4), true, true, (Some (TAtom "v360")), (Some (0)), "opaque")]); ((TAtom "L366"), []); ((TAtom "L377"), []); ((TAtom "L372"), []); ((TAtom "L388"), []); ((TAtom "L390"), [])].


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

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
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

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
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

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), [(4%N, (TApp "tmp" [(TAtom "v7")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (24)), "buffer->__prev"); (6%N, (TApp "tmp" [(TAtom "v5")]), (0), (Some 8), false, true, (Some (TAtom "v3")), (Some (776)), "self->cleanup"); (9%N, (TApp "tmp" [(TAtom "v11")]), (0), (Some 4), true, false, (Some (TAtom "v3")), (Some (792)), "self->cancelhandling"); (12%N, (TApp "tmp" [(TAtom "v17")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (16)), "buffer->__canceltype")]); ((TAtom "L20"), []); ((TAtom "L21"), []); ((TAtom "L29"), [(3%N, (TApp "tmp" [(TAtom "v36")]), (0), (Some 4), true, true, (Some (TAtom "v3")), (Some (792)), "self->cancelhandling")]); ((TAtom "L41"), []); ((TAtom "L42"), []); ((TAtom "iw_1.start"), []); ((TAtom "L44"), [(4%N, (TApp "tmp" [(TAtom "iw_2.v5")]), (0), (Some 8), false, true, (Some (TAtom "iw_2.v3")), (Some (1608)), "self->result"); (7%N, (TApp "tmp" [(TAtom "iw_2.v9")]), (0), (Some 4), true, false, (Some (TAtom "iw_2.v3")), (Some (792)), "self->cancelhandling")]); ((TAtom "iw_2.L12"), []); ((TAtom "iw_2.L13"), [(2%N, (TApp "tmp" [(TAtom "iw_2.v32")]), (0), (Some 4), true, true, (Some (TAtom "iw_2.v3")), (Some (792)), "self->cancelhandling")]); ((TAtom "iw_2.L37"), []); ((TAtom "iw_2.L38"), []); ((TAtom "iw_2.L14"), [(2%N, (TApp "tmp" [(TAtom "iw_2.v41")]), (0), (Some 8), true, false, (Some (TAtom "iw_2.v3")), (Some (784)), "self->cleanup_jmp_buf")]); ((TAtom "L15"), [])].


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

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), [])].


End fn___gnu_dev_major.

End HiAtexitSrc07.
