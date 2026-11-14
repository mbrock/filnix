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
Module HiAtexitSrc06.

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


Definition live_in : list (name * list name) :=
  [((TAtom "start"), []); ((TAtom "iw_1.L23"), [(TAtom "iw_1.v16"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L24"), [(TAtom "iw_1.v16"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L17"), [(TAtom "iw_1.v16"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L18"), [(TAtom "iw_1.v16"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L37"), [(TAtom "iw_1.v16"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L57"), [(TAtom "iw_1.v16"); (TAtom "iw_1.v2"); (TAtom "iw_1.v48"); (TAtom "iw_1.v55"); (TAtom "v1")]); ((TAtom "iw_1.L58"), [(TAtom "iw_1.v16"); (TAtom "iw_1.v2"); (TAtom "iw_1.v48"); (TAtom "iw_1.v55"); (TAtom "v1")]); ((TAtom "iw_1.L62"), [(TAtom "iw_1.v16"); (TAtom "iw_1.v2"); (TAtom "iw_1.v48"); (TAtom "v1")]); ((TAtom "iw_1.L51"), [(TAtom "iw_1.v16"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L38"), [(TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L14"), [(TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L81"), [(TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L82"), [(TAtom "iw_1.pr.1"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L98"), [(TAtom "chk13"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L109"), [(TAtom "chk13"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v102"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L110"), [(TAtom "chk13"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v102"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L103"), [(TAtom "chk13"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v102"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L104"), [(TAtom "chk13"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v102"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L129"), [(TAtom "chk13"); (TAtom "chk21"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v102"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L153"), [(TAtom "chk13"); (TAtom "chk21"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v102"); (TAtom "iw_1.v144"); (TAtom "iw_1.v151"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L154"), [(TAtom "chk13"); (TAtom "chk21"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v102"); (TAtom "iw_1.v144"); (TAtom "iw_1.v151"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L158"), [(TAtom "chk13"); (TAtom "chk21"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v102"); (TAtom "iw_1.v144"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L147"), [(TAtom "chk13"); (TAtom "chk21"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v102"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L130"), [(TAtom "chk13"); (TAtom "chk21"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L93"), [(TAtom "chk13"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L179"), [(TAtom "chk13"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v186"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L194"), [(TAtom "chk13"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v186"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L202"), [(TAtom "chk13"); (TAtom "chk31"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v186"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L203"), [(TAtom "chk13"); (TAtom "chk31"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L189"), [(TAtom "chk13"); (TAtom "chk31"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L191"), [(TAtom "chk13"); (TAtom "chk31"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L225"), [(TAtom "chk13"); (TAtom "chk31"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L223"), [(TAtom "chk13"); (TAtom "chk31"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L240"), [(TAtom "chk13"); (TAtom "chk31"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L247"), [(TAtom "chk13"); (TAtom "chk31"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L248"), [(TAtom "chk13"); (TAtom "chk31"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L235"), [(TAtom "chk13"); (TAtom "chk31"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L237"), [(TAtom "chk13"); (TAtom "chk31"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.iw_1.L10"), [(TAtom "chk13"); (TAtom "chk31"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v2"); (TAtom "iw_1.v271"); (TAtom "v1")]); ((TAtom "iw_1.iw_1.join"), [(TAtom "chk13"); (TAtom "chk31"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v2"); (TAtom "iw_1.v271"); (TAtom "v1")]); ((TAtom "iw_1.L277"), [(TAtom "chk13"); (TAtom "chk31"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L291"), [(TAtom "chk13"); (TAtom "chk31"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L306"), [(TAtom "chk13"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L315"), [(TAtom "chk13"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L316"), [(TAtom "chk13"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L309"), [(TAtom "chk13"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L310"), [(TAtom "chk13"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L332"), [(TAtom "chk13"); (TAtom "chk58"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L353"), [(TAtom "chk13"); (TAtom "chk63"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v2"); (TAtom "iw_1.v348"); (TAtom "v1")]); ((TAtom "iw_1.L354"), [(TAtom "chk13"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v2"); (TAtom "iw_1.v348"); (TAtom "iw_1.v355"); (TAtom "v1")]); ((TAtom "iw_1.L365"), [(TAtom "chk13"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v2"); (TAtom "iw_1.v348"); (TAtom "v1")]); ((TAtom "iw_1.L333"), [(TAtom "chk13"); (TAtom "chk58"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L301"), [(TAtom "chk13"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L386"), [(TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L395"), [(TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L396"), [(TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L389"), [(TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L390"), [(TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L406"), [(TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L421"), [(TAtom "chk76"); (TAtom "iw_1.v2"); (TAtom "iw_1.v416"); (TAtom "v1")]); ((TAtom "iw_1.L422"), [(TAtom "iw_1.v2"); (TAtom "iw_1.v416"); (TAtom "iw_1.v423"); (TAtom "v1")]); ((TAtom "iw_1.L433"), [(TAtom "iw_1.v2"); (TAtom "iw_1.v416"); (TAtom "v1")]); ((TAtom "iw_1.L407"), [(TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L448"), [(TAtom "iw_1.v2"); (TAtom "v1")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "iw_1.v16"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L23"), [(TAtom "iw_1.v16"); (TAtom "iw_1.v2"); (TAtom "iw_1.v30"); (TAtom "v1")]); ((TAtom "iw_1.L24"), [(TAtom "iw_1.v16"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L17"), [(TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L18"), [(TAtom "iw_1.v16"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L37"), [(TAtom "iw_1.v16"); (TAtom "iw_1.v2"); (TAtom "iw_1.v48"); (TAtom "iw_1.v55"); (TAtom "v1")]); ((TAtom "iw_1.L57"), [(TAtom "iw_1.v16"); (TAtom "iw_1.v2"); (TAtom "iw_1.v48"); (TAtom "iw_1.v55"); (TAtom "v1")]); ((TAtom "iw_1.L58"), [(TAtom "iw_1.v16"); (TAtom "iw_1.v2"); (TAtom "iw_1.v48"); (TAtom "v1")]); ((TAtom "iw_1.L62"), [(TAtom "iw_1.v16"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L51"), [(TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L38"), [(TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L14"), [(TAtom "iw_1.v2"); (TAtom "iw_1.v80"); (TAtom "v1")]); ((TAtom "iw_1.L81"), [(TAtom "iw_1.pr.1"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L82"), [(TAtom "chk13"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L98"), [(TAtom "chk13"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v102"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L109"), [(TAtom "chk13"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v102"); (TAtom "iw_1.v118"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L110"), [(TAtom "chk13"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v102"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L103"), [(TAtom "chk13"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L104"), [(TAtom "chk13"); (TAtom "chk21"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v102"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L129"), [(TAtom "chk13"); (TAtom "chk21"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v102"); (TAtom "iw_1.v144"); (TAtom "iw_1.v151"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L153"), [(TAtom "chk13"); (TAtom "chk21"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v102"); (TAtom "iw_1.v144"); (TAtom "iw_1.v151"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L154"), [(TAtom "chk13"); (TAtom "chk21"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v102"); (TAtom "iw_1.v144"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L158"), [(TAtom "chk13"); (TAtom "chk21"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v102"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L147"), [(TAtom "chk13"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L130"), [(TAtom "chk13"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L93"), [(TAtom "chk13"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v186"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L179"), [(TAtom "chk13"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v186"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L194"), [(TAtom "chk13"); (TAtom "chk31"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v186"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L202"), [(TAtom "chk13"); (TAtom "chk31"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v2"); (TAtom "iw_1.v211"); (TAtom "v1")]); ((TAtom "iw_1.L203"), [(TAtom "chk13"); (TAtom "chk31"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L189"), [(TAtom "chk13"); (TAtom "chk31"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L191"), [(TAtom "chk13"); (TAtom "chk31"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L225"), [(TAtom "chk13"); (TAtom "chk31"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v2"); (TAtom "iw_1.v230"); (TAtom "v1")]); ((TAtom "iw_1.L223"), [(TAtom "chk13"); (TAtom "chk31"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L240"), [(TAtom "chk13"); (TAtom "chk31"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L247"), [(TAtom "chk13"); (TAtom "chk31"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v2"); (TAtom "iw_1.v252"); (TAtom "v1")]); ((TAtom "iw_1.L248"), [(TAtom "chk13"); (TAtom "chk31"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L235"), [(TAtom "chk13"); (TAtom "chk31"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L237"), [(TAtom "chk13"); (TAtom "chk31"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v2"); (TAtom "iw_1.v271"); (TAtom "v1")]); ((TAtom "iw_1.iw_1.L10"), [(TAtom "chk13"); (TAtom "chk31"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v2"); (TAtom "iw_1.v271"); (TAtom "v1")]); ((TAtom "iw_1.iw_1.join"), [(TAtom "chk13"); (TAtom "chk31"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L277"), [(TAtom "chk13"); (TAtom "chk31"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L291"), [(TAtom "chk13"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L306"), [(TAtom "chk13"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L315"), [(TAtom "chk13"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v2"); (TAtom "iw_1.v322"); (TAtom "v1")]); ((TAtom "iw_1.L316"), [(TAtom "chk13"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L309"), [(TAtom "chk13"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L310"), [(TAtom "chk13"); (TAtom "chk58"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L332"), [(TAtom "chk13"); (TAtom "chk63"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v2"); (TAtom "iw_1.v348"); (TAtom "iw_1.v352"); (TAtom "v1")]); ((TAtom "iw_1.L353"), [(TAtom "chk13"); (TAtom "chk63"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v2"); (TAtom "iw_1.v348"); (TAtom "iw_1.v355"); (TAtom "iw_1.v356"); (TAtom "v1")]); ((TAtom "iw_1.L354"), [(TAtom "chk13"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v2"); (TAtom "iw_1.v348"); (TAtom "v1")]); ((TAtom "iw_1.L365"), [(TAtom "chk13"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L333"), [(TAtom "chk13"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L301"), [(TAtom "iw_1.v2"); (TAtom "iw_1.v385"); (TAtom "v1")]); ((TAtom "iw_1.L386"), [(TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L395"), [(TAtom "iw_1.v2"); (TAtom "iw_1.v400"); (TAtom "v1")]); ((TAtom "iw_1.L396"), [(TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L389"), [(TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L390"), [(TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L406"), [(TAtom "chk76"); (TAtom "iw_1.v2"); (TAtom "iw_1.v416"); (TAtom "iw_1.v420"); (TAtom "v1")]); ((TAtom "iw_1.L421"), [(TAtom "chk76"); (TAtom "iw_1.v2"); (TAtom "iw_1.v416"); (TAtom "iw_1.v423"); (TAtom "iw_1.v424"); (TAtom "v1")]); ((TAtom "iw_1.L422"), [(TAtom "iw_1.v2"); (TAtom "iw_1.v416"); (TAtom "v1")]); ((TAtom "iw_1.L433"), [(TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L407"), [(TAtom "iw_1.v2"); (TAtom "v1")]); ((TAtom "iw_1.L448"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [(5%N, (TApp "tmp" [(TAtom "iw_1.v5")]), (0), (Some 8), false, true, (Some (TAtom "iw_1.v2")), (Some (8))); (7%N, (TApp "tmp" [(TAtom "iw_1.v2")]), (0), (Some 8), false, true, (Some (TAtom "iw_1.v2")), (Some (0))); (12%N, (TApp "tmp" [(TAtom "iw_1.v20")]), (0), (Some 1), true, false, (Some (TAtom "iw_1.v20")), (Some (0)))]); ((TAtom "iw_1.L23"), [(3%N, (TApp "tmp" [(TAtom "iw_1.v26")]), (0), (Some 8), true, false, (Some (TAtom "iw_1.v25")), (Some (8)))]); ((TAtom "iw_1.L24"), []); ((TAtom "iw_1.L17"), [(2%N, (TApp "tmp" [(TAtom "iw_1.v33")]), (0), (Some 4), false, true, (Some (TAtom "iw_1.v33")), (Some (0))); (6%N, (TApp "tmp" [(TAtom "iw_1.v35")]), (0), (Some 8), false, true, (Some (TAtom "iw_1.v34")), (Some (8)))]); ((TAtom "iw_1.L18"), [(3%N, (TApp "tmp" [(TAtom "iw_1.v41")]), (0), (Some 8), true, false, (Some (TAtom "iw_1.v40")), (Some (8)))]); ((TAtom "iw_1.L37"), [(2%N, (TApp "tmp" [(TAtom "iw_1.v48")]), (0), (Some 4), true, true, (Some (TAtom "iw_1.v48")), (Some (0)))]); ((TAtom "iw_1.L57"), []); ((TAtom "iw_1.L58"), []); ((TAtom "iw_1.L62"), []); ((TAtom "iw_1.L51"), [(3%N, (TApp "tmp" [(TAtom "iw_1.v73")]), (0), (Some 8), false, true, (Some (TAtom "iw_1.v72")), (Some (8)))]); ((TAtom "iw_1.L38"), [(3%N, (TApp "tmp" [(TAtom "iw_1.v76")]), (0), (Some 4), true, false, (Some (TAtom "iw_1.v75")), (Some (4))); (6%N, (TApp "tmp" [(TAtom "iw_1.v76")]), (0), (Some 4), false, true, (Some (TAtom "iw_1.v75")), (Some (4)))]); ((TAtom "iw_1.L14"), [(2%N, (TApp "tmp" [(TAtom "iw_1.v79")]), (0), (Some 8), true, false, (Some (TAtom "iw_1.v79")), (Some (0)))]); ((TAtom "iw_1.L81"), []); ((TAtom "iw_1.L82"), [(2%N, (TApp "tmp" [(TAtom "iw_1.v89")]), (0), (Some 8), false, true, (Some (TAtom "iw_1.v89")), (Some (0))); (4%N, (TApp "tmp" [(TAtom "iw_1.pr.1")]), (0), (Some 4), true, false, (Some (TAtom "iw_1.pr.1")), (Some (0)))]); ((TAtom "iw_1.L98"), [(3%N, (TApp "tmp" [(TAtom "iw_1.v106")]), (0), (Some 1), true, false, (Some (TAtom "iw_1.v106")), (Some (0)))]); ((TAtom "iw_1.L109"), [(2%N, (TApp "tmp" [(TAtom "iw_1.v112")]), (0), (Some 8), true, false, (Some (TAtom "iw_1.pr.1")), (Some (136))); (5%N, (TApp "tmp" [(TAtom "iw_1.v114")]), (0), (Some 8), true, false, (Some (TAtom "iw_1.v113")), (Some (8)))]); ((TAtom "iw_1.L110"), []); ((TAtom "iw_1.L103"), [(2%N, (TApp "tmp" [(TAtom "iw_1.v122")]), (0), (Some 8), true, false, (Some (TAtom "iw_1.pr.1")), (Some (136))); (4%N, (TApp "tmp" [(TAtom "iw_1.v123")]), (0), (Some 4), false, true, (Some (TAtom "iw_1.v123")), (Some (0))); (5%N, (TApp "tmp" [(TAtom "iw_1.v122")]), (0), (Some 8), true, false, (Some (TAtom "iw_1.pr.1")), (Some (136))); (8%N, (TApp "tmp" [(TAtom "iw_1.v127")]), (0), (Some 8), false, true, (Some (TAtom "iw_1.v126")), (Some (8)))]); ((TAtom "iw_1.L104"), [(2%N, (TApp "tmp" [(TAtom "iw_1.v133")]), (0), (Some 8), true, false, (Some (TAtom "iw_1.pr.1")), (Some (136))); (5%N, (TApp "tmp" [(TAtom "iw_1.v135")]), (0), (Some 8), true, false, (Some (TAtom "iw_1.v134")), (Some (8)))]); ((TAtom "iw_1.L129"), [(1%N, (TApp "tmp" [(TAtom "iw_1.v133")]), (0), (Some 8), true, false, (Some (TAtom "iw_1.pr.1")), (Some (136))); (3%N, (TApp "tmp" [(TAtom "iw_1.v144")]), (0), (Some 4), true, true, (Some (TAtom "iw_1.v144")), (Some (0)))]); ((TAtom "iw_1.L153"), []); ((TAtom "iw_1.L154"), []); ((TAtom "iw_1.L158"), []); ((TAtom "iw_1.L147"), [(2%N, (TApp "tmp" [(TAtom "iw_1.v169")]), (0), (Some 8), true, false, (Some (TAtom "iw_1.pr.1")), (Some (136))); (5%N, (TApp "tmp" [(TAtom "iw_1.v171")]), (0), (Some 8), false, true, (Some (TAtom "iw_1.v170")), (Some (8)))]); ((TAtom "iw_1.L130"), [(1%N, (TApp "tmp" [(TAtom "iw_1.v133")]), (0), (Some 8), true, false, (Some (TAtom "iw_1.pr.1")), (Some (136))); (4%N, (TApp "tmp" [(TAtom "iw_1.v176")]), (0), (Some 4), true, false, (Some (TAtom "iw_1.v175")), (Some (4))); (7%N, (TApp "tmp" [(TAtom "iw_1.v176")]), (0), (Some 4), false, true, (Some (TAtom "iw_1.v175")), (Some (4)))]); ((TAtom "iw_1.L93"), [(2%N, (TApp "tmp" [(TAtom "iw_1.v183")]), (0), (Some 8), true, false, (Some (TAtom "iw_1.pr.1")), (Some (80)))]); ((TAtom "iw_1.L179"), []); ((TAtom "iw_1.L194"), [(2%N, (TApp "tmp" [(TAtom "iw_1.v197")]), (0), (Some 4), true, false, (Some (TAtom "iw_1.pr.1")), (Some (192)))]); ((TAtom "iw_1.L202"), [(2%N, (TApp "tmp" [(TAtom "iw_1.v205")]), (0), (Some 8), true, false, (Some (TAtom "iw_1.pr.1")), (Some (160))); (5%N, (TApp "tmp" [(TAtom "iw_1.v207")]), (0), (Some 8), true, false, (Some (TAtom "iw_1.v206")), (Some (72)))]); ((TAtom "iw_1.L203"), []); ((TAtom "iw_1.L189"), []); ((TAtom "iw_1.L191"), [(1%N, (TApp "tmp" [(TAtom "iw_1.pr.1")]), (0), (Some 4), true, false, (Some (TAtom "iw_1.pr.1")), (Some (0)))]); ((TAtom "iw_1.L225"), [(2%N, (TApp "tmp" [(TAtom "iw_1.v228")]), (0), (Some 4), true, false, (Some (TAtom "iw_1.pr.1")), (Some (192)))]); ((TAtom "iw_1.L223"), []); ((TAtom "iw_1.L240"), [(2%N, (TApp "tmp" [(TAtom "iw_1.v242")]), (0), (Some 1), true, false, (Some (TAtom "iw_1.v242")), (Some (0)))]); ((TAtom "iw_1.L247"), [(1%N, (TApp "tmp" [(TAtom "iw_1.pr.1")]), (0), (Some 4), true, false, (Some (TAtom "iw_1.pr.1")), (Some (0)))]); ((TAtom "iw_1.L248"), []); ((TAtom "iw_1.L235"), [(1%N, (TApp "tmp" [(TAtom "iw_1.pr.1")]), (0), (Some 4), true, false, (Some (TAtom "iw_1.pr.1")), (Some (0))); (4%N, (TApp "tmp" [(TAtom "iw_1.pr.1")]), (0), (Some 4), false, true, (Some (TAtom "iw_1.pr.1")), (Some (0))); (8%N, (TApp "tmp" [(TAtom "iw_1.v260")]), (0), (Some 8), true, false, (Some (TAtom "iw_1.v260")), (Some (0))); (10%N, (TApp "tmp" [(TAtom "iw_1.v259")]), (0), (Some 8), false, true, (Some (TAtom "iw_1.pr.1")), (Some (168))); (13%N, (TApp "tmp" [(TAtom "iw_1.v262")]), (0), (Some 8), false, true, (Some (TAtom "iw_1.v262")), (Some (0))); (17%N, (TApp "tmp" [(TAtom "iw_1.v267")]), (0), (Some 8), true, false, (Some (TAtom "iw_1.pr.1")), (Some (56))); (19%N, (TApp "tmp" [(TAtom "iw_1.v265")]), (0), (Some 8), false, true, (Some (TAtom "iw_1.pr.1")), (Some (176)))]); ((TAtom "iw_1.L237"), [(2%N, (TApp "tmp" [(TAtom "iw_1.v270")]), (0), (Some 8), true, false, (Some (TAtom "iw_1.pr.1")), (Some (216)))]); ((TAtom "iw_1.iw_1.L10"), []); ((TAtom "iw_1.iw_1.join"), [(2%N, (TApp "tmp" [(TAtom "iw_1.v273")]), (0), (Some 8), true, false, (Some (TAtom "iw_1.v271")), (Some (88))); (7%N, (TApp "tmp" [(TAtom "iw_1.v285")]), (0), (Some 4), true, false, (Some (TAtom "iw_1.pr.1")), (Some (192)))]); ((TAtom "iw_1.L277"), []); ((TAtom "iw_1.L291"), [(2%N, (TApp "tmp" [(TAtom "iw_1.v297")]), (0), (Some 4), false, true, (Some (TAtom "iw_1.pr.1")), (Some (192))); (4%N, (TApp "tmp" [(TAtom "iw_1.pr.1")]), (0), (Some 4), true, false, (Some (TAtom "iw_1.pr.1")), (Some (0)))]); ((TAtom "iw_1.L306"), [(2%N, (TApp "tmp" [(TAtom "iw_1.v312")]), (0), (Some 1), true, false, (Some (TAtom "iw_1.v312")), (Some (0)))]); ((TAtom "iw_1.L315"), [(2%N, (TApp "tmp" [(TAtom "iw_1.v318")]), (0), (Some 8), true, false, (Some (TAtom "iw_1.pr.1")), (Some (136))); (5%N, (TApp "tmp" [(TAtom "iw_1.v320")]), (0), (Some 4), true, false, (Some (TAtom "iw_1.v319")), (Some (4)))]); ((TAtom "iw_1.L316"), []); ((TAtom "iw_1.L309"), [(2%N, (TApp "tmp" [(TAtom "iw_1.v326")]), (0), (Some 8), true, false, (Some (TAtom "iw_1.pr.1")), (Some (136))); (5%N, (TApp "tmp" [(TAtom "iw_1.v328")]), (0), (Some 8), false, true, (Some (TAtom "iw_1.v327")), (Some (8))); (7%N, (TApp "tmp" [(TAtom "iw_1.v326")]), (0), (Some 8), true, false, (Some (TAtom "iw_1.pr.1")), (Some (136))); (9%N, (TApp "tmp" [(TAtom "iw_1.v331")]), (0), (Some 4), false, true, (Some (TAtom "iw_1.v331")), (Some (0)))]); ((TAtom "iw_1.L310"), [(2%N, (TApp "tmp" [(TAtom "iw_1.v336")]), (0), (Some 8), true, false, (Some (TAtom "iw_1.pr.1")), (Some (136))); (5%N, (TApp "tmp" [(TAtom "iw_1.v338")]), (0), (Some 4), true, false, (Some (TAtom "iw_1.v337")), (Some (4)))]); ((TAtom "iw_1.L332"), [(1%N, (TApp "tmp" [(TAtom "iw_1.v336")]), (0), (Some 8), true, false, (Some (TAtom "iw_1.pr.1")), (Some (136))); (4%N, (TApp "tmp" [(TAtom "iw_1.v344")]), (0), (Some 8), false, true, (Some (TAtom "iw_1.v343")), (Some (8))); (6%N, (TApp "tmp" [(TAtom "iw_1.v342")]), (0), (Some 8), true, false, (Some (TAtom "iw_1.pr.1")), (Some (136))); (8%N, (TApp "tmp" [(TAtom "iw_1.v348")]), (0), (Some 4), true, false, (Some (TAtom "iw_1.v348")), (Some (0)))]); ((TAtom "iw_1.L353"), [(1%N, (TApp "tmp" [(TAtom "iw_1.v348")]), (0), (Some 4), true, true, (Some (TAtom "iw_1.v348")), (Some (0)))]); ((TAtom "iw_1.L354"), []); ((TAtom "iw_1.L365"), []); ((TAtom "iw_1.L333"), [(1%N, (TApp "tmp" [(TAtom "iw_1.v336")]), (0), (Some 8), true, false, (Some (TAtom "iw_1.pr.1")), (Some (136))); (4%N, (TApp "tmp" [(TAtom "iw_1.v379")]), (0), (Some 4), true, false, (Some (TAtom "iw_1.v378")), (Some (4))); (7%N, (TApp "tmp" [(TAtom "iw_1.v379")]), (0), (Some 4), false, true, (Some (TAtom "iw_1.v378")), (Some (4)))]); ((TAtom "iw_1.L301"), [(2%N, (TApp "tmp" [(TAtom "iw_1.v382")]), (0), (Some 8), false, true, (Some (TAtom "iw_1.v382")), (Some (0))); (5%N, (TApp "tmp" [(TAtom "iw_1.v384")]), (0), (Some 8), true, false, (Some (TAtom "iw_1.pr.1")), (Some (104)))]); ((TAtom "iw_1.L386"), [(2%N, (TApp "tmp" [(TAtom "iw_1.v392")]), (0), (Some 1), true, false, (Some (TAtom "iw_1.v392")), (Some (0)))]); ((TAtom "iw_1.L395"), [(3%N, (TApp "tmp" [(TAtom "iw_1.v398")]), (0), (Some 4), true, false, (Some (TAtom "iw_1.v397")), (Some (4)))]); ((TAtom "iw_1.L396"), []); ((TAtom "iw_1.L389"), [(3%N, (TApp "tmp" [(TAtom "iw_1.v404")]), (0), (Some 8), false, true, (Some (TAtom "iw_1.v403")), (Some (8))); (6%N, (TApp "tmp" [(TAtom "iw_1.v405")]), (0), (Some 4), false, true, (Some (TAtom "iw_1.v405")), (Some (0)))]); ((TAtom "iw_1.L390"), [(3%N, (TApp "tmp" [(TAtom "iw_1.v410")]), (0), (Some 4), true, false, (Some (TAtom "iw_1.v409")), (Some (4)))]); ((TAtom "iw_1.L406"), [(3%N, (TApp "tmp" [(TAtom "iw_1.v414")]), (0), (Some 8), false, true, (Some (TAtom "iw_1.v413")), (Some (8))); (6%N, (TApp "tmp" [(TAtom "iw_1.v416")]), (0), (Some 4), true, false, (Some (TAtom "iw_1.v416")), (Some (0)))]); ((TAtom "iw_1.L421"), [(1%N, (TApp "tmp" [(TAtom "iw_1.v416")]), (0), (Some 4), true, true, (Some (TAtom "iw_1.v416")), (Some (0)))]); ((TAtom "iw_1.L422"), []); ((TAtom "iw_1.L433"), []); ((TAtom "iw_1.L407"), [(3%N, (TApp "tmp" [(TAtom "iw_1.v445")]), (0), (Some 4), true, false, (Some (TAtom "iw_1.v444")), (Some (4))); (6%N, (TApp "tmp" [(TAtom "iw_1.v445")]), (0), (Some 4), false, true, (Some (TAtom "iw_1.v444")), (Some (4)))]); ((TAtom "iw_1.L448"), [])].


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


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "L6"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L8"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L14"), [(TAtom "v0")]); ((TAtom "L16"), [])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L6"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L8"), [(TAtom "v0")]); ((TAtom "L14"), []); ((TAtom "L16"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "v4")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (96)))]); ((TAtom "L6"), [(2%N, (TApp "tmp" [(TAtom "v13")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (96)))]); ((TAtom "L8"), [(2%N, (TApp "tmp" [(TAtom "v18")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (80)))]); ((TAtom "L14"), []); ((TAtom "L16"), [])].


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


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2")]); ((TAtom "L16"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L17"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L24"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L25"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L4"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L5"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L42"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L61"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L62"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L49"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L71"), []); ((TAtom "L50"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L81"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk12"); (TAtom "v0"); (TAtom "v2"); (TAtom "v88")]); ((TAtom "L96"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk12"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L98"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk12"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L51"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L43"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L127"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L155"), []); ((TAtom "L157"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v149"); (TAtom "v152"); (TAtom "v154"); (TAtom "v2")]); ((TAtom "iw_1.L4"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v152"); (TAtom "v154"); (TAtom "v168"); (TAtom "v177"); (TAtom "v2")]); ((TAtom "iw_1.join"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v152"); (TAtom "v154"); (TAtom "v168"); (TAtom "v2")]); ((TAtom "L44"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L6"), [(TAtom "v2")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L16"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2"); (TAtom "v21")]); ((TAtom "L17"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L24"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2"); (TAtom "v35")]); ((TAtom "L25"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L4"), [(TAtom "v2")]); ((TAtom "L5"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L42"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L61"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2"); (TAtom "v68")]); ((TAtom "L62"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L49"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L71"), []); ((TAtom "L50"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk12"); (TAtom "v0"); (TAtom "v2"); (TAtom "v88")]); ((TAtom "L81"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk12"); (TAtom "v0"); (TAtom "v2"); (TAtom "v95")]); ((TAtom "L96"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk12"); (TAtom "v0"); (TAtom "v104"); (TAtom "v2")]); ((TAtom "L98"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L51"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L43"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L127"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v149"); (TAtom "v152"); (TAtom "v154"); (TAtom "v2")]); ((TAtom "L155"), []); ((TAtom "L157"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v152"); (TAtom "v154"); (TAtom "v168"); (TAtom "v177"); (TAtom "v2")]); ((TAtom "iw_1.L4"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v152"); (TAtom "v154"); (TAtom "v168"); (TAtom "v2")]); ((TAtom "iw_1.join"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L44"), [(TAtom "v2")]); ((TAtom "L6"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "v8")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (8))); (5%N, (TApp "tmp" [(TAtom "v11")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (24)))]); ((TAtom "L16"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0)))]); ((TAtom "L17"), []); ((TAtom "L24"), [(1%N, (TApp "tmp" [(TAtom "v8")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (8))); (4%N, (TApp "tmp" [(TAtom "v31")]), (0), (Some 1), true, false, (Some (TAtom "v28")), (Some (-1)))]); ((TAtom "L25"), []); ((TAtom "L4"), [(1%N, (TApp "tmp" [(TAtom "v8")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (8))); (4%N, (TApp "tmp" [(TAtom "v39")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (8)))]); ((TAtom "L5"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0)))]); ((TAtom "L42"), [(1%N, (TApp "tmp" [(TAtom "v8")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (8))); (3%N, (TApp "tmp" [(TAtom "v11")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (24)))]); ((TAtom "L61"), [(2%N, (TApp "tmp" [(TAtom "v64")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (80)))]); ((TAtom "L62"), []); ((TAtom "L49"), [(1%N, (TApp "tmp" [(TAtom "v8")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (8)))]); ((TAtom "L71"), []); ((TAtom "L50"), [(2%N, (TApp "tmp" [(TAtom "v85")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (80)))]); ((TAtom "L81"), []); ((TAtom "L96"), []); ((TAtom "L98"), [(2%N, (TApp "tmp" [(TAtom "v106")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (72))); (5%N, (TApp "tmp" [(TAtom "v106")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (72))); (9%N, (TApp "tmp" [(TAtom "v109")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (88))); (12%N, (TApp "tmp" [(TAtom "v109")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (88))); (14%N, (TApp "tmp" [(TAtom "v117")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (80)))]); ((TAtom "L51"), [(3%N, (TApp "tmp" [(TAtom "v124")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (8))); (5%N, (TApp "tmp" [(TAtom "v122")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (24)))]); ((TAtom "L43"), [(1%N, (TApp "tmp" [(TAtom "v8")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (8))); (3%N, (TApp "tmp" [(TAtom "v11")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (24)))]); ((TAtom "L127"), [(1%N, (TApp "tmp" [(TAtom "v11")]), (-8), (Some 8), true, false, (Some (TAtom "v0")), (Some (16))); (3%N, (TApp "tmp" [(TAtom "v11")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (24)))]); ((TAtom "L155"), []); ((TAtom "L157"), [(4%N, (TApp "tmp" [(TAtom "v170")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (24))); (7%N, (TApp "tmp" [(TAtom "v170")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (24)))]); ((TAtom "iw_1.L4"), []); ((TAtom "iw_1.join"), [(2%N, (TApp "tmp" [(TAtom "v179")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (24))); (5%N, (TApp "tmp" [(TAtom "v182")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (8))); (9%N, (TApp "tmp" [(TAtom "v189")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (16))); (12%N, (TApp "tmp" [(TAtom "v182")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (8))); (14%N, (TApp "tmp" [(TAtom "v194")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (80)))]); ((TAtom "L44"), [(2%N, (TApp "tmp" [(TAtom "v199")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (8))); (5%N, (TApp "tmp" [(TAtom "v199")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (8))); (8%N, (TApp "tmp" [(TAtom "v201")]), (0), (Some 1), false, true, (Some (TAtom "v200")), (Some (-1)))]); ((TAtom "L6"), [])].


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


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "L18"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L29"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v22")]); ((TAtom "L30"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v22")]); ((TAtom "L23"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v22")]); ((TAtom "L24"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v22")]); ((TAtom "L49"), [(TAtom "chk0"); (TAtom "chk8"); (TAtom "v0"); (TAtom "v22")]); ((TAtom "L73"), [(TAtom "chk0"); (TAtom "chk8"); (TAtom "v0"); (TAtom "v22"); (TAtom "v64"); (TAtom "v71")]); ((TAtom "L74"), [(TAtom "chk0"); (TAtom "chk8"); (TAtom "v0"); (TAtom "v22"); (TAtom "v64"); (TAtom "v71")]); ((TAtom "L78"), [(TAtom "chk0"); (TAtom "chk8"); (TAtom "v0"); (TAtom "v22"); (TAtom "v64")]); ((TAtom "L67"), [(TAtom "chk0"); (TAtom "chk8"); (TAtom "v0"); (TAtom "v22")]); ((TAtom "L50"), [(TAtom "chk0"); (TAtom "chk8"); (TAtom "v0")]); ((TAtom "L13"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L99"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L100"), [(TAtom "chk0"); (TAtom "chk17"); (TAtom "v0")]); ((TAtom "L121"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L101"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "iw_1.L5"), [(TAtom "chk0"); (TAtom "chk22"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_1.L19"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_1.L28"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_1.L29"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_1.L22"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_1.L23"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_1.L45"), [(TAtom "chk0"); (TAtom "chk31"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_1.L66"), [(TAtom "chk0"); (TAtom "chk36"); (TAtom "iw_1.v61"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_1.L67"), [(TAtom "chk0"); (TAtom "iw_1.v61"); (TAtom "iw_1.v68"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_1.L78"), [(TAtom "chk0"); (TAtom "iw_1.v61"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_1.L46"), [(TAtom "chk0"); (TAtom "chk31"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "L8"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_2.L10"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v131")]); ((TAtom "iw_2.join"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v131")]); ((TAtom "L136"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "L143"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "L145"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "L169"), [(TAtom "pr.1"); (TAtom "v0"); (TAtom "v158"); (TAtom "v160"); (TAtom "v167")]); ((TAtom "L170"), [(TAtom "pr.1"); (TAtom "v0"); (TAtom "v158"); (TAtom "v160"); (TAtom "v167")]); ((TAtom "L174"), [(TAtom "pr.1"); (TAtom "v0"); (TAtom "v158"); (TAtom "v160")]); ((TAtom "L163"), [(TAtom "pr.1"); (TAtom "v0"); (TAtom "v158")]); ((TAtom "L195"), [(TAtom "chk51"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v190")]); ((TAtom "L196"), [(TAtom "pr.1"); (TAtom "v0"); (TAtom "v190"); (TAtom "v197")]); ((TAtom "L207"), [(TAtom "pr.1"); (TAtom "v0"); (TAtom "v190")]); ((TAtom "L137"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "L218"), [(TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_3.start"), [(TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_3.L10"), [(TAtom "iw_3.v7"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_3.L11"), [(TAtom "iw_3.v7"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_3.L19"), [(TAtom "iw_3.v7"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_3.L20"), [(TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_3.L4"), [(TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_3.join"), [(TAtom "pr.1")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L18"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v22")]); ((TAtom "L29"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v22"); (TAtom "v38")]); ((TAtom "L30"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v22")]); ((TAtom "L23"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L24"), [(TAtom "chk0"); (TAtom "chk8"); (TAtom "v0"); (TAtom "v22")]); ((TAtom "L49"), [(TAtom "chk0"); (TAtom "chk8"); (TAtom "v0"); (TAtom "v22"); (TAtom "v64"); (TAtom "v71")]); ((TAtom "L73"), [(TAtom "chk0"); (TAtom "chk8"); (TAtom "v0"); (TAtom "v22"); (TAtom "v64"); (TAtom "v71")]); ((TAtom "L74"), [(TAtom "chk0"); (TAtom "chk8"); (TAtom "v0"); (TAtom "v22"); (TAtom "v64")]); ((TAtom "L78"), [(TAtom "chk0"); (TAtom "chk8"); (TAtom "v0"); (TAtom "v22")]); ((TAtom "L67"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L50"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L13"), [(TAtom "chk0"); (TAtom "chk17"); (TAtom "v0")]); ((TAtom "L99"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v107")]); ((TAtom "L100"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L121"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L101"), [(TAtom "chk0"); (TAtom "chk22"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_1.L5"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_1.L19"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_1.L28"), [(TAtom "chk0"); (TAtom "iw_1.v35"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_1.L29"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_1.L22"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_1.L23"), [(TAtom "chk0"); (TAtom "chk31"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_1.L45"), [(TAtom "chk0"); (TAtom "chk36"); (TAtom "iw_1.v61"); (TAtom "iw_1.v65"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_1.L66"), [(TAtom "chk0"); (TAtom "chk36"); (TAtom "iw_1.v61"); (TAtom "iw_1.v68"); (TAtom "iw_1.v69"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_1.L67"), [(TAtom "chk0"); (TAtom "iw_1.v61"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_1.L78"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_1.L46"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "L8"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v131")]); ((TAtom "iw_2.L10"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v131")]); ((TAtom "iw_2.join"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "L136"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "L143"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "L145"), [(TAtom "pr.1"); (TAtom "v0"); (TAtom "v158"); (TAtom "v160"); (TAtom "v167")]); ((TAtom "L169"), [(TAtom "pr.1"); (TAtom "v0"); (TAtom "v158"); (TAtom "v160"); (TAtom "v167")]); ((TAtom "L170"), [(TAtom "pr.1"); (TAtom "v0"); (TAtom "v158"); (TAtom "v160")]); ((TAtom "L174"), [(TAtom "pr.1"); (TAtom "v0"); (TAtom "v158")]); ((TAtom "L163"), [(TAtom "chk51"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v190"); (TAtom "v194")]); ((TAtom "L195"), [(TAtom "chk51"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v190"); (TAtom "v197"); (TAtom "v198")]); ((TAtom "L196"), [(TAtom "pr.1"); (TAtom "v0"); (TAtom "v190")]); ((TAtom "L207"), [(TAtom "pr.1"); (TAtom "v0")]); ((TAtom "L137"), [(TAtom "pr.1"); (TAtom "v0")]); ((TAtom "L218"), [(TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_3.start"), [(TAtom "iw_3.v7"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_3.L10"), [(TAtom "iw_3.v16"); (TAtom "iw_3.v7"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_3.L11"), [(TAtom "iw_3.v7"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_3.L19"), [(TAtom "iw_3.v25"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_3.L20"), [(TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_3.L4"), [(TAtom "pr.1")]); ((TAtom "iw_3.join"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0)))]); ((TAtom "L18"), [(3%N, (TApp "tmp" [(TAtom "v26")]), (0), (Some 1), true, false, (Some (TAtom "v26")), (Some (0)))]); ((TAtom "L29"), [(2%N, (TApp "tmp" [(TAtom "v32")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136))); (5%N, (TApp "tmp" [(TAtom "v34")]), (0), (Some 8), true, false, (Some (TAtom "v33")), (Some (8)))]); ((TAtom "L30"), []); ((TAtom "L23"), [(2%N, (TApp "tmp" [(TAtom "v42")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136))); (4%N, (TApp "tmp" [(TAtom "v43")]), (0), (Some 4), false, true, (Some (TAtom "v43")), (Some (0))); (5%N, (TApp "tmp" [(TAtom "v42")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136))); (8%N, (TApp "tmp" [(TAtom "v47")]), (0), (Some 8), false, true, (Some (TAtom "v46")), (Some (8)))]); ((TAtom "L24"), [(2%N, (TApp "tmp" [(TAtom "v53")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136))); (5%N, (TApp "tmp" [(TAtom "v55")]), (0), (Some 8), true, false, (Some (TAtom "v54")), (Some (8)))]); ((TAtom "L49"), [(1%N, (TApp "tmp" [(TAtom "v53")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136))); (3%N, (TApp "tmp" [(TAtom "v64")]), (0), (Some 4), true, true, (Some (TAtom "v64")), (Some (0)))]); ((TAtom "L73"), []); ((TAtom "L74"), []); ((TAtom "L78"), []); ((TAtom "L67"), [(2%N, (TApp "tmp" [(TAtom "v89")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136))); (5%N, (TApp "tmp" [(TAtom "v91")]), (0), (Some 8), false, true, (Some (TAtom "v90")), (Some (8)))]); ((TAtom "L50"), [(1%N, (TApp "tmp" [(TAtom "v53")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136))); (4%N, (TApp "tmp" [(TAtom "v96")]), (0), (Some 4), true, false, (Some (TAtom "v95")), (Some (4))); (7%N, (TApp "tmp" [(TAtom "v96")]), (0), (Some 4), false, true, (Some (TAtom "v95")), (Some (4)))]); ((TAtom "L13"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0)))]); ((TAtom "L99"), [(3%N, (TApp "tmp" [(TAtom "v109")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (116))); (7%N, (TApp "tmp" [(TAtom "v109")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (116))); (12%N, (TApp "tmp" [(TAtom "v109")]), (0), (Some 4), false, true, (Some (TAtom "v0")), (Some (116)))]); ((TAtom "L100"), [(0%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0)))]); ((TAtom "L121"), []); ((TAtom "L101"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0)))]); ((TAtom "iw_1.L5"), [(0%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0)))]); ((TAtom "iw_1.L19"), [(2%N, (TApp "tmp" [(TAtom "iw_1.v25")]), (0), (Some 1), true, false, (Some (TAtom "iw_1.v25")), (Some (0)))]); ((TAtom "iw_1.L28"), [(2%N, (TApp "tmp" [(TAtom "iw_1.v31")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136))); (5%N, (TApp "tmp" [(TAtom "iw_1.v33")]), (0), (Some 4), true, false, (Some (TAtom "iw_1.v32")), (Some (4)))]); ((TAtom "iw_1.L29"), []); ((TAtom "iw_1.L22"), [(2%N, (TApp "tmp" [(TAtom "iw_1.v39")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136))); (5%N, (TApp "tmp" [(TAtom "iw_1.v41")]), (0), (Some 8), false, true, (Some (TAtom "iw_1.v40")), (Some (8))); (7%N, (TApp "tmp" [(TAtom "iw_1.v39")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136))); (9%N, (TApp "tmp" [(TAtom "iw_1.v44")]), (0), (Some 4), false, true, (Some (TAtom "iw_1.v44")), (Some (0)))]); ((TAtom "iw_1.L23"), [(2%N, (TApp "tmp" [(TAtom "iw_1.v49")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136))); (5%N, (TApp "tmp" [(TAtom "iw_1.v51")]), (0), (Some 4), true, false, (Some (TAtom "iw_1.v50")), (Some (4)))]); ((TAtom "iw_1.L45"), [(1%N, (TApp "tmp" [(TAtom "iw_1.v49")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136))); (4%N, (TApp "tmp" [(TAtom "iw_1.v57")]), (0), (Some 8), false, true, (Some (TAtom "iw_1.v56")), (Some (8))); (6%N, (TApp "tmp" [(TAtom "iw_1.v55")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136))); (8%N, (TApp "tmp" [(TAtom "iw_1.v61")]), (0), (Some 4), true, false, (Some (TAtom "iw_1.v61")), (Some (0)))]); ((TAtom "iw_1.L66"), [(1%N, (TApp "tmp" [(TAtom "iw_1.v61")]), (0), (Some 4), true, true, (Some (TAtom "iw_1.v61")), (Some (0)))]); ((TAtom "iw_1.L67"), []); ((TAtom "iw_1.L78"), []); ((TAtom "iw_1.L46"), [(1%N, (TApp "tmp" [(TAtom "iw_1.v49")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136))); (4%N, (TApp "tmp" [(TAtom "iw_1.v92")]), (0), (Some 4), true, false, (Some (TAtom "iw_1.v91")), (Some (4))); (7%N, (TApp "tmp" [(TAtom "iw_1.v92")]), (0), (Some 4), false, true, (Some (TAtom "iw_1.v91")), (Some (4)))]); ((TAtom "L8"), [(3%N, (TApp "tmp" [(TAtom "v130")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (216)))]); ((TAtom "iw_2.L10"), []); ((TAtom "iw_2.join"), [(2%N, (TApp "tmp" [(TAtom "v133")]), (0), (Some 8), true, false, (Some (TAtom "v131")), (Some (16))); (7%N, (TApp "tmp" [(TAtom "v140")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (192)))]); ((TAtom "L136"), [(2%N, (TApp "tmp" [(TAtom "v147")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (160))); (5%N, (TApp "tmp" [(TAtom "v149")]), (0), (Some 8), true, false, (Some (TAtom "v148")), (Some (72)))]); ((TAtom "L143"), []); ((TAtom "L145"), [(2%N, (TApp "tmp" [(TAtom "v157")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (152))); (5%N, (TApp "tmp" [(TAtom "v160")]), (0), (Some 4), true, true, (Some (TAtom "v160")), (Some (0)))]); ((TAtom "L169"), []); ((TAtom "L170"), []); ((TAtom "L174"), []); ((TAtom "L163"), [(1%N, (TApp "tmp" [(TAtom "v158")]), (0), (Some 8), true, false, (Some (TAtom "v158")), (Some (0))); (5%N, (TApp "tmp" [(TAtom "v187")]), (0), (Some 8), true, false, (Some (TAtom "v158")), (Some (56))); (9%N, (TApp "tmp" [(TAtom "v190")]), (0), (Some 4), true, false, (Some (TAtom "v190")), (Some (0)))]); ((TAtom "L195"), [(1%N, (TApp "tmp" [(TAtom "v190")]), (0), (Some 4), true, true, (Some (TAtom "v190")), (Some (0)))]); ((TAtom "L196"), []); ((TAtom "L207"), []); ((TAtom "L137"), [(2%N, (TApp "tmp" [(TAtom "v222")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (80)))]); ((TAtom "L218"), []); ((TAtom "iw_3.start"), []); ((TAtom "iw_3.L10"), []); ((TAtom "iw_3.L11"), []); ((TAtom "iw_3.L19"), []); ((TAtom "iw_3.L20"), []); ((TAtom "iw_3.L4"), []); ((TAtom "iw_3.join"), [])].


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

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [(3%N, (TApp "tmp" [(TAtom "v11")]), (0), (Some 8), true, false, (Some (TAtom "v11")), (Some (0))); (5%N, (TApp "tmp" [(TAtom "v12")]), (0), (Some 4), true, false, (Some (TAtom "v12")), (Some (0)))]); ((TAtom "L20"), [(3%N, (TApp "tmp" [(TAtom "v28")]), (0), (Some 1), true, false, (Some (TAtom "v28")), (Some (0)))]); ((TAtom "L31"), [(2%N, (TApp "tmp" [(TAtom "v34")]), (0), (Some 8), true, false, (Some (TAtom "v12")), (Some (136))); (5%N, (TApp "tmp" [(TAtom "v36")]), (0), (Some 8), true, false, (Some (TAtom "v35")), (Some (8)))]); ((TAtom "L32"), []); ((TAtom "L25"), [(2%N, (TApp "tmp" [(TAtom "v44")]), (0), (Some 8), true, false, (Some (TAtom "v12")), (Some (136))); (4%N, (TApp "tmp" [(TAtom "v45")]), (0), (Some 4), false, true, (Some (TAtom "v45")), (Some (0))); (5%N, (TApp "tmp" [(TAtom "v44")]), (0), (Some 8), true, false, (Some (TAtom "v12")), (Some (136))); (8%N, (TApp "tmp" [(TAtom "v49")]), (0), (Some 8), false, true, (Some (TAtom "v48")), (Some (8)))]); ((TAtom "L26"), [(2%N, (TApp "tmp" [(TAtom "v55")]), (0), (Some 8), true, false, (Some (TAtom "v12")), (Some (136))); (5%N, (TApp "tmp" [(TAtom "v57")]), (0), (Some 8), true, false, (Some (TAtom "v56")), (Some (8)))]); ((TAtom "L51"), [(1%N, (TApp "tmp" [(TAtom "v55")]), (0), (Some 8), true, false, (Some (TAtom "v12")), (Some (136))); (3%N, (TApp "tmp" [(TAtom "v66")]), (0), (Some 4), true, true, (Some (TAtom "v66")), (Some (0)))]); ((TAtom "L75"), []); ((TAtom "L76"), []); ((TAtom "L80"), []); ((TAtom "L69"), [(2%N, (TApp "tmp" [(TAtom "v91")]), (0), (Some 8), true, false, (Some (TAtom "v12")), (Some (136))); (5%N, (TApp "tmp" [(TAtom "v93")]), (0), (Some 8), false, true, (Some (TAtom "v92")), (Some (8)))]); ((TAtom "L52"), [(1%N, (TApp "tmp" [(TAtom "v55")]), (0), (Some 8), true, false, (Some (TAtom "v12")), (Some (136))); (4%N, (TApp "tmp" [(TAtom "v98")]), (0), (Some 4), true, false, (Some (TAtom "v97")), (Some (4))); (7%N, (TApp "tmp" [(TAtom "v98")]), (0), (Some 4), false, true, (Some (TAtom "v97")), (Some (4)))]); ((TAtom "L109"), [(2%N, (TApp "tmp" [(TAtom "v122")]), (0), (Some 8), true, false, (Some (TAtom "v122")), (Some (0))); (5%N, (TApp "tmp" [(TAtom "v124")]), (0), (Some 4), true, false, (Some (TAtom "v123")), (Some (192)))]); ((TAtom "L119"), [(2%N, (TApp "tmp" [(TAtom "v127")]), (0), (Some 8), true, false, (Some (TAtom "v127")), (Some (0))); (5%N, (TApp "tmp" [(TAtom "v129")]), (0), (Some 4), false, true, (Some (TAtom "v128")), (Some (192)))]); ((TAtom "L121"), [(2%N, (TApp "tmp" [(TAtom "v131")]), (0), (Some 8), true, false, (Some (TAtom "v131")), (Some (0))); (5%N, (TApp "tmp" [(TAtom "v133")]), (0), (Some 4), true, false, (Some (TAtom "v132")), (Some (192)))]); ((TAtom "L162"), [(2%N, (TApp "tmp" [(TAtom "v164")]), (0), (Some 8), true, false, (Some (TAtom "v164")), (Some (0))); (5%N, (TApp "tmp" [(TAtom "v166")]), (0), (Some 8), true, false, (Some (TAtom "v165")), (Some (216)))]); ((TAtom "iw_1.L10"), []); ((TAtom "iw_1.join"), [(2%N, (TApp "tmp" [(TAtom "v169")]), (0), (Some 8), true, false, (Some (TAtom "v167")), (Some (56))); (5%N, (TApp "tmp" [(TAtom "v171")]), (0), (Some 8), true, false, (Some (TAtom "v171")), (Some (0)))]); ((TAtom "L163"), []); ((TAtom "L180"), [(2%N, (TApp "tmp" [(TAtom "v185")]), (0), (Some 8), true, false, (Some (TAtom "v185")), (Some (0))); (5%N, (TApp "tmp" [(TAtom "v187")]), (0), (Some 8), true, false, (Some (TAtom "v186")), (Some (40))); (8%N, (TApp "tmp" [(TAtom "v189")]), (0), (Some 8), true, false, (Some (TAtom "v189")), (Some (0))); (11%N, (TApp "tmp" [(TAtom "v191")]), (0), (Some 8), true, false, (Some (TAtom "v190")), (Some (48)))]); ((TAtom "L182"), [(2%N, (TApp "tmp" [(TAtom "v198")]), (0), (Some 8), true, false, (Some (TAtom "v198")), (Some (0)))]); ((TAtom "L183"), [(2%N, (TApp "tmp" [(TAtom "v201")]), (0), (Some 8), true, false, (Some (TAtom "v201")), (Some (0))); (5%N, (TApp "tmp" [(TAtom "v203")]), (0), (Some 8), true, false, (Some (TAtom "v202")), (Some (40))); (8%N, (TApp "tmp" [(TAtom "v203")]), (0), (Some 8), false, true, (Some (TAtom "v202")), (Some (40))); (10%N, (TApp "tmp" [(TAtom "v204")]), (0), (Some 1), false, true, (Some (TAtom "v204")), (Some (0)))]); ((TAtom "L184"), []); ((TAtom "L181"), []); ((TAtom "L101"), []); ((TAtom "L212"), []); ((TAtom "L103"), [(1%N, (TApp "tmp" [(TAtom "v12")]), (0), (Some 4), true, false, (Some (TAtom "v12")), (Some (0)))]); ((TAtom "iw_2.L5"), [(0%N, (TApp "tmp" [(TAtom "v12")]), (0), (Some 4), true, false, (Some (TAtom "v12")), (Some (0)))]); ((TAtom "iw_2.L19"), [(2%N, (TApp "tmp" [(TAtom "iw_2.v25")]), (0), (Some 1), true, false, (Some (TAtom "iw_2.v25")), (Some (0)))]); ((TAtom "iw_2.L28"), [(2%N, (TApp "tmp" [(TAtom "iw_2.v31")]), (0), (Some 8), true, false, (Some (TAtom "v12")), (Some (136))); (5%N, (TApp "tmp" [(TAtom "iw_2.v33")]), (0), (Some 4), true, false, (Some (TAtom "iw_2.v32")), (Some (4)))]); ((TAtom "iw_2.L29"), []); ((TAtom "iw_2.L22"), [(2%N, (TApp "tmp" [(TAtom "iw_2.v39")]), (0), (Some 8), true, false, (Some (TAtom "v12")), (Some (136))); (5%N, (TApp "tmp" [(TAtom "iw_2.v41")]), (0), (Some 8), false, true, (Some (TAtom "iw_2.v40")), (Some (8))); (7%N, (TApp "tmp" [(TAtom "iw_2.v39")]), (0), (Some 8), true, false, (Some (TAtom "v12")), (Some (136))); (9%N, (TApp "tmp" [(TAtom "iw_2.v44")]), (0), (Some 4), false, true, (Some (TAtom "iw_2.v44")), (Some (0)))]); ((TAtom "iw_2.L23"), [(2%N, (TApp "tmp" [(TAtom "iw_2.v49")]), (0), (Some 8), true, false, (Some (TAtom "v12")), (Some (136))); (5%N, (TApp "tmp" [(TAtom "iw_2.v51")]), (0), (Some 4), true, false, (Some (TAtom "iw_2.v50")), (Some (4)))]); ((TAtom "iw_2.L45"), [(1%N, (TApp "tmp" [(TAtom "iw_2.v49")]), (0), (Some 8), true, false, (Some (TAtom "v12")), (Some (136))); (4%N, (TApp "tmp" [(TAtom "iw_2.v57")]), (0), (Some 8), false, true, (Some (TAtom "iw_2.v56")), (Some (8))); (6%N, (TApp "tmp" [(TAtom "iw_2.v55")]), (0), (Some 8), true, false, (Some (TAtom "v12")), (Some (136))); (8%N, (TApp "tmp" [(TAtom "iw_2.v61")]), (0), (Some 4), true, false, (Some (TAtom "iw_2.v61")), (Some (0)))]); ((TAtom "iw_2.L66"), [(1%N, (TApp "tmp" [(TAtom "iw_2.v61")]), (0), (Some 4), true, true, (Some (TAtom "iw_2.v61")), (Some (0)))]); ((TAtom "iw_2.L67"), []); ((TAtom "iw_2.L78"), []); ((TAtom "iw_2.L46"), [(1%N, (TApp "tmp" [(TAtom "iw_2.v49")]), (0), (Some 8), true, false, (Some (TAtom "v12")), (Some (136))); (4%N, (TApp "tmp" [(TAtom "iw_2.v92")]), (0), (Some 4), true, false, (Some (TAtom "iw_2.v91")), (Some (4))); (7%N, (TApp "tmp" [(TAtom "iw_2.v92")]), (0), (Some 4), false, true, (Some (TAtom "iw_2.v91")), (Some (4)))]); ((TAtom "L9"), [])].


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

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), []); ((TAtom "L2"), [(1%N, (TApp "tmp" [(TAtom "pr.1")]), (0), (Some 8), true, false, (Some (TAtom "pr.1")), (Some (0)))]); ((TAtom "L3"), [(0%N, (TApp "tmp" [(TAtom "pr.1")]), (0), (Some 8), true, false, (Some (TAtom "pr.1")), (Some (0))); (3%N, (TApp "tmp" [(TAtom "v13")]), (0), (Some 8), false, true, (Some (TAtom "v12")), (Some (184))); (5%N, (TApp "tmp" [(TAtom "pr.1")]), (0), (Some 8), true, false, (Some (TAtom "pr.1")), (Some (0)))]); ((TAtom "L5"), [])].


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

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
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

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [(3%N, (TApp "tmp" [(TAtom "v4")]), (0), (Some 8), true, false, (Some (TAtom "v3")), (Some (216)))]); ((TAtom "L11"), [(3%N, (TApp "tmp" [(TAtom "v14")]), (0), (Some 8), true, false, (Some (TAtom "v13")), (Some (216)))]); ((TAtom "L12"), []); ((TAtom "L23"), [(3%N, (TApp "tmp" [(TAtom "v26")]), (0), (Some 8), true, false, (Some (TAtom "v25")), (Some (216)))]); ((TAtom "L24"), []); ((TAtom "L0"), [(3%N, (TApp "tmp" [(TAtom "iw_1.v6")]), (0), (Some 8), false, true, (Some (TAtom "iw_1.v6")), (Some (0)))]); ((TAtom "L2"), [])].


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

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
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

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [])].


End fn___GI___libc_write.

End HiAtexitSrc06.
