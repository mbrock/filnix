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
Module HiAtexitSrc02.

Module fn__IO_new_file_overflow.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_19, 780%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_19, 783%N)); ((TAtom "L4"), (file_19, 785%N)); ((TAtom "L6"), (file_19, 790%N)); ((TAtom "L23"), (file_19, 790%N)); ((TAtom "L24"), (file_19, 790%N)); ((TAtom "L16"), (file_19, 793%N)); ((TAtom "L33"), (file_19, 795%N)); ((TAtom "L35"), (file_19, 805%N)); ((TAtom "L58"), (file_19, 807%N)); ((TAtom "L81"), (file_19, 809%N)); ((TAtom "L82"), (file_19, 809%N)); ((TAtom "L60"), (file_19, 814%N)); ((TAtom "L111"), (file_19, 815%N)); ((TAtom "L113"), (file_19, 816%N)); ((TAtom "L162"), (file_19, 822%N)); ((TAtom "L163"), (file_19, 822%N)); ((TAtom "L155"), (file_19, 823%N)); ((TAtom "L18"), (file_19, 825%N)); ((TAtom "L175"), (file_19, 826%N)); ((TAtom "L177"), (file_19, 828%N)); ((TAtom "L196"), (file_19, 829%N)); ((TAtom "L211"), (file_19, 829%N)); ((TAtom "L212"), (file_19, 829%N)); ((TAtom "L213"), (file_19, 829%N)); ((TAtom "L208"), (file_19, 830%N)); ((TAtom "L198"), (file_19, 831%N)); ((TAtom "L270"), (file_19, 832%N)); ((TAtom "L275"), (file_19, 832%N)); ((TAtom "L271"), (file_19, 832%N)); ((TAtom "L264"), (file_19, 834%N)); ((TAtom "L283"), (file_19, 836%N)); ((TAtom "L266"), (file_19, 837%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "f"); ((TAtom "v10"), "f"); ((TAtom "v106"), "f"); ((TAtom "v108"), "f"); ((TAtom "v114"), "f"); ((TAtom "v117"), "f"); ((TAtom "v123"), "f"); ((TAtom "v125"), "f"); ((TAtom "v127"), "f"); ((TAtom "v130"), "f"); ((TAtom "v132"), "f"); ((TAtom "v135"), "f"); ((TAtom "v137"), "f"); ((TAtom "v140"), "f"); ((TAtom "v142"), "f"); ((TAtom "v145"), "f"); ((TAtom "v147"), "f"); ((TAtom "v149"), "f"); ((TAtom "v152"), "f"); ((TAtom "v158"), "f"); ((TAtom "v164"), "f"); ((TAtom "v170"), "f"); ((TAtom "v172"), "f"); ((TAtom "v178"), "ch"); ((TAtom "v181"), "f"); ((TAtom "v182"), "f"); ((TAtom "v185"), "f"); ((TAtom "v188"), "f"); ((TAtom "v19"), "f"); ((TAtom "v199"), "f"); ((TAtom "v2"), "ch"); ((TAtom "v202"), "f"); ((TAtom "v214"), "f"); ((TAtom "v218"), "f"); ((TAtom "v219"), "f"); ((TAtom "v222"), "f"); ((TAtom "v225"), "f"); ((TAtom "v232"), "f"); ((TAtom "v233"), "f"); ((TAtom "v238"), "f"); ((TAtom "v243"), "f"); ((TAtom "v25"), "f"); ((TAtom "v258"), "f"); ((TAtom "v262"), "ch"); ((TAtom "v267"), "f"); ((TAtom "v272"), "f"); ((TAtom "v277"), "ch"); ((TAtom "v286"), "f"); ((TAtom "v287"), "f"); ((TAtom "v290"), "f"); ((TAtom "v293"), "f"); ((TAtom "v304"), "ch"); ((TAtom "v36"), "f"); ((TAtom "v42"), "f"); ((TAtom "v43"), "f"); ((TAtom "v45"), "f"); ((TAtom "v48"), "f"); ((TAtom "v50"), "f"); ((TAtom "v53"), "f"); ((TAtom "v55"), "f"); ((TAtom "v61"), "f"); ((TAtom "v67"), "f"); ((TAtom "v7"), "f"); ((TAtom "v70"), "f"); ((TAtom "v75"), "nbackup"); ((TAtom "v76"), "f"); ((TAtom "v77"), "f"); ((TAtom "v83"), "nbackup"); ((TAtom "v84"), "f"); ((TAtom "v87"), "f"); ((TAtom "v94"), "nbackup"); ((TAtom "v95"), "f"); ((TAtom "v98"), "f")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

End fn__IO_new_file_overflow.

Module fn__IO_new_file_sync.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_19, 841%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_19, 848%N)); ((TAtom "L4"), (file_19, 849%N)); ((TAtom "L19"), (file_19, 849%N)); ((TAtom "L20"), (file_19, 849%N)); ((TAtom "L21"), (file_19, 849%N)); ((TAtom "L16"), (file_19, 849%N)); ((TAtom "L6"), (file_19, 850%N)); ((TAtom "L73"), (file_19, 853%N)); ((TAtom "L75"), (file_19, 844%N)); ((TAtom "L91"), (file_19, 858%N)); ((TAtom "iw_1.L10"), (file_10, 1049%N)); ((TAtom "iw_1.join"), (file_19, 858%N)); ((TAtom "L106"), (file_19, 860%N)); ((TAtom "L107"), (file_19, 861%N)); ((TAtom "L119"), (file_19, 861%N)); ((TAtom "L93"), (file_19, 845%N)); ((TAtom "L125"), (file_19, 867%N)); ((TAtom "L127"), (file_19, 870%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "vtable"); ((TAtom "iw_1.v13"), "offset"); ((TAtom "iw_1.v18"), "vtable"); ((TAtom "iw_1.v3"), "vtable"); ((TAtom "iw_1.v4"), "ptr"); ((TAtom "iw_1.v6"), "ptr"); ((TAtom "iw_1.v9"), "offset"); ((TAtom "pr.1"), "delta"); ((TAtom "pr.2"), "retval"); ((TAtom "pr.3"), "retval"); ((TAtom "pr.4"), "retval"); ((TAtom "v0"), "fp"); ((TAtom "v10"), "fp"); ((TAtom "v103"), "fp"); ((TAtom "v104"), "delta"); ((TAtom "v105"), "new_pos"); ((TAtom "v109"), "new_pos"); ((TAtom "v113"), "fp"); ((TAtom "v115"), "fp"); ((TAtom "v122"), "__libc_errno"); ((TAtom "v124"), "retval"); ((TAtom "v128"), "retval"); ((TAtom "v131"), "fp"); ((TAtom "v135"), "retval"); ((TAtom "v22"), "fp"); ((TAtom "v26"), "fp"); ((TAtom "v27"), "fp"); ((TAtom "v30"), "fp"); ((TAtom "v33"), "fp"); ((TAtom "v40"), "fp"); ((TAtom "v41"), "fp"); ((TAtom "v46"), "fp"); ((TAtom "v51"), "fp"); ((TAtom "v64"), "fp"); ((TAtom "v67"), "fp"); ((TAtom "v7"), "fp"); ((TAtom "v72"), "delta"); ((TAtom "v76"), "fp"); ((TAtom "v79"), "fp"); ((TAtom "v80"), "delta"); ((TAtom "v81"), "fp"); ((TAtom "v84"), "fp"); ((TAtom "v90"), "delta"); ((TAtom "v94"), "delta"); ((TAtom "v97"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

End fn__IO_new_file_sync.

Module fn__IO_file_sync_mmap.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_19, 874%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_19, 877%N)); ((TAtom "L16"), (file_19, 880%N)); ((TAtom "L28"), (file_19, 882%N)); ((TAtom "L30"), (file_19, 877%N)); ((TAtom "L46"), (file_19, 887%N)); ((TAtom "L18"), (file_19, 877%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "pr.1"), "o"); ((TAtom "pr.2"), "o"); ((TAtom "v0"), "fp"); ((TAtom "v15"), "o"); ((TAtom "v19"), "fp"); ((TAtom "v22"), "fp"); ((TAtom "v3"), "fp"); ((TAtom "v31"), "fp"); ((TAtom "v34"), "fp"); ((TAtom "v35"), "o"); ((TAtom "v36"), "fp"); ((TAtom "v39"), "fp"); ((TAtom "v45"), "o"); ((TAtom "v49"), "fp"); ((TAtom "v52"), "o"); ((TAtom "v54"), "o"); ((TAtom "v56"), "fp"); ((TAtom "v6"), "fp"); ((TAtom "v61"), "fp"); ((TAtom "v63"), "o"); ((TAtom "v64"), "fp"); ((TAtom "v66"), "fp"); ((TAtom "v68"), "fp"); ((TAtom "v9"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

End fn__IO_file_sync_mmap.

Module fn__IO_new_file_seekoff.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_19, 968%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_19, 1034%N)); ((TAtom "iw_1.start"), (file_19, 906%N)); ((TAtom "iw_1.L4"), (file_19, 908%N)); ((TAtom "iw_1.L34"), (file_19, 915%N)); ((TAtom "iw_1.L35"), (file_19, 915%N)); ((TAtom "iw_1.L30"), (file_19, 917%N)); ((TAtom "iw_1.iw_1.L10"), (file_10, 1049%N)); ((TAtom "iw_1.iw_1.join"), (file_19, 917%N)); ((TAtom "iw_1.L48"), (file_19, 921%N)); ((TAtom "iw_1.L32"), (file_19, 925%N)); ((TAtom "iw_1.L60"), (file_19, 926%N)); ((TAtom "iw_1.L61"), (file_19, 932%N)); ((TAtom "iw_1.L76"), (file_19, 933%N)); ((TAtom "iw_1.L77"), (file_19, 936%N)); ((TAtom "iw_1.L6"), (file_19, 902%N)); ((TAtom "iw_1.L102"), (file_19, 940%N)); ((TAtom "iw_1.L103"), (file_19, 942%N)); ((TAtom "iw_1.iw_2.L10"), (file_10, 1049%N)); ((TAtom "iw_1.iw_2.join"), (file_19, 942%N)); ((TAtom "iw_1.L104"), (file_19, 902%N)); ((TAtom "iw_1.L124"), (file_19, 947%N)); ((TAtom "iw_1.L136"), (file_19, 947%N)); ((TAtom "iw_1.L137"), (file_19, 947%N)); ((TAtom "iw_1.L131"), (file_19, 953%N)); ((TAtom "iw_1.L133"), (file_19, 957%N)); ((TAtom "iw_1.L149"), (file_19, 961%N)); ((TAtom "iw_1.join"), (file_19, 979%N)); ((TAtom "L14"), (file_19, 983%N)); ((TAtom "L30"), (file_19, 983%N)); ((TAtom "L31"), (file_19, 983%N)); ((TAtom "L53"), (file_19, 986%N)); ((TAtom "L54"), (file_19, 986%N)); ((TAtom "L65"), (file_19, 996%N)); ((TAtom "L66"), (file_19, 996%N)); ((TAtom "L61"), (file_19, 997%N)); ((TAtom "L63"), (file_19, 999%N)); ((TAtom "L74"), (file_19, 1002%N)); ((TAtom "L83"), (file_19, 1004%N)); ((TAtom "iw_2.L4"), (file_10, 1059%N)); ((TAtom "iw_2.join"), (file_19, 1005%N)); ((TAtom "L85"), (file_19, 1007%N)); ((TAtom "L131"), (file_19, 1016%N)); ((TAtom "L145"), (file_19, 1021%N)); ((TAtom "L159"), (file_19, 1024%N)); ((TAtom "L169"), (file_19, 1035%N)); ((TAtom "iw_3.L10"), (file_10, 1049%N)); ((TAtom "iw_3.join"), (file_19, 1035%N)); ((TAtom "L183"), (file_19, 1035%N)); ((TAtom "L184"), (file_19, 1035%N)); ((TAtom "L171"), (file_19, 1037%N)); ((TAtom "L129"), (file_19, 1012%N)); ((TAtom "L196"), (file_19, 1012%N)); ((TAtom "L198"), (file_19, 1012%N)); ((TAtom "L130"), (file_19, 968%N)); ((TAtom "L211"), (file_19, 1050%N)); ((TAtom "L212"), (file_19, 1050%N)); ((TAtom "L221"), (file_19, 1050%N)); ((TAtom "L222"), (file_19, 1050%N)); ((TAtom "L202"), (file_19, 1053%N)); ((TAtom "L249"), (file_19, 1055%N)); ((TAtom "L250"), (file_19, 1055%N)); ((TAtom "L243"), (file_19, 1057%N)); ((TAtom "L204"), (file_19, 1067%N)); ((TAtom "L300"), (file_19, 1071%N)); ((TAtom "L322"), (file_19, 1073%N)); ((TAtom "L323"), (file_19, 972%N)); ((TAtom "iw_4.L10"), (file_10, 1049%N)); ((TAtom "iw_4.join"), (file_19, 1078%N)); ((TAtom "L345"), (file_19, 1080%N)); ((TAtom "L347"), (file_19, 1081%N)); ((TAtom "L354"), (file_19, 1085%N)); ((TAtom "iw_5.L10"), (file_10, 1049%N)); ((TAtom "iw_5.join"), (file_19, 1085%N)); ((TAtom "L369"), (file_19, 1085%N)); ((TAtom "L370"), (file_19, 1085%N)); ((TAtom "L384"), (file_19, 1091%N)); ((TAtom "L391"), (file_19, 1091%N)); ((TAtom "L355"), (file_19, 973%N)); ((TAtom "L152"), (file_19, 968%N)); ((TAtom "iw_6.L10"), (file_10, 1049%N)); ((TAtom "iw_6.join"), (file_19, 1105%N)); ((TAtom "L458"), (file_19, 1108%N)); ((TAtom "L460"), (file_19, 1113%N)); ((TAtom "L503"), (file_19, 1121%N)); ((TAtom "iw_7.L10"), (file_10, 1049%N)); ((TAtom "iw_7.join"), (file_19, 1121%N)); ((TAtom "L505"), (file_19, 1123%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.iw_1.v0"), "vtable"); ((TAtom "iw_1.iw_1.v13"), "offset"); ((TAtom "iw_1.iw_1.v18"), "vtable"); ((TAtom "iw_1.iw_1.v3"), "vtable"); ((TAtom "iw_1.iw_1.v4"), "ptr"); ((TAtom "iw_1.iw_1.v6"), "ptr"); ((TAtom "iw_1.iw_1.v9"), "offset"); ((TAtom "iw_1.iw_2.v0"), "vtable"); ((TAtom "iw_1.iw_2.v13"), "offset"); ((TAtom "iw_1.iw_2.v18"), "vtable"); ((TAtom "iw_1.iw_2.v3"), "vtable"); ((TAtom "iw_1.iw_2.v4"), "ptr"); ((TAtom "iw_1.iw_2.v6"), "ptr"); ((TAtom "iw_1.iw_2.v9"), "offset"); ((TAtom "iw_1.pr.1"), "result"); ((TAtom "iw_1.pr.2"), "offset"); ((TAtom "iw_1.pr.3"), "offset"); ((TAtom "iw_1.pr.4"), "offset"); ((TAtom "iw_1.v0"), "fp"); ((TAtom "iw_1.v101"), "offset"); ((TAtom "iw_1.v105"), "fp"); ((TAtom "iw_1.v111"), "fp"); ((TAtom "iw_1.v113"), "result"); ((TAtom "iw_1.v114"), "fp"); ((TAtom "iw_1.v120"), "fp"); ((TAtom "iw_1.v121"), "result"); ((TAtom "iw_1.v125"), "result"); ((TAtom "iw_1.v129"), "result"); ((TAtom "iw_1.v134"), "result"); ((TAtom "iw_1.v138"), "offset"); ((TAtom "iw_1.v14"), "fp"); ((TAtom "iw_1.v146"), "result"); ((TAtom "iw_1.v147"), "offset"); ((TAtom "iw_1.v148"), "result"); ((TAtom "iw_1.v152"), "result"); ((TAtom "iw_1.v158"), "result"); ((TAtom "iw_1.v17"), "fp"); ((TAtom "iw_1.v23"), "unflushed_writes"); ((TAtom "iw_1.v25"), "fp"); ((TAtom "iw_1.v29"), "append_mode"); ((TAtom "iw_1.v33"), "unflushed_writes"); ((TAtom "iw_1.v36"), "append_mode"); ((TAtom "iw_1.v39"), "fp"); ((TAtom "iw_1.v45"), "fp"); ((TAtom "iw_1.v46"), "result"); ((TAtom "iw_1.v50"), "result"); ((TAtom "iw_1.v57"), "fp"); ((TAtom "iw_1.v59"), "result"); ((TAtom "iw_1.v63"), "unflushed_writes"); ((TAtom "iw_1.v65"), "offset"); ((TAtom "iw_1.v66"), "fp"); ((TAtom "iw_1.v69"), "fp"); ((TAtom "iw_1.v7"), "fp"); ((TAtom "iw_1.v75"), "offset"); ((TAtom "iw_1.v79"), "append_mode"); ((TAtom "iw_1.v80"), "offset"); ((TAtom "iw_1.v81"), "fp"); ((TAtom "iw_1.v84"), "fp"); ((TAtom "iw_1.v90"), "offset"); ((TAtom "iw_1.v91"), "offset"); ((TAtom "iw_1.v92"), "fp"); ((TAtom "iw_1.v95"), "fp"); ((TAtom "iw_2.v0"), "fp"); ((TAtom "iw_2.v13"), "ptr"); ((TAtom "iw_2.v2"), "ptr"); ((TAtom "iw_2.v7"), "ptr"); ((TAtom "iw_2.v8"), "fp"); ((TAtom "iw_3.v0"), "vtable"); ((TAtom "iw_3.v13"), "offset"); ((TAtom "iw_3.v18"), "vtable"); ((TAtom "iw_3.v3"), "vtable"); ((TAtom "iw_3.v4"), "ptr"); ((TAtom "iw_3.v6"), "ptr"); ((TAtom "iw_3.v9"), "offset"); ((TAtom "iw_4.v0"), "vtable"); ((TAtom "iw_4.v13"), "offset"); ((TAtom "iw_4.v18"), "vtable"); ((TAtom "iw_4.v3"), "vtable"); ((TAtom "iw_4.v4"), "ptr"); ((TAtom "iw_4.v6"), "ptr"); ((TAtom "iw_4.v9"), "offset"); ((TAtom "iw_5.v0"), "vtable"); ((TAtom "iw_5.v13"), "offset"); ((TAtom "iw_5.v18"), "vtable"); ((TAtom "iw_5.v3"), "vtable"); ((TAtom "iw_5.v4"), "ptr"); ((TAtom "iw_5.v6"), "ptr"); ((TAtom "iw_5.v9"), "offset"); ((TAtom "iw_6.v0"), "vtable"); ((TAtom "iw_6.v13"), "offset"); ((TAtom "iw_6.v18"), "vtable"); ((TAtom "iw_6.v3"), "vtable"); ((TAtom "iw_6.v4"), "ptr"); ((TAtom "iw_6.v6"), "ptr"); ((TAtom "iw_6.v9"), "offset"); ((TAtom "iw_7.v0"), "vtable"); ((TAtom "iw_7.v13"), "offset"); ((TAtom "iw_7.v18"), "vtable"); ((TAtom "iw_7.v3"), "vtable"); ((TAtom "iw_7.v4"), "ptr"); ((TAtom "iw_7.v6"), "ptr"); ((TAtom "iw_7.v9"), "offset"); ((TAtom "pr.1"), "offset"); ((TAtom "pr.2"), "offset"); ((TAtom "pr.3"), "dir"); ((TAtom "pr.4"), "dir"); ((TAtom "pr.5"), "delta"); ((TAtom "pr.6"), "new_offset"); ((TAtom "pr.7"), "count"); ((TAtom "v0"), "fp"); ((TAtom "v100"), "fp"); ((TAtom "v101"), "fp"); ((TAtom "v103"), "fp"); ((TAtom "v105"), "fp"); ((TAtom "v108"), "fp"); ((TAtom "v110"), "fp"); ((TAtom "v113"), "fp"); ((TAtom "v115"), "fp"); ((TAtom "v118"), "fp"); ((TAtom "v120"), "fp"); ((TAtom "v123"), "fp"); ((TAtom "v125"), "fp"); ((TAtom "v128"), "dir"); ((TAtom "v132"), "offset"); ((TAtom "v133"), "fp"); ((TAtom "v136"), "fp"); ((TAtom "v142"), "offset"); ((TAtom "v146"), "fp"); ((TAtom "v15"), "mode"); ((TAtom "v154"), "offset"); ((TAtom "v155"), "fp"); ((TAtom "v158"), "offset"); ((TAtom "v162"), "offset"); ((TAtom "v17"), "fp"); ((TAtom "v174"), "fp"); ((TAtom "v180"), "fp"); ((TAtom "v191"), "offset"); ((TAtom "v194"), "offset"); ((TAtom "v2"), "offset"); ((TAtom "v201"), "fp"); ((TAtom "v205"), "fp"); ((TAtom "v21"), "fp"); ((TAtom "v213"), "fp"); ((TAtom "v223"), "fp"); ((TAtom "v230"), "fp"); ((TAtom "v233"), "fp"); ((TAtom "v236"), "fp"); ((TAtom "v24"), "fp"); ((TAtom "v242"), "start_offset"); ((TAtom "v246"), "offset"); ((TAtom "v247"), "start_offset"); ((TAtom "v251"), "offset"); ((TAtom "v252"), "fp"); ((TAtom "v258"), "fp"); ((TAtom "v260"), "fp"); ((TAtom "v263"), "fp"); ((TAtom "v265"), "fp"); ((TAtom "v268"), "offset"); ((TAtom "v269"), "start_offset"); ((TAtom "v272"), "fp"); ((TAtom "v274"), "fp"); ((TAtom "v277"), "fp"); ((TAtom "v279"), "fp"); ((TAtom "v281"), "fp"); ((TAtom "v284"), "fp"); ((TAtom "v286"), "fp"); ((TAtom "v289"), "fp"); ((TAtom "v290"), "fp"); ((TAtom "v301"), "fp"); ((TAtom "v305"), "offset"); ((TAtom "v306"), "fp"); ((TAtom "v309"), "fp"); ((TAtom "v317"), "new_offset"); ((TAtom "v318"), "offset"); ((TAtom "v319"), "new_offset"); ((TAtom "v32"), "fp"); ((TAtom "v320"), "delta"); ((TAtom "v324"), "delta"); ((TAtom "v325"), "fp"); ((TAtom "v328"), "fp"); ((TAtom "v335"), "offset"); ((TAtom "v336"), "fp"); ((TAtom "v342"), "fp"); ((TAtom "v343"), "new_offset"); ((TAtom "v344"), "result"); ((TAtom "v348"), "result"); ((TAtom "v35"), "fp"); ((TAtom "v356"), "delta"); ((TAtom "v358"), "fp"); ((TAtom "v364"), "fp"); ((TAtom "v365"), "fp"); ((TAtom "v371"), "must_be_exact"); ((TAtom "v372"), "delta"); ((TAtom "v373"), "fp"); ((TAtom "v376"), "fp"); ((TAtom "v383"), "count"); ((TAtom "v387"), "count"); ((TAtom "v388"), "delta"); ((TAtom "v393"), "count"); ((TAtom "v397"), "delta"); ((TAtom "v398"), "delta"); ((TAtom "v399"), "count"); ((TAtom "v4"), "dir"); ((TAtom "v401"), "offset"); ((TAtom "v403"), "fp"); ((TAtom "v405"), "fp"); ((TAtom "v408"), "fp"); ((TAtom "v410"), "fp"); ((TAtom "v413"), "delta"); ((TAtom "v415"), "fp"); ((TAtom "v417"), "fp"); ((TAtom "v42"), "must_be_exact"); ((TAtom "v420"), "count"); ((TAtom "v422"), "fp"); ((TAtom "v424"), "fp"); ((TAtom "v426"), "fp"); ((TAtom "v429"), "fp"); ((TAtom "v431"), "fp"); ((TAtom "v434"), "fp"); ((TAtom "v436"), "result"); ((TAtom "v437"), "count"); ((TAtom "v439"), "fp"); ((TAtom "v44"), "fp"); ((TAtom "v440"), "fp"); ((TAtom "v446"), "offset"); ((TAtom "v447"), "fp"); ((TAtom "v448"), "fp"); ((TAtom "v454"), "fp"); ((TAtom "v455"), "offset"); ((TAtom "v456"), "dir"); ((TAtom "v457"), "result"); ((TAtom "v461"), "result"); ((TAtom "v465"), "fp"); ((TAtom "v466"), "fp"); ((TAtom "v47"), "fp"); ((TAtom "v472"), "fp"); ((TAtom "v474"), "result"); ((TAtom "v475"), "fp"); ((TAtom "v477"), "fp"); ((TAtom "v480"), "fp"); ((TAtom "v482"), "fp"); ((TAtom "v485"), "fp"); ((TAtom "v487"), "fp"); ((TAtom "v490"), "fp"); ((TAtom "v492"), "fp"); ((TAtom "v494"), "fp"); ((TAtom "v497"), "fp"); ((TAtom "v499"), "fp"); ((TAtom "v502"), "result"); ((TAtom "v506"), "fp"); ((TAtom "v510"), "fp"); ((TAtom "v516"), "fp"); ((TAtom "v517"), "fp"); ((TAtom "v521"), "offset"); ((TAtom "v55"), "fp"); ((TAtom "v6"), "mode"); ((TAtom "v60"), "was_writing"); ((TAtom "v64"), "was_writing"); ((TAtom "v67"), "fp"); ((TAtom "v77"), "fp"); ((TAtom "v86"), "fp"); ((TAtom "v92"), "fp"); ((TAtom "v93"), "fp"); ((TAtom "v96"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

End fn__IO_new_file_seekoff.

Module fn__IO_file_seekoff_mmap.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_19, 1127%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_19, 1136%N)); ((TAtom "L9"), (file_19, 1137%N)); ((TAtom "L11"), (file_19, 1139%N)); ((TAtom "L28"), (file_19, 1141%N)); ((TAtom "L34"), (file_19, 1142%N)); ((TAtom "L36"), (file_19, 1127%N)); ((TAtom "L30"), (file_19, 1127%N)); ((TAtom "L54"), (file_19, 1150%N)); ((TAtom "L71"), (file_19, 1155%N)); ((TAtom "L85"), (file_19, 1146%N)); ((TAtom "L87"), (file_19, 1146%N)); ((TAtom "L53"), (file_19, 1127%N)); ((TAtom "L90"), (file_19, 1163%N)); ((TAtom "L92"), (file_19, 1167%N)); ((TAtom "iw_1.L10"), (file_10, 1049%N)); ((TAtom "iw_1.join"), (file_19, 1167%N)); ((TAtom "L108"), (file_19, 1169%N)); ((TAtom "L110"), (file_19, 1171%N)); ((TAtom "L116"), (file_19, 1175%N)); ((TAtom "L117"), (file_19, 1179%N)); ((TAtom "L118"), (file_19, 1182%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "vtable"); ((TAtom "iw_1.v13"), "offset"); ((TAtom "iw_1.v18"), "vtable"); ((TAtom "iw_1.v3"), "vtable"); ((TAtom "iw_1.v4"), "ptr"); ((TAtom "iw_1.v6"), "ptr"); ((TAtom "iw_1.v9"), "offset"); ((TAtom "pr.1"), "offset"); ((TAtom "pr.2"), "offset"); ((TAtom "pr.3"), "offset"); ((TAtom "v0"), "fp"); ((TAtom "v105"), "fp"); ((TAtom "v106"), "offset"); ((TAtom "v107"), "result"); ((TAtom "v111"), "result"); ((TAtom "v119"), "offset"); ((TAtom "v12"), "mode"); ((TAtom "v120"), "fp"); ((TAtom "v123"), "fp"); ((TAtom "v130"), "fp"); ((TAtom "v132"), "fp"); ((TAtom "v135"), "fp"); ((TAtom "v137"), "fp"); ((TAtom "v14"), "fp"); ((TAtom "v140"), "fp"); ((TAtom "v142"), "fp"); ((TAtom "v145"), "fp"); ((TAtom "v147"), "fp"); ((TAtom "v150"), "fp"); ((TAtom "v152"), "fp"); ((TAtom "v155"), "offset"); ((TAtom "v157"), "fp"); ((TAtom "v159"), "fp"); ((TAtom "v162"), "offset"); ((TAtom "v164"), "fp"); ((TAtom "v166"), "result"); ((TAtom "v167"), "fp"); ((TAtom "v168"), "fp"); ((TAtom "v17"), "fp"); ((TAtom "v174"), "offset"); ((TAtom "v2"), "offset"); ((TAtom "v20"), "fp"); ((TAtom "v31"), "fp"); ((TAtom "v37"), "dir"); ((TAtom "v39"), "offset"); ((TAtom "v4"), "dir"); ((TAtom "v40"), "fp"); ((TAtom "v43"), "fp"); ((TAtom "v49"), "offset"); ((TAtom "v50"), "fp"); ((TAtom "v51"), "dir"); ((TAtom "v55"), "offset"); ((TAtom "v56"), "fp"); ((TAtom "v59"), "fp"); ((TAtom "v6"), "mode"); ((TAtom "v62"), "fp"); ((TAtom "v69"), "offset"); ((TAtom "v72"), "offset"); ((TAtom "v73"), "fp"); ((TAtom "v76"), "fp"); ((TAtom "v82"), "offset"); ((TAtom "v93"), "offset"); ((TAtom "v99"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

End fn__IO_file_seekoff_mmap.

Module fn__IO_file_seekoff_maybe_mmap.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_19, 1189%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_19, 1197%N)); ((TAtom "iw_1.L10"), (file_10, 1049%N)); ((TAtom "iw_1.join"), (file_19, 1197%N)); ((TAtom "L19"), (file_19, 1199%N)); ((TAtom "L21"), (file_19, 1201%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "vtable"); ((TAtom "iw_1.v13"), "offset"); ((TAtom "iw_1.v18"), "vtable"); ((TAtom "iw_1.v3"), "vtable"); ((TAtom "iw_1.v4"), "ptr"); ((TAtom "iw_1.v6"), "ptr"); ((TAtom "iw_1.v9"), "offset"); ((TAtom "v0"), "fp"); ((TAtom "v15"), "fp"); ((TAtom "v16"), "offset"); ((TAtom "v17"), "dir"); ((TAtom "v18"), "result"); ((TAtom "v2"), "offset"); ((TAtom "v22"), "result"); ((TAtom "v27"), "fp"); ((TAtom "v29"), "result"); ((TAtom "v30"), "result"); ((TAtom "v4"), "dir"); ((TAtom "v6"), "mode"); ((TAtom "v9"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

End fn__IO_file_seekoff_maybe_mmap.

Module fn___GI__IO_file_read.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_19, 1205%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_19, 1208%N)); ((TAtom "L6"), (file_19, 1208%N)); ((TAtom "L7"), (file_19, 1208%N)); ((TAtom "L8"), (file_19, 1208%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fp"); ((TAtom "v17"), "fp"); ((TAtom "v2"), "buf"); ((TAtom "v20"), "buf"); ((TAtom "v21"), "size"); ((TAtom "v23"), "fp"); ((TAtom "v26"), "buf"); ((TAtom "v27"), "size"); ((TAtom "v4"), "size"); ((TAtom "v9"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

End fn___GI__IO_file_read.

Module fn___GI__IO_file_seek.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_19, 1214%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_19, 1217%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fp"); ((TAtom "v10"), "dir"); ((TAtom "v2"), "offset"); ((TAtom "v4"), "dir"); ((TAtom "v6"), "fp"); ((TAtom "v9"), "offset")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

End fn___GI__IO_file_seek.

Module fn___GI__IO_file_stat.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_19, 1221%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_19, 1224%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fp"); ((TAtom "v2"), "st"); ((TAtom "v4"), "fp"); ((TAtom "v7"), "st")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

End fn___GI__IO_file_stat.

Module fn__IO_file_close_mmap.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_19, 1228%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_19, 1232%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fp"); ((TAtom "v15"), "fp"); ((TAtom "v17"), "fp"); ((TAtom "v19"), "fp"); ((TAtom "v2"), "fp"); ((TAtom "v5"), "fp"); ((TAtom "v8"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

End fn__IO_file_close_mmap.

Module fn___GI__IO_file_close.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_19, 1239%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_19, 1244%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fp"); ((TAtom "v2"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

End fn___GI__IO_file_close.

Module fn__IO_new_file_write.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_19, 1248%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_19, 1252%N)); ((TAtom "L8"), (file_19, 1251%N)); ((TAtom "L9"), (file_19, 1254%N)); ((TAtom "L14"), (file_19, 1254%N)); ((TAtom "L15"), (file_19, 1254%N)); ((TAtom "L16"), (file_19, 1254%N)); ((TAtom "L38"), (file_19, 1260%N)); ((TAtom "L40"), (file_19, 1263%N)); ((TAtom "L10"), (file_19, 1267%N)); ((TAtom "L61"), (file_19, 1269%N)); ((TAtom "L63"), (file_19, 1270%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "pr.1"), "data"); ((TAtom "pr.2"), "to_do"); ((TAtom "v0"), "f"); ((TAtom "v11"), "to_do"); ((TAtom "v17"), "f"); ((TAtom "v2"), "data"); ((TAtom "v25"), "f"); ((TAtom "v28"), "data"); ((TAtom "v29"), "to_do"); ((TAtom "v31"), "f"); ((TAtom "v34"), "data"); ((TAtom "v35"), "to_do"); ((TAtom "v37"), "count"); ((TAtom "v4"), "n"); ((TAtom "v41"), "count"); ((TAtom "v43"), "f"); ((TAtom "v47"), "f"); ((TAtom "v50"), "count"); ((TAtom "v52"), "to_do"); ((TAtom "v53"), "count"); ((TAtom "v54"), "to_do"); ((TAtom "v55"), "data"); ((TAtom "v56"), "count"); ((TAtom "v57"), "data"); ((TAtom "v58"), "n"); ((TAtom "v59"), "to_do"); ((TAtom "v60"), "n"); ((TAtom "v64"), "f"); ((TAtom "v68"), "f"); ((TAtom "v7"), "n"); ((TAtom "v71"), "n"); ((TAtom "v73"), "n")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L8")].

End fn__IO_new_file_write.

Module fn__IO_new_file_xsputn.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_19, 1273%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_19, 1281%N)); ((TAtom "L12"), (file_19, 1282%N)); ((TAtom "L14"), (file_19, 1288%N)); ((TAtom "L24"), (file_19, 1288%N)); ((TAtom "L25"), (file_19, 1288%N)); ((TAtom "L18"), (file_19, 1290%N)); ((TAtom "L40"), (file_19, 1294%N)); ((TAtom "L50"), (file_19, 1293%N)); ((TAtom "L51"), (file_19, 1296%N)); ((TAtom "L59"), (file_19, 1298%N)); ((TAtom "L19"), (file_19, 1305%N)); ((TAtom "L73"), (file_19, 1306%N)); ((TAtom "L20"), (file_19, 1279%N)); ((TAtom "L94"), (file_19, 1311%N)); ((TAtom "L100"), (file_19, 1311%N)); ((TAtom "L101"), (file_19, 1279%N)); ((TAtom "L96"), (file_19, 1277%N)); ((TAtom "L120"), (file_19, 1321%N)); ((TAtom "iw_1.L10"), (file_10, 1049%N)); ((TAtom "iw_1.join"), (file_19, 1321%N)); ((TAtom "L130"), (file_19, 1324%N)); ((TAtom "L145"), (file_19, 1324%N)); ((TAtom "L146"), (file_19, 1324%N)); ((TAtom "L132"), (file_19, 1327%N)); ((TAtom "L166"), (file_19, 1328%N)); ((TAtom "L168"), (file_19, 1328%N)); ((TAtom "iw_2.start"), (file_19, 484%N)); ((TAtom "iw_2.L7"), (file_19, 490%N)); ((TAtom "iw_2.L8"), (file_19, 491%N)); ((TAtom "iw_2.L17"), (file_19, 493%N)); ((TAtom "iw_2.iw_1.L10"), (file_10, 1049%N)); ((TAtom "iw_2.iw_1.join"), (file_19, 493%N)); ((TAtom "iw_2.L49"), (file_19, 497%N)); ((TAtom "iw_2.L9"), (file_19, 499%N)); ((TAtom "iw_2.iw_2.L10"), (file_10, 1049%N)); ((TAtom "iw_2.iw_2.join"), (file_19, 499%N)); ((TAtom "iw_2.L74"), (file_19, 500%N)); ((TAtom "iw_2.L75"), (file_19, 500%N)); ((TAtom "iw_2.L68"), (file_19, 501%N)); ((TAtom "iw_2.L70"), (file_19, 502%N)); ((TAtom "iw_2.L122"), (file_19, 504%N)); ((TAtom "iw_2.L123"), (file_19, 504%N)); ((TAtom "iw_2.L115"), (file_19, 504%N)); ((TAtom "iw_2.L116"), (file_19, 504%N)); ((TAtom "iw_2.L117"), (file_19, 504%N)); ((TAtom "iw_2.join"), (file_19, 1333%N)); ((TAtom "L188"), (file_19, 1335%N)); ((TAtom "L178"), (file_19, 1277%N)); ((TAtom "L198"), (file_19, 1342%N)); ((TAtom "L122"), (file_19, 1277%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "vtable"); ((TAtom "iw_1.v13"), "offset"); ((TAtom "iw_1.v18"), "vtable"); ((TAtom "iw_1.v3"), "vtable"); ((TAtom "iw_1.v4"), "ptr"); ((TAtom "iw_1.v6"), "ptr"); ((TAtom "iw_1.v9"), "offset"); ((TAtom "iw_2.iw_1.v0"), "vtable"); ((TAtom "iw_2.iw_1.v13"), "offset"); ((TAtom "iw_2.iw_1.v18"), "vtable"); ((TAtom "iw_2.iw_1.v3"), "vtable"); ((TAtom "iw_2.iw_1.v4"), "ptr"); ((TAtom "iw_2.iw_1.v6"), "ptr"); ((TAtom "iw_2.iw_1.v9"), "offset"); ((TAtom "iw_2.iw_2.v0"), "vtable"); ((TAtom "iw_2.iw_2.v13"), "offset"); ((TAtom "iw_2.iw_2.v18"), "vtable"); ((TAtom "iw_2.iw_2.v3"), "vtable"); ((TAtom "iw_2.iw_2.v4"), "ptr"); ((TAtom "iw_2.iw_2.v6"), "ptr"); ((TAtom "iw_2.iw_2.v9"), "offset"); ((TAtom "iw_2.v0"), "fp"); ((TAtom "iw_2.v10"), "fp"); ((TAtom "iw_2.v101"), "fp"); ((TAtom "iw_2.v103"), "fp"); ((TAtom "iw_2.v106"), "fp"); ((TAtom "iw_2.v108"), "fp"); ((TAtom "iw_2.v110"), "fp"); ((TAtom "iw_2.v113"), "fp"); ((TAtom "iw_2.v118"), "fp"); ((TAtom "iw_2.v124"), "fp"); ((TAtom "iw_2.v13"), "fp"); ((TAtom "iw_2.v130"), "fp"); ((TAtom "iw_2.v133"), "fp"); ((TAtom "iw_2.v137"), "count"); ((TAtom "iw_2.v2"), "data"); ((TAtom "iw_2.v20"), "fp"); ((TAtom "iw_2.v23"), "fp"); ((TAtom "iw_2.v30"), "fp"); ((TAtom "iw_2.v36"), "fp"); ((TAtom "iw_2.v37"), "fp"); ((TAtom "iw_2.v4"), "to_do"); ((TAtom "iw_2.v40"), "fp"); ((TAtom "iw_2.v46"), "new_pos"); ((TAtom "iw_2.v50"), "new_pos"); ((TAtom "iw_2.v55"), "fp"); ((TAtom "iw_2.v57"), "new_pos"); ((TAtom "iw_2.v58"), "fp"); ((TAtom "iw_2.v64"), "fp"); ((TAtom "iw_2.v65"), "data"); ((TAtom "iw_2.v66"), "to_do"); ((TAtom "iw_2.v67"), "count"); ((TAtom "iw_2.v71"), "fp"); ((TAtom "iw_2.v76"), "count"); ((TAtom "iw_2.v80"), "fp"); ((TAtom "iw_2.v82"), "fp"); ((TAtom "iw_2.v86"), "data"); ((TAtom "iw_2.v87"), "count"); ((TAtom "iw_2.v91"), "fp"); ((TAtom "iw_2.v93"), "fp"); ((TAtom "iw_2.v96"), "fp"); ((TAtom "iw_2.v98"), "fp"); ((TAtom "pr.1"), "s"); ((TAtom "pr.10"), "count"); ((TAtom "pr.11"), "count"); ((TAtom "pr.12"), "count"); ((TAtom "pr.13"), "count"); ((TAtom "pr.14"), "p"); ((TAtom "pr.2"), "to_do"); ((TAtom "pr.3"), "to_do"); ((TAtom "pr.4"), "to_do"); ((TAtom "pr.5"), "to_do"); ((TAtom "pr.6"), "must_flush"); ((TAtom "pr.7"), "must_flush"); ((TAtom "pr.8"), "must_flush"); ((TAtom "pr.9"), "count"); ((TAtom "v0"), "f"); ((TAtom "v102"), "count"); ((TAtom "v103"), "to_do"); ((TAtom "v105"), "to_do"); ((TAtom "v106"), "f"); ((TAtom "v108"), "f"); ((TAtom "v111"), "s"); ((TAtom "v112"), "count"); ((TAtom "v114"), "s"); ((TAtom "v115"), "count"); ((TAtom "v116"), "s"); ((TAtom "v117"), "to_do"); ((TAtom "v118"), "count"); ((TAtom "v119"), "to_do"); ((TAtom "v123"), "to_do"); ((TAtom "v124"), "must_flush"); ((TAtom "v133"), "f"); ((TAtom "v139"), "f"); ((TAtom "v147"), "to_do"); ((TAtom "v15"), "n"); ((TAtom "v151"), "n"); ((TAtom "v152"), "to_do"); ((TAtom "v156"), "f"); ((TAtom "v159"), "f"); ((TAtom "v164"), "block_size"); ((TAtom "v165"), "to_do"); ((TAtom "v169"), "block_size"); ((TAtom "v171"), "to_do"); ((TAtom "v172"), "block_size"); ((TAtom "v175"), "do_write"); ((TAtom "v179"), "do_write"); ((TAtom "v181"), "f"); ((TAtom "v182"), "s"); ((TAtom "v183"), "do_write"); ((TAtom "v184"), "count"); ((TAtom "v185"), "to_do"); ((TAtom "v186"), "count"); ((TAtom "v187"), "to_do"); ((TAtom "v191"), "count"); ((TAtom "v192"), "do_write"); ((TAtom "v194"), "n"); ((TAtom "v195"), "to_do"); ((TAtom "v2"), "data"); ((TAtom "v201"), "to_do"); ((TAtom "v203"), "to_do"); ((TAtom "v204"), "f"); ((TAtom "v205"), "s"); ((TAtom "v206"), "do_write"); ((TAtom "v208"), "to_do"); ((TAtom "v21"), "f"); ((TAtom "v210"), "to_do"); ((TAtom "v211"), "n"); ((TAtom "v212"), "to_do"); ((TAtom "v26"), "f"); ((TAtom "v31"), "f"); ((TAtom "v34"), "f"); ((TAtom "v39"), "count"); ((TAtom "v4"), "n"); ((TAtom "v43"), "count"); ((TAtom "v44"), "n"); ((TAtom "v47"), "s"); ((TAtom "v48"), "n"); ((TAtom "v49"), "p"); ((TAtom "v54"), "p"); ((TAtom "v55"), "s"); ((TAtom "v62"), "p"); ((TAtom "v63"), "p"); ((TAtom "v66"), "p"); ((TAtom "v67"), "s"); ((TAtom "v7"), "data"); ((TAtom "v71"), "count"); ((TAtom "v76"), "f"); ((TAtom "v79"), "f"); ((TAtom "v85"), "f"); ((TAtom "v88"), "f"); ((TAtom "v9"), "n"); ((TAtom "v93"), "count"); ((TAtom "v97"), "count")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L50")].

End fn__IO_new_file_xsputn.

Module fn___GI__IO_file_xsgetn.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_19, 1348%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_19, 1357%N)); ((TAtom "L12"), (file_19, 1360%N)); ((TAtom "L21"), (file_19, 1362%N)); ((TAtom "iw_1.L4"), (file_10, 1059%N)); ((TAtom "iw_1.join"), (file_19, 1363%N)); ((TAtom "L23"), (file_19, 1365%N)); ((TAtom "L39"), (file_19, 1353%N)); ((TAtom "L40"), (file_19, 1370%N)); ((TAtom "L53"), (file_19, 1373%N)); ((TAtom "L54"), (file_19, 1379%N)); ((TAtom "L70"), (file_19, 1381%N)); ((TAtom "L72"), (file_19, 1353%N)); ((TAtom "L89"), (file_19, 1389%N)); ((TAtom "L91"), (file_19, 1396%N)); ((TAtom "L105"), (file_19, 1396%N)); ((TAtom "L106"), (file_19, 1396%N)); ((TAtom "L97"), (file_19, 1399%N)); ((TAtom "L99"), (file_19, 1407%N)); ((TAtom "L157"), (file_19, 1414%N)); ((TAtom "L175"), (file_19, 1416%N)); ((TAtom "L159"), (file_19, 1352%N)); ((TAtom "iw_2.L10"), (file_10, 1049%N)); ((TAtom "iw_2.join"), (file_19, 1419%N)); ((TAtom "L195"), (file_19, 1422%N)); ((TAtom "L200"), (file_19, 1423%N)); ((TAtom "L201"), (file_19, 1425%N)); ((TAtom "L197"), (file_19, 1430%N)); ((TAtom "L218"), (file_19, 1433%N)); ((TAtom "L41"), (file_19, 1351%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "fp"); ((TAtom "iw_1.v13"), "ptr"); ((TAtom "iw_1.v2"), "ptr"); ((TAtom "iw_1.v7"), "ptr"); ((TAtom "iw_1.v8"), "fp"); ((TAtom "iw_2.v0"), "vtable"); ((TAtom "iw_2.v13"), "offset"); ((TAtom "iw_2.v18"), "vtable"); ((TAtom "iw_2.v3"), "vtable"); ((TAtom "iw_2.v4"), "ptr"); ((TAtom "iw_2.v6"), "ptr"); ((TAtom "iw_2.v9"), "offset"); ((TAtom "pr.1"), "want"); ((TAtom "pr.2"), "want"); ((TAtom "pr.3"), "want"); ((TAtom "pr.4"), "want"); ((TAtom "pr.5"), "count"); ((TAtom "pr.6"), "count"); ((TAtom "pr.7"), "s"); ((TAtom "pr.8"), "s"); ((TAtom "pr.9"), "s"); ((TAtom "v0"), "fp"); ((TAtom "v10"), "data"); ((TAtom "v100"), "fp"); ((TAtom "v107"), "want"); ((TAtom "v108"), "fp"); ((TAtom "v11"), "n"); ((TAtom "v111"), "fp"); ((TAtom "v123"), "fp"); ((TAtom "v129"), "fp"); ((TAtom "v131"), "fp"); ((TAtom "v134"), "fp"); ((TAtom "v136"), "fp"); ((TAtom "v139"), "fp"); ((TAtom "v141"), "fp"); ((TAtom "v144"), "fp"); ((TAtom "v146"), "fp"); ((TAtom "v148"), "fp"); ((TAtom "v15"), "fp"); ((TAtom "v151"), "fp"); ((TAtom "v153"), "fp"); ((TAtom "v156"), "want"); ((TAtom "v160"), "fp"); ((TAtom "v166"), "fp"); ((TAtom "v169"), "fp"); ((TAtom "v174"), "block_size"); ((TAtom "v178"), "block_size"); ((TAtom "v180"), "count"); ((TAtom "v181"), "want"); ((TAtom "v182"), "block_size"); ((TAtom "v184"), "count"); ((TAtom "v185"), "fp"); ((TAtom "v191"), "fp"); ((TAtom "v192"), "s"); ((TAtom "v193"), "count"); ((TAtom "v194"), "count"); ((TAtom "v198"), "count"); ((TAtom "v2"), "data"); ((TAtom "v203"), "count"); ((TAtom "v205"), "fp"); ((TAtom "v208"), "fp"); ((TAtom "v212"), "s"); ((TAtom "v213"), "count"); ((TAtom "v214"), "s"); ((TAtom "v215"), "want"); ((TAtom "v216"), "count"); ((TAtom "v217"), "want"); ((TAtom "v221"), "fp"); ((TAtom "v227"), "fp"); ((TAtom "v230"), "count"); ((TAtom "v232"), "n"); ((TAtom "v233"), "want"); ((TAtom "v24"), "fp"); ((TAtom "v30"), "fp"); ((TAtom "v31"), "fp"); ((TAtom "v34"), "fp"); ((TAtom "v38"), "fp"); ((TAtom "v4"), "n"); ((TAtom "v42"), "want"); ((TAtom "v44"), "fp"); ((TAtom "v47"), "fp"); ((TAtom "v52"), "have"); ((TAtom "v56"), "want"); ((TAtom "v57"), "have"); ((TAtom "v59"), "s"); ((TAtom "v60"), "fp"); ((TAtom "v63"), "want"); ((TAtom "v65"), "fp"); ((TAtom "v68"), "want"); ((TAtom "v73"), "have"); ((TAtom "v75"), "s"); ((TAtom "v76"), "fp"); ((TAtom "v79"), "have"); ((TAtom "v80"), "s"); ((TAtom "v81"), "want"); ((TAtom "v82"), "have"); ((TAtom "v83"), "want"); ((TAtom "v84"), "fp"); ((TAtom "v87"), "have"); ((TAtom "v92"), "fp"); ((TAtom "v95"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L39")].

End fn___GI__IO_file_xsgetn.

Module fn__IO_file_xsgetn_mmap.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_19, 1441%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_19, 1445%N)); ((TAtom "L22"), (file_19, 1452%N)); ((TAtom "L28"), (file_19, 1454%N)); ((TAtom "L30"), (file_19, 1446%N)); ((TAtom "L56"), (file_19, 1464%N)); ((TAtom "L62"), (file_19, 1466%N)); ((TAtom "iw_1.L10"), (file_10, 1049%N)); ((TAtom "iw_1.join"), (file_19, 1466%N)); ((TAtom "L64"), (file_19, 1468%N)); ((TAtom "L24"), (file_19, 1446%N)); ((TAtom "L96"), (file_19, 1474%N)); ((TAtom "L98"), (file_19, 1476%N)); ((TAtom "L105"), (file_19, 1478%N)); ((TAtom "L111"), (file_19, 1478%N)); ((TAtom "L112"), (file_19, 1478%N)); ((TAtom "L107"), (file_19, 1446%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "vtable"); ((TAtom "iw_1.v13"), "offset"); ((TAtom "iw_1.v18"), "vtable"); ((TAtom "iw_1.v3"), "vtable"); ((TAtom "iw_1.v4"), "ptr"); ((TAtom "iw_1.v6"), "ptr"); ((TAtom "iw_1.v9"), "offset"); ((TAtom "pr.1"), "n"); ((TAtom "pr.10"), "s"); ((TAtom "pr.11"), "s"); ((TAtom "pr.2"), "n"); ((TAtom "pr.3"), "have"); ((TAtom "pr.4"), "have"); ((TAtom "pr.5"), "have"); ((TAtom "pr.6"), "read_ptr"); ((TAtom "pr.7"), "read_ptr"); ((TAtom "pr.8"), "read_ptr"); ((TAtom "pr.9"), "s"); ((TAtom "v0"), "fp"); ((TAtom "v10"), "read_ptr"); ((TAtom "v100"), "n"); ((TAtom "v102"), "fp"); ((TAtom "v108"), "have"); ((TAtom "v113"), "have"); ((TAtom "v114"), "n"); ((TAtom "v116"), "have"); ((TAtom "v117"), "n"); ((TAtom "v118"), "have"); ((TAtom "v119"), "s"); ((TAtom "v12"), "data"); ((TAtom "v120"), "read_ptr"); ((TAtom "v121"), "have"); ((TAtom "v122"), "s"); ((TAtom "v123"), "fp"); ((TAtom "v125"), "read_ptr"); ((TAtom "v126"), "have"); ((TAtom "v128"), "s"); ((TAtom "v129"), "data"); ((TAtom "v13"), "fp"); ((TAtom "v16"), "fp"); ((TAtom "v2"), "data"); ((TAtom "v21"), "have"); ((TAtom "v25"), "have"); ((TAtom "v26"), "n"); ((TAtom "v31"), "fp"); ((TAtom "v36"), "s"); ((TAtom "v37"), "read_ptr"); ((TAtom "v38"), "have"); ((TAtom "v39"), "s"); ((TAtom "v4"), "n"); ((TAtom "v40"), "n"); ((TAtom "v41"), "have"); ((TAtom "v42"), "n"); ((TAtom "v43"), "fp"); ((TAtom "v44"), "fp"); ((TAtom "v46"), "read_ptr"); ((TAtom "v47"), "fp"); ((TAtom "v50"), "fp"); ((TAtom "v55"), "have"); ((TAtom "v59"), "have"); ((TAtom "v60"), "n"); ((TAtom "v65"), "fp"); ((TAtom "v69"), "s"); ((TAtom "v70"), "data"); ((TAtom "v74"), "fp"); ((TAtom "v8"), "fp"); ((TAtom "v80"), "fp"); ((TAtom "v81"), "data"); ((TAtom "v82"), "n"); ((TAtom "v86"), "fp"); ((TAtom "v88"), "read_ptr"); ((TAtom "v89"), "fp"); ((TAtom "v92"), "read_ptr"); ((TAtom "v95"), "have"); ((TAtom "v99"), "have")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

End fn__IO_file_xsgetn_mmap.

Module fn__IO_file_xsgetn_maybe_mmap.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_19, 1486%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_19, 1492%N)); ((TAtom "iw_1.L10"), (file_10, 1049%N)); ((TAtom "iw_1.join"), (file_19, 1493%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "vtable"); ((TAtom "iw_1.v13"), "offset"); ((TAtom "iw_1.v18"), "vtable"); ((TAtom "iw_1.v3"), "vtable"); ((TAtom "iw_1.v4"), "ptr"); ((TAtom "iw_1.v6"), "ptr"); ((TAtom "iw_1.v9"), "offset"); ((TAtom "v0"), "fp"); ((TAtom "v13"), "fp"); ((TAtom "v14"), "data"); ((TAtom "v15"), "n"); ((TAtom "v2"), "data"); ((TAtom "v4"), "n"); ((TAtom "v6"), "fp"); ((TAtom "v7"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

End fn__IO_file_xsgetn_maybe_mmap.

Module fn_glibc_genops_flush_cleanup.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_20, 43%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_20, 46%N)); ((TAtom "L2"), (file_20, 47%N)); ((TAtom "L18"), (file_20, 47%N)); ((TAtom "L27"), (file_20, 47%N)); ((TAtom "L28"), (file_20, 47%N)); ((TAtom "L21"), (file_20, 47%N)); ((TAtom "L22"), (file_20, 47%N)); ((TAtom "L47"), (file_20, 47%N)); ((TAtom "L71"), (file_20, 47%N)); ((TAtom "L72"), (file_20, 47%N)); ((TAtom "L83"), (file_20, 47%N)); ((TAtom "L48"), (file_20, 47%N)); ((TAtom "L101"), (file_20, 48%N)); ((TAtom "L110"), (file_20, 48%N)); ((TAtom "L111"), (file_20, 48%N)); ((TAtom "L104"), (file_20, 48%N)); ((TAtom "L105"), (file_20, 48%N)); ((TAtom "L121"), (file_20, 48%N)); ((TAtom "L136"), (file_20, 48%N)); ((TAtom "L137"), (file_20, 48%N)); ((TAtom "L148"), (file_20, 48%N)); ((TAtom "L122"), (file_20, 48%N)); ((TAtom "L103"), (file_20, 43%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "not_used"); ((TAtom "v108"), "__libc_single_threaded_internal"); ((TAtom "v134"), "__futex"); ((TAtom "v138"), "__oldval"); ((TAtom "v14"), "run_fp"); ((TAtom "v144"), "__oldval"); ((TAtom "v156"), "__futex"); ((TAtom "v157"), "__futex"); ((TAtom "v158"), "__private"); ((TAtom "v25"), "__libc_single_threaded_internal"); ((TAtom "v30"), "run_fp"); ((TAtom "v39"), "run_fp"); ((TAtom "v44"), "run_fp"); ((TAtom "v51"), "run_fp"); ((TAtom "v58"), "run_fp"); ((TAtom "v6"), "run_fp"); ((TAtom "v64"), "run_fp"); ((TAtom "v66"), "__futex"); ((TAtom "v69"), "__futex"); ((TAtom "v73"), "__oldval"); ((TAtom "v79"), "__oldval"); ((TAtom "v91"), "__futex"); ((TAtom "v92"), "__futex"); ((TAtom "v93"), "__private"); ((TAtom "v95"), "run_fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L136"); (TAtom "L71")].

End fn_glibc_genops_flush_cleanup.

Module fn___GI__IO_un_link.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_20, 65%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_20, 72%N)); ((TAtom "L2"), (file_20, 72%N)); ((TAtom "L31"), (file_20, 73%N)); ((TAtom "L32"), (file_20, 73%N)); ((TAtom "L25"), (file_20, 73%N)); ((TAtom "L26"), (file_20, 73%N)); ((TAtom "L45"), (file_20, 73%N)); ((TAtom "L65"), (file_20, 73%N)); ((TAtom "L66"), (file_20, 73%N)); ((TAtom "L70"), (file_20, 73%N)); ((TAtom "L59"), (file_20, 73%N)); ((TAtom "L46"), (file_20, 73%N)); ((TAtom "L22"), (file_20, 74%N)); ((TAtom "L96"), (file_20, 75%N)); ((TAtom "L107"), (file_20, 75%N)); ((TAtom "L108"), (file_20, 75%N)); ((TAtom "L101"), (file_20, 75%N)); ((TAtom "L102"), (file_20, 75%N)); ((TAtom "L127"), (file_20, 75%N)); ((TAtom "L151"), (file_20, 75%N)); ((TAtom "L152"), (file_20, 75%N)); ((TAtom "L156"), (file_20, 75%N)); ((TAtom "L145"), (file_20, 75%N)); ((TAtom "L128"), (file_20, 75%N)); ((TAtom "L91"), (file_20, 77%N)); ((TAtom "L185"), (file_20, 81%N)); ((TAtom "L199"), (file_20, 85%N)); ((TAtom "L179"), (file_20, 96%N)); ((TAtom "L262"), (file_20, 98%N)); ((TAtom "L271"), (file_20, 98%N)); ((TAtom "L272"), (file_20, 98%N)); ((TAtom "L265"), (file_20, 98%N)); ((TAtom "L266"), (file_20, 98%N)); ((TAtom "L288"), (file_20, 98%N)); ((TAtom "L309"), (file_20, 98%N)); ((TAtom "L310"), (file_20, 98%N)); ((TAtom "L321"), (file_20, 98%N)); ((TAtom "L289"), (file_20, 98%N)); ((TAtom "L257"), (file_20, 99%N)); ((TAtom "L348"), (file_20, 100%N)); ((TAtom "L349"), (file_20, 100%N)); ((TAtom "L342"), (file_20, 100%N)); ((TAtom "L343"), (file_20, 100%N)); ((TAtom "L359"), (file_20, 100%N)); ((TAtom "L374"), (file_20, 100%N)); ((TAtom "L375"), (file_20, 100%N)); ((TAtom "L386"), (file_20, 100%N)); ((TAtom "L360"), (file_20, 100%N)); ((TAtom "L401"), (file_20, 101%N)); ((TAtom "L4"), (file_20, 65%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "pr.1"), "f"); ((TAtom "pr.2"), "_cleanup_start_doit"); ((TAtom "v0"), "fp"); ((TAtom "v100"), "__self"); ((TAtom "v105"), "__libc_single_threaded_internal"); ((TAtom "v109"), "fp"); ((TAtom "v119"), "fp"); ((TAtom "v12"), "_cleanup_routine"); ((TAtom "v122"), "fp"); ((TAtom "v126"), "__self"); ((TAtom "v130"), "fp"); ((TAtom "v135"), "__self"); ((TAtom "v140"), "fp"); ((TAtom "v142"), "__futex"); ((TAtom "v147"), "__futex"); ((TAtom "v148"), "__atg3_old"); ((TAtom "v149"), "__atg3_old"); ((TAtom "v164"), "__futex"); ((TAtom "v165"), "__futex"); ((TAtom "v166"), "fp"); ((TAtom "v17"), "_cleanup_start_doit"); ((TAtom "v170"), "__self"); ((TAtom "v171"), "fp"); ((TAtom "v18"), "_cleanup_routine"); ((TAtom "v181"), "_IO_list_all"); ((TAtom "v19"), "_cleanup_start_doit"); ((TAtom "v190"), "fp"); ((TAtom "v192"), "pr"); ((TAtom "v194"), "fp"); ((TAtom "v196"), "nx"); ((TAtom "v197"), "pr"); ((TAtom "v198"), "nx"); ((TAtom "v202"), "nx"); ((TAtom "v206"), "nx"); ((TAtom "v208"), "pr"); ((TAtom "v212"), "fp"); ((TAtom "v214"), "_IO_list_all"); ((TAtom "v220"), "_IO_list_all"); ((TAtom "v222"), "_IO_list_all"); ((TAtom "v224"), "_IO_list_all"); ((TAtom "v225"), "f"); ((TAtom "v230"), "f"); ((TAtom "v237"), "f"); ((TAtom "v239"), "fp"); ((TAtom "v24"), "__self"); ((TAtom "v243"), "f"); ((TAtom "v244"), "fp"); ((TAtom "v248"), "f"); ((TAtom "v250"), "f"); ((TAtom "v251"), "fp"); ((TAtom "v258"), "fp"); ((TAtom "v269"), "__libc_single_threaded_internal"); ((TAtom "v273"), "fp"); ((TAtom "v281"), "fp"); ((TAtom "v285"), "fp"); ((TAtom "v29"), "__libc_single_threaded_internal"); ((TAtom "v291"), "fp"); ((TAtom "v297"), "fp"); ((TAtom "v302"), "fp"); ((TAtom "v304"), "__futex"); ((TAtom "v307"), "__futex"); ((TAtom "v311"), "__oldval"); ((TAtom "v317"), "__oldval"); ((TAtom "v329"), "__futex"); ((TAtom "v330"), "__futex"); ((TAtom "v331"), "__private"); ((TAtom "v332"), "fp"); ((TAtom "v346"), "__libc_single_threaded_internal"); ((TAtom "v372"), "__futex"); ((TAtom "v376"), "__oldval"); ((TAtom "v382"), "__oldval"); ((TAtom "v394"), "__futex"); ((TAtom "v395"), "__futex"); ((TAtom "v396"), "__private"); ((TAtom "v404"), "_cleanup_start_doit"); ((TAtom "v408"), "_cleanup_routine"); ((TAtom "v44"), "__self"); ((TAtom "v5"), "fp"); ((TAtom "v51"), "__self"); ((TAtom "v61"), "__futex"); ((TAtom "v62"), "__atg3_old"); ((TAtom "v63"), "__atg3_old"); ((TAtom "v78"), "__futex"); ((TAtom "v79"), "__futex"); ((TAtom "v82"), "__self"); ((TAtom "v88"), "fp"); ((TAtom "v92"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L309"); (TAtom "L374")].

End fn___GI__IO_un_link.

Module fn__IO_switch_to_main_get_area.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_20, 152%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_20, 156%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fp"); ((TAtom "v10"), "fp"); ((TAtom "v12"), "fp"); ((TAtom "v15"), "fp"); ((TAtom "v17"), "tmp"); ((TAtom "v18"), "fp"); ((TAtom "v20"), "tmp"); ((TAtom "v21"), "fp"); ((TAtom "v23"), "fp"); ((TAtom "v26"), "fp"); ((TAtom "v28"), "tmp"); ((TAtom "v29"), "fp"); ((TAtom "v3"), "fp"); ((TAtom "v31"), "fp"); ((TAtom "v7"), "fp"); ((TAtom "v9"), "tmp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

End fn__IO_switch_to_main_get_area.

Module fn__IO_switch_to_backup_area.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_20, 171%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_20, 175%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fp"); ((TAtom "v11"), "fp"); ((TAtom "v14"), "fp"); ((TAtom "v16"), "tmp"); ((TAtom "v17"), "fp"); ((TAtom "v19"), "tmp"); ((TAtom "v20"), "fp"); ((TAtom "v22"), "fp"); ((TAtom "v25"), "fp"); ((TAtom "v27"), "tmp"); ((TAtom "v28"), "fp"); ((TAtom "v3"), "fp"); ((TAtom "v30"), "fp"); ((TAtom "v6"), "fp"); ((TAtom "v8"), "tmp"); ((TAtom "v9"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

End fn__IO_switch_to_backup_area.

Module fn___GI__IO_switch_to_get_mode.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_20, 188%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_20, 191%N)); ((TAtom "L2"), (file_20, 192%N)); ((TAtom "iw_1.L10"), (file_10, 1049%N)); ((TAtom "iw_1.join"), (file_20, 192%N)); ((TAtom "L14"), (file_20, 193%N)); ((TAtom "L4"), (file_20, 194%N)); ((TAtom "L30"), (file_20, 195%N)); ((TAtom "L31"), (file_20, 198%N)); ((TAtom "L46"), (file_20, 200%N)); ((TAtom "L32"), (file_20, 202%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "vtable"); ((TAtom "iw_1.v13"), "offset"); ((TAtom "iw_1.v18"), "vtable"); ((TAtom "iw_1.v3"), "vtable"); ((TAtom "iw_1.v4"), "ptr"); ((TAtom "iw_1.v6"), "ptr"); ((TAtom "iw_1.v9"), "offset"); ((TAtom "v0"), "fp"); ((TAtom "v17"), "fp"); ((TAtom "v23"), "fp"); ((TAtom "v33"), "fp"); ((TAtom "v36"), "fp"); ((TAtom "v38"), "fp"); ((TAtom "v41"), "fp"); ((TAtom "v43"), "fp"); ((TAtom "v49"), "fp"); ((TAtom "v5"), "fp"); ((TAtom "v52"), "fp"); ((TAtom "v58"), "fp"); ((TAtom "v60"), "fp"); ((TAtom "v63"), "fp"); ((TAtom "v65"), "fp"); ((TAtom "v68"), "fp"); ((TAtom "v70"), "fp"); ((TAtom "v72"), "fp"); ((TAtom "v74"), "fp"); ((TAtom "v77"), "fp"); ((TAtom "v8"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

End fn___GI__IO_switch_to_get_mode.

Module fn___GI__IO_free_backup_area.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_20, 211%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_20, 214%N)); ((TAtom "L2"), (file_20, 215%N)); ((TAtom "L4"), (file_20, 216%N)); ((TAtom "iw_1.L4"), (file_10, 1059%N)); ((TAtom "iw_1.join"), (file_20, 217%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "fp"); ((TAtom "iw_1.v13"), "ptr"); ((TAtom "iw_1.v2"), "ptr"); ((TAtom "iw_1.v7"), "ptr"); ((TAtom "iw_1.v8"), "fp"); ((TAtom "v0"), "fp"); ((TAtom "v10"), "fp"); ((TAtom "v13"), "fp"); ((TAtom "v15"), "fp"); ((TAtom "v17"), "fp"); ((TAtom "v5"), "fp"); ((TAtom "v8"), "fp"); ((TAtom "v9"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

End fn___GI__IO_free_backup_area.

Module fn___GI___overflow.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_20, 223%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_20, 227%N)); ((TAtom "L13"), (file_20, 228%N)); ((TAtom "L23"), (file_20, 228%N)); ((TAtom "L25"), (file_20, 228%N)); ((TAtom "L6"), (file_20, 229%N)); ((TAtom "iw_1.L10"), (file_10, 1049%N)); ((TAtom "iw_1.join"), (file_20, 229%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "vtable"); ((TAtom "iw_1.v13"), "offset"); ((TAtom "iw_1.v18"), "vtable"); ((TAtom "iw_1.v3"), "vtable"); ((TAtom "iw_1.v4"), "ptr"); ((TAtom "iw_1.v6"), "ptr"); ((TAtom "iw_1.v9"), "offset"); ((TAtom "pr.1"), "__result"); ((TAtom "pr.2"), "__result"); ((TAtom "v0"), "f"); ((TAtom "v12"), "__result"); ((TAtom "v16"), "__result"); ((TAtom "v2"), "ch"); ((TAtom "v26"), "f"); ((TAtom "v30"), "f"); ((TAtom "v33"), "f"); ((TAtom "v35"), "__result"); ((TAtom "v49"), "f"); ((TAtom "v52"), "__result"); ((TAtom "v53"), "f"); ((TAtom "v54"), "__result"); ((TAtom "v55"), "__result"); ((TAtom "v56"), "__result"); ((TAtom "v57"), "f"); ((TAtom "v63"), "f"); ((TAtom "v64"), "ch"); ((TAtom "v7"), "f")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

End fn___GI___overflow.

Module fn_glibc_genops_save_for_backup.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_20, 233%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_20, 142%N)); ((TAtom "iw_1.L16"), (file_20, 143%N)); ((TAtom "iw_1.L17"), (file_20, 145%N)); ((TAtom "iw_1.L24"), (file_20, 146%N)); ((TAtom "iw_1.L26"), (file_20, 142%N)); ((TAtom "iw_1.join"), (file_20, 239%N)); ((TAtom "L31"), (file_20, 249%N)); ((TAtom "L42"), (file_20, 251%N)); ((TAtom "L44"), (file_20, 252%N)); ((TAtom "L51"), (file_20, 254%N)); ((TAtom "L52"), (file_20, 261%N)); ((TAtom "L53"), (file_20, 264%N)); ((TAtom "iw_2.L4"), (file_10, 1059%N)); ((TAtom "iw_2.join"), (file_20, 265%N)); ((TAtom "L32"), (file_20, 270%N)); ((TAtom "L105"), (file_20, 273%N)); ((TAtom "L106"), (file_20, 280%N)); ((TAtom "L141"), (file_20, 281%N)); ((TAtom "L33"), (file_20, 242%N)); ((TAtom "L175"), (file_20, 244%N)); ((TAtom "L176"), (file_20, 289%N)); ((TAtom "L178"), (file_20, 290%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.pr.1"), "least_so_far"); ((TAtom "iw_1.pr.2"), "least_so_far"); ((TAtom "iw_1.pr.3"), "mark"); ((TAtom "iw_1.v0"), "fp"); ((TAtom "iw_1.v11"), "least_so_far"); ((TAtom "iw_1.v13"), "fp"); ((TAtom "iw_1.v15"), "mark"); ((TAtom "iw_1.v2"), "end_p"); ((TAtom "iw_1.v20"), "mark"); ((TAtom "iw_1.v27"), "mark"); ((TAtom "iw_1.v30"), "least_so_far"); ((TAtom "iw_1.v33"), "mark"); ((TAtom "iw_1.v36"), "least_so_far"); ((TAtom "iw_1.v37"), "mark"); ((TAtom "iw_1.v38"), "mark"); ((TAtom "iw_1.v39"), "least_so_far"); ((TAtom "iw_1.v5"), "end_p"); ((TAtom "iw_1.v6"), "fp"); ((TAtom "iw_2.v0"), "fp"); ((TAtom "iw_2.v13"), "ptr"); ((TAtom "iw_2.v2"), "ptr"); ((TAtom "iw_2.v7"), "ptr"); ((TAtom "iw_2.v8"), "fp"); ((TAtom "pr.1"), "avail"); ((TAtom "pr.2"), "mark"); ((TAtom "v0"), "fp"); ((TAtom "v10"), "fp"); ((TAtom "v100"), "needed_size"); ((TAtom "v102"), "current_Bsize"); ((TAtom "v103"), "needed_size"); ((TAtom "v104"), "avail"); ((TAtom "v108"), "least_mark"); ((TAtom "v110"), "fp"); ((TAtom "v113"), "avail"); ((TAtom "v115"), "fp"); ((TAtom "v118"), "least_mark"); ((TAtom "v120"), "least_mark"); ((TAtom "v123"), "fp"); ((TAtom "v126"), "avail"); ((TAtom "v128"), "least_mark"); ((TAtom "v130"), "fp"); ((TAtom "v133"), "end_p"); ((TAtom "v134"), "fp"); ((TAtom "v144"), "needed_size"); ((TAtom "v146"), "fp"); ((TAtom "v149"), "avail"); ((TAtom "v151"), "fp"); ((TAtom "v154"), "least_mark"); ((TAtom "v156"), "needed_size"); ((TAtom "v158"), "fp"); ((TAtom "v16"), "least_mark"); ((TAtom "v160"), "fp"); ((TAtom "v163"), "avail"); ((TAtom "v165"), "end_p"); ((TAtom "v166"), "fp"); ((TAtom "v17"), "needed_size"); ((TAtom "v171"), "delta"); ((TAtom "v172"), "fp"); ((TAtom "v174"), "mark"); ((TAtom "v179"), "mark"); ((TAtom "v183"), "mark"); ((TAtom "v186"), "delta"); ((TAtom "v189"), "mark"); ((TAtom "v19"), "fp"); ((TAtom "v190"), "mark"); ((TAtom "v2"), "end_p"); ((TAtom "v22"), "fp"); ((TAtom "v27"), "current_Bsize"); ((TAtom "v34"), "needed_size"); ((TAtom "v35"), "current_Bsize"); ((TAtom "v38"), "avail"); ((TAtom "v39"), "needed_size"); ((TAtom "v41"), "new_buffer"); ((TAtom "v45"), "new_buffer"); ((TAtom "v5"), "fp"); ((TAtom "v54"), "least_mark"); ((TAtom "v56"), "new_buffer"); ((TAtom "v57"), "avail"); ((TAtom "v59"), "fp"); ((TAtom "v6"), "end_p"); ((TAtom "v62"), "least_mark"); ((TAtom "v64"), "least_mark"); ((TAtom "v67"), "fp"); ((TAtom "v7"), "least_mark"); ((TAtom "v70"), "end_p"); ((TAtom "v71"), "fp"); ((TAtom "v78"), "new_buffer"); ((TAtom "v79"), "avail"); ((TAtom "v81"), "fp"); ((TAtom "v84"), "least_mark"); ((TAtom "v86"), "needed_size"); ((TAtom "v88"), "fp"); ((TAtom "v89"), "fp"); ((TAtom "v9"), "end_p"); ((TAtom "v92"), "fp"); ((TAtom "v94"), "new_buffer"); ((TAtom "v95"), "fp"); ((TAtom "v97"), "new_buffer"); ((TAtom "v98"), "avail")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L175"); (TAtom "iw_1.L16")].

End fn_glibc_genops_save_for_backup.

End HiAtexitSrc02.
