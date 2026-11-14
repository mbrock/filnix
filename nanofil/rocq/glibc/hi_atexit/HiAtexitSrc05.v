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
Module HiAtexitSrc05.

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


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2")]); ((TAtom "iw_1.L16"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "iw_1.v9"); (TAtom "v0")]); ((TAtom "iw_1.L17"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.pr.3"); (TAtom "iw_1.v9"); (TAtom "v0")]); ((TAtom "iw_1.L24"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk2"); (TAtom "iw_1.pr.3"); (TAtom "iw_1.v9"); (TAtom "v0")]); ((TAtom "iw_1.L26"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk2"); (TAtom "iw_1.pr.3"); (TAtom "iw_1.v9"); (TAtom "v0")]); ((TAtom "iw_1.join"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v22"); (TAtom "iw_1.v9"); (TAtom "v0")]); ((TAtom "L31"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk6"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v22"); (TAtom "iw_1.v9"); (TAtom "v0"); (TAtom "v17")]); ((TAtom "L42"), []); ((TAtom "L44"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk6"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v22"); (TAtom "iw_1.v9"); (TAtom "v0"); (TAtom "v17"); (TAtom "v41")]); ((TAtom "L51"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk6"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v22"); (TAtom "iw_1.v9"); (TAtom "v0"); (TAtom "v17"); (TAtom "v41")]); ((TAtom "L52"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk6"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v22"); (TAtom "iw_1.v9"); (TAtom "v0"); (TAtom "v17"); (TAtom "v41")]); ((TAtom "L53"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk6"); (TAtom "iw_1.v22"); (TAtom "iw_1.v9"); (TAtom "v0"); (TAtom "v17"); (TAtom "v41")]); ((TAtom "iw_2.L4"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk12"); (TAtom "chk6"); (TAtom "iw_1.v22"); (TAtom "iw_1.v9"); (TAtom "v0"); (TAtom "v17"); (TAtom "v41"); (TAtom "v91")]); ((TAtom "iw_2.join"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk12"); (TAtom "chk6"); (TAtom "iw_1.v22"); (TAtom "iw_1.v9"); (TAtom "v0"); (TAtom "v17"); (TAtom "v41")]); ((TAtom "L32"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk5"); (TAtom "chk6"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v22"); (TAtom "iw_1.v9"); (TAtom "v0"); (TAtom "v17"); (TAtom "v27")]); ((TAtom "L105"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk6"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v22"); (TAtom "iw_1.v9"); (TAtom "v0"); (TAtom "v104")]); ((TAtom "L106"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk5"); (TAtom "chk6"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v22"); (TAtom "iw_1.v9"); (TAtom "v0"); (TAtom "v104"); (TAtom "v17")]); ((TAtom "L141"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk5"); (TAtom "chk6"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v22"); (TAtom "iw_1.v9"); (TAtom "v0"); (TAtom "v104"); (TAtom "v17")]); ((TAtom "L33"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "iw_1.v22"); (TAtom "iw_1.v9"); (TAtom "v0")]); ((TAtom "L175"), [(TAtom "iw_1.v22"); (TAtom "v171")]); ((TAtom "L176"), [(TAtom "iw_1.v22"); (TAtom "pr.2"); (TAtom "v171")]); ((TAtom "L178"), [])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "iw_1.v11"); (TAtom "iw_1.v15"); (TAtom "iw_1.v9"); (TAtom "v0")]); ((TAtom "iw_1.L16"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.pr.3"); (TAtom "iw_1.v22"); (TAtom "iw_1.v9"); (TAtom "v0")]); ((TAtom "iw_1.L17"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk2"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.pr.3"); (TAtom "iw_1.v9"); (TAtom "v0")]); ((TAtom "iw_1.L24"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk2"); (TAtom "iw_1.pr.3"); (TAtom "iw_1.v36"); (TAtom "iw_1.v9"); (TAtom "v0")]); ((TAtom "iw_1.L26"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "iw_1.pr.2"); (TAtom "iw_1.v38"); (TAtom "iw_1.v9"); (TAtom "v0")]); ((TAtom "iw_1.join"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk5"); (TAtom "chk6"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v22"); (TAtom "iw_1.v9"); (TAtom "v0"); (TAtom "v17"); (TAtom "v27")]); ((TAtom "L31"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk6"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v22"); (TAtom "iw_1.v9"); (TAtom "v0"); (TAtom "v17"); (TAtom "v41")]); ((TAtom "L42"), []); ((TAtom "L44"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk6"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v22"); (TAtom "iw_1.v9"); (TAtom "v0"); (TAtom "v17"); (TAtom "v41")]); ((TAtom "L51"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk6"); (TAtom "iw_1.v22"); (TAtom "iw_1.v9"); (TAtom "v0"); (TAtom "v17"); (TAtom "v41")]); ((TAtom "L52"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk6"); (TAtom "iw_1.v22"); (TAtom "iw_1.v9"); (TAtom "v0"); (TAtom "v17"); (TAtom "v41")]); ((TAtom "L53"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk12"); (TAtom "chk6"); (TAtom "iw_1.v22"); (TAtom "iw_1.v9"); (TAtom "v0"); (TAtom "v17"); (TAtom "v41"); (TAtom "v91")]); ((TAtom "iw_2.L4"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk12"); (TAtom "chk6"); (TAtom "iw_1.v22"); (TAtom "iw_1.v9"); (TAtom "v0"); (TAtom "v17"); (TAtom "v41")]); ((TAtom "iw_2.join"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "iw_1.v22"); (TAtom "iw_1.v9"); (TAtom "v0")]); ((TAtom "L32"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk5"); (TAtom "chk6"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v22"); (TAtom "iw_1.v9"); (TAtom "v0"); (TAtom "v104"); (TAtom "v17")]); ((TAtom "L105"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "iw_1.v22"); (TAtom "iw_1.v9"); (TAtom "v0"); (TAtom "v104")]); ((TAtom "L106"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk5"); (TAtom "chk6"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v22"); (TAtom "iw_1.v9"); (TAtom "v0"); (TAtom "v104"); (TAtom "v17")]); ((TAtom "L141"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "iw_1.v22"); (TAtom "iw_1.v9"); (TAtom "v0"); (TAtom "v104")]); ((TAtom "L33"), [(TAtom "iw_1.v22"); (TAtom "v171"); (TAtom "v174")]); ((TAtom "L175"), [(TAtom "iw_1.v22"); (TAtom "pr.2"); (TAtom "v171")]); ((TAtom "L176"), [(TAtom "iw_1.v22"); (TAtom "v171"); (TAtom "v190")]); ((TAtom "L178"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "iw_1.v7")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (24))); (8%N, (TApp "tmp" [(TAtom "iw_1.v14")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (96)))]); ((TAtom "iw_1.L16"), []); ((TAtom "iw_1.L17"), [(2%N, (TApp "tmp" [(TAtom "iw_1.v28")]), (0), (Some 4), true, false, (Some (TAtom "iw_1.pr.3")), (Some (16)))]); ((TAtom "iw_1.L24"), [(1%N, (TApp "tmp" [(TAtom "iw_1.v28")]), (0), (Some 4), true, false, (Some (TAtom "iw_1.pr.3")), (Some (16)))]); ((TAtom "iw_1.L26"), [(1%N, (TApp "tmp" [(TAtom "iw_1.pr.3")]), (0), (Some 8), true, false, (Some (TAtom "iw_1.pr.3")), (Some (0)))]); ((TAtom "iw_1.join"), [(2%N, (TApp "tmp" [(TAtom "v11")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (24))); (8%N, (TApp "tmp" [(TAtom "v20")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (88))); (10%N, (TApp "tmp" [(TAtom "v20")]), (-16), (Some 8), true, false, (Some (TAtom "v0")), (Some (72)))]); ((TAtom "L31"), []); ((TAtom "L42"), []); ((TAtom "L44"), []); ((TAtom "L51"), [(3%N, (TApp "tmp" [(TAtom "v60")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (88))); (9%N, (TApp "tmp" [(TAtom "v68")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (24))); (10%N, (TApp "tmp" [(TAtom "v68")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (24)))]); ((TAtom "L52"), [(3%N, (TApp "tmp" [(TAtom "v82")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (24)))]); ((TAtom "L53"), [(2%N, (TApp "tmp" [(TAtom "v90")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (72)))]); ((TAtom "iw_2.L4"), []); ((TAtom "iw_2.join"), [(2%N, (TApp "tmp" [(TAtom "v93")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (72))); (7%N, (TApp "tmp" [(TAtom "v96")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (88)))]); ((TAtom "L32"), []); ((TAtom "L105"), [(1%N, (TApp "tmp" [(TAtom "v20")]), (-16), (Some 8), true, false, (Some (TAtom "v0")), (Some (72))); (4%N, (TApp "tmp" [(TAtom "v20")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (88))); (9%N, (TApp "tmp" [(TAtom "v111")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (72))); (14%N, (TApp "tmp" [(TAtom "v131")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (24))); (15%N, (TApp "tmp" [(TAtom "v131")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (24)))]); ((TAtom "L106"), []); ((TAtom "L141"), [(1%N, (TApp "tmp" [(TAtom "v20")]), (-16), (Some 8), true, false, (Some (TAtom "v0")), (Some (72))); (4%N, (TApp "tmp" [(TAtom "v11")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (24)))]); ((TAtom "L33"), [(3%N, (TApp "tmp" [(TAtom "v161")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (72))); (6%N, (TApp "tmp" [(TAtom "v159")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (80))); (9%N, (TApp "tmp" [(TAtom "v167")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (24))); (14%N, (TApp "tmp" [(TAtom "v173")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (96)))]); ((TAtom "L175"), []); ((TAtom "L176"), [(2%N, (TApp "tmp" [(TAtom "v184")]), (0), (Some 4), true, false, (Some (TAtom "pr.2")), (Some (16))); (6%N, (TApp "tmp" [(TAtom "v184")]), (0), (Some 4), false, true, (Some (TAtom "pr.2")), (Some (16))); (8%N, (TApp "tmp" [(TAtom "pr.2")]), (0), (Some 8), true, false, (Some (TAtom "pr.2")), (Some (0)))]); ((TAtom "L178"), [])].


End fn_glibc_genops_save_for_backup.

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


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "L20"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L22"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L2"), []); ((TAtom "L4"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L69"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L79"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L81"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L62"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L113"), [(TAtom "chk0"); (TAtom "chk7"); (TAtom "v0")]); ((TAtom "L119"), []); ((TAtom "L115"), [(TAtom "chk0"); (TAtom "chk7"); (TAtom "v0")]); ((TAtom "L128"), [(TAtom "chk8"); (TAtom "v0")]); ((TAtom "L130"), [(TAtom "chk0"); (TAtom "chk7"); (TAtom "chk8"); (TAtom "chk9"); (TAtom "v0")]); ((TAtom "L145"), [(TAtom "chk0"); (TAtom "chk8"); (TAtom "chk9"); (TAtom "v0")]); ((TAtom "L152"), [(TAtom "chk13"); (TAtom "v0")]); ((TAtom "L147"), [(TAtom "chk0"); (TAtom "chk9"); (TAtom "v0")]); ((TAtom "L169"), [(TAtom "chk0"); (TAtom "chk9"); (TAtom "v0")]); ((TAtom "L178"), []); ((TAtom "L170"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v176")]); ((TAtom "L188"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L171"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "iw_1.L10"), [(TAtom "v0"); (TAtom "v200")]); ((TAtom "iw_1.join"), [(TAtom "v0"); (TAtom "v200")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L20"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L22"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L2"), []); ((TAtom "L4"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L69"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L79"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L81"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L62"), [(TAtom "chk0"); (TAtom "chk7"); (TAtom "v0")]); ((TAtom "L113"), [(TAtom "chk0"); (TAtom "chk7"); (TAtom "v0")]); ((TAtom "L119"), []); ((TAtom "L115"), [(TAtom "chk0"); (TAtom "chk7"); (TAtom "chk8"); (TAtom "chk9"); (TAtom "v0")]); ((TAtom "L128"), []); ((TAtom "L130"), [(TAtom "chk0"); (TAtom "chk8"); (TAtom "chk9"); (TAtom "v0")]); ((TAtom "L145"), [(TAtom "chk0"); (TAtom "chk13"); (TAtom "chk9"); (TAtom "v0")]); ((TAtom "L152"), []); ((TAtom "L147"), [(TAtom "chk0"); (TAtom "chk9"); (TAtom "v0"); (TAtom "v176")]); ((TAtom "L169"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L178"), []); ((TAtom "L170"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L188"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L171"), [(TAtom "v0"); (TAtom "v200")]); ((TAtom "iw_1.L10"), [(TAtom "v0"); (TAtom "v200")]); ((TAtom "iw_1.join"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "v24")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (192)))]); ((TAtom "L20"), [(2%N, (TApp "tmp" [(TAtom "v28")]), (0), (Some 4), false, true, (Some (TAtom "v0")), (Some (192)))]); ((TAtom "L22"), [(1%N, (TApp "tmp" [(TAtom "v24")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (192)))]); ((TAtom "L2"), []); ((TAtom "L4"), [(1%N, (TApp "tmp" [(TAtom "v24")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (192)))]); ((TAtom "L69"), [(1%N, (TApp "tmp" [(TAtom "v24")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (192)))]); ((TAtom "L79"), [(2%N, (TApp "tmp" [(TAtom "v87")]), (0), (Some 4), false, true, (Some (TAtom "v0")), (Some (192)))]); ((TAtom "L81"), [(1%N, (TApp "tmp" [(TAtom "v24")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (192)))]); ((TAtom "L62"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0)))]); ((TAtom "L113"), []); ((TAtom "L119"), []); ((TAtom "L115"), [(2%N, (TApp "tmp" [(TAtom "v132")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (8))); (5%N, (TApp "tmp" [(TAtom "v135")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (16)))]); ((TAtom "L128"), [(1%N, (TApp "tmp" [(TAtom "v132")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (8))); (3%N, (TApp "tmp" [(TAtom "v142")]), (0), (Some 1), true, false, (Some (TAtom "v142")), (Some (0)))]); ((TAtom "L130"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0)))]); ((TAtom "L145"), [(3%N, (TApp "tmp" [(TAtom "v156")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (8))); (6%N, (TApp "tmp" [(TAtom "v159")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (16)))]); ((TAtom "L152"), [(1%N, (TApp "tmp" [(TAtom "v156")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (8))); (3%N, (TApp "tmp" [(TAtom "v166")]), (0), (Some 1), true, false, (Some (TAtom "v166")), (Some (0)))]); ((TAtom "L147"), [(2%N, (TApp "tmp" [(TAtom "v173")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (96)))]); ((TAtom "L169"), [(2%N, (TApp "tmp" [(TAtom "v183")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (16)))]); ((TAtom "L178"), []); ((TAtom "L170"), [(2%N, (TApp "tmp" [(TAtom "v192")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (80)))]); ((TAtom "L188"), []); ((TAtom "L171"), [(2%N, (TApp "tmp" [(TAtom "v199")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (216)))]); ((TAtom "iw_1.L10"), []); ((TAtom "iw_1.join"), [(2%N, (TApp "tmp" [(TAtom "v202")]), (0), (Some 8), true, false, (Some (TAtom "v200")), (Some (32)))])].


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


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L16"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L17"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L8"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L10"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L33"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L34"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L35"), [])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L16"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2"); (TAtom "v21"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L17"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L8"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L10"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L33"), []); ((TAtom "L34"), []); ((TAtom "L35"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "v12")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (56)))]); ((TAtom "L16"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0)))]); ((TAtom "L17"), []); ((TAtom "L8"), [(1%N, (TApp "tmp" [(TAtom "v12")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (56)))]); ((TAtom "L10"), [(2%N, (TApp "tmp" [(TAtom "v28")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (56))); (5%N, (TApp "tmp" [(TAtom "v31")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (64)))]); ((TAtom "L33"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0))); (4%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), false, true, (Some (TAtom "v0")), (Some (0)))]); ((TAtom "L34"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0))); (4%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), false, true, (Some (TAtom "v0")), (Some (0)))]); ((TAtom "L35"), [])].


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


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "L2"), []); ((TAtom "L4"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L18"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L19"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L11"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "iw_1.L10"), [(TAtom "v0"); (TAtom "v31")]); ((TAtom "iw_1.join"), [(TAtom "v0"); (TAtom "v31")]); ((TAtom "L26"), []); ((TAtom "L13"), [(TAtom "v0")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L2"), []); ((TAtom "L4"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L18"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v23")]); ((TAtom "L19"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L11"), [(TAtom "v0"); (TAtom "v31")]); ((TAtom "iw_1.L10"), [(TAtom "v0"); (TAtom "v31")]); ((TAtom "iw_1.join"), [(TAtom "v0")]); ((TAtom "L26"), []); ((TAtom "L13"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "v6")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (56)))]); ((TAtom "L2"), []); ((TAtom "L4"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0)))]); ((TAtom "L18"), [(2%N, (TApp "tmp" [(TAtom "v21")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (192)))]); ((TAtom "L19"), []); ((TAtom "L11"), [(2%N, (TApp "tmp" [(TAtom "v30")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (216)))]); ((TAtom "iw_1.L10"), []); ((TAtom "iw_1.join"), [(2%N, (TApp "tmp" [(TAtom "v33")]), (0), (Some 8), true, false, (Some (TAtom "v31")), (Some (104)))]); ((TAtom "L26"), []); ((TAtom "L13"), [])].


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


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "iw_1.L10"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v5")]); ((TAtom "iw_1.join"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v5")]); ((TAtom "L11"), []); ((TAtom "L13"), [(TAtom "chk0"); (TAtom "v0")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v5")]); ((TAtom "iw_1.L10"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v5")]); ((TAtom "iw_1.join"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L11"), []); ((TAtom "L13"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "v4")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (216)))]); ((TAtom "iw_1.L10"), []); ((TAtom "iw_1.join"), [(2%N, (TApp "tmp" [(TAtom "v7")]), (0), (Some 8), true, false, (Some (TAtom "v5")), (Some (32)))]); ((TAtom "L11"), []); ((TAtom "L13"), [(2%N, (TApp "tmp" [(TAtom "v20")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (8))); (5%N, (TApp "tmp" [(TAtom "v20")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (8))); (7%N, (TApp "tmp" [(TAtom "v21")]), (0), (Some 1), true, false, (Some (TAtom "v21")), (Some (0)))])].


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


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L10"), []); ((TAtom "L16"), [(TAtom "v0"); (TAtom "v4")]); ((TAtom "L20"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "pr.2"); (TAtom "pr.7"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L43"), [(TAtom "chk0"); (TAtom "pr.2"); (TAtom "pr.7"); (TAtom "v0"); (TAtom "v4"); (TAtom "v41")]); ((TAtom "L44"), [(TAtom "chk0"); (TAtom "pr.2"); (TAtom "pr.7"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L49"), [(TAtom "chk0"); (TAtom "pr.2"); (TAtom "pr.7"); (TAtom "pr.9"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L50"), [(TAtom "chk0"); (TAtom "pr.2"); (TAtom "pr.7"); (TAtom "pr.9"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L65"), [(TAtom "chk0"); (TAtom "pr.2"); (TAtom "pr.7"); (TAtom "pr.9"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L76"), [(TAtom "chk0"); (TAtom "pr.7"); (TAtom "pr.9"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L77"), [(TAtom "chk0"); (TAtom "pr.10"); (TAtom "pr.6"); (TAtom "pr.7"); (TAtom "pr.9"); (TAtom "v0"); (TAtom "v4"); (TAtom "v81")]); ((TAtom "L79"), [(TAtom "chk0"); (TAtom "pr.10"); (TAtom "pr.6"); (TAtom "pr.7"); (TAtom "pr.9"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L51"), [(TAtom "chk0"); (TAtom "pr.7"); (TAtom "pr.9"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L22"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L99"), [(TAtom "chk0"); (TAtom "pr.3"); (TAtom "pr.8"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "iw_1.L10"), [(TAtom "pr.3"); (TAtom "pr.8"); (TAtom "v0"); (TAtom "v103"); (TAtom "v4")]); ((TAtom "iw_1.join"), [(TAtom "pr.3"); (TAtom "pr.8"); (TAtom "v0"); (TAtom "v103"); (TAtom "v4")]); ((TAtom "L100"), [(TAtom "pr.8"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L96"), [(TAtom "pr.1"); (TAtom "pr.8"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L19"), [(TAtom "pr.8"); (TAtom "v4")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L10"), []); ((TAtom "L16"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "pr.2"); (TAtom "pr.7"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L20"), [(TAtom "chk0"); (TAtom "pr.2"); (TAtom "pr.7"); (TAtom "v0"); (TAtom "v4"); (TAtom "v41")]); ((TAtom "L43"), [(TAtom "chk0"); (TAtom "pr.2"); (TAtom "pr.7"); (TAtom "v0"); (TAtom "v4"); (TAtom "v41")]); ((TAtom "L44"), [(TAtom "chk0"); (TAtom "pr.2"); (TAtom "pr.7"); (TAtom "pr.9"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L49"), [(TAtom "chk0"); (TAtom "pr.7"); (TAtom "pr.9"); (TAtom "v0"); (TAtom "v4"); (TAtom "v64")]); ((TAtom "L50"), [(TAtom "chk0"); (TAtom "pr.2"); (TAtom "pr.7"); (TAtom "pr.9"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L65"), [(TAtom "chk0"); (TAtom "pr.2"); (TAtom "pr.7"); (TAtom "pr.9"); (TAtom "v0"); (TAtom "v4"); (TAtom "v73")]); ((TAtom "L76"), [(TAtom "chk0"); (TAtom "pr.10"); (TAtom "pr.6"); (TAtom "pr.7"); (TAtom "pr.9"); (TAtom "v0"); (TAtom "v4"); (TAtom "v81")]); ((TAtom "L77"), [(TAtom "chk0"); (TAtom "pr.7"); (TAtom "pr.9"); (TAtom "v0"); (TAtom "v4"); (TAtom "v81"); (TAtom "v84"); (TAtom "v86")]); ((TAtom "L79"), [(TAtom "chk0"); (TAtom "pr.6"); (TAtom "pr.7"); (TAtom "pr.9"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L51"), [(TAtom "chk0"); (TAtom "pr.4"); (TAtom "v0"); (TAtom "v4"); (TAtom "v93")]); ((TAtom "L22"), [(TAtom "chk0"); (TAtom "pr.3"); (TAtom "pr.8"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L99"), [(TAtom "pr.3"); (TAtom "pr.8"); (TAtom "v0"); (TAtom "v103"); (TAtom "v4")]); ((TAtom "iw_1.L10"), [(TAtom "pr.3"); (TAtom "pr.8"); (TAtom "v0"); (TAtom "v103"); (TAtom "v4")]); ((TAtom "iw_1.join"), [(TAtom "pr.8"); (TAtom "v0"); (TAtom "v109"); (TAtom "v114"); (TAtom "v4")]); ((TAtom "L100"), [(TAtom "pr.1"); (TAtom "pr.8"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L96"), [(TAtom "pr.1"); (TAtom "v0"); (TAtom "v119"); (TAtom "v4")]); ((TAtom "L19"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), []); ((TAtom "L10"), []); ((TAtom "L16"), [(2%N, (TApp "tmp" [(TAtom "v24")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (40))); (5%N, (TApp "tmp" [(TAtom "v27")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (48)))]); ((TAtom "L20"), [(1%N, (TApp "tmp" [(TAtom "v27")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (48))); (3%N, (TApp "tmp" [(TAtom "v24")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (40)))]); ((TAtom "L43"), []); ((TAtom "L44"), []); ((TAtom "L49"), [(1%N, (TApp "tmp" [(TAtom "v24")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (40))); (4%N, (TApp "tmp" [(TAtom "v55")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (40)))]); ((TAtom "L50"), []); ((TAtom "L65"), [(1%N, (TApp "tmp" [(TAtom "v24")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (40)))]); ((TAtom "L76"), []); ((TAtom "L77"), [(3%N, (TApp "tmp" [(TAtom "pr.6")]), (0), (Some 1), true, false, (Some (TAtom "pr.6")), (Some (0))); (5%N, (TApp "tmp" [(TAtom "pr.10")]), (0), (Some 1), false, true, (Some (TAtom "pr.10")), (Some (0)))]); ((TAtom "L79"), [(2%N, (TApp "tmp" [(TAtom "v89")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (40)))]); ((TAtom "L51"), []); ((TAtom "L22"), []); ((TAtom "L99"), [(2%N, (TApp "tmp" [(TAtom "v102")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (216)))]); ((TAtom "iw_1.L10"), []); ((TAtom "iw_1.join"), [(2%N, (TApp "tmp" [(TAtom "v105")]), (0), (Some 8), true, false, (Some (TAtom "v103")), (Some (24))); (5%N, (TApp "tmp" [(TAtom "pr.3")]), (0), (Some 1), true, false, (Some (TAtom "pr.3")), (Some (0)))]); ((TAtom "L100"), []); ((TAtom "L96"), []); ((TAtom "L19"), [])].


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


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L10"), [(TAtom "v0"); (TAtom "v4")]); ((TAtom "L14"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L37"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v35"); (TAtom "v4")]); ((TAtom "L38"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L43"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "pr.8"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L44"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "pr.8"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L59"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "pr.8"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L70"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "pr.8"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L71"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "pr.7"); (TAtom "pr.8"); (TAtom "pr.9"); (TAtom "v0"); (TAtom "v4"); (TAtom "v74")]); ((TAtom "L72"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "pr.7"); (TAtom "pr.8"); (TAtom "pr.9"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L45"), [(TAtom "pr.1"); (TAtom "pr.8"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L16"), [(TAtom "v0"); (TAtom "v4")]); ((TAtom "L92"), [(TAtom "pr.2"); (TAtom "pr.4"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L93"), [(TAtom "pr.2"); (TAtom "pr.4"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L13"), [(TAtom "pr.2"); (TAtom "v4")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L10"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L14"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v35"); (TAtom "v4")]); ((TAtom "L37"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v35"); (TAtom "v4")]); ((TAtom "L38"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "pr.8"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L43"), [(TAtom "pr.1"); (TAtom "pr.8"); (TAtom "v0"); (TAtom "v4"); (TAtom "v53")]); ((TAtom "L44"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "pr.8"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L59"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "pr.8"); (TAtom "v0"); (TAtom "v4"); (TAtom "v67")]); ((TAtom "L70"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "pr.7"); (TAtom "pr.8"); (TAtom "pr.9"); (TAtom "v0"); (TAtom "v4"); (TAtom "v74")]); ((TAtom "L71"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "pr.8"); (TAtom "v0"); (TAtom "v4"); (TAtom "v74"); (TAtom "v77"); (TAtom "v79")]); ((TAtom "L72"), [(TAtom "pr.1"); (TAtom "pr.7"); (TAtom "pr.8"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L45"), [(TAtom "pr.5"); (TAtom "v0"); (TAtom "v4"); (TAtom "v86")]); ((TAtom "L16"), [(TAtom "pr.2"); (TAtom "pr.4"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L92"), [(TAtom "pr.2"); (TAtom "pr.4"); (TAtom "v0"); (TAtom "v4"); (TAtom "v97")]); ((TAtom "L93"), [(TAtom "pr.2"); (TAtom "pr.4"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L13"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), []); ((TAtom "L10"), [(2%N, (TApp "tmp" [(TAtom "v18")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (8))); (5%N, (TApp "tmp" [(TAtom "v21")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (16)))]); ((TAtom "L14"), [(1%N, (TApp "tmp" [(TAtom "v21")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (16))); (3%N, (TApp "tmp" [(TAtom "v18")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (8)))]); ((TAtom "L37"), []); ((TAtom "L38"), []); ((TAtom "L43"), [(1%N, (TApp "tmp" [(TAtom "v18")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (8))); (4%N, (TApp "tmp" [(TAtom "v50")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (8))); (7%N, (TApp "tmp" [(TAtom "v50")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (8)))]); ((TAtom "L44"), []); ((TAtom "L59"), [(1%N, (TApp "tmp" [(TAtom "v18")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (8)))]); ((TAtom "L70"), []); ((TAtom "L71"), [(3%N, (TApp "tmp" [(TAtom "pr.9")]), (0), (Some 1), true, false, (Some (TAtom "pr.9")), (Some (0))); (5%N, (TApp "tmp" [(TAtom "pr.7")]), (0), (Some 1), false, true, (Some (TAtom "pr.7")), (Some (0)))]); ((TAtom "L72"), [(2%N, (TApp "tmp" [(TAtom "v82")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (8)))]); ((TAtom "L45"), []); ((TAtom "L16"), []); ((TAtom "L92"), []); ((TAtom "L93"), []); ((TAtom "L13"), [])].


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


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "iw_1.L10"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v11"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "iw_1.join"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v11"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L6"), []); ((TAtom "L8"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L27"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L28"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L20"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L21"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L22"), [(TAtom "chk0"); (TAtom "v0")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v11"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "iw_1.L10"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v11"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "iw_1.join"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L6"), []); ((TAtom "L8"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L27"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2"); (TAtom "v30"); (TAtom "v4")]); ((TAtom "L28"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L20"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L21"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L22"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "v10")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (216)))]); ((TAtom "iw_1.L10"), []); ((TAtom "iw_1.join"), [(2%N, (TApp "tmp" [(TAtom "v13")]), (0), (Some 8), true, false, (Some (TAtom "v11")), (Some (96)))]); ((TAtom "L6"), []); ((TAtom "L8"), []); ((TAtom "L27"), []); ((TAtom "L28"), []); ((TAtom "L20"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0))); (4%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), false, true, (Some (TAtom "v0")), (Some (0)))]); ((TAtom "L21"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0))); (4%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), false, true, (Some (TAtom "v0")), (Some (0)))]); ((TAtom "L22"), [(4%N, (TApp "tmp" [(TAtom "v56")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (48))); (6%N, (TApp "tmp" [(TAtom "v54")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (40))); (8%N, (TApp "tmp" [(TAtom "v52")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (32))); (13%N, (TApp "tmp" [(TAtom "v62")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (16))); (15%N, (TApp "tmp" [(TAtom "v60")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (8))); (17%N, (TApp "tmp" [(TAtom "v58")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (24)))])].


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


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "iw_1.L10"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v8")]); ((TAtom "iw_1.join"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v8")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v8")]); ((TAtom "iw_1.L10"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v8")]); ((TAtom "iw_1.join"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "v7")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (216)))]); ((TAtom "iw_1.L10"), []); ((TAtom "iw_1.join"), [(2%N, (TApp "tmp" [(TAtom "v10")]), (0), (Some 8), true, false, (Some (TAtom "v8")), (Some (72)))])].


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


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "L4"), []); ((TAtom "L6"), [(TAtom "v0"); (TAtom "v3")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v3")]); ((TAtom "L4"), []); ((TAtom "L6"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), []); ((TAtom "L4"), []); ((TAtom "L6"), [])].


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


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "L13"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L14"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L5"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L7"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L31"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L32"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "L34"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v37")]); ((TAtom "L43"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v37")]); ((TAtom "L45"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v37")]); ((TAtom "L55"), []); ((TAtom "L56"), [])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L13"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v18")]); ((TAtom "L14"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L5"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L7"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v30")]); ((TAtom "L31"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v37")]); ((TAtom "L32"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v42")]); ((TAtom "L34"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v37")]); ((TAtom "L43"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v37")]); ((TAtom "L45"), []); ((TAtom "L55"), []); ((TAtom "L56"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "v9")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (56)))]); ((TAtom "L13"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0)))]); ((TAtom "L14"), []); ((TAtom "L5"), [(1%N, (TApp "tmp" [(TAtom "v9")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (56))); (5%N, (TApp "tmp" [(TAtom "v27")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (64))); (7%N, (TApp "tmp" [(TAtom "v22")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (56)))]); ((TAtom "L7"), [(2%N, (TApp "tmp" [(TAtom "v29")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (96)))]); ((TAtom "L31"), []); ((TAtom "L32"), [(2%N, (TApp "tmp" [(TAtom "v40")]), (0), (Some 8), false, true, (Some (TAtom "pr.1")), (Some (8))); (4%N, (TApp "tmp" [(TAtom "pr.1")]), (0), (Some 8), true, false, (Some (TAtom "pr.1")), (Some (0)))]); ((TAtom "L34"), [(2%N, (TApp "tmp" [(TAtom "v47")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (80)))]); ((TAtom "L43"), []); ((TAtom "L45"), [(3%N, (TApp "tmp" [(TAtom "v58")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136)))]); ((TAtom "L55"), []); ((TAtom "L56"), [])].


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


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L11"), [(TAtom "v0"); (TAtom "v10"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L12"), [(TAtom "pr.1"); (TAtom "v0"); (TAtom "v10"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L19"), [(TAtom "v10"); (TAtom "v23")]); ((TAtom "L13"), [(TAtom "v0"); (TAtom "v4")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v10"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L11"), [(TAtom "pr.1"); (TAtom "v0"); (TAtom "v10"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L12"), [(TAtom "v0"); (TAtom "v10"); (TAtom "v2"); (TAtom "v23"); (TAtom "v4")]); ((TAtom "L19"), []); ((TAtom "L13"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), []); ((TAtom "L11"), []); ((TAtom "L12"), [(2%N, (TApp "tmp" [(TAtom "v23")]), (0), (Some 1), true, false, (Some (TAtom "pr.1")), (Some (-1)))]); ((TAtom "L19"), []); ((TAtom "L13"), [])].


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


Definition live_in : list (name * list name) :=
  [((TAtom "start"), []); ((TAtom "L24"), [(TAtom "v17"); (TAtom "v3")]); ((TAtom "L25"), [(TAtom "v17"); (TAtom "v3")]); ((TAtom "L18"), [(TAtom "v17"); (TAtom "v3")]); ((TAtom "L19"), [(TAtom "v17"); (TAtom "v3")]); ((TAtom "L38"), [(TAtom "v17"); (TAtom "v3")]); ((TAtom "L58"), [(TAtom "v17"); (TAtom "v3"); (TAtom "v49"); (TAtom "v56")]); ((TAtom "L59"), [(TAtom "v17"); (TAtom "v3"); (TAtom "v49"); (TAtom "v56")]); ((TAtom "L63"), [(TAtom "v17"); (TAtom "v3"); (TAtom "v49")]); ((TAtom "L52"), [(TAtom "v17"); (TAtom "v3")]); ((TAtom "L39"), [(TAtom "v3")]); ((TAtom "L15"), [(TAtom "v3")]); ((TAtom "L82"), [(TAtom "v3")]); ((TAtom "L83"), [(TAtom "pr.4"); (TAtom "pr.5"); (TAtom "v3"); (TAtom "v88")]); ((TAtom "L99"), [(TAtom "chk13"); (TAtom "pr.4"); (TAtom "pr.5"); (TAtom "v3"); (TAtom "v88")]); ((TAtom "L110"), [(TAtom "chk13"); (TAtom "pr.4"); (TAtom "pr.5"); (TAtom "v103"); (TAtom "v3"); (TAtom "v88")]); ((TAtom "L111"), [(TAtom "chk13"); (TAtom "pr.4"); (TAtom "pr.5"); (TAtom "v103"); (TAtom "v3")]); ((TAtom "L104"), [(TAtom "chk13"); (TAtom "pr.4"); (TAtom "pr.5"); (TAtom "v103"); (TAtom "v3")]); ((TAtom "L105"), [(TAtom "chk13"); (TAtom "pr.4"); (TAtom "pr.5"); (TAtom "v103"); (TAtom "v3")]); ((TAtom "L130"), [(TAtom "chk13"); (TAtom "chk21"); (TAtom "pr.4"); (TAtom "pr.5"); (TAtom "v103"); (TAtom "v3")]); ((TAtom "L154"), [(TAtom "chk13"); (TAtom "chk21"); (TAtom "pr.4"); (TAtom "pr.5"); (TAtom "v103"); (TAtom "v145"); (TAtom "v152"); (TAtom "v3")]); ((TAtom "L155"), [(TAtom "chk13"); (TAtom "chk21"); (TAtom "pr.4"); (TAtom "pr.5"); (TAtom "v103"); (TAtom "v145"); (TAtom "v152"); (TAtom "v3")]); ((TAtom "L159"), [(TAtom "chk13"); (TAtom "chk21"); (TAtom "pr.4"); (TAtom "pr.5"); (TAtom "v103"); (TAtom "v145"); (TAtom "v3")]); ((TAtom "L148"), [(TAtom "chk13"); (TAtom "chk21"); (TAtom "pr.4"); (TAtom "pr.5"); (TAtom "v103"); (TAtom "v3")]); ((TAtom "L131"), [(TAtom "chk13"); (TAtom "chk21"); (TAtom "pr.4"); (TAtom "pr.5"); (TAtom "v3")]); ((TAtom "L94"), [(TAtom "chk13"); (TAtom "pr.4"); (TAtom "pr.5"); (TAtom "v3")]); ((TAtom "L180"), [(TAtom "chk13"); (TAtom "pr.4"); (TAtom "pr.5"); (TAtom "v3")]); ((TAtom "L197"), [(TAtom "chk13"); (TAtom "chk31"); (TAtom "pr.4"); (TAtom "pr.5"); (TAtom "v3")]); ((TAtom "L198"), [(TAtom "chk13"); (TAtom "chk31"); (TAtom "pr.4"); (TAtom "pr.5"); (TAtom "v3")]); ((TAtom "L213"), [(TAtom "chk13"); (TAtom "chk31"); (TAtom "pr.4"); (TAtom "pr.5"); (TAtom "v3")]); ((TAtom "L221"), [(TAtom "chk13"); (TAtom "chk31"); (TAtom "pr.4"); (TAtom "pr.5"); (TAtom "v3")]); ((TAtom "L211"), [(TAtom "chk13"); (TAtom "chk31"); (TAtom "pr.4"); (TAtom "pr.5"); (TAtom "v3")]); ((TAtom "L240"), [(TAtom "chk13"); (TAtom "chk31"); (TAtom "pr.4"); (TAtom "pr.5"); (TAtom "v3")]); ((TAtom "iw_1.L10"), [(TAtom "chk13"); (TAtom "chk31"); (TAtom "pr.4"); (TAtom "pr.5"); (TAtom "v244"); (TAtom "v3")]); ((TAtom "iw_1.join"), [(TAtom "chk13"); (TAtom "chk31"); (TAtom "pr.4"); (TAtom "pr.5"); (TAtom "v244"); (TAtom "v3")]); ((TAtom "L241"), [(TAtom "chk13"); (TAtom "chk31"); (TAtom "pr.4"); (TAtom "pr.5"); (TAtom "v3")]); ((TAtom "L191"), [(TAtom "chk13"); (TAtom "chk31"); (TAtom "pr.4"); (TAtom "pr.5"); (TAtom "v3")]); ((TAtom "L192"), [(TAtom "chk13"); (TAtom "chk31"); (TAtom "pr.5"); (TAtom "v3")]); ((TAtom "L263"), [(TAtom "chk13"); (TAtom "chk31"); (TAtom "pr.2"); (TAtom "pr.5"); (TAtom "v3")]); ((TAtom "L269"), [(TAtom "chk13"); (TAtom "chk43"); (TAtom "pr.2"); (TAtom "pr.5"); (TAtom "v3")]); ((TAtom "L270"), [(TAtom "chk13"); (TAtom "chk43"); (TAtom "pr.2"); (TAtom "pr.5"); (TAtom "v3")]); ((TAtom "L285"), [(TAtom "chk13"); (TAtom "chk43"); (TAtom "pr.2"); (TAtom "pr.5"); (TAtom "v3")]); ((TAtom "L293"), [(TAtom "chk13"); (TAtom "pr.2"); (TAtom "pr.5"); (TAtom "v3")]); ((TAtom "L264"), [(TAtom "chk13"); (TAtom "pr.2"); (TAtom "pr.5"); (TAtom "v3")]); ((TAtom "L313"), [(TAtom "chk13"); (TAtom "pr.2"); (TAtom "pr.5"); (TAtom "v3")]); ((TAtom "iw_2.L10"), [(TAtom "chk13"); (TAtom "pr.2"); (TAtom "pr.5"); (TAtom "v3"); (TAtom "v317")]); ((TAtom "iw_2.join"), [(TAtom "chk13"); (TAtom "pr.2"); (TAtom "pr.5"); (TAtom "v3"); (TAtom "v317")]); ((TAtom "L314"), [(TAtom "chk13"); (TAtom "pr.2"); (TAtom "pr.5"); (TAtom "v3")]); ((TAtom "L257"), [(TAtom "chk13"); (TAtom "pr.2"); (TAtom "pr.5"); (TAtom "v3")]); ((TAtom "L182"), [(TAtom "chk13"); (TAtom "pr.5"); (TAtom "v3")]); ((TAtom "L334"), [(TAtom "chk13"); (TAtom "pr.1"); (TAtom "pr.5"); (TAtom "v3")]); ((TAtom "L343"), [(TAtom "chk13"); (TAtom "pr.1"); (TAtom "pr.5"); (TAtom "v3")]); ((TAtom "L344"), [(TAtom "chk13"); (TAtom "pr.1"); (TAtom "pr.5"); (TAtom "v3")]); ((TAtom "L337"), [(TAtom "chk13"); (TAtom "pr.1"); (TAtom "pr.5"); (TAtom "v3")]); ((TAtom "L338"), [(TAtom "chk13"); (TAtom "pr.1"); (TAtom "pr.5"); (TAtom "v3")]); ((TAtom "L360"), [(TAtom "chk13"); (TAtom "chk62"); (TAtom "pr.1"); (TAtom "pr.5"); (TAtom "v3")]); ((TAtom "L381"), [(TAtom "chk13"); (TAtom "chk67"); (TAtom "pr.1"); (TAtom "pr.5"); (TAtom "v3"); (TAtom "v376")]); ((TAtom "L382"), [(TAtom "chk13"); (TAtom "pr.1"); (TAtom "pr.5"); (TAtom "v3"); (TAtom "v376"); (TAtom "v383")]); ((TAtom "L393"), [(TAtom "chk13"); (TAtom "pr.1"); (TAtom "pr.5"); (TAtom "v3"); (TAtom "v376")]); ((TAtom "L361"), [(TAtom "chk13"); (TAtom "chk62"); (TAtom "pr.1"); (TAtom "pr.5"); (TAtom "v3")]); ((TAtom "L329"), [(TAtom "chk13"); (TAtom "pr.1"); (TAtom "pr.5"); (TAtom "v3")]); ((TAtom "L414"), [(TAtom "pr.4"); (TAtom "v3")]); ((TAtom "L423"), [(TAtom "pr.4"); (TAtom "v3")]); ((TAtom "L424"), [(TAtom "pr.4"); (TAtom "v3")]); ((TAtom "L417"), [(TAtom "pr.4"); (TAtom "v3")]); ((TAtom "L418"), [(TAtom "pr.4"); (TAtom "v3")]); ((TAtom "L434"), [(TAtom "pr.4"); (TAtom "v3")]); ((TAtom "L449"), [(TAtom "chk80"); (TAtom "pr.4"); (TAtom "v3"); (TAtom "v444")]); ((TAtom "L450"), [(TAtom "pr.4"); (TAtom "v3"); (TAtom "v444"); (TAtom "v451")]); ((TAtom "L461"), [(TAtom "pr.4"); (TAtom "v3"); (TAtom "v444")]); ((TAtom "L435"), [(TAtom "pr.4"); (TAtom "v3")]); ((TAtom "L476"), [(TAtom "pr.4"); (TAtom "v3")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v17"); (TAtom "v3")]); ((TAtom "L24"), [(TAtom "v17"); (TAtom "v3"); (TAtom "v31")]); ((TAtom "L25"), [(TAtom "v17"); (TAtom "v3")]); ((TAtom "L18"), [(TAtom "v3")]); ((TAtom "L19"), [(TAtom "v17"); (TAtom "v3")]); ((TAtom "L38"), [(TAtom "v17"); (TAtom "v3"); (TAtom "v49"); (TAtom "v56")]); ((TAtom "L58"), [(TAtom "v17"); (TAtom "v3"); (TAtom "v49"); (TAtom "v56")]); ((TAtom "L59"), [(TAtom "v17"); (TAtom "v3"); (TAtom "v49")]); ((TAtom "L63"), [(TAtom "v17"); (TAtom "v3")]); ((TAtom "L52"), [(TAtom "v3")]); ((TAtom "L39"), [(TAtom "v3")]); ((TAtom "L15"), [(TAtom "v3"); (TAtom "v81")]); ((TAtom "L82"), [(TAtom "pr.4"); (TAtom "pr.5"); (TAtom "v3"); (TAtom "v88")]); ((TAtom "L83"), [(TAtom "chk13"); (TAtom "pr.4"); (TAtom "pr.5"); (TAtom "v3"); (TAtom "v88")]); ((TAtom "L99"), [(TAtom "chk13"); (TAtom "pr.4"); (TAtom "pr.5"); (TAtom "v103"); (TAtom "v3"); (TAtom "v88")]); ((TAtom "L110"), [(TAtom "chk13"); (TAtom "pr.4"); (TAtom "pr.5"); (TAtom "v103"); (TAtom "v119"); (TAtom "v3")]); ((TAtom "L111"), [(TAtom "chk13"); (TAtom "pr.4"); (TAtom "pr.5"); (TAtom "v103"); (TAtom "v3")]); ((TAtom "L104"), [(TAtom "chk13"); (TAtom "pr.4"); (TAtom "pr.5"); (TAtom "v3")]); ((TAtom "L105"), [(TAtom "chk13"); (TAtom "chk21"); (TAtom "pr.4"); (TAtom "pr.5"); (TAtom "v103"); (TAtom "v3")]); ((TAtom "L130"), [(TAtom "chk13"); (TAtom "chk21"); (TAtom "pr.4"); (TAtom "pr.5"); (TAtom "v103"); (TAtom "v145"); (TAtom "v152"); (TAtom "v3")]); ((TAtom "L154"), [(TAtom "chk13"); (TAtom "chk21"); (TAtom "pr.4"); (TAtom "pr.5"); (TAtom "v103"); (TAtom "v145"); (TAtom "v152"); (TAtom "v3")]); ((TAtom "L155"), [(TAtom "chk13"); (TAtom "chk21"); (TAtom "pr.4"); (TAtom "pr.5"); (TAtom "v103"); (TAtom "v145"); (TAtom "v3")]); ((TAtom "L159"), [(TAtom "chk13"); (TAtom "chk21"); (TAtom "pr.4"); (TAtom "pr.5"); (TAtom "v103"); (TAtom "v3")]); ((TAtom "L148"), [(TAtom "chk13"); (TAtom "pr.4"); (TAtom "pr.5"); (TAtom "v3")]); ((TAtom "L131"), [(TAtom "chk13"); (TAtom "pr.4"); (TAtom "pr.5"); (TAtom "v3")]); ((TAtom "L94"), [(TAtom "chk13"); (TAtom "pr.4"); (TAtom "pr.5"); (TAtom "v3")]); ((TAtom "L180"), [(TAtom "chk13"); (TAtom "chk31"); (TAtom "pr.4"); (TAtom "pr.5"); (TAtom "v3")]); ((TAtom "L197"), [(TAtom "chk13"); (TAtom "chk31"); (TAtom "pr.4"); (TAtom "pr.5"); (TAtom "v207"); (TAtom "v3")]); ((TAtom "L198"), [(TAtom "chk13"); (TAtom "chk31"); (TAtom "pr.4"); (TAtom "pr.5"); (TAtom "v3")]); ((TAtom "L213"), [(TAtom "chk13"); (TAtom "chk31"); (TAtom "pr.4"); (TAtom "pr.5"); (TAtom "v3")]); ((TAtom "L221"), [(TAtom "chk13"); (TAtom "chk31"); (TAtom "pr.4"); (TAtom "pr.5"); (TAtom "v235"); (TAtom "v3")]); ((TAtom "L211"), [(TAtom "chk13"); (TAtom "chk31"); (TAtom "pr.4"); (TAtom "pr.5"); (TAtom "v3")]); ((TAtom "L240"), [(TAtom "chk13"); (TAtom "chk31"); (TAtom "pr.4"); (TAtom "pr.5"); (TAtom "v244"); (TAtom "v3")]); ((TAtom "iw_1.L10"), [(TAtom "chk13"); (TAtom "chk31"); (TAtom "pr.4"); (TAtom "pr.5"); (TAtom "v244"); (TAtom "v3")]); ((TAtom "iw_1.join"), [(TAtom "chk13"); (TAtom "chk31"); (TAtom "pr.4"); (TAtom "pr.5"); (TAtom "v252"); (TAtom "v3")]); ((TAtom "L241"), [(TAtom "chk13"); (TAtom "chk31"); (TAtom "pr.4"); (TAtom "pr.5"); (TAtom "v3")]); ((TAtom "L191"), [(TAtom "chk13"); (TAtom "chk31"); (TAtom "pr.4"); (TAtom "pr.5"); (TAtom "v3")]); ((TAtom "L192"), [(TAtom "chk13"); (TAtom "chk31"); (TAtom "pr.2"); (TAtom "pr.5"); (TAtom "v3")]); ((TAtom "L263"), [(TAtom "chk13"); (TAtom "chk43"); (TAtom "pr.2"); (TAtom "pr.5"); (TAtom "v3")]); ((TAtom "L269"), [(TAtom "chk13"); (TAtom "chk43"); (TAtom "pr.2"); (TAtom "pr.5"); (TAtom "v279"); (TAtom "v3")]); ((TAtom "L270"), [(TAtom "chk13"); (TAtom "chk43"); (TAtom "pr.2"); (TAtom "pr.5"); (TAtom "v3")]); ((TAtom "L285"), [(TAtom "chk13"); (TAtom "pr.2"); (TAtom "pr.5"); (TAtom "v3")]); ((TAtom "L293"), [(TAtom "chk13"); (TAtom "pr.2"); (TAtom "pr.5"); (TAtom "v3"); (TAtom "v306")]); ((TAtom "L264"), [(TAtom "chk13"); (TAtom "pr.2"); (TAtom "pr.5"); (TAtom "v3")]); ((TAtom "L313"), [(TAtom "chk13"); (TAtom "pr.2"); (TAtom "pr.5"); (TAtom "v3"); (TAtom "v317")]); ((TAtom "iw_2.L10"), [(TAtom "chk13"); (TAtom "pr.2"); (TAtom "pr.5"); (TAtom "v3"); (TAtom "v317")]); ((TAtom "iw_2.join"), [(TAtom "chk13"); (TAtom "pr.2"); (TAtom "pr.5"); (TAtom "v3"); (TAtom "v323")]); ((TAtom "L314"), [(TAtom "chk13"); (TAtom "pr.2"); (TAtom "pr.5"); (TAtom "v3")]); ((TAtom "L257"), [(TAtom "chk13"); (TAtom "pr.2"); (TAtom "pr.5"); (TAtom "v3")]); ((TAtom "L182"), [(TAtom "chk13"); (TAtom "pr.1"); (TAtom "pr.5"); (TAtom "v3")]); ((TAtom "L334"), [(TAtom "chk13"); (TAtom "pr.1"); (TAtom "pr.5"); (TAtom "v3")]); ((TAtom "L343"), [(TAtom "chk13"); (TAtom "pr.1"); (TAtom "pr.5"); (TAtom "v3"); (TAtom "v350")]); ((TAtom "L344"), [(TAtom "chk13"); (TAtom "pr.1"); (TAtom "pr.5"); (TAtom "v3")]); ((TAtom "L337"), [(TAtom "chk13"); (TAtom "pr.1"); (TAtom "pr.5"); (TAtom "v3")]); ((TAtom "L338"), [(TAtom "chk13"); (TAtom "chk62"); (TAtom "pr.1"); (TAtom "pr.5"); (TAtom "v3")]); ((TAtom "L360"), [(TAtom "chk13"); (TAtom "chk67"); (TAtom "pr.1"); (TAtom "pr.5"); (TAtom "v3"); (TAtom "v376"); (TAtom "v380")]); ((TAtom "L381"), [(TAtom "chk13"); (TAtom "chk67"); (TAtom "pr.1"); (TAtom "pr.5"); (TAtom "v3"); (TAtom "v376"); (TAtom "v383"); (TAtom "v384")]); ((TAtom "L382"), [(TAtom "chk13"); (TAtom "pr.1"); (TAtom "pr.5"); (TAtom "v3"); (TAtom "v376")]); ((TAtom "L393"), [(TAtom "chk13"); (TAtom "pr.1"); (TAtom "pr.5"); (TAtom "v3")]); ((TAtom "L361"), [(TAtom "chk13"); (TAtom "pr.1"); (TAtom "pr.5"); (TAtom "v3")]); ((TAtom "L329"), [(TAtom "pr.1"); (TAtom "v3"); (TAtom "v413")]); ((TAtom "L414"), [(TAtom "pr.4"); (TAtom "v3")]); ((TAtom "L423"), [(TAtom "pr.4"); (TAtom "v3"); (TAtom "v428")]); ((TAtom "L424"), [(TAtom "pr.4"); (TAtom "v3")]); ((TAtom "L417"), [(TAtom "pr.4"); (TAtom "v3")]); ((TAtom "L418"), [(TAtom "pr.4"); (TAtom "v3")]); ((TAtom "L434"), [(TAtom "chk80"); (TAtom "pr.4"); (TAtom "v3"); (TAtom "v444"); (TAtom "v448")]); ((TAtom "L449"), [(TAtom "chk80"); (TAtom "pr.4"); (TAtom "v3"); (TAtom "v444"); (TAtom "v451"); (TAtom "v452")]); ((TAtom "L450"), [(TAtom "pr.4"); (TAtom "v3"); (TAtom "v444")]); ((TAtom "L461"), [(TAtom "pr.4"); (TAtom "v3")]); ((TAtom "L435"), [(TAtom "pr.4"); (TAtom "v3")]); ((TAtom "L476"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [(4%N, (TApp "tmp" [(TAtom "v6")]), (0), (Some 8), false, true, (Some (TAtom "v3")), (Some (8))); (6%N, (TApp "tmp" [(TAtom "v3")]), (0), (Some 8), false, true, (Some (TAtom "v3")), (Some (0))); (11%N, (TApp "tmp" [(TAtom "v21")]), (0), (Some 1), true, false, (Some (TAtom "v21")), (Some (0)))]); ((TAtom "L24"), [(3%N, (TApp "tmp" [(TAtom "v27")]), (0), (Some 8), true, false, (Some (TAtom "v26")), (Some (8)))]); ((TAtom "L25"), []); ((TAtom "L18"), [(2%N, (TApp "tmp" [(TAtom "v34")]), (0), (Some 4), false, true, (Some (TAtom "v34")), (Some (0))); (6%N, (TApp "tmp" [(TAtom "v36")]), (0), (Some 8), false, true, (Some (TAtom "v35")), (Some (8)))]); ((TAtom "L19"), [(3%N, (TApp "tmp" [(TAtom "v42")]), (0), (Some 8), true, false, (Some (TAtom "v41")), (Some (8)))]); ((TAtom "L38"), [(2%N, (TApp "tmp" [(TAtom "v49")]), (0), (Some 4), true, true, (Some (TAtom "v49")), (Some (0)))]); ((TAtom "L58"), []); ((TAtom "L59"), []); ((TAtom "L63"), []); ((TAtom "L52"), [(3%N, (TApp "tmp" [(TAtom "v74")]), (0), (Some 8), false, true, (Some (TAtom "v73")), (Some (8)))]); ((TAtom "L39"), [(3%N, (TApp "tmp" [(TAtom "v77")]), (0), (Some 4), true, false, (Some (TAtom "v76")), (Some (4))); (6%N, (TApp "tmp" [(TAtom "v77")]), (0), (Some 4), false, true, (Some (TAtom "v76")), (Some (4)))]); ((TAtom "L15"), [(2%N, (TApp "tmp" [(TAtom "v80")]), (0), (Some 8), true, false, (Some (TAtom "v80")), (Some (0)))]); ((TAtom "L82"), []); ((TAtom "L83"), [(2%N, (TApp "tmp" [(TAtom "v90")]), (0), (Some 8), false, true, (Some (TAtom "v90")), (Some (0))); (4%N, (TApp "tmp" [(TAtom "pr.5")]), (0), (Some 4), true, false, (Some (TAtom "pr.5")), (Some (0)))]); ((TAtom "L99"), [(3%N, (TApp "tmp" [(TAtom "v107")]), (0), (Some 1), true, false, (Some (TAtom "v107")), (Some (0)))]); ((TAtom "L110"), [(2%N, (TApp "tmp" [(TAtom "v113")]), (0), (Some 8), true, false, (Some (TAtom "pr.5")), (Some (136))); (5%N, (TApp "tmp" [(TAtom "v115")]), (0), (Some 8), true, false, (Some (TAtom "v114")), (Some (8)))]); ((TAtom "L111"), []); ((TAtom "L104"), [(2%N, (TApp "tmp" [(TAtom "v123")]), (0), (Some 8), true, false, (Some (TAtom "pr.5")), (Some (136))); (4%N, (TApp "tmp" [(TAtom "v124")]), (0), (Some 4), false, true, (Some (TAtom "v124")), (Some (0))); (5%N, (TApp "tmp" [(TAtom "v123")]), (0), (Some 8), true, false, (Some (TAtom "pr.5")), (Some (136))); (8%N, (TApp "tmp" [(TAtom "v128")]), (0), (Some 8), false, true, (Some (TAtom "v127")), (Some (8)))]); ((TAtom "L105"), [(2%N, (TApp "tmp" [(TAtom "v134")]), (0), (Some 8), true, false, (Some (TAtom "pr.5")), (Some (136))); (5%N, (TApp "tmp" [(TAtom "v136")]), (0), (Some 8), true, false, (Some (TAtom "v135")), (Some (8)))]); ((TAtom "L130"), [(1%N, (TApp "tmp" [(TAtom "v134")]), (0), (Some 8), true, false, (Some (TAtom "pr.5")), (Some (136))); (3%N, (TApp "tmp" [(TAtom "v145")]), (0), (Some 4), true, true, (Some (TAtom "v145")), (Some (0)))]); ((TAtom "L154"), []); ((TAtom "L155"), []); ((TAtom "L159"), []); ((TAtom "L148"), [(2%N, (TApp "tmp" [(TAtom "v170")]), (0), (Some 8), true, false, (Some (TAtom "pr.5")), (Some (136))); (5%N, (TApp "tmp" [(TAtom "v172")]), (0), (Some 8), false, true, (Some (TAtom "v171")), (Some (8)))]); ((TAtom "L131"), [(1%N, (TApp "tmp" [(TAtom "v134")]), (0), (Some 8), true, false, (Some (TAtom "pr.5")), (Some (136))); (4%N, (TApp "tmp" [(TAtom "v177")]), (0), (Some 4), true, false, (Some (TAtom "v176")), (Some (4))); (7%N, (TApp "tmp" [(TAtom "v177")]), (0), (Some 4), false, true, (Some (TAtom "v176")), (Some (4)))]); ((TAtom "L94"), [(2%N, (TApp "tmp" [(TAtom "v184")]), (0), (Some 4), true, false, (Some (TAtom "pr.5")), (Some (116)))]); ((TAtom "L180"), [(2%N, (TApp "tmp" [(TAtom "v194")]), (0), (Some 4), true, false, (Some (TAtom "pr.5")), (Some (192)))]); ((TAtom "L197"), [(2%N, (TApp "tmp" [(TAtom "v200")]), (0), (Some 8), true, false, (Some (TAtom "pr.5")), (Some (40))); (5%N, (TApp "tmp" [(TAtom "v203")]), (0), (Some 8), true, false, (Some (TAtom "pr.5")), (Some (32)))]); ((TAtom "L198"), []); ((TAtom "L213"), [(1%N, (TApp "tmp" [(TAtom "v194")]), (0), (Some 4), true, false, (Some (TAtom "pr.5")), (Some (192)))]); ((TAtom "L221"), [(2%N, (TApp "tmp" [(TAtom "v224")]), (0), (Some 8), true, false, (Some (TAtom "pr.5")), (Some (160))); (5%N, (TApp "tmp" [(TAtom "v226")]), (0), (Some 8), true, false, (Some (TAtom "v225")), (Some (32))); (6%N, (TApp "tmp" [(TAtom "v224")]), (0), (Some 8), true, false, (Some (TAtom "pr.5")), (Some (160))); (9%N, (TApp "tmp" [(TAtom "v231")]), (0), (Some 8), true, false, (Some (TAtom "v230")), (Some (24)))]); ((TAtom "L211"), []); ((TAtom "L240"), [(2%N, (TApp "tmp" [(TAtom "v243")]), (0), (Some 8), true, false, (Some (TAtom "pr.5")), (Some (216)))]); ((TAtom "iw_1.L10"), []); ((TAtom "iw_1.join"), [(2%N, (TApp "tmp" [(TAtom "v246")]), (0), (Some 8), true, false, (Some (TAtom "v244")), (Some (24)))]); ((TAtom "L241"), []); ((TAtom "L191"), []); ((TAtom "L192"), [(2%N, (TApp "tmp" [(TAtom "v260")]), (0), (Some 4), true, false, (Some (TAtom "pr.5")), (Some (112)))]); ((TAtom "L263"), [(2%N, (TApp "tmp" [(TAtom "v266")]), (0), (Some 4), true, false, (Some (TAtom "pr.5")), (Some (192)))]); ((TAtom "L269"), [(2%N, (TApp "tmp" [(TAtom "v272")]), (0), (Some 8), true, false, (Some (TAtom "pr.5")), (Some (8))); (4%N, (TApp "tmp" [(TAtom "v272")]), (8), (Some 8), true, false, (Some (TAtom "pr.5")), (Some (16)))]); ((TAtom "L270"), []); ((TAtom "L285"), [(1%N, (TApp "tmp" [(TAtom "v266")]), (0), (Some 4), true, false, (Some (TAtom "pr.5")), (Some (192)))]); ((TAtom "L293"), [(2%N, (TApp "tmp" [(TAtom "v296")]), (0), (Some 8), true, false, (Some (TAtom "pr.5")), (Some (160))); (4%N, (TApp "tmp" [(TAtom "v297")]), (0), (Some 8), true, false, (Some (TAtom "v297")), (Some (0))); (5%N, (TApp "tmp" [(TAtom "v296")]), (0), (Some 8), true, false, (Some (TAtom "pr.5")), (Some (160))); (8%N, (TApp "tmp" [(TAtom "v302")]), (0), (Some 8), true, false, (Some (TAtom "v301")), (Some (8)))]); ((TAtom "L264"), []); ((TAtom "L313"), [(2%N, (TApp "tmp" [(TAtom "v316")]), (0), (Some 8), true, false, (Some (TAtom "pr.5")), (Some (216)))]); ((TAtom "iw_2.L10"), []); ((TAtom "iw_2.join"), [(2%N, (TApp "tmp" [(TAtom "v319")]), (0), (Some 8), true, false, (Some (TAtom "v317")), (Some (96)))]); ((TAtom "L314"), []); ((TAtom "L257"), []); ((TAtom "L182"), [(1%N, (TApp "tmp" [(TAtom "pr.5")]), (0), (Some 4), true, false, (Some (TAtom "pr.5")), (Some (0)))]); ((TAtom "L334"), [(2%N, (TApp "tmp" [(TAtom "v340")]), (0), (Some 1), true, false, (Some (TAtom "v340")), (Some (0)))]); ((TAtom "L343"), [(2%N, (TApp "tmp" [(TAtom "v346")]), (0), (Some 8), true, false, (Some (TAtom "pr.5")), (Some (136))); (5%N, (TApp "tmp" [(TAtom "v348")]), (0), (Some 4), true, false, (Some (TAtom "v347")), (Some (4)))]); ((TAtom "L344"), []); ((TAtom "L337"), [(2%N, (TApp "tmp" [(TAtom "v354")]), (0), (Some 8), true, false, (Some (TAtom "pr.5")), (Some (136))); (5%N, (TApp "tmp" [(TAtom "v356")]), (0), (Some 8), false, true, (Some (TAtom "v355")), (Some (8))); (7%N, (TApp "tmp" [(TAtom "v354")]), (0), (Some 8), true, false, (Some (TAtom "pr.5")), (Some (136))); (9%N, (TApp "tmp" [(TAtom "v359")]), (0), (Some 4), false, true, (Some (TAtom "v359")), (Some (0)))]); ((TAtom "L338"), [(2%N, (TApp "tmp" [(TAtom "v364")]), (0), (Some 8), true, false, (Some (TAtom "pr.5")), (Some (136))); (5%N, (TApp "tmp" [(TAtom "v366")]), (0), (Some 4), true, false, (Some (TAtom "v365")), (Some (4)))]); ((TAtom "L360"), [(1%N, (TApp "tmp" [(TAtom "v364")]), (0), (Some 8), true, false, (Some (TAtom "pr.5")), (Some (136))); (4%N, (TApp "tmp" [(TAtom "v372")]), (0), (Some 8), false, true, (Some (TAtom "v371")), (Some (8))); (6%N, (TApp "tmp" [(TAtom "v370")]), (0), (Some 8), true, false, (Some (TAtom "pr.5")), (Some (136))); (8%N, (TApp "tmp" [(TAtom "v376")]), (0), (Some 4), true, false, (Some (TAtom "v376")), (Some (0)))]); ((TAtom "L381"), [(1%N, (TApp "tmp" [(TAtom "v376")]), (0), (Some 4), true, true, (Some (TAtom "v376")), (Some (0)))]); ((TAtom "L382"), []); ((TAtom "L393"), []); ((TAtom "L361"), [(1%N, (TApp "tmp" [(TAtom "v364")]), (0), (Some 8), true, false, (Some (TAtom "pr.5")), (Some (136))); (4%N, (TApp "tmp" [(TAtom "v407")]), (0), (Some 4), true, false, (Some (TAtom "v406")), (Some (4))); (7%N, (TApp "tmp" [(TAtom "v407")]), (0), (Some 4), false, true, (Some (TAtom "v406")), (Some (4)))]); ((TAtom "L329"), [(2%N, (TApp "tmp" [(TAtom "v410")]), (0), (Some 8), false, true, (Some (TAtom "v410")), (Some (0))); (5%N, (TApp "tmp" [(TAtom "v412")]), (0), (Some 8), true, false, (Some (TAtom "pr.5")), (Some (104)))]); ((TAtom "L414"), [(2%N, (TApp "tmp" [(TAtom "v420")]), (0), (Some 1), true, false, (Some (TAtom "v420")), (Some (0)))]); ((TAtom "L423"), [(3%N, (TApp "tmp" [(TAtom "v426")]), (0), (Some 4), true, false, (Some (TAtom "v425")), (Some (4)))]); ((TAtom "L424"), []); ((TAtom "L417"), [(3%N, (TApp "tmp" [(TAtom "v432")]), (0), (Some 8), false, true, (Some (TAtom "v431")), (Some (8))); (6%N, (TApp "tmp" [(TAtom "v433")]), (0), (Some 4), false, true, (Some (TAtom "v433")), (Some (0)))]); ((TAtom "L418"), [(3%N, (TApp "tmp" [(TAtom "v438")]), (0), (Some 4), true, false, (Some (TAtom "v437")), (Some (4)))]); ((TAtom "L434"), [(3%N, (TApp "tmp" [(TAtom "v442")]), (0), (Some 8), false, true, (Some (TAtom "v441")), (Some (8))); (6%N, (TApp "tmp" [(TAtom "v444")]), (0), (Some 4), true, false, (Some (TAtom "v444")), (Some (0)))]); ((TAtom "L449"), [(1%N, (TApp "tmp" [(TAtom "v444")]), (0), (Some 4), true, true, (Some (TAtom "v444")), (Some (0)))]); ((TAtom "L450"), []); ((TAtom "L461"), []); ((TAtom "L435"), [(3%N, (TApp "tmp" [(TAtom "v473")]), (0), (Some 4), true, false, (Some (TAtom "v472")), (Some (4))); (6%N, (TApp "tmp" [(TAtom "v473")]), (0), (Some 4), false, true, (Some (TAtom "v472")), (Some (4)))]); ((TAtom "L476"), [])].


End fn___GI__IO_flush_all.

End HiAtexitSrc05.
