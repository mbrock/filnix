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


From Glibc Require Import GettextLinkSrcFiles.
Import GettextLinkSrcFiles.
Module GettextLinkSrc01.

Module fn___GI___dcgettext.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_5, 44%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_5, 47%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "domainname"); ((TAtom "v2"), "msgid"); ((TAtom "v4"), "category"); ((TAtom "v6"), "domainname"); ((TAtom "v7"), "msgid"); ((TAtom "v8"), "category")].

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  [((TAtom "v0"), ((TAtom "v0"), "domainname", 0)); ((TAtom "v2"), ((TAtom "v2"), "msgid", 0)); ((TAtom "v4"), ((TAtom "v4"), "category", 0))].

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


End fn___GI___dcgettext.

Module fn_glibc_dcigettext_transcmp.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_6, 258%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_6, 268%N)); ((TAtom "L9"), (file_6, 268%N)); ((TAtom "L10"), (file_6, 268%N)); ((TAtom "L11"), (file_6, 268%N)); ((TAtom "L24"), (file_6, 268%N)); ((TAtom "L25"), (file_6, 268%N)); ((TAtom "L26"), (file_6, 268%N)); ((TAtom "L40"), (file_6, 272%N)); ((TAtom "L50"), (file_6, 276%N)); ((TAtom "L62"), (file_6, 283%N)); ((TAtom "L42"), (file_6, 263%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "pr.1"), "result"); ((TAtom "pr.2"), "result"); ((TAtom "pr.3"), "result"); ((TAtom "v0"), "p1"); ((TAtom "v12"), "s1"); ((TAtom "v18"), "s1"); ((TAtom "v2"), "p2"); ((TAtom "v20"), "s1"); ((TAtom "v27"), "s2"); ((TAtom "v33"), "s2"); ((TAtom "v35"), "s2"); ((TAtom "v39"), "result"); ((TAtom "v43"), "result"); ((TAtom "v45"), "s1"); ((TAtom "v47"), "s2"); ((TAtom "v49"), "result"); ((TAtom "v53"), "result"); ((TAtom "v55"), "s1"); ((TAtom "v58"), "s2"); ((TAtom "v61"), "result"); ((TAtom "v65"), "result"); ((TAtom "v67"), "s1"); ((TAtom "v7"), "p1"); ((TAtom "v70"), "s2"); ((TAtom "v73"), "result"); ((TAtom "v74"), "result"); ((TAtom "v8"), "p2")].

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  [((TAtom "chk0"), ((TAtom "v0"), "p1", 32)); ((TAtom "chk1"), ((TAtom "v0"), "p1", 56)); ((TAtom "chk2"), ((TAtom "v2"), "p2", 32)); ((TAtom "chk3"), ((TAtom "v2"), "p2", 56)); ((TAtom "chk4"), ((TAtom "v0"), "p1", 0)); ((TAtom "chk5"), ((TAtom "v2"), "p2", 0)); ((TAtom "chk6"), ((TAtom "v0"), "p1", 16)); ((TAtom "chk7"), ((TAtom "v2"), "p2", 16)); ((TAtom "chk8"), ((TAtom "v0"), "p1", 8)); ((TAtom "chk9"), ((TAtom "v2"), "p2", 8)); ((TAtom "pr.1"), ((TAtom "pr.1"), "result", 0)); ((TAtom "v0"), ((TAtom "v0"), "p1", 0)); ((TAtom "v13"), ((TAtom "v0"), "p1", 32)); ((TAtom "v19"), ((TAtom "v0"), "p1", 56)); ((TAtom "v2"), ((TAtom "v2"), "p2", 0)); ((TAtom "v21"), ((TAtom "v0"), "p1", 56)); ((TAtom "v28"), ((TAtom "v2"), "p2", 32)); ((TAtom "v34"), ((TAtom "v2"), "p2", 56)); ((TAtom "v36"), ((TAtom "v2"), "p2", 56)); ((TAtom "v39"), ((TAtom "v39"), "result", 0)); ((TAtom "v49"), ((TAtom "v49"), "result", 0)); ((TAtom "v56"), ((TAtom "v0"), "p1", 16)); ((TAtom "v59"), ((TAtom "v2"), "p2", 16)); ((TAtom "v61"), ((TAtom "v61"), "result", 0)); ((TAtom "v68"), ((TAtom "v0"), "p1", 8)); ((TAtom "v71"), ((TAtom "v2"), "p2", 8)); ((TAtom "v73"), ((TAtom "v73"), "result", 0))].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2")]); ((TAtom "L9"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v16"); (TAtom "v2")]); ((TAtom "L10"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v16"); (TAtom "v2")]); ((TAtom "L11"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v16"); (TAtom "v2")]); ((TAtom "L24"), [(TAtom "chk0"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v2"); (TAtom "v23")]); ((TAtom "L25"), [(TAtom "chk0"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v2"); (TAtom "v23")]); ((TAtom "L26"), [(TAtom "chk0"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v2"); (TAtom "v23")]); ((TAtom "L40"), [(TAtom "chk0"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L50"), [(TAtom "chk0"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L62"), [(TAtom "chk0"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L42"), [])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v16"); (TAtom "v2")]); ((TAtom "L9"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v16"); (TAtom "v19"); (TAtom "v2")]); ((TAtom "L10"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v16"); (TAtom "v2"); (TAtom "v22")]); ((TAtom "L11"), [(TAtom "chk0"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v2"); (TAtom "v23")]); ((TAtom "L24"), [(TAtom "chk0"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v2"); (TAtom "v23"); (TAtom "v34")]); ((TAtom "L25"), [(TAtom "chk0"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v2"); (TAtom "v23"); (TAtom "v37")]); ((TAtom "L26"), [(TAtom "chk0"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v2"); (TAtom "v39")]); ((TAtom "L40"), [(TAtom "chk0"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v2"); (TAtom "v49")]); ((TAtom "L50"), [(TAtom "chk0"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v2"); (TAtom "v61")]); ((TAtom "L62"), [(TAtom "v73")]); ((TAtom "L42"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "v13")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (32)), "s1->domain")]); ((TAtom "L9"), []); ((TAtom "L10"), [(2%N, (TApp "tmp" [(TAtom "v21")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (56)), "opaque")]); ((TAtom "L11"), [(2%N, (TApp "tmp" [(TAtom "v28")]), (0), (Some 8), true, false, (Some (TAtom "v2")), (Some (32)), "s2->domain")]); ((TAtom "L24"), []); ((TAtom "L25"), [(2%N, (TApp "tmp" [(TAtom "v36")]), (0), (Some 8), true, false, (Some (TAtom "v2")), (Some (56)), "opaque")]); ((TAtom "L26"), []); ((TAtom "L40"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (0)), "s1->domainname"); (3%N, (TApp "tmp" [(TAtom "v2")]), (0), (Some 8), true, false, (Some (TAtom "v2")), (Some (0)), "s2->domainname")]); ((TAtom "L50"), [(2%N, (TApp "tmp" [(TAtom "v56")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (16)), "s1->localename"); (5%N, (TApp "tmp" [(TAtom "v59")]), (0), (Some 8), true, false, (Some (TAtom "v2")), (Some (16)), "s2->localename")]); ((TAtom "L62"), [(2%N, (TApp "tmp" [(TAtom "v68")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (8)), "s1->category"); (5%N, (TApp "tmp" [(TAtom "v71")]), (0), (Some 4), true, false, (Some (TAtom "v2")), (Some (8)), "s2->category")]); ((TAtom "L42"), [])].


End fn_glibc_dcigettext_transcmp.

Module fn_glibc_dcigettext_plural_eval_recurse.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_3, 52%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_3, 56%N)); ((TAtom "L6"), (file_3, 58%N)); ((TAtom "L8"), (file_3, 59%N)); ((TAtom "L23"), (file_3, 64%N)); ((TAtom "L29"), (file_3, 67%N)); ((TAtom "L37"), (file_3, 69%N)); ((TAtom "L50"), (file_3, 64%N)); ((TAtom "L53"), (file_3, 78%N)); ((TAtom "L69"), (file_3, 81%N)); ((TAtom "L71"), (file_3, 82%N)); ((TAtom "L89"), (file_3, 86%N)); ((TAtom "L105"), (file_3, 89%N)); ((TAtom "L107"), (file_3, 90%N)); ((TAtom "L114"), (file_3, 92%N)); ((TAtom "L121"), (file_3, 93%N)); ((TAtom "L123"), (file_3, 94%N)); ((TAtom "L149"), (file_3, 97%N)); ((TAtom "L151"), (file_3, 98%N)); ((TAtom "L162"), (file_3, 98%N)); ((TAtom "L163"), (file_3, 98%N)); ((TAtom "L115"), (file_3, 100%N)); ((TAtom "L173"), (file_3, 102%N)); ((TAtom "L180"), (file_3, 103%N)); ((TAtom "L182"), (file_3, 104%N)); ((TAtom "L209"), (file_3, 107%N)); ((TAtom "L211"), (file_3, 108%N)); ((TAtom "L222"), (file_3, 108%N)); ((TAtom "L223"), (file_3, 108%N)); ((TAtom "L174"), (file_3, 112%N)); ((TAtom "L248"), (file_3, 115%N)); ((TAtom "L250"), (file_3, 117%N)); ((TAtom "L262"), (file_3, 120%N)); ((TAtom "L274"), (file_3, 122%N)); ((TAtom "L275"), (file_3, 123%N)); ((TAtom "L277"), (file_3, 124%N)); ((TAtom "L298"), (file_3, 126%N)); ((TAtom "L299"), (file_3, 127%N)); ((TAtom "L301"), (file_3, 128%N)); ((TAtom "L322"), (file_3, 130%N)); ((TAtom "L334"), (file_3, 132%N)); ((TAtom "L346"), (file_3, 134%N)); ((TAtom "L359"), (file_3, 136%N)); ((TAtom "L372"), (file_3, 138%N)); ((TAtom "L385"), (file_3, 140%N)); ((TAtom "L398"), (file_3, 142%N)); ((TAtom "L411"), (file_3, 144%N)); ((TAtom "L427"), (file_3, 117%N)); ((TAtom "L430"), (file_3, 117%N)); ((TAtom "L433"), (file_3, 117%N)); ((TAtom "L431"), (file_3, 117%N)); ((TAtom "L437"), (file_3, 117%N)); ((TAtom "L439"), (file_3, 117%N)); ((TAtom "L428"), (file_3, 117%N)); ((TAtom "L443"), (file_3, 117%N)); ((TAtom "L446"), (file_3, 117%N)); ((TAtom "L448"), (file_3, 117%N)); ((TAtom "L444"), (file_3, 117%N)); ((TAtom "L452"), (file_3, 117%N)); ((TAtom "L454"), (file_3, 117%N)); ((TAtom "L457"), (file_3, 155%N)); ((TAtom "L473"), (file_3, 158%N)); ((TAtom "L475"), (file_3, 159%N)); ((TAtom "L485"), (file_3, 159%N)); ((TAtom "L486"), (file_3, 159%N)); ((TAtom "L506"), (file_3, 61%N)); ((TAtom "L508"), (file_3, 61%N)); ((TAtom "L510"), (file_3, 61%N)); ((TAtom "L22"), (file_3, 164%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "pexp"); ((TAtom "v117"), "pexp"); ((TAtom "v135"), "pexp"); ((TAtom "v139"), "n"); ((TAtom "v140"), "allowed_depth"); ((TAtom "v17"), "allowed_depth"); ((TAtom "v176"), "pexp"); ((TAtom "v18"), "allowed_depth"); ((TAtom "v19"), "pexp"); ((TAtom "v195"), "pexp"); ((TAtom "v199"), "n"); ((TAtom "v2"), "n"); ((TAtom "v200"), "allowed_depth"); ((TAtom "v234"), "pexp"); ((TAtom "v238"), "n"); ((TAtom "v239"), "allowed_depth"); ((TAtom "v24"), "pexp"); ((TAtom "v257"), "pexp"); ((TAtom "v33"), "n"); ((TAtom "v4"), "allowed_depth"); ((TAtom "v41"), "pexp"); ((TAtom "v459"), "pexp"); ((TAtom "v463"), "n"); ((TAtom "v464"), "allowed_depth"); ((TAtom "v482"), "pexp"); ((TAtom "v495"), "n"); ((TAtom "v496"), "allowed_depth"); ((TAtom "v55"), "pexp"); ((TAtom "v59"), "n"); ((TAtom "v60"), "allowed_depth"); ((TAtom "v9"), "allowed_depth"); ((TAtom "v91"), "pexp"); ((TAtom "v95"), "n"); ((TAtom "v96"), "allowed_depth")].

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  [((TAtom "chk0"), ((TAtom "v0"), "pexp", 0)); ((TAtom "chk1"), ((TAtom "v0"), "pexp", 4)); ((TAtom "chk10"), ((TAtom "v0"), "pexp", 4)); ((TAtom "chk11"), ((TAtom "v0"), "pexp", 8)); ((TAtom "chk12"), ((TAtom "v493"), "v493", 0)); ((TAtom "chk2"), ((TAtom "v0"), "pexp", 8)); ((TAtom "chk3"), ((TAtom "v0"), "pexp", 8)); ((TAtom "chk4"), ((TAtom "v0"), "pexp", 8)); ((TAtom "chk5"), ((TAtom "v0"), "pexp", 4)); ((TAtom "chk6"), ((TAtom "v0"), "pexp", 16)); ((TAtom "chk8"), ((TAtom "v0"), "pexp", 16)); ((TAtom "chk9"), ((TAtom "v0"), "pexp", 16)); ((TAtom "v0"), ((TAtom "v0"), "pexp", 0)); ((TAtom "v118"), ((TAtom "v0"), "pexp", 4)); ((TAtom "v136"), ((TAtom "v0"), "pexp", 8)); ((TAtom "v137"), ((TAtom "v0"), "pexp", 16)); ((TAtom "v177"), ((TAtom "v0"), "pexp", 4)); ((TAtom "v18"), ((TAtom "v18"), "allowed_depth", 0)); ((TAtom "v196"), ((TAtom "v0"), "pexp", 8)); ((TAtom "v197"), ((TAtom "v0"), "pexp", 16)); ((TAtom "v2"), ((TAtom "v2"), "n", 0)); ((TAtom "v235"), ((TAtom "v0"), "pexp", 8)); ((TAtom "v236"), ((TAtom "v0"), "pexp", 16)); ((TAtom "v25"), ((TAtom "v0"), "pexp", 4)); ((TAtom "v258"), ((TAtom "v0"), "pexp", 4)); ((TAtom "v4"), ((TAtom "v4"), "allowed_depth", 0)); ((TAtom "v42"), ((TAtom "v0"), "pexp", 8)); ((TAtom "v460"), ((TAtom "v0"), "pexp", 8)); ((TAtom "v483"), ((TAtom "v0"), "pexp", 8)); ((TAtom "v56"), ((TAtom "v0"), "pexp", 8)); ((TAtom "v92"), ((TAtom "v0"), "pexp", 8))].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L6"), []); ((TAtom "L8"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L23"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L29"), [(TAtom "v2")]); ((TAtom "L37"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L50"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v26")]); ((TAtom "L53"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v18"); (TAtom "v2")]); ((TAtom "L69"), [(TAtom "sw.18"); (TAtom "v62"); (TAtom "v63")]); ((TAtom "L71"), [(TAtom "v63")]); ((TAtom "L89"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v18"); (TAtom "v2")]); ((TAtom "L105"), [(TAtom "sw.30"); (TAtom "v98"); (TAtom "v99")]); ((TAtom "L107"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v18"); (TAtom "v2"); (TAtom "v99")]); ((TAtom "L114"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v18"); (TAtom "v2"); (TAtom "v99")]); ((TAtom "L121"), []); ((TAtom "L123"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v18"); (TAtom "v2")]); ((TAtom "L149"), [(TAtom "sw.42"); (TAtom "v142"); (TAtom "v143")]); ((TAtom "L151"), [(TAtom "v143")]); ((TAtom "L162"), []); ((TAtom "L163"), []); ((TAtom "L115"), [(TAtom "chk0"); (TAtom "chk5"); (TAtom "v0"); (TAtom "v18"); (TAtom "v2"); (TAtom "v99")]); ((TAtom "L173"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v18"); (TAtom "v2"); (TAtom "v99")]); ((TAtom "L180"), []); ((TAtom "L182"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v18"); (TAtom "v2")]); ((TAtom "L209"), [(TAtom "sw.60"); (TAtom "v202"); (TAtom "v203")]); ((TAtom "L211"), [(TAtom "v203")]); ((TAtom "L222"), []); ((TAtom "L223"), []); ((TAtom "L174"), [(TAtom "chk0"); (TAtom "chk5"); (TAtom "v0"); (TAtom "v18"); (TAtom "v2"); (TAtom "v99")]); ((TAtom "L248"), [(TAtom "sw.72"); (TAtom "v241"); (TAtom "v242")]); ((TAtom "L250"), [(TAtom "chk5"); (TAtom "v0"); (TAtom "v242"); (TAtom "v99")]); ((TAtom "L262"), [(TAtom "v242"); (TAtom "v99")]); ((TAtom "L274"), [(TAtom "v242"); (TAtom "v99")]); ((TAtom "L275"), []); ((TAtom "L277"), [(TAtom "v242"); (TAtom "v99")]); ((TAtom "L298"), [(TAtom "v242"); (TAtom "v99")]); ((TAtom "L299"), []); ((TAtom "L301"), [(TAtom "v242"); (TAtom "v99")]); ((TAtom "L322"), [(TAtom "v242"); (TAtom "v99")]); ((TAtom "L334"), [(TAtom "v242"); (TAtom "v99")]); ((TAtom "L346"), [(TAtom "v242"); (TAtom "v99")]); ((TAtom "L359"), [(TAtom "v242"); (TAtom "v99")]); ((TAtom "L372"), [(TAtom "v242"); (TAtom "v99")]); ((TAtom "L385"), [(TAtom "v242"); (TAtom "v99")]); ((TAtom "L398"), [(TAtom "v242"); (TAtom "v99")]); ((TAtom "L411"), [(TAtom "v242"); (TAtom "v99")]); ((TAtom "L427"), [(TAtom "v242"); (TAtom "v259"); (TAtom "v99")]); ((TAtom "L430"), [(TAtom "v242"); (TAtom "v259"); (TAtom "v99")]); ((TAtom "L433"), [(TAtom "v242"); (TAtom "v259"); (TAtom "v99")]); ((TAtom "L431"), [(TAtom "v242"); (TAtom "v259"); (TAtom "v99")]); ((TAtom "L437"), [(TAtom "v242"); (TAtom "v259"); (TAtom "v99")]); ((TAtom "L439"), [(TAtom "v242"); (TAtom "v259"); (TAtom "v99")]); ((TAtom "L428"), [(TAtom "v242"); (TAtom "v259"); (TAtom "v99")]); ((TAtom "L443"), [(TAtom "v242"); (TAtom "v259"); (TAtom "v99")]); ((TAtom "L446"), [(TAtom "v242"); (TAtom "v259"); (TAtom "v99")]); ((TAtom "L448"), [(TAtom "v242"); (TAtom "v259"); (TAtom "v99")]); ((TAtom "L444"), [(TAtom "v242"); (TAtom "v259"); (TAtom "v99")]); ((TAtom "L452"), [(TAtom "v242"); (TAtom "v259"); (TAtom "v99")]); ((TAtom "L454"), [(TAtom "v242"); (TAtom "v259"); (TAtom "v99")]); ((TAtom "L457"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v18"); (TAtom "v2")]); ((TAtom "L473"), [(TAtom "sw.156"); (TAtom "v466"); (TAtom "v467")]); ((TAtom "L475"), [(TAtom "v0"); (TAtom "v18"); (TAtom "v2"); (TAtom "v467")]); ((TAtom "L485"), [(TAtom "v18"); (TAtom "v2"); (TAtom "v483")]); ((TAtom "L486"), [(TAtom "v18"); (TAtom "v2"); (TAtom "v483")]); ((TAtom "L506"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v18"); (TAtom "v2"); (TAtom "v20")]); ((TAtom "L508"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v18"); (TAtom "v2"); (TAtom "v20")]); ((TAtom "L510"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v18"); (TAtom "v2"); (TAtom "v20")]); ((TAtom "L22"), [])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L6"), []); ((TAtom "L8"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v18"); (TAtom "v2"); (TAtom "v20")]); ((TAtom "L23"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2"); (TAtom "v26")]); ((TAtom "L29"), []); ((TAtom "L37"), []); ((TAtom "L50"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L53"), [(TAtom "sw.18"); (TAtom "v62"); (TAtom "v63")]); ((TAtom "L69"), []); ((TAtom "L71"), []); ((TAtom "L89"), [(TAtom "chk0"); (TAtom "sw.30"); (TAtom "v0"); (TAtom "v18"); (TAtom "v2"); (TAtom "v98"); (TAtom "v99")]); ((TAtom "L105"), []); ((TAtom "L107"), [(TAtom "chk0"); (TAtom "chk5"); (TAtom "v0"); (TAtom "v18"); (TAtom "v2"); (TAtom "v99")]); ((TAtom "L114"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v18"); (TAtom "v2")]); ((TAtom "L121"), []); ((TAtom "L123"), [(TAtom "sw.42"); (TAtom "v142"); (TAtom "v143")]); ((TAtom "L149"), []); ((TAtom "L151"), []); ((TAtom "L162"), []); ((TAtom "L163"), []); ((TAtom "L115"), [(TAtom "chk0"); (TAtom "chk5"); (TAtom "v0"); (TAtom "v18"); (TAtom "v2"); (TAtom "v99")]); ((TAtom "L173"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v18"); (TAtom "v2")]); ((TAtom "L180"), []); ((TAtom "L182"), [(TAtom "sw.60"); (TAtom "v202"); (TAtom "v203")]); ((TAtom "L209"), []); ((TAtom "L211"), []); ((TAtom "L222"), []); ((TAtom "L223"), []); ((TAtom "L174"), [(TAtom "chk5"); (TAtom "sw.72"); (TAtom "v0"); (TAtom "v241"); (TAtom "v242"); (TAtom "v99")]); ((TAtom "L248"), []); ((TAtom "L250"), [(TAtom "v242"); (TAtom "v259"); (TAtom "v99")]); ((TAtom "L262"), []); ((TAtom "L274"), [(TAtom "v242"); (TAtom "v99")]); ((TAtom "L275"), []); ((TAtom "L277"), []); ((TAtom "L298"), [(TAtom "v242"); (TAtom "v99")]); ((TAtom "L299"), []); ((TAtom "L301"), []); ((TAtom "L322"), []); ((TAtom "L334"), []); ((TAtom "L346"), []); ((TAtom "L359"), []); ((TAtom "L372"), []); ((TAtom "L385"), []); ((TAtom "L398"), []); ((TAtom "L411"), []); ((TAtom "L427"), [(TAtom "v242"); (TAtom "v259"); (TAtom "v99")]); ((TAtom "L430"), [(TAtom "v242"); (TAtom "v259"); (TAtom "v99")]); ((TAtom "L433"), [(TAtom "v242"); (TAtom "v99")]); ((TAtom "L431"), [(TAtom "v242"); (TAtom "v259"); (TAtom "v99")]); ((TAtom "L437"), [(TAtom "v242"); (TAtom "v259"); (TAtom "v99")]); ((TAtom "L439"), [(TAtom "v242"); (TAtom "v99")]); ((TAtom "L428"), [(TAtom "v242"); (TAtom "v259"); (TAtom "v99")]); ((TAtom "L443"), [(TAtom "v242"); (TAtom "v259"); (TAtom "v99")]); ((TAtom "L446"), [(TAtom "v242"); (TAtom "v259"); (TAtom "v99")]); ((TAtom "L448"), [(TAtom "v242"); (TAtom "v99")]); ((TAtom "L444"), [(TAtom "v242"); (TAtom "v259"); (TAtom "v99")]); ((TAtom "L452"), [(TAtom "v242"); (TAtom "v259"); (TAtom "v99")]); ((TAtom "L454"), [(TAtom "v242"); (TAtom "v99")]); ((TAtom "L457"), [(TAtom "sw.156"); (TAtom "v0"); (TAtom "v18"); (TAtom "v2"); (TAtom "v466"); (TAtom "v467")]); ((TAtom "L473"), []); ((TAtom "L475"), [(TAtom "v18"); (TAtom "v2"); (TAtom "v483")]); ((TAtom "L485"), [(TAtom "v18"); (TAtom "v2"); (TAtom "v483")]); ((TAtom "L486"), []); ((TAtom "L506"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v18"); (TAtom "v2"); (TAtom "v20")]); ((TAtom "L508"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v18"); (TAtom "v2"); (TAtom "v20")]); ((TAtom "L510"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v18"); (TAtom "v2")]); ((TAtom "L22"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), []); ((TAtom "L6"), []); ((TAtom "L8"), [(2%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0)), "pexp->nargs")]); ((TAtom "L23"), [(2%N, (TApp "tmp" [(TAtom "v25")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (4)), "pexp->operation")]); ((TAtom "L29"), []); ((TAtom "L37"), [(2%N, (TApp "tmp" [(TAtom "v42")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (8)), "pexp->val.num")]); ((TAtom "L50"), []); ((TAtom "L53"), [(2%N, (TApp "tmp" [(TAtom "v56")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (8)), "pexp->val")]); ((TAtom "L69"), []); ((TAtom "L71"), []); ((TAtom "L89"), [(2%N, (TApp "tmp" [(TAtom "v92")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (8)), "pexp->val")]); ((TAtom "L105"), []); ((TAtom "L107"), [(2%N, (TApp "tmp" [(TAtom "v118")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (4)), "pexp->operation")]); ((TAtom "L114"), []); ((TAtom "L121"), []); ((TAtom "L123"), [(3%N, (TApp "tmp" [(TAtom "v137")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (16)), "opaque")]); ((TAtom "L149"), []); ((TAtom "L151"), []); ((TAtom "L162"), []); ((TAtom "L163"), []); ((TAtom "L115"), [(1%N, (TApp "tmp" [(TAtom "v118")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (4)), "pexp->operation")]); ((TAtom "L173"), []); ((TAtom "L180"), []); ((TAtom "L182"), [(3%N, (TApp "tmp" [(TAtom "v197")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (16)), "opaque")]); ((TAtom "L209"), []); ((TAtom "L211"), []); ((TAtom "L222"), []); ((TAtom "L223"), []); ((TAtom "L174"), [(3%N, (TApp "tmp" [(TAtom "v236")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (16)), "opaque")]); ((TAtom "L248"), []); ((TAtom "L250"), [(2%N, (TApp "tmp" [(TAtom "v258")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (4)), "pexp->operation")]); ((TAtom "L262"), []); ((TAtom "L274"), []); ((TAtom "L275"), []); ((TAtom "L277"), []); ((TAtom "L298"), []); ((TAtom "L299"), []); ((TAtom "L301"), []); ((TAtom "L322"), []); ((TAtom "L334"), []); ((TAtom "L346"), []); ((TAtom "L359"), []); ((TAtom "L372"), []); ((TAtom "L385"), []); ((TAtom "L398"), []); ((TAtom "L411"), []); ((TAtom "L427"), []); ((TAtom "L430"), []); ((TAtom "L433"), []); ((TAtom "L431"), []); ((TAtom "L437"), []); ((TAtom "L439"), []); ((TAtom "L428"), []); ((TAtom "L443"), []); ((TAtom "L446"), []); ((TAtom "L448"), []); ((TAtom "L444"), []); ((TAtom "L452"), []); ((TAtom "L454"), []); ((TAtom "L457"), [(2%N, (TApp "tmp" [(TAtom "v460")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (8)), "pexp->val")]); ((TAtom "L473"), []); ((TAtom "L475"), []); ((TAtom "L485"), []); ((TAtom "L486"), [(4%N, (TApp "tmp" [(TAtom "v493")]), (0), (Some 8), true, false, (Some (TAtom "v0")), None, "opaque")]); ((TAtom "L506"), []); ((TAtom "L508"), []); ((TAtom "L510"), []); ((TAtom "L22"), [])].


End fn_glibc_dcigettext_plural_eval_recurse.

End GettextLinkSrc01.
