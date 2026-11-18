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


From Glibc Require Import PostloadCtypeCode.
Module PostloadCtypeSrc.

Definition file_0 : string := "lc-ctype.c".

Module fn__nl_postload_ctype.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_0, 61%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_0, 67%N)); ((TAtom "L32"), (file_0, 97%N)); ((TAtom "L34"), (file_0, 103%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v100"), "__ctype32_b"); ((TAtom "v103"), "__libc_tsd_LOCALE"); ((TAtom "v112"), "__ctype32_toupper"); ((TAtom "v115"), "__libc_tsd_LOCALE"); ((TAtom "v124"), "__ctype32_tolower"); ((TAtom "v16"), "ctypes"); ((TAtom "v25"), "ctypes"); ((TAtom "v36"), "__libc_tsd_LOCALE"); ((TAtom "v4"), "ctypes"); ((TAtom "v44"), "__libc_tsd_CTYPE_B"); ((TAtom "v48"), "__libc_tsd_CTYPE_TOUPPER"); ((TAtom "v52"), "__libc_tsd_CTYPE_TOLOWER"); ((TAtom "v55"), "__libc_tsd_LOCALE"); ((TAtom "v64"), "__ctype_b"); ((TAtom "v67"), "__libc_tsd_LOCALE"); ((TAtom "v7"), "ctypes"); ((TAtom "v76"), "__ctype_toupper"); ((TAtom "v79"), "__libc_tsd_LOCALE"); ((TAtom "v88"), "__ctype_tolower"); ((TAtom "v91"), "__libc_tsd_LOCALE")].

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  [((TAtom "chk0"), ((TAtom "v1"), "&_nl_global_locale", 0)); ((TAtom "chk1"), ((TAtom "v4"), "ctypes", 0)); ((TAtom "chk10"), ((TAtom "v46"), "&_nl_global_locale", 120)); ((TAtom "chk11"), ((TAtom "v45"), "&__libc_tsd_CTYPE_TOUPPER", 0)); ((TAtom "chk12"), ((TAtom "v50"), "&_nl_global_locale", 112)); ((TAtom "chk13"), ((TAtom "v49"), "&__libc_tsd_CTYPE_TOLOWER", 0)); ((TAtom "chk14"), ((TAtom "v54"), "&__libc_tsd_LOCALE", 0)); ((TAtom "chk15"), ((TAtom "v55"), "__libc_tsd_LOCALE", 0)); ((TAtom "chk16"), ((TAtom "v57"), "v57", 56)); ((TAtom "chk17"), ((TAtom "v53"), "&__ctype_b", 0)); ((TAtom "chk18"), ((TAtom "v66"), "&__libc_tsd_LOCALE", 0)); ((TAtom "chk19"), ((TAtom "v67"), "__libc_tsd_LOCALE", 0)); ((TAtom "chk2"), ((TAtom "v5"), "&_nl_global_locale", 104)); ((TAtom "chk20"), ((TAtom "v69"), "v69", 64)); ((TAtom "chk21"), ((TAtom "v65"), "&__ctype_toupper", 0)); ((TAtom "chk22"), ((TAtom "v78"), "&__libc_tsd_LOCALE", 0)); ((TAtom "chk23"), ((TAtom "v79"), "__libc_tsd_LOCALE", 0)); ((TAtom "chk24"), ((TAtom "v81"), "v81", 80)); ((TAtom "chk25"), ((TAtom "v77"), "&__ctype_tolower", 0)); ((TAtom "chk26"), ((TAtom "v90"), "&__libc_tsd_LOCALE", 0)); ((TAtom "chk27"), ((TAtom "v91"), "__libc_tsd_LOCALE", 0)); ((TAtom "chk28"), ((TAtom "v93"), "v93", 96)); ((TAtom "chk29"), ((TAtom "v89"), "&__ctype32_b", 0)); ((TAtom "chk3"), ((TAtom "v4"), "ctypes", 24)); ((TAtom "chk30"), ((TAtom "v102"), "&__libc_tsd_LOCALE", 0)); ((TAtom "chk31"), ((TAtom "v103"), "__libc_tsd_LOCALE", 0)); ((TAtom "chk32"), ((TAtom "v105"), "v105", 176)); ((TAtom "chk33"), ((TAtom "v101"), "&__ctype32_toupper", 0)); ((TAtom "chk34"), ((TAtom "v114"), "&__libc_tsd_LOCALE", 0)); ((TAtom "chk35"), ((TAtom "v115"), "__libc_tsd_LOCALE", 0)); ((TAtom "chk36"), ((TAtom "v117"), "v117", 184)); ((TAtom "chk37"), ((TAtom "v113"), "&__ctype32_tolower", 0)); ((TAtom "chk4"), ((TAtom "v14"), "&_nl_global_locale", 112)); ((TAtom "chk5"), ((TAtom "v4"), "ctypes", 8)); ((TAtom "chk6"), ((TAtom "v23"), "&_nl_global_locale", 120)); ((TAtom "chk7"), ((TAtom "v35"), "&__libc_tsd_LOCALE", 0)); ((TAtom "chk8"), ((TAtom "v42"), "&_nl_global_locale", 104)); ((TAtom "chk9"), ((TAtom "v41"), "&__libc_tsd_CTYPE_B", 0)); ((TAtom "v1"), ((TAtom "v1"), "&_nl_global_locale", 0)); ((TAtom "v101"), ((TAtom "v101"), "&__ctype32_toupper", 0)); ((TAtom "v102"), ((TAtom "v102"), "&__libc_tsd_LOCALE", 0)); ((TAtom "v103"), ((TAtom "v103"), "__libc_tsd_LOCALE", 0)); ((TAtom "v106"), ((TAtom "v105"), "v105", 56)); ((TAtom "v110"), ((TAtom "v105"), "v105", 176)); ((TAtom "v113"), ((TAtom "v113"), "&__ctype32_tolower", 0)); ((TAtom "v114"), ((TAtom "v114"), "&__libc_tsd_LOCALE", 0)); ((TAtom "v115"), ((TAtom "v115"), "__libc_tsd_LOCALE", 0)); ((TAtom "v118"), ((TAtom "v117"), "v117", 56)); ((TAtom "v122"), ((TAtom "v117"), "v117", 184)); ((TAtom "v13"), ((TAtom "v12"), "v12", 256)); ((TAtom "v14"), ((TAtom "v14"), "&_nl_global_locale", 0)); ((TAtom "v15"), ((TAtom "v14"), "&_nl_global_locale", 112)); ((TAtom "v20"), ((TAtom "v4"), "ctypes", 24)); ((TAtom "v22"), ((TAtom "v21"), "v21", 512)); ((TAtom "v23"), ((TAtom "v23"), "&_nl_global_locale", 0)); ((TAtom "v24"), ((TAtom "v23"), "&_nl_global_locale", 120)); ((TAtom "v29"), ((TAtom "v4"), "ctypes", 8)); ((TAtom "v31"), ((TAtom "v30"), "v30", 512)); ((TAtom "v35"), ((TAtom "v35"), "&__libc_tsd_LOCALE", 0)); ((TAtom "v36"), ((TAtom "v36"), "__libc_tsd_LOCALE", 0)); ((TAtom "v37"), ((TAtom "v37"), "&_nl_global_locale", 0)); ((TAtom "v4"), ((TAtom "v4"), "ctypes", 0)); ((TAtom "v41"), ((TAtom "v41"), "&__libc_tsd_CTYPE_B", 0)); ((TAtom "v42"), ((TAtom "v42"), "&_nl_global_locale", 0)); ((TAtom "v43"), ((TAtom "v42"), "&_nl_global_locale", 104)); ((TAtom "v44"), ((TAtom "v44"), "__libc_tsd_CTYPE_B", 0)); ((TAtom "v45"), ((TAtom "v45"), "&__libc_tsd_CTYPE_TOUPPER", 0)); ((TAtom "v46"), ((TAtom "v46"), "&_nl_global_locale", 0)); ((TAtom "v47"), ((TAtom "v46"), "&_nl_global_locale", 120)); ((TAtom "v48"), ((TAtom "v48"), "__libc_tsd_CTYPE_TOUPPER", 0)); ((TAtom "v49"), ((TAtom "v49"), "&__libc_tsd_CTYPE_TOLOWER", 0)); ((TAtom "v5"), ((TAtom "v5"), "&_nl_global_locale", 0)); ((TAtom "v50"), ((TAtom "v50"), "&_nl_global_locale", 0)); ((TAtom "v51"), ((TAtom "v50"), "&_nl_global_locale", 112)); ((TAtom "v52"), ((TAtom "v52"), "__libc_tsd_CTYPE_TOLOWER", 0)); ((TAtom "v53"), ((TAtom "v53"), "&__ctype_b", 0)); ((TAtom "v54"), ((TAtom "v54"), "&__libc_tsd_LOCALE", 0)); ((TAtom "v55"), ((TAtom "v55"), "__libc_tsd_LOCALE", 0)); ((TAtom "v58"), ((TAtom "v57"), "v57", 56)); ((TAtom "v6"), ((TAtom "v5"), "&_nl_global_locale", 104)); ((TAtom "v64"), ((TAtom "v64"), "__ctype_b", 0)); ((TAtom "v65"), ((TAtom "v65"), "&__ctype_toupper", 0)); ((TAtom "v66"), ((TAtom "v66"), "&__libc_tsd_LOCALE", 0)); ((TAtom "v67"), ((TAtom "v67"), "__libc_tsd_LOCALE", 0)); ((TAtom "v70"), ((TAtom "v69"), "v69", 56)); ((TAtom "v74"), ((TAtom "v69"), "v69", 64)); ((TAtom "v76"), ((TAtom "v76"), "__ctype_toupper", 0)); ((TAtom "v77"), ((TAtom "v77"), "&__ctype_tolower", 0)); ((TAtom "v78"), ((TAtom "v78"), "&__libc_tsd_LOCALE", 0)); ((TAtom "v79"), ((TAtom "v79"), "__libc_tsd_LOCALE", 0)); ((TAtom "v82"), ((TAtom "v81"), "v81", 56)); ((TAtom "v86"), ((TAtom "v81"), "v81", 80)); ((TAtom "v88"), ((TAtom "v88"), "__ctype_tolower", 0)); ((TAtom "v89"), ((TAtom "v89"), "&__ctype32_b", 0)); ((TAtom "v90"), ((TAtom "v90"), "&__libc_tsd_LOCALE", 0)); ((TAtom "v91"), ((TAtom "v91"), "__libc_tsd_LOCALE", 0)); ((TAtom "v94"), ((TAtom "v93"), "v93", 56)); ((TAtom "v98"), ((TAtom "v93"), "v93", 96))].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), []); ((TAtom "L32"), []); ((TAtom "L34"), [])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), []); ((TAtom "L32"), []); ((TAtom "L34"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "v1")]), (0), (Some 8), true, false, (Some (TAtom "v1")), (Some (0)), "_nl_global_locale.__locales"); (7%N, (TApp "tmp" [(TAtom "v4")]), (0), (Some 8), true, false, (Some (TAtom "v3")), (Some (56)), "opaque"); (10%N, (TApp "tmp" [(TAtom "v6")]), (0), (Some 8), false, true, (Some (TAtom "v5")), (Some (104)), "_nl_global_locale.__ctype_b"); (15%N, (TApp "tmp" [(TAtom "v20")]), (0), (Some 8), true, false, (Some (TAtom "v3")), (Some (80)), "opaque"); (18%N, (TApp "tmp" [(TAtom "v15")]), (0), (Some 8), false, true, (Some (TAtom "v14")), (Some (112)), "_nl_global_locale.__ctype_tolower"); (23%N, (TApp "tmp" [(TAtom "v29")]), (0), (Some 8), true, false, (Some (TAtom "v3")), (Some (64)), "opaque"); (26%N, (TApp "tmp" [(TAtom "v24")]), (0), (Some 8), false, true, (Some (TAtom "v23")), (Some (120)), "_nl_global_locale.__ctype_toupper"); (29%N, (TApp "tmp" [(TAtom "v35")]), (0), (Some 8), true, false, (Some (TAtom "v35")), (Some (0)), "opaque")]); ((TAtom "L32"), [(4%N, (TApp "tmp" [(TAtom "v43")]), (0), (Some 8), true, false, (Some (TAtom "v42")), (Some (104)), "_nl_global_locale.__ctype_b"); (6%N, (TApp "tmp" [(TAtom "v41")]), (0), (Some 8), false, true, (Some (TAtom "v41")), (Some (0)), "opaque"); (11%N, (TApp "tmp" [(TAtom "v47")]), (0), (Some 8), true, false, (Some (TAtom "v46")), (Some (120)), "_nl_global_locale.__ctype_toupper"); (13%N, (TApp "tmp" [(TAtom "v45")]), (0), (Some 8), false, true, (Some (TAtom "v45")), (Some (0)), "opaque"); (18%N, (TApp "tmp" [(TAtom "v51")]), (0), (Some 8), true, false, (Some (TAtom "v50")), (Some (112)), "_nl_global_locale.__ctype_tolower"); (20%N, (TApp "tmp" [(TAtom "v49")]), (0), (Some 8), false, true, (Some (TAtom "v49")), (Some (0)), "opaque")]); ((TAtom "L34"), [(3%N, (TApp "tmp" [(TAtom "v54")]), (0), (Some 8), true, false, (Some (TAtom "v54")), (Some (0)), "opaque"); (5%N, (TApp "tmp" [(TAtom "v55")]), (0), (Some 8), true, false, (Some (TAtom "v55")), (Some (0)), "__libc_tsd_LOCALE->__locales"); (8%N, (TApp "tmp" [(TAtom "v58")]), (0), (Some 8), true, false, (Some (TAtom "v57")), (Some (56)), "opaque"); (11%N, (TApp "tmp" [(TAtom "v53")]), (0), (Some 8), false, true, (Some (TAtom "v53")), (Some (0)), "opaque"); (15%N, (TApp "tmp" [(TAtom "v66")]), (0), (Some 8), true, false, (Some (TAtom "v66")), (Some (0)), "opaque"); (17%N, (TApp "tmp" [(TAtom "v67")]), (0), (Some 8), true, false, (Some (TAtom "v67")), (Some (0)), "__libc_tsd_LOCALE->__locales"); (21%N, (TApp "tmp" [(TAtom "v74")]), (0), (Some 8), true, false, (Some (TAtom "v69")), (Some (64)), "opaque"); (24%N, (TApp "tmp" [(TAtom "v65")]), (0), (Some 8), false, true, (Some (TAtom "v65")), (Some (0)), "opaque"); (28%N, (TApp "tmp" [(TAtom "v78")]), (0), (Some 8), true, false, (Some (TAtom "v78")), (Some (0)), "opaque"); (30%N, (TApp "tmp" [(TAtom "v79")]), (0), (Some 8), true, false, (Some (TAtom "v79")), (Some (0)), "__libc_tsd_LOCALE->__locales"); (34%N, (TApp "tmp" [(TAtom "v86")]), (0), (Some 8), true, false, (Some (TAtom "v81")), (Some (80)), "opaque"); (37%N, (TApp "tmp" [(TAtom "v77")]), (0), (Some 8), false, true, (Some (TAtom "v77")), (Some (0)), "opaque"); (41%N, (TApp "tmp" [(TAtom "v90")]), (0), (Some 8), true, false, (Some (TAtom "v90")), (Some (0)), "opaque"); (43%N, (TApp "tmp" [(TAtom "v91")]), (0), (Some 8), true, false, (Some (TAtom "v91")), (Some (0)), "__libc_tsd_LOCALE->__locales"); (47%N, (TApp "tmp" [(TAtom "v98")]), (0), (Some 8), true, false, (Some (TAtom "v93")), (Some (96)), "opaque"); (49%N, (TApp "tmp" [(TAtom "v89")]), (0), (Some 8), false, true, (Some (TAtom "v89")), (Some (0)), "opaque"); (53%N, (TApp "tmp" [(TAtom "v102")]), (0), (Some 8), true, false, (Some (TAtom "v102")), (Some (0)), "opaque"); (55%N, (TApp "tmp" [(TAtom "v103")]), (0), (Some 8), true, false, (Some (TAtom "v103")), (Some (0)), "__libc_tsd_LOCALE->__locales"); (59%N, (TApp "tmp" [(TAtom "v110")]), (0), (Some 8), true, false, (Some (TAtom "v105")), (Some (176)), "opaque"); (61%N, (TApp "tmp" [(TAtom "v101")]), (0), (Some 8), false, true, (Some (TAtom "v101")), (Some (0)), "opaque"); (65%N, (TApp "tmp" [(TAtom "v114")]), (0), (Some 8), true, false, (Some (TAtom "v114")), (Some (0)), "opaque"); (67%N, (TApp "tmp" [(TAtom "v115")]), (0), (Some 8), true, false, (Some (TAtom "v115")), (Some (0)), "__libc_tsd_LOCALE->__locales"); (71%N, (TApp "tmp" [(TAtom "v122")]), (0), (Some 8), true, false, (Some (TAtom "v117")), (Some (184)), "opaque"); (73%N, (TApp "tmp" [(TAtom "v113")]), (0), (Some 8), false, true, (Some (TAtom "v113")), (Some (0)), "opaque")])].


End fn__nl_postload_ctype.

(** Projection keeps instruction bodies out of the VM code used by the membership check. *)
Definition source_blocks : list (string * option (list name)) := Eval lazy in
  map (fun n => (n,
    match find_direct (TAtom n) postloadctype_module with
    | Some (Defined f) => Some (map b_label (fn_blocks f))
    | _ => None
    end)) ["_nl_postload_ctype"].

(** Projection keeps live sets and memory access records out of the membership computation. *)
Definition table_labels : list (string * list name) := Eval lazy in
  [("_nl_postload_ctype", app (map fst fn__nl_postload_ctype.block_src) (app (map fst fn__nl_postload_ctype.live_in) (app (map fst fn__nl_postload_ctype.live_out) (app (map fst fn__nl_postload_ctype.footprint) (fn__nl_postload_ctype.loop_heads)))))].

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

End PostloadCtypeSrc.
