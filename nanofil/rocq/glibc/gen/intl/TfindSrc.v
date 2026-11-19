(** These tables connect checked function bodies to C declarations and source lines.
    Names and locations support annotations and diagnostic messages, not soundness premises.
    Natural-loop headers provide optional cuts for symbolic execution; any cut list is sound.
    Live sets and memory footprints guide execution but cannot justify a memory access.
    Computation checks that every recorded block label belongs to its function.
    The code generator reproduces this file from the capture; do not edit it. *)

From Stdlib Require Import String List Bool NArith ZArith.
From Glibc Require Import CodePrelude.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

From Glibc Require Import Unit_misc_tsearch_os.

Module TfindSrc.

Definition file_0 : string := "tsearch.c".

Module fn___GI___tfind.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_0, 370%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_0, 376%N)); ((TAtom "L9"), (file_0, 377%N)); ((TAtom "L11"), (file_0, 379%N)); ((TAtom "L19"), (file_0, 374%N)); ((TAtom "L20"), (file_0, 384%N)); ((TAtom "L35"), (file_0, 389%N)); ((TAtom "L37"), (file_0, 391%N)); ((TAtom "L42"), (file_0, 391%N)); ((TAtom "L43"), (file_0, 391%N)); ((TAtom "L21"), (file_0, 393%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "pr.1"), "rootp"); ((TAtom "v0"), "key"); ((TAtom "v12"), "rootp"); ((TAtom "v17"), "rootp"); ((TAtom "v18"), "root"); ((TAtom "v2"), "vrootp"); ((TAtom "v22"), "rootp"); ((TAtom "v27"), "rootp"); ((TAtom "v28"), "root"); ((TAtom "v30"), "compar"); ((TAtom "v31"), "key"); ((TAtom "v32"), "root"); ((TAtom "v34"), "r"); ((TAtom "v38"), "r"); ((TAtom "v4"), "compar"); ((TAtom "v40"), "root"); ((TAtom "v45"), "r"); ((TAtom "v47"), "root"); ((TAtom "v49"), "root"); ((TAtom "v51"), "rootp"); ((TAtom "v8"), "vrootp")].

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  [((TAtom "chk0"), ((TAtom "v2"), "vrootp", 0)); ((TAtom "chk1"), ((TAtom "pr.1"), "rootp", 0)); ((TAtom "chk3"), ((TAtom "v28"), "root", 0)); ((TAtom "pr.1"), ((TAtom "pr.1"), "rootp", 0)); ((TAtom "v0"), ((TAtom "v0"), "key", 0)); ((TAtom "v18"), ((TAtom "v18"), "root", 0)); ((TAtom "v2"), ((TAtom "v2"), "vrootp", 0)); ((TAtom "v28"), ((TAtom "v28"), "root", 0)); ((TAtom "v34"), ((TAtom "v34"), "r", 0)); ((TAtom "v4"), ((TAtom "v4"), "compar", 0)); ((TAtom "v48"), ((TAtom "v28"), "root", 8)); ((TAtom "v50"), ((TAtom "v28"), "root", 16))].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L19")].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L9"), []); ((TAtom "L11"), [(TAtom "v0"); (TAtom "v14"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L19"), [(TAtom "v0"); (TAtom "v14"); (TAtom "v4")]); ((TAtom "L20"), [(TAtom "chk1"); (TAtom "v0"); (TAtom "v14"); (TAtom "v4")]); ((TAtom "L35"), [(TAtom "v28")]); ((TAtom "L37"), [(TAtom "v0"); (TAtom "v14"); (TAtom "v28"); (TAtom "v34"); (TAtom "v4")]); ((TAtom "L42"), [(TAtom "v0"); (TAtom "v14"); (TAtom "v28"); (TAtom "v4")]); ((TAtom "L43"), [(TAtom "v0"); (TAtom "v14"); (TAtom "v28"); (TAtom "v4")]); ((TAtom "L21"), [])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v14"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L9"), []); ((TAtom "L11"), [(TAtom "v0"); (TAtom "v14"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L19"), [(TAtom "chk1"); (TAtom "v0"); (TAtom "v14"); (TAtom "v4")]); ((TAtom "L20"), [(TAtom "v0"); (TAtom "v14"); (TAtom "v28"); (TAtom "v34"); (TAtom "v4")]); ((TAtom "L35"), []); ((TAtom "L37"), [(TAtom "v0"); (TAtom "v14"); (TAtom "v28"); (TAtom "v4")]); ((TAtom "L42"), [(TAtom "v0"); (TAtom "v14"); (TAtom "v4"); (TAtom "v48")]); ((TAtom "L43"), [(TAtom "v0"); (TAtom "v14"); (TAtom "v4"); (TAtom "v50")]); ((TAtom "L21"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), []); ((TAtom "L9"), []); ((TAtom "L11"), [(1%N, (TApp "tmp" [(TAtom "v2")]), (0), (Some 8), true, false, (Some (TAtom "v2")), (Some (0)), "opaque")]); ((TAtom "L19"), [(1%N, (TApp "tmp" [(TAtom "pr.1")]), (0), (Some 8), true, false, (Some (TAtom "pr.1")), (Some (0)), "opaque")]); ((TAtom "L20"), [(0%N, (TApp "tmp" [(TAtom "pr.1")]), (0), (Some 8), true, false, (Some (TAtom "pr.1")), (Some (0)), "opaque"); (2%N, (TApp "tmp" [(TAtom "v28")]), (0), (Some 8), true, false, (Some (TAtom "v28")), (Some (0)), "root->key")]); ((TAtom "L35"), []); ((TAtom "L37"), []); ((TAtom "L42"), []); ((TAtom "L43"), []); ((TAtom "L21"), [])].


End fn___GI___tfind.

(** Projection keeps instruction bodies out of the VM code used by the membership check. *)
Definition source_blocks : list (string * list name) := Eval lazy in
  [("__GI___tfind", map b_label (fn_blocks Unit_misc_tsearch_os.fn___GI___tfind))].

(** Projection keeps live sets and memory access records out of the membership computation. *)
Definition table_labels : list (string * list name) := Eval lazy in
  [("__GI___tfind", app (map fst fn___GI___tfind.block_src) (app (map fst fn___GI___tfind.live_in) (app (map fst fn___GI___tfind.live_out) (app (map fst fn___GI___tfind.footprint) (fn___GI___tfind.loop_heads)))))].

(** One computation rejects missing functions and stale labels across all tables in this fixture. *)
Lemma labels_valid :
  forallb (fun row =>
  match find (fun entry => String.eqb (fst entry) (fst row)) source_blocks with
  | Some (_, labels) =>
      forallb (fun l => existsb (name_eqb l) labels)
        (snd row)
  | _ => false
  end) table_labels = true.
Proof. vm_compute. reflexivity. Qed.

End TfindSrc.
