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


From Glibc Require Import ItoaWordCode.
Module ItoaWordSrc.

Definition file_0 : string := "_fitoa_word.c".

Module fn__itoa_word.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_0, 21%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_0, 25%N)); ((TAtom "L9"), (file_0, 25%N)); ((TAtom "L10"), (file_0, 25%N)); ((TAtom "L11"), (file_0, 25%N)); ((TAtom "L20"), (file_0, 21%N)); ((TAtom "L34"), (file_0, 21%N)); ((TAtom "L48"), (file_0, 21%N)); ((TAtom "L62"), (file_0, 21%N)); ((TAtom "L80"), (file_0, 29%N)); ((TAtom "L82"), (file_0, 29%N)); ((TAtom "L18"), (file_0, 21%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "pr.1"), "value"); ((TAtom "pr.2"), "value"); ((TAtom "pr.3"), "value"); ((TAtom "pr.4"), "value"); ((TAtom "pr.5"), "buflim"); ((TAtom "pr.6"), "buflim"); ((TAtom "pr.7"), "buflim"); ((TAtom "pr.8"), "buflim"); ((TAtom "pr.9"), "buflim"); ((TAtom "v0"), "value"); ((TAtom "v12"), "upper_case"); ((TAtom "v15"), "digits"); ((TAtom "v16"), "base"); ((TAtom "v2"), "buflim"); ((TAtom "v23"), "buflim"); ((TAtom "v24"), "buflim"); ((TAtom "v25"), "digits"); ((TAtom "v26"), "value"); ((TAtom "v30"), "value"); ((TAtom "v31"), "value"); ((TAtom "v37"), "buflim"); ((TAtom "v38"), "buflim"); ((TAtom "v39"), "digits"); ((TAtom "v4"), "base"); ((TAtom "v40"), "value"); ((TAtom "v44"), "value"); ((TAtom "v45"), "value"); ((TAtom "v51"), "buflim"); ((TAtom "v52"), "buflim"); ((TAtom "v53"), "digits"); ((TAtom "v54"), "value"); ((TAtom "v58"), "value"); ((TAtom "v59"), "value"); ((TAtom "v6"), "upper_case"); ((TAtom "v65"), "buflim"); ((TAtom "v66"), "buflim"); ((TAtom "v67"), "digits"); ((TAtom "v68"), "value"); ((TAtom "v69"), "base"); ((TAtom "v74"), "value"); ((TAtom "v75"), "base"); ((TAtom "v77"), "value"); ((TAtom "v85"), "buflim")].

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  [((TAtom "chk0"), ((TAtom "v28"), "v28", 0)); ((TAtom "chk1"), ((TAtom "v24"), "buflim", 0)); ((TAtom "chk2"), ((TAtom "v42"), "v42", 0)); ((TAtom "chk3"), ((TAtom "v38"), "buflim", 0)); ((TAtom "chk4"), ((TAtom "v56"), "v56", 0)); ((TAtom "chk5"), ((TAtom "v52"), "buflim", 0)); ((TAtom "chk6"), ((TAtom "v72"), "v72", 0)); ((TAtom "chk7"), ((TAtom "v66"), "buflim", 0)); ((TAtom "pr.1"), ((TAtom "pr.1"), "value", 0)); ((TAtom "pr.2"), ((TAtom "pr.2"), "value", 0)); ((TAtom "pr.3"), ((TAtom "pr.3"), "value", 0)); ((TAtom "pr.4"), ((TAtom "pr.4"), "value", 0)); ((TAtom "pr.5"), ((TAtom "pr.5"), "buflim", 0)); ((TAtom "pr.6"), ((TAtom "pr.6"), "buflim", 0)); ((TAtom "pr.7"), ((TAtom "pr.7"), "buflim", 0)); ((TAtom "pr.8"), ((TAtom "pr.8"), "buflim", 0)); ((TAtom "pr.9"), ((TAtom "pr.9"), "buflim", 0)); ((TAtom "v0"), ((TAtom "v0"), "value", 0)); ((TAtom "v13"), ((TAtom "v13"), "&_itoa_upper_digits", 0)); ((TAtom "v14"), ((TAtom "v14"), "&_itoa_lower_digits", 0)); ((TAtom "v15"), ((TAtom "v15"), "digits", 0)); ((TAtom "v2"), ((TAtom "v2"), "buflim", 0)); ((TAtom "v24"), ((TAtom "v24"), "buflim", 0)); ((TAtom "v31"), ((TAtom "v31"), "value", 0)); ((TAtom "v38"), ((TAtom "v38"), "buflim", 0)); ((TAtom "v4"), ((TAtom "v4"), "base", 0)); ((TAtom "v45"), ((TAtom "v45"), "value", 0)); ((TAtom "v52"), ((TAtom "v52"), "buflim", 0)); ((TAtom "v59"), ((TAtom "v59"), "value", 0)); ((TAtom "v6"), ((TAtom "v6"), "upper_case", 0)); ((TAtom "v66"), ((TAtom "v66"), "buflim", 0)); ((TAtom "v77"), ((TAtom "v77"), "value", 0))].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L20"); (TAtom "L34"); (TAtom "L48"); (TAtom "L62")].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L9"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L10"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L11"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L20"), [(TAtom "v15")]); ((TAtom "L34"), [(TAtom "v15")]); ((TAtom "L48"), [(TAtom "v15")]); ((TAtom "L62"), [(TAtom "v15"); (TAtom "v4")]); ((TAtom "L80"), [(TAtom "v0"); (TAtom "v15"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L82"), [(TAtom "v0"); (TAtom "v15"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L18"), [])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L9"), [(TAtom "v0"); (TAtom "v13"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L10"), [(TAtom "v0"); (TAtom "v14"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L11"), [(TAtom "v0"); (TAtom "v15"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L20"), [(TAtom "v15"); (TAtom "v24"); (TAtom "v31")]); ((TAtom "L34"), [(TAtom "v15"); (TAtom "v38"); (TAtom "v45")]); ((TAtom "L48"), [(TAtom "v15"); (TAtom "v52"); (TAtom "v59")]); ((TAtom "L62"), [(TAtom "v15"); (TAtom "v4"); (TAtom "v66"); (TAtom "v77")]); ((TAtom "L80"), [(TAtom "v0"); (TAtom "v15"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L82"), [(TAtom "v0"); (TAtom "v15"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L18"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), []); ((TAtom "L9"), []); ((TAtom "L10"), []); ((TAtom "L11"), []); ((TAtom "L20"), [(4%N, (TApp "tmp" [(TAtom "v28")]), (0), (Some 1), true, false, (Some (TAtom "v15")), None, "opaque"); (6%N, (TApp "tmp" [(TAtom "v24")]), (0), (Some 1), false, true, (Some (TAtom "pr.6")), (Some (-1)), "opaque")]); ((TAtom "L34"), [(4%N, (TApp "tmp" [(TAtom "v42")]), (0), (Some 1), true, false, (Some (TAtom "v15")), None, "opaque"); (6%N, (TApp "tmp" [(TAtom "v38")]), (0), (Some 1), false, true, (Some (TAtom "pr.7")), (Some (-1)), "opaque")]); ((TAtom "L48"), [(4%N, (TApp "tmp" [(TAtom "v56")]), (0), (Some 1), true, false, (Some (TAtom "v15")), None, "opaque"); (6%N, (TApp "tmp" [(TAtom "v52")]), (0), (Some 1), false, true, (Some (TAtom "pr.8")), (Some (-1)), "opaque")]); ((TAtom "L62"), [(5%N, (TApp "tmp" [(TAtom "v72")]), (0), (Some 1), true, false, (Some (TAtom "v15")), None, "opaque"); (7%N, (TApp "tmp" [(TAtom "v66")]), (0), (Some 1), false, true, (Some (TAtom "pr.9")), (Some (-1)), "opaque")]); ((TAtom "L80"), []); ((TAtom "L82"), []); ((TAtom "L18"), [])].


End fn__itoa_word.

(** Projection keeps instruction bodies out of the VM code used by the membership check. *)
Definition source_blocks : list (string * option (list name)) := Eval lazy in
  map (fun n => (n,
    match find_direct (TAtom n) itoaword_module with
    | Some (Defined f) => Some (map b_label (fn_blocks f))
    | _ => None
    end)) ["_itoa_word"].

(** Projection keeps live sets and memory access records out of the membership computation. *)
Definition table_labels : list (string * list name) := Eval lazy in
  [("_itoa_word", app (map fst fn__itoa_word.block_src) (app (map fst fn__itoa_word.live_in) (app (map fst fn__itoa_word.live_out) (app (map fst fn__itoa_word.footprint) (fn__itoa_word.loop_heads)))))].

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

End ItoaWordSrc.
