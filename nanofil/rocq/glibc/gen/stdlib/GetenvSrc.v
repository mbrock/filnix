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

From Glibc Require Import Unit_stdlib_getenv_os.

Module GetenvSrc.

Definition file_0 : string := "getenv.c".

Module fn___GI_getenv.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_0, 23%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_0, 26%N)); ((TAtom "L3"), (file_0, 29%N)); ((TAtom "L18"), (file_0, 43%N)); ((TAtom "L19"), (file_0, 43%N)); ((TAtom "L11"), (file_0, 44%N)); ((TAtom "L13"), (file_0, 46%N)); ((TAtom "L32"), (file_0, 47%N)); ((TAtom "L41"), (file_0, 55%N)); ((TAtom "L57"), (file_0, 55%N)); ((TAtom "L58"), (file_0, 55%N)); ((TAtom "L66"), (file_0, 55%N)); ((TAtom "L67"), (file_0, 55%N)); ((TAtom "L47"), (file_0, 57%N)); ((TAtom "L34"), (file_0, 47%N)); ((TAtom "L35"), (file_0, 69%N)); ((TAtom "L82"), (file_0, 149%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "pr.1"), "ep"); ((TAtom "v0"), "name"); ((TAtom "v10"), "start_environ"); ((TAtom "v14"), "start_environ"); ((TAtom "v20"), "name"); ((TAtom "v28"), "name"); ((TAtom "v29"), "len"); ((TAtom "v31"), "start_environ"); ((TAtom "v37"), "ep"); ((TAtom "v38"), "entry"); ((TAtom "v42"), "entry"); ((TAtom "v50"), "name"); ((TAtom "v53"), "entry"); ((TAtom "v59"), "name"); ((TAtom "v60"), "entry"); ((TAtom "v61"), "len"); ((TAtom "v68"), "entry"); ((TAtom "v69"), "len"); ((TAtom "v7"), "__environ_counter"); ((TAtom "v75"), "entry"); ((TAtom "v76"), "len"); ((TAtom "v80"), "ep"); ((TAtom "v81"), "ep"); ((TAtom "v86"), "__environ_counter"); ((TAtom "v87"), "start_counter")].

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  [((TAtom "chk0"), ((TAtom "v6"), "&__environ_counter", 0)); ((TAtom "chk1"), ((TAtom "v9"), "&__environ", 0)); ((TAtom "chk2"), ((TAtom "v0"), "name", 0)); ((TAtom "chk3"), ((TAtom "pr.1"), "ep", 0)); ((TAtom "chk4"), ((TAtom "v0"), "name", 0)); ((TAtom "chk5"), ((TAtom "v38"), "entry", 0)); ((TAtom "chk6"), ((TAtom "v70"), "v70", 0)); ((TAtom "chk7"), ((TAtom "v85"), "&__environ_counter", 0)); ((TAtom "pr.1"), ((TAtom "pr.1"), "ep", 0)); ((TAtom "v0"), ((TAtom "v0"), "name", 0)); ((TAtom "v10"), ((TAtom "v10"), "start_environ", 0)); ((TAtom "v29"), ((TAtom "v29"), "len", 0)); ((TAtom "v38"), ((TAtom "v38"), "entry", 0)); ((TAtom "v6"), ((TAtom "v6"), "&__environ_counter", 0)); ((TAtom "v7"), ((TAtom "v7"), "__environ_counter", 0)); ((TAtom "v78"), ((TAtom "v77"), "v77", 1)); ((TAtom "v81"), ((TAtom "v81"), "ep", 0)); ((TAtom "v85"), ((TAtom "v85"), "&__environ_counter", 0)); ((TAtom "v86"), ((TAtom "v86"), "__environ_counter", 0)); ((TAtom "v9"), ((TAtom "v9"), "&__environ", 0))].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L3"); (TAtom "L32")].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "L3"), [(TAtom "v0")]); ((TAtom "L18"), [(TAtom "v0"); (TAtom "v10"); (TAtom "v16"); (TAtom "v7")]); ((TAtom "L19"), [(TAtom "v0"); (TAtom "v10"); (TAtom "v16"); (TAtom "v7")]); ((TAtom "L11"), []); ((TAtom "L13"), [(TAtom "v0"); (TAtom "v10"); (TAtom "v16"); (TAtom "v7")]); ((TAtom "L32"), [(TAtom "v0"); (TAtom "v16"); (TAtom "v29"); (TAtom "v7")]); ((TAtom "L41"), [(TAtom "pr.1"); (TAtom "v0"); (TAtom "v16"); (TAtom "v29"); (TAtom "v38"); (TAtom "v7")]); ((TAtom "L57"), [(TAtom "pr.1"); (TAtom "v0"); (TAtom "v16"); (TAtom "v29"); (TAtom "v38"); (TAtom "v7")]); ((TAtom "L58"), [(TAtom "pr.1"); (TAtom "v0"); (TAtom "v16"); (TAtom "v29"); (TAtom "v38"); (TAtom "v7")]); ((TAtom "L66"), [(TAtom "pr.1"); (TAtom "v0"); (TAtom "v16"); (TAtom "v29"); (TAtom "v38"); (TAtom "v7")]); ((TAtom "L67"), [(TAtom "pr.1"); (TAtom "v0"); (TAtom "v16"); (TAtom "v29"); (TAtom "v38"); (TAtom "v7")]); ((TAtom "L47"), [(TAtom "v29"); (TAtom "v38")]); ((TAtom "L34"), [(TAtom "pr.1"); (TAtom "v0"); (TAtom "v16"); (TAtom "v29"); (TAtom "v7")]); ((TAtom "L35"), [(TAtom "v0"); (TAtom "v7")]); ((TAtom "L82"), [])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "L3"), [(TAtom "v0"); (TAtom "v10"); (TAtom "v16"); (TAtom "v7")]); ((TAtom "L18"), [(TAtom "v0"); (TAtom "v10"); (TAtom "v16"); (TAtom "v23"); (TAtom "v7")]); ((TAtom "L19"), [(TAtom "v0"); (TAtom "v10"); (TAtom "v16"); (TAtom "v7")]); ((TAtom "L11"), []); ((TAtom "L13"), [(TAtom "v0"); (TAtom "v10"); (TAtom "v16"); (TAtom "v29"); (TAtom "v7")]); ((TAtom "L32"), [(TAtom "pr.1"); (TAtom "v0"); (TAtom "v16"); (TAtom "v29"); (TAtom "v38"); (TAtom "v7")]); ((TAtom "L41"), [(TAtom "pr.1"); (TAtom "v0"); (TAtom "v16"); (TAtom "v29"); (TAtom "v38"); (TAtom "v7")]); ((TAtom "L57"), [(TAtom "pr.1"); (TAtom "v0"); (TAtom "v16"); (TAtom "v29"); (TAtom "v38"); (TAtom "v63"); (TAtom "v7")]); ((TAtom "L58"), [(TAtom "pr.1"); (TAtom "v0"); (TAtom "v16"); (TAtom "v29"); (TAtom "v38"); (TAtom "v7")]); ((TAtom "L66"), [(TAtom "pr.1"); (TAtom "v0"); (TAtom "v16"); (TAtom "v29"); (TAtom "v38"); (TAtom "v7"); (TAtom "v72")]); ((TAtom "L67"), [(TAtom "pr.1"); (TAtom "v0"); (TAtom "v16"); (TAtom "v29"); (TAtom "v38"); (TAtom "v7")]); ((TAtom "L47"), []); ((TAtom "L34"), [(TAtom "v0"); (TAtom "v16"); (TAtom "v29"); (TAtom "v7"); (TAtom "v81")]); ((TAtom "L35"), [(TAtom "v0")]); ((TAtom "L82"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), []); ((TAtom "L3"), [(2%N, (TApp "tmp" [(TAtom "v6")]), (0), (Some 8), true, false, (Some (TAtom "v6")), (Some (0)), "opaque"); (5%N, (TApp "tmp" [(TAtom "v9")]), (0), (Some 8), true, false, (Some (TAtom "v9")), (Some (0)), "opaque")]); ((TAtom "L18"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 1), true, false, (Some (TAtom "v0")), (Some (0)), "opaque")]); ((TAtom "L19"), []); ((TAtom "L11"), []); ((TAtom "L13"), []); ((TAtom "L32"), [(1%N, (TApp "tmp" [(TAtom "pr.1")]), (0), (Some 8), true, false, (Some (TAtom "pr.1")), (Some (0)), "opaque")]); ((TAtom "L41"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 1), true, false, (Some (TAtom "v0")), (Some (0)), "opaque"); (3%N, (TApp "tmp" [(TAtom "v38")]), (0), (Some 1), true, false, (Some (TAtom "v38")), (Some (0)), "opaque")]); ((TAtom "L57"), []); ((TAtom "L58"), []); ((TAtom "L66"), [(2%N, (TApp "tmp" [(TAtom "v70")]), (0), (Some 1), true, false, (Some (TAtom "v38")), None, "opaque")]); ((TAtom "L67"), []); ((TAtom "L47"), []); ((TAtom "L34"), []); ((TAtom "L35"), [(2%N, (TApp "tmp" [(TAtom "v85")]), (0), (Some 8), true, false, (Some (TAtom "v85")), (Some (0)), "opaque")]); ((TAtom "L82"), [])].


End fn___GI_getenv.

(** Projection keeps instruction bodies out of the VM code used by the membership check. *)
Definition source_blocks : list (string * list name) := Eval lazy in
  [("__GI_getenv", map b_label (fn_blocks Unit_stdlib_getenv_os.fn___GI_getenv))].

(** Projection keeps live sets and memory access records out of the membership computation. *)
Definition table_labels : list (string * list name) := Eval lazy in
  [("__GI_getenv", app (map fst fn___GI_getenv.block_src) (app (map fst fn___GI_getenv.live_in) (app (map fst fn___GI_getenv.live_out) (app (map fst fn___GI_getenv.footprint) (fn___GI_getenv.loop_heads)))))].

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

End GetenvSrc.
