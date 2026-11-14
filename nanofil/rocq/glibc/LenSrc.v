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


From Glibc Require Import LenCode.
Module LenSrc.

Definition file_0 : string := "../stdlib/stdbit.h".

Definition file_1 : string := "rocq/glibc/len.c".

Definition file_2 : string := "strlen.c".

(** Decoding once lets all source tables share the same checked function bodies. *)
Definition source_module : module := Eval vm_compute in code_module len_term.

Module fn_main.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_1, 9%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_1, 9%N))].

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


End fn_main.

Module fn___strlen.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_2, 31%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_2, 35%N)); ((TAtom "iw_3.start"), (file_0, 193%N)); ((TAtom "iw_3.iw_1.iw_1.L3"), (file_0, 193%N)); ((TAtom "iw_3.iw_1.iw_1.L4"), (file_0, 193%N)); ((TAtom "L28"), (file_2, 36%N)); ((TAtom "iw_5.start"), (file_0, 193%N)); ((TAtom "iw_5.iw_3.iw_1.iw_1.L3"), (file_0, 193%N)); ((TAtom "iw_5.iw_3.iw_1.iw_1.L4"), (file_0, 193%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.iw_1.v0"), "c_in"); ((TAtom "iw_1.iw_1.v5"), "c_in"); ((TAtom "iw_1.v0"), "x"); ((TAtom "iw_1.v11"), "m"); ((TAtom "iw_1.v3"), "m"); ((TAtom "iw_1.v4"), "x"); ((TAtom "iw_1.v5"), "m"); ((TAtom "iw_1.v7"), "m"); ((TAtom "iw_1.v9"), "x"); ((TAtom "iw_2.v0"), "word"); ((TAtom "iw_2.v14"), "word"); ((TAtom "iw_2.v15"), "s"); ((TAtom "iw_2.v2"), "s"); ((TAtom "iw_2.v8"), "word"); ((TAtom "iw_2.v9"), "s"); ((TAtom "iw_3.iw_1.iw_1.v0"), "__x"); ((TAtom "iw_3.iw_1.iw_1.v5"), "__x"); ((TAtom "iw_3.iw_1.iw_1.v7"), "__x"); ((TAtom "iw_3.iw_1.iw_2.v0"), "__x"); ((TAtom "iw_3.iw_1.iw_2.v5"), "__x"); ((TAtom "iw_3.iw_1.iw_2.v7"), "__x"); ((TAtom "iw_3.iw_1.iw_3.v0"), "__x"); ((TAtom "iw_3.iw_1.iw_3.v5"), "__x"); ((TAtom "iw_3.iw_1.iw_3.v7"), "__x"); ((TAtom "iw_3.iw_1.iw_4.v0"), "__x"); ((TAtom "iw_3.iw_1.iw_4.v5"), "__x"); ((TAtom "iw_3.iw_1.iw_4.v7"), "__x"); ((TAtom "iw_3.iw_1.v0"), "c"); ((TAtom "iw_3.iw_1.v12"), "c"); ((TAtom "iw_3.iw_1.v18"), "c"); ((TAtom "iw_3.iw_1.v21"), "c"); ((TAtom "iw_3.iw_1.v6"), "c"); ((TAtom "iw_3.iw_2.iw_1.v0"), "__x"); ((TAtom "iw_3.iw_2.iw_1.v5"), "__x"); ((TAtom "iw_3.iw_2.iw_1.v7"), "__x"); ((TAtom "iw_3.iw_2.v0"), "c"); ((TAtom "iw_3.iw_2.v2"), "c"); ((TAtom "iw_3.pr.1"), "r"); ((TAtom "iw_3.v0"), "c"); ((TAtom "iw_3.v10"), "r"); ((TAtom "iw_3.v11"), "r"); ((TAtom "iw_3.v7"), "c"); ((TAtom "iw_3.v8"), "r"); ((TAtom "iw_3.v9"), "c"); ((TAtom "iw_4.iw_1.iw_1.v0"), "c_in"); ((TAtom "iw_4.iw_1.iw_1.v5"), "c_in"); ((TAtom "iw_4.iw_1.iw_2.v0"), "c_in"); ((TAtom "iw_4.iw_1.iw_2.v5"), "c_in"); ((TAtom "iw_4.iw_1.v0"), "x"); ((TAtom "iw_4.iw_1.v12"), "msb"); ((TAtom "iw_4.iw_1.v3"), "lsb"); ((TAtom "iw_4.iw_1.v5"), "msb"); ((TAtom "iw_4.iw_1.v6"), "x"); ((TAtom "iw_4.iw_1.v7"), "lsb"); ((TAtom "iw_4.iw_1.v9"), "x"); ((TAtom "iw_4.v0"), "x"); ((TAtom "iw_4.v2"), "x"); ((TAtom "iw_5.iw_1.iw_1.v0"), "c_in"); ((TAtom "iw_5.iw_1.iw_1.v5"), "c_in"); ((TAtom "iw_5.iw_1.iw_2.v0"), "c_in"); ((TAtom "iw_5.iw_1.iw_2.v5"), "c_in"); ((TAtom "iw_5.iw_1.v0"), "x"); ((TAtom "iw_5.iw_1.v12"), "msb"); ((TAtom "iw_5.iw_1.v3"), "lsb"); ((TAtom "iw_5.iw_1.v5"), "msb"); ((TAtom "iw_5.iw_1.v6"), "x"); ((TAtom "iw_5.iw_1.v7"), "lsb"); ((TAtom "iw_5.iw_1.v9"), "x"); ((TAtom "iw_5.iw_2.iw_1.v0"), "c_in"); ((TAtom "iw_5.iw_2.iw_1.v5"), "c_in"); ((TAtom "iw_5.iw_2.v0"), "x"); ((TAtom "iw_5.iw_2.v11"), "m"); ((TAtom "iw_5.iw_2.v3"), "m"); ((TAtom "iw_5.iw_2.v4"), "x"); ((TAtom "iw_5.iw_2.v5"), "m"); ((TAtom "iw_5.iw_2.v7"), "m"); ((TAtom "iw_5.iw_2.v9"), "x"); ((TAtom "iw_5.iw_3.iw_1.iw_1.v0"), "__x"); ((TAtom "iw_5.iw_3.iw_1.iw_1.v5"), "__x"); ((TAtom "iw_5.iw_3.iw_1.iw_1.v7"), "__x"); ((TAtom "iw_5.iw_3.iw_1.iw_2.v0"), "__x"); ((TAtom "iw_5.iw_3.iw_1.iw_2.v5"), "__x"); ((TAtom "iw_5.iw_3.iw_1.iw_2.v7"), "__x"); ((TAtom "iw_5.iw_3.iw_1.iw_3.v0"), "__x"); ((TAtom "iw_5.iw_3.iw_1.iw_3.v5"), "__x"); ((TAtom "iw_5.iw_3.iw_1.iw_3.v7"), "__x"); ((TAtom "iw_5.iw_3.iw_1.iw_4.v0"), "__x"); ((TAtom "iw_5.iw_3.iw_1.iw_4.v5"), "__x"); ((TAtom "iw_5.iw_3.iw_1.iw_4.v7"), "__x"); ((TAtom "iw_5.iw_3.iw_1.v0"), "c"); ((TAtom "iw_5.iw_3.iw_1.v12"), "c"); ((TAtom "iw_5.iw_3.iw_1.v18"), "c"); ((TAtom "iw_5.iw_3.iw_1.v21"), "c"); ((TAtom "iw_5.iw_3.iw_1.v6"), "c"); ((TAtom "iw_5.iw_3.iw_2.iw_1.v0"), "__x"); ((TAtom "iw_5.iw_3.iw_2.iw_1.v5"), "__x"); ((TAtom "iw_5.iw_3.iw_2.iw_1.v7"), "__x"); ((TAtom "iw_5.iw_3.iw_2.v0"), "c"); ((TAtom "iw_5.iw_3.iw_2.v2"), "c"); ((TAtom "iw_5.iw_3.pr.1"), "r"); ((TAtom "iw_5.iw_3.v0"), "c"); ((TAtom "iw_5.iw_3.v10"), "r"); ((TAtom "iw_5.iw_3.v11"), "r"); ((TAtom "iw_5.iw_3.v7"), "c"); ((TAtom "iw_5.iw_3.v8"), "r"); ((TAtom "iw_5.iw_3.v9"), "c"); ((TAtom "iw_5.pr.1"), "x"); ((TAtom "iw_5.v0"), "x"); ((TAtom "iw_5.v10"), "x"); ((TAtom "iw_5.v6"), "x"); ((TAtom "iw_5.v7"), "x"); ((TAtom "iw_5.v8"), "x"); ((TAtom "iw_5.v9"), "x"); ((TAtom "pr.1"), "word_ptr"); ((TAtom "v0"), "str"); ((TAtom "v10"), "word_ptr"); ((TAtom "v12"), "word_ptr"); ((TAtom "v13"), "word"); ((TAtom "v15"), "word"); ((TAtom "v17"), "s_int"); ((TAtom "v18"), "mask"); ((TAtom "v22"), "mask"); ((TAtom "v24"), "mask"); ((TAtom "v3"), "str"); ((TAtom "v31"), "word_ptr"); ((TAtom "v32"), "word_ptr"); ((TAtom "v33"), "word"); ((TAtom "v34"), "word"); ((TAtom "v38"), "word_ptr"); ((TAtom "v39"), "word"); ((TAtom "v4"), "s_int"); ((TAtom "v43"), "str"); ((TAtom "v6"), "str")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L28")].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "iw_3.start"), [(TAtom "iw_2.v12")]); ((TAtom "iw_3.iw_1.iw_1.L3"), [(TAtom "iw_2.v12")]); ((TAtom "iw_3.iw_1.iw_1.L4"), []); ((TAtom "L28"), [(TAtom "v4")]); ((TAtom "iw_5.start"), [(TAtom "iw_4.iw_1.v13"); (TAtom "v32"); (TAtom "v37"); (TAtom "v4")]); ((TAtom "iw_5.iw_3.iw_1.iw_1.L3"), [(TAtom "iw_4.iw_1.v13"); (TAtom "v32"); (TAtom "v4")]); ((TAtom "iw_5.iw_3.iw_1.iw_1.L4"), [(TAtom "v32"); (TAtom "v4")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "iw_2.v12"); (TAtom "v10"); (TAtom "v4")]); ((TAtom "iw_3.start"), [(TAtom "iw_2.v12")]); ((TAtom "iw_3.iw_1.iw_1.L3"), [(TAtom "iw_3.iw_1.iw_1.v22")]); ((TAtom "iw_3.iw_1.iw_1.L4"), []); ((TAtom "L28"), [(TAtom "iw_4.iw_1.v13"); (TAtom "v32"); (TAtom "v37"); (TAtom "v4")]); ((TAtom "iw_5.start"), [(TAtom "iw_4.iw_1.v13"); (TAtom "v32"); (TAtom "v4")]); ((TAtom "iw_5.iw_3.iw_1.iw_1.L3"), [(TAtom "iw_5.iw_3.iw_1.iw_1.v22"); (TAtom "v32"); (TAtom "v4")]); ((TAtom "iw_5.iw_3.iw_1.iw_1.L4"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [(5%N, (TApp "tmp" [(TAtom "v10")]), (0), (Some 8), true, false, (Some (TAtom "v0")), None)]); ((TAtom "iw_3.start"), []); ((TAtom "iw_3.iw_1.iw_1.L3"), []); ((TAtom "iw_3.iw_1.iw_1.L4"), []); ((TAtom "L28"), [(2%N, (TApp "tmp" [(TAtom "v32")]), (0), (Some 8), true, false, (Some (TAtom "pr.1")), (Some (8)))]); ((TAtom "iw_5.start"), []); ((TAtom "iw_5.iw_3.iw_1.iw_1.L3"), []); ((TAtom "iw_5.iw_3.iw_1.iw_1.L4"), [])].


End fn___strlen.

(** Projection keeps instruction bodies out of the VM code used by the membership check. *)
Definition source_blocks : list (string * option (list name)) := Eval lazy in
  map (fun n => (n,
    match find_direct (TAtom n) source_module with
    | Some (Defined f) => Some (map b_label (fn_blocks f))
    | _ => None
    end)) ["main"; "__strlen"].

(** Projection keeps live sets and memory access records out of the membership computation. *)
Definition table_labels : list (string * list name) := Eval lazy in
  [("main", app (map fst fn_main.block_src) (app (map fst fn_main.live_in) (app (map fst fn_main.live_out) (app (map fst fn_main.footprint) (fn_main.loop_heads))))); ("__strlen", app (map fst fn___strlen.block_src) (app (map fst fn___strlen.live_in) (app (map fst fn___strlen.live_out) (app (map fst fn___strlen.footprint) (fn___strlen.loop_heads)))))].

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

End LenSrc.
