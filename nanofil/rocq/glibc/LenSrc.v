(** These tables connect checked function bodies to C declarations and source lines.
    Names and locations support annotations and diagnostic messages, not soundness premises.
    Natural-loop headers provide optional cuts for symbolic execution; any cut list is sound.
    Computation checks that every recorded block label belongs to the decoded function.
    The code generator reproduces this file from the capture; do not edit it. *)

From Stdlib Require Import String List Bool.
From Glibc Require Import CodePrelude LenCode.
Import ListNotations.
Open Scope string_scope.

Module LenSrc.

Module fn_main.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("rocq/glibc/len.c", 9%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("rocq/glibc/len.c", 9%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "main") (code_module len_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn_main.

Module fn___strlen.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("strlen.c", 31%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("strlen.c", 35%nat)); ((TAtom "iw_3.start"), ("../stdlib/stdbit.h", 193%nat)); ((TAtom "iw_3.iw_1.iw_1.L3"), ("../stdlib/stdbit.h", 193%nat)); ((TAtom "iw_3.iw_1.iw_1.L4"), ("../stdlib/stdbit.h", 193%nat)); ((TAtom "L28"), ("strlen.c", 36%nat)); ((TAtom "iw_5.start"), ("../stdlib/stdbit.h", 193%nat)); ((TAtom "iw_5.iw_3.iw_1.iw_1.L3"), ("../stdlib/stdbit.h", 193%nat)); ((TAtom "iw_5.iw_3.iw_1.iw_1.L4"), ("../stdlib/stdbit.h", 193%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.iw_1.v0"), "c_in"); ((TAtom "iw_1.iw_1.v5"), "c_in"); ((TAtom "iw_1.v0"), "x"); ((TAtom "iw_1.v11"), "m"); ((TAtom "iw_1.v3"), "m"); ((TAtom "iw_1.v4"), "x"); ((TAtom "iw_1.v5"), "m"); ((TAtom "iw_1.v7"), "m"); ((TAtom "iw_1.v9"), "x"); ((TAtom "iw_2.v0"), "word"); ((TAtom "iw_2.v14"), "word"); ((TAtom "iw_2.v15"), "s"); ((TAtom "iw_2.v2"), "s"); ((TAtom "iw_2.v8"), "word"); ((TAtom "iw_2.v9"), "s"); ((TAtom "iw_3.iw_1.iw_1.v0"), "__x"); ((TAtom "iw_3.iw_1.iw_1.v5"), "__x"); ((TAtom "iw_3.iw_1.iw_1.v7"), "__x"); ((TAtom "iw_3.iw_1.iw_2.v0"), "__x"); ((TAtom "iw_3.iw_1.iw_2.v5"), "__x"); ((TAtom "iw_3.iw_1.iw_2.v7"), "__x"); ((TAtom "iw_3.iw_1.iw_3.v0"), "__x"); ((TAtom "iw_3.iw_1.iw_3.v5"), "__x"); ((TAtom "iw_3.iw_1.iw_3.v7"), "__x"); ((TAtom "iw_3.iw_1.iw_4.v0"), "__x"); ((TAtom "iw_3.iw_1.iw_4.v5"), "__x"); ((TAtom "iw_3.iw_1.iw_4.v7"), "__x"); ((TAtom "iw_3.iw_1.v0"), "c"); ((TAtom "iw_3.iw_1.v12"), "c"); ((TAtom "iw_3.iw_1.v18"), "c"); ((TAtom "iw_3.iw_1.v21"), "c"); ((TAtom "iw_3.iw_1.v6"), "c"); ((TAtom "iw_3.iw_2.iw_1.v0"), "__x"); ((TAtom "iw_3.iw_2.iw_1.v5"), "__x"); ((TAtom "iw_3.iw_2.iw_1.v7"), "__x"); ((TAtom "iw_3.iw_2.v0"), "c"); ((TAtom "iw_3.iw_2.v2"), "c"); ((TAtom "iw_3.pr.1"), "r"); ((TAtom "iw_3.v0"), "c"); ((TAtom "iw_3.v10"), "r"); ((TAtom "iw_3.v11"), "r"); ((TAtom "iw_3.v7"), "c"); ((TAtom "iw_3.v8"), "r"); ((TAtom "iw_3.v9"), "c"); ((TAtom "iw_4.iw_1.iw_1.v0"), "c_in"); ((TAtom "iw_4.iw_1.iw_1.v5"), "c_in"); ((TAtom "iw_4.iw_1.iw_2.v0"), "c_in"); ((TAtom "iw_4.iw_1.iw_2.v5"), "c_in"); ((TAtom "iw_4.iw_1.v0"), "x"); ((TAtom "iw_4.iw_1.v12"), "msb"); ((TAtom "iw_4.iw_1.v3"), "lsb"); ((TAtom "iw_4.iw_1.v5"), "msb"); ((TAtom "iw_4.iw_1.v6"), "x"); ((TAtom "iw_4.iw_1.v7"), "lsb"); ((TAtom "iw_4.iw_1.v9"), "x"); ((TAtom "iw_4.v0"), "x"); ((TAtom "iw_4.v2"), "x"); ((TAtom "iw_5.iw_1.iw_1.v0"), "c_in"); ((TAtom "iw_5.iw_1.iw_1.v5"), "c_in"); ((TAtom "iw_5.iw_1.iw_2.v0"), "c_in"); ((TAtom "iw_5.iw_1.iw_2.v5"), "c_in"); ((TAtom "iw_5.iw_1.v0"), "x"); ((TAtom "iw_5.iw_1.v12"), "msb"); ((TAtom "iw_5.iw_1.v3"), "lsb"); ((TAtom "iw_5.iw_1.v5"), "msb"); ((TAtom "iw_5.iw_1.v6"), "x"); ((TAtom "iw_5.iw_1.v7"), "lsb"); ((TAtom "iw_5.iw_1.v9"), "x"); ((TAtom "iw_5.iw_2.iw_1.v0"), "c_in"); ((TAtom "iw_5.iw_2.iw_1.v5"), "c_in"); ((TAtom "iw_5.iw_2.v0"), "x"); ((TAtom "iw_5.iw_2.v11"), "m"); ((TAtom "iw_5.iw_2.v3"), "m"); ((TAtom "iw_5.iw_2.v4"), "x"); ((TAtom "iw_5.iw_2.v5"), "m"); ((TAtom "iw_5.iw_2.v7"), "m"); ((TAtom "iw_5.iw_2.v9"), "x"); ((TAtom "iw_5.iw_3.iw_1.iw_1.v0"), "__x"); ((TAtom "iw_5.iw_3.iw_1.iw_1.v5"), "__x"); ((TAtom "iw_5.iw_3.iw_1.iw_1.v7"), "__x"); ((TAtom "iw_5.iw_3.iw_1.iw_2.v0"), "__x"); ((TAtom "iw_5.iw_3.iw_1.iw_2.v5"), "__x"); ((TAtom "iw_5.iw_3.iw_1.iw_2.v7"), "__x"); ((TAtom "iw_5.iw_3.iw_1.iw_3.v0"), "__x"); ((TAtom "iw_5.iw_3.iw_1.iw_3.v5"), "__x"); ((TAtom "iw_5.iw_3.iw_1.iw_3.v7"), "__x"); ((TAtom "iw_5.iw_3.iw_1.iw_4.v0"), "__x"); ((TAtom "iw_5.iw_3.iw_1.iw_4.v5"), "__x"); ((TAtom "iw_5.iw_3.iw_1.iw_4.v7"), "__x"); ((TAtom "iw_5.iw_3.iw_1.v0"), "c"); ((TAtom "iw_5.iw_3.iw_1.v12"), "c"); ((TAtom "iw_5.iw_3.iw_1.v18"), "c"); ((TAtom "iw_5.iw_3.iw_1.v21"), "c"); ((TAtom "iw_5.iw_3.iw_1.v6"), "c"); ((TAtom "iw_5.iw_3.iw_2.iw_1.v0"), "__x"); ((TAtom "iw_5.iw_3.iw_2.iw_1.v5"), "__x"); ((TAtom "iw_5.iw_3.iw_2.iw_1.v7"), "__x"); ((TAtom "iw_5.iw_3.iw_2.v0"), "c"); ((TAtom "iw_5.iw_3.iw_2.v2"), "c"); ((TAtom "iw_5.iw_3.pr.1"), "r"); ((TAtom "iw_5.iw_3.v0"), "c"); ((TAtom "iw_5.iw_3.v10"), "r"); ((TAtom "iw_5.iw_3.v11"), "r"); ((TAtom "iw_5.iw_3.v7"), "c"); ((TAtom "iw_5.iw_3.v8"), "r"); ((TAtom "iw_5.iw_3.v9"), "c"); ((TAtom "iw_5.pr.1"), "x"); ((TAtom "iw_5.v0"), "x"); ((TAtom "iw_5.v10"), "x"); ((TAtom "iw_5.v6"), "x"); ((TAtom "iw_5.v7"), "x"); ((TAtom "iw_5.v8"), "x"); ((TAtom "iw_5.v9"), "x"); ((TAtom "pr.1"), "word_ptr"); ((TAtom "v0"), "str"); ((TAtom "v10"), "word_ptr"); ((TAtom "v12"), "word_ptr"); ((TAtom "v13"), "word"); ((TAtom "v15"), "word"); ((TAtom "v17"), "s_int"); ((TAtom "v18"), "mask"); ((TAtom "v22"), "mask"); ((TAtom "v24"), "mask"); ((TAtom "v3"), "str"); ((TAtom "v31"), "word_ptr"); ((TAtom "v32"), "word_ptr"); ((TAtom "v33"), "word"); ((TAtom "v34"), "word"); ((TAtom "v38"), "word_ptr"); ((TAtom "v39"), "word"); ((TAtom "v4"), "s_int"); ((TAtom "v43"), "str"); ((TAtom "v6"), "str")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L28")].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__strlen") (code_module len_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___strlen.

End LenSrc.
