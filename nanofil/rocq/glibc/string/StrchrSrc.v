(** These tables connect checked function bodies to C declarations and source lines.
    Names and locations support annotations and diagnostic messages, not soundness premises.
    Natural-loop headers provide optional cuts for symbolic execution; any cut list is sound.
    Computation checks that every recorded block label belongs to the decoded function.
    The code generator reproduces this file from the capture; do not edit it. *)

From Stdlib Require Import String List Bool.
From Glibc Require Import CodePrelude StrchrCode.
Import ListNotations.
Open Scope string_scope.

Module StrchrSrc.

Module fn___GI_strchr.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("strchr.c", 28%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("strchr.c", 31%nat)); ((TAtom "L9"), ("strchr.c", 32%nat)); ((TAtom "L10"), ("strchr.c", 32%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "s"); ((TAtom "v11"), "r"); ((TAtom "v13"), "c_in"); ((TAtom "v16"), "r"); ((TAtom "v2"), "c_in"); ((TAtom "v5"), "s"); ((TAtom "v6"), "c_in"); ((TAtom "v7"), "r")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__GI_strchr") (code_module strchr_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___GI_strchr.

Module fn___GI___strchrnul.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("strchrnul.c", 33%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("strchrnul.c", 37%nat)); ((TAtom "iw_4.start"), ("../stdlib/stdbit.h", 193%nat)); ((TAtom "iw_4.iw_1.iw_1.L3"), ("../stdlib/stdbit.h", 193%nat)); ((TAtom "iw_4.iw_1.iw_1.L4"), ("../stdlib/stdbit.h", 193%nat)); ((TAtom "L37"), ("strchrnul.c", 38%nat)); ((TAtom "iw_6.start"), ("../stdlib/stdbit.h", 193%nat)); ((TAtom "iw_6.iw_3.iw_1.iw_1.L3"), ("../stdlib/stdbit.h", 193%nat)); ((TAtom "iw_6.iw_3.iw_1.iw_1.L4"), ("../stdlib/stdbit.h", 193%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "c_in"); ((TAtom "iw_1.v5"), "c_in"); ((TAtom "iw_2.iw_1.iw_1.v0"), "c_in"); ((TAtom "iw_2.iw_1.iw_1.v5"), "c_in"); ((TAtom "iw_2.iw_1.v0"), "x"); ((TAtom "iw_2.iw_1.v11"), "m"); ((TAtom "iw_2.iw_1.v3"), "m"); ((TAtom "iw_2.iw_1.v4"), "x"); ((TAtom "iw_2.iw_1.v5"), "m"); ((TAtom "iw_2.iw_1.v7"), "m"); ((TAtom "iw_2.iw_1.v9"), "x"); ((TAtom "iw_2.iw_2.iw_1.v0"), "c_in"); ((TAtom "iw_2.iw_2.iw_1.v5"), "c_in"); ((TAtom "iw_2.iw_2.v0"), "x"); ((TAtom "iw_2.iw_2.v11"), "m"); ((TAtom "iw_2.iw_2.v3"), "m"); ((TAtom "iw_2.iw_2.v4"), "x"); ((TAtom "iw_2.iw_2.v5"), "m"); ((TAtom "iw_2.iw_2.v7"), "m"); ((TAtom "iw_2.iw_2.v9"), "x"); ((TAtom "iw_2.v0"), "x1"); ((TAtom "iw_2.v2"), "x2"); ((TAtom "iw_2.v4"), "x1"); ((TAtom "iw_2.v6"), "x1"); ((TAtom "iw_2.v7"), "x2"); ((TAtom "iw_3.v0"), "word"); ((TAtom "iw_3.v14"), "word"); ((TAtom "iw_3.v15"), "s"); ((TAtom "iw_3.v2"), "s"); ((TAtom "iw_3.v8"), "word"); ((TAtom "iw_3.v9"), "s"); ((TAtom "iw_4.iw_1.iw_1.v0"), "__x"); ((TAtom "iw_4.iw_1.iw_1.v5"), "__x"); ((TAtom "iw_4.iw_1.iw_1.v7"), "__x"); ((TAtom "iw_4.iw_1.iw_2.v0"), "__x"); ((TAtom "iw_4.iw_1.iw_2.v5"), "__x"); ((TAtom "iw_4.iw_1.iw_2.v7"), "__x"); ((TAtom "iw_4.iw_1.iw_3.v0"), "__x"); ((TAtom "iw_4.iw_1.iw_3.v5"), "__x"); ((TAtom "iw_4.iw_1.iw_3.v7"), "__x"); ((TAtom "iw_4.iw_1.iw_4.v0"), "__x"); ((TAtom "iw_4.iw_1.iw_4.v5"), "__x"); ((TAtom "iw_4.iw_1.iw_4.v7"), "__x"); ((TAtom "iw_4.iw_1.v0"), "c"); ((TAtom "iw_4.iw_1.v12"), "c"); ((TAtom "iw_4.iw_1.v18"), "c"); ((TAtom "iw_4.iw_1.v21"), "c"); ((TAtom "iw_4.iw_1.v6"), "c"); ((TAtom "iw_4.iw_2.iw_1.v0"), "__x"); ((TAtom "iw_4.iw_2.iw_1.v5"), "__x"); ((TAtom "iw_4.iw_2.iw_1.v7"), "__x"); ((TAtom "iw_4.iw_2.v0"), "c"); ((TAtom "iw_4.iw_2.v2"), "c"); ((TAtom "iw_4.pr.1"), "r"); ((TAtom "iw_4.v0"), "c"); ((TAtom "iw_4.v10"), "r"); ((TAtom "iw_4.v11"), "r"); ((TAtom "iw_4.v7"), "c"); ((TAtom "iw_4.v8"), "r"); ((TAtom "iw_4.v9"), "c"); ((TAtom "iw_5.iw_1.iw_1.iw_1.v0"), "c_in"); ((TAtom "iw_5.iw_1.iw_1.iw_1.v5"), "c_in"); ((TAtom "iw_5.iw_1.iw_1.iw_2.v0"), "c_in"); ((TAtom "iw_5.iw_1.iw_1.iw_2.v5"), "c_in"); ((TAtom "iw_5.iw_1.iw_1.v0"), "x"); ((TAtom "iw_5.iw_1.iw_1.v12"), "msb"); ((TAtom "iw_5.iw_1.iw_1.v3"), "lsb"); ((TAtom "iw_5.iw_1.iw_1.v5"), "msb"); ((TAtom "iw_5.iw_1.iw_1.v6"), "x"); ((TAtom "iw_5.iw_1.iw_1.v7"), "lsb"); ((TAtom "iw_5.iw_1.iw_1.v9"), "x"); ((TAtom "iw_5.iw_1.iw_2.iw_1.v0"), "c_in"); ((TAtom "iw_5.iw_1.iw_2.iw_1.v5"), "c_in"); ((TAtom "iw_5.iw_1.iw_2.iw_2.v0"), "c_in"); ((TAtom "iw_5.iw_1.iw_2.iw_2.v5"), "c_in"); ((TAtom "iw_5.iw_1.iw_2.v0"), "x"); ((TAtom "iw_5.iw_1.iw_2.v12"), "msb"); ((TAtom "iw_5.iw_1.iw_2.v3"), "lsb"); ((TAtom "iw_5.iw_1.iw_2.v5"), "msb"); ((TAtom "iw_5.iw_1.iw_2.v6"), "x"); ((TAtom "iw_5.iw_1.iw_2.v7"), "lsb"); ((TAtom "iw_5.iw_1.iw_2.v9"), "x"); ((TAtom "iw_5.iw_1.v0"), "x1"); ((TAtom "iw_5.iw_1.v2"), "x2"); ((TAtom "iw_5.iw_1.v4"), "x1"); ((TAtom "iw_5.iw_1.v6"), "x1"); ((TAtom "iw_5.iw_1.v7"), "x2"); ((TAtom "iw_5.v0"), "x1"); ((TAtom "iw_5.v2"), "x2"); ((TAtom "iw_5.v4"), "x1"); ((TAtom "iw_5.v5"), "x2"); ((TAtom "iw_6.iw_1.iw_1.iw_1.v0"), "c_in"); ((TAtom "iw_6.iw_1.iw_1.iw_1.v5"), "c_in"); ((TAtom "iw_6.iw_1.iw_1.iw_2.v0"), "c_in"); ((TAtom "iw_6.iw_1.iw_1.iw_2.v5"), "c_in"); ((TAtom "iw_6.iw_1.iw_1.v0"), "x"); ((TAtom "iw_6.iw_1.iw_1.v12"), "msb"); ((TAtom "iw_6.iw_1.iw_1.v3"), "lsb"); ((TAtom "iw_6.iw_1.iw_1.v5"), "msb"); ((TAtom "iw_6.iw_1.iw_1.v6"), "x"); ((TAtom "iw_6.iw_1.iw_1.v7"), "lsb"); ((TAtom "iw_6.iw_1.iw_1.v9"), "x"); ((TAtom "iw_6.iw_1.iw_2.iw_1.v0"), "c_in"); ((TAtom "iw_6.iw_1.iw_2.iw_1.v5"), "c_in"); ((TAtom "iw_6.iw_1.iw_2.iw_2.v0"), "c_in"); ((TAtom "iw_6.iw_1.iw_2.iw_2.v5"), "c_in"); ((TAtom "iw_6.iw_1.iw_2.v0"), "x"); ((TAtom "iw_6.iw_1.iw_2.v12"), "msb"); ((TAtom "iw_6.iw_1.iw_2.v3"), "lsb"); ((TAtom "iw_6.iw_1.iw_2.v5"), "msb"); ((TAtom "iw_6.iw_1.iw_2.v6"), "x"); ((TAtom "iw_6.iw_1.iw_2.v7"), "lsb"); ((TAtom "iw_6.iw_1.iw_2.v9"), "x"); ((TAtom "iw_6.iw_1.v0"), "x1"); ((TAtom "iw_6.iw_1.v2"), "x2"); ((TAtom "iw_6.iw_1.v4"), "x1"); ((TAtom "iw_6.iw_1.v6"), "x1"); ((TAtom "iw_6.iw_1.v7"), "x2"); ((TAtom "iw_6.iw_2.iw_1.iw_1.v0"), "c_in"); ((TAtom "iw_6.iw_2.iw_1.iw_1.v5"), "c_in"); ((TAtom "iw_6.iw_2.iw_1.v0"), "x"); ((TAtom "iw_6.iw_2.iw_1.v11"), "m"); ((TAtom "iw_6.iw_2.iw_1.v3"), "m"); ((TAtom "iw_6.iw_2.iw_1.v4"), "x"); ((TAtom "iw_6.iw_2.iw_1.v5"), "m"); ((TAtom "iw_6.iw_2.iw_1.v7"), "m"); ((TAtom "iw_6.iw_2.iw_1.v9"), "x"); ((TAtom "iw_6.iw_2.iw_2.iw_1.v0"), "c_in"); ((TAtom "iw_6.iw_2.iw_2.iw_1.v5"), "c_in"); ((TAtom "iw_6.iw_2.iw_2.v0"), "x"); ((TAtom "iw_6.iw_2.iw_2.v11"), "m"); ((TAtom "iw_6.iw_2.iw_2.v3"), "m"); ((TAtom "iw_6.iw_2.iw_2.v4"), "x"); ((TAtom "iw_6.iw_2.iw_2.v5"), "m"); ((TAtom "iw_6.iw_2.iw_2.v7"), "m"); ((TAtom "iw_6.iw_2.iw_2.v9"), "x"); ((TAtom "iw_6.iw_2.v0"), "x1"); ((TAtom "iw_6.iw_2.v2"), "x2"); ((TAtom "iw_6.iw_2.v4"), "x1"); ((TAtom "iw_6.iw_2.v6"), "x1"); ((TAtom "iw_6.iw_2.v7"), "x2"); ((TAtom "iw_6.iw_3.iw_1.iw_1.v0"), "__x"); ((TAtom "iw_6.iw_3.iw_1.iw_1.v5"), "__x"); ((TAtom "iw_6.iw_3.iw_1.iw_1.v7"), "__x"); ((TAtom "iw_6.iw_3.iw_1.iw_2.v0"), "__x"); ((TAtom "iw_6.iw_3.iw_1.iw_2.v5"), "__x"); ((TAtom "iw_6.iw_3.iw_1.iw_2.v7"), "__x"); ((TAtom "iw_6.iw_3.iw_1.iw_3.v0"), "__x"); ((TAtom "iw_6.iw_3.iw_1.iw_3.v5"), "__x"); ((TAtom "iw_6.iw_3.iw_1.iw_3.v7"), "__x"); ((TAtom "iw_6.iw_3.iw_1.iw_4.v0"), "__x"); ((TAtom "iw_6.iw_3.iw_1.iw_4.v5"), "__x"); ((TAtom "iw_6.iw_3.iw_1.iw_4.v7"), "__x"); ((TAtom "iw_6.iw_3.iw_1.v0"), "c"); ((TAtom "iw_6.iw_3.iw_1.v12"), "c"); ((TAtom "iw_6.iw_3.iw_1.v18"), "c"); ((TAtom "iw_6.iw_3.iw_1.v21"), "c"); ((TAtom "iw_6.iw_3.iw_1.v6"), "c"); ((TAtom "iw_6.iw_3.iw_2.iw_1.v0"), "__x"); ((TAtom "iw_6.iw_3.iw_2.iw_1.v5"), "__x"); ((TAtom "iw_6.iw_3.iw_2.iw_1.v7"), "__x"); ((TAtom "iw_6.iw_3.iw_2.v0"), "c"); ((TAtom "iw_6.iw_3.iw_2.v2"), "c"); ((TAtom "iw_6.iw_3.pr.1"), "r"); ((TAtom "iw_6.iw_3.v0"), "c"); ((TAtom "iw_6.iw_3.v10"), "r"); ((TAtom "iw_6.iw_3.v11"), "r"); ((TAtom "iw_6.iw_3.v7"), "c"); ((TAtom "iw_6.iw_3.v8"), "r"); ((TAtom "iw_6.iw_3.v9"), "c"); ((TAtom "iw_6.pr.1"), "x1"); ((TAtom "iw_6.v0"), "x1"); ((TAtom "iw_6.v10"), "x1"); ((TAtom "iw_6.v11"), "x1"); ((TAtom "iw_6.v12"), "x2"); ((TAtom "iw_6.v13"), "x1"); ((TAtom "iw_6.v14"), "x1"); ((TAtom "iw_6.v2"), "x2"); ((TAtom "iw_6.v8"), "x1"); ((TAtom "iw_6.v9"), "x2"); ((TAtom "pr.1"), "word_ptr"); ((TAtom "v0"), "str"); ((TAtom "v12"), "word_ptr"); ((TAtom "v14"), "c_in"); ((TAtom "v16"), "repeated_c"); ((TAtom "v18"), "word_ptr"); ((TAtom "v19"), "word"); ((TAtom "v2"), "c_in"); ((TAtom "v21"), "word"); ((TAtom "v22"), "repeated_c"); ((TAtom "v24"), "s_int"); ((TAtom "v25"), "mask"); ((TAtom "v29"), "mask"); ((TAtom "v31"), "str"); ((TAtom "v32"), "mask"); ((TAtom "v40"), "word_ptr"); ((TAtom "v41"), "word_ptr"); ((TAtom "v42"), "word"); ((TAtom "v43"), "word"); ((TAtom "v44"), "repeated_c"); ((TAtom "v48"), "word_ptr"); ((TAtom "v49"), "word"); ((TAtom "v5"), "str"); ((TAtom "v50"), "repeated_c"); ((TAtom "v6"), "s_int"); ((TAtom "v8"), "str")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L37")].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__GI___strchrnul") (code_module strchr_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___GI___strchrnul.

Module fn___GI_strrchr.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("strrchr.c", 27%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("strrchr.c", 30%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "s"); ((TAtom "v2"), "c"); ((TAtom "v4"), "s"); ((TAtom "v5"), "c"); ((TAtom "v6"), "s")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__GI_strrchr") (code_module strchr_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___GI_strrchr.

Module fn___memchr.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("memchr.c", 40%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("memchr.c", 43%nat)); ((TAtom "L6"), ("memchr.c", 44%nat)); ((TAtom "L8"), ("memchr.c", 48%nat)); ((TAtom "iw_2.L5"), ("memchr.c", 36%nat)); ((TAtom "iw_2.L6"), ("memchr.c", 36%nat)); ((TAtom "iw_6.start"), ("../stdlib/stdbit.h", 193%nat)); ((TAtom "iw_6.iw_1.iw_1.L3"), ("../stdlib/stdbit.h", 193%nat)); ((TAtom "iw_6.iw_1.iw_1.L4"), ("../stdlib/stdbit.h", 193%nat)); ((TAtom "L62"), ("memchr.c", 63%nat)); ((TAtom "L63"), ("memchr.c", 63%nat)); ((TAtom "L52"), ("memchr.c", 65%nat)); ((TAtom "L72"), ("memchr.c", 66%nat)); ((TAtom "L74"), ("memchr.c", 68%nat)); ((TAtom "L84"), ("memchr.c", 51%nat)); ((TAtom "iw_7.start"), ("../sysdeps/generic/string-fza.h", 63%nat)); ((TAtom "iw_8.start"), ("../stdlib/stdbit.h", 193%nat)); ((TAtom "iw_8.iw_3.iw_1.iw_1.L3"), ("../stdlib/stdbit.h", 193%nat)); ((TAtom "iw_8.iw_3.iw_1.iw_1.L4"), ("../stdlib/stdbit.h", 193%nat)); ((TAtom "L94"), ("memchr.c", 73%nat)); ((TAtom "iw_9.start"), ("../sysdeps/generic/string-fza.h", 63%nat)); ((TAtom "iw_10.start"), ("../stdlib/stdbit.h", 193%nat)); ((TAtom "iw_10.iw_3.iw_1.iw_1.L3"), ("../stdlib/stdbit.h", 193%nat)); ((TAtom "iw_10.iw_3.iw_1.iw_1.L4"), ("../stdlib/stdbit.h", 193%nat)); ((TAtom "L123"), ("memchr.c", 82%nat)); ((TAtom "L111"), ("memchr.c", 84%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "c_in"); ((TAtom "iw_1.v5"), "c_in"); ((TAtom "iw_10.iw_1.iw_1.iw_1.v0"), "c_in"); ((TAtom "iw_10.iw_1.iw_1.iw_1.v5"), "c_in"); ((TAtom "iw_10.iw_1.iw_1.iw_2.v0"), "c_in"); ((TAtom "iw_10.iw_1.iw_1.iw_2.v5"), "c_in"); ((TAtom "iw_10.iw_1.iw_1.v0"), "x"); ((TAtom "iw_10.iw_1.iw_1.v12"), "msb"); ((TAtom "iw_10.iw_1.iw_1.v3"), "lsb"); ((TAtom "iw_10.iw_1.iw_1.v5"), "msb"); ((TAtom "iw_10.iw_1.iw_1.v6"), "x"); ((TAtom "iw_10.iw_1.iw_1.v7"), "lsb"); ((TAtom "iw_10.iw_1.iw_1.v9"), "x"); ((TAtom "iw_10.iw_1.v0"), "x1"); ((TAtom "iw_10.iw_1.v2"), "x2"); ((TAtom "iw_10.iw_1.v4"), "x1"); ((TAtom "iw_10.iw_1.v5"), "x2"); ((TAtom "iw_10.iw_2.iw_1.iw_1.v0"), "c_in"); ((TAtom "iw_10.iw_2.iw_1.iw_1.v5"), "c_in"); ((TAtom "iw_10.iw_2.iw_1.v0"), "x"); ((TAtom "iw_10.iw_2.iw_1.v11"), "m"); ((TAtom "iw_10.iw_2.iw_1.v3"), "m"); ((TAtom "iw_10.iw_2.iw_1.v4"), "x"); ((TAtom "iw_10.iw_2.iw_1.v5"), "m"); ((TAtom "iw_10.iw_2.iw_1.v7"), "m"); ((TAtom "iw_10.iw_2.iw_1.v9"), "x"); ((TAtom "iw_10.iw_2.v0"), "x1"); ((TAtom "iw_10.iw_2.v2"), "x2"); ((TAtom "iw_10.iw_2.v4"), "x1"); ((TAtom "iw_10.iw_2.v5"), "x2"); ((TAtom "iw_10.iw_3.iw_1.iw_1.v0"), "__x"); ((TAtom "iw_10.iw_3.iw_1.iw_1.v5"), "__x"); ((TAtom "iw_10.iw_3.iw_1.iw_1.v7"), "__x"); ((TAtom "iw_10.iw_3.iw_1.iw_2.v0"), "__x"); ((TAtom "iw_10.iw_3.iw_1.iw_2.v5"), "__x"); ((TAtom "iw_10.iw_3.iw_1.iw_2.v7"), "__x"); ((TAtom "iw_10.iw_3.iw_1.iw_3.v0"), "__x"); ((TAtom "iw_10.iw_3.iw_1.iw_3.v5"), "__x"); ((TAtom "iw_10.iw_3.iw_1.iw_3.v7"), "__x"); ((TAtom "iw_10.iw_3.iw_1.iw_4.v0"), "__x"); ((TAtom "iw_10.iw_3.iw_1.iw_4.v5"), "__x"); ((TAtom "iw_10.iw_3.iw_1.iw_4.v7"), "__x"); ((TAtom "iw_10.iw_3.iw_1.v0"), "c"); ((TAtom "iw_10.iw_3.iw_1.v12"), "c"); ((TAtom "iw_10.iw_3.iw_1.v18"), "c"); ((TAtom "iw_10.iw_3.iw_1.v21"), "c"); ((TAtom "iw_10.iw_3.iw_1.v6"), "c"); ((TAtom "iw_10.iw_3.iw_2.iw_1.v0"), "__x"); ((TAtom "iw_10.iw_3.iw_2.iw_1.v5"), "__x"); ((TAtom "iw_10.iw_3.iw_2.iw_1.v7"), "__x"); ((TAtom "iw_10.iw_3.iw_2.v0"), "c"); ((TAtom "iw_10.iw_3.iw_2.v2"), "c"); ((TAtom "iw_10.iw_3.pr.1"), "r"); ((TAtom "iw_10.iw_3.v0"), "c"); ((TAtom "iw_10.iw_3.v10"), "r"); ((TAtom "iw_10.iw_3.v11"), "r"); ((TAtom "iw_10.iw_3.v7"), "c"); ((TAtom "iw_10.iw_3.v8"), "r"); ((TAtom "iw_10.iw_3.v9"), "c"); ((TAtom "iw_10.pr.1"), "x1"); ((TAtom "iw_10.v0"), "x1"); ((TAtom "iw_10.v10"), "x1"); ((TAtom "iw_10.v11"), "x1"); ((TAtom "iw_10.v12"), "x2"); ((TAtom "iw_10.v13"), "x1"); ((TAtom "iw_10.v14"), "x1"); ((TAtom "iw_10.v2"), "x2"); ((TAtom "iw_10.v8"), "x1"); ((TAtom "iw_10.v9"), "x2"); ((TAtom "iw_2.v0"), "x"); ((TAtom "iw_2.v11"), "x"); ((TAtom "iw_2.v12"), "y"); ((TAtom "iw_2.v2"), "y"); ((TAtom "iw_2.v7"), "y"); ((TAtom "iw_2.v8"), "x"); ((TAtom "iw_3.v0"), "object"); ((TAtom "iw_3.v10"), "ptr"); ((TAtom "iw_3.v11"), "address"); ((TAtom "iw_3.v12"), "ptr"); ((TAtom "iw_3.v13"), "ptr"); ((TAtom "iw_3.v2"), "address"); ((TAtom "iw_3.v5"), "object"); ((TAtom "iw_3.v6"), "ptr"); ((TAtom "iw_3.v7"), "object"); ((TAtom "iw_3.v9"), "ptr"); ((TAtom "iw_4.iw_1.iw_1.v0"), "c_in"); ((TAtom "iw_4.iw_1.iw_1.v5"), "c_in"); ((TAtom "iw_4.iw_1.v0"), "x"); ((TAtom "iw_4.iw_1.v11"), "m"); ((TAtom "iw_4.iw_1.v3"), "m"); ((TAtom "iw_4.iw_1.v4"), "x"); ((TAtom "iw_4.iw_1.v5"), "m"); ((TAtom "iw_4.iw_1.v7"), "m"); ((TAtom "iw_4.iw_1.v9"), "x"); ((TAtom "iw_4.v0"), "x1"); ((TAtom "iw_4.v2"), "x2"); ((TAtom "iw_4.v4"), "x1"); ((TAtom "iw_4.v5"), "x2"); ((TAtom "iw_5.v0"), "word"); ((TAtom "iw_5.v14"), "word"); ((TAtom "iw_5.v15"), "s"); ((TAtom "iw_5.v2"), "s"); ((TAtom "iw_5.v8"), "word"); ((TAtom "iw_5.v9"), "s"); ((TAtom "iw_6.iw_1.iw_1.v0"), "__x"); ((TAtom "iw_6.iw_1.iw_1.v5"), "__x"); ((TAtom "iw_6.iw_1.iw_1.v7"), "__x"); ((TAtom "iw_6.iw_1.iw_2.v0"), "__x"); ((TAtom "iw_6.iw_1.iw_2.v5"), "__x"); ((TAtom "iw_6.iw_1.iw_2.v7"), "__x"); ((TAtom "iw_6.iw_1.iw_3.v0"), "__x"); ((TAtom "iw_6.iw_1.iw_3.v5"), "__x"); ((TAtom "iw_6.iw_1.iw_3.v7"), "__x"); ((TAtom "iw_6.iw_1.iw_4.v0"), "__x"); ((TAtom "iw_6.iw_1.iw_4.v5"), "__x"); ((TAtom "iw_6.iw_1.iw_4.v7"), "__x"); ((TAtom "iw_6.iw_1.v0"), "c"); ((TAtom "iw_6.iw_1.v12"), "c"); ((TAtom "iw_6.iw_1.v18"), "c"); ((TAtom "iw_6.iw_1.v21"), "c"); ((TAtom "iw_6.iw_1.v6"), "c"); ((TAtom "iw_6.iw_2.iw_1.v0"), "__x"); ((TAtom "iw_6.iw_2.iw_1.v5"), "__x"); ((TAtom "iw_6.iw_2.iw_1.v7"), "__x"); ((TAtom "iw_6.iw_2.v0"), "c"); ((TAtom "iw_6.iw_2.v2"), "c"); ((TAtom "iw_6.pr.1"), "r"); ((TAtom "iw_6.v0"), "c"); ((TAtom "iw_6.v10"), "r"); ((TAtom "iw_6.v11"), "r"); ((TAtom "iw_6.v7"), "c"); ((TAtom "iw_6.v8"), "r"); ((TAtom "iw_6.v9"), "c"); ((TAtom "iw_7.iw_1.iw_1.iw_1.v0"), "c_in"); ((TAtom "iw_7.iw_1.iw_1.iw_1.v5"), "c_in"); ((TAtom "iw_7.iw_1.iw_1.iw_2.v0"), "c_in"); ((TAtom "iw_7.iw_1.iw_1.iw_2.v5"), "c_in"); ((TAtom "iw_7.iw_1.iw_1.v0"), "x"); ((TAtom "iw_7.iw_1.iw_1.v12"), "msb"); ((TAtom "iw_7.iw_1.iw_1.v3"), "lsb"); ((TAtom "iw_7.iw_1.iw_1.v5"), "msb"); ((TAtom "iw_7.iw_1.iw_1.v6"), "x"); ((TAtom "iw_7.iw_1.iw_1.v7"), "lsb"); ((TAtom "iw_7.iw_1.iw_1.v9"), "x"); ((TAtom "iw_7.iw_1.v0"), "x1"); ((TAtom "iw_7.iw_1.v2"), "x2"); ((TAtom "iw_7.iw_1.v4"), "x1"); ((TAtom "iw_7.iw_1.v5"), "x2"); ((TAtom "iw_7.v0"), "x1"); ((TAtom "iw_7.v2"), "x2"); ((TAtom "iw_7.v4"), "x1"); ((TAtom "iw_7.v5"), "x2"); ((TAtom "iw_8.iw_1.iw_1.iw_1.v0"), "c_in"); ((TAtom "iw_8.iw_1.iw_1.iw_1.v5"), "c_in"); ((TAtom "iw_8.iw_1.iw_1.iw_2.v0"), "c_in"); ((TAtom "iw_8.iw_1.iw_1.iw_2.v5"), "c_in"); ((TAtom "iw_8.iw_1.iw_1.v0"), "x"); ((TAtom "iw_8.iw_1.iw_1.v12"), "msb"); ((TAtom "iw_8.iw_1.iw_1.v3"), "lsb"); ((TAtom "iw_8.iw_1.iw_1.v5"), "msb"); ((TAtom "iw_8.iw_1.iw_1.v6"), "x"); ((TAtom "iw_8.iw_1.iw_1.v7"), "lsb"); ((TAtom "iw_8.iw_1.iw_1.v9"), "x"); ((TAtom "iw_8.iw_1.v0"), "x1"); ((TAtom "iw_8.iw_1.v2"), "x2"); ((TAtom "iw_8.iw_1.v4"), "x1"); ((TAtom "iw_8.iw_1.v5"), "x2"); ((TAtom "iw_8.iw_2.iw_1.iw_1.v0"), "c_in"); ((TAtom "iw_8.iw_2.iw_1.iw_1.v5"), "c_in"); ((TAtom "iw_8.iw_2.iw_1.v0"), "x"); ((TAtom "iw_8.iw_2.iw_1.v11"), "m"); ((TAtom "iw_8.iw_2.iw_1.v3"), "m"); ((TAtom "iw_8.iw_2.iw_1.v4"), "x"); ((TAtom "iw_8.iw_2.iw_1.v5"), "m"); ((TAtom "iw_8.iw_2.iw_1.v7"), "m"); ((TAtom "iw_8.iw_2.iw_1.v9"), "x"); ((TAtom "iw_8.iw_2.v0"), "x1"); ((TAtom "iw_8.iw_2.v2"), "x2"); ((TAtom "iw_8.iw_2.v4"), "x1"); ((TAtom "iw_8.iw_2.v5"), "x2"); ((TAtom "iw_8.iw_3.iw_1.iw_1.v0"), "__x"); ((TAtom "iw_8.iw_3.iw_1.iw_1.v5"), "__x"); ((TAtom "iw_8.iw_3.iw_1.iw_1.v7"), "__x"); ((TAtom "iw_8.iw_3.iw_1.iw_2.v0"), "__x"); ((TAtom "iw_8.iw_3.iw_1.iw_2.v5"), "__x"); ((TAtom "iw_8.iw_3.iw_1.iw_2.v7"), "__x"); ((TAtom "iw_8.iw_3.iw_1.iw_3.v0"), "__x"); ((TAtom "iw_8.iw_3.iw_1.iw_3.v5"), "__x"); ((TAtom "iw_8.iw_3.iw_1.iw_3.v7"), "__x"); ((TAtom "iw_8.iw_3.iw_1.iw_4.v0"), "__x"); ((TAtom "iw_8.iw_3.iw_1.iw_4.v5"), "__x"); ((TAtom "iw_8.iw_3.iw_1.iw_4.v7"), "__x"); ((TAtom "iw_8.iw_3.iw_1.v0"), "c"); ((TAtom "iw_8.iw_3.iw_1.v12"), "c"); ((TAtom "iw_8.iw_3.iw_1.v18"), "c"); ((TAtom "iw_8.iw_3.iw_1.v21"), "c"); ((TAtom "iw_8.iw_3.iw_1.v6"), "c"); ((TAtom "iw_8.iw_3.iw_2.iw_1.v0"), "__x"); ((TAtom "iw_8.iw_3.iw_2.iw_1.v5"), "__x"); ((TAtom "iw_8.iw_3.iw_2.iw_1.v7"), "__x"); ((TAtom "iw_8.iw_3.iw_2.v0"), "c"); ((TAtom "iw_8.iw_3.iw_2.v2"), "c"); ((TAtom "iw_8.iw_3.pr.1"), "r"); ((TAtom "iw_8.iw_3.v0"), "c"); ((TAtom "iw_8.iw_3.v10"), "r"); ((TAtom "iw_8.iw_3.v11"), "r"); ((TAtom "iw_8.iw_3.v7"), "c"); ((TAtom "iw_8.iw_3.v8"), "r"); ((TAtom "iw_8.iw_3.v9"), "c"); ((TAtom "iw_8.pr.1"), "x1"); ((TAtom "iw_8.v0"), "x1"); ((TAtom "iw_8.v10"), "x1"); ((TAtom "iw_8.v11"), "x1"); ((TAtom "iw_8.v12"), "x2"); ((TAtom "iw_8.v13"), "x1"); ((TAtom "iw_8.v14"), "x1"); ((TAtom "iw_8.v2"), "x2"); ((TAtom "iw_8.v8"), "x1"); ((TAtom "iw_8.v9"), "x2"); ((TAtom "iw_9.iw_1.iw_1.iw_1.v0"), "c_in"); ((TAtom "iw_9.iw_1.iw_1.iw_1.v5"), "c_in"); ((TAtom "iw_9.iw_1.iw_1.iw_2.v0"), "c_in"); ((TAtom "iw_9.iw_1.iw_1.iw_2.v5"), "c_in"); ((TAtom "iw_9.iw_1.iw_1.v0"), "x"); ((TAtom "iw_9.iw_1.iw_1.v12"), "msb"); ((TAtom "iw_9.iw_1.iw_1.v3"), "lsb"); ((TAtom "iw_9.iw_1.iw_1.v5"), "msb"); ((TAtom "iw_9.iw_1.iw_1.v6"), "x"); ((TAtom "iw_9.iw_1.iw_1.v7"), "lsb"); ((TAtom "iw_9.iw_1.iw_1.v9"), "x"); ((TAtom "iw_9.iw_1.v0"), "x1"); ((TAtom "iw_9.iw_1.v2"), "x2"); ((TAtom "iw_9.iw_1.v4"), "x1"); ((TAtom "iw_9.iw_1.v5"), "x2"); ((TAtom "iw_9.v0"), "x1"); ((TAtom "iw_9.v2"), "x2"); ((TAtom "iw_9.v4"), "x1"); ((TAtom "iw_9.v5"), "x2"); ((TAtom "pr.1"), "word_ptr"); ((TAtom "pr.2"), "word"); ((TAtom "v0"), "s"); ((TAtom "v100"), "word"); ((TAtom "v101"), "repeated_c"); ((TAtom "v106"), "word_ptr"); ((TAtom "v107"), "word_ptr"); ((TAtom "v108"), "word"); ((TAtom "v112"), "word"); ((TAtom "v113"), "repeated_c"); ((TAtom "v117"), "word_ptr"); ((TAtom "v118"), "word"); ((TAtom "v119"), "repeated_c"); ((TAtom "v122"), "ret"); ((TAtom "v126"), "ret"); ((TAtom "v127"), "lbyte"); ((TAtom "v131"), "ret"); ((TAtom "v15"), "s"); ((TAtom "v19"), "word_ptr"); ((TAtom "v2"), "c_in"); ((TAtom "v21"), "s"); ((TAtom "v22"), "s_int"); ((TAtom "v24"), "word_ptr"); ((TAtom "v25"), "word"); ((TAtom "v27"), "c_in"); ((TAtom "v29"), "repeated_c"); ((TAtom "v31"), "s"); ((TAtom "v32"), "s_int"); ((TAtom "v33"), "n"); ((TAtom "v37"), "lbyte"); ((TAtom "v39"), "lbyte"); ((TAtom "v4"), "n"); ((TAtom "v43"), "lword"); ((TAtom "v45"), "word"); ((TAtom "v46"), "repeated_c"); ((TAtom "v48"), "s_int"); ((TAtom "v49"), "mask"); ((TAtom "v53"), "mask"); ((TAtom "v56"), "s"); ((TAtom "v57"), "mask"); ((TAtom "v60"), "ret"); ((TAtom "v64"), "ret"); ((TAtom "v65"), "lbyte"); ((TAtom "v69"), "ret"); ((TAtom "v75"), "word_ptr"); ((TAtom "v76"), "lword"); ((TAtom "v81"), "word_ptr"); ((TAtom "v82"), "word_ptr"); ((TAtom "v83"), "word"); ((TAtom "v87"), "word_ptr"); ((TAtom "v88"), "lword"); ((TAtom "v9"), "n"); ((TAtom "v95"), "word"); ((TAtom "v96"), "repeated_c"); ((TAtom "v99"), "word_ptr")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L84")].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__memchr") (code_module strchr_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___memchr.

Module fn___GI___strnlen.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("strnlen.c", 27%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("strnlen.c", 30%nat)); ((TAtom "L8"), ("strnlen.c", 31%nat)); ((TAtom "L10"), ("strnlen.c", 31%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "str"); ((TAtom "v11"), "found"); ((TAtom "v14"), "found"); ((TAtom "v15"), "str"); ((TAtom "v19"), "maxlen"); ((TAtom "v2"), "maxlen"); ((TAtom "v5"), "str"); ((TAtom "v6"), "maxlen"); ((TAtom "v7"), "found")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__GI___strnlen") (code_module strchr_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___GI___strnlen.

End StrchrSrc.
