(** These tables connect checked function bodies to C declarations and source lines.
    Names and locations support annotations and diagnostic messages, not soundness premises.
    Natural-loop headers provide optional cuts for symbolic execution; any cut list is sound.
    Computation checks that every recorded block label belongs to the decoded function.
    The code generator reproduces this file from the capture; do not edit it. *)

From Stdlib Require Import String List Bool NArith.
From Glibc Require Import CodePrelude.
Import ListNotations.
Open Scope string_scope.


From Glibc Require Import StrchrCode.
Module StrchrSrc.

Definition file_0 : string := "../stdlib/stdbit.h".

Definition file_1 : string := "../sysdeps/generic/string-fza.h".

Definition file_2 : string := "memchr.c".

Definition file_3 : string := "strchr.c".

Definition file_4 : string := "strchrnul.c".

Definition file_5 : string := "strnlen.c".

Definition file_6 : string := "strrchr.c".

Module fn___GI_strchr.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_3, 28%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_3, 31%N)); ((TAtom "L9"), (file_3, 32%N)); ((TAtom "L10"), (file_3, 32%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "s"); ((TAtom "v11"), "r"); ((TAtom "v13"), "c_in"); ((TAtom "v16"), "r"); ((TAtom "v2"), "c_in"); ((TAtom "v5"), "s"); ((TAtom "v6"), "c_in"); ((TAtom "v7"), "r")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

End fn___GI_strchr.

Module fn___GI___strchrnul.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_4, 33%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_4, 37%N)); ((TAtom "iw_4.start"), (file_0, 193%N)); ((TAtom "iw_4.iw_1.iw_1.L3"), (file_0, 193%N)); ((TAtom "iw_4.iw_1.iw_1.L4"), (file_0, 193%N)); ((TAtom "L37"), (file_4, 38%N)); ((TAtom "iw_6.start"), (file_0, 193%N)); ((TAtom "iw_6.iw_3.iw_1.iw_1.L3"), (file_0, 193%N)); ((TAtom "iw_6.iw_3.iw_1.iw_1.L4"), (file_0, 193%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "c_in"); ((TAtom "iw_1.v5"), "c_in"); ((TAtom "iw_2.iw_1.iw_1.v0"), "c_in"); ((TAtom "iw_2.iw_1.iw_1.v5"), "c_in"); ((TAtom "iw_2.iw_1.v0"), "x"); ((TAtom "iw_2.iw_1.v11"), "m"); ((TAtom "iw_2.iw_1.v3"), "m"); ((TAtom "iw_2.iw_1.v4"), "x"); ((TAtom "iw_2.iw_1.v5"), "m"); ((TAtom "iw_2.iw_1.v7"), "m"); ((TAtom "iw_2.iw_1.v9"), "x"); ((TAtom "iw_2.iw_2.iw_1.v0"), "c_in"); ((TAtom "iw_2.iw_2.iw_1.v5"), "c_in"); ((TAtom "iw_2.iw_2.v0"), "x"); ((TAtom "iw_2.iw_2.v11"), "m"); ((TAtom "iw_2.iw_2.v3"), "m"); ((TAtom "iw_2.iw_2.v4"), "x"); ((TAtom "iw_2.iw_2.v5"), "m"); ((TAtom "iw_2.iw_2.v7"), "m"); ((TAtom "iw_2.iw_2.v9"), "x"); ((TAtom "iw_2.v0"), "x1"); ((TAtom "iw_2.v2"), "x2"); ((TAtom "iw_2.v4"), "x1"); ((TAtom "iw_2.v6"), "x1"); ((TAtom "iw_2.v7"), "x2"); ((TAtom "iw_3.v0"), "word"); ((TAtom "iw_3.v14"), "word"); ((TAtom "iw_3.v15"), "s"); ((TAtom "iw_3.v2"), "s"); ((TAtom "iw_3.v8"), "word"); ((TAtom "iw_3.v9"), "s"); ((TAtom "iw_4.iw_1.iw_1.v0"), "__x"); ((TAtom "iw_4.iw_1.iw_1.v5"), "__x"); ((TAtom "iw_4.iw_1.iw_1.v7"), "__x"); ((TAtom "iw_4.iw_1.iw_2.v0"), "__x"); ((TAtom "iw_4.iw_1.iw_2.v5"), "__x"); ((TAtom "iw_4.iw_1.iw_2.v7"), "__x"); ((TAtom "iw_4.iw_1.iw_3.v0"), "__x"); ((TAtom "iw_4.iw_1.iw_3.v5"), "__x"); ((TAtom "iw_4.iw_1.iw_3.v7"), "__x"); ((TAtom "iw_4.iw_1.iw_4.v0"), "__x"); ((TAtom "iw_4.iw_1.iw_4.v5"), "__x"); ((TAtom "iw_4.iw_1.iw_4.v7"), "__x"); ((TAtom "iw_4.iw_1.v0"), "c"); ((TAtom "iw_4.iw_1.v12"), "c"); ((TAtom "iw_4.iw_1.v18"), "c"); ((TAtom "iw_4.iw_1.v21"), "c"); ((TAtom "iw_4.iw_1.v6"), "c"); ((TAtom "iw_4.iw_2.iw_1.v0"), "__x"); ((TAtom "iw_4.iw_2.iw_1.v5"), "__x"); ((TAtom "iw_4.iw_2.iw_1.v7"), "__x"); ((TAtom "iw_4.iw_2.v0"), "c"); ((TAtom "iw_4.iw_2.v2"), "c"); ((TAtom "iw_4.pr.1"), "r"); ((TAtom "iw_4.v0"), "c"); ((TAtom "iw_4.v10"), "r"); ((TAtom "iw_4.v11"), "r"); ((TAtom "iw_4.v7"), "c"); ((TAtom "iw_4.v8"), "r"); ((TAtom "iw_4.v9"), "c"); ((TAtom "iw_5.iw_1.iw_1.iw_1.v0"), "c_in"); ((TAtom "iw_5.iw_1.iw_1.iw_1.v5"), "c_in"); ((TAtom "iw_5.iw_1.iw_1.iw_2.v0"), "c_in"); ((TAtom "iw_5.iw_1.iw_1.iw_2.v5"), "c_in"); ((TAtom "iw_5.iw_1.iw_1.v0"), "x"); ((TAtom "iw_5.iw_1.iw_1.v12"), "msb"); ((TAtom "iw_5.iw_1.iw_1.v3"), "lsb"); ((TAtom "iw_5.iw_1.iw_1.v5"), "msb"); ((TAtom "iw_5.iw_1.iw_1.v6"), "x"); ((TAtom "iw_5.iw_1.iw_1.v7"), "lsb"); ((TAtom "iw_5.iw_1.iw_1.v9"), "x"); ((TAtom "iw_5.iw_1.iw_2.iw_1.v0"), "c_in"); ((TAtom "iw_5.iw_1.iw_2.iw_1.v5"), "c_in"); ((TAtom "iw_5.iw_1.iw_2.iw_2.v0"), "c_in"); ((TAtom "iw_5.iw_1.iw_2.iw_2.v5"), "c_in"); ((TAtom "iw_5.iw_1.iw_2.v0"), "x"); ((TAtom "iw_5.iw_1.iw_2.v12"), "msb"); ((TAtom "iw_5.iw_1.iw_2.v3"), "lsb"); ((TAtom "iw_5.iw_1.iw_2.v5"), "msb"); ((TAtom "iw_5.iw_1.iw_2.v6"), "x"); ((TAtom "iw_5.iw_1.iw_2.v7"), "lsb"); ((TAtom "iw_5.iw_1.iw_2.v9"), "x"); ((TAtom "iw_5.iw_1.v0"), "x1"); ((TAtom "iw_5.iw_1.v2"), "x2"); ((TAtom "iw_5.iw_1.v4"), "x1"); ((TAtom "iw_5.iw_1.v6"), "x1"); ((TAtom "iw_5.iw_1.v7"), "x2"); ((TAtom "iw_5.v0"), "x1"); ((TAtom "iw_5.v2"), "x2"); ((TAtom "iw_5.v4"), "x1"); ((TAtom "iw_5.v5"), "x2"); ((TAtom "iw_6.iw_1.iw_1.iw_1.v0"), "c_in"); ((TAtom "iw_6.iw_1.iw_1.iw_1.v5"), "c_in"); ((TAtom "iw_6.iw_1.iw_1.iw_2.v0"), "c_in"); ((TAtom "iw_6.iw_1.iw_1.iw_2.v5"), "c_in"); ((TAtom "iw_6.iw_1.iw_1.v0"), "x"); ((TAtom "iw_6.iw_1.iw_1.v12"), "msb"); ((TAtom "iw_6.iw_1.iw_1.v3"), "lsb"); ((TAtom "iw_6.iw_1.iw_1.v5"), "msb"); ((TAtom "iw_6.iw_1.iw_1.v6"), "x"); ((TAtom "iw_6.iw_1.iw_1.v7"), "lsb"); ((TAtom "iw_6.iw_1.iw_1.v9"), "x"); ((TAtom "iw_6.iw_1.iw_2.iw_1.v0"), "c_in"); ((TAtom "iw_6.iw_1.iw_2.iw_1.v5"), "c_in"); ((TAtom "iw_6.iw_1.iw_2.iw_2.v0"), "c_in"); ((TAtom "iw_6.iw_1.iw_2.iw_2.v5"), "c_in"); ((TAtom "iw_6.iw_1.iw_2.v0"), "x"); ((TAtom "iw_6.iw_1.iw_2.v12"), "msb"); ((TAtom "iw_6.iw_1.iw_2.v3"), "lsb"); ((TAtom "iw_6.iw_1.iw_2.v5"), "msb"); ((TAtom "iw_6.iw_1.iw_2.v6"), "x"); ((TAtom "iw_6.iw_1.iw_2.v7"), "lsb"); ((TAtom "iw_6.iw_1.iw_2.v9"), "x"); ((TAtom "iw_6.iw_1.v0"), "x1"); ((TAtom "iw_6.iw_1.v2"), "x2"); ((TAtom "iw_6.iw_1.v4"), "x1"); ((TAtom "iw_6.iw_1.v6"), "x1"); ((TAtom "iw_6.iw_1.v7"), "x2"); ((TAtom "iw_6.iw_2.iw_1.iw_1.v0"), "c_in"); ((TAtom "iw_6.iw_2.iw_1.iw_1.v5"), "c_in"); ((TAtom "iw_6.iw_2.iw_1.v0"), "x"); ((TAtom "iw_6.iw_2.iw_1.v11"), "m"); ((TAtom "iw_6.iw_2.iw_1.v3"), "m"); ((TAtom "iw_6.iw_2.iw_1.v4"), "x"); ((TAtom "iw_6.iw_2.iw_1.v5"), "m"); ((TAtom "iw_6.iw_2.iw_1.v7"), "m"); ((TAtom "iw_6.iw_2.iw_1.v9"), "x"); ((TAtom "iw_6.iw_2.iw_2.iw_1.v0"), "c_in"); ((TAtom "iw_6.iw_2.iw_2.iw_1.v5"), "c_in"); ((TAtom "iw_6.iw_2.iw_2.v0"), "x"); ((TAtom "iw_6.iw_2.iw_2.v11"), "m"); ((TAtom "iw_6.iw_2.iw_2.v3"), "m"); ((TAtom "iw_6.iw_2.iw_2.v4"), "x"); ((TAtom "iw_6.iw_2.iw_2.v5"), "m"); ((TAtom "iw_6.iw_2.iw_2.v7"), "m"); ((TAtom "iw_6.iw_2.iw_2.v9"), "x"); ((TAtom "iw_6.iw_2.v0"), "x1"); ((TAtom "iw_6.iw_2.v2"), "x2"); ((TAtom "iw_6.iw_2.v4"), "x1"); ((TAtom "iw_6.iw_2.v6"), "x1"); ((TAtom "iw_6.iw_2.v7"), "x2"); ((TAtom "iw_6.iw_3.iw_1.iw_1.v0"), "__x"); ((TAtom "iw_6.iw_3.iw_1.iw_1.v5"), "__x"); ((TAtom "iw_6.iw_3.iw_1.iw_1.v7"), "__x"); ((TAtom "iw_6.iw_3.iw_1.iw_2.v0"), "__x"); ((TAtom "iw_6.iw_3.iw_1.iw_2.v5"), "__x"); ((TAtom "iw_6.iw_3.iw_1.iw_2.v7"), "__x"); ((TAtom "iw_6.iw_3.iw_1.iw_3.v0"), "__x"); ((TAtom "iw_6.iw_3.iw_1.iw_3.v5"), "__x"); ((TAtom "iw_6.iw_3.iw_1.iw_3.v7"), "__x"); ((TAtom "iw_6.iw_3.iw_1.iw_4.v0"), "__x"); ((TAtom "iw_6.iw_3.iw_1.iw_4.v5"), "__x"); ((TAtom "iw_6.iw_3.iw_1.iw_4.v7"), "__x"); ((TAtom "iw_6.iw_3.iw_1.v0"), "c"); ((TAtom "iw_6.iw_3.iw_1.v12"), "c"); ((TAtom "iw_6.iw_3.iw_1.v18"), "c"); ((TAtom "iw_6.iw_3.iw_1.v21"), "c"); ((TAtom "iw_6.iw_3.iw_1.v6"), "c"); ((TAtom "iw_6.iw_3.iw_2.iw_1.v0"), "__x"); ((TAtom "iw_6.iw_3.iw_2.iw_1.v5"), "__x"); ((TAtom "iw_6.iw_3.iw_2.iw_1.v7"), "__x"); ((TAtom "iw_6.iw_3.iw_2.v0"), "c"); ((TAtom "iw_6.iw_3.iw_2.v2"), "c"); ((TAtom "iw_6.iw_3.pr.1"), "r"); ((TAtom "iw_6.iw_3.v0"), "c"); ((TAtom "iw_6.iw_3.v10"), "r"); ((TAtom "iw_6.iw_3.v11"), "r"); ((TAtom "iw_6.iw_3.v7"), "c"); ((TAtom "iw_6.iw_3.v8"), "r"); ((TAtom "iw_6.iw_3.v9"), "c"); ((TAtom "iw_6.pr.1"), "x1"); ((TAtom "iw_6.v0"), "x1"); ((TAtom "iw_6.v10"), "x1"); ((TAtom "iw_6.v11"), "x1"); ((TAtom "iw_6.v12"), "x2"); ((TAtom "iw_6.v13"), "x1"); ((TAtom "iw_6.v14"), "x1"); ((TAtom "iw_6.v2"), "x2"); ((TAtom "iw_6.v8"), "x1"); ((TAtom "iw_6.v9"), "x2"); ((TAtom "pr.1"), "word_ptr"); ((TAtom "v0"), "str"); ((TAtom "v12"), "word_ptr"); ((TAtom "v14"), "c_in"); ((TAtom "v16"), "repeated_c"); ((TAtom "v18"), "word_ptr"); ((TAtom "v19"), "word"); ((TAtom "v2"), "c_in"); ((TAtom "v21"), "word"); ((TAtom "v22"), "repeated_c"); ((TAtom "v24"), "s_int"); ((TAtom "v25"), "mask"); ((TAtom "v29"), "mask"); ((TAtom "v31"), "str"); ((TAtom "v32"), "mask"); ((TAtom "v40"), "word_ptr"); ((TAtom "v41"), "word_ptr"); ((TAtom "v42"), "word"); ((TAtom "v43"), "word"); ((TAtom "v44"), "repeated_c"); ((TAtom "v48"), "word_ptr"); ((TAtom "v49"), "word"); ((TAtom "v5"), "str"); ((TAtom "v50"), "repeated_c"); ((TAtom "v6"), "s_int"); ((TAtom "v8"), "str")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L37")].

End fn___GI___strchrnul.

Module fn___GI_strrchr.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_6, 27%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_6, 30%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "s"); ((TAtom "v2"), "c"); ((TAtom "v4"), "s"); ((TAtom "v5"), "c"); ((TAtom "v6"), "s")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

End fn___GI_strrchr.

Module fn___memchr.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_2, 40%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_2, 43%N)); ((TAtom "L6"), (file_2, 44%N)); ((TAtom "L8"), (file_2, 48%N)); ((TAtom "iw_2.L5"), (file_2, 36%N)); ((TAtom "iw_2.L6"), (file_2, 36%N)); ((TAtom "iw_6.start"), (file_0, 193%N)); ((TAtom "iw_6.iw_1.iw_1.L3"), (file_0, 193%N)); ((TAtom "iw_6.iw_1.iw_1.L4"), (file_0, 193%N)); ((TAtom "L62"), (file_2, 63%N)); ((TAtom "L63"), (file_2, 63%N)); ((TAtom "L52"), (file_2, 65%N)); ((TAtom "L72"), (file_2, 66%N)); ((TAtom "L74"), (file_2, 68%N)); ((TAtom "L84"), (file_2, 51%N)); ((TAtom "iw_7.start"), (file_1, 63%N)); ((TAtom "iw_8.start"), (file_0, 193%N)); ((TAtom "iw_8.iw_3.iw_1.iw_1.L3"), (file_0, 193%N)); ((TAtom "iw_8.iw_3.iw_1.iw_1.L4"), (file_0, 193%N)); ((TAtom "L94"), (file_2, 73%N)); ((TAtom "iw_9.start"), (file_1, 63%N)); ((TAtom "iw_10.start"), (file_0, 193%N)); ((TAtom "iw_10.iw_3.iw_1.iw_1.L3"), (file_0, 193%N)); ((TAtom "iw_10.iw_3.iw_1.iw_1.L4"), (file_0, 193%N)); ((TAtom "L123"), (file_2, 82%N)); ((TAtom "L111"), (file_2, 84%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "c_in"); ((TAtom "iw_1.v5"), "c_in"); ((TAtom "iw_10.iw_1.iw_1.iw_1.v0"), "c_in"); ((TAtom "iw_10.iw_1.iw_1.iw_1.v5"), "c_in"); ((TAtom "iw_10.iw_1.iw_1.iw_2.v0"), "c_in"); ((TAtom "iw_10.iw_1.iw_1.iw_2.v5"), "c_in"); ((TAtom "iw_10.iw_1.iw_1.v0"), "x"); ((TAtom "iw_10.iw_1.iw_1.v12"), "msb"); ((TAtom "iw_10.iw_1.iw_1.v3"), "lsb"); ((TAtom "iw_10.iw_1.iw_1.v5"), "msb"); ((TAtom "iw_10.iw_1.iw_1.v6"), "x"); ((TAtom "iw_10.iw_1.iw_1.v7"), "lsb"); ((TAtom "iw_10.iw_1.iw_1.v9"), "x"); ((TAtom "iw_10.iw_1.v0"), "x1"); ((TAtom "iw_10.iw_1.v2"), "x2"); ((TAtom "iw_10.iw_1.v4"), "x1"); ((TAtom "iw_10.iw_1.v5"), "x2"); ((TAtom "iw_10.iw_2.iw_1.iw_1.v0"), "c_in"); ((TAtom "iw_10.iw_2.iw_1.iw_1.v5"), "c_in"); ((TAtom "iw_10.iw_2.iw_1.v0"), "x"); ((TAtom "iw_10.iw_2.iw_1.v11"), "m"); ((TAtom "iw_10.iw_2.iw_1.v3"), "m"); ((TAtom "iw_10.iw_2.iw_1.v4"), "x"); ((TAtom "iw_10.iw_2.iw_1.v5"), "m"); ((TAtom "iw_10.iw_2.iw_1.v7"), "m"); ((TAtom "iw_10.iw_2.iw_1.v9"), "x"); ((TAtom "iw_10.iw_2.v0"), "x1"); ((TAtom "iw_10.iw_2.v2"), "x2"); ((TAtom "iw_10.iw_2.v4"), "x1"); ((TAtom "iw_10.iw_2.v5"), "x2"); ((TAtom "iw_10.iw_3.iw_1.iw_1.v0"), "__x"); ((TAtom "iw_10.iw_3.iw_1.iw_1.v5"), "__x"); ((TAtom "iw_10.iw_3.iw_1.iw_1.v7"), "__x"); ((TAtom "iw_10.iw_3.iw_1.iw_2.v0"), "__x"); ((TAtom "iw_10.iw_3.iw_1.iw_2.v5"), "__x"); ((TAtom "iw_10.iw_3.iw_1.iw_2.v7"), "__x"); ((TAtom "iw_10.iw_3.iw_1.iw_3.v0"), "__x"); ((TAtom "iw_10.iw_3.iw_1.iw_3.v5"), "__x"); ((TAtom "iw_10.iw_3.iw_1.iw_3.v7"), "__x"); ((TAtom "iw_10.iw_3.iw_1.iw_4.v0"), "__x"); ((TAtom "iw_10.iw_3.iw_1.iw_4.v5"), "__x"); ((TAtom "iw_10.iw_3.iw_1.iw_4.v7"), "__x"); ((TAtom "iw_10.iw_3.iw_1.v0"), "c"); ((TAtom "iw_10.iw_3.iw_1.v12"), "c"); ((TAtom "iw_10.iw_3.iw_1.v18"), "c"); ((TAtom "iw_10.iw_3.iw_1.v21"), "c"); ((TAtom "iw_10.iw_3.iw_1.v6"), "c"); ((TAtom "iw_10.iw_3.iw_2.iw_1.v0"), "__x"); ((TAtom "iw_10.iw_3.iw_2.iw_1.v5"), "__x"); ((TAtom "iw_10.iw_3.iw_2.iw_1.v7"), "__x"); ((TAtom "iw_10.iw_3.iw_2.v0"), "c"); ((TAtom "iw_10.iw_3.iw_2.v2"), "c"); ((TAtom "iw_10.iw_3.pr.1"), "r"); ((TAtom "iw_10.iw_3.v0"), "c"); ((TAtom "iw_10.iw_3.v10"), "r"); ((TAtom "iw_10.iw_3.v11"), "r"); ((TAtom "iw_10.iw_3.v7"), "c"); ((TAtom "iw_10.iw_3.v8"), "r"); ((TAtom "iw_10.iw_3.v9"), "c"); ((TAtom "iw_10.pr.1"), "x1"); ((TAtom "iw_10.v0"), "x1"); ((TAtom "iw_10.v10"), "x1"); ((TAtom "iw_10.v11"), "x1"); ((TAtom "iw_10.v12"), "x2"); ((TAtom "iw_10.v13"), "x1"); ((TAtom "iw_10.v14"), "x1"); ((TAtom "iw_10.v2"), "x2"); ((TAtom "iw_10.v8"), "x1"); ((TAtom "iw_10.v9"), "x2"); ((TAtom "iw_2.v0"), "x"); ((TAtom "iw_2.v11"), "x"); ((TAtom "iw_2.v12"), "y"); ((TAtom "iw_2.v2"), "y"); ((TAtom "iw_2.v7"), "y"); ((TAtom "iw_2.v8"), "x"); ((TAtom "iw_3.v0"), "object"); ((TAtom "iw_3.v10"), "ptr"); ((TAtom "iw_3.v11"), "address"); ((TAtom "iw_3.v12"), "ptr"); ((TAtom "iw_3.v13"), "ptr"); ((TAtom "iw_3.v2"), "address"); ((TAtom "iw_3.v5"), "object"); ((TAtom "iw_3.v6"), "ptr"); ((TAtom "iw_3.v7"), "object"); ((TAtom "iw_3.v9"), "ptr"); ((TAtom "iw_4.iw_1.iw_1.v0"), "c_in"); ((TAtom "iw_4.iw_1.iw_1.v5"), "c_in"); ((TAtom "iw_4.iw_1.v0"), "x"); ((TAtom "iw_4.iw_1.v11"), "m"); ((TAtom "iw_4.iw_1.v3"), "m"); ((TAtom "iw_4.iw_1.v4"), "x"); ((TAtom "iw_4.iw_1.v5"), "m"); ((TAtom "iw_4.iw_1.v7"), "m"); ((TAtom "iw_4.iw_1.v9"), "x"); ((TAtom "iw_4.v0"), "x1"); ((TAtom "iw_4.v2"), "x2"); ((TAtom "iw_4.v4"), "x1"); ((TAtom "iw_4.v5"), "x2"); ((TAtom "iw_5.v0"), "word"); ((TAtom "iw_5.v14"), "word"); ((TAtom "iw_5.v15"), "s"); ((TAtom "iw_5.v2"), "s"); ((TAtom "iw_5.v8"), "word"); ((TAtom "iw_5.v9"), "s"); ((TAtom "iw_6.iw_1.iw_1.v0"), "__x"); ((TAtom "iw_6.iw_1.iw_1.v5"), "__x"); ((TAtom "iw_6.iw_1.iw_1.v7"), "__x"); ((TAtom "iw_6.iw_1.iw_2.v0"), "__x"); ((TAtom "iw_6.iw_1.iw_2.v5"), "__x"); ((TAtom "iw_6.iw_1.iw_2.v7"), "__x"); ((TAtom "iw_6.iw_1.iw_3.v0"), "__x"); ((TAtom "iw_6.iw_1.iw_3.v5"), "__x"); ((TAtom "iw_6.iw_1.iw_3.v7"), "__x"); ((TAtom "iw_6.iw_1.iw_4.v0"), "__x"); ((TAtom "iw_6.iw_1.iw_4.v5"), "__x"); ((TAtom "iw_6.iw_1.iw_4.v7"), "__x"); ((TAtom "iw_6.iw_1.v0"), "c"); ((TAtom "iw_6.iw_1.v12"), "c"); ((TAtom "iw_6.iw_1.v18"), "c"); ((TAtom "iw_6.iw_1.v21"), "c"); ((TAtom "iw_6.iw_1.v6"), "c"); ((TAtom "iw_6.iw_2.iw_1.v0"), "__x"); ((TAtom "iw_6.iw_2.iw_1.v5"), "__x"); ((TAtom "iw_6.iw_2.iw_1.v7"), "__x"); ((TAtom "iw_6.iw_2.v0"), "c"); ((TAtom "iw_6.iw_2.v2"), "c"); ((TAtom "iw_6.pr.1"), "r"); ((TAtom "iw_6.v0"), "c"); ((TAtom "iw_6.v10"), "r"); ((TAtom "iw_6.v11"), "r"); ((TAtom "iw_6.v7"), "c"); ((TAtom "iw_6.v8"), "r"); ((TAtom "iw_6.v9"), "c"); ((TAtom "iw_7.iw_1.iw_1.iw_1.v0"), "c_in"); ((TAtom "iw_7.iw_1.iw_1.iw_1.v5"), "c_in"); ((TAtom "iw_7.iw_1.iw_1.iw_2.v0"), "c_in"); ((TAtom "iw_7.iw_1.iw_1.iw_2.v5"), "c_in"); ((TAtom "iw_7.iw_1.iw_1.v0"), "x"); ((TAtom "iw_7.iw_1.iw_1.v12"), "msb"); ((TAtom "iw_7.iw_1.iw_1.v3"), "lsb"); ((TAtom "iw_7.iw_1.iw_1.v5"), "msb"); ((TAtom "iw_7.iw_1.iw_1.v6"), "x"); ((TAtom "iw_7.iw_1.iw_1.v7"), "lsb"); ((TAtom "iw_7.iw_1.iw_1.v9"), "x"); ((TAtom "iw_7.iw_1.v0"), "x1"); ((TAtom "iw_7.iw_1.v2"), "x2"); ((TAtom "iw_7.iw_1.v4"), "x1"); ((TAtom "iw_7.iw_1.v5"), "x2"); ((TAtom "iw_7.v0"), "x1"); ((TAtom "iw_7.v2"), "x2"); ((TAtom "iw_7.v4"), "x1"); ((TAtom "iw_7.v5"), "x2"); ((TAtom "iw_8.iw_1.iw_1.iw_1.v0"), "c_in"); ((TAtom "iw_8.iw_1.iw_1.iw_1.v5"), "c_in"); ((TAtom "iw_8.iw_1.iw_1.iw_2.v0"), "c_in"); ((TAtom "iw_8.iw_1.iw_1.iw_2.v5"), "c_in"); ((TAtom "iw_8.iw_1.iw_1.v0"), "x"); ((TAtom "iw_8.iw_1.iw_1.v12"), "msb"); ((TAtom "iw_8.iw_1.iw_1.v3"), "lsb"); ((TAtom "iw_8.iw_1.iw_1.v5"), "msb"); ((TAtom "iw_8.iw_1.iw_1.v6"), "x"); ((TAtom "iw_8.iw_1.iw_1.v7"), "lsb"); ((TAtom "iw_8.iw_1.iw_1.v9"), "x"); ((TAtom "iw_8.iw_1.v0"), "x1"); ((TAtom "iw_8.iw_1.v2"), "x2"); ((TAtom "iw_8.iw_1.v4"), "x1"); ((TAtom "iw_8.iw_1.v5"), "x2"); ((TAtom "iw_8.iw_2.iw_1.iw_1.v0"), "c_in"); ((TAtom "iw_8.iw_2.iw_1.iw_1.v5"), "c_in"); ((TAtom "iw_8.iw_2.iw_1.v0"), "x"); ((TAtom "iw_8.iw_2.iw_1.v11"), "m"); ((TAtom "iw_8.iw_2.iw_1.v3"), "m"); ((TAtom "iw_8.iw_2.iw_1.v4"), "x"); ((TAtom "iw_8.iw_2.iw_1.v5"), "m"); ((TAtom "iw_8.iw_2.iw_1.v7"), "m"); ((TAtom "iw_8.iw_2.iw_1.v9"), "x"); ((TAtom "iw_8.iw_2.v0"), "x1"); ((TAtom "iw_8.iw_2.v2"), "x2"); ((TAtom "iw_8.iw_2.v4"), "x1"); ((TAtom "iw_8.iw_2.v5"), "x2"); ((TAtom "iw_8.iw_3.iw_1.iw_1.v0"), "__x"); ((TAtom "iw_8.iw_3.iw_1.iw_1.v5"), "__x"); ((TAtom "iw_8.iw_3.iw_1.iw_1.v7"), "__x"); ((TAtom "iw_8.iw_3.iw_1.iw_2.v0"), "__x"); ((TAtom "iw_8.iw_3.iw_1.iw_2.v5"), "__x"); ((TAtom "iw_8.iw_3.iw_1.iw_2.v7"), "__x"); ((TAtom "iw_8.iw_3.iw_1.iw_3.v0"), "__x"); ((TAtom "iw_8.iw_3.iw_1.iw_3.v5"), "__x"); ((TAtom "iw_8.iw_3.iw_1.iw_3.v7"), "__x"); ((TAtom "iw_8.iw_3.iw_1.iw_4.v0"), "__x"); ((TAtom "iw_8.iw_3.iw_1.iw_4.v5"), "__x"); ((TAtom "iw_8.iw_3.iw_1.iw_4.v7"), "__x"); ((TAtom "iw_8.iw_3.iw_1.v0"), "c"); ((TAtom "iw_8.iw_3.iw_1.v12"), "c"); ((TAtom "iw_8.iw_3.iw_1.v18"), "c"); ((TAtom "iw_8.iw_3.iw_1.v21"), "c"); ((TAtom "iw_8.iw_3.iw_1.v6"), "c"); ((TAtom "iw_8.iw_3.iw_2.iw_1.v0"), "__x"); ((TAtom "iw_8.iw_3.iw_2.iw_1.v5"), "__x"); ((TAtom "iw_8.iw_3.iw_2.iw_1.v7"), "__x"); ((TAtom "iw_8.iw_3.iw_2.v0"), "c"); ((TAtom "iw_8.iw_3.iw_2.v2"), "c"); ((TAtom "iw_8.iw_3.pr.1"), "r"); ((TAtom "iw_8.iw_3.v0"), "c"); ((TAtom "iw_8.iw_3.v10"), "r"); ((TAtom "iw_8.iw_3.v11"), "r"); ((TAtom "iw_8.iw_3.v7"), "c"); ((TAtom "iw_8.iw_3.v8"), "r"); ((TAtom "iw_8.iw_3.v9"), "c"); ((TAtom "iw_8.pr.1"), "x1"); ((TAtom "iw_8.v0"), "x1"); ((TAtom "iw_8.v10"), "x1"); ((TAtom "iw_8.v11"), "x1"); ((TAtom "iw_8.v12"), "x2"); ((TAtom "iw_8.v13"), "x1"); ((TAtom "iw_8.v14"), "x1"); ((TAtom "iw_8.v2"), "x2"); ((TAtom "iw_8.v8"), "x1"); ((TAtom "iw_8.v9"), "x2"); ((TAtom "iw_9.iw_1.iw_1.iw_1.v0"), "c_in"); ((TAtom "iw_9.iw_1.iw_1.iw_1.v5"), "c_in"); ((TAtom "iw_9.iw_1.iw_1.iw_2.v0"), "c_in"); ((TAtom "iw_9.iw_1.iw_1.iw_2.v5"), "c_in"); ((TAtom "iw_9.iw_1.iw_1.v0"), "x"); ((TAtom "iw_9.iw_1.iw_1.v12"), "msb"); ((TAtom "iw_9.iw_1.iw_1.v3"), "lsb"); ((TAtom "iw_9.iw_1.iw_1.v5"), "msb"); ((TAtom "iw_9.iw_1.iw_1.v6"), "x"); ((TAtom "iw_9.iw_1.iw_1.v7"), "lsb"); ((TAtom "iw_9.iw_1.iw_1.v9"), "x"); ((TAtom "iw_9.iw_1.v0"), "x1"); ((TAtom "iw_9.iw_1.v2"), "x2"); ((TAtom "iw_9.iw_1.v4"), "x1"); ((TAtom "iw_9.iw_1.v5"), "x2"); ((TAtom "iw_9.v0"), "x1"); ((TAtom "iw_9.v2"), "x2"); ((TAtom "iw_9.v4"), "x1"); ((TAtom "iw_9.v5"), "x2"); ((TAtom "pr.1"), "word_ptr"); ((TAtom "pr.2"), "word"); ((TAtom "v0"), "s"); ((TAtom "v100"), "word"); ((TAtom "v101"), "repeated_c"); ((TAtom "v106"), "word_ptr"); ((TAtom "v107"), "word_ptr"); ((TAtom "v108"), "word"); ((TAtom "v112"), "word"); ((TAtom "v113"), "repeated_c"); ((TAtom "v117"), "word_ptr"); ((TAtom "v118"), "word"); ((TAtom "v119"), "repeated_c"); ((TAtom "v122"), "ret"); ((TAtom "v126"), "ret"); ((TAtom "v127"), "lbyte"); ((TAtom "v131"), "ret"); ((TAtom "v15"), "s"); ((TAtom "v19"), "word_ptr"); ((TAtom "v2"), "c_in"); ((TAtom "v21"), "s"); ((TAtom "v22"), "s_int"); ((TAtom "v24"), "word_ptr"); ((TAtom "v25"), "word"); ((TAtom "v27"), "c_in"); ((TAtom "v29"), "repeated_c"); ((TAtom "v31"), "s"); ((TAtom "v32"), "s_int"); ((TAtom "v33"), "n"); ((TAtom "v37"), "lbyte"); ((TAtom "v39"), "lbyte"); ((TAtom "v4"), "n"); ((TAtom "v43"), "lword"); ((TAtom "v45"), "word"); ((TAtom "v46"), "repeated_c"); ((TAtom "v48"), "s_int"); ((TAtom "v49"), "mask"); ((TAtom "v53"), "mask"); ((TAtom "v56"), "s"); ((TAtom "v57"), "mask"); ((TAtom "v60"), "ret"); ((TAtom "v64"), "ret"); ((TAtom "v65"), "lbyte"); ((TAtom "v69"), "ret"); ((TAtom "v75"), "word_ptr"); ((TAtom "v76"), "lword"); ((TAtom "v81"), "word_ptr"); ((TAtom "v82"), "word_ptr"); ((TAtom "v83"), "word"); ((TAtom "v87"), "word_ptr"); ((TAtom "v88"), "lword"); ((TAtom "v9"), "n"); ((TAtom "v95"), "word"); ((TAtom "v96"), "repeated_c"); ((TAtom "v99"), "word_ptr")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L84")].

End fn___memchr.

Module fn___GI___strnlen.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_5, 27%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_5, 30%N)); ((TAtom "L8"), (file_5, 31%N)); ((TAtom "L10"), (file_5, 31%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "str"); ((TAtom "v11"), "found"); ((TAtom "v14"), "found"); ((TAtom "v15"), "str"); ((TAtom "v19"), "maxlen"); ((TAtom "v2"), "maxlen"); ((TAtom "v5"), "str"); ((TAtom "v6"), "maxlen"); ((TAtom "v7"), "found")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

End fn___GI___strnlen.

(** Projection keeps instruction bodies out of the VM code used by the membership check. *)
Definition source_blocks : list (string * option (list name)) := Eval lazy in
  map (fun n => (n,
    match find_direct (TAtom n) strchr_module with
    | Some (Defined f) => Some (map b_label (fn_blocks f))
    | _ => None
    end)) ["__GI_strchr"; "__GI___strchrnul"; "__GI_strrchr"; "__memchr"; "__GI___strnlen"].

(** One computation rejects missing functions and stale labels across all tables in this fixture. *)
Lemma labels_valid :
  forallb (fun row =>
  match find (fun entry => String.eqb (fst entry) (fst row)) source_blocks with
  | Some (_, Some labels) =>
      forallb (fun l => existsb (name_eqb l) labels)
        (snd row)
  | _ => false
  end) [("__GI_strchr", app (map fst fn___GI_strchr.block_src) fn___GI_strchr.loop_heads); ("__GI___strchrnul", app (map fst fn___GI___strchrnul.block_src) fn___GI___strchrnul.loop_heads); ("__GI_strrchr", app (map fst fn___GI_strrchr.block_src) fn___GI_strrchr.loop_heads); ("__memchr", app (map fst fn___memchr.block_src) fn___memchr.loop_heads); ("__GI___strnlen", app (map fst fn___GI___strnlen.block_src) fn___GI___strnlen.loop_heads)] = true.
Proof. vm_compute. reflexivity. Qed.

End StrchrSrc.
