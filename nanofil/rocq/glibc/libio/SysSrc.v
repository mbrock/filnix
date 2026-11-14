(** These tables connect checked function bodies to C declarations and source lines.
    Names and locations support annotations and diagnostic messages, not soundness premises.
    Natural-loop headers provide optional cuts for symbolic execution; any cut list is sound.
    Computation checks that every recorded block label belongs to the decoded function.
    The code generator reproduces this file from the capture; do not edit it. *)

From Stdlib Require Import String List Bool.
From Glibc Require Import CodePrelude SysCode.
Import ListNotations.
Open Scope string_scope.

Module SysSrc.

Module fn___isatty_nostatus.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("../sysdeps/unix/sysv/linux/isatty_nostatus.c", 22%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("../sysdeps/unix/sysv/linux/isatty_nostatus.c", 25%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fd"); ((TAtom "v3"), "fd")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__isatty_nostatus") (code_module sys_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___isatty_nostatus.

Module fn___GI___libc_write.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("../sysdeps/unix/sysv/linux/write.c", 24%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("../sysdeps/unix/sysv/linux/write.c", 27%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fd"); ((TAtom "v2"), "buf"); ((TAtom "v4"), "nbytes"); ((TAtom "v6"), "fd"); ((TAtom "v7"), "buf"); ((TAtom "v8"), "nbytes")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__GI___libc_write") (code_module sys_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___GI___libc_write.

Module fn___lseek64.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("../sysdeps/unix/sysv/linux/lseek64.c", 27%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("../sysdeps/unix/sysv/linux/lseek64.c", 30%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fd"); ((TAtom "v2"), "offset"); ((TAtom "v4"), "whence"); ((TAtom "v6"), "fd"); ((TAtom "v7"), "offset"); ((TAtom "v8"), "whence")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__lseek64") (code_module sys_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___lseek64.

Module fn___GI___fstat64.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("../sysdeps/unix/sysv/linux/fstat64.c", 29%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("../sysdeps/unix/sysv/linux/fstat64.c", 32%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fd"); ((TAtom "v2"), "buf"); ((TAtom "v4"), "fd"); ((TAtom "v5"), "buf")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__GI___fstat64") (code_module sys_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___GI___fstat64.

Module fn___GI___close_nocancel.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("../sysdeps/unix/sysv/linux/close_nocancel.c", 24%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("../sysdeps/unix/sysv/linux/close_nocancel.c", 27%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fd"); ((TAtom "v2"), "fd")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__GI___close_nocancel") (code_module sys_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___GI___close_nocancel.

Module fn___GI___close_nocancel_nostatus.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("../sysdeps/unix/sysv/linux/close_nocancel_nostatus.c", 24%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("../sysdeps/unix/sysv/linux/close_nocancel_nostatus.c", 27%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fd"); ((TAtom "v2"), "fd")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__GI___close_nocancel_nostatus") (code_module sys_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___GI___close_nocancel_nostatus.

Module fn___GI__exit.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("../sysdeps/unix/sysv/linux/_exit.c", 26%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("../sysdeps/unix/sysv/linux/_exit.c", 30%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "status"); ((TAtom "v2"), "status")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__GI__exit") (code_module sys_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___GI__exit.

Module fn___GI___libc_cleanup_push_defer.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("libc-cleanup.c", 22%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("libc-cleanup.c", 25%nat)); ((TAtom "L22"), ("libc-cleanup.c", 29%nat)); ((TAtom "L35"), ("libc-cleanup.c", 39%nat)); ((TAtom "L36"), ("libc-cleanup.c", 29%nat)); ((TAtom "L15"), ("libc-cleanup.c", 29%nat)); ((TAtom "L41"), ("libc-cleanup.c", 44%nat)); ((TAtom "L42"), ("libc-cleanup.c", 44%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "pr.1"), "cancelhandling"); ((TAtom "pr.2"), "cancelhandling"); ((TAtom "pr.3"), "cancelhandling"); ((TAtom "v0"), "buffer"); ((TAtom "v10"), "self"); ((TAtom "v12"), "cancelhandling"); ((TAtom "v16"), "cancelhandling"); ((TAtom "v25"), "cancelhandling"); ((TAtom "v28"), "newval"); ((TAtom "v29"), "self"); ((TAtom "v3"), "self"); ((TAtom "v31"), "newval"); ((TAtom "v32"), "cancelhandling"); ((TAtom "v33"), "cancelhandling"); ((TAtom "v38"), "buffer"); ((TAtom "v4"), "buffer"); ((TAtom "v43"), "cancelhandling"); ((TAtom "v47"), "self"); ((TAtom "v49"), "buffer"); ((TAtom "v6"), "self")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L22")].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__GI___libc_cleanup_push_defer") (code_module sys_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___GI___libc_cleanup_push_defer.

Module fn___GI___libc_cleanup_pop_restore.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("libc-cleanup.c", 52%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("libc-cleanup.c", 55%nat)); ((TAtom "L20"), ("libc-cleanup.c", 60%nat)); ((TAtom "L21"), ("libc-cleanup.c", 60%nat)); ((TAtom "L29"), ("libc-cleanup.c", 59%nat)); ((TAtom "L41"), ("libc-cleanup.c", 68%nat)); ((TAtom "L42"), ("libc-cleanup.c", 59%nat)); ((TAtom "iw_1.start"), ("../nptl/descr.h", 463%nat)); ((TAtom "L44"), ("libc-cleanup.c", 72%nat)); ((TAtom "iw_2.L12"), ("../sysdeps/nptl/pthreadP.h", 256%nat)); ((TAtom "iw_2.L13"), ("../sysdeps/nptl/pthreadP.h", 268%nat)); ((TAtom "iw_2.L37"), ("../sysdeps/nptl/pthreadP.h", 268%nat)); ((TAtom "iw_2.L38"), ("../sysdeps/nptl/pthreadP.h", 256%nat)); ((TAtom "iw_2.L14"), ("../sysdeps/nptl/pthreadP.h", 271%nat)); ((TAtom "L15"), ("libc-cleanup.c", 52%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "value"); ((TAtom "iw_1.v2"), "value"); ((TAtom "iw_2.pr.1"), "oldval"); ((TAtom "iw_2.pr.2"), "oldval"); ((TAtom "iw_2.v0"), "result"); ((TAtom "iw_2.v10"), "oldval"); ((TAtom "iw_2.v15"), "oldval"); ((TAtom "iw_2.v19"), "newval"); ((TAtom "iw_2.v20"), "newval"); ((TAtom "iw_2.v23"), "newval"); ((TAtom "iw_2.v27"), "oldval"); ((TAtom "iw_2.v28"), "newval"); ((TAtom "iw_2.v3"), "self"); ((TAtom "iw_2.v31"), "self"); ((TAtom "iw_2.v33"), "newval"); ((TAtom "iw_2.v34"), "oldval"); ((TAtom "iw_2.v35"), "oldval"); ((TAtom "iw_2.v4"), "self"); ((TAtom "iw_2.v40"), "self"); ((TAtom "iw_2.v6"), "result"); ((TAtom "iw_2.v8"), "self"); ((TAtom "pr.1"), "cancelhandling"); ((TAtom "pr.2"), "cancelhandling"); ((TAtom "v0"), "buffer"); ((TAtom "v10"), "self"); ((TAtom "v12"), "cancelhandling"); ((TAtom "v16"), "buffer"); ((TAtom "v22"), "cancelhandling"); ((TAtom "v3"), "self"); ((TAtom "v32"), "cancelhandling"); ((TAtom "v34"), "newval"); ((TAtom "v35"), "self"); ((TAtom "v37"), "newval"); ((TAtom "v38"), "cancelhandling"); ((TAtom "v39"), "cancelhandling"); ((TAtom "v4"), "self"); ((TAtom "v47"), "cancelhandling"); ((TAtom "v6"), "buffer")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L29"); (TAtom "iw_2.L12")].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__GI___libc_cleanup_pop_restore") (code_module sys_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___GI___libc_cleanup_pop_restore.

Module fn___GI___write_nocancel.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("../sysdeps/unix/sysv/linux/write_nocancel.c", 24%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("../sysdeps/unix/sysv/linux/write_nocancel.c", 27%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fd"); ((TAtom "v2"), "buf"); ((TAtom "v4"), "nbytes"); ((TAtom "v6"), "fd"); ((TAtom "v7"), "buf"); ((TAtom "v8"), "nbytes")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__GI___write_nocancel") (code_module sys_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___GI___write_nocancel.

End SysSrc.
