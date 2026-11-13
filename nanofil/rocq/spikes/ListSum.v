(** The C program `spikes/listsum.c` builds a linked list of n nodes on
    Fil-C's collected heap using `__builtin_alloca`, and then calls
    `sum` to walk the list and add each node's value. The compiler's
    checked IR for that program lives in [listsum_term]
    (`ListSumCode.v`), which `spikes/code.sh` keeps current with the C
    source.

    To walk the list safely, the summation loop must prove to Fil-C that
    each node pointer is live and in bounds before reading its fields.
    Each iteration runs a [[check]] on the 8-byte node value, runs a
    [[half_check|lower half check]] on the next pointer, loads that
    pointer through the [[aux]], and hits a [[poll]] on the back edge.

    Building the list in C allocates one node per iteration, stores the
    link pointer into it, and then calls the summation function. This
    shared module decodes the compiled fixture, lays out its globals and
    initial memory, and defines the entry frames that both logic spikes
    use (`docs/logic.md`). *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Transport.
From Spike Require Import ListSumCode.
Import ListNotations.
Open Scope Z_scope.

(** This definition decodes the checked module from the fixture [listsum_term]. *)
Definition ls_module : module :=
  match decode_module listsum_term with Some md => md | None => [] end.

(** Decoding the serialized fixture succeeds and produces the module [ls_module]. *)
Lemma ls_decodes : decode_module listsum_term = Some ls_module.
Proof. vm_compute. reflexivity. Qed.

(** This list holds the module's global addresses for its two functions, `sum` and `listsum`. *)
Definition ls_globals : list (name * ptr) :=
  match initial_memory ls_module with Some (g, _) => g | None => [] end.

(** The module starts with an initial memory that contains no heap objects. *)
Definition ls_mem : mem :=
  match initial_memory ls_module with Some (_, m) => m | None => empty_mem end.

(** Laying out [ls_module] in memory succeeds and produces [ls_globals] alongside [ls_mem]. *)
Lemma ls_initial : initial_memory ls_module = Some (ls_globals, ls_mem).
Proof.
  assert (H : option_map (fun _ => tt) (initial_memory ls_module) = Some tt)
    by (vm_compute; reflexivity).
  unfold ls_globals, ls_mem. destruct (initial_memory ls_module) as [[g m]|];
    inversion H; reflexivity.
Qed.

(** This helper constructs the global environment of [ls_module] with a caller-supplied `free` handler x. *)
Definition ls_ge (free : word -> mem -> option (res unit * mem)) : genv :=
  mkGenv ls_module ls_globals free.

(** This helper looks up a function named n in [ls_module] via [find_fn]. *)
Definition ls_fn (n : string) : func :=
  match find_fn (ls_ge (fun _ _ => None)) (TAtom n) with
  | Some (Defined f) => f
  | _ => mkFunc (TAtom n) (TAtom "export") (RClass L) [] []
  end.

(** The module defines `sum` as a function of the [[core subset]]. *)
Lemma ls_find_sum : forall free, find_fn (ls_ge free) (TAtom "sum") = Some (Defined (ls_fn "sum")).
Proof. intros free. vm_compute. reflexivity. Qed.

(** The module also defines `listsum` as a function of the core subset. *)
Lemma ls_find_listsum : forall free,
  find_fn (ls_ge free) (TAtom "listsum") = Some (Defined (ls_fn "listsum")).
Proof. intros free. vm_compute. reflexivity. Qed.

(** This helper returns the program point for block l of function f after skipping its first j instructions. *)
Definition ls_at (f : func) (l : string) (j : nat) : point :=
  match find_block (TAtom l) (fn_blocks f) with
  | Some b => Exec (TAtom l) (skipn j (b_insts b)) (b_jump b)
  | None => Enter (TAtom l) None
  end.

(** Calling `sum` with an argument list whose first word is x creates an
    entry frame that binds x to parameter `v0`. *)
Lemma sum_call_frame : forall x rest,
  call_frame (ls_fn "sum") (x :: rest) =
  Some (mkFrame (ls_fn "sum") [(TAtom "v0", x)] [] None (Enter (TAtom "start") None)).
Proof. reflexivity. Qed.

(** Calling `listsum` with an integer n as its first argument creates an
    entry frame that binds n to parameter `v0`. *)
Lemma listsum_call_frame : forall n rest,
  call_frame (ls_fn "listsum") (WInt n :: rest) =
  Some (mkFrame (ls_fn "listsum") [(TAtom "v0", WInt n)] [] None (Enter (TAtom "start") None)).
Proof. reflexivity. Qed.
