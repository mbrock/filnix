(** The program both logic spikes prove, shared by them: spikes/listsum.c,
    which builds a linked list of n nodes on the collected heap
    (`__builtin_alloca`, which Fil-C places there), then calls `sum`,
    which walks it and adds each node's value. Its checked module is
    [listsum_term] (ListSumCode.v, checked current by spikes/code.sh).

    `sum` is gc.ir's list walk in checked form: per node a [[check]] of
    the value's 8 bytes, a [[half_check|lower half check]] for the next
    pointer, a raw pointer load through the [[aux]], and a
    [[poll|poll]] on the back edge. `listsum` adds an allocation per
    iteration, a pointer store and a direct call. This file holds only
    what both spikes need: the module, its globals, its two functions
    and their call frames (docs/logic.md). *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Transport.
From Spike Require Import ListSumCode.
Import ListNotations.
Open Scope Z_scope.

(** The checked module, decoded from the fixture [listsum_term]. *)
Definition ls_module : module :=
  match decode_module listsum_term with Some md => md | None => [] end.

(** The fixture decodes to [ls_module]. *)
Lemma ls_decodes : decode_module listsum_term = Some ls_module.
Proof. vm_compute. reflexivity. Qed.

(** The module's globals: its two functions, `sum` and `listsum`. *)
Definition ls_globals : list (name * ptr) :=
  match initial_memory ls_module with Some (g, _) => g | None => [] end.

(** The module's initial memory, which holds no object. *)
Definition ls_mem : mem :=
  match initial_memory ls_module with Some (_, m) => m | None => empty_mem end.

(** Laying out the module succeeds, with [ls_globals] and [ls_mem]. *)
Lemma ls_initial : initial_memory ls_module = Some (ls_globals, ls_mem).
Proof.
  assert (H : option_map (fun _ => tt) (initial_memory ls_module) = Some tt)
    by (vm_compute; reflexivity).
  unfold ls_globals, ls_mem. destruct (initial_memory ls_module) as [[g m]|];
    inversion H; reflexivity.
Qed.

(** The genv of the module with the free x. *)
Definition ls_ge (free : word -> mem -> option (res unit * mem)) : genv :=
  mkGenv ls_module ls_globals free.

(** The function named n in the module, as [find_fn] finds it. *)
Definition ls_fn (n : string) : func :=
  match find_fn (ls_ge (fun _ _ => None)) (TAtom n) with
  | Some (Defined f) => f
  | _ => mkFunc (TAtom n) (TAtom "export") (RClass L) [] []
  end.

(** `sum` is a function of the [[core subset]] in the module. *)
Lemma ls_find_sum : forall free, find_fn (ls_ge free) (TAtom "sum") = Some (Defined (ls_fn "sum")).
Proof. intros free. vm_compute. reflexivity. Qed.

(** `listsum` is a function of the core subset in the module. *)
Lemma ls_find_listsum : forall free,
  find_fn (ls_ge free) (TAtom "listsum") = Some (Defined (ls_fn "listsum")).
Proof. intros free. vm_compute. reflexivity. Qed.

(** Block l of the function f after its first j instructions. *)
Definition ls_at (f : func) (l : string) (j : nat) : point :=
  match find_block (TAtom l) (fn_blocks f) with
  | Some b => Exec (TAtom l) (skipn j (b_insts b)) (b_jump b)
  | None => Enter (TAtom l) None
  end.

(** Any arguments whose first word is x start `sum` at its entry with
    x as its parameter `v0`. *)
Lemma sum_call_frame : forall x rest,
  call_frame (ls_fn "sum") (x :: rest) =
  Some (mkFrame (ls_fn "sum") [(TAtom "v0", x)] [] None (Enter (TAtom "start") None)).
Proof. reflexivity. Qed.

(** Any arguments whose first word is the integer n start `listsum` at
    its entry with n as its parameter `v0`. *)
Lemma listsum_call_frame : forall n rest,
  call_frame (ls_fn "listsum") (WInt n :: rest) =
  Some (mkFrame (ls_fn "listsum") [(TAtom "v0", WInt n)] [] None (Enter (TAtom "start") None)).
Proof. reflexivity. Qed.
