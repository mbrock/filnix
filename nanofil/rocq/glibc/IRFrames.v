(** The proof of a compiled function needs to know where execution starts
    and which arguments it receives. This module looks up the starting
    instructions and supplies tactics for reasoning about their operands. *)

From Stdlib Require Import String List.
From Nanofil Require Import Term Syntax Values Memory Semantics Symbolic.
Import ListNotations.

(** A call binds the argument words in the frame at the function's entry. *)
Definition invocation (f : func) (xs : list word) : frame :=
  match call_frame f xs with
  | Some fr => fr
  | None => mkFrame f [] [] None (Enter (TAtom "start") None)
  end.

(** A block label selects its instructions, or an unreachable block if the label is absent. *)
Definition hblk (f : func) (l : string) : block :=
  match find_block (TAtom l) (fn_blocks f) with
  | Some b => b
  | None => mkBlock (TAtom l) [] [] JUnreachable
  end.

(** The environment's known words let the step rule compute its operands. *)
Ltac word_premise := first [ reflexivity | compute_premise ].

(** The address premise reduces to arithmetic once the bounds rule out wrapping. *)
Ltac addr_premise := cbn [ptr_addr]; unfold raw_address; drop_wraps_goal; arith.
