(** A stepping rule describes the current [[frame]] and what the next instruction
    changes. The notation names the environment, local allocations and pending
    failure. A frame with only an environment has no local allocations or
    pending failure. A machine configuration also names its caller stack,
    memory and remaining [[fuel]]. *)

From Stdlib Require Import List ZArith.
From Nanofil Require Import Term Syntax Values Semantics.
Import ListNotations.

(** A literal name starts with @. A computed key uses its ordinary Gallina
    spelling. Successive updates bind names from left to right, so the last
    update determines what a lookup of the same name returns. *)
Declare Custom Entry frame_name.
Notation "'@' s" := (TAtom s) (in custom frame_name at level 1, s constr at level 0, format "@ s").
Notation "n" := n (in custom frame_name at level 0, n constr at level 0).
Notation "e '.[' k ']'" := (lookup k e)
  (at level 1, left associativity, k custom frame_name at level 1, format "e .[ k ]").
Notation "e '.[' k ':=' v ']'" := (put k v e)
  (at level 1, left associativity, k custom frame_name at level 1, v at level 200,
   format "e .[ k  :=  v ]").

(** Shift a pointer's address by [off] while keeping its [[capability]]. *)
Definition ptr_shift (p : ptr) (off : Z) : ptr :=
  mkPtr (ptr_addr p + off)%Z (ptr_cap p).

(** Shift a pointer's address modulo `2 ^ 64` while keeping its [[capability]]. *)
Definition ptr_shift_mod (p : ptr) (off : Z) : ptr :=
  mkPtr ((ptr_addr p + off) mod 2 ^ 64)%Z (ptr_cap p).

(** Environment lookup results holding a typed integer or pointer [[word]]. *)
Abbreviation int_val n := (Some (WInt n)).
Abbreviation ptr_val p := (Some (WPtr p)).

(** An environment binds temporary [k] to some integer [[word]]. *)
Definition has_int (e : env) (k : name) : Prop :=
  exists n, e.[k] = int_val n.

(** An environment binds every temporary in [ks] to an integer [[word]]. *)
Fixpoint has_ints (e : env) (ks : list name) : Prop :=
  match ks with
  | [] => True
  | k :: rest => has_int e k /\ has_ints e rest
  end.

(** Program point executing [[block]] [l] of function [f] from its first
    instruction, falling back to [Enter l None] when [l] is absent. *)
Definition at_block (f : func) (l : name) : point :=
  match find_block l (fn_blocks f) with
  | Some b => Exec (b_label b) (b_insts b) (b_jump b)
  | None => Enter l None
  end.

(** Entering a [[block]] can select a predecessor for its [[phi]] nodes.
    Inside a block, the arrow separates the remaining instructions from the
    terminator. A computed program point can appear after the keyword pc. *)
Declare Custom Entry frame_point.
Notation "'pc:' p" := p (in custom frame_point at level 1, p constr at level 0).
Notation "'enter:' l 'from:' k" := (Enter l (Some k))
  (in custom frame_point at level 1, l custom frame_name, k custom frame_name).
Notation "'enter:' l" := (Enter l None) (in custom frame_point at level 1, l custom frame_name).
Notation "'at' l '{' code '=>' j '}'" := (Exec l code j)
  (in custom frame_point at level 0, l custom frame_name, code constr, j constr,
   format "'[hv' at  l  {  code  =>  j  } ']'").

Declare Custom Entry active_frame.
Notation "fr" := fr (in custom active_frame at level 10, fr constr at level 0).
Notation "f 'env:' e 'locals:' ls 'doomed:' d '|' p" := (mkFrame f e ls d p)
  (in custom active_frame at level 10, f constr at level 0, e constr at level 1,
   ls constr at level 0, d constr at level 0, p custom frame_point,
   format "'[hv' f  env:  e  locals:  ls  doomed:  d  '/  ' |  p ']'").
Notation "f 'env:' e 'doomed:' d '|' p" := (mkFrame f e [] d p)
  (in custom active_frame at level 10, f constr at level 0, e constr at level 1,
   d constr at level 0, p custom frame_point,
   format "'[hv' f  env:  e  doomed:  d  '/  ' |  p ']'").
Notation "f 'env:' e 'locals:' ls '|' p" := (mkFrame f e ls None p)
  (in custom active_frame at level 10, f constr at level 0, e constr at level 1,
   ls constr at level 0, p custom frame_point,
   format "'[hv' f  env:  e  locals:  ls  '/  ' |  p ']'").
Notation "f 'env:' e '|' p" := (mkFrame f e [] None p)
  (in custom active_frame at level 10, f constr at level 0, e constr at level 1, p custom frame_point,
   format "'[hv' f  env:  e  '/  ' |  p ']'").
Notation "'frame{' fr '}'" := (fr : frame)
  (only parsing, fr custom active_frame at level 10).
Notation "'frame{' fr '}'" := fr
  (only printing, fr custom active_frame at level 10, format "'[hv' frame{  fr  } ']'").

(** A configuration with no stack clause has no suspended callers.
    The labeled arrow says that one interpreter step produces the
    configuration on its right. *)
Notation "'cfg{' fr ';' 'stack:' cs ';' 'mem:' m ';' 'fuel:' n '}'" := (mkConfig fr cs m n)
  (fr custom active_frame at level 10, cs constr, m constr, n constr,
   format "'[hv' cfg{  fr ;  '/  ' '[hv' stack:  cs ;  mem:  m ;  fuel:  n ']'  } ']'").
Notation "'cfg{' fr ';' 'mem:' m ';' 'fuel:' n '}'" := (mkConfig fr [] m n)
  (fr custom active_frame at level 10, m constr, n constr,
   format "'[hv' cfg{  fr ;  '/  ' '[hv' mem:  m ;  fuel:  n ']'  } ']'").
Notation "c '⟶[' ge ']' c'" := (step ge c = Next c')
  (at level 70, ge at level 200, no associativity, format "'[v' c '/' ⟶[ ge ]  c' ']'").
