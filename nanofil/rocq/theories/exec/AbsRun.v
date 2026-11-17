(** A proof that a function never panics has to hold for every input,
    and a function of several thousand IR instructions is too long to
    step through by hand. This module is the first half of a checker
    that carries out such a proof by computation.

    The checker runs a function on abstract values. An integer is a
    constant or a named unknown with a range. A pointer is an object
    and an offset into it. Each byte of an object is a constant, a
    piece of a named unknown, a range, or unknown. A run fails when a
    bounds check, a store, a call or a jump could go wrong for some
    value in those ranges.

    A call of a function with a body is matched against a specification
    of that function. A call of anything else goes to a hook that the
    user of the checker supplies, so that the checker itself knows no
    system call. The checker can also carry one fact about the world
    outside the program, which it calls the guard, and which a hook may
    require before a call.

    This file defines the checker, and it states no theorem about a
    program. The theorem [verify_sound] of [AbsSound](AbsSound.v)
    proves that the checker is sound. It says that a function which
    passes the check satisfies its specification in the program logic.
    [AbsInfer](AbsInfer.v) finds the loop invariants that a run needs. *)

From Stdlib Require Import String ZArith List Bool.
From Nanofil Require Import Term Syntax Values Memory Ops Semantics.
Import ListNotations.
Open Scope list_scope.
Open Scope Z_scope.

(** * Abstract values *)

Inductive aint : Type := K (z : Z) | S (s : nat).

Inductive aval : Type :=
| VI (a : aint)
| VC (c : cond) (k : class) (a b : aint)
| VJ
| VP (o : nat) (a : aint)
| VN (a : aint)
| VA
| VF (g : name).

(** An abstract byte says what the checker knows about one byte of
    memory. The byte is a constant, or it is byte [i] of the symbol
    [s], or it lies in a range, or nothing is known about it. Two more
    forms attach one fact to an unknown byte. Bit [k] of a [BGuard k]
    byte is set only when the guard holds. The bits under [mask] of a
    [BEnd s key mask] byte are zero when the symbol [s] equals [key]. *)
Inductive abyte : Type :=
| BK (z : Z) | BOf (s : nat) (i : Z) | BIn (lo hi : Z) | BR
| BGuard (k : Z) | BEnd (s : nat) (key mask : Z).

(** A flag records one fact about a symbol that an interval cannot
    express. The guard holds when bit [n] of a symbol with [FBit n] is
    set, and when a symbol with [FNz] is not zero. A symbol with
    [FEnd s key mask] has zero bits under [mask] when [s] equals [key],
    and a symbol with [FEndNz s key] is zero when [s] equals [key]. *)
Inductive flag : Type := FBit (n : Z) | FNz | FEnd (s : nat) (key mask : Z) | FEndNz (s : nat) (key : Z).

Inductive aaux : Type := XNone | XObj (o : nat) | XAny.

Record aobj : Type := mkObj {
  o_ro : bool;
  o_align : Z;
  o_bytes : list abyte;
  o_aux : list aaux
}.

Definition o_size (ob : aobj) : Z := Z.of_nat (length (o_bytes ob)).

Record astate : Type := mkSt {
  st_env : list (name * aval);
  st_bnd : list (Z * Z);
  st_flags : list (nat * flag);
  st_lin : list (nat * nat * Z);
  st_objs : list (option aobj);
  st_guard : bool
}.

Inductive cval : Type :=
| CI (lo hi : Z) | CJ | CP (o : nat) (lo hi : Z) | CN (lo hi : Z) | CA | CF (g : name).

Record cstate : Type := mkCs {
  cs_env : list (name * cval);
  cs_objs : list (option aobj);
  cs_guard : bool
}.

Record fspec : Type := mkSpec {
  sp_args : list cval;
  sp_pre : list (option aobj);
  sp_guard : bool;
  sp_post : list (option aobj);
  sp_guard' : bool;
  sp_ret : option cval
}.

(** * Small helpers *)

Notation "'let?' x ':=' e 'in' b" :=
  (match e with Some x => b | None => None end)
  (at level 10, x pattern, e at level 100, b at level 200).

Fixpoint list_set {A : Type} (n : nat) (x : A) (l : list A) : list A :=
  match n, l with
  | O, _ :: l' => x :: l'
  | Datatypes.S n', y :: l' => y :: list_set n' x l'
  | _, [] => []
  end.

Fixpoint index_of (n : name) (l : list name) : option nat :=
  match l with
  | [] => None
  | x :: l' => if name_eqb n x then Some O else option_map Datatypes.S (index_of n l')
  end.

Definition mem_name (n : name) (l : list name) : bool := existsb (name_eqb n) l.

Definition cond_eqb (c d : cond) : bool :=
  match c, d with
  | Eq, Eq | Ne, Ne | Ult, Ult | Ule, Ule | Ugt, Ugt | Uge, Uge
  | Slt, Slt | Sle, Sle | Sgt, Sgt | Sge, Sge => true
  | _, _ => false
  end.

Definition window {A : Type} (k w : Z) (l : list A) : list A :=
  firstn (Z.to_nat w) (skipn (Z.to_nat k) l).

Definition splice {A : Type} (k : Z) (new : list A) (l : list A) : list A :=
  firstn (Z.to_nat k) l ++ new ++ skipn (Z.to_nat k + length new) l.

Fixpoint of_bytes' (xs : list Z) : Z :=
  match xs with [] => 0 | x :: xs' => x + 256 * of_bytes' xs' end.

(** * Symbols *)

Definition rng (st : astate) (a : aint) : Z * Z :=
  match a with K z => (z, z) | S s => nth s (st_bnd st) (0, 0) end.

Definition fresh (st : astate) (lo hi : Z) : nat * astate :=
  (length (st_bnd st),
   mkSt (st_env st) (st_bnd st ++ [(lo, hi)]) (st_flags st) (st_lin st) (st_objs st) (st_guard st)).

Definition mk (st : astate) (lo hi : Z) : aint * astate :=
  if lo =? hi then (K lo, st) else let (s, st') := fresh st lo hi in (S s, st').

Definition set_bnd (st : astate) (bnd : list (Z * Z)) : astate :=
  mkSt (st_env st) bnd (st_flags st) (st_lin st) (st_objs st) (st_guard st).

Definition meet (s : nat) (lo hi : Z) (bnd : list (Z * Z)) : list (Z * Z) :=
  let (l, h) := nth s bnd (0, 0) in list_set s (Z.max l lo, Z.min h hi) bnd.

(** A new range for a symbol also narrows the symbols that differ from it
    by a constant. *)
Definition set_rng (st : astate) (a : aint) (lo hi : Z) : astate :=
  match a with
  | K _ => st
  | S s =>
      set_bnd st (fold_left (fun bnd l =>
                               let '(t, u, c) := l in
                               if Nat.eqb u s then meet t (lo + c) (hi + c) bnd
                               else if Nat.eqb t s then meet u (lo - c) (hi - c) bnd
                               else bnd)
                            (st_lin st) (list_set s (lo, hi) (st_bnd st)))
  end.

Definition set_env (st : astate) (e : list (name * aval)) : astate :=
  mkSt e (st_bnd st) (st_flags st) (st_lin st) (st_objs st) (st_guard st).

Definition bind (st : astate) (d : name) (v : aval) : astate := set_env st ((d, v) :: st_env st).

Definition set_objs (st : astate) (os : list (option aobj)) : astate :=
  mkSt (st_env st) (st_bnd st) (st_flags st) (st_lin st) os (st_guard st).

Definition set_guard (st : astate) (b : bool) : astate :=
  mkSt (st_env st) (st_bnd st) (st_flags st) (st_lin st) (st_objs st) b.

Definition add_flag (st : astate) (s : nat) (fl : flag) : astate :=
  mkSt (st_env st) (st_bnd st) ((s, fl) :: st_flags st) (st_lin st) (st_objs st) (st_guard st).

Definition add_lin (st : astate) (t s : nat) (c : Z) : astate :=
  mkSt (st_env st) (st_bnd st) (st_flags st) ((t, s, c) :: st_lin st) (st_objs st) (st_guard st).

Definition flag_eqb (a b : flag) : bool :=
  match a, b with
  | FBit n, FBit m => n =? m
  | FNz, FNz => true
  | FEnd s k m, FEnd t k' m' => Nat.eqb s t && (k =? k') && (m =? m')
  | FEndNz s k, FEndNz t k' => Nat.eqb s t && (k =? k')
  | _, _ => false
  end.

Definition has_flag (st : astate) (s : nat) (fl : flag) : bool :=
  existsb (fun f => Nat.eqb (fst f) s && flag_eqb (snd f) fl) (st_flags st).

(** The function [flag_picks] lists what [pick] selects from the flags on [s]. *)
Definition flag_picks {A : Type} (st : astate) (s : nat) (pick : flag -> option A) : list A :=
  flat_map (fun f => if Nat.eqb (fst f) s then match pick (snd f) with Some u => [u] | None => [] end else [])
           (st_flags st).

Definition get_obj (st : astate) (o : nat) : option aobj :=
  match nth_error (st_objs st) o with Some (Some ob) => Some ob | _ => None end.

Definition put_obj (st : astate) (o : nat) (ob : option aobj) : astate :=
  set_objs st (list_set o ob (st_objs st)).

(** * Substituting one symbol for another *)

Definition sub_aint (s t : nat) (a : aint) : aint :=
  match a with S u => if Nat.eqb u s then S t else a | _ => a end.

Definition sub_aval (s t : nat) (v : aval) : aval :=
  match v with
  | VI a => VI (sub_aint s t a)
  | VC c k a b => VC c k (sub_aint s t a) (sub_aint s t b)
  | VP o a => VP o (sub_aint s t a)
  | VN a => VN (sub_aint s t a)
  | _ => v
  end.

Definition sub_sym (s t u : nat) : nat := if Nat.eqb u s then t else u.

Definition sub_byte (s t : nat) (b : abyte) : abyte :=
  match b with
  | BOf u i => BOf (sub_sym s t u) i
  | BEnd u key mask => BEnd (sub_sym s t u) key mask
  | _ => b
  end.

Definition sub_flag (s t : nat) (fl : flag) : flag :=
  match fl with
  | FEnd u key mask => FEnd (sub_sym s t u) key mask
  | FEndNz u key => FEndNz (sub_sym s t u) key
  | _ => fl
  end.

Definition sub_obj (s t : nat) (ob : aobj) : aobj :=
  mkObj (o_ro ob) (o_align ob) (map (sub_byte s t) (o_bytes ob)) (o_aux ob).

Definition sub_state (s t : nat) (st : astate) : astate :=
  mkSt (map (fun nv => (fst nv, sub_aval s t (snd nv))) (st_env st)) (st_bnd st)
       (map (fun f => (sub_sym s t (fst f), sub_flag s t (snd f))) (st_flags st))
       (map (fun l => let '(a, b, c) := l in (sub_sym s t a, sub_sym s t b, c)) (st_lin st))
       (map (option_map (sub_obj s t)) (st_objs st)) (st_guard st).

(** * Refinement by a comparison *)

Definition ref_le (st : astate) (a b : aint) : option astate :=
  let (alo, ahi) := rng st a in
  let (blo, bhi) := rng st b in
  if bhi <? alo then None
  else Some (set_rng (set_rng st a alo (Z.min ahi bhi)) b (Z.max blo alo) bhi).

Definition ref_lt (st : astate) (a b : aint) : option astate :=
  let (alo, ahi) := rng st a in
  let (blo, bhi) := rng st b in
  if bhi <=? alo then None
  else Some (set_rng (set_rng st a alo (Z.min ahi (bhi - 1))) b (Z.max blo (alo + 1)) bhi).

Definition ref_eq (st : astate) (a b : aint) : option astate :=
  let (alo, ahi) := rng st a in
  let (blo, bhi) := rng st b in
  let lo := Z.max alo blo in
  let hi := Z.min ahi bhi in
  if hi <? lo then None
  else
    let st' := set_rng (set_rng st a lo hi) b lo hi in
    Some (match a, b with
          | S s, S t => if Nat.eqb s t then st'
                        else if Nat.ltb s t then sub_state t s st' else sub_state s t st'
          | _, _ => st'
          end).

Definition ref_ne (st : astate) (a b : aint) : option astate :=
  let (alo, ahi) := rng st a in
  let (blo, bhi) := rng st b in
  if (alo =? ahi) && (blo =? bhi) && (alo =? blo) then None
  else if blo =? bhi then
    Some (if alo =? blo then set_rng st a (alo + 1) ahi
          else if ahi =? blo then set_rng st a alo (ahi - 1) else st)
  else if alo =? ahi then
    Some (if blo =? alo then set_rng st b (blo + 1) bhi
          else if bhi =? alo then set_rng st b blo (bhi - 1) else st)
  else Some st.

Definition negate (c : cond) : cond :=
  match c with
  | Eq => Ne | Ne => Eq | Ult => Uge | Uge => Ult | Ule => Ugt | Ugt => Ule
  | Slt => Sge | Sge => Slt | Sle => Sgt | Sgt => Sle | c => c
  end.

Definition half (k : class) : Z := match k with W => 2 ^ 31 | _ => 2 ^ 63 end.

Definition nonneg_half (st : astate) (k : class) (a : aint) : bool :=
  let (lo, hi) := rng st a in (0 <=? lo) && (hi <? half k).

(** A nonzero flagged symbol shows that the guard holds, or that the
    symbol its flag names differs from the flag's key. *)
Definition note_nonzero (st : astate) (a : aint) : option astate :=
  match a with
  | S s =>
      fold_left (fun acc uk => let* st' := acc in ref_ne st' (S (fst uk)) (K (snd uk)))
                (flag_picks st s (fun fl => match fl with FEndNz u key => Some (u, key) | _ => None end))
                (Some (if has_flag st s FNz then set_guard st true else st))
  | K _ => Some st
  end.

Definition refine1 (st : astate) (c : cond) (k : class) (a b : aint) : option astate :=
  match c with
  | Eq => ref_eq st a b
  | Ne => let* st' := ref_ne st a b in
          match b with K 0 => note_nonzero st' a | _ => Some st' end
  | Ult => ref_lt st a b
  | Ule => ref_le st a b
  | Ugt => ref_lt st b a
  | Uge => ref_le st b a
  | Slt => if nonneg_half st k a && nonneg_half st k b then ref_lt st a b else Some st
  | Sle => if nonneg_half st k a && nonneg_half st k b then ref_le st a b else Some st
  | Sgt => if nonneg_half st k a && nonneg_half st k b then ref_lt st b a else Some st
  | Sge => if nonneg_half st k a && nonneg_half st k b then ref_le st b a else Some st
  | _ => Some st
  end.

Definition refine (st : astate) (c : cond) (k : class) (a b : aint) (truth : bool) : option astate :=
  refine1 st (if truth then c else negate c) k a b.

(** * Reading operands *)

Definition modulus_of (k : class) : option Z :=
  match k with W => Some (2 ^ 32) | L => Some (2 ^ 64) | _ => None end.

Definition tmp_at (k : class) (v : aval) (st : astate) : option (aval * astate) :=
  match k with
  | W | L =>
      let m := match k with W => 2 ^ 32 | _ => 2 ^ 64 end in
      match v with
      | VI a => let (lo, hi) := rng st a in
                if (0 <=? lo) && (hi <? m) then Some (v, st)
                else let (s, st') := fresh st 0 (m - 1) in Some (VI (S s), st')
      | VC _ _ _ _ => Some (v, st)
      | VJ => let (s, st') := fresh st 0 (m - 1) in Some (VI (S s), st')
      | _ => None
      end
  | P | A | F => Some (v, st)
  | _ => None
  end.

(** A pointer whose offset is one known number names one place. *)
(** A hook answers a call of a function without a body. It is given
    the function's name, where the result goes, the classes of the
    arguments and their values. It answers [None] when the function is
    not one of its own, [Some None] when the call may go wrong, and
    otherwise the state after the call. *)
Definition hook : Type := name -> call_result -> list class -> list aval -> astate -> option (option astate).

Definition class_plain (k : class) : bool := match k with W | L | P => true | _ => false end.

Definition exact_ptr (st : astate) (v : aval) : option (nat * Z) :=
  match v with
  | VP o a => let (lo, hi) := rng st a in if lo =? hi then Some (o, lo) else None
  | _ => None
  end.

Section exec.

(** The interpreter is given four things about the program around the
    function. The hook [builtin] answers calls of functions without a
    body. Every state numbers the global data objects in [gobjs] first.
    The list [fnames] gives the functions that a pointer may name, each
    with the classes of its parameters and its return type, and [specs]
    gives the specifications of the callees. *)
Variable builtin : hook.
Variable gobjs : list name.
Variable fnames : list (name * (list class * ret_type)).
Variable specs : name -> list fspec.

Definition nglob : nat := length gobjs.

Definition avalue (k : class) (v : value) (st : astate) : option (aval * astate) :=
  match v with
  | Tmp n => let* x := lookup n (st_env st) in tmp_at k x st
  | Const n =>
      match k with
      | W => Some (VI (K (n mod 2 ^ 32)), st)
      | L => Some (VI (K (n mod 2 ^ 64)), st)
      | P => Some (VN (K (n mod 2 ^ 64)), st)
      | _ => None
      end
  | Global s =>
      match index_of s gobjs with
      | Some o => Some (VP o (K 0), st)
      | None => match lookup s fnames with Some _ => Some (VF s, st) | None => Some (VA, st) end
      end
  end.

Fixpoint avalues (ks : list class) (vs : list value) (st : astate) : option (list aval * astate) :=
  match ks, vs with
  | [], [] => Some ([], st)
  | k :: ks', v :: vs' =>
      let? (x, st1) := avalue k v st in
      let? (xs, st2) := avalues ks' vs' st1 in
      Some (x :: xs, st2)
  | _, _ => None
  end.

(** * Arithmetic *)

Definition clamp (st : astate) (m lo hi : Z) : aint * astate :=
  if (0 <=? lo) && (hi <? m) then mk st lo hi else mk st 0 (m - 1).

Definition ext_keep (t : narrow) (k : class) (hi : Z) : bool :=
  match t with
  | Uw => true
  | Ub => hi <? 256
  | Uh => hi <? 65536
  | Sw => match k with W => true | _ => hi <? 2 ^ 31 end
  | Sb => hi <? 128
  | Sh => hi <? 32768
  end.

Definition ext_top (t : narrow) (k : class) (m : Z) : Z :=
  match t with
  | Ub => 255
  | Uh => 65535
  | Uw => 2 ^ 32 - 1
  | _ => m - 1
  end.

(** Arithmetic on two integers of which one is a symbol works on their
    ranges. Both operands must already lie in the class. *)
Definition abin_rng (o : op) (k : class) (m : Z) (x y : aint) (st : astate) : option (aint * astate) :=
  let (xlo, xhi) := rng st x in
  let (ylo, yhi) := rng st y in
  if negb ((0 <=? xlo) && (xhi <? m) && (0 <=? ylo) && (yhi <? 2 ^ 64)) then None else
  match o with
  | Add => Some (clamp st m (xlo + ylo) (xhi + yhi))
  | Sub => Some (clamp st m (xlo - yhi) (xhi - ylo))
  | Mul => Some (clamp st m (xlo * ylo) (xhi * yhi))
  | And => Some (mk st 0 (Z.min xhi yhi))
  | Or | Xor => Some (mk st 0 (2 ^ (Z.log2 (Z.max xhi yhi) + 1) - 1))
  | Shl =>
      match y with
      | K c => let p := 2 ^ (c mod (match k with W => 32 | _ => 64 end)) in
               Some (clamp st m (xlo * p) (xhi * p))
      | _ => Some (mk st 0 (m - 1))
      end
  | Shr =>
      match y with
      | K c => let p := 2 ^ (c mod (match k with W => 32 | _ => 64 end)) in
               Some (mk st (xlo / p) (xhi / p))
      | _ => Some (mk st 0 xhi)
      end
  | Udiv => Some (mk st 0 xhi)
  | Div => if (xhi <? half k) && (yhi <? half k) then Some (mk st 0 xhi) else Some (mk st 0 (m - 1))
  | _ => None
  end.

Definition abin (o : op) (k : class) (x y : aint) (st : astate) : option (aint * astate) :=
  let* m := modulus_of k in
  match x, y with
  | K a, K b =>
      match alu o k [WInt a; WInt b] with
      | Some (WInt r) => Some (K r, st)
      | _ => None
      end
  | _, _ => abin_rng o k m x y st
  end.

Definition int_cond (c : cond) : bool :=
  match c with Le | Lt | Ge | Gt | Ord | Unord => false | _ => true end.

(** A comparison result used as a number is 0 or 1, and is known when
    one of its two outcomes is impossible. *)
Definition as_int (v : aval) (st : astate) : aval * astate :=
  match v with
  | VC c k a b =>
      match refine st c k a b true, refine st c k a b false with
      | None, _ => (VI (K 0), st)
      | _, None => (VI (K 1), st)
      | _, _ => let (s, st') := fresh st 0 1 in (VI (S s), st')
      end
  | _ => (v, st)
  end.

Fixpoint as_ints (vs : list aval) (st : astate) : list aval * astate :=
  match vs with
  | [] => ([], st)
  | v :: vs' => let (x, st1) := as_int v st in
                let (xs, st2) := as_ints vs' st1 in (x :: xs, st2)
  end.

(** An "and" with a constant mask and an addition of a constant keep a
    fact about their first operand. The result of the "and" inherits
    the flags that the mask selects, and the result of the addition
    differs from the operand by the constant when it does not wrap. *)
Definition aflags (o : op) (k : class) (a b r : aint) (st st' : astate) : astate :=
  match o, a, b, r with
  | And, S s, K c, S t =>
      let bits := flag_picks st s (fun fl => match fl with FBit n => Some n | _ => None end) in
      let st1 := if existsb (fun n => (0 <=? n) && (c =? 2 ^ n)) bits then add_flag st' t FNz else st' in
      fold_left (fun acc uk => add_flag acc t (FEndNz (fst uk) (snd uk)))
                (flag_picks st s (fun fl => match fl with
                                            | FEnd u key mask => if mask =? c then Some (u, key) else None
                                            | _ => None
                                            end)) st1
  | Add, S s, K c, S t =>
      match modulus_of k with
      | Some m => let (lo, hi) := rng st (S s) in
                  if (0 <=? lo + c) && (hi + c <? m) then add_lin st' t s c else st'
      | None => st'
      end
  | _, _, _, _ => st'
  end.

Definition aop_int (o : op) (k : class) (xs : list aval) (st : astate) : option (aval * astate) :=
  match o, xs with
  | Cmp c ck, [VI a; VI b] =>
      if int_cond c && match ck with W | L => true | _ => false end then Some (VC c ck a b, st) else None
  | Cmp _ _, _ => None
  | Ext t, [VI a] =>
      let* m := modulus_of k in
      let (lo, hi) := rng st a in
      if (0 <=? lo) && (hi <? 2 ^ 32) && ext_keep t k hi then Some (VI a, st)
      else let (r, st') := mk st 0 (ext_top t k m) in Some (VI r, st')
  | Neg, [VI a] =>
      let* m := modulus_of k in
      match a with
      | K z => Some (VI (K ((- z) mod m)), st)
      | _ => let (r, st') := mk st 0 (m - 1) in Some (VI r, st')
      end
  | _, [VI a; VI b] =>
      let? (r, st') := abin o k a b st in Some (VI r, aflags o k a b r st st')
  | _, _ => None
  end.

Definition aop (o : op) (k : class) (xs : list aval) (st : astate) : option (aval * astate) :=
  match o, xs with
  | Copy, [x] => match k with Single | Double | Extended => None | _ => Some (x, st) end
  | Ptoi, [VN a] => Some (VI a, st)
  | Ptoi, [(VP _ _ | VA | VF _)] => Some (VJ, st)
  | (Copy | Ptoi), _ => None
  | _, _ => let (xs', st') := as_ints xs st in aop_int o k xs' st'
  end.

(** * Memory *)

Definition byte_rng (st : astate) (b : abyte) : Z * Z :=
  match b with
  | BK z => (z, z)
  | BOf s i => let (lo, hi) := rng st (S s) in
               if lo =? hi then (byte_of lo i, byte_of lo i)
               else if (i =? 0) && (0 <=? lo) && (hi <? 256) then (lo, hi) else (0, 255)
  | BIn lo hi => (lo, hi)
  | _ => (0, 255)
  end.

Fixpoint win_const (ws : list abyte) : option Z :=
  match ws with
  | [] => Some 0
  | BK z :: ws' => let* r := win_const ws' in Some (z + 256 * r)
  | _ => None
  end.

Fixpoint win_sym (s : nat) (i : Z) (ws : list abyte) : bool :=
  match ws with
  | [] => true
  | BOf t j :: ws' => Nat.eqb s t && (i =? j) && win_sym s (i + 1) ws'
  | _ => false
  end.

Definition has_bx (ws : list abyte) : bool :=
  existsb (fun b => match b with BGuard _ | BEnd _ _ _ => true | _ => false end) ws.

(** A loaded integer inherits the flags of the bytes it was read from. *)
Definition load_flags (ws : list abyte) (w : Z) (t : nat) (st : astate) : astate :=
  let st1 := fst (fold_left (fun (acc : astate * Z) (b : abyte) =>
                               (match b with
                                | BGuard k =>
                                    if (0 <=? k) && (k <? 8) then add_flag (fst acc) t (FBit (8 * snd acc + k))
                                    else fst acc
                                | _ => fst acc
                                end, snd acc + 1)) ws (st, 0)) in
  match ws with
  | BEnd u key mask :: _ => if (0 <=? mask) && (mask <? 256) then add_flag st1 t (FEnd u key mask) else st1
  | _ => st1
  end.

Fixpoint sym_bytes (s : nat) (i : Z) (n : nat) : list abyte :=
  match n with O => [] | Datatypes.S n' => BOf s i :: sym_bytes s (i + 1) n' end.

Definition aint_bytes (a : aint) (w : nat) : list abyte :=
  match a with
  | K z => map (fun i => BK (byte_of z (Z.of_nat i))) (seq 0 w)
  | S s => sym_bytes s 0 w
  end.

(** Reading [w] bytes at an exact offset returns the unsigned integer they
    hold and, when that integer is a new symbol, the bytes that name it. *)
Definition load_exact (st : astate) (ws : list abyte) (w : Z) : aint * astate * option (list abyte) :=
  match win_const ws with
  | Some z => (K z, st, None)
  | None =>
      match ws with
      | BOf s 0 :: ws' =>
          let (lo, hi) := rng st (S s) in
          if win_sym s 1 ws' && (0 <=? lo) && (hi <? 2 ^ (8 * w)) then (S s, st, None)
          else let (t, st') := fresh st 0 (2 ^ (8 * w) - 1) in (S t, st', Some (sym_bytes t 0 (Z.to_nat w)))
      | [b] =>
          let (lo, hi) := byte_rng st b in
          let (t, st') := fresh st lo hi in
          (S t, load_flags ws w t st', match b with BGuard _ | BEnd _ _ _ => None | _ => Some [BOf t 0] end)
      | _ =>
          let (t, st') := fresh st 0 (2 ^ (8 * w) - 1) in
          if has_bx ws then
            (S t, load_flags ws w t st', None)
          else (S t, st', Some (sym_bytes t 0 (Z.to_nat w)))
      end
  end.

Definition load_size (t : load_type) : option Z :=
  match t with
  | LdL => Some 8
  | LdNarrow n => Some (fst (narrow_type n))
  | _ => None
  end.

(** A load binds the unsigned integer that the bytes hold, extended as the
    load's type says. *)
Definition load_ext (t : load_type) (k : class) (a : aint) (st : astate) : option (aval * astate) :=
  match t with
  | LdL => Some (VI a, st)
  | LdNarrow n =>
      let* m := modulus_of k in
      let (_, hi) := rng st a in
      let keep := match n with
                  | Uw | Uh | Ub => true
                  | Sw => match k with W => true | _ => hi <? 2 ^ 31 end
                  | Sh => hi <? 32768
                  | Sb => hi <? 128
                  end in
      if keep then Some (VI a, st)
      else let (r, st') := mk st 0 (m - 1) in Some (VI r, st')
  | _ => None
  end.

Definition aload (t : load_type) (k : class) (off : Z) (p : aval) (st : astate) : option (aval * astate) :=
  match p with
  | VP o a =>
      let* ob := get_obj st o in
      let* w := load_size t in
      let (lo, hi) := rng st a in
      if (0 <=? lo + off) && (hi + off + w <=? o_size ob) then
        if lo =? hi then
          let '(r, st1, back) := load_exact st (window (lo + off) w (o_bytes ob)) w in
          let st2 := match back with
                     | Some bs => put_obj st1 o (Some (mkObj (o_ro ob) (o_align ob)
                                                         (splice (lo + off) bs (o_bytes ob)) (o_aux ob)))
                     | None => st1
                     end in
          load_ext t k r st2
        else
          let (r, st1) := fresh st 0 (2 ^ (8 * w) - 1) in load_ext t k (S r) st1
      else None
  | _ => None
  end.

Definition store_width (w : width) : option Z :=
  match w with Wb => Some 1 | Ww => Some 4 | Wl => Some 8 | _ => None end.

Definition astore (w : width) (off : Z) (v p : aval) (st : astate) : option astate :=
  match p with
  | VP o a =>
      let* ob := get_obj st o in
      let* n := store_width w in
      let (lo, hi) := rng st a in
      if negb (o_ro ob) && (0 <=? lo + off) && (hi + off + n <=? o_size ob) then
        let? (x, st1) := match as_int v st with
                         | (VI x, st') => Some (x, st')
                         | _ => None
                         end in
        let bytes :=
          if lo =? hi then splice (lo + off) (aint_bytes x (Z.to_nat n)) (o_bytes ob)
          else splice (lo + off) (repeat BR (Z.to_nat (hi - lo + n))) (o_bytes ob) in
        Some (put_obj st1 o (Some (mkObj (o_ro ob) (o_align ob) bytes (o_aux ob))))
      else None
  | _ => None
  end.

Definition ptr_aux (v : aval) : option aaux :=
  match v with
  | VP o _ => Some (XObj o)
  | VN _ => Some XNone
  | VA | VF _ => Some XAny
  | _ => None
  end.

Definition astore_ptr (off : Z) (v p : aval) (st : astate) : option astate :=
  match p with
  | VP o a =>
      let* ob := get_obj st o in
      let* x := ptr_aux v in
      let (lo, hi) := rng st a in
      if negb (o_ro ob) && (lo =? hi) && (0 <=? lo + off) && (lo + off + 8 <=? o_size ob)
         && ((lo + off) mod 8 =? 0) && (o_align ob mod 8 =? 0) then
        Some (put_obj st o (Some (mkObj (o_ro ob) (o_align ob)
                                    (splice (lo + off) (repeat BR 8) (o_bytes ob))
                                    (splice (lo + off) [x] (o_aux ob)))))
      else None
  | _ => None
  end.

Definition aload_ptr (off : Z) (p : aval) (st : astate) : option (aval * astate) :=
  match p with
  | VP o a =>
      let* ob := get_obj st o in
      let (lo, hi) := rng st a in
      if (lo =? hi) && (0 <=? lo + off) && (lo + off + 8 <=? o_size ob)
         && ((lo + off) mod 8 =? 0) && (o_align ob mod 8 =? 0) then
        match nth (Z.to_nat (lo + off)) (o_aux ob) XAny with
        | XNone => Some (VA, st)
        | XObj o' => if Nat.eqb o o' then None
                     else match get_obj st o' with Some _ => Some (VA, st) | None => None end
        | XAny => None
        end
      else None
  | _ => None
  end.

(** A check passes when the access lies inside a live object that grants
    the requested rights at the requested alignment. *)
Definition acheck (lo hi : Z) (r : rights) (al : Z) (p : aval) (st : astate) : bool :=
  match p with
  | VP o a =>
      match get_obj st o with
      | Some ob =>
          let (alo, ahi) := rng st a in
          (0 <=? alo + lo) && (ahi + hi <=? o_size ob) && (lo <? hi)
          && (match r with Write => negb (o_ro ob) | Read => true end)
          && ((al =? 1) || ((alo =? ahi) && ((alo + lo) mod al =? 0) && (o_align ob mod al =? 0)
                            && (0 <? al)))
      | None => false
      end
  | _ => false
  end.

Definition same_obj (p q : aval) : bool :=
  match p, q with VP o _, VP o' _ => Nat.eqb o o' | _, _ => false end.

Definition signed64 (z : Z) : Z := if z <? 2 ^ 63 then z else z - 2 ^ 64.

Definition aflight (p x q : aval) (st : astate) : option (aval * astate) :=
  match x with
  | VI x =>
      let any := match p, q with
                 | (VP _ _ | VN _ | VA | VF _), (VP _ _ | VN _ | VA | VF _) => Some (VA, st)
                 | _, _ => None
                 end in
      match p, q with
      | VP o a, VP o' _ =>
          if Nat.eqb o o' then
            let (alo, ahi) := rng st a in
            let (xlo, xhi) := rng st x in
            let d := match x with K z => signed64 z | _ => 0 end in
            match a, x with
            | K z, K _ => if (0 <=? z + d) && (z + d <=? 2 ^ 62) then Some (VP o (K (z + d)), st) else any
            | _, K _ => if (0 <=? alo + d) && (ahi + d <=? 2 ^ 62) then
                          let (r, st') := mk st (alo + d) (ahi + d) in Some (VP o r, st')
                        else any
            | _, _ => if (0 <=? alo + xlo) && (ahi + xhi <=? 2 ^ 62) then
                        let (r, st') := mk st (alo + xlo) (ahi + xhi) in Some (VP o r, st')
                      else any
            end
          else any
      | _, _ => any
      end
  | _ => None
  end.

(** * Closed values *)

Definition close_val (st : astate) (v : aval) : cval :=
  match v with
  | VI a => let (lo, hi) := rng st a in CI lo hi
  | VC _ _ _ _ => CI 0 1
  | VJ => CJ
  | VP o a => let (lo, hi) := rng st a in CP o lo hi
  | VN a => let (lo, hi) := rng st a in CN lo hi
  | VA => CA
  | VF g => CF g
  end.

Definition val_le (st : astate) (v : aval) (c : cval) : bool :=
  match close_val st v, c with
  | CI lo hi, CI lo' hi' => (lo' <=? lo) && (hi <=? hi')
  | (CI _ _ | CJ), CJ => true
  | CP o lo hi, CP o' lo' hi' => Nat.eqb o o' && (lo' <=? lo) && (hi <=? hi')
  | CN lo hi, CN lo' hi' => (lo' <=? lo) && (hi <=? hi')
  | (CP _ _ _ | CN _ _ | CA | CF _), CA => true
  | CF g, CF g' => name_eqb g g'
  | _, _ => false
  end.

Definition open_val (c : cval) (st : astate) : aval * astate :=
  match c with
  | CI lo hi => let (a, st') := mk st lo hi in (VI a, st')
  | CJ => (VJ, st)
  | CP o lo hi => let (a, st') := mk st lo hi in (VP o a, st')
  | CN lo hi => let (a, st') := mk st lo hi in (VN a, st')
  | CA => (VA, st)
  | CF g => (VF g, st)
  end.

Definition byte_le (st : astate) (b t : abyte) : bool :=
  match t with
  | BR => true
  | BK z => let (lo, hi) := byte_rng st b in
            match b with BR | BGuard _ | BEnd _ _ _ => false | _ => (lo =? z) && (hi =? z) end
  | BIn lo' hi' => let (lo, hi) := byte_rng st b in (lo' <=? lo) && (hi <=? hi')
  | BGuard k => match b with
          | BGuard k' => k =? k'
          | _ => st_guard st || (let (lo, hi) := byte_rng st b in (0 <=? lo) && (hi <? 2 ^ k))
          end
  | BOf _ _ | BEnd _ _ _ => false
  end.

Definition aux_le (x t : aaux) : bool :=
  match t, x with
  | XAny, _ => true
  | XNone, XNone => true
  | XObj o, XObj o' => Nat.eqb o o'
  | _, _ => false
  end.

Fixpoint all2 {A B : Type} (f : A -> B -> bool) (xs : list A) (ys : list B) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => f x y && all2 f xs' ys'
  | _, _ => false
  end.

Definition obj_le (st : astate) (ob t : aobj) : bool :=
  Bool.eqb (o_ro ob) (o_ro t) && (o_align t <=? o_align ob) && (o_align ob mod o_align t =? 0)
  && all2 (byte_le st) (o_bytes ob) (o_bytes t) && all2 aux_le (o_aux ob) (o_aux t).

Definition close_byte (st : astate) (b : abyte) : abyte :=
  match b with
  | BOf s i => if i =? 0 then
                 let (lo, hi) := rng st (S s) in
                 if (0 <=? lo) && (hi <? 256) then (if lo =? hi then BK lo else BIn lo hi) else BR
               else let (lo, hi) := rng st (S s) in if lo =? hi then BK (byte_of lo i) else BR
  | BEnd _ _ _ => BR
  | _ => b
  end.

Definition close_obj (st : astate) (ob : aobj) : aobj :=
  mkObj (o_ro ob) (o_align ob) (map (close_byte st) (o_bytes ob)) (o_aux ob).

Definition open_byte (b : abyte) : abyte := match b with BOf _ _ | BEnd _ _ _ => BR | _ => b end.

Definition open_obj (ob : aobj) : aobj :=
  mkObj (o_ro ob) (o_align ob) (map open_byte (o_bytes ob)) (o_aux ob).

(** * Entailment of a closed state *)

Fixpoint objs_le (st : astate) (os ts : list (option aobj)) : bool :=
  match ts, os with
  | [], _ => true
  | None :: ts', _ :: os' => objs_le st os' ts'
  | Some t :: ts', Some ob :: os' => obj_le st ob t && objs_le st os' ts'
  | _, _ => false
  end.

Definition env_le (st : astate) (te : list (name * cval)) : bool :=
  forallb (fun nc => match lookup (fst nc) (st_env st) with
                     | Some v => val_le st v (snd nc)
                     | None => false
                     end) te.

Definition entails (st : astate) (t : cstate) : bool :=
  env_le st (cs_env t) && objs_le st (st_objs st) (cs_objs t) && (implb (cs_guard t) (st_guard st)).

(** A closed state may describe fewer objects than the state that
    entails it, and the objects beyond its list are then forgotten. It
    must not mention a forgotten object, and it must keep the first
    [n0] objects, which are the ones the function was given. *)
Definition cval_in (n : nat) (c : cval) : bool := match c with CP o _ _ => Nat.ltb o n | _ => true end.

Definition aux_in (n : nat) (x : aaux) : bool := match x with XObj o => Nat.ltb o n | _ => true end.

Definition cstate_ok (n0 : nat) (t : cstate) : bool :=
  let n := length (cs_objs t) in
  Nat.leb n0 n && forallb (fun nc => cval_in n (snd nc)) (cs_env t)
  && forallb (fun o => match o with Some ob => forallb (aux_in n) (o_aux ob) | None => true end) (cs_objs t).

Fixpoint open_env (te : list (name * cval)) (st : astate) : astate :=
  match te with
  | [] => st
  | (n, c) :: te' =>
      let st1 := open_env te' st in
      let (v, st2) := open_val c st1 in
      bind st2 n v
  end.

Definition open_state (t : cstate) : astate :=
  open_env (cs_env t) (mkSt [] [] [] [] (map (option_map open_obj) (cs_objs t)) (cs_guard t)).

(** * Calls *)

(** A call is matched against one specification of the callee. Object
    [nglob + j] of the specification is the object that argument [j] points to. *)
Definition arg_obj (st : astate) (args : list aval) (i : nat) : option nat :=
  if Nat.ltb i nglob then Some i
  else match nth_error args (i - nglob) with
       | Some (VP o _) => Some o
       | _ => None
       end.

Definition arg_le (st : astate) (j : nat) (v : aval) (c : cval) : bool :=
  match c, v with
  | CP o lo hi, VP o' a =>
      let (alo, ahi) := rng st a in
      (lo <=? alo) && (ahi <=? hi) && (if Nat.ltb o nglob then Nat.eqb o o' else Nat.eqb o (nglob + j))
  | CP _ _ _, _ => false
  | _, _ => val_le st v c
  end.

Fixpoint args_le (st : astate) (j : nat) (vs : list aval) (cs : list cval) : bool :=
  match vs, cs with
  | [], [] => true
  | v :: vs', c :: cs' => arg_le st j v c && args_le st (Datatypes.S j) vs' cs'
  | _, _ => false
  end.

Definition aux_global (x : aaux) : bool :=
  match x with XObj o => Nat.ltb o nglob | _ => true end.

(** A call takes the objects that the specification names out of the
    caller's state, and it gives them back as the postcondition describes. *)
Fixpoint take_objs (st : astate) (args : list aval) (i : nat) (pre : list (option aobj))
  : option astate :=
  match pre with
  | [] => Some st
  | None :: pre' => take_objs st args (Datatypes.S i) pre'
  | Some t :: pre' =>
      let* o := arg_obj st args i in
      let* ob := get_obj st o in
      if obj_le st ob t && forallb aux_global (o_aux t) then
        take_objs (put_obj st o None) args (Datatypes.S i) pre'
      else None
  end.

Fixpoint give_objs (st : astate) (args : list aval) (i : nat) (post : list (option aobj))
  : option astate :=
  match post with
  | [] => Some st
  | None :: post' => give_objs st args (Datatypes.S i) post'
  | Some t :: post' =>
      let* o := arg_obj st args i in
      if Nat.ltb o (length (st_objs st)) && forallb aux_global (o_aux t) then
        give_objs (put_obj st o (Some (open_obj t))) args (Datatypes.S i) post'
      else None
  end.

Definition same_shape (pre post : list (option aobj)) : bool :=
  all2 (fun p q => match p, q with None, None | Some _, Some _ => true | _, _ => false end) pre post.

Definition bind_result (r : call_result) (ret : option cval) (st : astate) : option astate :=
  match r, ret with
  | CVoid, _ => Some st
  | CResult d k, Some c =>
      if match c with CP o _ _ => negb (Nat.ltb o nglob) | _ => false end then None else
      let (v, st1) := open_val c st in
      let? (v', st2) := tmp_at k v st1 in
      Some (bind st2 d v')
  | _, _ => None
  end.

(** A specification is usable when it names one object for every
    global and one for every argument, when its postcondition describes
    the same objects as its precondition, and when every capability
    and every returned pointer that it mentions belongs to a global. *)
Definition obj_global (o : option aobj) : bool :=
  match o with Some t => forallb aux_global (o_aux t) | None => true end.

Definition spec_ok (sp : fspec) : bool :=
  Nat.eqb (length (sp_pre sp)) (nglob + length (sp_args sp)) && same_shape (sp_pre sp) (sp_post sp)
  && forallb obj_global (sp_pre sp) && forallb obj_global (sp_post sp)
  && match sp_ret sp with Some (CP o _ _) => Nat.ltb o nglob | _ => true end.

Definition call_spec (r : call_result) (args : list aval) (st : astate) (sp : fspec) : option astate :=
  if args_le st 0 args (sp_args sp) && implb (sp_guard sp) (st_guard st) && spec_ok sp then
    let* st1 := take_objs st args 0 (sp_pre sp) in
    let* st2 := give_objs st1 args 0 (sp_post sp) in
    bind_result r (sp_ret sp) (set_guard st2 (st_guard st2 || sp_guard' sp))
  else None.

Fixpoint first_spec (r : call_result) (args : list aval) (st : astate) (sps : list fspec) : option astate :=
  match sps with
  | [] => None
  | sp :: sps' => match call_spec r args st sp with
                  | Some st' => Some st'
                  | None => first_spec r args st sps'
                  end
  end.

Definition arg_classes (args : list arg) : list class := map (fun a => match a with Arg k _ => k end) args.
Definition arg_values (args : list arg) : list value := map (fun a => match a with Arg _ v => v end) args.

(** A call first asks [builtin], which answers for the functions that
    have no body. Any other call needs a specification of the callee. *)
Definition acall (r : call_result) (g : name) (args : list arg) (st : astate) : option astate :=
  let? (xs, st1) := avalues (arg_classes args) (arg_values args) st in
  match builtin g r (arg_classes args) xs st1 with
  | Some res => res
  | None => first_spec r xs st1 (specs g)
  end.

(** * Instructions *)

Definition new_obj (al size : Z) : aobj :=
  let n := Z.to_nat ((size + 15) / 16 * 16) in
  mkObj false (Z.max al 16) (repeat (BK 0) n) (repeat XNone n).

Definition ainst (i : inst) (st : astate) : option astate :=
  match i with
  | Let d k o args =>
      match o with
      | Alloc al =>
          let? (xs, st1) := avalues [L] args st in
          match xs with
          | [VI (K n)] =>
              if (0 <=? n) && (n <? 2 ^ 32) then
                Some (bind (set_objs st1 (st_objs st1 ++ [Some (new_obj al n)])) d
                        (VP (length (st_objs st1)) (K 0)))
              else None
          | _ => None
          end
      | Check lo hi r al =>
          let? (xs, st1) := avalues [P] args st in
          match k, xs with
          | A, [p] => if acheck lo hi r al p st1 then Some (bind st1 d p) else None
          | _, _ => None
          end
      | HalfCheck _ lo hi r al | Renew lo hi r al =>
          let? (xs, st1) := avalues [A; P] args st in
          match k, xs with
          | A, [q; p] => if same_obj q p && acheck lo hi r al p st1 then Some (bind st1 d p) else None
          | _, _ => None
          end
      | RawLoad t off =>
          let? (xs, st1) := avalues [A] args st in
          match xs with
          | [p] => let? (v, st2) := aload t k off p st1 in Some (bind st2 d v)
          | _ => None
          end
      | RawLoadPointer off [AuxRead; LowerResolve; AddressRead] =>
          let? (xs, st1) := avalues [A] args st in
          match k, xs with
          | P, [p] => let? (v, st2) := aload_ptr off p st1 in Some (bind st2 d v)
          | _, _ => None
          end
      | CheckFunction =>
          match k, args with
          | F, [v] =>
              let? (x, st1) := avalue P v st in
              match x with VF g => Some (bind st1 d x) | _ => None end
          | _, _ => None
          end
      | Add | Sub | Mul | Div | Udiv | And | Or | Xor | Shr | Shl | Neg | Copy | Ptoi
      | Cmp _ _ | Ext _ =>
          let* classes := op_arg_classes o k in
          let? (xs, st1) := avalues classes args st in
          let? (v, st2) := aop o k xs st1 in
          Some (bind st2 d v)
      | _ => None
      end
  | Flight d Add [FAddress p; FValue x] (LowerOf q) =>
      let? (pv, st1) := avalue P p st in
      let? (xv, st2) := avalue L x st1 in
      let? (qv, st3) := avalue P q st2 in
      let? (v, st4) := aflight pv xv qv st3 in
      Some (bind st4 d v)
  | RawStore w off v a =>
      let* vk := width_value_class w in
      let? (x, st1) := avalue vk v st in
      let? (p, st2) := avalue A a st1 in
      astore w off x p st2
  | RawStorePointer off v a [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite] =>
      let? (x, st1) := avalue P v st in
      let? (p, st2) := avalue A a st1 in
      astore_ptr off x p st2
  | Call r (Global g) args => acall r g args st
  | RawCall r callee args =>
      let? (c, st1) := avalue F callee st in
      match c with
      | VF g =>
          let* sg := lookup g fnames in
          if all2 class_eqb (arg_classes args) (fst sg) && forallb class_plain (fst sg)
             && same_words (result_words r) (return_words (snd sg)) then
            let? (xs, st2) := avalues (arg_classes args) (arg_values args) st1 in
            first_spec r xs st2 (specs g)
          else None
      | _ => None
      end
  | _ => None
  end.

Fixpoint ainsts (ins : list inst) (st : astate) : option astate * option inst :=
  match ins with
  | [] => (Some st, None)
  | i :: ins' => match ainst i st with
                | Some st' => ainsts ins' st'
                | None => (None, Some i)
                end
  end.

(** * Blocks *)

Inductive leaf : Type :=
| LCut (l : name) (st : astate)
| LRet (v : option aval) (st : astate)
| LFail (l : name) (i : option inst) (st : astate).

Definition abranch (v : aval) (st : astate) : option (option astate * option astate) :=
  match v with
  | VI a => Some (let* st' := ref_ne st a (K 0) in note_nonzero st' a, ref_eq st a (K 0))
  | VC c k a b => Some (refine st c k a b true, refine st c k a b false)
  | _ => None
  end.

Definition aphis (phis : list phi) (from : option name) (st : astate) : option astate :=
  match from with
  | None => match phis with [] => Some st | _ => None end
  | Some pred =>
      let? (e, st') :=
        fold_left (fun acc ph =>
                     let? (e, st') := acc in
                     match ph with
                     | Phi d k pairs =>
                         let* v := lookup pred pairs in
                         let? (x, st2) := avalue k v (set_env st' (st_env st)) in
                         Some ((d, x) :: e, st2)
                     end) phis (Some (st_env st, st)) in
      Some (set_env st' e)
  end.

Section fn.
Variable f : func.
Variable cuts : list name.

Fixpoint run (fuel : nat) (l : name) (from : option name) (st : astate) : list leaf :=
  match fuel with
  | O => [LFail l None st]
  | Datatypes.S fuel' =>
      match find_block l (fn_blocks f) with
      | None => [LFail l None st]
      | Some b =>
          match aphis (b_phis b) from st with
          | None => [LFail l None st]
          | Some st1 =>
              if mem_name l cuts && match from with Some _ => true | None => false end
              then [LCut l st1]
              else body fuel' l (b_insts b) (b_jump b) st1
          end
      end
  end
with body (fuel : nat) (l : name) (ins : list inst) (j : jump) (st : astate) : list leaf :=
  match fuel with
  | O => [LFail l None st]
  | Datatypes.S fuel' =>
      match ainsts ins st with
      | (None, i) => [LFail l i st]
      | (Some st1, _) =>
          match j with
          | JGoto t => run fuel' (edge_label t) (Some l) st1
          | JBranch v t1 t2 =>
              match avalue W v st1 with
              | Some (x, st2) =>
                  match abranch x st2 with
                  | Some (yes, no) =>
                      (match yes with Some s => run fuel' (edge_label t1) (Some l) s | None => [] end)
                      ++ (match no with Some s => run fuel' (edge_label t2) (Some l) s | None => [] end)
                  | None => [LFail l None st2]
                  end
              | None => [LFail l None st1]
              end
          | JRet v =>
              match fn_ret f with
              | RClass k => match avalue k v st1 with
                            | Some (x, st2) => [LRet (Some x) st2]
                            | None => [LFail l None st1]
                            end
              | _ => [LFail l None st1]
              end
          | JRetVoid => [LRet None st1]
          | _ => [LFail l None st1]
          end
      end
  end.

End fn.
End exec.
