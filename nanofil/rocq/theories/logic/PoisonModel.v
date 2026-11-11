(** Cryptographic code must not branch on secret values, index memory by
    secret offsets, or feed secret operands to variable-time instructions.
    This module models Zegarmistrz's [[poison]] and taint rules over
    nanofil's [[stage|checked IR]] so constant-time guarantees can be
    proved on the same representation as memory safety.

    Every runtime word carries three independent taint bits that forbid
    branches, memory indexing, and variable-time arithmetic, while every
    memory byte records load or store poison alongside sticky or
    overwritable taint. The instrumented operational semantics steps in
    lockstep with the standard IR interpreter without changing program
    values, so any run that avoids poison faults produces the same
    observable control-flow and address trace on all secret inputs. *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Maps Ieee Syntax Values Memory Runtime Ops Semantics Machine Panics.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

(** ## The three-bit taint lattice

    A secret may be unsafe for branching, indexing, or variable-time
    arithmetic. The [[poison]] model tracks these restrictions separately
    and combines them when an operation consumes several inputs. *)

(** Each taint records whether a value is forbidden in control flow,
    memory addresses, or variable-latency operations. *)
Record taint : Type := mkTaint {
  t_branch : bool;
  t_index : bool;
  t_vartime : bool
}.

(** A clean value has no restrictions. *)
Definition taint_bot : taint := mkTaint false false false.

(** This taint forbids branching on a value. *)
Definition taint_branch : taint := mkTaint true false false.

(** This taint forbids indexing memory with a value. *)
Definition taint_index : taint := mkTaint false true false.

(** This taint forbids variable-time operations on a value. *)
Definition taint_vartime : taint := mkTaint false false true.

(** Fully secret values carry all three restrictions. *)
Definition taint_all : taint := mkTaint true true true.

(** The equality test compares all three restrictions. *)
Definition taint_eqb (a b : taint) : bool :=
  Bool.eqb (t_branch a) (t_branch b) &&
  Bool.eqb (t_index a) (t_index b) &&
  Bool.eqb (t_vartime a) (t_vartime b).

(** Combining two taints keeps every restriction from either input. *)
Definition taint_join (a b : taint) : taint :=
  mkTaint (t_branch a || t_branch b)
          (t_index a || t_index b)
          (t_vartime a || t_vartime b).

(** One taint is below another when the latter includes all its restrictions. *)
Definition taint_le (a b : taint) : bool :=
  implb (t_branch a) (t_branch b) &&
  implb (t_index a) (t_index b) &&
  implb (t_vartime a) (t_vartime b).

(** [taint_eqb] reflects equality. *)
Lemma taint_eqb_eq : forall a b, taint_eqb a b = true <-> a = b.
Proof.
  intros [b1 i1 v1] [b2 i2 v2]; unfold taint_eqb; cbn.
  destruct b1, b2, i1, i2, v1, v2; split; intros H; try reflexivity; discriminate.
Qed.

(** Joining with [taint_bot] on the left is the identity. *)
Lemma taint_join_bot_l : forall t, taint_join taint_bot t = t.
Proof. intros [b i v]; reflexivity. Qed.

(** Joining with [taint_bot] on the right is the identity. *)
Lemma taint_join_bot_r : forall t, taint_join t taint_bot = t.
Proof. intros [b i v]; unfold taint_join; cbn; rewrite !orb_false_r; reflexivity. Qed.

(** [taint_join] is commutative. *)
Lemma taint_join_comm : forall a b, taint_join a b = taint_join b a.
Proof.
  intros [b1 i1 v1] [b2 i2 v2]; unfold taint_join; cbn.
  rewrite (orb_comm b1), (orb_comm i1), (orb_comm v1); reflexivity.
Qed.

(** [taint_join] is associative. *)
Lemma taint_join_assoc : forall a b c,
  taint_join (taint_join a b) c = taint_join a (taint_join b c).
Proof.
  intros [b1 i1 v1] [b2 i2 v2] [b3 i3 v3]; unfold taint_join; cbn.
  rewrite !orb_assoc; reflexivity.
Qed.

(** [taint_join] is idempotent. *)
Lemma taint_join_idem : forall t, taint_join t t = t.
Proof. intros [b i v]; unfold taint_join; cbn; rewrite !orb_diag; reflexivity. Qed.

(** [taint_all] absorbs on the left. *)
Lemma taint_join_all_l : forall t, taint_join taint_all t = taint_all.
Proof. intros [b i v]; reflexivity. Qed.

(** [taint_all] absorbs on the right. *)
Lemma taint_join_all_r : forall t, taint_join t taint_all = taint_all.
Proof. intros [b i v]; unfold taint_join; cbn; rewrite !orb_true_r; reflexivity. Qed.

(** [taint_le] is reflexive. *)
Lemma taint_le_refl : forall t, taint_le t t = true.
Proof. intros [b i v]; destruct b, i, v; reflexivity. Qed.

(** [taint_le] is transitive. *)
Lemma taint_le_trans : forall a b c,
  taint_le a b = true -> taint_le b c = true -> taint_le a c = true.
Proof.
  intros [b1 i1 v1] [b2 i2 v2] [b3 i3 v3]; destruct b1, i1, v1, b2, i2, v2, b3, i3, v3; auto.
Qed.

(** [taint_join] is the least upper bound for [taint_le]. *)
Lemma taint_join_lub : forall a b c,
  taint_le (taint_join a b) c = (taint_le a c && taint_le b c).
Proof.
  intros [b1 i1 v1] [b2 i2 v2] [b3 i3 v3]; destruct b1, i1, v1, b2, i2, v2, b3, i3, v3; reflexivity.
Qed.

(** ## Word taints

    A [[word]] may hold an integer, a pointer, or a limit snapshot.
    Pointer values need separate restrictions for their address and
    [[capability]], because those parts can come from different sources. *)

(** Integers and floats carry one taint. Pointers carry separate taints
    for the address in primary memory and the capability in [[aux]]. *)
Inductive word_taint : Type :=
| WTInt (t : taint)
| WTPtr (t_addr : taint) (t_cap : taint)
| WTLimit (t_cap : taint) (t_lim : taint).

(** Each value class has a matching unrestricted taint. *)
Definition wt_bot (k : class) : word_taint :=
  match k with
  | P | A | F => WTPtr taint_bot taint_bot
  | _ => WTInt taint_bot
  end.

(** The equality test compares word taints with matching shapes. *)
Definition wt_eqb (x y : word_taint) : bool :=
  match x, y with
  | WTInt a, WTInt b => taint_eqb a b
  | WTPtr a1 c1, WTPtr a2 c2 => taint_eqb a1 a2 && taint_eqb c1 c2
  | WTLimit c1 l1, WTLimit c2 l2 => taint_eqb c1 c2 && taint_eqb l1 l2
  | _, _ => false
  end.

(** The ordering compares restrictions of word taints with matching shapes. *)
Definition wt_le (x y : word_taint) : bool :=
  match x, y with
  | WTInt a, WTInt b => taint_le a b
  | WTPtr a1 c1, WTPtr a2 c2 => taint_le a1 a2 && taint_le c1 c2
  | WTLimit c1 l1, WTLimit c2 l2 => taint_le c1 c2 && taint_le l1 l2
  | _, _ => false
  end.

(** Combining word taints keeps restrictions from both inputs.
    Mismatched shapes produce a fully restricted result. *)
Definition wt_join (x y : word_taint) : word_taint :=
  match x, y with
  | WTInt a, WTInt b => WTInt (taint_join a b)
  | WTPtr a1 c1, WTPtr a2 c2 => WTPtr (taint_join a1 a2) (taint_join c1 c2)
  | WTLimit c1 l1, WTLimit c2 l2 => WTLimit (taint_join c1 c2) (taint_join l1 l2)
  | _, _ => WTInt taint_all
  end.

(** Reading a word at a class preserves its taint when the shapes match. *)
Definition wt_at_class (k : class) (wt : word_taint) : option word_taint :=
  match k, wt with
  | (W | L | Single | Double | Extended), WTInt t => Some (WTInt t)
  | L, WTLimit _ _ => Some wt
  | (P | A | F), WTPtr _ _ => Some wt
  | (P | A | F), WTInt t => Some (WTInt t)
  | _, _ => None
  end.

(** ## Per-byte memory poison and clear-on-store

    Memory can forbid loads and stores as well as restrict loaded values.
    A [[poison]] byte also records whether a later clean store may clear
    restrictions introduced by an earlier store. *)

(** A memory byte records load and store prohibitions, value restrictions,
    and flags that allow later stores to clear those restrictions. *)
Record poison_byte : Type := mkPoisonByte {
  pb_no_load : bool;
  pb_no_store : bool;
  pb_clear_branch : bool;
  pb_clear_index : bool;
  pb_clear_vartime : bool;
  pb_taint : taint
}.

(** A clean byte permits loads and stores and carries no value restrictions. *)
Definition pb_clean : poison_byte :=
  mkPoisonByte false false false false false taint_bot.

(** A secret byte keeps its original restrictions across clean stores.
    This models the key buffers in `simple-openssl-tests`. *)
Definition pb_secret (t : taint) : poison_byte :=
  mkPoisonByte false false false false false t.

(** Poisoning a range adds the supplied restrictions to every byte. *)
Definition poison_range (pm : Z -> poison_byte) (a size : Z) (pb : poison_byte)
  : Z -> poison_byte :=
  fun b =>
    if (a <=? b) && (b <? a + size) then
      let old := pm b in
      mkPoisonByte
        (pb_no_load old || pb_no_load pb)
        (pb_no_store old || pb_no_store pb)
        (pb_clear_branch old || pb_clear_branch pb)
        (pb_clear_index old || pb_clear_index pb)
        (pb_clear_vartime old || pb_clear_vartime pb)
        (taint_join (pb_taint old) (pb_taint pb))
    else pm b.

(** Unpoisoning a range erases all restrictions in its bytes. *)
Definition unpoison_range (pm : Z -> poison_byte) (a size : Z) : Z -> poison_byte :=
  fun b => if (a <=? b) && (b <? a + size) then pb_clean else pm b.

(** Allocation clears capability taint throughout the new object's range,
    just as it clears the capabilities stored in shadow memory. *)
Definition unpoison_aux (paux : Z -> taint) (a size : Z) : Z -> taint :=
  fun b => if (a <=? b) && (b <? a + size) then taint_bot else paux b.

(** Storing a restricted value sets its restriction and permits a later
    clean store to clear it. A clean store otherwise keeps sticky restrictions. *)
Definition note_dim (stored old_taint old_clear : bool) : bool * bool :=
  if stored then (true, true)
  else (if old_clear then false else old_taint, old_clear).

(** The repaired store rule updates each value restriction independently.
    It preserves load and store prohibitions and existing clearing flags. *)
Definition note_store_byte (t : taint) (old : poison_byte) : poison_byte :=
  let (nb, cb) := note_dim (t_branch t) (t_branch (pb_taint old)) (pb_clear_branch old) in
  let (ni, ci) := note_dim (t_index t) (t_index (pb_taint old)) (pb_clear_index old) in
  let (nv, cv) := note_dim (t_vartime t) (t_vartime (pb_taint old)) (pb_clear_vartime old) in
  mkPoisonByte (pb_no_load old) (pb_no_store old) cb ci cv (mkTaint nb ni nv).

(** This definition transcribes zegarmistrz's unpatched `mem_note_store`
    loop in `src/mem.cpp`. When [t] has any bit set, storing
    `true` into a byte that already carries `clear_on_store` clears the
    taint bit instead of keeping it, and storing `false` in another
    dimension skips sanitization. *)
Definition note_store_byte_buggy (t : taint) (old : poison_byte) : poison_byte :=
  let cb := t_branch t in
  let ci := t_index t in
  let cv := t_vartime t in
  if negb (cb || ci || cv) then note_store_byte taint_bot old
  else
    let '(nb, clb) :=
      if cb then
        if pb_clear_branch old then (false, pb_clear_branch old)
        else (true, true)
      else (t_branch (pb_taint old), pb_clear_branch old) in
    let '(ni, cli) :=
      if ci then
        if pb_clear_index old then (false, pb_clear_index old)
        else (true, true)
      else (t_index (pb_taint old), pb_clear_index old) in
    let '(nv, clv) :=
      if cv then
        if pb_clear_vartime old then (false, pb_clear_vartime old)
        else (true, true)
      else (t_vartime (pb_taint old), pb_clear_vartime old) in
    mkPoisonByte (pb_no_load old) (pb_no_store old) clb cli clv (mkTaint nb ni nv).

(** Storing a value tainted in `cannot_branch` always leaves the
    destination byte tainted in `cannot_branch`. *)
Lemma note_store_tainted_branch : forall t old,
  t_branch t = true -> t_branch (pb_taint (note_store_byte t old)) = true.
Proof.
  intros [b i v] [nl ns cb ci cv [ob oi ov]] Hb; cbn in Hb; subst b;
    destruct i, v, cb, ci, cv, ob, oi, ov; reflexivity.
Qed.

(** Storing [taint_all] always leaves [taint_all] on the byte. *)
Lemma note_store_all : forall old,
  pb_taint (note_store_byte taint_all old) = taint_all.
Proof.
  intros [nl ns cb ci cv [ob oi ov]]; reflexivity.
Qed.

(** Storing the same taint twice is idempotent under [note_store_byte]. *)
Lemma note_store_idempotent : forall t old,
  note_store_byte t (note_store_byte t old) = note_store_byte t old.
Proof.
  intros [b i v] [nl ns cb ci cv [ob oi ov]];
    destruct b, i, v, cb, ci, cv, ob, oi, ov; reflexivity.
Qed.

(** Storing clean data into a clear-on-store byte clears its taint. *)
Lemma note_store_clean_sanitizes : forall old,
  pb_clear_branch old = true ->
  pb_clear_index old = true ->
  pb_clear_vartime old = true ->
  pb_taint (note_store_byte taint_bot old) = taint_bot.
Proof.
  intros [nl ns cb ci cv tb] Hb Hi Hv; cbn in *; subst cb ci cv; reflexivity.
Qed.

(** Storing clean data into a sticky secret byte preserves its restrictions.
    A later reload remains secret. *)
Lemma note_store_sticky_launders : forall old,
  pb_clear_branch old = false ->
  pb_clear_index old = false ->
  pb_clear_vartime old = false ->
  pb_taint (note_store_byte taint_bot old) = pb_taint old.
Proof.
  intros [nl ns cb ci cv [b i v]] Hb Hi Hv; cbn in *; subst cb ci cv; reflexivity.
Qed.

(** The buggy rule clears the branch restriction after storing a
    branch-tainted value twice to a clean spill slot. Subsequent tainted
    stores incorrectly keep it cleared. *)
Lemma buggy_double_store_toggles :
  t_branch (pb_taint
    (note_store_byte_buggy taint_branch
      (note_store_byte_buggy taint_branch pb_clean))) = false.
Proof. reflexivity. Qed.

(** An ordinary writable byte permits loads and stores. Each active
    restriction can be cleared by a later clean store, so the next store
    replaces the byte's value restrictions. *)
Definition pb_normal (pb : poison_byte) : bool :=
  negb (pb_no_load pb) && negb (pb_no_store pb) &&
  implb (t_branch (pb_taint pb)) (pb_clear_branch pb) &&
  implb (t_index (pb_taint pb)) (pb_clear_index pb) &&
  implb (t_vartime (pb_taint pb)) (pb_clear_vartime pb).

(** Clean bytes satisfy [pb_normal]. *)
Lemma pb_normal_clean : pb_normal pb_clean = true.
Proof. reflexivity. Qed.

(** Storing any taint into a [pb_normal] byte preserves [pb_normal]. *)
Lemma pb_normal_store : forall tv pb,
  pb_normal pb = true -> pb_normal (note_store_byte tv pb) = true.
Proof.
  intros [b i v] [nl ns cb ci cv [ob oi ov]] H.
  destruct nl, ns, cb, ci, cv, ob, oi, ov, b, i, v; cbn in *; try discriminate H; reflexivity.
Qed.

(** Storing any taint [tv] into a [pb_normal] byte sets its [pb_taint]
    to [tv]. *)
Lemma pb_normal_taint : forall tv pb,
  pb_normal pb = true -> pb_taint (note_store_byte tv pb) = tv.
Proof.
  intros [b i v] [nl ns cb ci cv [ob oi ov]] H.
  destruct nl, ns, cb, ci, cv, ob, oi, ov, b, i, v; cbn in *; try discriminate H; reflexivity.
Qed.

(** A range forbids loading if any of its bytes forbids loading. *)
Fixpoint range_no_load_nat (pm : Z -> poison_byte) (a : Z) (n : nat) : bool :=
  match n with
  | O => false
  | S n' => pb_no_load (pm a) || range_no_load_nat pm (a + 1) n'
  end.

(** A range forbids storing if any of its bytes forbids storing. *)
Fixpoint range_no_store_nat (pm : Z -> poison_byte) (a : Z) (n : nat) : bool :=
  match n with
  | O => false
  | S n' => pb_no_store (pm a) || range_no_store_nat pm (a + 1) n'
  end.

(** A range carries every value restriction found in any of its bytes. *)
Fixpoint range_taint_nat (pm : Z -> poison_byte) (a : Z) (n : nat) : taint :=
  match n with
  | O => taint_bot
  | S n' => taint_join (pb_taint (pm a)) (range_taint_nat pm (a + 1) n')
  end.

(** The load test checks every byte in the requested range. *)
Definition mem_no_load (pm : Z -> poison_byte) (a size : Z) : bool :=
  range_no_load_nat pm a (Z.to_nat size).

(** The store test checks every byte in the requested range. *)
Definition mem_no_store (pm : Z -> poison_byte) (a size : Z) : bool :=
  range_no_store_nat pm a (Z.to_nat size).

(** A load combines the value restrictions of all bytes it reads. *)
Definition mem_load_taint (pm : Z -> poison_byte) (a size : Z) : taint :=
  range_taint_nat pm a (Z.to_nat size).

(** A store updates restrictions only within the range it writes. *)
Definition mem_store_taint (pm : Z -> poison_byte) (a size : Z) (t : taint)
  : Z -> poison_byte :=
  fun b => if (a <=? b) && (b <? a + size) then note_store_byte t (pm b) else pm b.

(** ## Policies and variable-latency operations

    A [[poison]] policy selects which operations must reject secret inputs.
    It also states whether capability checks expose branches, as native
    Fil-C checks do. *)

(** Zegarmistrz provides three levels of variable-time checking. *)
Inductive vartime_mode : Type :=
| VTKnown
| VTPlausible
| VTEverything.

(** Each checking level includes the levels below it. *)
Definition mode_at_least (m req : vartime_mode) : bool :=
  match m, req with
  | VTEverything, _ => true
  | VTPlausible, (VTKnown | VTPlausible) => true
  | VTKnown, VTKnown => true
  | _, _ => false
  end.

(** A policy selects a variable-time checking level and decides whether
    bounds checks reject secret pointers. Native x86-64 bounds checks
    expose branches and therefore require this restriction. *)
Record poison_policy : Type := mkPolicy {
  pol_vartime : vartime_mode;
  pol_check_branches : bool
}.

(** The default policy matches native zegarmistrz on checked Fil-C code. *)
Definition pol_default : poison_policy := mkPolicy VTKnown true.

(** The strict policy enables every variable-time check and native check branches. *)
Definition pol_strict : poison_policy := mkPolicy VTEverything true.

(** The erased policy assumes that static proofs have discharged bounds checks. *)
Definition pol_erased : poison_policy := mkPolicy VTKnown false.

(** A fault identifies the poison rule that rejected a step. *)
Inductive poison_reason : Type :=
| PoisonLoad
| PoisonStore
| CannotBranch
| CannotIndex
| CannotVarTimeOp.

(** The classifier assigns an IR operation to a variable-time checking level.
    Integer addition, subtraction, multiplication, bitwise logic, integer
    comparisons, and branchless selection need no such check in this model. *)
Definition op_vartime_class (o : op) (k : class) : option vartime_mode :=
  match o with
  | Div | Udiv | Rem | Urem => Some VTKnown
  | Add | Sub | Mul => if float_class k then Some VTKnown else None
  | Sqrt | ExtF _ | Truncd | Truncx | FloatToInt _ _ => Some VTKnown
  | Cmp _ ck => if float_class ck then Some VTPlausible else None
  | RawCas _ _ => Some VTPlausible
  | IntToFloat _ _ => Some VTEverything
  | _ => None
  end.

(** An operation checks its operands when the policy enables its checking level. *)
Definition op_checks_vartime (pol : poison_policy) (o : op) (k : class) : bool :=
  match op_vartime_class o k with
  | Some req => mode_at_least (pol_vartime pol) req
  | None => false
  end.

(** ## Taint environments and instrumented states

    The instrumented machine keeps value restrictions alongside ordinary
    [[word|words]]. Its shadow state follows registers, suspended callers,
    memory bytes, and capability slots. *)

(** The taint environment records restrictions on SSA temporaries. *)
Definition tenv := list (name * word_taint).

(** Each machine configuration has a matching shadow poison state. *)
Record pstate : Type := mkPState {
  ps_tenv : tenv;
  ps_callers : list (tenv * call_result);
  ps_mem : Z -> poison_byte;
  ps_aux : Z -> taint
}.

(** Read the taint of IR operand [v] at class [k] in [te]. Constants and
    global symbol addresses are untainted. *)
Definition value_t (te : tenv) (k : class) (v : value) : option word_taint :=
  match v with
  | Tmp n => let* wt := lookup n te in wt_at_class k wt
  | Const _ => Some (wt_bot k)
  | Global _ => Some (WTPtr taint_bot taint_bot)
  end.

(** Read a call argument's taint at its declared class. *)
Definition arg_t (te : tenv) (a : arg) : option word_taint :=
  match a with Arg k v => value_t te k v end.

(** Read a [[flight]] argument's scalar taint: `address(P)` projects the
    pointer's address taint; a plain value is read at class `l`. *)
Definition flight_arg_t (te : tenv) (a : flight_arg) : option taint :=
  match a with
  | FAddress v =>
      let* wt := value_t te P v in
      match wt with WTPtr ta _ | WTInt ta => Some ta | _ => None end
  | FValue v =>
      let* wt := value_t te L v in
      match wt with WTInt t => Some t | _ => None end
  end.

(** Read a [[flight]]'s lower donor taint: `none` gives clean capability
    taint; `lower(P)` copies `P`'s capability taint. *)
Definition flight_cap_t (te : tenv) (lw : flight_lower) : option taint :=
  match lw with
  | LowerNone => Some taint_bot
  | LowerOf v =>
      let* wt := value_t te P v in
      match wt with WTPtr _ tc => Some tc | WTInt _ => Some taint_bot | _ => None end
  end.

(** Join a list of scalar taints. *)
Fixpoint join_taints (ts : list taint) : taint :=
  match ts with
  | [] => taint_bot
  | t :: ts' => taint_join t (join_taints ts')
  end.

(** Extract the scalar taint of a [WTInt] argument. *)
Definition scalar_wt (wt : word_taint) : option taint :=
  match wt with WTInt t => Some t | _ => None end.

(** Whether `let(d, k, o, args)` is a self-zeroing integer idiom
    (`xor x, x` or `sub x, x`), which produces 0 regardless of `x` and
    clears taint as zegarmistrz does. *)
Definition is_zero_idiom (o : op) (k : class) (args : list value) : bool :=
  int_class k &&
  match o, args with
  | (Xor | Sub), [Tmp x; Tmp y] => name_eqb x y
  | _, _ => false
  end.

(** Size in bytes of a non-pointer [load_type]. *)
Definition load_type_bytes (t : load_type) : Z :=
  match t with
  | LdL | LdD => 8
  | LdS => 4
  | LdX => 10
  | LdNarrow n => fst (narrow_type n)
  end.

(** Environment after a block's phis for taint: mirrors [phis_env]. *)
Definition phis_tenv (phis : list phi) (from : option name) (te0 : tenv)
  : option tenv :=
  match from with
  | None => match phis with [] => Some te0 | _ => None end
  | Some pred =>
      fold_left (fun acc ph =>
                   let* te := acc in
                   match ph with
                   | Phi d k pairs =>
                       let* v := lookup pred pairs in
                       let* wt := value_t te0 k v in
                       Some (put d wt te)
                   end) phis (Some te0)
  end.

(** Initial taint environment of a called function [f] on argument
    taints [wts], mirroring [call_frame]. *)
Definition call_tenv (f : func) (wts : list word_taint) : option tenv :=
  let params := fn_params f in
  if (length wts <? length params)%nat then None else
  Some (fold_left (fun te px => put (snd (fst px)) (snd px) te)
                  (combine params (firstn (length params) wts)) []).

(** Bind returned word taints [ots] into a caller's [te], mirroring
    [returned_env]. *)
Definition returned_tenv (r : call_result) (ots : list word_taint) (te : tenv)
  : option tenv :=
  match r, ots with
  | CVoid, _ => Some te
  | CResult d k, [wt] => let* wt' := wt_at_class k wt in Some (put d wt' te)
  | CTuple rs, _ =>
      if negb (length ots =? length rs)%nat then None else
      fold_left (fun acc rx =>
                   let* te' := acc in
                   let* wt' := wt_at_class (snd (fst rx)) (snd rx) in
                   Some (put (fst (fst rx)) wt' te')) (combine rs ots) (Some te)
  | _, _ => None
  end.

(** ## Instruction taint transfer and checks

    Each instruction propagates restrictions from its inputs to its result.
    Instructions that expose secrets through control flow, addresses, or
    latency must also enforce the corresponding [[poison]] check. *)

(** Taint outcome of one step before pairing with [Semantics.step]. *)
Inductive tstep_out : Type :=
| TNext (ps' : pstate)
| TDone (ots : list word_taint)
| TFresh (tps : Z -> pstate)
| TFault (why : poison_reason)
| TStuck (why : string).

(** Check a runtime check op on pointer taint `(ta, tc)` under [pol].
    When [pol_check_branches] holds, branching on the address or flags
    checks `t_branch` on `ta` and `tc`, and reading the object header at
    `lower - 16` checks `t_index` on `tc`. *)
Definition check_ptr_bounds_taint (pol : poison_policy) (ta tc : taint)
  : option poison_reason :=
  if pol_check_branches pol then
    if t_branch ta || t_branch tc then Some CannotBranch
    else if t_index tc then Some CannotIndex
    else None
  else None.

(** Pure scalar ALU and float operations handled uniformly through
    [op_arg_classes]. `select` is one of them: its result carries the
    join of the taints of its condition and of both values, and it is
    not a branch, as zegarmistrz treats `cmov`. *)
Definition pure_scalar_op (o : op) : bool :=
  match o with
  | Add | Sub | Mul | Div | Udiv | Rem | Urem | And | Or | Xor
  | Sar | Shr | Shl | Neg | Select | Cmp _ _ | Ext _
  | ExtF _ | Truncd | Truncx | FloatToInt _ _ | IntToFloat _ _ | Cast | Sqrt => true
  | _ => false
  end.

(** Taint transfer and poison checks for `let(d, k, o, args)` in frame
    environment [e] and poison state [ps]. *)
Definition let_tstep (pol : poison_policy) (ge : genv) (e : env)
    (ps : pstate) (d : name) (k : class) (o : op) (args : list value)
  : tstep_out :=
  let te := ps_tenv ps in
  let bind (wt : word_taint) :=
    TNext (mkPState (put d wt te) (ps_callers ps) (ps_mem ps) (ps_aux ps)) in
  if is_zero_idiom o k args then bind (WTInt taint_bot) else
  match o with
  | CheckLocal _ _ _ _ _ => bind (WTPtr taint_bot taint_bot)
  | CheckFunction =>
      match args with
      | [v] =>
          match value_t te P v with
          | Some (WTPtr ta tc) =>
              if t_branch ta || t_branch tc then TFault CannotBranch
              else bind (WTPtr ta tc)
          | _ => TStuck "check_function"
          end
      | _ => TStuck "check_function"
      end
  | Alloc al =>
      match args with
      | [v] =>
          match value_x ge e L v, value_t te L v with
          | Some (WInt sz), Some (WTInt tsz) =>
              if t_branch tsz then TFault CannotBranch
              else if t_index tsz then TFault CannotIndex
              else if max_allocation_size <? sz then TDone []
              else
                let q := heap_req al sz in
                TFresh (fun base =>
                  mkPState (put d (WTPtr taint_bot taint_bot) te) (ps_callers ps)
                           (unpoison_range (ps_mem ps) base (req_extent q))
                           (unpoison_aux (ps_aux ps) base (req_extent q)))
          | _, _ => TStuck "alloc"
          end
      | _ => TStuck "alloc"
      end
  | Check _ _ _ _ =>
      match args with
      | [v] =>
          match value_t te P v with
          | Some (WTPtr ta tc) =>
              match check_ptr_bounds_taint pol ta tc with
              | Some why => TFault why
              | None => bind (WTPtr ta tc)
              end
          | _ => TStuck "check"
          end
      | _ => TStuck "check"
      end
  | CheckAhead _ _ _ _ _ => TStuck "check_ahead"
  | HalfCheck _ _ _ _ _ | Renew _ _ _ _ =>
      match args with
      | [q1; v] =>
          match value_t te A q1, value_t te P v with
          | Some (WTPtr qa qc), Some (WTPtr ta tc) =>
              match check_ptr_bounds_taint pol (taint_join qa ta) (taint_join qc tc) with
              | Some why => TFault why
              | None => bind (WTPtr ta tc)
              end
          | _, _ => TStuck "renew"
          end
      | _ => TStuck "renew"
      end
  | RenewHull _ _ _ _ =>
      match args with
      | [ql; qh; v] =>
          match value_t te A ql, value_t te A qh, value_t te P v with
          | Some (WTPtr al cl), Some (WTPtr ah ch), Some (WTPtr ta tc) =>
              match check_ptr_bounds_taint pol
                      (taint_join al (taint_join ah ta))
                      (taint_join cl (taint_join ch tc)) with
              | Some why => TFault why
              | None => bind (WTPtr ta tc)
              end
          | _, _, _ => TStuck "renew_hull"
          end
      | _ => TStuck "renew_hull"
      end
  | SpanTest _ _ =>
      match args with
      | [v] =>
          match value_t te P v with
          | Some (WTPtr ta tc) =>
              match check_ptr_bounds_taint pol ta tc with
              | Some why => TFault why
              | None => bind (WTInt (taint_join ta tc))
              end
          | _ => TStuck "span_test"
          end
      | _ => TStuck "span_test"
      end
  | RenewIf _ _ _ _ =>
      match args with
      | [v; gv] =>
          match value_t te P v, value_t te W gv with
          | Some (WTPtr ta tc), Some (WTInt tg) =>
              if pol_check_branches pol && t_branch tg then TFault CannotBranch
              else match check_ptr_bounds_taint pol ta tc with
                   | Some why => TFault why
                   | None => bind (WTPtr ta tc)
                   end
          | _, _ => TStuck "renew_if"
          end
      | _ => TStuck "renew_if"
      end
  | Limit _ =>
      match args with
      | [v] =>
          match value_t te P v with
          | Some (WTPtr _ tc) =>
              if pol_check_branches pol && t_branch tc then TFault CannotBranch
              else if pol_check_branches pol && t_index tc then TFault CannotIndex
              else bind (WTLimit tc tc)
          | _ => TStuck "limit"
          end
      | _ => TStuck "limit"
      end
  | CheckLimit _ _ _ _ =>
      match args with
      | [v; uv] =>
          match value_t te P v, value_t te L uv with
          | Some (WTPtr ta tc), Some (WTLimit uc ul) =>
              let tc' := taint_join tc (taint_join uc ul) in
              match check_ptr_bounds_taint pol ta tc' with
              | Some why => TFault why
              | None => bind (WTPtr ta tc)
              end
          | _, _ => TStuck "check_limit"
          end
      | _ => TStuck "check_limit"
      end
  | RawLoad t off =>
      match args with
      | [av] =>
          match value_x ge e A av, value_t te A av with
          | Some (WPtr p), Some (WTPtr ta tc) =>
              if t_index ta then TFault CannotIndex
              else if pol_check_branches pol && (t_branch ta || t_branch tc || t_index tc) then
                TFault CannotBranch
              else
                let addr := raw_address (ptr_addr p) off in
                let sz := load_type_bytes t in
                if mem_no_load (ps_mem ps) addr sz then TFault PoisonLoad
                else bind (WTInt (mem_load_taint (ps_mem ps) addr sz))
          | _, _ => TStuck "raw_load"
          end
      | _ => TStuck "raw_load"
      end
  | RawLoadPointer off _ =>
      match args with
      | [av] =>
          match value_x ge e A av, value_t te A av with
          | Some (WPtr p), Some (WTPtr ta tc) =>
              if t_index ta || t_index tc then TFault CannotIndex
              else if pol_check_branches pol && (t_branch ta || t_branch tc) then
                TFault CannotBranch
              else
                let addr := raw_address (ptr_addr p) off in
                if mem_no_load (ps_mem ps) addr 8 then TFault PoisonLoad
                else bind (WTPtr (mem_load_taint (ps_mem ps) addr 8) (ps_aux ps addr))
          | _, _ => TStuck "raw_load_pointer"
          end
      | _ => TStuck "raw_load_pointer"
      end
  | Ptoi =>
      match args with
      | [v] =>
          match value_t te P v with
          | Some (WTPtr ta _) | Some (WTInt ta) => bind (WTInt ta)
          | _ => TStuck "ptoi"
          end
      | _ => TStuck "ptoi"
      end
  | Itop =>
      match args with
      | [v] =>
          match value_t te L v with
          | Some (WTInt ta) => bind (WTPtr ta taint_bot)
          | _ => TStuck "itop"
          end
      | _ => TStuck "itop"
      end
  | Copy =>
      match args with
      | [v] =>
          match value_t te k v with
          | Some wt => bind wt
          | None => TStuck "copy"
          end
      | _ => TStuck "copy"
      end
  | Add | Sub =>
      match k, args with
      | P, [pv; ov] =>
          match value_t te P pv, value_t te L ov with
          | Some (WTPtr ta tc), Some (WTInt toff) => bind (WTPtr (taint_join ta toff) tc)
          | _, _ => TStuck "ptr_add"
          end
      | (A | F), _ => TStuck "add_proof"
      | _, _ =>
          match op_arg_classes o k with
          | Some cls =>
              match map2_option (value_t te) cls args with
              | Some wts =>
                  match map_option scalar_wt wts with
                  | Some ts =>
                      let tj := join_taints ts in
                      if op_checks_vartime pol o k && t_vartime tj then TFault CannotVarTimeOp
                      else bind (WTInt tj)
                  | None => TStuck "op_scalar"
                  end
              | None => TStuck "op_args"
              end
          | None => TStuck "op_cls"
          end
      end
  | _ =>
      if pure_scalar_op o && negb (class_eqb k P || class_eqb k A || class_eqb k F) then
        match op_arg_classes o k with
        | Some cls =>
            match map2_option (value_t te) cls args with
            | Some wts =>
                match map_option scalar_wt wts with
                | Some ts =>
                    let tj := join_taints ts in
                    if op_checks_vartime pol o k && t_vartime tj then TFault CannotVarTimeOp
                    else bind (WTInt tj)
                | None => TStuck "op_scalar"
                end
            | None => TStuck "op_args"
            end
        | None => TStuck "op_cls"
        end
      else TStuck "unsupported_op"
  end.

(** Taint transfer and poison checks for one instruction [i]. Notice
    [[flight]] (`lea`): it checks only whether [o] is variable-time and
    never faults on `cannot_index`, propagating the joined address taint
    into its result pointer. *)
Definition inst_tstep (pol : poison_policy) (ge : genv) (fr : frame)
    (ps : pstate) (i : inst) : tstep_out :=
  let e := fr_env fr in
  let te := ps_tenv ps in
  match i with
  | Loc _ _ | Touch _ => TNext ps
  | LocalAlloc _ size =>
      let q := local_req size in
      TFresh (fun base =>
        mkPState te (ps_callers ps)
                 (unpoison_range (ps_mem ps) base (req_extent q))
                 (unpoison_aux (ps_aux ps) base (req_extent q)))
  | Flight d o args lw =>
      match map_option (flight_arg_t te) args, flight_cap_t te lw with
      | Some ts, Some tc =>
          let ta := join_taints ts in
          if op_checks_vartime pol o L && t_vartime ta then TFault CannotVarTimeOp
          else TNext (mkPState (put d (WTPtr ta tc) te) (ps_callers ps) (ps_mem ps) (ps_aux ps))
      | _, _ => TStuck "flight"
      end
  | Let d k o args => let_tstep pol ge e ps d k o args
  | RawStore w off v av =>
      match width_value_class w, value_x ge e A av, value_t te A av with
      | Some vk, Some (WPtr p), Some (WTPtr ta tc) =>
          if t_index ta then TFault CannotIndex
          else if pol_check_branches pol && (t_branch ta || t_branch tc || t_index tc) then
            TFault CannotBranch
          else
            let addr := raw_address (ptr_addr p) off in
            let sz := width_bytes w in
            if mem_no_store (ps_mem ps) addr sz then TFault PoisonStore
            else match w, value_t te vk v with
                 | Wp, Some (WTPtr tva tvc) =>
                     TNext (mkPState te (ps_callers ps)
                              (mem_store_taint (ps_mem ps) addr sz tva)
                              (fun b => if b =? addr then tvc else ps_aux ps b))
                 | (Wb | Wh | Ww | Wl | Ws | Wd | Wx), Some (WTInt tv) =>
                     TNext (mkPState te (ps_callers ps)
                              (mem_store_taint (ps_mem ps) addr sz tv)
                              (ps_aux ps))
                 | _, _ => TStuck "raw_store_val"
                 end
      | _, _, _ => TStuck "raw_store"
      end
  | RawStorePointer off v av es =>
      if effects_eqb es [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]
         || effects_eqb es [LowerWrite; AddressWrite]
         || effects_eqb es [AtomicWrite] then
        match value_x ge e A av, value_t te A av, value_t te P v with
        | Some (WPtr p), Some (WTPtr ta tca), Some (WTPtr tva tvc) =>
            if t_index ta || t_index tca then TFault CannotIndex
            else if pol_check_branches pol && (t_branch ta || t_branch tca) then
              TFault CannotBranch
            else
              let addr := raw_address (ptr_addr p) off in
              if mem_no_store (ps_mem ps) addr 8 then TFault PoisonStore
              else TNext (mkPState te (ps_callers ps)
                            (mem_store_taint (ps_mem ps) addr 8 tva)
                            (fun b => if b =? addr then tvc else ps_aux ps b))
        | _, _, _ => TStuck "raw_store_pointer"
        end
      else TStuck "raw_store_effects"
  | Call r (Global f) args =>
      match map_option (arg_t te) args with
      | Some wts =>
          match find_fn ge f with
          | Some (Defined g) =>
              if variadic_func g then TStuck "variadic_call"
              else match call_tenv g wts with
                   | Some cte =>
                       TNext (mkPState cte ((te, r) :: ps_callers ps) (ps_mem ps) (ps_aux ps))
                   | None => TStuck "call_tenv"
                   end
          | Some (Outside _) => TStuck "outside"
          | None =>
              match lookup f (ge_globals ge) with
              | Some _ => TDone []
              | None =>
                  if is_free_name f then
                    match r, args, wts with
                    | CVoid, [Arg P _], [WTPtr ta tc] =>
                        if t_branch ta || t_branch tc then TFault CannotBranch
                        else if t_index tc then TFault CannotIndex
                        else TNext ps
                    | CVoid, [Arg P _], [WTInt ta] =>
                        if t_branch ta then TFault CannotBranch else TNext ps
                    | _, _, _ => TStuck "free"
                    end
                  else TStuck "external"
              end
          end
      | None => TStuck "call_args"
      end
  | Call _ _ _ => TStuck "indirect_call"
  | RawCall _ _ _ => TStuck "raw_call"
  end.

(** Pop a returning frame's taint stack, binding [ots] in the caller if
    one is waiting. *)
Definition return_tstep (ps : pstate) (ots : list word_taint) : tstep_out :=
  match ps_callers ps with
  | [] => TDone ots
  | (caller_te, r) :: rest =>
      match returned_tenv r ots caller_te with
      | Some te' => TNext (mkPState te' rest (ps_mem ps) (ps_aux ps))
      | None => TStuck "return_tenv"
      end
  end.

(** Taint step of a block's jump [j]: `branch` enforces `cannot_branch`
    and ignores `cannot_index` (the orthogonality invariant). *)
Definition jump_tstep (fr : frame) (ps : pstate) (j : jump) : tstep_out :=
  let te := ps_tenv ps in
  match j with
  | JGoto _ => TNext ps
  | JBranch v _ _ =>
      match value_t te W v with
      | Some (WTInt tv) => if t_branch tv then TFault CannotBranch else TNext ps
      | _ => TStuck "branch_taint"
      end
  | JRet v =>
      match fn_ret (fr_fn fr) with
      | RClass k =>
          match value_t te k v with
          | Some wt => return_tstep ps [wt]
          | None => TStuck "ret_taint"
          end
      | _ => TStuck "ret_type"
      end
  | JRets _ => TStuck "rets"
  | JRetVoid =>
      match fn_ret (fr_fn fr) with
      | RVoid => return_tstep ps []
      | _ => TStuck "ret_void_type"
      end
  | JUnreachable => TDone []
  end.

(** Taint step of configuration [c] with poison state [ps]. *)
Definition tstep (pol : poison_policy) (ge : genv) (c : config) (ps : pstate) : tstep_out :=
  let fr := c_frame c in
  match fr_doomed fr with
  | Some _ => TStuck "doomed"
  | None =>
      match fr_at fr with
      | Snapshot _ _ => TStuck "snapshot"
      | Enter l from =>
          if c_fuel c =? 0 then TDone []
          else match find_block l (fn_blocks (fr_fn fr)) with
               | Some b =>
                   match phis_tenv (b_phis b) from (ps_tenv ps) with
                   | Some te' => TNext (mkPState te' (ps_callers ps) (ps_mem ps) (ps_aux ps))
                   | None => TStuck "phis_tenv"
                   end
               | None => TStuck "find_block"
               end
      | Exec _ [] j => jump_tstep fr ps j
      | Exec _ (i :: _) _ => inst_tstep pol ge fr ps i
      end
  end.

(** ## Combined lockstep semantics and erasure

    The instrumented machine checks restrictions alongside an ordinary IR
    step. Erasing its [[poison]] state recovers the ordinary execution
    whenever the checks succeed. *)

(** Result of one instrumented step of `(c, ps)`. *)
Inductive pstep_result : Type :=
| PNext (c' : config) (ps' : pstate)
| PDone (o : outcome) (ots : list word_taint)
| PFresh (q : alloc_req) (k : Z -> config * pstate)
| PTrap (why : poison_reason)
| PStuck (why : string).

(** One instrumented step: poison checks run first (so a tainted operand
    faults as [PTrap] even when the underlying operation would trap or
    stop), and otherwise [Semantics.step] advances [c] in lockstep with
    [tstep]'s [ps]. *)
Definition pstep (pol : poison_policy) (ge : genv) (c : config) (ps : pstate)
  : pstep_result :=
  match tstep pol ge c ps with
  | TFault why => PTrap why
  | TStuck why => PStuck why
  | TNext ps' =>
      match step ge c with
      | Next c' => PNext c' ps'
      | Done o => PDone o []
      | Stuck why => PStuck why
      | Fresh _ _ => PStuck "fresh_mismatch"
      end
  | TDone ots =>
      match step ge c with
      | Done o => PDone o ots
      | Stuck why => PStuck why
      | _ => PStuck "done_mismatch"
      end
  | TFresh tps =>
      match step ge c with
      | Fresh q k => PFresh q (fun base => (k base, tps base))
      | Done o => PDone o []
      | Stuck why => PStuck why
      | Next _ => PStuck "next_mismatch"
      end
  end.

(** Multi-step deterministic poison run up to [steps] transitions,
    returning the terminal outcome or the first poison fault. *)
Fixpoint prun (pol : poison_policy) (ge : genv) (steps : nat) (c : config) (ps : pstate)
  : pstep_result :=
  match steps with
  | O => PNext c ps
  | S n =>
      match pstep pol ge c ps with
      | PNext c' ps' => prun pol ge n c' ps'
      | res => res
      end
  end.

(** Erasure theorem: every non-faulting [pstep] transition is an exact
    [Semantics.step] transition of the underlying configuration. Poison
    tracking never alters what a program computes. *)
Theorem pstep_erases : forall pol ge c ps,
  match pstep pol ge c ps with
  | PNext c' _ => step ge c = Next c'
  | PDone o _ => step ge c = Done o
  | PFresh q k => exists k0, step ge c = Fresh q k0 /\ forall base, fst (k base) = k0 base
  | PTrap _ | PStuck _ => True
  end.
Proof.
  intros pol ge c ps. unfold pstep.
  destruct (tstep pol ge c ps) as [ps' | ots | tps | why | why]; auto;
    destruct (step ge c) eqn:Es; auto.
  exists k. split; [reflexivity | intros base; reflexivity].
Qed.

(** ## Leakage observations and constant-time noninterference

    The observation model records control flow, memory addresses, and
    variable-time operands. Equal observations establish constant time at
    the [[stage|checked IR]] level, not a hardware timing guarantee. *)

(** Abstract leakage observation of a single IR step: control-flow
    transfers and branch outcomes, memory access addresses and byte
    widths, variable-latency operand bit-patterns, capability check
    inputs, and allocation/free requests. This is not a trace of every
    native instruction or a proof of a hardware timing model. *)
Inductive leak_event : Type :=
| LeakEnter (l : name) (from : option name)
| LeakGoto (l : name)
| LeakBranch (taken : bool) (target : name)
| LeakRet
| LeakCall (callee : name)
| LeakFree (x : word)
| LeakAlloc (q : alloc_req)
| LeakCheck (o : op) (p : ptr)
| LeakMem (r : rights) (addr size : Z)
| LeakVarTime (o : op) (xs : list word)
| LeakPure
| LeakDone (tag : string).

(** Leakage event emitted by configuration [c] under [pol]. The policy
    selects the variable-time observations as well as the checks.
    [LeakPure] includes flights and several runtime-check operations;
    [LeakCheck] records only the principal pointer, not every donor.
    Native constant-time adequacy therefore needs a separate argument
    relating these observations and the taint guards to emitted code. *)
Definition leak_of (pol : poison_policy) (ge : genv) (c : config) : leak_event :=
  let fr := c_frame c in
  let e := fr_env fr in
  match fr_at fr with
  | Snapshot _ l => LeakEnter l None
  | Enter l from =>
      if c_fuel c =? 0 then LeakDone "out_of_fuel" else LeakEnter l from
  | Exec _ [] j =>
      match j with
      | JGoto t => LeakGoto (edge_label t)
      | JBranch v t1 t2 =>
          match value_x ge e W v with
          | Some (WInt n) =>
              let taken := negb (n =? 0) in
              LeakBranch taken (edge_label (if taken then t1 else t2))
          | _ => LeakPure
          end
      | JRet _ | JRets _ | JRetVoid => LeakRet
      | JUnreachable => LeakDone "unreachable"
      end
  | Exec _ (i :: _) _ =>
      match i with
      | Loc _ _ | Touch _ | Flight _ _ _ _ => LeakPure
      | LocalAlloc _ sz => LeakAlloc (local_req sz)
      | RawStore w off _ av =>
          match value_x ge e A av with
          | Some (WPtr p) => LeakMem Write (raw_address (ptr_addr p) off) (width_bytes w)
          | _ => LeakPure
          end
      | RawStorePointer off _ av _ =>
          match value_x ge e A av with
          | Some (WPtr p) => LeakMem Write (raw_address (ptr_addr p) off) 8
          | _ => LeakPure
          end
      | Call _ (Global f) args =>
          match find_fn ge f with
          | Some (Defined _) => LeakCall f
          | _ =>
              if is_free_name f then
                match map_option (arg_x ge e) args with
                | Some [x] => LeakFree x
                | _ => LeakCall f
                end
              else LeakCall f
          end
      | Call _ _ _ | RawCall _ _ _ => LeakPure
      | Let _ k o args =>
          if is_zero_idiom o k args then LeakPure else
          match o with
          | Alloc al =>
              match args with
              | [v] => match value_x ge e L v with
                       | Some (WInt sz) => LeakAlloc (heap_req al sz)
                       | _ => LeakPure
                       end
              | _ => LeakPure
              end
          | Check _ _ _ _ | SpanTest _ _ =>
              if pol_check_branches pol then
                match args with
                | [v] => match value_x ge e P v with
                         | Some (WPtr p) => LeakCheck o p
                         | _ => LeakPure
                         end
                | _ => LeakPure
                end
              else LeakPure
          | HalfCheck _ _ _ _ _ | Renew _ _ _ _ =>
              if pol_check_branches pol then
                match args with
                | [_; v] => match value_x ge e P v with
                            | Some (WPtr p) => LeakCheck o p
                            | _ => LeakPure
                            end
                | _ => LeakPure
                end
              else LeakPure
          | RawLoad t off =>
              match args with
              | [av] => match value_x ge e A av with
                        | Some (WPtr p) => LeakMem Read (raw_address (ptr_addr p) off) (load_type_bytes t)
                        | _ => LeakPure
                        end
              | _ => LeakPure
              end
          | RawLoadPointer off _ =>
              match args with
              | [av] => match value_x ge e A av with
                        | Some (WPtr p) => LeakMem Read (raw_address (ptr_addr p) off) 8
                        | _ => LeakPure
                        end
              | _ => LeakPure
              end
          | _ =>
              if pure_scalar_op o && op_checks_vartime pol o k then
                match op_arg_classes o k with
                | Some cls =>
                    match map2_option (value_x ge e) cls args with
                    | Some xs => LeakVarTime o xs
                    | None => LeakPure
                    end
                | None => LeakPure
                end
              else LeakPure
          end
      end
  end.

(** Multi-step leakage trace of a deterministic run, collecting the
    [leak_event] of each step up to termination or [steps] steps. *)
Fixpoint prun_trace (pol : poison_policy) (ge : genv) (steps : nat) (c : config) (ps : pstate)
  : option (list leak_event) :=
  match steps with
  | O => Some []
  | S n =>
      let ev := leak_of pol ge c in
      match pstep pol ge c ps with
      | PNext c' ps' =>
          let* rest := prun_trace pol ge n c' ps' in
          Some (ev :: rest)
      | PDone _ _ => Some [ev]
      | _ => None
      end
  end.

(** ## Implicit-flow counterexample when branch checking is off

    An address can depend on a secret without using that secret in pointer
    arithmetic. This [[poison]] counterexample branches first and then
    chooses between two public addresses. *)

(** A minimal 3-block function `implicit_leak(int sec)`:
    if `sec == 0`, load byte 0 of `tbl`; else load byte 64 of `tbl`.
    Neither arm uses `sec` in an address expression. *)
Definition implicit_leak_fn : func :=
  mkFunc (TAtom "implicit_leak") (TAtom "export") (RClass W) [(W, TAtom "sec")]
    [ mkBlock (TAtom "entry") []
        [ Let (TAtom "z") W (Cmp Eq W) [Tmp (TAtom "sec"); Const 0] ]
        (JBranch (Tmp (TAtom "z")) (To (TAtom "then_b")) (To (TAtom "else_b")));
      mkBlock (TAtom "then_b") []
        [ Let (TAtom "p0") P Copy [Global (TAtom "tbl")];
          Let (TAtom "q0") A (Check 0 1 Read 1) [Tmp (TAtom "p0")];
          Let (TAtom "r0") W (RawLoad (LdNarrow Ub) 0) [Tmp (TAtom "q0")] ]
        (JRet (Tmp (TAtom "r0")));
      mkBlock (TAtom "else_b") []
        [ Let (TAtom "p1") P Copy [Global (TAtom "tbl")];
          Flight (TAtom "p64") Add [FAddress (Tmp (TAtom "p1")); FValue (Const 64)] (LowerOf (Tmp (TAtom "p1")));
          Let (TAtom "q1") A (Check 0 1 Read 1) [Tmp (TAtom "p64")];
          Let (TAtom "r1") W (RawLoad (LdNarrow Ub) 0) [Tmp (TAtom "q1")] ]
        (JRet (Tmp (TAtom "r1"))) ].

(** Global environment holding `implicit_leak` and a 128-byte read-only
    table `tbl` at base 4096. *)
Definition implicit_leak_ge : genv :=
  mkGenv [IFunc implicit_leak_fn] [(TAtom "tbl", mkPtr 4096 (Ro 4096))] free_res.

(** Memory containing `tbl` live at `[4096, 4224)`. *)
Definition implicit_leak_mem : mem :=
  mkMem (fun _ => 0) [mkRegion 4096 4224 GlobalData Live] (fun _ => CNone).

(** Starting configuration for `implicit_leak(sec)`. *)
Definition implicit_leak_cfg (sec : Z) : config :=
  mkConfig (mkFrame implicit_leak_fn [(TAtom "sec", WInt sec)] [] None (Enter (TAtom "entry") None))
           [] implicit_leak_mem 10.

(** Starting poison state with `sec` tainted only with `cannot_index`
    (`cannot_branch = false`). *)
Definition implicit_leak_ps_index_only : pstate :=
  mkPState [(TAtom "sec", WTInt taint_index)] [] (fun _ => pb_clean) (fun _ => taint_bot).

(** Counterexample theorem: when `sec` carries `cannot_index` alone,
    both `sec = 0` and `sec = 1` run to completion without any [PTrap],
    yet their leakage traces touch different addresses (`4096` vs
    `4160`) via implicit control flow. Pairing `cannot_branch` with
    `cannot_index` faults at the branch instead. *)
Theorem index_only_allows_implicit_addr_leak :
  exists tr0 tr1,
    prun_trace pol_default implicit_leak_ge 12 (implicit_leak_cfg 0) implicit_leak_ps_index_only = Some tr0 /\
    prun_trace pol_default implicit_leak_ge 12 (implicit_leak_cfg 1) implicit_leak_ps_index_only = Some tr1 /\
    In (LeakMem Read 4096 1) tr0 /\
    In (LeakMem Read 4160 1) tr1 /\
    ~ In (LeakMem Read 4160 1) tr0.
Proof.
  eexists _, _. split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  cbn. split; [auto 10|]. split; [auto 10|].
  intros Hin. repeat (destruct Hin as [Hin | Hin]; [discriminate Hin|]). exact Hin.
Qed.

(** ## Relational invariant and two-run constant-time soundness

    Two runs may differ in secret values but must agree on public values
    and restrictions. The relation below follows both executions through
    matching [[stage|checked IR]] steps. *)

(** Relational agreement between two runtime words under [wt]: any
    component on which [w1] and [w2] differ must carry [taint_all]. *)
Definition word_rel (wt : word_taint) (w1 w2 : word) : Prop :=
  match wt, w1, w2 with
  | WTInt t, WInt n1, WInt n2 => n1 <> n2 -> t = taint_all
  | WTPtr ta tc, WPtr p1, WPtr p2 =>
      (ptr_addr p1 <> ptr_addr p2 -> ta = taint_all) /\
      (ptr_cap p1 <> ptr_cap p2 -> tc = taint_all)
  | WTLimit tc tl, WLimit c1 s1, WLimit c2 s2 =>
      (c1 <> c2 -> tc = taint_all) /\ (s1 <> s2 -> tl = taint_all)
  | _, _, _ => False
  end.

(** Environment agreement between [e1] and [e2] under [te]. *)
Definition env_rel (te : tenv) (e1 e2 : env) : Prop :=
  forall x,
    (lookup x e1 = None /\ lookup x e2 = None) \/
    exists w1 w2 wt,
      lookup x e1 = Some w1 /\
      lookup x e2 = Some w2 /\
      lookup x te = Some wt /\
      word_rel wt w1 w2.

(** Agreement of suspended caller stacks (direct calls with `pd_conv = None`). *)
Fixpoint callers_rel (tcs : list (tenv * call_result))
    (cs1 cs2 : list (frame * pending)) : Prop :=
  match tcs, cs1, cs2 with
  | [], [], [] => True
  | (te, r) :: tcs', (fr1, pd1) :: cs1', (fr2, pd2) :: cs2' =>
      fr_fn fr1 = fr_fn fr2 /\
      fr_locals fr1 = fr_locals fr2 /\
      fr_doomed fr1 = None /\
      fr_doomed fr2 = None /\
      fr_at fr1 = fr_at fr2 /\
      pd1 = mkPending r None /\
      pd2 = mkPending r None /\
      env_rel te (fr_env fr1) (fr_env fr2) /\
      callers_rel tcs' cs1' cs2'
  | _, _, _ => False
  end.

(** Two configurations [c1] and [c2] are low-equivalent under [ps] when
    they sit at the same control point with the same regions, fuel and
    local layout, and every memory byte, stored capability or temporary
    where [c1] and [c2] differ carries [taint_all]. Partially tainted
    components must agree: this relation deliberately does not promise
    noninterference for index-only or branch-only secrets. The shared
    poison state also fixes redzones and clear-on-store flags. *)
Definition ct_rel (c1 c2 : config) (ps : pstate) : Prop :=
  let fr1 := c_frame c1 in
  let fr2 := c_frame c2 in
  let m1 := c_mem c1 in
  let m2 := c_mem c2 in
  fr_fn fr1 = fr_fn fr2 /\
  fr_locals fr1 = fr_locals fr2 /\
  fr_doomed fr1 = None /\
  fr_doomed fr2 = None /\
  fr_at fr1 = fr_at fr2 /\
  c_fuel c1 = c_fuel c2 /\
  m_regions m1 = m_regions m2 /\
  callers_rel (ps_callers ps) (c_callers c1) (c_callers c2) /\
  env_rel (ps_tenv ps) (fr_env fr1) (fr_env fr2) /\
  (forall a, m_bytes m1 a <> m_bytes m2 a -> pb_taint (ps_mem ps a) = taint_all) /\
  (forall a, m_aux m1 a <> m_aux m2 a -> ps_aux ps a = taint_all).

(** Putting related words into related environments keeps [env_rel]. *)
Lemma env_rel_put : forall te e1 e2 d wt w1 w2,
  env_rel te e1 e2 -> word_rel wt w1 w2 ->
  env_rel (put d wt te) (put d w1 e1) (put d w2 e2).
Proof.
  intros te e1 e2 d wt w1 w2 He Hw x.
  rewrite !lookup_put_name. destruct (name_eqb x d).
  - right. exists w1, w2, wt. auto.
  - exact (He x).
Qed.

(** Reading an operand [v] at class [k] in related environments gives
    related words under [value_t]. *)
Lemma value_rel : forall ge te e1 e2 k v w1 wt,
  env_rel te e1 e2 ->
  value_x ge e1 k v = Some w1 ->
  value_t te k v = Some wt ->
  exists w2, value_x ge e2 k v = Some w2 /\ word_rel wt w1 w2.
Proof.
  intros ge te e1 e2 k v w1 wt He Hv1 Ht.
  destruct v as [n | z | s]; cbn in *.
  - destruct (He n) as [[E1 _] | (u1 & u2 & ut & E1 & E2 & Et & Hrel)];
      rewrite E1 in Hv1; [discriminate Hv1|].
    rewrite E2. rewrite Et in Ht.
    destruct k, u1, u2, ut; cbn in *; try contradiction Hrel; try discriminate Hv1; try discriminate Ht;
      injection Hv1 as <-; injection Ht as <-; eexists; split; try reflexivity; cbn.
    all: try (intros Hne; apply Hrel; congruence).
    all: exact Hrel.
  - destruct k; cbn in *; try discriminate Hv1;
      injection Hv1 as <-; injection Ht as <-;
      eexists; (split; [reflexivity | cbn; repeat split; intros; congruence]).
  - injection Ht as <-. destruct (lookup s (ge_globals ge)) as [p|];
      injection Hv1 as <-; eexists; (split; [reflexivity | cbn; split; intros Hne; congruence]).
Qed.

(** Reading a list of operands at classes [cls] preserves [word_rel]
    pairwise. *)
Lemma map2_value_rel : forall ge te e1 e2 cls args xs1 wts,
  env_rel te e1 e2 ->
  map2_option (value_x ge e1) cls args = Some xs1 ->
  map2_option (value_t te) cls args = Some wts ->
  exists xs2, map2_option (value_x ge e2) cls args = Some xs2 /\
    Forall2 (fun wt p => word_rel wt (fst p) (snd p)) wts (combine xs1 xs2).
Proof.
  intros ge te e1 e2 cls. induction cls as [|k cls IH]; intros [|v args] xs1 wts He Hx Ht;
    cbn in *; try discriminate Hx; try discriminate Ht.
  - injection Hx as <-; injection Ht as <-. exists []. split; [reflexivity | constructor].
  - destruct (value_x ge e1 k v) as [w1|] eqn:Ev1; [|discriminate Hx].
    destruct (map2_option (value_x ge e1) cls args) as [ys1|] eqn:Eys1; [|discriminate Hx].
    destruct (value_t te k v) as [wt|] eqn:Evt; [|discriminate Ht].
    destruct (map2_option (value_t te) cls args) as [wts'|] eqn:Ewts; [|discriminate Ht].
    injection Hx as <-; injection Ht as <-.
    destruct (value_rel ge te e1 e2 k v w1 wt He Ev1 Evt) as (w2 & -> & Hw).
    destruct (IH args ys1 wts' He Eys1 Ewts) as (ys2 & -> & Hys).
    exists (w2 :: ys2). split; [reflexivity | constructor; [exact Hw | exact Hys]].
Qed.

(** Pairwise `word_rel` over scalar taints means equal `WInt` lists or
    `join_taints = taint_all`. *)
Lemma scalar_args_eq_or_all : forall wts xs1 xs2 ts,
  Forall2 (fun wt p => word_rel wt (fst p) (snd p)) wts (combine xs1 xs2) ->
  map_option scalar_wt wts = Some ts ->
  length xs1 = length xs2 ->
  xs1 = xs2 \/ join_taints ts = taint_all.
Proof.
  intros wts. induction wts as [|wt wts IH]; intros [|x1 xs1] [|x2 xs2] ts Hrel Hsc Hlen;
    cbn in Hrel, Hsc, Hlen; try discriminate Hlen; inversion Hrel; subst.
  - cbn in Hsc; injection Hsc as <-; left; reflexivity.
  - destruct (scalar_wt wt) as [t|] eqn:Est; [|discriminate Hsc].
    destruct (map_option scalar_wt wts) as [ts'|] eqn:Ests; [|discriminate Hsc].
    injection Hsc as <-. destruct wt as [t0| |]; try discriminate Est. injection Est as <-.
    cbn in H2. destruct x1 as [n1| |], x2 as [n2| |]; try contradiction H2.
    destruct (Z.eq_dec n1 n2) as [-> | Hn].
    + destruct (IH xs1 xs2 ts' H4 eq_refl ltac:(lia)) as [-> | Hall].
      * left; reflexivity.
      * right; cbn; rewrite Hall, taint_join_all_r; reflexivity.
    + right; cbn; rewrite (H2 Hn), taint_join_all_l; reflexivity.
Qed.

(** Loading [n] bytes from [a] in two memories whose differing bytes carry
    [taint_all] gives equal bytes or [range_taint_nat = taint_all]. *)
Lemma range_load_rel_nat : forall (m1 m2 : mem) pm n a,
  (forall b, m_bytes m1 b <> m_bytes m2 b -> pb_taint (pm b) = taint_all) ->
  (forall i, (i < n)%nat -> m_bytes m1 (a + Z.of_nat i) = m_bytes m2 (a + Z.of_nat i)) \/
  range_taint_nat pm a n = taint_all.
Proof.
  intros m1 m2 pm n. induction n as [|n IH]; intros a Hmem; cbn.
  - left. intros i Hi. lia.
  - destruct (Z.eq_dec (m_bytes m1 a) (m_bytes m2 a)) as [Heq | Hne].
    + destruct (IH (a + 1) Hmem) as [Hall | Htall].
      * left. intros [|i] Hi.
        -- cbn [Z.of_nat]; rewrite Z.add_0_r. exact Heq.
        -- replace (a + Z.of_nat (S i)) with ((a + 1) + Z.of_nat i) by lia.
           apply Hall. lia.
      * right. rewrite Htall, taint_join_all_r. reflexivity.
    + right. rewrite (Hmem a Hne), taint_join_all_l. reflexivity.
Qed.

(** Equal bytes in `[a, a + size)` make [load_bytes] equal. *)
Lemma load_bytes_eq_on : forall m1 m2 a size,
  (forall i, (i < Z.to_nat size)%nat -> m_bytes m1 (a + Z.of_nat i) = m_bytes m2 (a + Z.of_nat i)) ->
  load_bytes m1 a size = load_bytes m2 a size.
Proof.
  intros m1 m2 a size Hall. unfold load_bytes.
  generalize 0 as acc. induction (Z.to_nat size) as [|n IH]; intros acc; [reflexivity|].
  cbn. rewrite Hall by lia. apply IH. intros i Hi. apply Hall. lia.
Qed.

(** Storing `v1` and `v2` of width `size` at the same address [addr]
    with taint [tv] preserves the memory-byte relation. *)
Lemma store_bytes_rel : forall m1 m2 pm addr size v1 v2 tv,
  (forall b, m_bytes m1 b <> m_bytes m2 b -> pb_taint (pm b) = taint_all) ->
  (v1 <> v2 -> tv = taint_all) ->
  forall b,
    m_bytes (store_bytes m1 addr size v1) b <> m_bytes (store_bytes m2 addr size v2) b ->
    pb_taint (mem_store_taint pm addr size tv b) = taint_all.
Proof.
  intros m1 m2 pm addr size v1 v2 tv Hmem Hv b Hne.
  unfold store_bytes in Hne; unfold mem_store_taint; cbn in Hne.
  destruct ((addr <=? b) && (b <? addr + size)) eqn:Ein.
  - assert (v1 <> v2) by congruence. rewrite (Hv H). apply note_store_all.
  - exact (Hmem b Hne).
Qed.

(** Helper: `fold_left` over `option` from `None` stays `None`. *)
Lemma fold_none_opt : forall (A B : Type) (f : B -> A -> option B) xs,
  fold_left (fun acc x => let* y := acc in f y x) xs None = None.
Proof. intros A B f xs. induction xs as [|x xs IH]; cbn; [reflexivity | exact IH]. Qed.

(** `invalidate_locals` preserves region equality and byte/aux relations. *)
Lemma invalidate_locals_rel : forall ls pm paux m1 m2 m1',
  m_regions m1 = m_regions m2 ->
  (forall a, m_bytes m1 a <> m_bytes m2 a -> pb_taint (pm a) = taint_all) ->
  (forall a, m_aux m1 a <> m_aux m2 a -> paux a = taint_all) ->
  invalidate_locals ls m1 = Some m1' ->
  exists m2', invalidate_locals ls m2 = Some m2' /\
    m_regions m1' = m_regions m2' /\
    (forall a, m_bytes m1' a <> m_bytes m2' a -> pb_taint (pm a) = taint_all) /\
    (forall a, m_aux m1' a <> m_aux m2' a -> paux a = taint_all).
Proof.
  intros ls. induction ls as [|[x [base|]] ls IH]; intros pm paux m1 m2 m1' Hrg Hmb Hma Hinv; cbn in *.
  - injection Hinv as <-. exists m2. auto.
  - rewrite <- Hrg.
    destruct (object_region base (m_regions m1)) as [reg|]; [|rewrite fold_none_opt in Hinv; discriminate Hinv].
    destruct (r_kind reg), (r_life reg); try (rewrite fold_none_opt in Hinv; discriminate Hinv).
    destruct (replace_region base (mkRegion base base Stack Freed) (m_regions m1)) as [rs|];
      [|rewrite fold_none_opt in Hinv; discriminate Hinv].
    exact (IH pm paux (mkMem (m_bytes m1) rs (m_aux m1)) (mkMem (m_bytes m2) rs (m_aux m2)) m1' eq_refl Hmb Hma Hinv).
  - exact (IH pm paux m1 m2 m1' Hrg Hmb Hma Hinv).
Qed.

(** `flight_arg_x` in related environments agrees unless `flight_arg_t`
    is [taint_all]. *)
Lemma flight_arg_rel : forall ge te e1 e2 a w1 t,
  env_rel te e1 e2 ->
  flight_arg_x ge e1 a = Some w1 ->
  flight_arg_t te a = Some t ->
  exists w2, flight_arg_x ge e2 a = Some w2 /\ word_rel (WTInt t) w1 w2.
Proof.
  intros ge te e1 e2 [v | v] w1 t He Hx Ht; cbn in *.
  - destruct (value_x ge e1 L v) as [u1|] eqn:Eu1; [|discriminate Hx].
    destruct (value_t te L v) as [wt|] eqn:Ewt; [|discriminate Ht].
    destruct wt as [tv| |]; try discriminate Ht. injection Hx as <-; injection Ht as <-.
    exact (value_rel ge te e1 e2 L v u1 (WTInt tv) He Eu1 Ewt).
  - destruct (value_x ge e1 P v) as [u1|] eqn:Eu1; [|discriminate Hx].
    destruct u1 as [|p1|]; try discriminate Hx.
    destruct (value_t te P v) as [wt|] eqn:Ewt; [|discriminate Ht].
    destruct (value_rel ge te e1 e2 P v (WPtr p1) wt He Eu1 Ewt) as (u2 & -> & Hrel).
    destruct wt as [tv | ta tc |]; try discriminate Ht; destruct u2 as [|p2|]; try contradiction Hrel;
      injection Hx as <-; injection Ht as <-.
    exists (WInt (ptr_addr p2 mod 2 ^ 64)). split; [reflexivity|].
    cbn in *. intros Hne. apply (proj1 Hrel). congruence.
Qed.

(** List version of [flight_arg_rel]. *)
Lemma map_flight_arg_rel : forall ge te e1 e2 args xs1 ts,
  env_rel te e1 e2 ->
  map_option (flight_arg_x ge e1) args = Some xs1 ->
  map_option (flight_arg_t te) args = Some ts ->
  exists xs2, map_option (flight_arg_x ge e2) args = Some xs2 /\
    (forall w, In w xs1 -> exists z, w = WInt z) /\
    (forall w, In w xs2 -> exists z, w = WInt z) /\
    (xs1 = xs2 \/ join_taints ts = taint_all).
Proof.
  intros ge te e1 e2 args. induction args as [|a args IH]; intros xs1 ts He Hx Ht; cbn in *.
  - injection Hx as <-; injection Ht as <-.
    exists []. repeat split; try contradiction; left; reflexivity.
  - destruct (flight_arg_x ge e1 a) as [w1|] eqn:Ew1; [|discriminate Hx].
    destruct (map_option (flight_arg_x ge e1) args) as [ys1|] eqn:Eys1; [|discriminate Hx].
    destruct (flight_arg_t te a) as [t|] eqn:Et; [|discriminate Ht].
    destruct (map_option (flight_arg_t te) args) as [ts'|] eqn:Ets; [|discriminate Ht].
    injection Hx as <-; injection Ht as <-.
    destruct (flight_arg_rel ge te e1 e2 a w1 t He Ew1 Et) as (w2 & -> & Hw).
    destruct (IH ys1 ts' He eq_refl eq_refl) as (ys2 & -> & Hw1 & Hw2 & Hys).
    destruct w1 as [n1| |], w2 as [n2| |]; try contradiction Hw.
    exists (WInt n2 :: ys2). split; [reflexivity|]. split; [|split].
    + intros w [<- | Hin]; [exists n1; reflexivity | exact (Hw1 w Hin)].
    + intros w [<- | Hin]; [exists n2; reflexivity | exact (Hw2 w Hin)].
    + destruct (Z.eq_dec n1 n2) as [-> | Hn].
      * destruct Hys as [-> | Hall]; [left; reflexivity|].
        right; cbn; rewrite Hall, taint_join_all_r; reflexivity.
      * right; cbn; rewrite (Hw Hn), taint_join_all_l; reflexivity.
Qed.

(** `flight_cap` in related environments agrees unless `flight_cap_t` is
    [taint_all]. *)
Lemma flight_cap_rel : forall ge te e1 e2 lw c1 tc,
  env_rel te e1 e2 ->
  flight_cap ge e1 lw = Some c1 ->
  flight_cap_t te lw = Some tc ->
  exists c2, flight_cap ge e2 lw = Some c2 /\ (c1 <> c2 -> tc = taint_all).
Proof.
  intros ge te e1 e2 [|v] c1 tc He Hc Ht; cbn in *.
  - injection Hc as <-; injection Ht as <-. exists CNone. split; [reflexivity | congruence].
  - destruct (value_x ge e1 P v) as [u1|] eqn:Eu1; [|discriminate Hc].
    destruct u1 as [|p1|]; try discriminate Hc.
    destruct (value_t te P v) as [wt|] eqn:Ewt; [|discriminate Ht].
    destruct (value_rel ge te e1 e2 P v (WPtr p1) wt He Eu1 Ewt) as (u2 & -> & Hrel).
    destruct wt as [|ta tc0|]; try discriminate Ht; destruct u2 as [|p2|]; try contradiction Hrel.
    injection Hc as <-; injection Ht as <-. exists (ptr_cap p2). split; [reflexivity | exact (proj2 Hrel)].
Qed.

(** `phis_env` preserves [env_rel] when `phis_tenv` succeeds. *)
Lemma phis_rel : forall ge phis from e1 e2 te0 e1' te',
  env_rel te0 e1 e2 ->
  phis_env ge phis from e1 = Some e1' ->
  phis_tenv phis from te0 = Some te' ->
  exists e2', phis_env ge phis from e2 = Some e2' /\ env_rel te' e1' e2'.
Proof.
  intros ge phis [pred|] e1 e2 te0 e1' te' He0 Hp1 Hpt; cbn in *.
  - assert (Hfold : forall ps acc_e1 acc_e2 acc_te,
      env_rel acc_te acc_e1 acc_e2 ->
      fold_left (fun acc ph =>
                   let* e := acc in
                   match ph with Phi d k pairs =>
                     let* v := lookup pred pairs in let* x := value_x ge e1 k v in Some (put d x e)
                   end) ps (Some acc_e1) = Some e1' ->
      fold_left (fun acc ph =>
                   let* te := acc in
                   match ph with Phi d k pairs =>
                     let* v := lookup pred pairs in let* wt := value_t te0 k v in Some (put d wt te)
                   end) ps (Some acc_te) = Some te' ->
      exists e2',
        fold_left (fun acc ph =>
                     let* e := acc in
                     match ph with Phi d k pairs =>
                       let* v := lookup pred pairs in let* x := value_x ge e2 k v in Some (put d x e)
                     end) ps (Some acc_e2) = Some e2' /\ env_rel te' e1' e2').
    { induction ps as [|[d k pairs] ps IH]; intros ae1 ae2 ate Hae H1 Ht1; cbn in *.
      - injection H1 as <-; injection Ht1 as <-. exists ae2. auto.
      - destruct (lookup pred pairs) as [v|]; [|rewrite fold_none_opt in H1; discriminate H1].
        destruct (value_x ge e1 k v) as [w1|] eqn:Ew1; [|rewrite fold_none_opt in H1; discriminate H1].
        destruct (value_t te0 k v) as [wt|] eqn:Ewt; [|rewrite fold_none_opt in Ht1; discriminate Ht1].
        destruct (value_rel ge te0 e1 e2 k v w1 wt He0 Ew1 Ewt) as (w2 & -> & Hw).
        exact (IH (put d w1 ae1) (put d w2 ae2) (put d wt ate) (env_rel_put _ _ _ _ _ _ _ Hae Hw) H1 Ht1). }
    exact (Hfold phis e1 e2 te0 He0 Hp1 Hpt).
  - destruct phis; try discriminate Hp1. injection Hp1 as <-; injection Hpt as <-.
    exists e2. auto.
Qed.

(** Call argument lists in related environments give related argument
    lists. *)
Lemma call_args_rel : forall ge te e1 e2 args xs1 wts,
  env_rel te e1 e2 ->
  map_option (arg_x ge e1) args = Some xs1 ->
  map_option (arg_t te) args = Some wts ->
  exists xs2, map_option (arg_x ge e2) args = Some xs2 /\
    length xs1 = length xs2 /\
    Forall2 (fun wt p => word_rel wt (fst p) (snd p)) wts (combine xs1 xs2).
Proof.
  intros ge te e1 e2 args. induction args as [|[k v] args IH]; intros xs1 wts He Hx Ht; cbn in *.
  - injection Hx as <-; injection Ht as <-. exists []. repeat split; constructor.
  - destruct (value_x ge e1 k v) as [w1|] eqn:Ew1; [|discriminate Hx].
    destruct (map_option (arg_x ge e1) args) as [ys1|] eqn:Eys1; [|discriminate Hx].
    destruct (value_t te k v) as [wt|] eqn:Ewt; [|discriminate Ht].
    destruct (map_option (arg_t te) args) as [wts'|] eqn:Ewts; [|discriminate Ht].
    injection Hx as <-; injection Ht as <-.
    destruct (value_rel ge te e1 e2 k v w1 wt He Ew1 Ewt) as (w2 & -> & Hw).
    destruct (IH ys1 wts' He eq_refl eq_refl) as (ys2 & -> & Hlen & Hys).
    exists (w2 :: ys2). split; [reflexivity | split; [cbn; lia | constructor; assumption]].
Qed.

(** `call_frame` and `call_tenv` on related argument lists produce
    related initial environments. *)
Lemma call_frame_rel : forall g xs1 xs2 wts fr1 cte,
  variadic_func g = false ->
  length xs1 = length xs2 ->
  Forall2 (fun wt p => word_rel wt (fst p) (snd p)) wts (combine xs1 xs2) ->
  call_frame g xs1 = Some fr1 ->
  call_tenv g wts = Some cte ->
  exists fr2, call_frame g xs2 = Some fr2 /\
    fr_fn fr1 = fr_fn fr2 /\
    fr_locals fr1 = fr_locals fr2 /\
    fr_doomed fr1 = None /\
    fr_doomed fr2 = None /\
    fr_at fr1 = fr_at fr2 /\
    env_rel cte (fr_env fr1) (fr_env fr2).
Proof.
  intros g xs1 xs2 wts fr1 cte Hvar Hlen2 Hrel Hcf Hct.
  unfold call_frame in *; unfold call_tenv in *.
  assert (Hlen1 : length wts = length xs1).
  { clear -Hlen2 Hrel. revert xs1 xs2 Hlen2 Hrel.
    induction wts as [|wt wts IH]; intros [|x1 xs1] [|x2 xs2] Hlen Hrel; cbn in *;
      try discriminate; try solve [inversion Hrel]; auto.
    injection Hlen as Hlen. inversion Hrel; subst. f_equal. exact (IH _ _ Hlen H4). }
  rewrite <- Hlen2.
  destruct (length xs1 <? length (fn_params g))%nat; [discriminate Hcf|].
  rewrite Hlen1 in Hct. destruct (length xs1 <? length (fn_params g))%nat; [discriminate Hct|].
  destruct (fn_blocks g) as [|b bs]; [discriminate Hcf|].
  rewrite Hvar in Hcf |- *. injection Hcf as <-; injection Hct as <-.
  eexists. repeat split; try reflexivity.
  assert (Hfirst : Forall2 (fun wt p => word_rel wt (fst p) (snd p))
                     (firstn (length (fn_params g)) wts)
                     (combine (firstn (length (fn_params g)) xs1) (firstn (length (fn_params g)) xs2))).
  { generalize (length (fn_params g)) as n. clear -Hrel Hlen2. intros n.
    revert wts xs1 xs2 Hlen2 Hrel.
    induction n as [|n IH]; intros wts xs1 xs2 Hlen H; [cbn; constructor|].
    destruct wts as [|wt wts], xs1 as [|x1 xs1], xs2 as [|x2 xs2]; cbn in *;
      try discriminate Hlen; try solve [inversion H]; try solve [constructor].
    injection Hlen as Hlen. inversion H; subst.
    constructor; [assumption | exact (IH _ _ _ Hlen H5)]. }
  assert (Hfold : forall (ps : list (class * name)) ws1 ws2 ts ae1 ae2 ate,
    length ws1 = length ws2 ->
    Forall2 (fun wt p => word_rel wt (fst p) (snd p)) ts (combine ws1 ws2) ->
    env_rel ate ae1 ae2 ->
    env_rel (fold_left (fun te px => put (snd (fst px)) (snd px) te) (combine ps ts) ate)
            (fold_left (fun e px => put (snd (fst px)) (snd px) e) (combine ps ws1) ae1)
            (fold_left (fun e px => put (snd (fst px)) (snd px) e) (combine ps ws2) ae2)).
  { induction ps as [|[pk pn] ps IH]; intros [|x1 ws1] [|x2 ws2] [|t ts] ae1 ae2 ate Hlw Hw Hae;
      cbn in *; try exact Hae; try discriminate Hlw; try solve [inversion Hw].
    injection Hlw as Hlw. inversion Hw; subst. apply IH; [exact Hlw | assumption | apply env_rel_put; assumption]. }
  apply Hfold; [rewrite !length_firstn, Hlen2; reflexivity | exact Hfirst | intros x; left; auto].
Qed.

(** When `check_ptr_bounds_taint pol ta tc = None` under
    `pol_check_branches pol = true`, neither `ta` nor `tc` can be
    [taint_all]. *)
Lemma check_ptr_bounds_not_all : forall pol ta tc,
  pol_check_branches pol = true ->
  check_ptr_bounds_taint pol ta tc = None ->
  ta <> taint_all /\ tc <> taint_all.
Proof.
  intros pol [b1 i1 v1] [b2 i2 v2] Hcb H; unfold check_ptr_bounds_taint in H; rewrite Hcb in H; cbn in H.
  destruct b1; [discriminate H|]. destruct b2; [discriminate H|].
  split; discriminate.
Qed.

(** `pointer_load_effects` on two memories whose differing bytes/aux
    carry [taint_all] returns related pointers. *)
Lemma pointer_load_effects_rel : forall m1 m2 pm paux addr es p1,
  (forall b, m_bytes m1 b <> m_bytes m2 b -> pb_taint (pm b) = taint_all) ->
  (forall b, m_aux m1 b <> m_aux m2 b -> paux b = taint_all) ->
  pointer_load_effects m1 addr es = Some p1 ->
  exists p2, pointer_load_effects m2 addr es = Some p2 /\
    word_rel (WTPtr (mem_load_taint pm addr 8) (paux addr)) (WPtr p1) (WPtr p2).
Proof.
  intros m1 m2 pm paux addr es p1 Hmb Hma Hpl.
  unfold pointer_load_effects in *.
  assert (Hstep : forall st1 st2,
    (ptr_addr (snd st1) <> ptr_addr (snd st2) -> mem_load_taint pm addr 8 = taint_all) /\
    (fst st1 <> fst st2 -> paux addr = taint_all) /\
    (ptr_cap (snd st1) <> ptr_cap (snd st2) -> paux addr = taint_all) ->
    forall xs r1,
      fold_left (fun st e => let* s := st in pointer_load_effect m1 addr s e) xs (Some st1) = Some r1 ->
      exists r2,
        fold_left (fun st e => let* s := st in pointer_load_effect m2 addr s e) xs (Some st2) = Some r2 /\
        (ptr_addr (snd r1) <> ptr_addr (snd r2) -> mem_load_taint pm addr 8 = taint_all) /\
        (fst r1 <> fst r2 -> paux addr = taint_all) /\
        (ptr_cap (snd r1) <> ptr_cap (snd r2) -> paux addr = taint_all)).
  { intros st1 st2 Hst xs. revert st1 st2 Hst.
    induction xs as [|e xs IH]; intros [c1 q1] [c2 q2] (Ha & Hc & Hqc) r1 H1; cbn in *.
    - injection H1 as <-. exists (c2, q2). auto.
    - destruct e; try (rewrite fold_none_opt in H1; discriminate H1); cbn in *.
      + apply (IH (aux_at m1 addr, mkPtr (ptr_addr q1) (aux_at m1 addr))
                  (aux_at m2 addr, mkPtr (ptr_addr q2) (aux_at m2 addr)));
          [cbn; repeat split; [exact Ha | apply Hma | apply Hma] | exact H1].
      + apply (IH (c1, mkPtr (ptr_addr q1) c1)
                  (c2, mkPtr (ptr_addr q2) c2));
          [cbn; repeat split; [exact Ha | exact Hc | exact Hc] | exact H1].
      + assert (Hld : load_bytes m1 addr 8 <> load_bytes m2 addr 8 -> mem_load_taint pm addr 8 = taint_all).
        { intros Hne. destruct (range_load_rel_nat m1 m2 pm 8 addr Hmb) as [Hall | Htall]; [|exact Htall].
          exfalso. apply Hne, load_bytes_eq_on. exact Hall. }
        apply (IH (c1, mkPtr (load_bytes m1 addr 8) (ptr_cap q1))
                  (c2, mkPtr (load_bytes m2 addr 8) (ptr_cap q2)));
          [cbn; repeat split; [exact Hld | exact Hc | exact Hqc] | exact H1].
      + assert (Hld : load_bytes m1 addr 8 <> load_bytes m2 addr 8 -> mem_load_taint pm addr 8 = taint_all).
        { intros Hne. destruct (range_load_rel_nat m1 m2 pm 8 addr Hmb) as [Hall | Htall]; [|exact Htall].
          exfalso. apply Hne, load_bytes_eq_on. exact Hall. }
        apply (IH (aux_at m1 addr, mkPtr (load_bytes m1 addr 8) (aux_at m1 addr))
                  (aux_at m2 addr, mkPtr (load_bytes m2 addr 8) (aux_at m2 addr)));
          [cbn; repeat split; [exact Hld | apply Hma | apply Hma] | exact H1]. }
  destruct (fold_left _ es (Some (CNone, mkPtr 0 CNone))) as [r1|] eqn:Ef1; [|discriminate Hpl].
  injection Hpl as <-.
  destruct (Hstep (CNone, mkPtr 0 CNone) (CNone, mkPtr 0 CNone)
             ltac:(cbn; repeat split; congruence) es r1 Ef1) as (r2 & -> & Ha & _ & Hqc).
  exists (snd r2). split; [reflexivity | split; assumption].
Qed.

(** `free` called on identical pointer arguments in two memories with
    identical regions preserves region equality and byte/aux relations. *)
Lemma free_rel : forall (free_fn : word -> mem -> option (res unit * mem))
    x m1 m2 pm paux r1 m1',
  free_fn = free_res ->
  m_regions m1 = m_regions m2 ->
  (forall a, m_bytes m1 a <> m_bytes m2 a -> pb_taint (pm a) = taint_all) ->
  (forall a, m_aux m1 a <> m_aux m2 a -> paux a = taint_all) ->
  free_fn x m1 = Some (r1, m1') ->
  exists m2', free_fn x m2 = Some (r1, m2') /\
    m_regions m1' = m_regions m2' /\
    (forall a, m_bytes m1' a <> m_bytes m2' a -> pb_taint (pm a) = taint_all) /\
    (forall a, m_aux m1' a <> m_aux m2' a -> paux a = taint_all).
Proof.
  intros free_fn x m1 m2 pm paux r1 m1' -> Hrg Hmb Hma Hf.
  unfold free_res, cap_free_res, object_free_res in *.
  destruct x as [a | [a c] | lc ls]; cbn [ptr_addr ptr_cap] in *; try discriminate Hf.
  - destruct (a =? 0); injection Hf as <- <-; exists m2; auto.
  - destruct c as [| base | base | fn | ext]; try discriminate Hf;
      try solve [destruct (a =? 0); injection Hf as <- <-; exists m2; auto];
      (destruct (a =? 0); [injection Hf as <- <-; exists m2; auto|]);
      rewrite <- Hrg;
      destruct (object_region base (m_regions m1)) as [reg|]; try discriminate Hf;
      destruct (negb (kind_eqb (r_kind reg) Heap)); try (injection Hf as <- <-; exists m2; auto);
      destruct (negb (a =? base)); try (injection Hf as <- <-; exists m2; auto);
      destruct (r_life reg); try (injection Hf as <- <-; exists m2; auto);
      destruct (replace_region base (mkRegion base base Heap Freed) (m_regions m1)) as [rs|];
      try discriminate Hf;
      injection Hf as <- <-;
      exists (mkMem (m_bytes m2) rs (m_aux m2)); cbn; auto.
Qed.

(** Shape lemma: scalar taints force related word lists to consist of
    [WInt] values pairwise. *)
Lemma scalar_args_shapes : forall wts xs1 xs2 ts,
  Forall2 (fun wt p => word_rel wt (fst p) (snd p)) wts (combine xs1 xs2) ->
  map_option scalar_wt wts = Some ts ->
  length xs1 = length xs2 ->
  (xs1 = [] /\ xs2 = []) \/
  (exists a1 a2, xs1 = [WInt a1] /\ xs2 = [WInt a2]) \/
  (exists a1 b1 a2 b2, xs1 = [WInt a1; WInt b1] /\ xs2 = [WInt a2; WInt b2]) \/
  (3 <= length xs1)%nat.
Proof.
  intros wts [|x1 [|y1 [|z1 xs1]]] [|x2 [|y2 [|z2 xs2]]] ts Hfor Hsc Hlen; cbn in *;
    try discriminate Hlen; try (do 3 right; lia).
  - left; auto.
  - inversion Hfor as [|wt1 p1 wts1 ps1 Hw1 Hfor2]; subst.
    destruct wt1 as [t1| |]; try discriminate Hsc.
    destruct x1, x2; try contradiction Hw1. right; left. repeat eexists.
  - inversion Hfor as [|wt1 p1 wts1 ps1 Hw1 Hfor2]; subst.
    inversion Hfor2 as [|wt2 p2 wts2 ps2 Hw2 Hfor3]; subst.
    destruct wt1 as [t1| |]; try discriminate Hsc. cbn in Hsc.
    destruct wt2 as [t2| |]; try discriminate Hsc.
    destruct x1, x2; try contradiction Hw1. destruct y1, y2; try contradiction Hw2.
    right; right; left. repeat eexists.
Qed.

(** Shape lemma for three or more scalar arguments, the arity of
    `select`: the first three of each list are [WInt] values. *)
Lemma scalar_args_three : forall wts x1 y1 z1 xs1 xs2 ts,
  Forall2 (fun wt p => word_rel wt (fst p) (snd p)) wts
    (combine (x1 :: y1 :: z1 :: xs1) xs2) ->
  map_option scalar_wt wts = Some ts ->
  length (x1 :: y1 :: z1 :: xs1) = length xs2 ->
  exists a1 b1 c1 a2 b2 c2 xs2',
    x1 = WInt a1 /\ y1 = WInt b1 /\ z1 = WInt c1 /\
    xs2 = WInt a2 :: WInt b2 :: WInt c2 :: xs2' /\ length xs1 = length xs2'.
Proof.
  intros wts x1 y1 z1 xs1 [|x2 [|y2 [|z2 xs2]]] ts Hfor Hsc Hlen; cbn in *;
    try discriminate Hlen.
  inversion Hfor as [|wt1 p1 wts1 ps1 Hw1 Hfor2]; subst.
  inversion Hfor2 as [|wt2 p2 wts2 ps2 Hw2 Hfor3]; subst.
  inversion Hfor3 as [|wt3 p3 wts3 ps3 Hw3 Hfor4]; subst.
  destruct wt1 as [t1| |]; try discriminate Hsc. cbn in Hsc.
  destruct wt2 as [t2| |]; try discriminate Hsc. cbn in Hsc.
  destruct wt3 as [t3| |]; try discriminate Hsc.
  destruct x1, x2; try contradiction Hw1. destruct y1, y2; try contradiction Hw2.
  destruct z1, z2; try contradiction Hw3.
  repeat eexists. lia.
Qed.

(** `map2_option` preserves list length. *)
Lemma map2_option_len : forall (A B C : Type) (f : A -> B -> option C) xs ys zs,
  map2_option f xs ys = Some zs -> length zs = length xs.
Proof.
  intros A B C f xs. induction xs as [|x xs IH]; intros [|y ys] zs H; cbn in *; try discriminate H.
  - injection H as <-; reflexivity.
  - destruct (f x y); [|discriminate H]. destruct (map2_option f xs ys) eqn:Em; [|discriminate H].
    injection H as <-; cbn; f_equal; exact (IH _ _ Em).
Qed.

Local Opaque Z.pow ieee_binary ieee_neg ieee_convert ieee_sqrt ieee_compare ieee_from_int ieee_to_int.

(** Pure deterministic scalar `op_res` on two related inputs `xs1, xs2`
    that passed [op_checks_vartime]: `op_res` on `xs2` succeeds with an
    integer `n2`, and if `n1 <> n2` then `join_taints ts = taint_all`. *)
Lemma pure_scalar_op_rel : forall pol o k cls xs1 xs2 wts ts m1 m2 w1 m1',
  pure_scalar_op o = true ->
  k <> P -> k <> A -> k <> F ->
  op_arg_classes o k = Some cls ->
  length xs1 = length xs2 ->
  Forall2 (fun wt p => word_rel wt (fst p) (snd p)) wts (combine xs1 xs2) ->
  map_option scalar_wt wts = Some ts ->
  op_checks_vartime pol o k && t_vartime (join_taints ts) = false ->
  op_res o k xs1 m1 = Some (OpRes (RVal w1) m1') ->
  exists n1 n2,
    w1 = WInt n1 /\ m1' = m1 /\
    op_res o k xs2 m2 = Some (OpRes (RVal (WInt n2)) m2) /\
    (n1 <> n2 -> join_taints ts = taint_all).
Proof.
  intros pol o k cls xs1 xs2 wts ts m1 m2 w1 m1' Hpure HkP HkA HkF Hcls Hlen Hfor Hsc Hvt Hop1.
  assert (Hm_indep : forall mm, op_res o k xs1 mm = Some (OpRes (RVal w1) mm)).
  { intros mm. destruct o; try discriminate Hpure;
      unfold op_res, op_res_int, float_integer in Hop1 |- *;
      repeat match type of Hop1 with
      | context [match ?x with _ => _ end] =>
          lazymatch x with
          | m1 => fail
          | _ => destruct x eqn:?; cbn in Hop1 |- *; try discriminate Hop1
          end
      end;
      injection Hop1 as <- <-; reflexivity. }
  assert (Hw_int : exists n1, w1 = WInt n1 /\ m1' = m1).
  { pose proof (Hm_indep m1) as E. rewrite Hop1 in E. injection E as <-.
    destruct xs1 as [|[| | ] [|[| | ] [|? ?]]];
      destruct o; try discriminate Hpure; destruct k; try congruence;
      cbv beta iota zeta delta [op_res op_res_int float_integer additive_res alu] in Hop1;
      cbn in Hop1; try discriminate Hop1;
      repeat match type of Hop1 with
      | context [match ?x with _ => _ end] =>
          lazymatch x with context [match _ with _ => _ end] => fail | _ => destruct x eqn:?; cbn in Hop1; try discriminate Hop1 end
      end;
      injection Hop1 as <-; eexists; split; reflexivity. }
  destruct Hw_int as (n1 & -> & ->).
  destruct (scalar_args_eq_or_all wts xs1 xs2 ts Hfor Hsc Hlen) as [<- | Hall].
  - exists n1, n1. repeat split; [exact (Hm_indep m2) | congruence].
  - assert (Hnknown : op_vartime_class o k <> Some VTKnown).
    { intros Hkn. unfold op_checks_vartime in Hvt. rewrite Hkn, Hall in Hvt.
      destruct (pol_vartime pol); discriminate Hvt. }
    destruct (scalar_args_shapes wts xs1 xs2 ts Hfor Hsc Hlen)
      as [(-> & ->) | [(a1 & a2 & -> & ->) | [(a1 & b1 & a2 & b2 & -> & ->) | Hge3]]].
    + destruct o; try discriminate Hpure; destruct k; try congruence;
        cbv beta iota zeta delta [op_res op_res_int float_integer additive_res alu] in Hop1;
        cbn in Hop1; try destruct (fmt_of _); cbn in Hop1; discriminate Hop1.
    + destruct o; try discriminate Hpure;
        try (exfalso; apply Hnknown; reflexivity);
        destruct k; try congruence;
        cbv beta iota zeta delta [op_res op_res_int float_arithmetic additive_res alu integer_source signed] in Hop1 |- *;
        cbn in Hop1 |- *; try (destruct (fmt_of _); cbn in Hop1 |- *); try discriminate Hop1;
        try match goal with H : context [modulus ?ik] |- _ => destruct ik; cbn in H |- *; try discriminate H end;
        try match goal with |- context [match ?sg with Signed => _ | Unsigned => _ end] => destruct sg; cbn in Hop1 |- *; try discriminate Hop1 end;
        eexists n1, _; (split; [reflexivity | split; [reflexivity | split; [reflexivity | intros _; exact Hall]]]).
    + destruct o; try discriminate Hpure;
        try (exfalso; apply Hnknown; reflexivity);
        try (destruct (float_class k) eqn:Efc; [exfalso; apply Hnknown; cbn; rewrite Efc; reflexivity|]);
        destruct k; try congruence; try discriminate Efc;
        cbv beta iota zeta delta [op_res op_res_int float_arithmetic additive_res alu cond_bit signed shift_factor] in Hop1 |- *;
        cbn in Hop1 |- *; try discriminate Hop1;
        try match goal with |- context [fmt_of ?ck] =>
          destruct ck; cbn in Hop1 |- *; try discriminate Hop1;
          match goal with |- context [match ?cc with Eq => _ | _ => _ end] =>
            destruct cc; cbn in Hop1 |- *; try discriminate Hop1
          | _ => idtac end
        end;
        eexists n1, _; (split; [reflexivity | split; [reflexivity | split; [reflexivity | intros _; exact Hall]]]).
    + destruct xs1 as [|x1 [|y1 [|z1 xs1']]]; cbn in Hge3; try lia.
      destruct (scalar_args_three wts x1 y1 z1 xs1' xs2 ts Hfor Hsc Hlen)
        as (a1 & b1 & c1 & a2 & b2 & c2 & xs2' & -> & -> & -> & -> & Hlen').
      destruct o; try discriminate Hpure;
        try solve [exfalso; destruct k; try congruence;
          cbv beta iota zeta delta [op_res op_res_int float_integer float_arithmetic additive_res alu] in Hop1;
          cbn in Hop1; try destruct (fmt_of _); cbn in Hop1; discriminate Hop1].
      (* `select`, the one operation of three arguments *)
      destruct xs1' as [|? ?]; [|exfalso; destruct k; try congruence; cbn in Hop1; discriminate Hop1].
      destruct xs2' as [|? ?]; [|discriminate Hlen'].
      exists n1, (if a2 =? 0 then c2 else b2).
      split; [reflexivity | split; [reflexivity | split; [|intros _; exact Hall]]].
      destruct k; try congruence; reflexivity.
Qed.

(** `Flight`'s address `alu o L` on related `WInt` argument lists: if
    `op_checks_vartime pol o L && t_vartime (join_taints ts) = false`,
    `alu o L xs2` evaluates to an integer and differs from `xs1`'s only
    when `join_taints ts = taint_all`. *)
Lemma flight_alu_rel : forall pol o xs1 xs2 ts n1,
  (forall w, In w xs1 -> exists z, w = WInt z) ->
  (forall w, In w xs2 -> exists z, w = WInt z) ->
  length xs1 = length xs2 ->
  (xs1 = xs2 \/ join_taints ts = taint_all) ->
  op_checks_vartime pol o L && t_vartime (join_taints ts) = false ->
  alu o L xs1 = Some (WInt n1) ->
  exists n2, alu o L xs2 = Some (WInt n2) /\ (n1 <> n2 -> join_taints ts = taint_all).
Proof.
  intros pol o xs1 xs2 ts n1 Hw1 Hw2 Hlen Hxs Hvt Halu1.
  destruct Hxs as [<- | Hall].
  - exists n1; split; [exact Halu1 | congruence].
  - assert (Hnknown : op_vartime_class o L <> Some VTKnown).
    { intros Hkn. unfold op_checks_vartime in Hvt. rewrite Hkn, Hall in Hvt.
      destruct (pol_vartime pol); discriminate Hvt. }
    destruct xs1 as [|x1 [|y1 [|z1 xs1']]]; destruct xs2 as [|x2 [|y2 [|z2 xs2']]]; try discriminate Hlen.
    + destruct o; cbn in Halu1; discriminate Halu1.
    + destruct (Hw1 x1 (or_introl eq_refl)) as (zx1 & ->).
      destruct (Hw2 x2 (or_introl eq_refl)) as (zx2 & ->).
      destruct o; try (exfalso; apply Hnknown; reflexivity);
        cbv beta iota zeta delta [alu] in Halu1 |- *; cbn in Halu1 |- *; try discriminate Halu1;
        eexists _; (split; [reflexivity | intros _; exact Hall]).
    + destruct (Hw1 x1 (or_introl eq_refl)) as (zx1 & ->).
      destruct (Hw1 y1 (or_intror (or_introl eq_refl))) as (zy1 & ->).
      destruct (Hw2 x2 (or_introl eq_refl)) as (zx2 & ->).
      destruct (Hw2 y2 (or_intror (or_introl eq_refl))) as (zy2 & ->).
      destruct o; try (exfalso; apply Hnknown; reflexivity);
        cbv beta iota zeta delta [alu cond_bit signed shift_factor] in Halu1 |- *;
        cbn in Halu1 |- *; try discriminate Halu1;
        try match goal with |- context [match ?cc with Eq => _ | _ => _ end] =>
          destruct cc; cbn in Halu1 |- *; try discriminate Halu1
        end;
        try match goal with |- context [modulus ?ck] =>
          destruct ck; cbn in Halu1 |- *; try discriminate Halu1
        end;
        eexists _; (split; [reflexivity | intros _; exact Hall]).
    + destruct (Hw1 x1 (or_introl eq_refl)) as (zx1 & ->).
      destruct (Hw1 y1 (or_intror (or_introl eq_refl))) as (zy1 & ->).
      destruct (Hw1 z1 (or_intror (or_intror (or_introl eq_refl)))) as (zz1 & ->).
      destruct (Hw2 x2 (or_introl eq_refl)) as (zx2 & ->).
      destruct (Hw2 y2 (or_intror (or_introl eq_refl))) as (zy2 & ->).
      destruct (Hw2 z2 (or_intror (or_intror (or_introl eq_refl)))) as (zz2 & ->).
      destruct xs1' as [|? ?]; [|exfalso; destruct o; cbn in Halu1; discriminate Halu1].
      destruct xs2' as [|? ?]; [|discriminate Hlen].
      (* `select`, the one operation of three arguments *)
      destruct o; cbn in Halu1 |- *; try discriminate Halu1.
      eexists _; split; [reflexivity | intros _; exact Hall].
Qed.

(** Capabilities related under a taint other than [taint_all] are equal. *)
Lemma cap_eq_of_not_all : forall tc (c1 c2 : cap),
  (c1 <> c2 -> tc = taint_all) -> tc <> taint_all -> c1 = c2.
Proof.
  intros tc c1 c2 Himp Hn. destruct (cap_eqb c1 c2) eqn:Ec.
  - destruct c1, c2; cbn in Ec; try discriminate; try reflexivity;
      try (apply Z.eqb_eq in Ec; congruence); apply term_eqb_eq in Ec; congruence.
  - exfalso; apply Hn, Himp; intros ->; destruct c2; cbn in Ec;
      try rewrite Z.eqb_refl in Ec; try rewrite term_eqb_refl in Ec; discriminate.
Qed.

(** `map_option` preserves list length. *)
Lemma map_option_len : forall (A B : Type) (f : A -> option B) xs ys,
  map_option f xs = Some ys -> length ys = length xs.
Proof.
  intros A B f xs. induction xs as [|x xs IH]; intros ys H; cbn in *.
  - injection H as <-; reflexivity.
  - destruct (f x); [|discriminate H]. destruct (map_option f xs) eqn:Em; [|discriminate H].
    injection H as <-; cbn; f_equal; exact (IH _ eq_refl).
Qed.

Local Transparent Z.pow.

(** Shared lemma for all non-pointer [pure_scalar_op] cases of `Let`. *)
Lemma scalar_let_step_rel : forall pol ge e1 e2 m1 m2 ps d k o args cls wts ts xs1 r1 m1',
  pure_scalar_op o = true ->
  k <> P -> k <> A -> k <> F ->
  (forall v, o <> CheckLocal v 0 0 Read 1) ->
  env_rel (ps_tenv ps) e1 e2 ->
  op_arg_classes o k = Some cls ->
  map2_option (value_t (ps_tenv ps)) cls args = Some wts ->
  map_option scalar_wt wts = Some ts ->
  op_checks_vartime pol o k && t_vartime (join_taints ts) = false ->
  map2_option (value_x ge e1) cls args = Some xs1 ->
  op_res o k xs1 m1 = Some (OpRes (RVal r1) m1') ->
  exists n1 n2 xs2,
    r1 = WInt n1 /\ m1' = m1 /\
    map2_option (value_x ge e2) cls args = Some xs2 /\
    op_res o k xs2 m2 = Some (OpRes (RVal (WInt n2)) m2) /\
    (op_checks_vartime pol o k = true -> xs1 = xs2) /\
    env_rel (put d (WTInt (join_taints ts)) (ps_tenv ps)) (put d (WInt n1) e1) (put d (WInt n2) e2).
Proof.
  intros pol ge e1 e2 m1 m2 ps d k o args cls wts ts xs1 r1 m1' Hpure HkP HkA HkF _ Henv Ecls Ewts Ets Evt Exs1 Eop1.
  destruct (map2_value_rel ge _ _ _ cls args xs1 wts Henv Exs1 Ewts) as (xs2 & Exs2 & Hfor).
  assert (Hlen : length xs1 = length xs2).
  { rewrite (map2_option_len _ _ _ _ _ _ _ Exs1), (map2_option_len _ _ _ _ _ _ _ Exs2); reflexivity. }
  destruct (pure_scalar_op_rel pol o k cls xs1 xs2 wts ts m1 m2 r1 m1'
              Hpure HkP HkA HkF Ecls Hlen Hfor Ets Evt Eop1) as (n1 & n2 & -> & -> & Eop2 & Hdiff).
  exists n1, n2, xs2. repeat split; auto.
  - intros Evtc. destruct (scalar_args_eq_or_all wts xs1 xs2 ts Hfor Ets Hlen) as [E | Hall]; [exact E|].
    rewrite Evtc, Hall in Evt; discriminate Evt.
  - apply env_rel_put; [exact Henv | exact Hdiff].
Qed.

Lemma effects_eqb_eq : forall es es', effects_eqb es es' = true -> es = es'.
Proof.
  induction es as [|e es IH]; destruct es' as [|e' es'];
    cbn [effects_eqb List.length combine forallb Nat.eqb]; intros H;
    try discriminate H; [reflexivity|].
  apply andb_true_iff in H as [Hlen Hrest].
  apply andb_true_iff in Hrest as [He Htail].
  assert (e = e') by (destruct e, e'; cbn in He; congruence).
  subst e'; f_equal; apply IH; unfold effects_eqb; apply andb_true_iff; auto.
Qed.

Lemma pure_scalar_special_let : forall o,
  pure_scalar_op o = true -> special_let o = false.
Proof.
  destruct o; intros H; try discriminate H; reflexivity.
Qed.

Lemma pure_scalar_doomed : forall ge fr m d k o args out0,
  fr_doomed fr = None ->
  pure_scalar_op o = true ->
  doomed_result ge fr m (Let d k o args) out0 = Some (out0, None).
Proof.
  intros ge fr m d k o args out0 Hd Hp.
  unfold doomed_result; rewrite Hd.
  destruct k; destruct o; try discriminate Hp; destruct out0 as [|[]| | |]; reflexivity.
Qed.

Lemma let_tstep_pure_scalar : forall pol ge e ps d k o args,
  is_zero_idiom o k args = false ->
  pure_scalar_op o = true ->
  k <> P -> k <> A -> k <> F ->
  let_tstep pol ge e ps d k o args =
    match op_arg_classes o k with
    | Some cls =>
        match map2_option (value_t (ps_tenv ps)) cls args with
        | Some wts =>
            match map_option scalar_wt wts with
            | Some ts =>
                let tj := join_taints ts in
                if op_checks_vartime pol o k && t_vartime tj then TFault CannotVarTimeOp
                else TNext (mkPState (put d (WTInt tj) (ps_tenv ps)) (ps_callers ps) (ps_mem ps) (ps_aux ps))
            | None => TStuck "op_scalar"
            end
        | None => TStuck "op_args"
        end
    | None => TStuck "op_cls"
    end.
Proof.
  intros pol ge e ps d k o args Ez Ep HkP HkA HkF.
  unfold let_tstep; rewrite Ez.
  destruct k; try contradiction; destruct o; try discriminate Ep; reflexivity.
Qed.

Lemma leak_of_pure_scalar : forall pol ge c l d k o args rest j,
  fr_at (c_frame c) = Exec l (Let d k o args :: rest) j ->
  is_zero_idiom o k args = false ->
  pure_scalar_op o = true ->
  leak_of pol ge c =
    if op_checks_vartime pol o k then
      match op_arg_classes o k with
      | Some cls =>
          match map2_option (value_x ge (fr_env (c_frame c))) cls args with
          | Some xs => LeakVarTime o xs
          | None => LeakPure
          end
      | None => LeakPure
      end
    else LeakPure.
Proof.
  intros pol ge c l d k o args rest j Hat Ez Ep.
  unfold leak_of; rewrite Hat; cbn -[op_arg_classes]; rewrite Ez.
  destruct o; try discriminate Ep; cbn [pure_scalar_op andb]; reflexivity.
Qed.

(** Single-step 2-run constant-time soundness (`pstep_ct_sound`):
    under any policy [pol] with `pol_check_branches pol = true` (such as
    [pol_default] and [pol_strict]), and with `ge_free ge = free_res`,
    if `(c1, c2)` satisfy [ct_rel] under [ps] and
    `pstep pol ge c1 ps = PNext c1' ps'`, then:
    1. `(c1, c2)` emit the exact same [leak_event] (`leak_of pol ge c1 = leak_of pol ge c2`),
    2. `pstep pol ge c2 ps = PNext c2' ps'` for a matching `c2'`, and
    3. `ct_rel c1' c2' ps'` holds again. *)
Theorem pstep_ct_sound : forall pol ge c1 c2 ps c1' ps',
  pol_check_branches pol = true ->
  ge_free ge = free_res ->
  ct_rel c1 c2 ps ->
  pstep pol ge c1 ps = PNext c1' ps' ->
  leak_of pol ge c1 = leak_of pol ge c2 /\
  exists c2', pstep pol ge c2 ps = PNext c2' ps' /\ ct_rel c1' c2' ps'.
Proof.
  intros pol ge c1 c2 ps c1' ps' Hcb Hfree Hrel Hp1.
  pose proof (pstep_erases pol ge c1 ps) as Hstep.
  rewrite Hp1 in Hstep.
  destruct Hrel as (Hfn & Hloc & Hd1 & Hd2 & Hat & Hfuel & Hreg & Hcallers & Henv & Hmem & Haux).
  unfold pstep in *.
  unfold tstep in Hp1. rewrite Hd1 in Hp1.
  destruct (fr_at (c_frame c1)) as [xs l | l from | l [|i rest] j] eqn:Eat1.
  - discriminate Hp1.
  - (* Enter l from *)
    destruct (c_fuel c1 =? 0) eqn:Ef0.
    + destruct (step ge c1); discriminate Hp1.
    + destruct (find_block l (fn_blocks (fr_fn (c_frame c1)))) as [b|] eqn:Eblk; [|discriminate Hp1].
      destruct (phis_tenv (b_phis b) from (ps_tenv ps)) as [te'|] eqn:Epte; [|discriminate Hp1].
      unfold step in Hp1; rewrite Eat1, Ef0, Eblk in Hp1; cbn [or_stuck] in Hp1.
      destruct (phis_env ge (b_phis b) from (fr_env (c_frame c1))) as [e1'|] eqn:Epe1; [|discriminate Hp1].
      injection Hp1 as <- <-.
      destruct (phis_rel ge (b_phis b) from _ _ _ _ _ Henv Epe1 Epte) as (e2' & Epe2 & Henv').
      split; [unfold leak_of; rewrite Eat1, <- Hat, Ef0, <- Hfuel, Ef0; reflexivity|].
      unfold tstep, step; rewrite Hd2, <- Hat, <- Hfuel, Ef0, <- Hfn, Eblk, Epte, Epe2; cbn [or_stuck].
      eexists; split; [reflexivity|].
      unfold ct_rel; cbn; repeat split; auto; congruence.
  - (* Jump *)
    unfold step in Hp1; rewrite Eat1 in Hp1; unfold jump_step in Hp1; rewrite Hd1 in Hp1.
    destruct j as [t | v t1 t2 | v | vs | | ]; cbn [jump_tstep] in Hp1; try discriminate Hp1.
    + unfold edge_step in Hp1; rewrite Hd1 in Hp1; destruct t;
        injection Hp1 as <- <-;
        (split; [unfold leak_of; rewrite Eat1, <- Hat; reflexivity|]);
        unfold tstep, step, jump_step, edge_step; rewrite Hd2, <- Hat; cbn [jump_tstep]; rewrite ?Hd2;
        eexists; (split; [reflexivity|]);
        unfold ct_rel, continue_at, with_point; cbn; repeat split; auto; congruence.
    + destruct (value_t (ps_tenv ps) W v) as [[tv| |]|] eqn:Evt; try discriminate Hp1.
      destruct (t_branch tv) eqn:Etb; [discriminate Hp1|].
      unfold or_stuck in Hp1.
      destruct (value_x ge (fr_env (c_frame c1)) W v) as [[n1| |]|] eqn:Ev1; try discriminate Hp1.
      destruct (value_rel ge _ _ _ W v (WInt n1) (WTInt tv) Henv Ev1 Evt) as (w2 & Ev2 & Hw).
      destruct w2 as [n2| |]; try contradiction Hw.
      assert (En : n1 = n2) by (destruct (Z.eq_dec n1 n2) as [E|Hne]; [exact E | exfalso; apply Hw in Hne; subst tv; discriminate Etb]).
      subst n2. unfold edge_step in Hp1; rewrite Hd1 in Hp1.
      destruct (if n1 =? 0 then t2 else t1) as [tl | tl] eqn:Etgt;
        injection Hp1 as <- <-;
        (split; [unfold leak_of; rewrite Eat1, <- Hat, Ev1, Ev2; reflexivity|]);
        unfold tstep, step, jump_step, or_stuck, edge_step;
        rewrite Hd2, <- Hat; cbn [jump_tstep]; rewrite Evt, Etb, ?Hd2, Ev2, Etgt;
        eexists; (split; [reflexivity|]);
        unfold ct_rel, continue_at, with_point; cbn; repeat split; auto; congruence.
    + destruct (fn_ret (fr_fn (c_frame c1))) as [rk | | ] eqn:Eret; try discriminate Hp1.
      destruct (value_t (ps_tenv ps) rk v) as [wt|] eqn:Evt; [|discriminate Hp1].
      unfold return_tstep in Hp1.
      destruct (ps_callers ps) as [|[caller_te r] tcs] eqn:Etcs.
      * match type of Hp1 with context [match ?x with Done _ => _ | _ => _ end] => destruct x; discriminate Hp1 end.
      * destruct (returned_tenv r [wt] caller_te) as [te'|] eqn:Erte; [|discriminate Hp1].
        unfold or_stuck in Hp1.
        destruct (value_x ge (fr_env (c_frame c1)) rk v) as [w1|] eqn:Ev1; [|discriminate Hp1].
        destruct (value_rel ge _ _ _ rk v w1 wt Henv Ev1 Evt) as (w2 & Ev2 & Hw).
        unfold return_step, or_stuck in Hp1.
        destruct (c_callers c1) as [|[caller1 pd1] cs1], (c_callers c2) as [|[caller2 pd2] cs2] eqn:Ecs2;
          try contradiction Hcallers.
        destruct Hcallers as (Hcfn & Hcloc & Hcd1 & Hcd2 & Hcat & -> & -> & Hcenv & Hcs).
        destruct (invalidate_locals (fr_locals (c_frame c1)) (c_mem c1)) as [m1'|] eqn:Einv1; [|discriminate Hp1].
        destruct (invalidate_locals_rel _ _ _ _ _ _ Hreg Hmem Haux Einv1) as (m2' & Einv2 & Hreg' & Hmem' & Haux').
        cbn [pd_conv pd_res] in Hp1.
        destruct (returned_env r (Ret w1) (fr_env caller1)) as [ce1'|] eqn:Erce1; [|discriminate Hp1].
        injection Hp1 as <- <-.
        assert (Hret_rel : exists ce2', returned_env r (Ret w2) (fr_env caller2) = Some ce2' /\ env_rel te' ce1' ce2').
        { destruct r as [| d rk' | rs]; cbn in Erte, Erce1 |- *.
          - injection Erte as <-; injection Erce1 as <-. exists (fr_env caller2); auto.
          - destruct (wt_at_class rk' wt) as [wt'|] eqn:Ewt'; [|discriminate Erte].
            destruct (word_at_class rk' w1) as [y1|] eqn:Ey1; [|discriminate Erce1].
            injection Erte as <-; injection Erce1 as <-.
            destruct rk', wt, w1, w2; cbn in *; try contradiction Hw; try discriminate Ewt'; try discriminate Ey1;
              injection Ewt' as <-; injection Ey1 as <-;
              eexists; (split; [reflexivity|]); apply env_rel_put; try exact Hcenv; cbn in *;
              try (intros Hne; apply Hw; congruence); exact Hw.
          - discriminate Erce1. }
        destruct Hret_rel as (ce2' & Erce2 & Hcenv').
        split; [unfold leak_of; rewrite Eat1, <- Hat; reflexivity|].
        unfold tstep, step; unfold jump_step, return_step, or_stuck; cbv zeta.
        rewrite Hd2, <- Hat; cbn [jump_tstep]; unfold return_tstep;
        rewrite <- Hfn, Eret, Evt, Etcs, Erte, ?Hd2, Ev2, <- Hloc, Einv2, Ecs2; cbn - [returned_env].
        rewrite Erce2; cbn. eexists; split; [reflexivity|].
        unfold ct_rel; cbn; repeat split; auto; congruence.
    + destruct (fn_ret (fr_fn (c_frame c1))) eqn:Eret; try discriminate Hp1.
      unfold return_tstep, return_step, or_stuck in Hp1.
      destruct (ps_callers ps) as [|[caller_te r] tcs] eqn:Etcs.
      * match type of Hp1 with context [match ?x with Done _ => _ | _ => _ end] => destruct x; discriminate Hp1 end.
      * destruct (c_callers c1) as [|[caller1 pd1] cs1], (c_callers c2) as [|[caller2 pd2] cs2] eqn:Ecs2;
          try contradiction Hcallers.
        destruct Hcallers as (Hcfn & Hcloc & Hcd1 & Hcd2 & Hcat & -> & -> & Hcenv & Hcs).
        destruct (returned_tenv r [] caller_te) as [te'|] eqn:Erte; [|discriminate Hp1].
        destruct (invalidate_locals (fr_locals (c_frame c1)) (c_mem c1)) as [m1'|] eqn:Einv1; [|discriminate Hp1].
        destruct (invalidate_locals_rel _ _ _ _ _ _ Hreg Hmem Haux Einv1) as (m2' & Einv2 & Hreg' & Hmem' & Haux').
        cbn [pd_conv pd_res] in Hp1.
        destruct (returned_env r RetVoid (fr_env caller1)) as [ce1'|] eqn:Erce1; [|discriminate Hp1].
        destruct r; try discriminate Erce1; cbn in Erte, Erce1;
          injection Erte as <-; injection Erce1 as <-; injection Hp1 as <- <-.
        split; [unfold leak_of; rewrite Eat1, <- Hat; reflexivity|].
        unfold tstep, step; unfold jump_step, return_step, or_stuck; cbv zeta.
        rewrite Hd2, <- Hat; cbn [jump_tstep]; unfold return_tstep;
        rewrite <- Hfn, Eret, Etcs, ?Hd2, <- Hloc, Einv2, Ecs2; cbn.
        eexists; split; [reflexivity|].
        unfold ct_rel; cbn; repeat split; auto; congruence.
  - (* Instruction *)
    unfold step in Hp1; rewrite Eat1, Hd1 in Hp1; cbn [or_stuck] in Hp1.
    destruct i as [d k o args | d o args lw | w off v av | off v av es | r cl args | r cl args | x sz | file line | tq];
      cbn [inst_tstep] in Hp1; try discriminate Hp1.
    + (* Let *)
      destruct (is_zero_idiom o k args) eqn:Ezero.
      * unfold let_tstep in Hp1; rewrite Ezero in Hp1.
        unfold is_zero_idiom in Ezero; apply andb_true_iff in Ezero as [Hint Exy].
        destruct o; try discriminate Exy.
        all: destruct args as [|v1 [|v2 [|]]]; try discriminate Exy; [destruct v1; discriminate Exy | | destruct v1, v2; discriminate Exy].
        all: destruct v1 as [nx| |], v2 as [ny| |]; try discriminate Exy.
        all: apply term_eqb_eq in Exy; subst ny; destruct k; try discriminate Hint;
          cbn [inst_step op_arg_classes map2_option] in Hp1;
          destruct (value_x ge (fr_env (c_frame c1)) _ (Tmp nx)) as [wx1|] eqn:Ewx1; try discriminate Hp1;
          cbn in Hp1; destruct wx1 as [z1| |]; try discriminate Hp1;
          destruct (Henv nx) as [[E1 _] | (u1 & u2 & ut & E1 & E2 & Et & Hure)];
          try (cbn in Ewx1; rewrite E1 in Ewx1; discriminate Ewx1);
          cbn in Ewx1; rewrite E1 in Ewx1; destruct u1; try discriminate Ewx1;
          destruct u2 as [u2z| |], ut; try contradiction Hure;
          try rewrite Z.lxor_nilpotent in Hp1; try rewrite Z.sub_diag in Hp1; cbn in Hp1;
          injection Hp1 as <- <-;
          (split; [unfold leak_of; rewrite Eat1, <- Hat; cbn; try rewrite term_eqb_refl; try rewrite Pos.eqb_refl; reflexivity|]);
          unfold tstep, step; rewrite Hd2, <- Hat; cbn [inst_tstep let_tstep is_zero_idiom int_class or_stuck inst_step op_arg_classes map2_option];
          unfold let_tstep; cbn [is_zero_idiom int_class];
          try rewrite term_eqb_refl; try rewrite Pos.eqb_refl; cbn [value_x andb]; rewrite E2; cbn;
          try rewrite Z.lxor_nilpotent; try rewrite Z.sub_diag; cbn;
          unfold name_eqb; rewrite ?term_eqb_refl; cbn;
          eexists; (split; [reflexivity|]);
          unfold ct_rel; cbn; repeat split; auto; try congruence;
          (apply env_rel_put; [exact Henv | intros Hne; congruence]).
      * (* Non-zero-idiom Let: handle pointer Add/Sub first, then pure_scalar_op, then specific ops *)
        destruct (pure_scalar_op o) eqn:Epure.
        -- (* Either Add/Sub at P, or scalar op *)
           assert (Hclasses : k = P \/ k = A \/ k = F \/ (k <> P /\ k <> A /\ k <> F))
             by (destruct k; intuition discriminate).
           destruct Hclasses as [-> | [-> | [-> | (HkP & HkA & HkF)]]].
           1: { (* k = P: only Add or Sub allowed *)
             unfold let_tstep in Hp1; rewrite Ezero in Hp1.
             destruct o; try discriminate Epure; try (cbn in Hp1; discriminate Hp1).
             all: destruct args as [|pv [|ov [|]]]; try discriminate Hp1.
             all: try solve [cbn [op_arg_classes map2_option] in Hp1;
               destruct (value_t (ps_tenv ps) P pv); cbn in Hp1;
               try destruct (value_t (ps_tenv ps) L ov); discriminate Hp1].
             all: destruct (value_t (ps_tenv ps) P pv) as [[|ta tc|]|] eqn:Et_pv; try discriminate Hp1;
               destruct (value_t (ps_tenv ps) L ov) as [[toff| |]|] eqn:Et_ov; try discriminate Hp1;
               cbn [inst_step op_arg_classes map2_option] in Hp1;
               destruct (value_x ge (fr_env (c_frame c1)) P pv) as [[|p1|]|] eqn:Ewp1; try discriminate Hp1;
               destruct (value_x ge (fr_env (c_frame c1)) L ov) as [[no1| |]|] eqn:Ewo1; try discriminate Hp1;
               cbn in Hp1; injection Hp1 as <- <-;
               destruct (value_rel ge _ _ _ P pv (WPtr p1) (WTPtr ta tc) Henv Ewp1 Et_pv) as ([|p2|] & Ewp2 & Hwp); try contradiction Hwp;
               destruct (value_rel ge _ _ _ L ov (WInt no1) (WTInt toff) Henv Ewo1 Et_ov) as ([no2| |] & Ewo2 & Hwo); try contradiction Hwo;
               (split; [unfold leak_of; rewrite Eat1, <- Hat; cbn; rewrite ?Ezero; reflexivity|]);
               unfold tstep, step; rewrite Hd2, <- Hat; cbn [inst_tstep]; unfold let_tstep; rewrite Ezero; cbn; rewrite Et_pv, Et_ov;
               cbn [or_stuck inst_step op_arg_classes map2_option]; rewrite Ewp2, Ewo2; cbn;
               eexists; (split; [reflexivity|]);
               unfold ct_rel; cbn; repeat split; auto; try congruence;
               (apply env_rel_put; [exact Henv | cbn in *; split; [|exact (proj2 Hwp)]; intros Hne;
                 destruct (Z.eq_dec (ptr_addr p1) (ptr_addr p2)) as [Ea|Hna];
                 [assert (no1 <> no2) by congruence; rewrite (Hwo H), taint_join_all_r; reflexivity
                 |rewrite (proj1 Hwp Hna), taint_join_all_l; reflexivity]]). }
           1: { unfold let_tstep in Hp1; rewrite Ezero in Hp1; destruct o; try discriminate Epure; cbn in Hp1; discriminate Hp1. }
           1: { unfold let_tstep in Hp1; rewrite Ezero in Hp1; destruct o; try discriminate Epure; cbn in Hp1; discriminate Hp1. }
           { (* k in W, L, Single, Double, Extended *)
             rewrite let_tstep_pure_scalar in Hp1 by assumption.
             rewrite inst_step_let in Hp1 by (apply pure_scalar_special_let; exact Epure).
             destruct (op_arg_classes o k) as [cls|] eqn:Ecls; [|discriminate Hp1].
             destruct (map2_option (value_t (ps_tenv ps)) cls args) as [wts|] eqn:Ewts; [|discriminate Hp1].
             destruct (map_option scalar_wt wts) as [ts|] eqn:Ets; [|discriminate Hp1].
             cbv zeta in Hp1.
             destruct (op_checks_vartime pol o k && t_vartime (join_taints ts)) eqn:Evt; [discriminate Hp1|].
             cbn [or_stuck] in Hp1.
             destruct (map2_option (value_x ge (fr_env (c_frame c1))) cls args) as [xs1|] eqn:Exs1; [|discriminate Hp1].
             cbn beta iota zeta in Hp1.
             destruct (op_res o k xs1 (c_mem c1)) as [[[r1| |] m1'| |]|] eqn:Eop1;
               try (try (rewrite pure_scalar_doomed in Hp1 by assumption); cbn in Hp1; discriminate Hp1).
             rewrite pure_scalar_doomed in Hp1 by assumption; cbn in Hp1.
             injection Hp1 as <- <-.
             destruct (scalar_let_step_rel pol ge _ _ (c_mem c1) (c_mem c2) ps d k o args cls wts ts xs1 r1 m1'
                         Epure HkP HkA HkF
                         ltac:(intros ? ?; subst o; discriminate Epure) Henv Ecls Ewts Ets Evt Exs1 Eop1)
               as (n1 & n2 & xs2 & -> & -> & Exs2 & Eop2 & Hxs_eq & Henv').
             split.
             { rewrite (leak_of_pure_scalar pol ge c1 l d k o args rest j Eat1 Ezero Epure),
                       (leak_of_pure_scalar pol ge c2 l d k o args rest j (eq_sym Hat) Ezero Epure).
               destruct (op_checks_vartime pol o k) eqn:Evtc; [|reflexivity].
               rewrite Ecls, Exs1, Exs2, (Hxs_eq eq_refl); reflexivity. }
             unfold tstep, step; rewrite Hd2, <- Hat; cbn [inst_tstep or_stuck].
             rewrite let_tstep_pure_scalar by assumption.
             rewrite Ecls, Ewts, Ets; cbv zeta; rewrite Evt.
             rewrite inst_step_let by (apply pure_scalar_special_let; exact Epure); cbv zeta.
             rewrite Ecls; cbn beta iota zeta; rewrite Exs2; cbn beta iota zeta.
             rewrite Eop2; rewrite pure_scalar_doomed by assumption; cbn.
             eexists; split; [reflexivity|].
             unfold ct_rel; cbn; repeat split; auto; congruence. }
        -- (* pure_scalar_op o = false *)
           unfold let_tstep in Hp1; rewrite Ezero in Hp1.
           destruct o; try discriminate Epure; try discriminate Hp1;
             try rename align into al;
             try (rewrite inst_step_let in Hp1 by reflexivity).
           ++ (* Copy *)
              destruct args as [|v [|]]; try discriminate Hp1.
              destruct (value_t (ps_tenv ps) k v) as [wt|] eqn:Ewt; [|discriminate Hp1].
              cbn [op_arg_classes map2_option] in Hp1.
              destruct (value_x ge (fr_env (c_frame c1)) k v) as [w1|] eqn:Ew1; [|discriminate Hp1].
              destruct (value_rel ge _ _ _ k v w1 wt Henv Ew1 Ewt) as (w2 & Ew2 & Hw).
              destruct k; cbn [op_res fmt_of float_arithmetic op_res_int alu] in Hp1;
                try (destruct w1; try discriminate Hp1);
                injection Hp1 as <- <-;
                (split; [unfold leak_of; rewrite Eat1, <- Hat; cbn; reflexivity|]);
                unfold tstep, step; rewrite Hd2, <- Hat; cbn [inst_tstep]; unfold let_tstep; rewrite Ezero; cbn; rewrite Ewt;
                cbn [or_stuck inst_step op_arg_classes map2_option]; rewrite Ew2;
                try (destruct wt, w2; try contradiction Hw); cbn;
                eexists; (split; [reflexivity|]);
                unfold ct_rel; cbn; repeat split; auto; try congruence;
                apply env_rel_put; assumption.
           ++ (* Ptoi *)
              destruct args as [|v [|]]; try discriminate Hp1.
              destruct (value_t (ps_tenv ps) P v) as [[ta | ta tc | ]|] eqn:Ewt; try discriminate Hp1;
                cbn [inst_step op_arg_classes map2_option] in Hp1;
                destruct (value_x ge (fr_env (c_frame c1)) P v) as [w1|] eqn:Ew1; try discriminate Hp1;
                destruct (value_rel ge _ _ _ P v w1 _ Henv Ew1 Ewt) as (w2 & Ew2 & Hw);
                destruct w1 as [|p1|], w2 as [|p2|]; try contradiction Hw;
                cbn [op_res op_res_int alu] in Hp1;
                destruct k; try discriminate Hp1;
                try (cbn [fmt_of] in Hp1; injection Hp1 as <- <-;
                     (split; [unfold leak_of; rewrite Eat1, <- Hat; cbn; reflexivity|]);
                     unfold tstep, step; rewrite Hd2, <- Hat; cbn [inst_tstep]; unfold let_tstep; rewrite Ezero; cbn; rewrite Ewt;
                     cbn [or_stuck inst_step op_arg_classes map2_option]; rewrite Ew2; cbn;
                     eexists; (split; [reflexivity|]);
                     unfold ct_rel; cbn; repeat split; auto; try congruence;
                     apply env_rel_put; [exact Henv | exact (proj1 Hw)]).
           ++ (* Itop *)
              destruct args as [|v [|]]; try discriminate Hp1.
              destruct (value_t (ps_tenv ps) L v) as [[ta| | ]|] eqn:Ewt; try discriminate Hp1.
              cbn [inst_step op_arg_classes map2_option] in Hp1.
              destruct (value_x ge (fr_env (c_frame c1)) L v) as [w1|] eqn:Ew1; [|discriminate Hp1].
              destruct (value_rel ge _ _ _ L v w1 (WTInt ta) Henv Ew1 Ewt) as (w2 & Ew2 & Hw).
              destruct w1 as [n1| |], w2 as [n2| |]; try contradiction Hw.
              destruct k; cbn [op_res fmt_of op_res_int alu] in Hp1; try discriminate Hp1;
                injection Hp1 as <- <-;
                (split; [unfold leak_of; rewrite Eat1, <- Hat; cbn; reflexivity|]);
                unfold tstep, step; rewrite Hd2, <- Hat; cbn [inst_tstep]; unfold let_tstep; rewrite Ezero; cbn; rewrite Ewt;
                cbn [or_stuck inst_step op_arg_classes map2_option]; rewrite Ew2; cbn;
                eexists; (split; [reflexivity|]);
                unfold ct_rel; cbn; repeat split; auto; try congruence;
                (apply env_rel_put; [exact Henv | cbn; split; [exact Hw | congruence]]).
           ++ (* Alloc: returns TFresh or TDone, never TNext *)
              destruct args as [|v [|]]; try discriminate Hp1.
              destruct (value_x ge _ L v) as [[sz| |]|]; try discriminate Hp1.
              destruct (value_t _ L v) as [[tsz| |]|]; try discriminate Hp1.
              destruct (t_branch tsz); [discriminate Hp1|].
              destruct (t_index tsz); [discriminate Hp1|].
              destruct (max_allocation_size <? sz);
                match type of Hp1 with context [match ?s with _ => _ end] => destruct s; discriminate Hp1 end.
           ++ (* Check *)
              destruct args as [|v [|]]; try discriminate Hp1.
              destruct (value_t (ps_tenv ps) P v) as [[|ta tc|]|] eqn:Ewt; try discriminate Hp1.
              destruct (check_ptr_bounds_taint pol ta tc) eqn:Echk; [discriminate Hp1|].
              destruct (check_ptr_bounds_not_all pol ta tc Hcb Echk) as [Hta Htc].
              cbn [inst_step op_arg_classes map2_option] in Hp1.
              destruct (value_x ge (fr_env (c_frame c1)) P v) as [w1|] eqn:Ew1; [|discriminate Hp1].
              destruct (value_rel ge _ _ _ P v w1 (WTPtr ta tc) Henv Ew1 Ewt) as (w2 & Ew2 & Hw).
              destruct w1 as [|[a1 c1p]|], w2 as [|[a2 c2p]|]; try contradiction Hw.
              assert (Ep : a1 = a2 /\ c1p = c2p) by
                (cbn in Hw; split; [destruct (Z.eq_dec a1 a2); [auto | exfalso; apply Hta, (proj1 Hw); auto]
                                   |exact (cap_eq_of_not_all tc _ _ (proj2 Hw) Htc)]).
              destruct Ep as [<- <-].
              destruct k; cbn [op_res fmt_of op_res_int] in Hp1; try discriminate Hp1.
              unfold access_res in Hp1; rewrite Hreg in Hp1.
              destruct (cap_access_res c1p (m_regions (c_mem c2)) (raw_address a1 lo) (hi - lo) r al) as [[[]| |]|] eqn:Ecap; try discriminate Hp1.
              all: cbn in Hp1; rewrite ?Ecap, ?Hd1 in Hp1; cbn in Hp1; try discriminate Hp1.
              injection Hp1 as <- <-.
              split; [unfold leak_of; rewrite Eat1, <- Hat; cbn; rewrite Hcb, Ew1, Ew2; reflexivity|].
              unfold tstep, step; rewrite Hd2, <- Hat; cbn [inst_tstep]; unfold let_tstep; rewrite Ezero; cbn; rewrite Ewt, Echk;
                cbn [or_stuck inst_step op_arg_classes map2_option]; rewrite Ew2; cbn [op_res fmt_of op_res_int];
                unfold access_res; cbn [ptr_addr ptr_cap]; rewrite Ecap; cbn.
              eexists; split; [reflexivity|].
              unfold ct_rel; cbn; repeat split; auto; try congruence.
              apply env_rel_put; [exact Henv | exact Hw].
           ++ (* Renew *)
              destruct args as [|q1v [|v [|]]]; try discriminate Hp1.
              destruct (value_t (ps_tenv ps) A q1v) as [[|qa qc|]|] eqn:Ewq; try discriminate Hp1.
              destruct (value_t (ps_tenv ps) P v) as [[|ta tc|]|] eqn:Ewt; try discriminate Hp1.
              destruct (check_ptr_bounds_taint pol (taint_join qa ta) (taint_join qc tc)) eqn:Echk; [discriminate Hp1|].
              destruct (check_ptr_bounds_not_all pol _ _ Hcb Echk) as [Hta Htc].
              cbn [inst_step op_arg_classes map2_option] in Hp1.
              destruct (value_x ge (fr_env (c_frame c1)) A q1v) as [wq1|] eqn:Ewq1; [|discriminate Hp1].
              destruct (value_x ge (fr_env (c_frame c1)) P v) as [w1|] eqn:Ew1; [|discriminate Hp1].
              destruct (value_rel ge _ _ _ A q1v wq1 (WTPtr qa qc) Henv Ewq1 Ewq) as (wq2 & Ewq2 & Hwq).
              destruct (value_rel ge _ _ _ P v w1 (WTPtr ta tc) Henv Ew1 Ewt) as (w2 & Ew2 & Hw).
              destruct wq1 as [|[qa1 qc1]|], wq2 as [|[qa2 qc2]|], w1 as [|[a1 c1p]|], w2 as [|[a2 c2p]|];
                try contradiction Hwq; try contradiction Hw.
              assert (Heq_all : qa1 = qa2 /\ qc1 = qc2 /\ a1 = a2 /\ c1p = c2p).
              { cbn in Hwq, Hw. repeat split.
                - destruct (Z.eq_dec qa1 qa2); [auto | exfalso; apply Hta; rewrite (proj1 Hwq n), taint_join_all_l; reflexivity].
                - destruct (cap_eqb qc1 qc2) eqn:Ec;
                    [destruct qc1, qc2; cbn in Ec; try discriminate; try reflexivity; try (apply Z.eqb_eq in Ec; congruence); apply term_eqb_eq in Ec; congruence
                    |exfalso; apply Htc; rewrite (proj2 Hwq ltac:(intros ->; destruct qc2; cbn in Ec; try rewrite Z.eqb_refl in Ec; try rewrite term_eqb_refl in Ec; discriminate)), taint_join_all_l; reflexivity].
                - destruct (Z.eq_dec a1 a2); [auto | exfalso; apply Hta; rewrite (proj1 Hw n), taint_join_all_r; reflexivity].
                - destruct (cap_eqb c1p c2p) eqn:Ec;
                    [destruct c1p, c2p; cbn in Ec; try discriminate; try reflexivity; try (apply Z.eqb_eq in Ec; congruence); apply term_eqb_eq in Ec; congruence
                    |exfalso; apply Htc; rewrite (proj2 Hw ltac:(intros ->; destruct c2p; cbn in Ec; try rewrite Z.eqb_refl in Ec; try rewrite term_eqb_refl in Ec; discriminate)), taint_join_all_r; reflexivity]. }
              destruct Heq_all as (-> & -> & -> & ->).
              destruct k; cbn [op_res fmt_of op_res_int] in Hp1; try discriminate Hp1.
              cbn [ptr_addr ptr_cap] in Hp1.
              destruct (cap_eqb qc2 c2p) eqn:Ece; [|cbn in Hp1; rewrite Hd1 in Hp1; discriminate Hp1].
              unfold access_res, renew_res in Hp1; rewrite Hreg in Hp1.
              destruct (cap_access_res c2p (m_regions (c_mem c2)) (raw_address a2 lo) (hi - lo) r al) as [[[]|why|why]|] eqn:Ecap;
                cbn in Hp1; rewrite ?Hd1 in Hp1; cbn in Hp1; try discriminate Hp1.
              all: try solve [repeat match type of Hp1 with context [match ?x with _ => _ end] =>
                lazymatch x with context [match _ with _ => _ end] => fail | _ =>
                destruct x; cbn in Hp1; rewrite ?Hd1 in Hp1; try discriminate Hp1 end end].
              injection Hp1 as <- <-.
              split; [unfold leak_of; rewrite Eat1, <- Hat; cbn; rewrite Hcb, Ew1, Ew2; reflexivity|].
              unfold tstep, step; rewrite Hd2, <- Hat; cbn [inst_tstep]; unfold let_tstep; rewrite Ezero; cbn; rewrite Ewq, Ewt, Echk;
                cbn [or_stuck inst_step op_arg_classes map2_option]; rewrite Ewq2, Ew2; cbn [op_res fmt_of op_res_int];
                cbn [ptr_addr ptr_cap]; rewrite Ece; unfold access_res; rewrite Ecap; cbn.
              eexists; split; [reflexivity|].
              unfold ct_rel; cbn; repeat split; auto; try congruence.
              apply env_rel_put; [exact Henv | exact Hw].
           ++ (* RenewHull *)
              destruct args as [|qlv [|qhv [|v [|]]]]; try discriminate Hp1.
              destruct (value_t (ps_tenv ps) A qlv) as [[|al0 cl0|]|] eqn:Ewql; try discriminate Hp1.
              destruct (value_t (ps_tenv ps) A qhv) as [[|ah0 ch0|]|] eqn:Ewqh; try discriminate Hp1.
              destruct (value_t (ps_tenv ps) P v) as [[|ta tc|]|] eqn:Ewt; try discriminate Hp1.
              destruct (check_ptr_bounds_taint pol _ _) eqn:Echk; [discriminate Hp1|].
              destruct (check_ptr_bounds_not_all pol _ _ Hcb Echk) as [Hta Htc].
              cbn [inst_step op_arg_classes map2_option] in Hp1.
              destruct (value_x ge (fr_env (c_frame c1)) A qlv) as [wql1|] eqn:Ewql1; [|discriminate Hp1].
              destruct (value_x ge (fr_env (c_frame c1)) A qhv) as [wqh1|] eqn:Ewqh1; [|discriminate Hp1].
              destruct (value_x ge (fr_env (c_frame c1)) P v) as [w1|] eqn:Ew1; [|discriminate Hp1].
              destruct (value_rel ge _ _ _ A qlv wql1 _ Henv Ewql1 Ewql) as (wql2 & Ewql2 & Hwql).
              destruct (value_rel ge _ _ _ A qhv wqh1 _ Henv Ewqh1 Ewqh) as (wqh2 & Ewqh2 & Hwqh).
              destruct (value_rel ge _ _ _ P v w1 _ Henv Ew1 Ewt) as (w2 & Ew2 & Hw).
              destruct wql1 as [|[la1 lc1]|], wql2 as [|[la2 lc2]|],
                       wqh1 as [|[ha1 hc1]|], wqh2 as [|[ha2 hc2]|],
                       w1 as [|[a1 c1p]|], w2 as [|[a2 c2p]|];
                try contradiction Hwql; try contradiction Hwqh; try contradiction Hw.
              assert (Heq_caps : lc1 = lc2 /\ hc1 = hc2 /\ a1 = a2 /\ c1p = c2p).
              { cbn in Hwql, Hwqh, Hw. repeat split.
                - destruct (cap_eqb lc1 lc2) eqn:Ec;
                    [destruct lc1, lc2; cbn in Ec; try discriminate; try reflexivity; try (apply Z.eqb_eq in Ec; congruence); apply term_eqb_eq in Ec; congruence
                    |exfalso; apply Htc; rewrite (proj2 Hwql ltac:(intros ->; destruct lc2; cbn in Ec; try rewrite Z.eqb_refl in Ec; try rewrite term_eqb_refl in Ec; discriminate)), taint_join_all_l; reflexivity].
                - destruct (cap_eqb hc1 hc2) eqn:Ec;
                    [destruct hc1, hc2; cbn in Ec; try discriminate; try reflexivity; try (apply Z.eqb_eq in Ec; congruence); apply term_eqb_eq in Ec; congruence
                    |exfalso; apply Htc; rewrite (proj2 Hwqh ltac:(intros ->; destruct hc2; cbn in Ec; try rewrite Z.eqb_refl in Ec; try rewrite term_eqb_refl in Ec; discriminate)), taint_join_all_l, taint_join_all_r; reflexivity].
                - destruct (Z.eq_dec a1 a2); [auto | exfalso; apply Hta; rewrite (proj1 Hw n), !taint_join_all_r; reflexivity].
                - destruct (cap_eqb c1p c2p) eqn:Ec;
                    [destruct c1p, c2p; cbn in Ec; try discriminate; try reflexivity; try (apply Z.eqb_eq in Ec; congruence); apply term_eqb_eq in Ec; congruence
                    |exfalso; apply Htc; rewrite (proj2 Hw ltac:(intros ->; destruct c2p; cbn in Ec; try rewrite Z.eqb_refl in Ec; try rewrite term_eqb_refl in Ec; discriminate)), !taint_join_all_r; reflexivity]. }
              destruct Heq_caps as (-> & -> & -> & ->).
              destruct k; cbn [op_res fmt_of op_res_int] in Hp1; try discriminate Hp1.
              cbn [ptr_addr ptr_cap] in Hp1.
              destruct (cap_eqb lc2 c2p && cap_eqb hc2 c2p) eqn:Ece; [|cbn in Hp1; rewrite Hd1 in Hp1; discriminate Hp1].
              unfold access_res, renew_res in Hp1; rewrite Hreg in Hp1.
              destruct (cap_access_res c2p (m_regions (c_mem c2)) (raw_address a2 lo) (hi - lo) r al) as [[[]|why|why]|] eqn:Ecap;
                cbn in Hp1; rewrite ?Hd1 in Hp1; cbn in Hp1; try discriminate Hp1.
              all: try solve [repeat match type of Hp1 with context [match ?x with _ => _ end] =>
                lazymatch x with context [match _ with _ => _ end] => fail | _ =>
                destruct x; cbn in Hp1; rewrite ?Hd1 in Hp1; try discriminate Hp1 end end].
              injection Hp1 as <- <-.
              split; [unfold leak_of; rewrite Eat1, <- Hat; cbn; reflexivity|].
              unfold tstep, step; rewrite Hd2, <- Hat; cbn [inst_tstep]; unfold let_tstep; rewrite Ezero; cbn; rewrite Ewql, Ewqh, Ewt, Echk;
                cbn [or_stuck inst_step op_arg_classes map2_option]; rewrite Ewql2, Ewqh2, Ew2; cbn [op_res fmt_of op_res_int];
                cbn [ptr_addr ptr_cap]; rewrite Ece; unfold access_res; rewrite Ecap; cbn.
              eexists; split; [reflexivity|].
              unfold ct_rel; cbn; repeat split; auto; try congruence.
              apply env_rel_put; [exact Henv | exact Hw].
           ++ (* HalfCheck *)
              destruct args as [|q1v [|v [|]]]; try discriminate Hp1.
              destruct (value_t (ps_tenv ps) A q1v) as [[|qa qc|]|] eqn:Ewq; try discriminate Hp1.
              destruct (value_t (ps_tenv ps) P v) as [[|ta tc|]|] eqn:Ewt; try discriminate Hp1.
              destruct (check_ptr_bounds_taint pol (taint_join qa ta) (taint_join qc tc)) eqn:Echk; [discriminate Hp1|].
              destruct (check_ptr_bounds_not_all pol _ _ Hcb Echk) as [Hta Htc].
              cbn [inst_step op_arg_classes map2_option] in Hp1.
              destruct (value_x ge (fr_env (c_frame c1)) A q1v) as [wq1|] eqn:Ewq1; [|discriminate Hp1].
              destruct (value_x ge (fr_env (c_frame c1)) P v) as [w1|] eqn:Ew1; [|discriminate Hp1].
              destruct (value_rel ge _ _ _ A q1v wq1 (WTPtr qa qc) Henv Ewq1 Ewq) as (wq2 & Ewq2 & Hwq).
              destruct (value_rel ge _ _ _ P v w1 (WTPtr ta tc) Henv Ew1 Ewt) as (w2 & Ew2 & Hw).
              destruct wq1 as [|[qa1 qc1]|], wq2 as [|[qa2 qc2]|], w1 as [|[a1 c1p]|], w2 as [|[a2 c2p]|];
                try contradiction Hwq; try contradiction Hw.
              assert (Heq_all : qc1 = qc2 /\ a1 = a2 /\ c1p = c2p).
              { cbn in Hwq, Hw. repeat split.
                - destruct (cap_eqb qc1 qc2) eqn:Ec;
                    [destruct qc1, qc2; cbn in Ec; try discriminate; try reflexivity; try (apply Z.eqb_eq in Ec; congruence); apply term_eqb_eq in Ec; congruence
                    |exfalso; apply Htc; rewrite (proj2 Hwq ltac:(intros ->; destruct qc2; cbn in Ec; try rewrite Z.eqb_refl in Ec; try rewrite term_eqb_refl in Ec; discriminate)), taint_join_all_l; reflexivity].
                - destruct (Z.eq_dec a1 a2); [auto | exfalso; apply Hta; rewrite (proj1 Hw n), taint_join_all_r; reflexivity].
                - destruct (cap_eqb c1p c2p) eqn:Ec;
                    [destruct c1p, c2p; cbn in Ec; try discriminate; try reflexivity; try (apply Z.eqb_eq in Ec; congruence); apply term_eqb_eq in Ec; congruence
                    |exfalso; apply Htc; rewrite (proj2 Hw ltac:(intros ->; destruct c2p; cbn in Ec; try rewrite Z.eqb_refl in Ec; try rewrite term_eqb_refl in Ec; discriminate)), taint_join_all_r; reflexivity]. }
              destruct Heq_all as (-> & -> & ->).
              destruct k; cbn [op_res fmt_of op_res_int] in Hp1; try discriminate Hp1.
              cbn [ptr_addr ptr_cap] in Hp1.
              destruct (cap_eqb qc2 c2p) eqn:Ece; [|cbn in Hp1; rewrite Hd1 in Hp1; discriminate Hp1].
              unfold access_res in Hp1; rewrite Hreg in Hp1.
              destruct (cap_access_res c2p (m_regions (c_mem c2)) (raw_address a2 lo) (hi - lo) r al) as [chk1|] eqn:Ecap; [|discriminate Hp1].
              cbn in Hp1.
              assert (Ehp : half_passes b (c_mem c1) (raw_address a2 lo) (hi - lo) c2p r al =
                            half_passes b (c_mem c2) (raw_address a2 lo) (hi - lo) c2p r al)
                by (unfold half_passes; rewrite Hreg; reflexivity).
              rewrite Ehp in Hp1.
              destruct (half_passes b (c_mem c2) (raw_address a2 lo) (hi - lo) c2p r al) as [[ok'|]|] eqn:Ehpass;
                cbn in Hp1; rewrite ?Hd1 in Hp1; try discriminate Hp1.
              destruct chk1 as [[]|why|why], ok'; cbn in Hp1; rewrite ?Hd1 in Hp1; try discriminate Hp1.
              all: try solve [destruct why; discriminate Hp1].
              all:
                injection Hp1 as <- <-;
                (split; [unfold leak_of; rewrite Eat1, <- Hat; cbn; rewrite Hcb, Ew1, Ew2; reflexivity|]);
                unfold tstep, step; rewrite Hd2, <- Hat; cbn [inst_tstep]; unfold let_tstep; rewrite Ezero; cbn; rewrite Ewq, Ewt, Echk;
                cbn [or_stuck inst_step op_arg_classes map2_option]; rewrite Ewq2, Ew2; cbn [op_res fmt_of op_res_int];
                cbn [ptr_addr ptr_cap]; rewrite Ece; unfold access_res; rewrite Ecap; cbn; rewrite Ehpass; cbn;
                eexists; (split; [reflexivity|]);
                unfold ct_rel; cbn; repeat split; auto; try congruence;
                (apply env_rel_put; [exact Henv | exact Hw]).
           ++ (* SpanTest *)
              destruct args as [|v [|]]; try discriminate Hp1.
              destruct (value_t (ps_tenv ps) P v) as [[|ta tc|]|] eqn:Ewt; try discriminate Hp1.
              destruct (check_ptr_bounds_taint pol ta tc) eqn:Echk; [discriminate Hp1|].
              destruct (check_ptr_bounds_not_all pol ta tc Hcb Echk) as [Hta Htc].
              cbn [inst_step op_arg_classes map2_option] in Hp1.
              destruct (value_x ge (fr_env (c_frame c1)) P v) as [w1|] eqn:Ew1; [|discriminate Hp1].
              destruct (value_rel ge _ _ _ P v w1 (WTPtr ta tc) Henv Ew1 Ewt) as (w2 & Ew2 & Hw).
              destruct w1 as [|[a1 c1p]|], w2 as [|[a2 c2p]|]; try contradiction Hw.
              assert (Ep : a1 = a2 /\ c1p = c2p) by
                (cbn in Hw; split; [destruct (Z.eq_dec a1 a2); [auto | exfalso; apply Hta, (proj1 Hw); auto]
                                   |destruct (cap_eqb c1p c2p) eqn:Ec;
                                     [destruct c1p, c2p; cbn in Ec; try discriminate; try reflexivity; try (apply Z.eqb_eq in Ec; congruence); apply term_eqb_eq in Ec; congruence
                                     |exfalso; apply Htc, (proj2 Hw); intros ->; destruct c2p; cbn in Ec; try rewrite Z.eqb_refl in Ec; try rewrite term_eqb_refl in Ec; discriminate]]).
              destruct Ep as [<- <-].
              destruct k; cbn [op_res fmt_of op_res_int] in Hp1; try discriminate Hp1.
              rewrite Hreg in Hp1.
              destruct c1p as [|base|base|fn|ext]; cbn in Hp1;
                try (destruct (object_region base (m_regions (c_mem c2))) as [reg|] eqn:Ereg; cbn in Hp1; [|discriminate Hp1]);
                injection Hp1 as <- <-;
                (split; [unfold leak_of; rewrite Eat1, <- Hat; cbn; rewrite Hcb, Ew1, Ew2; reflexivity|]);
                unfold tstep, step; rewrite Hd2, <- Hat; cbn [inst_tstep]; unfold let_tstep; rewrite Ezero; cbn; rewrite Ewt, Echk;
                cbn [or_stuck inst_step op_arg_classes map2_option]; rewrite Ew2; cbn [op_res fmt_of op_res_int];
                cbn; rewrite ?Ereg; cbn;
                eexists; (split; [reflexivity|]);
                unfold ct_rel; cbn; repeat split; auto; try congruence;
                (apply env_rel_put; [exact Henv | cbn; congruence]).
           ++ (* RenewIf *)
              destruct args as [|v [|gv [|]]]; try discriminate Hp1.
              destruct (value_t (ps_tenv ps) P v) as [[|ta tc|]|] eqn:Ewt; try discriminate Hp1.
              destruct (value_t (ps_tenv ps) W gv) as [[tg| |]|] eqn:Ewg; try discriminate Hp1.
              rewrite Hcb in Hp1; cbn [andb] in Hp1.
              destruct (t_branch tg) eqn:Etbg; [discriminate Hp1|].
              destruct (check_ptr_bounds_taint pol ta tc) eqn:Echk; [discriminate Hp1|].
              destruct (check_ptr_bounds_not_all pol ta tc Hcb Echk) as [Hta Htc].
              cbn [inst_step op_arg_classes map2_option] in Hp1.
              destruct (value_x ge (fr_env (c_frame c1)) P v) as [w1|] eqn:Ew1; [|discriminate Hp1].
              destruct (value_x ge (fr_env (c_frame c1)) W gv) as [wg1|] eqn:Ewg1; [|discriminate Hp1].
              destruct (value_rel ge _ _ _ P v w1 (WTPtr ta tc) Henv Ew1 Ewt) as (w2 & Ew2 & Hw).
              destruct (value_rel ge _ _ _ W gv wg1 (WTInt tg) Henv Ewg1 Ewg) as (wg2 & Ewg2 & Hwg).
              destruct w1 as [|[a1 c1p]|], w2 as [|[a2 c2p]|], wg1 as [ng1| |], wg2 as [ng2| |];
                try contradiction Hw; try contradiction Hwg.
              assert (Ep : a1 = a2 /\ c1p = c2p /\ ng1 = ng2).
              { cbn in Hw, Hwg; repeat split.
                - destruct (Z.eq_dec a1 a2); [auto | exfalso; apply Hta, (proj1 Hw); auto].
                - destruct (cap_eqb c1p c2p) eqn:Ec;
                    [destruct c1p, c2p; cbn in Ec; try discriminate; try reflexivity; try (apply Z.eqb_eq in Ec; congruence); apply term_eqb_eq in Ec; congruence
                    |exfalso; apply Htc, (proj2 Hw); intros ->; destruct c2p; cbn in Ec; try rewrite Z.eqb_refl in Ec; try rewrite term_eqb_refl in Ec; discriminate].
                - destruct (Z.eq_dec ng1 ng2); [auto | exfalso; pose proof (Hwg n) as ->; discriminate Etbg]. }
              destruct Ep as (-> & -> & ->).
              destruct k; cbn [op_res fmt_of op_res_int] in Hp1; try discriminate Hp1.
              cbn [ptr_addr ptr_cap] in Hp1.
              unfold access_res, renew_res in Hp1; rewrite Hreg in Hp1.
              destruct (cap_access_res c2p (m_regions (c_mem c2)) (raw_address a2 lo) (hi - lo) r al) as [[[]|why|why]|] eqn:Ecap;
                cbn in Hp1; try discriminate Hp1;
                destruct (ng2 =? 0) eqn:Eng; try destruct why; cbn in Hp1; rewrite ?Hd1 in Hp1; try discriminate Hp1.
              all: try solve [repeat match type of Hp1 with context [match ?x with _ => _ end] =>
                lazymatch x with context [match _ with _ => _ end] => fail | _ =>
                destruct x; cbn in Hp1; rewrite ?Hd1 in Hp1; try discriminate Hp1 end end].
              all:
                injection Hp1 as <- <-;
                (split; [unfold leak_of; rewrite Eat1, <- Hat; cbn; reflexivity|]);
                unfold tstep, step; rewrite Hd2, <- Hat; cbn [inst_tstep]; unfold let_tstep; rewrite Ezero; cbn; rewrite Ewt, Ewg, Hcb, Etbg, Echk;
                cbn [or_stuck inst_step op_arg_classes map2_option]; rewrite Ew2, Ewg2; cbn [op_res fmt_of op_res_int];
                cbn [ptr_addr ptr_cap]; unfold access_res, renew_res; rewrite Ecap; cbn; rewrite Eng; cbn;
                eexists; (split; [reflexivity|]);
                unfold ct_rel; cbn; repeat split; auto; try congruence;
                (apply env_rel_put; [exact Henv | exact Hw]).
           ++ (* Limit *)
              destruct args as [|v [|]]; try discriminate Hp1.
              destruct (value_t (ps_tenv ps) P v) as [[|ta tc|]|] eqn:Ewt; try discriminate Hp1.
              rewrite Hcb in Hp1; cbn [andb] in Hp1.
              destruct (t_branch tc) eqn:Etbc; [discriminate Hp1|].
              destruct (t_index tc) eqn:Etic; [discriminate Hp1|].
              cbn [inst_step op_arg_classes map2_option] in Hp1.
              destruct (value_x ge (fr_env (c_frame c1)) P v) as [w1|] eqn:Ew1; [|discriminate Hp1].
              destruct (value_rel ge _ _ _ P v w1 (WTPtr ta tc) Henv Ew1 Ewt) as (w2 & Ew2 & Hw).
              destruct w1 as [|[a1 c1p]|], w2 as [|[a2 c2p]|]; try contradiction Hw.
              destruct k; cbn [op_res fmt_of op_res_int] in Hp1; try discriminate Hp1.
              injection Hp1 as <- <-.
              split; [unfold leak_of; rewrite Eat1, <- Hat; cbn; reflexivity|].
              unfold tstep, step; rewrite Hd2, <- Hat; cbn [inst_tstep]; unfold let_tstep; rewrite Ezero; cbn; rewrite Ewt, Hcb, Etbc, Etic;
                cbn [or_stuck inst_step op_arg_classes map2_option]; rewrite Ew2; cbn.
              eexists; split; [reflexivity|].
              unfold ct_rel; cbn; repeat split; auto; try congruence.
              apply env_rel_put; [exact Henv | cbn; split; [exact (proj2 Hw) | congruence]].
           ++ (* CheckLimit *)
              destruct args as [|v [|uv [|]]]; try discriminate Hp1.
              destruct (value_t (ps_tenv ps) P v) as [[|ta tc|]|] eqn:Ewt; try discriminate Hp1.
              destruct (value_t (ps_tenv ps) L uv) as [[| |uc ul]|] eqn:Ewu; try discriminate Hp1.
              destruct (check_ptr_bounds_taint pol ta _) eqn:Echk; [discriminate Hp1|].
              destruct (check_ptr_bounds_not_all pol _ _ Hcb Echk) as [Hta Htc].
              cbn [inst_step op_arg_classes map2_option] in Hp1.
              destruct (value_x ge (fr_env (c_frame c1)) P v) as [w1|] eqn:Ew1; [|discriminate Hp1].
              destruct (value_x ge (fr_env (c_frame c1)) L uv) as [wu1|] eqn:Ewu1; [|discriminate Hp1].
              destruct (value_rel ge _ _ _ P v w1 (WTPtr ta tc) Henv Ew1 Ewt) as (w2 & Ew2 & Hw).
              destruct (value_rel ge _ _ _ L uv wu1 (WTLimit uc ul) Henv Ewu1 Ewu) as (wu2 & Ewu2 & Hwu).
              destruct w1 as [|[a1 c1p]|], w2 as [|[a2 c2p]|], wu1 as [| |uc1 us1], wu2 as [| |uc2 us2];
                try contradiction Hw; try contradiction Hwu.
              assert (Ep : a1 = a2 /\ c1p = c2p /\ uc1 = uc2 /\ us1 = us2).
              { cbn in Hw, Hwu; repeat split.
                - destruct (Z.eq_dec a1 a2); [auto | exfalso; apply Hta, (proj1 Hw); auto].
                - destruct (cap_eqb c1p c2p) eqn:Ec;
                    [destruct c1p, c2p; cbn in Ec; try discriminate; try reflexivity; try (apply Z.eqb_eq in Ec; congruence); apply term_eqb_eq in Ec; congruence
                    |exfalso; apply Htc; rewrite (proj2 Hw ltac:(intros ->; destruct c2p; cbn in Ec; try rewrite Z.eqb_refl in Ec; try rewrite term_eqb_refl in Ec; discriminate)), taint_join_all_l; reflexivity].
                - destruct (cap_eqb uc1 uc2) eqn:Ec;
                    [destruct uc1, uc2; cbn in Ec; try discriminate; try reflexivity; try (apply Z.eqb_eq in Ec; congruence); apply term_eqb_eq in Ec; congruence
                    |exfalso; apply Htc; rewrite (proj1 Hwu ltac:(intros ->; destruct uc2; cbn in Ec; try rewrite Z.eqb_refl in Ec; try rewrite term_eqb_refl in Ec; discriminate)), taint_join_all_l, taint_join_all_r; reflexivity].
                - destruct (Z.eq_dec us1 us2); [auto | exfalso; apply Htc; rewrite (proj2 Hwu n), !taint_join_all_r; reflexivity]. }
              destruct Ep as (-> & -> & -> & ->).
              destruct k; cbn [op_res fmt_of op_res_int] in Hp1; try discriminate Hp1.
              cbn [ptr_addr ptr_cap] in Hp1.
              destruct (cap_eqb uc2 c2p && (us2 =? hi - lo)) eqn:Ece; [|cbn in Hp1; rewrite Hd1 in Hp1; discriminate Hp1].
              unfold access_res in Hp1; rewrite Hreg in Hp1.
              destruct (cap_access_res c2p (m_regions (c_mem c2)) (raw_address a2 lo) (hi - lo) r al) as [[[]|why|why]|] eqn:Ecap; cbn in Hp1; rewrite ?Hd1 in Hp1; try discriminate Hp1.
              cbn in Hp1; injection Hp1 as <- <-.
              split; [unfold leak_of; rewrite Eat1, <- Hat; cbn; reflexivity|].
              unfold tstep, step; rewrite Hd2, <- Hat; cbn [inst_tstep]; unfold let_tstep; rewrite Ezero; cbn; rewrite Ewt, Ewu, Echk;
                cbn [or_stuck inst_step op_arg_classes map2_option]; rewrite Ew2, Ewu2; cbn [op_res fmt_of op_res_int];
                cbn [ptr_addr ptr_cap]; rewrite Ece; unfold access_res; rewrite Ecap; cbn.
              eexists; split; [reflexivity|].
              unfold ct_rel; cbn; repeat split; auto; try congruence.
              apply env_rel_put; [exact Henv | exact Hw].
           ++ (* CheckLocal *)
              destruct k; try (cbn in Hp1; discriminate Hp1).
              destruct args; [|cbn in Hp1; discriminate Hp1].
              cbn [inst_step] in Hp1.
              destruct (lookup x (fr_locals (c_frame c1))) as [[base|]|] eqn:El1; try discriminate Hp1.
              unfold access_res in Hp1; rewrite Hreg in Hp1.
              destruct (cap_access_res (Obj base) (m_regions (c_mem c2)) (base + off) bytes r al) as [[[]|why|why]|] eqn:Ecap; cbn in Hp1; rewrite ?Hd1 in Hp1; try discriminate Hp1.
              cbn in Hp1; injection Hp1 as <- <-.
              split; [unfold leak_of; rewrite Eat1, <- Hat; cbn; reflexivity|].
              unfold tstep, step; rewrite Hd2, <- Hat; cbn [inst_tstep]; unfold let_tstep; rewrite Ezero; cbn [or_stuck inst_step];
                rewrite <- Hloc, El1; unfold access_res; rewrite Ecap; cbn.
              eexists; split; [reflexivity|].
              unfold ct_rel; cbn; repeat split; auto; try congruence.
              apply env_rel_put; [exact Henv | cbn; split; congruence].
           ++ (* CheckFunction *)
              destruct args as [|v [|]]; try discriminate Hp1.
              destruct (value_t (ps_tenv ps) P v) as [[|ta tc|]|] eqn:Ewt; try discriminate Hp1.
              destruct (t_branch ta || t_branch tc) eqn:Etb; [discriminate Hp1|].
              apply orb_false_iff in Etb as [Etba Etbc].
              destruct k; try (cbn in Hp1; discriminate Hp1).
              cbn [inst_step] in Hp1.
              destruct (value_x ge (fr_env (c_frame c1)) P v) as [w1|] eqn:Ew1; [|discriminate Hp1].
              destruct (value_rel ge _ _ _ P v w1 (WTPtr ta tc) Henv Ew1 Ewt) as (w2 & Ew2 & Hw).
              destruct w1 as [|[a1 c1p]|], w2 as [|[a2 c2p]|]; try contradiction Hw.
              assert (Ha_eq : a1 = a2) by (destruct (Z.eq_dec a1 a2); [auto | exfalso; pose proof (proj1 Hw n) as ->; discriminate Etba]).
              assert (Hc_eq : c1p = c2p) by (apply (cap_eq_of_not_all tc); [exact (proj2 Hw) | intros ->; discriminate Etbc]).
              subst a2 c2p.
              destruct (function_check_res ge (mkPtr a1 c1p)) as [[[]|why|why]|] eqn:Efchk; cbn in Hp1; rewrite ?Hd1 in Hp1; try discriminate Hp1.
              cbn in Hp1; injection Hp1 as <- <-.
              split; [unfold leak_of; rewrite Eat1, <- Hat; cbn; reflexivity|].
              unfold tstep, step; rewrite Hd2, <- Hat; cbn [inst_tstep]; unfold let_tstep; rewrite Ezero; cbn; rewrite Ewt, Etba, Etbc;
                cbn [or_stuck inst_step]; rewrite Ew2, Efchk; cbn.
              eexists; split; [reflexivity|].
              unfold ct_rel; cbn; repeat split; auto; try congruence.
              apply env_rel_put; [exact Henv | exact Hw].
           ++ (* RawLoad *)
              destruct args as [|av [|]]; try discriminate Hp1.
              destruct (value_x ge (fr_env (c_frame c1)) A av) as [[|[a1 c1p]|]|] eqn:Ewa1; try discriminate Hp1.
              destruct (value_t (ps_tenv ps) A av) as [[|ta tc|]|] eqn:Ewta; try discriminate Hp1.
              destruct (t_index ta) eqn:Etia; [discriminate Hp1|].
              rewrite Hcb in Hp1; cbn [andb] in Hp1.
              destruct (t_branch ta || t_branch tc || t_index tc) eqn:Etbc; [discriminate Hp1|].
              apply orb_false_iff in Etbc as [Etbc Etic]; apply orb_false_iff in Etbc as [Etba Etbc].
              cbn [ptr_addr ptr_cap] in Hp1.
              destruct (mem_no_load (ps_mem ps) (raw_address a1 off) (load_type_bytes t)) eqn:Enl; [discriminate Hp1|].
              destruct (value_rel ge _ _ _ A av (WPtr (mkPtr a1 c1p)) (WTPtr ta tc) Henv Ewa1 Ewta) as (wa2 & Ewa2 & Hwa).
              destruct wa2 as [|[a2 c2p]|]; try contradiction Hwa.
              assert (Ha_eq : a1 = a2) by (destruct (Z.eq_dec a1 a2); [auto | exfalso; pose proof (proj1 Hwa n) as ->; discriminate Etba]).
              assert (Hc_eq : c1p = c2p) by (apply (cap_eq_of_not_all tc); [exact (proj2 Hwa) | intros ->; discriminate Etbc]).
              subst a2 c2p.
              destruct (op_arg_classes (RawLoad t off) k) eqn:Eocls; try discriminate Hp1.
              assert (Eclasses : l0 = [A]) by (destruct t, k; cbn in Eocls; congruence).
              subst l0.
              cbn in Hp1; rewrite Ewa1 in Hp1; cbn in Hp1.
              unfold int_load_res, access_res in Hp1; rewrite Hreg in Hp1.
              assert (Esz : match t with LdL | LdD => 8 | LdS => 4 | LdX => 10 | LdNarrow n => fst (narrow_type n) end = load_type_bytes t)
                by (destruct t; reflexivity).
              rewrite Esz in Hp1.
              destruct (cap_access_res c1p (m_regions (c_mem c2)) (raw_address a1 off) (load_type_bytes t) Read 1)
                as [[[]| |]|] eqn:Ecap; cbn in Hp1; rewrite ?Hd1 in Hp1; try discriminate Hp1;
                try solve [destruct k; discriminate Hp1].
              assert (Hld_rel :
                load_bytes (c_mem c1) (raw_address a1 off) (load_type_bytes t) =
                load_bytes (c_mem c2) (raw_address a1 off) (load_type_bytes t) \/
                mem_load_taint (ps_mem ps) (raw_address a1 off) (load_type_bytes t) = taint_all).
              { destruct (range_load_rel_nat (c_mem c1) (c_mem c2) (ps_mem ps) (Z.to_nat (load_type_bytes t)) (raw_address a1 off) Hmem)
                  as [Hall | Htall]; [left; exact (load_bytes_eq_on _ _ _ _ Hall) | right; exact Htall]. }
              destruct t as [| | | | nt], k; cbn in Eocls, Hp1; try discriminate Eocls; try discriminate Hp1;
                injection Hp1 as <- <-;
                (split; [unfold leak_of; rewrite Eat1, <- Hat; cbn; rewrite Ewa1, Ewa2; reflexivity|]);
                unfold tstep, step; rewrite Hd2, <- Hat; cbn [inst_tstep]; unfold let_tstep; rewrite Ezero; cbn [andb orb];
                rewrite Ewa2, Ewta, Etia, Hcb, Etba, Etbc, Etic;
                cbn [ptr_addr]; cbn [load_type_bytes] in Enl |- *; rewrite Enl;
                cbn [or_stuck inst_step op_arg_classes map2_option]; rewrite Ewa2;
                cbn [op_res fmt_of op_res_int int_load_res ptr_addr ptr_cap];
                unfold int_load_res, access_res; cbn [load_type_bytes] in Ecap; rewrite Ecap; cbn;
                eexists; (split; [reflexivity|]);
                unfold ct_rel; cbn; repeat split; auto; try congruence;
                (apply env_rel_put; [exact Henv | cbn; intros Hne; destruct Hld_rel as [E|Hall];
                  [exfalso; apply Hne; repeat first [exact E | reflexivity | progress f_equal] | exact Hall]]).
           ++ (* RawLoadPointer *)
              destruct args as [|av [|]]; try discriminate Hp1.
              destruct (value_x ge (fr_env (c_frame c1)) A av) as [[|[a1 c1p]|]|] eqn:Ewa1; try discriminate Hp1.
              destruct (value_t (ps_tenv ps) A av) as [[|ta tc|]|] eqn:Ewta; try discriminate Hp1.
              destruct (t_index ta || t_index tc) eqn:Etia; [discriminate Hp1|].
              apply orb_false_iff in Etia as [Etia Etic].
              rewrite Hcb in Hp1; cbn [andb] in Hp1.
              destruct (t_branch ta || t_branch tc) eqn:Etbc; [discriminate Hp1|].
              apply orb_false_iff in Etbc as [Etba Etbc].
              cbn [ptr_addr ptr_cap] in Hp1.
              destruct (mem_no_load (ps_mem ps) (raw_address a1 off) 8) eqn:Enl; [discriminate Hp1|].
              destruct (value_rel ge _ _ _ A av (WPtr (mkPtr a1 c1p)) (WTPtr ta tc) Henv Ewa1 Ewta) as (wa2 & Ewa2 & Hwa).
              destruct wa2 as [|[a2 c2p]|]; try contradiction Hwa.
              assert (Ha_eq : a1 = a2) by (destruct (Z.eq_dec a1 a2); [auto | exfalso; pose proof (proj1 Hwa n) as ->; discriminate Etba]).
              assert (Hc_eq : c1p = c2p) by (apply (cap_eq_of_not_all tc); [exact (proj2 Hwa) | intros ->; discriminate Etbc]).
              subst a2 c2p.
              destruct k; cbn [inst_step op_arg_classes map2_option] in Hp1; rewrite ?Ewa1 in Hp1;
                cbn [op_res fmt_of op_res_int] in Hp1; try discriminate Hp1.
              cbn [ptr_addr ptr_cap] in Hp1.
              unfold access_res in Hp1; rewrite Hreg in Hp1.
              destruct (cap_access_res c1p (m_regions (c_mem c2)) (raw_address a1 off) 8 Read 8) as [[[]| |]|] eqn:Ecap;
                cbn in Hp1; rewrite ?Hd1 in Hp1; try discriminate Hp1.
              destruct (pointer_load_effects (c_mem c1) (raw_address a1 off) es) as [lp1|] eqn:Epl1;
                cbn in Hp1; [|discriminate Hp1].
              injection Hp1 as <- <-.
              destruct (pointer_load_effects_rel (c_mem c1) (c_mem c2) (ps_mem ps) (ps_aux ps) (raw_address a1 off) es lp1 Hmem Haux Epl1)
                as (lp2 & Epl2 & Hlp).
              split; [unfold leak_of; rewrite Eat1, <- Hat; cbn; rewrite Ewa1, Ewa2; reflexivity|].
              unfold tstep, step; rewrite Hd2, <- Hat; cbn [inst_tstep]; unfold let_tstep; rewrite Ezero; cbn [andb orb];
                rewrite Ewa2, Ewta, Etia, Etic, Hcb, Etba, Etbc; cbn [ptr_addr]; rewrite Enl;
                cbn [or_stuck inst_step op_arg_classes map2_option]; rewrite Ewa2; cbn [op_res fmt_of op_res_int];
                cbn [ptr_addr ptr_cap]; unfold access_res; rewrite Ecap; cbn; rewrite Epl2; cbn.
              eexists; split; [reflexivity|].
              unfold ct_rel; cbn; repeat split; auto; try congruence.
              apply env_rel_put; [exact Henv | exact Hlp].
    + (* Flight *)
      destruct (map_option (flight_arg_t (ps_tenv ps)) args) as [ts|] eqn:Ets; [|discriminate Hp1].
      destruct (flight_cap_t (ps_tenv ps) lw) as [tc|] eqn:Etc; [|discriminate Hp1].
      destruct (op_checks_vartime pol o L && t_vartime (join_taints ts)) eqn:Evt; [discriminate Hp1|].
      cbn [inst_step] in Hp1.
      destruct (map_option (flight_arg_x ge (fr_env (c_frame c1))) args) as [xs1|] eqn:Exs1; [|discriminate Hp1].
      cbn in Hp1.
      destruct (alu o L xs1) as [[n1| |]|] eqn:Ealu1; try discriminate Hp1;
        try solve [destruct (flight_cap ge (fr_env (c_frame c1)) lw); discriminate Hp1].
      cbn in Hp1.
      destruct (flight_cap ge (fr_env (c_frame c1)) lw) as [cp1|] eqn:Ecp1; [|discriminate Hp1].
      cbn in Hp1; injection Hp1 as <- <-.
      destruct (map_flight_arg_rel ge _ _ _ args xs1 ts Henv Exs1 Ets) as (xs2 & Exs2 & Hw1 & Hw2 & Hxs).
      destruct (flight_cap_rel ge _ _ _ lw cp1 tc Henv Ecp1 Etc) as (cp2 & Ecp2 & Hcp).
      assert (Hlen : length xs1 = length xs2) by
        (rewrite (map_option_len _ _ _ _ _ Exs1), (map_option_len _ _ _ _ _ Exs2); reflexivity).
      destruct (flight_alu_rel pol o xs1 xs2 ts n1 Hw1 Hw2 Hlen Hxs Evt Ealu1) as (n2 & Ealu2 & Hndiff).
      split; [unfold leak_of; rewrite Eat1, <- Hat; reflexivity|].
      unfold tstep, step; rewrite Hd2, <- Hat; cbn [inst_tstep]; rewrite Ets, Etc, Evt;
        cbn [or_stuck inst_step]; rewrite Exs2; cbn; rewrite Ealu2; cbn; rewrite Ecp2; cbn.
      eexists; split; [reflexivity|].
      unfold ct_rel; cbn; repeat split; auto; try congruence.
      apply env_rel_put; [exact Henv | cbn; split; [exact Hndiff | exact Hcp]].
    + (* RawStore *)
      destruct (width_value_class w) as [vk|] eqn:Evk; [|discriminate Hp1].
      destruct (value_x ge (fr_env (c_frame c1)) A av) as [[|[a1 c1p]|]|] eqn:Ewa1; try discriminate Hp1.
      destruct (value_t (ps_tenv ps) A av) as [[|ta tc|]|] eqn:Ewta; try discriminate Hp1.
      destruct (t_index ta) eqn:Etia; [discriminate Hp1|].
      rewrite Hcb in Hp1; cbn [andb] in Hp1.
      destruct (t_branch ta || t_branch tc || t_index tc) eqn:Etbc; [discriminate Hp1|].
      apply orb_false_iff in Etbc as [Etbc Etic]; apply orb_false_iff in Etbc as [Etba Etbc].
      cbn [ptr_addr ptr_cap] in Hp1.
      destruct (mem_no_store (ps_mem ps) (raw_address a1 off) (width_bytes w)) eqn:Ens; [discriminate Hp1|].
      destruct (value_rel ge _ _ _ A av (WPtr (mkPtr a1 c1p)) (WTPtr ta tc) Henv Ewa1 Ewta) as (wa2 & Ewa2 & Hwa).
      destruct wa2 as [|[a2 c2p]|]; try contradiction Hwa.
      assert (Ha_eq : a1 = a2) by (destruct (Z.eq_dec a1 a2); [auto | exfalso; pose proof (proj1 Hwa n) as ->; discriminate Etba]).
      assert (Hc_eq : c1p = c2p) by (apply (cap_eq_of_not_all tc); [exact (proj2 Hwa) | intros ->; discriminate Etbc]).
      subst a2 c2p.
      destruct w; cbn [width_value_class] in Evk; injection Evk as <-.
      all: try (
        match type of Hp1 with context [value_t ?te ?vk ?vv] =>
          destruct (value_t te vk vv) as [[tv| |]|] eqn:Ewtv end; try discriminate Hp1;
        cbn [inst_step width_value_class] in Hp1;
        match type of Ewtv with value_t _ ?vk ?vv = _ =>
          destruct (value_x ge (fr_env (c_frame c1)) vk vv) as [wv1|] eqn:Ewv1 end; [|discriminate Hp1];
        cbn in Hp1; rewrite Ewa1 in Hp1; cbn in Hp1;
        destruct (value_rel ge _ _ _ _ v wv1 (WTInt tv) Henv Ewv1 Ewtv) as (wv2 & Ewv2 & Hwv);
        destruct wv1 as [nv1| |], wv2 as [nv2| |]; try contradiction Hwv;
        unfold store_res, access_res in Hp1; rewrite Hreg in Hp1;
        match type of Hp1 with context [cap_access_res ?cp ?regs ?a ?sz Write ?al] =>
          destruct (cap_access_res cp regs a sz Write al) as [[[]| |]|] eqn:Ecap end;
        cbn in Hp1; rewrite ?Hd1 in Hp1; try discriminate Hp1;
        injection Hp1 as <- <-;
        (split; [unfold leak_of; rewrite Eat1, <- Hat; cbn; rewrite Ewa1, Ewa2; reflexivity|]);
        unfold tstep, step; rewrite Hd2, <- Hat; cbn [inst_tstep width_value_class];
        rewrite Ewa2, Ewta, Etia, Hcb, Etba, Etbc, Etic; cbn [ptr_addr width_bytes] in Ens |- *; rewrite Ens, Ewtv;
        cbn [or_stuck inst_step width_value_class]; rewrite Ewv2, Ewa2; cbn;
        unfold store_res, access_res; cbn [width_bytes] in Ecap; rewrite Ecap; cbn;
        eexists; (split; [reflexivity|]);
        unfold ct_rel; cbn; repeat split; auto; try congruence;
        exact (store_bytes_rel _ _ _ _ _ _ _ _ Hmem Hwv)).
      (* Wp *)
      destruct (value_t (ps_tenv ps) P v) as [[|tva tvc|]|] eqn:Ewtv; try discriminate Hp1.
      cbn [inst_step width_value_class] in Hp1.
      destruct (value_x ge (fr_env (c_frame c1)) P v) as [wv1|] eqn:Ewv1; [|discriminate Hp1].
      cbn in Hp1; rewrite Ewa1 in Hp1; cbn in Hp1.
      destruct (value_rel ge _ _ _ P v wv1 (WTPtr tva tvc) Henv Ewv1 Ewtv) as (wv2 & Ewv2 & Hwv).
      destruct wv1 as [|[pva1 pvc1]|], wv2 as [|[pva2 pvc2]|]; try contradiction Hwv.
      unfold store_res, access_res in Hp1; rewrite Hreg in Hp1.
      destruct (cap_access_res c1p (m_regions (c_mem c2)) (raw_address a1 off) 8 Write 8) as [[[]| |]|] eqn:Ecap;
        cbn in Hp1; rewrite ?Hd1 in Hp1; try discriminate Hp1.
      injection Hp1 as <- <-.
      split; [unfold leak_of; rewrite Eat1, <- Hat; cbn; rewrite Ewa1, Ewa2; reflexivity|].
      unfold tstep, step; rewrite Hd2, <- Hat; cbn [inst_tstep width_value_class];
        rewrite Ewa2, Ewta, Etia, Hcb, Etba, Etbc, Etic; cbn [ptr_addr width_bytes] in Ens |- *; rewrite Ens, Ewtv;
        cbn [or_stuck inst_step width_value_class]; rewrite Ewv2, Ewa2; cbn;
        unfold store_res, access_res; cbn [width_bytes] in Ecap; rewrite Ecap; cbn.
      eexists; split; [reflexivity|].
      unfold ct_rel; cbn; repeat split; auto; try congruence.
      * exact (store_bytes_rel _ _ _ _ _ _ _ _ Hmem (proj1 Hwv)).
      * intros b Hne; unfold store_aux in Hne; cbn in Hne.
        destruct (b =? raw_address a1 off) eqn:Eb; [exact (proj2 Hwv Hne) | exact (Haux b Hne)].
    + (* RawStorePointer *)
      destruct (effects_eqb es [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]
                || effects_eqb es [LowerWrite; AddressWrite]
                || effects_eqb es [AtomicWrite]) eqn:Eeff; [|discriminate Hp1].
      destruct (value_x ge (fr_env (c_frame c1)) A av) as [[|[a1 c1p]|]|] eqn:Ewa1; try discriminate Hp1.
      destruct (value_t (ps_tenv ps) A av) as [[|ta tca|]|] eqn:Ewta; try discriminate Hp1.
      destruct (value_t (ps_tenv ps) P v) as [[|tva tvc|]|] eqn:Ewtv; try discriminate Hp1.
      destruct (t_index ta || t_index tca) eqn:Etia; [discriminate Hp1|].
      apply orb_false_iff in Etia as [Etia Etica].
      rewrite Hcb in Hp1; cbn [andb] in Hp1.
      destruct (t_branch ta || t_branch tca) eqn:Etba; [discriminate Hp1|].
      apply orb_false_iff in Etba as [Etba Etbca].
      cbn [ptr_addr ptr_cap] in Hp1.
      destruct (mem_no_store (ps_mem ps) (raw_address a1 off) 8) eqn:Ens; [discriminate Hp1|].
      destruct (value_rel ge _ _ _ A av (WPtr (mkPtr a1 c1p)) (WTPtr ta tca) Henv Ewa1 Ewta) as (wa2 & Ewa2 & Hwa).
      destruct wa2 as [|[a2 c2p]|]; try contradiction Hwa.
      assert (Ha_eq : a1 = a2) by (destruct (Z.eq_dec a1 a2); [auto | exfalso; pose proof (proj1 Hwa n) as ->; discriminate Etba]).
      assert (Hc_eq : c1p = c2p) by (apply (cap_eq_of_not_all tca); [exact (proj2 Hwa) | intros ->; discriminate Etbca]).
      subst a2 c2p.
      cbn [inst_step] in Hp1.
      destruct (value_x ge (fr_env (c_frame c1)) P v) as [wv1|] eqn:Ewv1; [|discriminate Hp1].
      cbn in Hp1; rewrite Ewa1 in Hp1; cbn in Hp1.
      destruct (value_rel ge _ _ _ P v wv1 (WTPtr tva tvc) Henv Ewv1 Ewtv) as (wv2 & Ewv2 & Hwv).
      destruct wv1 as [|[pva1 pvc1]|], wv2 as [|[pva2 pvc2]|]; try contradiction Hwv.
      unfold access_res in Hp1; rewrite Hreg in Hp1.
      destruct (cap_access_res c1p (m_regions (c_mem c2)) (raw_address a1 off) 8 Write 8) as [[[]| |]|] eqn:Ecap;
        cbn in Hp1; rewrite ?Hd1 in Hp1; try discriminate Hp1.
      assert (Heff_cases : es = [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite] \/
                           es = [LowerWrite; AddressWrite] \/ es = [AtomicWrite]).
      { apply orb_true_iff in Eeff as [Eeff|Eeff];
          [apply orb_true_iff in Eeff as [Eeff|Eeff]|];
          apply effects_eqb_eq in Eeff; auto. }
      destruct Heff_cases as [-> | [-> | ->]];
        cbn [pointer_store_effects fold_left pointer_store_effect] in Hp1;
        injection Hp1 as <- <-;
        (split; [unfold leak_of; rewrite Eat1, <- Hat; cbn; rewrite Ewa1, Ewa2; reflexivity|]);
        unfold tstep, step; rewrite Hd2, <- Hat; cbn [inst_tstep];
        rewrite Ewa2, Ewta, Ewtv, Etia, Etica, Hcb, Etba, Etbca; cbn [ptr_addr]; rewrite Ens;
        cbn [or_stuck inst_step]; rewrite Ewv2, Ewa2; cbn; unfold access_res; rewrite Ecap; cbn;
        eexists; (split; [reflexivity|]);
        unfold ct_rel; cbn; repeat split; auto; try congruence;
        first [exact (store_bytes_rel _ _ _ _ _ _ _ _ Hmem (proj1 Hwv))
        |intros b Hne; destruct (b =? raw_address a1 off) eqn:Eb; [exact (proj2 Hwv Hne) | exact (Haux b Hne)]].
    + (* Call *)
      destruct cl as [| |fn]; try discriminate Hp1.
      destruct (map_option (arg_t (ps_tenv ps)) args) as [wts|] eqn:Ewts; [|discriminate Hp1].
      cbn [inst_step] in Hp1.
      unfold step in Hstep; rewrite Eat1, Hd1 in Hstep; cbn [inst_step] in Hstep.
      destruct (map_option (arg_x ge (fr_env (c_frame c1))) args) as [xs1|] eqn:Exs1; [|discriminate Hstep].
      destruct (call_args_rel ge _ _ _ args xs1 wts Henv Exs1 Ewts) as (xs2 & Exs2 & Hxlen & Hxfor).
      cbn in Hp1.
      destruct (find_fn ge fn) as [[g | outfn]|] eqn:Efn; try discriminate Hp1.
      * (* Defined g *)
        destruct (variadic_func g) eqn:Evar; [discriminate Hp1|].
        destruct (call_tenv g wts) as [cte|] eqn:Ecte; [|discriminate Hp1].
        cbn in Hp1.
        destruct (call_frame g xs1) as [callee1|] eqn:Ecf1; [|discriminate Hp1].
        injection Hp1 as <- <-.
        destruct (call_frame_rel g xs1 xs2 wts callee1 cte Evar Hxlen Hxfor Ecf1 Ecte)
          as (callee2 & Ecf2 & Hgfn & Hgloc & Hgd1 & Hgd2 & Hgat & Hgenv).
        split; [unfold leak_of; rewrite Eat1, <- Hat; cbn; rewrite Efn; reflexivity|].
        unfold tstep, step; rewrite Hd2, <- Hat; cbn [inst_tstep]; rewrite Ewts, Efn, Evar, Ecte;
          cbn [or_stuck inst_step]; rewrite Exs2; cbn; rewrite Efn; cbn; rewrite Ecf2.
        eexists; split; [reflexivity|].
        unfold ct_rel; cbn; repeat split; auto; congruence.
      * (* External / free *)
        destruct (lookup fn (ge_globals ge)) eqn:Eglob;
          [unfold external_call in Hp1; rewrite Eglob in Hp1; discriminate Hp1|].
        destruct (is_free_name fn) eqn:Eisf; [|discriminate Hp1].
        unfold external_call in Hp1; rewrite Eglob, Eisf in Hp1; cbn [negb] in Hp1.
        destruct r; try discriminate Hp1.
        destruct args as [|[ak av] [|]]; try discriminate Hp1;
          try solve [destruct ak; discriminate Hp1].
        destruct ak; try discriminate Hp1.
        pose proof (map_option_len _ _ _ _ _ Ewts) as Hlent.
        destruct wts as [|wt0 [|]]; try discriminate Hp1; try discriminate Hlent.
        pose proof (map_option_len _ _ _ _ _ Exs1) as Hlen1.
        pose proof (map_option_len _ _ _ _ _ Exs2) as Hlen2.
        destruct xs1 as [|x1 [|]], xs2 as [|x2 [|]];
          try discriminate Hlen1; try discriminate Hlen2;
          inversion Hxfor as [|? ? ? ? Hwx _]; subst.
        assert (Ex_eq : x1 = x2 /\ match wt0 with
          | WTPtr ta tc => t_branch ta || t_branch tc = false /\ t_index tc = false
          | WTInt ta => t_branch ta = false
          | _ => False end).
        { destruct wt0 as [ta | ta tc | ]; try discriminate Hp1.
          - destruct (t_branch ta) eqn:Etb; [discriminate Hp1|].
            destruct x1 as [n1| |], x2 as [n2| |]; try contradiction Hwx.
            split; [destruct (Z.eq_dec n1 n2); [congruence | exfalso; pose proof (Hwx n) as ->; discriminate Etb] | reflexivity].
          - destruct (t_branch ta || t_branch tc) eqn:Etb; [discriminate Hp1|].
            destruct (t_index tc) eqn:Etic; [discriminate Hp1|].
            apply orb_false_iff in Etb as [Etba Etbc].
            destruct x1 as [|[a1 c1p]|], x2 as [|[a2 c2p]|]; try contradiction Hwx.
            assert (a1 = a2) by (destruct (Z.eq_dec a1 a2); [auto | exfalso; pose proof (proj1 Hwx n) as ->; discriminate Etba]).
            assert (c1p = c2p) by (apply (cap_eq_of_not_all tc); [exact (proj2 Hwx) | intros ->; discriminate Etbc]).
            subst; split; [reflexivity | auto]. }
        destruct Ex_eq as [<- Hwt0].
        assert (Efree_t : (match wt0 with
          | WTInt ta => if t_branch ta then TFault CannotBranch else TNext ps
          | WTPtr ta tc => if t_branch ta || t_branch tc then TFault CannotBranch
                          else if t_index tc then TFault CannotIndex else TNext ps
          | WTLimit _ _ => TStuck "free" end) = TNext ps).
        { destruct wt0; cbn in Hwt0; try contradiction;
            [rewrite Hwt0 | destruct Hwt0 as [-> ->]]; reflexivity. }
        rewrite Efree_t in Hp1.
        destruct (ge_free ge x1 (c_mem c1)) as [[r_fr m1']|] eqn:Ef1; [|discriminate Hp1].
        destruct r_fr as [[]| |]; cbn in Hp1; rewrite ?Hd1 in Hp1; try discriminate Hp1.
        injection Hp1 as <- <-.
        destruct (free_rel _ x1 (c_mem c1) (c_mem c2) (ps_mem ps) (ps_aux ps) ok m1' Hfree Hreg Hmem Haux Ef1)
          as (m2' & Ef2 & Hreg' & Hmem' & Haux').
        split.
        { unfold leak_of; rewrite Eat1, <- Hat; cbn; rewrite Efn, Eisf.
          cbn in Exs1, Exs2.
          rewrite Exs1, Exs2; reflexivity. }
        unfold tstep, step; rewrite Hd2, <- Hat; cbn [inst_tstep]; rewrite Ewts, Efn, Eglob, Eisf.
        rewrite Efree_t;
          cbn [or_stuck inst_step]; rewrite Exs2; cbn; rewrite Efn; unfold external_call;
          rewrite Eglob, Eisf; cbn [negb]; rewrite Ef2; cbn;
          eexists; (split; [reflexivity|]);
          unfold ct_rel; cbn; repeat split; auto; congruence.
    + (* LocalAlloc: returns TFresh, never PNext *)
      match type of Hp1 with (match ?out with _ => _ end) = _ =>
        destruct out; discriminate Hp1 end.
    + (* Loc *)
      cbn in Hp1.
      injection Hp1 as <- <-.
      split; [unfold leak_of; rewrite Eat1, <- Hat; reflexivity|].
      unfold tstep, step; rewrite Hd2, <- Hat; cbn; eexists; split; [reflexivity|].
      unfold ct_rel; cbn; repeat split; auto; congruence.
    + (* Touch *)
      cbn in Hp1.
      injection Hp1 as <- <-.
      split; [unfold leak_of; rewrite Eat1, <- Hat; reflexivity|].
      unfold tstep, step; rewrite Hd2, <- Hat; cbn; eexists; split; [reflexivity|].
      unfold ct_rel; cbn; repeat split; auto; congruence.
Qed.

Lemma inst_step_no_clean_stop : forall ge fr m i o,
  inst_step ge fr m i = Some (IStop o) ->
  ~(o = RetVoid \/ o = OutOfFuel \/ exists w, o = Ret w).
Proof.
  intros ge fr m i o H. destruct i.
  1: destruct (special_let o0) eqn:Es;
       [destruct o0; try discriminate Es | rewrite (inst_step_let _ _ _ _ _ _ _ Es) in H].
  all: unfold inst_step, external_call, bind_res, store_out in H;
    cases H; inversion H; subst;
    intros [Hbad|[Hbad|[retword Hbad]]]; discriminate Hbad.
Qed.

Lemma doomed_result_clean_stop : forall ge fr m i out od o,
  doomed_result ge fr m i out = Some od -> fst od = IStop o ->
  (o = RetVoid \/ o = OutOfFuel \/ exists w, o = Ret w) -> out = IStop o.
Proof.
  intros ge fr m i out od o H Hstop Hclean.
  destruct (ahead_inst i) eqn:Ea.
  - destruct i; try discriminate Ea. destruct k; try discriminate Ea.
    destruct o0; try discriminate Ea. destruct args as [|v [|v' args]]; try discriminate Ea.
    unfold doomed_result in H; cases H; inversion H; subst; cbn in Hstop;
      try discriminate Hstop; try congruence;
      injection Hstop as <-; destruct Hclean as [Hbad|[Hbad|[retword Hbad]]]; discriminate Hbad.
  - rewrite (doomed_result_other _ _ _ _ _ Ea) in H.
    cases H; inversion H; subst; cbn in Hstop; try discriminate Hstop; try congruence;
      injection Hstop as <-; destruct Hclean as [Hbad|[Hbad|[retword Hbad]]]; discriminate Hbad.
Qed.

(** Terminal-step constant-time soundness (`pstep_ct_done`): when `c1`
    terminates cleanly (`PDone (Ret _) _` or `PDone RetVoid _` or
    `PDone OutOfFuel _`), `c2` also terminates with `PDone` and the same
    final [leak_event]. *)
Lemma pstep_ct_done : forall pol ge c1 c2 ps o1 ots,
  pol_check_branches pol = true ->
  ct_rel c1 c2 ps ->
  (o1 = RetVoid \/ o1 = OutOfFuel \/ exists w, o1 = Ret w) ->
  pstep pol ge c1 ps = PDone o1 ots ->
  leak_of pol ge c1 = leak_of pol ge c2 /\
  exists o2, pstep pol ge c2 ps = PDone o2 ots.
Proof.
  intros pol ge c1 c2 ps o1 ots Hcb Hrel Ho1 Hp1.
  pose proof (pstep_erases pol ge c1 ps) as Edone.
  rewrite Hp1 in Edone.
  destruct Hrel as (Hfn & Hloc & Hd1 & Hd2 & Hat & Hfuel & Hreg & Hcallers & Henv & Hmem & Haux).
  unfold pstep in *. unfold tstep in Hp1; rewrite Hd1 in Hp1.
  destruct (fr_at (c_frame c1)) as [xs l | l from | l [|i rest] j] eqn:Eat1.
  - discriminate Hp1.
  - destruct (c_fuel c1 =? 0) eqn:Ef0.
    + unfold step in Hp1; rewrite Eat1, Ef0 in Hp1; injection Hp1 as <- <-.
      split; [unfold leak_of; rewrite Eat1, <- Hat, Ef0, <- Hfuel, Ef0; reflexivity|].
      unfold tstep, step; rewrite Hd2, <- Hat, <- Hfuel, Ef0; exists OutOfFuel; reflexivity.
    + destruct (find_block _ _); [|discriminate Hp1].
      destruct (phis_tenv _ _ _); [|discriminate Hp1].
      unfold step in Hp1; rewrite Eat1, Ef0 in Hp1; unfold or_stuck in Hp1.
      destruct (find_block _ _); [|discriminate Hp1].
      destruct (phis_env _ _ _ _); discriminate Hp1.
  - unfold step in Hp1; rewrite Eat1 in Hp1; unfold jump_step in Hp1; rewrite Hd1 in Hp1.
    destruct j as [t | v t1 t2 | v | vs | | ]; cbn [jump_tstep] in Hp1; try discriminate Hp1.
    + unfold edge_step in Hp1; rewrite Hd1 in Hp1; destruct t; discriminate Hp1.
    + destruct (value_t _ W v) as [[tv| |]|]; try discriminate Hp1.
      destruct (t_branch tv); [discriminate Hp1|].
      unfold or_stuck, edge_step in Hp1; rewrite Hd1 in Hp1.
      destruct (value_x ge (fr_env (c_frame c1)) W v) as [[n| |]|]; try discriminate Hp1.
      destruct (if n =? 0 then t2 else t1); discriminate Hp1.
    + destruct (fn_ret (fr_fn (c_frame c1))) as [rk| |] eqn:Eret; try discriminate Hp1.
      destruct (value_t (ps_tenv ps) rk v) as [wt|] eqn:Evt; [|discriminate Hp1].
      unfold return_tstep in Hp1.
      destruct (ps_callers ps) as [|[cte r] tcs] eqn:Etcs.
      * unfold or_stuck in Hp1.
        destruct (value_x ge (fr_env (c_frame c1)) rk v) as [w1|] eqn:Ev1; [|discriminate Hp1].
        destruct (value_rel ge _ _ _ rk v w1 wt Henv Ev1 Evt) as (w2 & Ev2 & _).
        unfold return_step, or_stuck in Hp1.
        destruct (c_callers c1), (c_callers c2) eqn:Ecs2; try contradiction Hcallers.
        destruct (invalidate_locals (fr_locals (c_frame c1)) (c_mem c1)) as [m1'|] eqn:Einv1; [|discriminate Hp1].
        destruct (invalidate_locals_rel _ _ _ _ _ _ Hreg Hmem Haux Einv1) as (m2' & Einv2 & _).
        injection Hp1 as <- <-.
        split; [unfold leak_of; rewrite Eat1, <- Hat; reflexivity|].
        unfold tstep, step; unfold jump_step, return_step, or_stuck; cbv zeta.
        rewrite Hd2, <- Hat; cbn [jump_tstep]; unfold return_tstep;
        rewrite <- Hfn, Eret, Evt, Etcs, ?Hd2, Ev2, <- Hloc, Einv2, Ecs2; cbn.
        exists (Ret w2); reflexivity.
      * destruct (returned_tenv r [wt] cte); [|discriminate Hp1].
        unfold or_stuck, return_step in Hp1.
        destruct (value_x ge (fr_env (c_frame c1)) rk v) as [w1|]; [|discriminate Hp1].
        destruct (c_callers c1) as [|[caller1 pd1] cs1]; [contradiction Hcallers|].
        destruct (invalidate_locals _ _); [|discriminate Hp1].
        destruct (pd_conv pd1) as [[cw kw]|];
          [destruct (converted_outcome _ _ _); [|discriminate Hp1]; destruct (returned_env _ _ _); discriminate Hp1
          |destruct (returned_env _ _ _); discriminate Hp1].
    + destruct (fn_ret (fr_fn (c_frame c1))) eqn:Eret; try discriminate Hp1.
      unfold return_tstep, return_step, or_stuck in Hp1.
      destruct (ps_callers ps) as [|[cte r] tcs] eqn:Etcs.
      * destruct (c_callers c1), (c_callers c2) eqn:Ecs2; try contradiction Hcallers.
        destruct (invalidate_locals (fr_locals (c_frame c1)) (c_mem c1)) as [m1'|] eqn:Einv1; [|discriminate Hp1].
        destruct (invalidate_locals_rel _ _ _ _ _ _ Hreg Hmem Haux Einv1) as (m2' & Einv2 & _).
        injection Hp1 as <- <-.
        split; [unfold leak_of; rewrite Eat1, <- Hat; reflexivity|].
        unfold tstep, step; unfold jump_step, return_step, or_stuck; cbv zeta.
        rewrite Hd2, <- Hat; cbn [jump_tstep]; unfold return_tstep;
        rewrite <- Hfn, Eret, Etcs, ?Hd2, <- Hloc, Einv2, Ecs2; cbn.
        exists RetVoid; reflexivity.
      * destruct (returned_tenv r [] cte); [|discriminate Hp1].
        destruct (c_callers c1) as [|[caller1 pd1] cs1]; [contradiction Hcallers|].
        destruct (invalidate_locals _ _); [|discriminate Hp1].
        destruct (pd_conv pd1) as [[cw kw]|];
          [destruct (converted_outcome _ _ _); [|discriminate Hp1]; destruct (returned_env _ _ _); discriminate Hp1
          |destruct (returned_env _ _ _); discriminate Hp1].
    + (* JUnreachable contradicts Ho1 *)
      injection Hp1 as <- <-.
      destruct Ho1 as [| [| [? ?]]]; discriminate.
  - (* An instruction never stops with Ret, RetVoid, or OutOfFuel! *)
    exfalso.
    unfold step in Edone; rewrite Eat1, Hd1 in Edone; cbn [or_stuck] in Edone.
    destruct (inst_step ge (c_frame c1) (c_mem c1) i) as [out0|] eqn:Eis; [|discriminate Edone].
    cbn in Edone.
    destruct (doomed_result ge (c_frame c1) (c_mem c1) i out0) as [[out d']|] eqn:Edr;
      [|discriminate Edone].
    destruct out as [|o_stop|g xs pd| |]; cbn in Edone;
      try (destruct (call_frame g xs); discriminate Edone); try discriminate Edone.
    injection Edone as <-.
    pose proof (doomed_result_clean_stop _ _ _ _ _ _ _ Edr eq_refl Ho1) as ->.
    exact (inst_step_no_clean_stop _ _ _ _ _ Eis Ho1).
Qed.

(** Multi-step 2-run constant-time noninterference (`prun_ct_sound`):
    if the first run returns or exhausts the configuration's block fuel
    within [steps] transitions, a related run has the same [leak_of]
    trace. This statement excludes poison faults, stuck runs, runtime
    traps and fresh-allocation requests; [prun] does not choose allocation
    bases. Exhausting [steps] alone yields [PNext], not [OutOfFuel], and
    is not covered here. Returned secret values need not agree. *)
Theorem prun_ct_sound : forall pol ge steps c1 c2 ps o1 ots tr,
  pol_check_branches pol = true ->
  ge_free ge = free_res ->
  ct_rel c1 c2 ps ->
  (o1 = RetVoid \/ o1 = OutOfFuel \/ exists w, o1 = Ret w) ->
  prun pol ge steps c1 ps = PDone o1 ots ->
  prun_trace pol ge steps c1 ps = Some tr ->
  prun_trace pol ge steps c2 ps = Some tr.
Proof.
  intros pol ge steps. induction steps as [|n IH]; intros c1 c2 ps o1 ots tr Hcb Hfree Hrel Ho1 Hrun Htr; cbn in *.
  - discriminate Hrun.
  - destruct (pstep pol ge c1 ps) as [c1' ps' | o1' ots' | | | ] eqn:Ep1; try discriminate Hrun.
    + destruct (prun_trace pol ge n c1' ps') as [rest|] eqn:Etr1; [|discriminate Htr].
      injection Htr as <-.
      destruct (pstep_ct_sound pol ge c1 c2 ps c1' ps' Hcb Hfree Hrel Ep1) as (Eleak & c2' & Ep2 & Hrel').
      rewrite <- Eleak, Ep2, (IH c1' c2' ps' o1 ots rest Hcb Hfree Hrel' Ho1 Hrun Etr1).
      reflexivity.
    + injection Hrun as <- <-; injection Htr as <-.
      destruct (pstep_ct_done pol ge c1 c2 ps o1' ots' Hcb Hrel Ho1 Ep1) as (Eleak & o2 & Ep2).
      rewrite <- Eleak, Ep2. reflexivity.
Qed.

(** ## Heap-allocation step soundness and runtime-driven constant time

    Allocation adds fresh memory and clears both kinds of poison state.
    The two-run argument uses the same deterministic [[runtime]] driver
    so matching allocation requests receive matching addresses. *)

(** [free_res] keeps memory in the sense of Machine.v's [free_keeps]. *)
Lemma cap_free_res_keeps : forall c a m r m',
  cap_free_res c a m = Some (r, m') -> kept m m'.
Proof.
  intros c a m r m' H.
  destruct c as [| base | base | fn | ext];
    [cbn [cap_free_res] in H; injection H as <- <-; apply kept_refl | |
    |cbn [cap_free_res] in H; injection H as <- <-; apply kept_refl
    |cbn [cap_free_res] in H; discriminate H].
  all: cbn [cap_free_res] in H; unfold object_free_res in H;
  destruct (a =? 0); [injection H as <- <-; apply kept_refl|];
  destruct (object_region base (m_regions m)) as [reg|] eqn:Ereg; [|discriminate H];
  destruct (negb (kind_eqb (r_kind reg) Heap)) eqn:Ek; [injection H as <- <-; apply kept_refl|];
  destruct (negb (a =? base)); [injection H as <- <-; apply kept_refl|];
  destruct (r_life reg) eqn:El; [|injection H as <- <-; apply kept_refl];
  destruct (replace_region base (mkRegion base base Heap Freed) (m_regions m)) as [rs|] eqn:Erep;
    [|discriminate H];
  injection H as <- <-;
  apply negb_false_iff in Ek; destruct (r_kind reg) eqn:Erk; try discriminate Ek;
  (split; [|intros b _; split; reflexivity]);
  intros b reg' Eb; cbn [m_regions] in Eb;
  rewrite (object_region_replace _ _ _ _ b Erep eq_refl) in Eb;
  destruct (Z.eqb_spec b base) as [-> | Hne];
  [injection Eb as <-; exists reg; split; [exact Ereg | right; split; [exact El | rewrite Erk; reflexivity]]
  |exists reg'; split; [exact Eb | left; reflexivity]].
Qed.

Lemma free_res_keeps : free_keeps free_res.
Proof.
  intros [a | [a c] | ? ?] m r m' H; cbn [free_res] in H; try discriminate H;
    eapply cap_free_res_keeps; exact H.
Qed.

(** Two memories with identical regions that agree outside [in_object]
    satisfy [kept], so [R.ready_kept] transfers [R.ready] from `m1` to
    `m2` automatically. *)
Lemma ct_kept_ready : forall m1 m2,
  m_regions m1 = m_regions m2 ->
  (forall a, ~ in_object m1 a -> m_bytes m2 a = m_bytes m1 a /\ m_aux m2 a = m_aux m1 a) ->
  kept m1 m2.
Proof.
  intros m1 m2 Hreg Hout. split.
  - intros b reg E2. rewrite <- Hreg in E2. exists reg. split; [exact E2 | left; reflexivity].
  - exact Hout.
Qed.

(** [access_res] never traps with [OutOfMemory] or [TooBig]. *)
Lemma access_res_not_refusal : forall m a c sz r al why,
  access_res m a c sz r al = Some (RTrap why) -> ~ refusal why.
Proof.
  intros m a c sz r al why H [-> | ->];
    unfold access_res, cap_access_res, readonly_access_res, aligned_res in H;
    destruct c as [|b|b|?|?]; try discriminate H;
    try (injection H as H; discriminate H);
    destruct (object_region b (m_regions m)); try discriminate H;
    destruct ((b <=? a) && _); try destruct r; try destruct (a mod al =? 0);
    injection H as H; discriminate H.
Qed.

(** A [pure_scalar_op] never returns `OpRes (RTrap _) _`. *)
Lemma pure_scalar_op_no_trap : forall o k xs m why m',
  pure_scalar_op o = true ->
  op_res o k xs m = Some (OpRes (RTrap why) m') -> False.
Proof.
  intros o k xs m why m' Hp Hop.
  destruct o; try discriminate Hp;
    unfold op_res, op_res_int, additive_res, float_arithmetic, float_convert, float_integer in Hop;
    destruct k;
    repeat match type of Hop with
    | context [match ?x with _ => _ end] =>
        lazymatch x with context [match _ with _ => _ end] => fail | _ => destruct x; try discriminate Hop end
    end.
Qed.

Lemma renew_res_not_refusal : forall chk p m rt,
  renew_res chk p m = Some (RTrap rt) ->
  ~ refusal rt.
Proof.
  intros chk p m rt Er Href. unfold renew_res in Er.
  destruct chk as [|[]|]; try discriminate Er;
    repeat match type of Er with context [match ?x with _ => _ end] =>
      lazymatch x with
      | context [match _ with _ => _ end] => fail
      | _ => destruct x; cbn in Er; try discriminate Er
      end
    end;
    injection Er as <-; destruct Href; discriminate.
Qed.

(** An instruction step that passes [inst_tstep] (not `TFault` or `TStuck`)
    can stop with a [refusal] trap (`OutOfMemory` or `TooBig`) only when
    it is `Let d k (Alloc al) [v]` with `why = TooBig` and `ots = []`. *)
Lemma inst_pstep_refusal_only_alloc : forall pol ge c ps l i rest j why ots,
  ge_free ge = free_res ->
  fr_doomed (c_frame c) = None ->
  fr_at (c_frame c) = Exec l (i :: rest) j ->
  refusal why ->
  pstep pol ge c ps = PDone (Trap why) ots ->
  why = TooBig /\ ots = [] /\
  exists d k al v sz,
    i = Let d k (Alloc al) [v] /\
    value_x ge (fr_env (c_frame c)) L v = Some (WInt sz) /\
    max_allocation_size <? sz = true.
Proof.
  intros pol ge c ps l i rest j why ots Hfree Hd Eat Href Hp.
  pose proof (pstep_erases pol ge c ps) as Es; rewrite Hp in Es.
  unfold pstep, tstep in Hp; rewrite Hd, Eat in Hp.
  unfold step, or_stuck in Es; rewrite Eat, Hd in Es.
  destruct i as [d k o args | d o args lw | w off v av | off v av es | r cl args | r cl args | x sz | file line | tq];
    cbn [inst_tstep] in Hp; try discriminate Hp;
    try solve [cbn [inst_step] in Es; rewrite ?Hd in Es; cbn in Es; discriminate Es].
  - (* Let *)
    unfold let_tstep in Hp.
    destruct (is_zero_idiom o k args) eqn:Ez.
    + unfold is_zero_idiom in Ez; apply andb_true_iff in Ez as [Hint Exy].
      destruct o; try discriminate Exy;
        destruct args as [|v1 [|v2 [|]]]; try discriminate Exy;
        try (destruct v1; discriminate Exy); try (destruct v1, v2; discriminate Exy);
        destruct k; try discriminate Hint; cbn in Es;
        destruct (value_x _ _ _ v1) as [[| |]|]; cbn in Es; try discriminate Es;
        destruct (value_x _ _ _ v2) as [[| |]|]; cbn in Es; rewrite ?Hd in Es; discriminate Es.
    + destruct (pure_scalar_op o) eqn:Ep.
      * rewrite (inst_step_let _ _ _ _ _ _ _ (pure_scalar_special_let o Ep)) in Es; cbv zeta in Es.
        destruct (op_arg_classes o k) as [cls|]; [|discriminate Es].
        destruct (map2_option (value_x ge (fr_env (c_frame c))) cls args) as [xs|]; [|discriminate Es].
        cbn beta iota zeta in Es.
        destruct (op_res o k xs (c_mem c)) as [[[|rt|] m'| |]|] eqn:Eop;
          rewrite ?(pure_scalar_doomed _ _ _ _ _ _ _ _ Hd Ep) in Es; cbn in Es; try discriminate Es.
        injection Es as <-. exfalso. exact (pure_scalar_op_no_trap _ _ _ _ _ _ Ep Eop).
      * destruct o; try discriminate Ep; try discriminate Hp.
        -- (* Copy *)
           rewrite inst_step_let in Es by reflexivity; cbv zeta in Es.
           destruct args as [|v [|]]; try discriminate Hp.
           destruct (value_t _ k v); [|discriminate Hp].
           cbn [op_arg_classes map2_option] in Es; destruct (value_x _ _ k v) as [[| |]|]; try discriminate Es;
             destruct k; cbn in Es; rewrite ?Hd in Es; discriminate Es.
        -- (* Ptoi *)
           rewrite inst_step_let in Es by reflexivity; cbv zeta in Es.
           destruct args as [|v [|]]; try discriminate Hp.
           cbn [op_arg_classes map2_option] in Es; destruct (value_x _ _ P v) as [[| |]|]; try discriminate Es;
             destruct k; cbn in Es; rewrite ?Hd in Es; discriminate Es.
        -- (* Itop *)
           rewrite inst_step_let in Es by reflexivity; cbv zeta in Es.
           destruct args as [|v [|]]; try discriminate Hp.
           cbn [op_arg_classes map2_option] in Es; destruct (value_x _ _ L v) as [[| |]|]; try discriminate Es;
             destruct k; cbn in Es; rewrite ?Hd in Es; discriminate Es.
        -- (* Alloc *)
           rename align into al.
           rewrite inst_step_let in Es by reflexivity; cbv zeta in Es.
           destruct args as [|v [|]]; try discriminate Hp.
           destruct (value_x ge (fr_env (c_frame c)) L v) as [[sz| |]|] eqn:Ev; try discriminate Hp.
           destruct (value_t (ps_tenv ps) L v) as [[tsz| |]|]; try discriminate Hp.
           destruct (t_branch tsz); [discriminate Hp|].
           destruct (t_index tsz); [discriminate Hp|].
           cbn [op_arg_classes map2_option] in Es; rewrite Ev in Es; cbn beta iota zeta in Es.
           assert (Eop_al : op_res (Alloc al) k [WInt sz] (c_mem c) = op_res_int (Alloc al) k [WInt sz] (c_mem c))
             by (destruct k; reflexivity).
           rewrite Eop_al in Es; cbn [op_res_int] in Es.
           assert (Ed_al : forall ge0 fr0 m0 out0, fr_doomed fr0 = None ->
                     doomed_result ge0 fr0 m0 (Let d k (Alloc al) [v]) out0 = Some (out0, None))
             by (intros ? ? ? [|[]| | |] H0; unfold doomed_result; rewrite H0; destruct k; reflexivity).
           destruct (max_allocation_size <? sz) eqn:Ebig; cbn beta iota zeta in Es;
             rewrite (Ed_al _ _ _ _ Hd) in Es; cbn in Es; [|discriminate Es].
           injection Es as <-.
           replace (step ge c) with (Done (Trap TooBig)) in Hp
             by (symmetry; unfold step; rewrite Eat, Hd; cbn [or_stuck];
                 rewrite inst_step_let by reflexivity; cbn [op_arg_classes map2_option];
                 rewrite Ev; cbn beta iota zeta; rewrite Eop_al; cbn [op_res_int]; rewrite Ebig;
                 cbn beta iota zeta; rewrite (Ed_al _ _ _ _ Hd); reflexivity).
           injection Hp as <-.
           split; [reflexivity | split; [reflexivity | exists d, k, al, v, sz; auto]].
        -- (* Check *)
           destruct args as [|v [|]]; try discriminate Hp.
           rewrite inst_step_let in Es by reflexivity; cbv zeta in Es.
           destruct k; cbn [op_arg_classes map2_option] in Es; try discriminate Es;
             destruct (value_x _ _ P v) as [[|xp|]|]; try unfold op_res, op_res_int in Es; cbn in Es; rewrite ?Hd in Es; cbn in Es; try discriminate Es.
           destruct (access_res _ _ _ _ _ _) as [[[]|rt|]|] eqn:Eac; cbn in Es; rewrite ?Hd in Es; cbn in Es; try discriminate Es.
           injection Es as <-; exfalso; exact (access_res_not_refusal _ _ _ _ _ _ _ Eac Href).
        -- (* Renew *)
           destruct args as [|q1 [|v [|]]]; try discriminate Hp.
           rewrite inst_step_let in Es by reflexivity; cbv zeta in Es.
           destruct k; cbn [op_arg_classes map2_option] in Es; try discriminate Es;
             destruct (value_x _ _ A q1) as [[|qp|]|]; try unfold op_res, op_res_int in Es; cbn in Es; rewrite ?Hd in Es; cbn in Es; try discriminate Es;
             destruct (value_x _ _ P v) as [[|xp|]|]; try unfold op_res, op_res_int in Es; cbn in Es; rewrite ?Hd in Es; cbn in Es; try discriminate Es.
           destruct (cap_eqb _ _); cbn in Es; rewrite ?Hd in Es; cbn in Es; [|discriminate Es].
           destruct (access_res _ _ _ _ _ _) as [chk|]; cbn in Es; [|discriminate Es].
           destruct (renew_res chk xp (c_mem c)) as [[|rt|]|] eqn:Ern;
             cbn in Es; rewrite ?Hd in Es; cbn in Es; try discriminate Es.
           injection Es as <-; exfalso; exact (renew_res_not_refusal _ _ _ _ Ern Href).
        -- (* RenewHull *)
           destruct args as [|ql [|qh [|v [|]]]]; try discriminate Hp.
           rewrite inst_step_let in Es by reflexivity; cbv zeta in Es.
           destruct k; cbn [op_arg_classes map2_option] in Es; try discriminate Es;
             destruct (value_x _ _ A ql) as [[|?|]|]; try unfold op_res, op_res_int in Es; cbn in Es; rewrite ?Hd in Es; cbn in Es; try discriminate Es;
             destruct (value_x _ _ A qh) as [[|?|]|]; try unfold op_res, op_res_int in Es; cbn in Es; rewrite ?Hd in Es; cbn in Es; try discriminate Es;
             destruct (value_x _ _ P v) as [[|xp|]|]; try unfold op_res, op_res_int in Es; cbn in Es; rewrite ?Hd in Es; cbn in Es; try discriminate Es.
           destruct (cap_eqb _ _ && cap_eqb _ _); cbn in Es; rewrite ?Hd in Es; cbn in Es; [|discriminate Es].
           destruct (access_res _ _ _ _ _ _) as [chk|]; cbn in Es; [|discriminate Es].
           destruct (renew_res chk xp (c_mem c)) as [[|rt|]|] eqn:Ern;
             cbn in Es; rewrite ?Hd in Es; cbn in Es; try discriminate Es.
           injection Es as <-; exfalso; exact (renew_res_not_refusal _ _ _ _ Ern Href).
        -- (* HalfCheck *)
           destruct args as [|q1 [|v [|]]]; try discriminate Hp.
           rewrite inst_step_let in Es by reflexivity; cbv zeta in Es.
           destruct k; cbn [op_arg_classes map2_option] in Es; try discriminate Es;
             destruct (value_x _ _ A q1) as [[|?|]|]; try unfold op_res, op_res_int in Es; cbn in Es; rewrite ?Hd in Es; cbn in Es; try discriminate Es;
             destruct (value_x _ _ P v) as [[|?|]|]; try unfold op_res, op_res_int in Es; cbn in Es; rewrite ?Hd in Es; cbn in Es; try discriminate Es.
           destruct (cap_eqb _ _); cbn in Es; rewrite ?Hd in Es; cbn in Es; [|discriminate Es].
           destruct (access_res _ _ _ _ _ _) as [[[]|rt|]|] eqn:Eac; cbn in Es; [| | |discriminate Es];
             destruct (half_passes _ _ _ _ _ _ _) as [[[]|]|];
             cbn in Es; rewrite ?Hd in Es; cbn in Es; try discriminate Es;
             injection Es as <-; exfalso; exact (access_res_not_refusal _ _ _ _ _ _ _ Eac Href).
        -- (* SpanTest *)
           destruct args as [|v [|]]; try discriminate Hp.
           rewrite inst_step_let in Es by reflexivity; cbv zeta in Es.
           destruct k; cbn [op_arg_classes map2_option] in Es; try discriminate Es;
             destruct (value_x _ _ P v) as [[|[? cp]|]|]; try unfold op_res, op_res_int in Es; cbn in Es; rewrite ?Hd in Es; cbn in Es; try discriminate Es.
           destruct cp; try (cbn in Es; rewrite ?Hd in Es; cbn in Es; discriminate Es);
             destruct (object_region _ _); cbn in Es; rewrite ?Hd in Es; cbn in Es; discriminate Es.
        -- (* RenewIf *)
           destruct args as [|v [|gv [|]]]; try discriminate Hp.
           rewrite inst_step_let in Es by reflexivity; cbv zeta in Es.
           destruct k; cbn [op_arg_classes map2_option] in Es; try discriminate Es;
             destruct (value_x _ _ P v) as [[|xp|]|]; try unfold op_res, op_res_int in Es; cbn in Es; rewrite ?Hd in Es; cbn in Es; try discriminate Es;
             destruct (value_x _ _ W gv) as [[g| |]|]; try unfold op_res, op_res_int in Es; cbn in Es; rewrite ?Hd in Es; cbn in Es; try discriminate Es.
           destruct (access_res _ _ _ _ _ _) as [chk|] eqn:Eac; cbn in Es; [|discriminate Es].
           destruct (g =? 0).
           ++ destruct chk as [[]|rt|]; cbn in Es; rewrite ?Hd in Es; cbn in Es; try discriminate Es.
              injection Es as <-; exfalso; exact (access_res_not_refusal _ _ _ _ _ _ _ Eac Href).
           ++ destruct chk as [[]|[]|] eqn:Echk;
                try (cbn in Es; rewrite ?Hd in Es; cbn in Es; injection Es as <-; destruct Href; discriminate);
                destruct (renew_res _ xp (c_mem c)) as [[|rt|]|] eqn:Ern;
                cbn in Es; rewrite ?Hd in Es; cbn in Es; try discriminate Es;
                injection Es as <-; exfalso; exact (renew_res_not_refusal _ _ _ _ Ern Href).
        -- (* Limit *)
           destruct args as [|v [|]]; try discriminate Hp.
           rewrite inst_step_let in Es by reflexivity; cbv zeta in Es.
           destruct k; cbn [op_arg_classes map2_option] in Es; try discriminate Es;
             destruct (value_x _ _ P v) as [[|?|]|]; try unfold op_res, op_res_int in Es; cbn in Es; rewrite ?Hd in Es; cbn in Es; discriminate Es.
        -- (* CheckLimit *)
           destruct args as [|v [|uv [|]]]; try discriminate Hp.
           rewrite inst_step_let in Es by reflexivity; cbv zeta in Es.
           destruct k; cbn [op_arg_classes map2_option] in Es; try discriminate Es;
             destruct (value_x _ _ P v) as [[|?|]|]; try unfold op_res, op_res_int in Es; cbn in Es; rewrite ?Hd in Es; cbn in Es; try discriminate Es;
             destruct (value_x _ _ L uv) as [[| |? ?]|]; try unfold op_res, op_res_int in Es; cbn in Es; rewrite ?Hd in Es; cbn in Es; try discriminate Es.
           destruct (cap_eqb _ _ && _); cbn in Es; rewrite ?Hd in Es; cbn in Es; [|discriminate Es].
           destruct (access_res _ _ _ _ _ _) as [[[]|rt|]|] eqn:Eac; cbn in Es; rewrite ?Hd in Es; cbn in Es; try discriminate Es.
           injection Es as <-; exfalso; exact (access_res_not_refusal _ _ _ _ _ _ _ Eac Href).
        -- (* CheckLocal *)
           destruct k; destruct args; cbn in Es; try discriminate Es.
           destruct (lookup x (fr_locals (c_frame c))) as [[base|]|]; cbn in Es; try discriminate Es.
           destruct (object_region base (m_regions (c_mem c))); cbn in Es; [|discriminate Es].
           (destruct (_ && _); [unfold aligned_res in Es; destruct (_ =? 0)|]);
             cbn in Es; rewrite ?Hd in Es; cbn in Es; try discriminate Es;
             injection Es as <-; destruct Href; discriminate.
        -- (* CheckFunction *)
           destruct k; destruct args as [|v [|]]; cbn -[value_x function_check_res] in Es; try discriminate Es.
           destruct (value_x _ _ P v) as [[|xp|]|]; cbn -[function_check_res] in Es; try discriminate Es.
           unfold function_check_res in Es;
             repeat match type of Es with context [match ?x with _ => _ end] =>
               lazymatch x with
               | context [match _ with _ => _ end] => fail
               | _ => destruct x; cbn in Es; rewrite ?Hd in Es; cbn in Es; try discriminate Es
               end
             end;
             injection Es as <-; destruct Href; discriminate.
        -- (* RawLoad *)
           destruct args as [|av [|]]; try discriminate Hp.
           rewrite inst_step_let in Es by reflexivity; cbv zeta in Es.
           destruct (op_arg_classes (RawLoad t off) k) as [cls|] eqn:Eoc; [|discriminate Es].
           assert (cls = [A]) as -> by (destruct t, k; inversion Eoc; reflexivity).
           cbn [map2_option] in Es.
           destruct (value_x _ _ A av) as [[|xp|]|]; cbn beta iota zeta in Es; try discriminate Es.
           assert (Eop_ld : op_res (RawLoad t off) k [WPtr xp] (c_mem c) = op_res_int (RawLoad t off) k [WPtr xp] (c_mem c))
             by (destruct k; reflexivity).
           rewrite Eop_ld in Es; cbn [op_res_int] in Es.
           destruct (int_load_res _ _ _ _ _) as [[| |]|]; destruct k; cbn in Es; rewrite ?Hd in Es; cbn in Es; discriminate Es.
        -- (* RawLoadPointer *)
           destruct args as [|av [|]]; try discriminate Hp.
           rewrite inst_step_let in Es by reflexivity; cbv zeta in Es.
           destruct k; cbn [op_arg_classes map2_option] in Es; try discriminate Es;
             destruct (value_x _ _ A av) as [[|xp|]|]; try unfold op_res, op_res_int in Es; cbn in Es; rewrite ?Hd in Es; cbn in Es; try discriminate Es.
           destruct (access_res _ _ _ _ _ _) as [[[]| |]|];
             try destruct (pointer_load_effects _ _ _);
             cbn in Es; rewrite ?Hd in Es; cbn in Es; discriminate Es.
  - (* Flight *)
    cbn [inst_step] in Es.
    destruct (map_option (flight_arg_x ge (fr_env (c_frame c))) args); cbn in Es; [|discriminate Es].
    destruct (alu o L _) as [[| |]|]; destruct (flight_cap ge (fr_env (c_frame c)) lw);
      cbn in Es; rewrite ?Hd in Es; cbn in Es; discriminate Es.
  - (* RawStore *)
    cbn [inst_step] in Es.
    destruct (width_value_class w) as [vk|]; cbn in Es; [|discriminate Es].
    destruct (value_x ge (fr_env (c_frame c)) vk v); cbn in Es; [|discriminate Es].
    destruct (value_x ge (fr_env (c_frame c)) A av) as [[|[a cp]|]|]; cbn -[store_res] in Es; try discriminate Es.
    destruct (store_res _ _ _ _ _) as [[[[]| | ] ?]|]; cbn in Es; rewrite ?Hd in Es; cbn in Es; discriminate Es.
  - (* RawStorePointer *)
    cbn [inst_step] in Es.
    destruct (value_x ge (fr_env (c_frame c)) P v) as [xv|]; cbn -[value_x access_res pointer_store_effects] in Es; [|discriminate Es].
    destruct (value_x ge (fr_env (c_frame c)) A av) as [[|[a cp]|]|]; cbn -[access_res pointer_store_effects] in Es; try discriminate Es.
    destruct (access_res _ _ _ _ _ _) as [[[]| |]|];
      try destruct xv as [|xp|];
      try destruct (pointer_store_effects _ _ _ _);
      cbn in Es; rewrite ?Hd in Es; cbn in Es; discriminate Es.
  - (* Call *)
    destruct cl as [| |fn]; try discriminate Hp.
    cbn [inst_step] in Es.
    destruct (map_option (arg_x ge (fr_env (c_frame c))) args) as [xs|]; cbn in Es; [|discriminate Es].
    destruct (find_fn ge fn) as [[g|outfn]|]; cbn -[external_call] in Es;
      [|cbn in Es; rewrite ?Hd in Es; cbn in Es; discriminate Es|].
    + cbn in Es; rewrite ?Hd in Es; cbn in Es; destruct (call_frame g xs); discriminate Es.
    + unfold external_call in Es.
      destruct (lookup fn (ge_globals ge)); [cbn in Es; rewrite ?Hd in Es; cbn in Es; injection Es as <-; destruct Href; discriminate|].
      destruct (negb (is_free_name fn)); [cbn in Es; discriminate Es|].
      destruct r; try (cbn in Es; discriminate Es).
      destruct args as [|[[] ?] [|]]; try (cbn in Es; discriminate Es).
      destruct xs as [|x1 [|]]; try (cbn in Es; discriminate Es).
      cbn -[ge_free free_res] in Es; rewrite Hfree in Es.
      assert (Hfr_no_ref : forall xx mm rr mm', free_res xx mm = Some (RTrap rr, mm') -> ~ refusal rr).
      { intros [aa | [aa [|b0|b0|fn0|ex0]] | ? ?] mm rr mm' Hcf;
          cbn [free_res cap_free_res ptr_cap ptr_addr] in Hcf; try unfold object_free_res in Hcf;
          repeat match type of Hcf with context [match ?x with _ => _ end] =>
            lazymatch x with context [match _ with _ => _ end] => fail | _ => destruct x; try discriminate Hcf end end;
          try discriminate Hcf; injection Hcf as <- _; intros [?|?]; discriminate. }
      destruct (free_res x1 (c_mem c)) as [[[[]|rf|rf] mf]|] eqn:Efr;
        cbn in Es; rewrite ?Hd in Es; cbn in Es; try discriminate Es.
      injection Es as <-; exfalso; exact (Hfr_no_ref _ _ _ _ Efr Href).
  - (* LocalAlloc *)
    cbn [inst_step] in Es.
    destruct (lookup x (fr_locals (c_frame c))) as [[|]|]; cbn in Es; rewrite ?Hd in Es; cbn in Es; discriminate Es.
Qed.

(** Extended terminal-step constant-time soundness (`pstep_ct_done_nofail`),
    covering `Trap TooBig` refusals as well as `Ret`, `RetVoid` and
    `OutOfFuel`, and relating returned words under [word_rel]. *)
Lemma pstep_ct_done_nofail : forall pol ge c1 c2 ps o1 ots,
  pol_check_branches pol = true ->
  ge_free ge = free_res ->
  ct_rel c1 c2 ps ->
  (o1 = RetVoid \/ o1 = OutOfFuel \/ o1 = Trap TooBig \/ exists w, o1 = Ret w) ->
  pstep pol ge c1 ps = PDone o1 ots ->
  leak_of pol ge c1 = leak_of pol ge c2 /\
  exists o2,
    pstep pol ge c2 ps = PDone o2 ots /\
    ~ failure o2 /\
    (forall w1 wt, o1 = Ret w1 -> ots = [wt] -> exists w2, o2 = Ret w2 /\ word_rel wt w1 w2).
Proof.
  intros pol ge c1 c2 ps o1 ots Hcb Hfree Hrel Ho1 Hp1.
  destruct Ho1 as [-> | [-> | [-> | [w1 ->]]]].
  - pose proof (pstep_erases pol ge c1 ps) as Ed1; rewrite Hp1 in Ed1.
    destruct (pstep_ct_done pol ge c1 c2 ps RetVoid ots Hcb Hrel (or_introl eq_refl) Hp1)
      as (Eleak & o2 & Ep2).
    split; [exact Eleak|].
    (* Inspect JRetVoid vs impossible cases to know ~ failure o2 *)
    destruct Hrel as (Hfn & Hloc & Hd1 & Hd2 & Hat & Hfuel & Hreg & Hcallers & Henv & Hmem & Haux).
    unfold pstep, tstep in Hp1; rewrite Hd1 in Hp1.
    destruct (fr_at (c_frame c1)) as [xs l | l from | l [|i rest] j] eqn:Eat1.
    + discriminate Hp1.
    + destruct (c_fuel c1 =? 0) eqn:Ef0;
        [unfold step in Hp1; rewrite Eat1, Ef0 in Hp1; discriminate Hp1|].
      destruct (find_block _ _); [|discriminate Hp1].
      destruct (phis_tenv _ _ _); [|discriminate Hp1].
      unfold step in Hp1; rewrite Eat1, Ef0 in Hp1; unfold or_stuck in Hp1.
      destruct (find_block _ _); [|discriminate Hp1].
      destruct (phis_env _ _ _ _); discriminate Hp1.
    + unfold step in Hp1; rewrite Eat1 in Hp1; unfold jump_step in Hp1; rewrite Hd1 in Hp1.
      destruct j as [t | v t1 t2 | v | vs | | ]; cbn [jump_tstep] in Hp1; try discriminate Hp1.
      * unfold edge_step in Hp1; rewrite Hd1 in Hp1; destruct t; discriminate Hp1.
      * destruct (value_t _ W v) as [[tv| |]|]; try discriminate Hp1.
        destruct (t_branch tv); [discriminate Hp1|].
        unfold or_stuck, edge_step in Hp1; rewrite Hd1 in Hp1.
        destruct (value_x ge (fr_env (c_frame c1)) W v) as [[n| |]|]; try discriminate Hp1.
        destruct (if n =? 0 then t2 else t1); discriminate Hp1.
      * destruct (fn_ret (fr_fn (c_frame c1))) as [rk| |]; try discriminate Hp1.
        destruct (value_t (ps_tenv ps) rk v) as [wt|]; [|discriminate Hp1].
        unfold return_tstep in Hp1.
        destruct (ps_callers ps) as [|[cte r] tcs].
        -- unfold or_stuck, return_step in Hp1.
           destruct (value_x ge (fr_env (c_frame c1)) rk v); [|discriminate Hp1].
           destruct (c_callers c1); [|contradiction Hcallers].
           destruct (invalidate_locals _ _); discriminate Hp1.
        -- destruct (returned_tenv r [wt] cte); [|discriminate Hp1].
           unfold or_stuck, return_step in Hp1.
           destruct (value_x ge (fr_env (c_frame c1)) rk v); [|discriminate Hp1].
           destruct (c_callers c1) as [|[caller1 pd1] cs1]; [contradiction Hcallers|].
           destruct (invalidate_locals _ _); [|discriminate Hp1].
           destruct (pd_conv pd1) as [[cw kw]|];
             [destruct (converted_outcome _ _ _); [|discriminate Hp1]; destruct (returned_env _ _ _); discriminate Hp1
             |destruct (returned_env _ _ _); discriminate Hp1].
      * exists RetVoid. split; [|split; [cbn; tauto | intros ? ? H; discriminate H]].
        destruct (fn_ret (fr_fn (c_frame c1))) eqn:Eret; try discriminate Hp1.
        unfold return_tstep, return_step, or_stuck in Hp1.
        destruct (ps_callers ps) as [|[cte r] tcs] eqn:Etcs.
        -- destruct (c_callers c1), (c_callers c2) eqn:Ecs2; try contradiction Hcallers.
           destruct (invalidate_locals (fr_locals (c_frame c1)) (c_mem c1)) as [m1'|] eqn:Einv1; [|discriminate Hp1].
           destruct (invalidate_locals_rel _ _ _ _ _ _ Hreg Hmem Haux Einv1) as (m2' & Einv2 & _).
           injection Hp1 as <-.
           unfold pstep, tstep, step; unfold jump_step, return_step, or_stuck; cbv zeta.
           rewrite Hd2, <- Hat; cbn [jump_tstep]; unfold return_tstep.
           rewrite <- Hfn, Eret, Etcs, ?Hd2, <- Hloc, Einv2, Ecs2; reflexivity.
        -- destruct (returned_tenv r [] cte); [|discriminate Hp1].
           destruct (c_callers c1) as [|[caller1 pd1] cs1]; [contradiction Hcallers|].
           destruct (invalidate_locals _ _); [|discriminate Hp1].
           destruct (pd_conv pd1) as [[cw kw]|];
             [destruct (converted_outcome _ _ _); [|discriminate Hp1]; destruct (returned_env _ _ _); discriminate Hp1
             |destruct (returned_env _ _ _); discriminate Hp1].
    + exfalso.
      unfold step in Ed1; rewrite Eat1, Hd1 in Ed1; cbn [or_stuck] in Ed1.
      destruct (inst_step ge (c_frame c1) (c_mem c1) i) as [out0|] eqn:Eis; [|discriminate Ed1].
      cbn in Ed1.
      destruct (doomed_result ge (c_frame c1) (c_mem c1) i out0) as [[out d']|] eqn:Edr; [|discriminate Ed1].
      destruct out as [|o_stop|g xs pd| |]; cbn in Ed1;
        try (destruct (call_frame g xs); discriminate Ed1); try discriminate Ed1.
      injection Ed1 as ->.
      pose proof (doomed_result_clean_stop _ _ _ _ _ _ _ Edr eq_refl (or_introl eq_refl)) as ->.
      exact (inst_step_no_clean_stop _ _ _ _ _ Eis (or_introl eq_refl)).
  - (* OutOfFuel *)
    destruct Hrel as (Hfn & Hloc & Hd1 & Hd2 & Hat & Hfuel & Hreg & Hcallers & Henv & Hmem & Haux).
    pose proof (pstep_erases pol ge c1 ps) as Edone; rewrite Hp1 in Edone.
    unfold pstep, tstep in Hp1; rewrite Hd1 in Hp1.
    destruct (fr_at (c_frame c1)) as [xs l | l from | l [|i rest] j] eqn:Eat1; try discriminate Hp1.
    + destruct (c_fuel c1 =? 0) eqn:Ef0.
      * unfold step in Hp1; rewrite Eat1, Ef0 in Hp1; injection Hp1 as <-.
        split; [unfold leak_of; rewrite Eat1, <- Hat, Ef0, <- Hfuel, Ef0; reflexivity|].
        exists OutOfFuel; split; [|split; [cbn; tauto | intros ? ? H; discriminate H]].
        unfold pstep, tstep, step; rewrite Hd2, <- Hat, <- Hfuel, Ef0; reflexivity.
      * destruct (find_block _ _); [|discriminate Hp1].
        destruct (phis_tenv _ _ _); [|discriminate Hp1].
        unfold step in Hp1; rewrite Eat1, Ef0 in Hp1; unfold or_stuck in Hp1.
        destruct (find_block _ _); [|discriminate Hp1].
        destruct (phis_env _ _ _ _); discriminate Hp1.
    + unfold step in Hp1; rewrite Eat1 in Hp1; unfold jump_step in Hp1; rewrite Hd1 in Hp1.
      destruct j as [t | v t1 t2 | v | vs | | ]; cbn [jump_tstep] in Hp1; try discriminate Hp1.
      * unfold edge_step in Hp1; rewrite Hd1 in Hp1; destruct t; discriminate Hp1.
      * destruct (value_t _ W v) as [[tv| |]|]; try discriminate Hp1.
        destruct (t_branch tv); [discriminate Hp1|].
        unfold or_stuck, edge_step in Hp1; rewrite Hd1 in Hp1.
        destruct (value_x ge (fr_env (c_frame c1)) W v) as [[n| |]|]; try discriminate Hp1.
        destruct (if n =? 0 then t2 else t1); discriminate Hp1.
      * destruct (fn_ret (fr_fn (c_frame c1))) as [rk| |]; try discriminate Hp1.
        destruct (value_t (ps_tenv ps) rk v) as [wt|]; [|discriminate Hp1].
        unfold return_tstep in Hp1; destruct (ps_callers ps) as [|[cte r] tcs].
        -- unfold or_stuck, return_step in Hp1.
           destruct (value_x ge (fr_env (c_frame c1)) rk v); [|discriminate Hp1].
           destruct (c_callers c1); [|contradiction Hcallers].
           destruct (invalidate_locals _ _); discriminate Hp1.
        -- destruct (returned_tenv r [wt] cte); [|discriminate Hp1].
           unfold or_stuck, return_step in Hp1.
           destruct (value_x ge (fr_env (c_frame c1)) rk v); [|discriminate Hp1].
           destruct (c_callers c1) as [|[caller1 pd1] cs1]; [contradiction Hcallers|].
           destruct (invalidate_locals _ _); [|discriminate Hp1].
           destruct (pd_conv pd1) as [[cw kw]|];
             [destruct (converted_outcome _ _ _); [|discriminate Hp1]; destruct (returned_env _ _ _); discriminate Hp1
             |destruct (returned_env _ _ _); discriminate Hp1].
      * destruct (fn_ret (fr_fn (c_frame c1))); try discriminate Hp1.
        unfold return_tstep, return_step, or_stuck in Hp1.
        destruct (ps_callers ps) as [|[cte r] tcs].
        -- destruct (c_callers c1); [|contradiction Hcallers].
           destruct (invalidate_locals _ _); discriminate Hp1.
        -- destruct (returned_tenv r [] cte); [|discriminate Hp1].
           destruct (c_callers c1) as [|[caller1 pd1] cs1]; [contradiction Hcallers|].
           destruct (invalidate_locals _ _); [|discriminate Hp1].
           destruct (pd_conv pd1) as [[cw kw]|];
             [destruct (converted_outcome _ _ _); [|discriminate Hp1]; destruct (returned_env _ _ _); discriminate Hp1
             |destruct (returned_env _ _ _); discriminate Hp1].
    + exfalso. unfold step in Edone; rewrite Eat1, Hd1 in Edone; cbn [or_stuck] in Edone.
      destruct (inst_step ge (c_frame c1) (c_mem c1) i) as [out0|] eqn:Eis; [|discriminate Edone].
      cbn in Edone.
      destruct (doomed_result ge (c_frame c1) (c_mem c1) i out0) as [[out d']|] eqn:Edr; [|discriminate Edone].
      destruct out as [|o_stop|g xs pd| |]; cbn in Edone;
        try (destruct (call_frame g xs); discriminate Edone); try discriminate Edone.
      injection Edone as ->.
      pose proof (doomed_result_clean_stop _ _ _ _ _ _ _ Edr eq_refl (or_intror (or_introl eq_refl))) as ->.
      exact (inst_step_no_clean_stop _ _ _ _ _ Eis (or_intror (or_introl eq_refl))).
  - (* Trap TooBig *)
    pose proof Hp1 as Hp1_orig.
    pose proof (pstep_erases pol ge c1 ps) as Edone; rewrite Hp1 in Edone.
    destruct Hrel as (Hfn & Hloc & Hd1 & Hd2 & Hat & Hfuel & Hreg & Hcallers & Henv & Hmem & Haux).
    unfold pstep, tstep in Hp1; rewrite Hd1 in Hp1.
    destruct (fr_at (c_frame c1)) as [xs l | l from | l [|i rest] j] eqn:Eat1; try discriminate Hp1.
    + destruct (c_fuel c1 =? 0) eqn:Ef0;
        [unfold step in Edone; rewrite Eat1, Ef0 in Edone; discriminate Edone|].
      destruct (find_block _ _); [|discriminate Hp1].
      destruct (phis_tenv _ _ _); [|discriminate Hp1].
      unfold step in Hp1; rewrite Eat1, Ef0 in Hp1; unfold or_stuck in Hp1.
      destruct (find_block _ _); [|discriminate Hp1].
      destruct (phis_env _ _ _ _); discriminate Hp1.
    + unfold step in Edone; rewrite Eat1 in Edone; unfold jump_step in Edone; rewrite Hd1 in Edone.
      destruct j as [t | v t1 t2 | v | vs | | ]; cbn in Edone, Hp1; try discriminate Edone; try discriminate Hp1.
      * unfold edge_step in Edone; rewrite Hd1 in Edone; destruct t; discriminate Edone.
      * unfold or_stuck, edge_step in Edone; rewrite Hd1 in Edone.
        destruct (value_x ge (fr_env (c_frame c1)) W v) as [[n| |]|]; try discriminate Edone.
        destruct (if n =? 0 then t2 else t1); discriminate Edone.
      * destruct (fn_ret (fr_fn (c_frame c1))) as [rk| |]; try discriminate Hp1.
        destruct (value_t (ps_tenv ps) rk v) as [wt|]; [|discriminate Hp1].
        unfold return_tstep in Hp1; destruct (ps_callers ps) as [|[cte r] tcs].
        -- unfold or_stuck, return_step in Edone.
           destruct (value_x ge (fr_env (c_frame c1)) rk v); [|discriminate Edone].
           destruct (c_callers c1); [|contradiction Hcallers].
           destruct (invalidate_locals _ _); discriminate Edone.
        -- unfold or_stuck, return_step in Edone.
           destruct (value_x ge (fr_env (c_frame c1)) rk v); [|discriminate Edone].
           destruct (c_callers c1) as [|[caller1 pd1] cs1]; [contradiction Hcallers|].
           destruct (invalidate_locals _ _); [|discriminate Edone].
           destruct (pd_conv pd1) as [[cw kw]|];
             [destruct (converted_outcome _ _ _); [|discriminate Edone]; destruct (returned_env _ _ _); discriminate Edone
             |destruct (returned_env _ _ _); discriminate Edone].
      * destruct (fn_ret (fr_fn (c_frame c1))); try discriminate Hp1.
        unfold return_tstep in Hp1; destruct (ps_callers ps) as [|[cte r] tcs].
        -- unfold return_step, or_stuck in Edone.
           destruct (c_callers c1); [|contradiction Hcallers].
           destruct (invalidate_locals _ _); discriminate Edone.
        -- unfold return_step, or_stuck in Edone.
           destruct (c_callers c1) as [|[caller1 pd1] cs1]; [contradiction Hcallers|].
           destruct (invalidate_locals _ _); [|discriminate Edone].
           destruct (pd_conv pd1) as [[cw kw]|];
             [destruct (converted_outcome _ _ _); [|discriminate Edone]; destruct (returned_env _ _ _); discriminate Edone
             |destruct (returned_env _ _ _); discriminate Edone].
    + (* Instruction stopping with Done (Trap TooBig) *)
      destruct (inst_pstep_refusal_only_alloc pol ge c1 ps l i rest j TooBig ots Hfree Hd1 Eat1 (or_intror eq_refl) Hp1_orig)
        as (_ & -> & d & k & al & v & sz & -> & Ev1 & Ebig).
      cbn [inst_tstep] in Hp1; unfold let_tstep in Hp1.
      replace (is_zero_idiom (Alloc al) k [v]) with false in Hp1 by (destruct k; reflexivity).
      cbn [pure_scalar_op] in Hp1; rewrite Ev1 in Hp1.
      destruct (value_t (ps_tenv ps) L v) as [[tsz| |]|] eqn:Evt; try discriminate Hp1.
      destruct (t_branch tsz) eqn:Etb; [discriminate Hp1|].
      destruct (t_index tsz) eqn:Eti; [discriminate Hp1|].
      destruct (value_rel ge _ _ _ L v (WInt sz) (WTInt tsz) Henv Ev1 Evt) as ([sz2| |] & Ev2 & Hsz); try contradiction Hsz.
      assert (sz = sz2) by (destruct (Z.eq_dec sz sz2); [auto | exfalso; pose proof (Hsz n) as ->; discriminate Etb]).
      subst sz2.
      split; [unfold leak_of; rewrite Eat1, <- Hat; cbn; rewrite Ev1, Ev2; reflexivity|].
      exists (Trap TooBig).
      split; [|split; [cbn; unfold refusal; intros Hnr; apply Hnr; right; reflexivity | intros ? ? H; discriminate H]].
      unfold pstep, tstep, step; rewrite Hd2, <- Hat; cbn [inst_tstep or_stuck]; unfold let_tstep.
      replace (is_zero_idiom (Alloc al) k [v]) with false by (destruct k; reflexivity).
      cbn [pure_scalar_op]; rewrite Ev2, Evt, Etb, Eti, Ebig.
      rewrite inst_step_let by reflexivity; cbn [op_arg_classes map2_option]; rewrite Ev2; cbn beta iota zeta.
      assert (Eop_al2 : op_res (Alloc al) k [WInt sz] (c_mem c2) = op_res_int (Alloc al) k [WInt sz] (c_mem c2))
        by (destruct k; reflexivity).
      assert (Ed_al2 : forall out0, doomed_result ge (c_frame c2) (c_mem c2) (Let d k (Alloc al) [v]) out0 = Some (out0, None))
        by (intros [|[]| | |]; unfold doomed_result; rewrite Hd2; destruct k; reflexivity).
      rewrite Eop_al2; cbn [op_res_int]; rewrite Ebig; cbn beta iota zeta; rewrite Ed_al2; reflexivity.
  - (* Ret w1 *)
    pose proof (pstep_erases pol ge c1 ps) as Edone; rewrite Hp1 in Edone.
    destruct Hrel as (Hfn & Hloc & Hd1 & Hd2 & Hat & Hfuel & Hreg & Hcallers & Henv & Hmem & Haux).
    unfold pstep, tstep in Hp1; rewrite Hd1 in Hp1.
    destruct (fr_at (c_frame c1)) as [xs l | l from | l [|i rest] j] eqn:Eat1; try discriminate Hp1.
    + destruct (c_fuel c1 =? 0) eqn:Ef0;
        [unfold step in Hp1; rewrite Eat1, Ef0 in Hp1; discriminate Hp1|].
      destruct (find_block _ _); [|discriminate Hp1].
      destruct (phis_tenv _ _ _); [|discriminate Hp1].
      unfold step in Hp1; rewrite Eat1, Ef0 in Hp1; unfold or_stuck in Hp1.
      destruct (find_block _ _); [|discriminate Hp1].
      destruct (phis_env _ _ _ _); discriminate Hp1.
    + unfold step in Hp1; rewrite Eat1 in Hp1; unfold jump_step in Hp1; rewrite Hd1 in Hp1.
      destruct j as [t | v t1 t2 | v | vs | | ]; cbn [jump_tstep] in Hp1; try discriminate Hp1.
      * unfold edge_step in Hp1; rewrite Hd1 in Hp1; destruct t; discriminate Hp1.
      * destruct (value_t _ W v) as [[tv| |]|]; try discriminate Hp1.
        destruct (t_branch tv); [discriminate Hp1|].
        unfold or_stuck, edge_step in Hp1; rewrite Hd1 in Hp1.
        destruct (value_x ge (fr_env (c_frame c1)) W v) as [[n| |]|]; try discriminate Hp1.
        destruct (if n =? 0 then t2 else t1); discriminate Hp1.
      * destruct (fn_ret (fr_fn (c_frame c1))) as [rk| |] eqn:Eret; try discriminate Hp1.
        destruct (value_t (ps_tenv ps) rk v) as [wt|] eqn:Evt; [|discriminate Hp1].
        unfold return_tstep in Hp1.
        destruct (ps_callers ps) as [|[cte r] tcs] eqn:Etcs.
        -- unfold or_stuck, return_step in Hp1.
           destruct (value_x ge (fr_env (c_frame c1)) rk v) as [w1'|] eqn:Ev1; [|discriminate Hp1].
           destruct (value_rel ge _ _ _ rk v w1' wt Henv Ev1 Evt) as (w2 & Ev2 & Hwrel).
           destruct (c_callers c1), (c_callers c2) eqn:Ecs2; try contradiction Hcallers.
           destruct (invalidate_locals (fr_locals (c_frame c1)) (c_mem c1)) as [m1'|] eqn:Einv1; [|discriminate Hp1].
           destruct (invalidate_locals_rel _ _ _ _ _ _ Hreg Hmem Haux Einv1) as (m2' & Einv2 & _).
           injection Hp1 as <- <-.
           split; [unfold leak_of; rewrite Eat1, <- Hat; reflexivity|].
           exists (Ret w2); split.
           ++ unfold pstep, tstep, step; unfold jump_step, return_step, or_stuck; cbv zeta.
              rewrite Hd2, <- Hat; cbn [jump_tstep]; unfold return_tstep.
              rewrite <- Hfn, Eret, Evt, Etcs, ?Hd2, Ev2, <- Hloc, Einv2, Ecs2; reflexivity.
           ++ split; [cbn; tauto|].
              intros w1'' wt' Hw Hots. injection Hw as <-. injection Hots as <-.
              exists w2; split; [reflexivity | exact Hwrel].
        -- destruct (returned_tenv r [wt] cte); [|discriminate Hp1].
           unfold or_stuck, return_step in Hp1.
           destruct (value_x ge (fr_env (c_frame c1)) rk v); [|discriminate Hp1].
           destruct (c_callers c1) as [|[caller1 pd1] cs1]; [contradiction Hcallers|].
           destruct (invalidate_locals _ _); [|discriminate Hp1].
           destruct (pd_conv pd1) as [[cw kw]|];
             [destruct (converted_outcome _ _ _); [|discriminate Hp1]; destruct (returned_env _ _ _); discriminate Hp1
             |destruct (returned_env _ _ _); discriminate Hp1].
      * destruct (fn_ret (fr_fn (c_frame c1))); try discriminate Hp1.
        unfold return_tstep, return_step, or_stuck in Hp1.
        destruct (ps_callers ps) as [|[cte r] tcs].
        -- destruct (c_callers c1); [|contradiction Hcallers].
           destruct (invalidate_locals _ _); discriminate Hp1.
        -- destruct (returned_tenv r [] cte); [|discriminate Hp1].
           destruct (c_callers c1) as [|[caller1 pd1] cs1]; [contradiction Hcallers|].
           destruct (invalidate_locals _ _); [|discriminate Hp1].
           destruct (pd_conv pd1) as [[cw kw]|];
             [destruct (converted_outcome _ _ _); [|discriminate Hp1]; destruct (returned_env _ _ _); discriminate Hp1
             |destruct (returned_env _ _ _); discriminate Hp1].
    + exfalso. unfold step in Edone; rewrite Eat1, Hd1 in Edone; cbn [or_stuck] in Edone.
      destruct (inst_step ge (c_frame c1) (c_mem c1) i) as [out0|] eqn:Eis; [|discriminate Edone].
      cbn in Edone.
      destruct (doomed_result ge (c_frame c1) (c_mem c1) i out0) as [[out d']|] eqn:Edr; [|discriminate Edone].
      destruct out as [|o_stop|g xs pd| |]; cbn in Edone;
        try (destruct (call_frame g xs); discriminate Edone); try discriminate Edone.
      injection Edone as ->.
      assert (Ho_ret : w1 = w1) by reflexivity; clear Ho_ret.
      pose proof (doomed_result_clean_stop _ _ _ _ _ _ _ Edr eq_refl (or_intror (or_intror (ex_intro _ w1 eq_refl)))) as ->.
      exact (inst_step_no_clean_stop _ _ _ _ _ Eis (or_intror (or_intror (ex_intro _ w1 eq_refl)))).
Qed.

(** Every non-failing [PDone] outcome of [pstep] (with `ge_free ge = free_res`)
    is one of the four clean outcomes handled by [pstep_ct_done_nofail]. *)
Lemma pstep_done_nofail_cases : forall pol ge c ps o ots,
  ge_free ge = free_res ->
  ~ failure o ->
  pstep pol ge c ps = PDone o ots ->
  o = RetVoid \/ o = OutOfFuel \/ o = Trap TooBig \/ exists w, o = Ret w.
Proof.
  intros pol ge c ps o ots Hfree Hnf Hp.
  pose proof (pstep_erases pol ge c ps) as Es; rewrite Hp in Es.
  destruct o as [w | ws | | | ? | r | ? | ]; cbn [failure] in Hnf; try contradiction.
  - right; right; right; exists w; reflexivity.
  - (* Rets ws: impossible under pstep *)
    exfalso.
    unfold pstep, tstep in Hp.
    destruct (fr_doomed (c_frame c)) eqn:Ed; [discriminate Hp|].
    destruct (fr_at (c_frame c)) as [xs l | l from | l [|i rest] j] eqn:Eat.
    + discriminate Hp.
    + unfold step in Es; rewrite Eat in Es.
      destruct (c_fuel c =? 0); [discriminate Es|].
      unfold or_stuck in Es; destruct (find_block _ _); [|discriminate Es].
      destruct (phis_env _ _ _ _); discriminate Es.
    + unfold step, jump_step, return_step, edge_step, or_stuck in Es; rewrite Eat, Ed in Es.
      destruct j as [t | v t1 t2 | v | vs | | ]; cbn [jump_tstep] in Hp; try discriminate Hp;
        repeat match type of Es with context [match ?x with _ => _ end] =>
          lazymatch x with context [match _ with _ => _ end] => fail | _ => destruct x; cbn in Es; try discriminate Es end end;
        discriminate Es.
    + unfold step in Es; rewrite Eat, Ed in Es; cbn [or_stuck] in Es.
      destruct (inst_step ge (c_frame c) (c_mem c) i) as [out0|] eqn:Eis; [|discriminate Es].
      cbn in Es.
      destruct (doomed_result ge (c_frame c) (c_mem c) i out0) as [[out d']|] eqn:Edr; [|discriminate Es].
      destruct out as [|o_stop|g xs pd| |]; cbn in Es;
        try (destruct (call_frame g xs); discriminate Es); try discriminate Es.
      injection Es as ->.
      assert (out0 = IStop (Rets ws)) as ->.
      { destruct (ahead_inst i) eqn:Ea.
        - destruct i; try discriminate Ea; destruct k; try discriminate Ea;
            destruct o; try discriminate Ea; destruct args as [|? [|]]; try discriminate Ea;
            unfold doomed_result in Edr; cases Edr; inversion Edr; subst; auto; discriminate.
        - rewrite (doomed_result_other _ _ _ _ _ Ea) in Edr;
            cases Edr; inversion Edr; subst; auto; discriminate. }
      destruct i.
      1: destruct (special_let o) eqn:Esl;
           [destruct o; try discriminate Esl | rewrite (inst_step_let _ _ _ _ _ _ _ Esl) in Eis].
      all: unfold inst_step, external_call, bind_res, store_out in Eis;
        cases Eis; discriminate Eis.
  - left; reflexivity.
  - (* Trap r: ~ ~ refusal r -> r = OutOfMemory \/ r = TooBig *)
    assert (Href : r = OutOfMemory \/ r = TooBig)
      by (destruct r; try (exfalso; apply Hnf; intros [?|?]; discriminate); auto).
    destruct Href as [-> | ->]; [|right; right; left; reflexivity].
    exfalso. pose proof Hp as Hp_orig.
    unfold pstep, tstep in Hp.
    destruct (fr_doomed (c_frame c)) eqn:Ed; [discriminate Hp|].
    destruct (fr_at (c_frame c)) as [xs l | l from | l [|i rest] j] eqn:Eat; try discriminate Hp.
    + unfold step in Es; rewrite Eat in Es; destruct (c_fuel c =? 0); [discriminate Es|].
      unfold or_stuck in Es; destruct (find_block _ _); [|discriminate Es]; destruct (phis_env _ _ _ _); discriminate Es.
    + unfold step, jump_step, return_step, edge_step, or_stuck in Es; rewrite Eat, Ed in Es.
      destruct j as [t | v t1 t2 | v | vs | | ]; cbn [jump_tstep] in Hp; try discriminate Hp;
        repeat match type of Es with context [match ?x with _ => _ end] =>
          lazymatch x with context [match _ with _ => _ end] => fail | _ => destruct x; cbn in Es; try discriminate Es end end;
        discriminate Es.
    + destruct (inst_pstep_refusal_only_alloc pol ge c ps l i rest j OutOfMemory ots Hfree Ed Eat (or_introl eq_refl) Hp_orig)
        as [Hbad _]; discriminate Hbad.
  - right; left; reflexivity.
Qed.

(** Fresh-allocation step soundness (`pstep_ct_fresh`): when `(c1, ps)`
    asks for an allocation `PFresh q k1` (`Alloc` or `LocalAlloc`), any
    related configuration `c2` emits the exact same [leak_event] and
    asks for the exact same [alloc_req] `q`, and at any `base` where `c1`
    and `c2` agree on `[base, base + req_extent q)` (such as a [fresh]
    base in both), `ct_rel` is preserved after the allocation. *)
Theorem pstep_ct_fresh : forall pol ge c1 c2 ps q k1,
  pol_check_branches pol = true ->
  ct_rel c1 c2 ps ->
  pstep pol ge c1 ps = PFresh q k1 ->
  leak_of pol ge c1 = leak_of pol ge c2 /\
  exists k2,
    pstep pol ge c2 ps = PFresh q k2 /\
    forall base,
      snd (k1 base) = snd (k2 base) /\
      ((forall a, base <= a < base + req_extent q ->
          m_bytes (c_mem c1) a = m_bytes (c_mem c2) a /\
          m_aux (c_mem c1) a = m_aux (c_mem c2) a) ->
       ct_rel (fst (k1 base)) (fst (k2 base)) (snd (k1 base))).
Proof.
  intros pol ge c1 c2 ps q k1 Hcb Hrel Hp1.
  destruct Hrel as (Hfn & Hloc & Hd1 & Hd2 & Hat & Hfuel & Hreg & Hcallers & Henv & Hmem & Haux).
  unfold pstep in *. unfold tstep in Hp1; rewrite Hd1 in Hp1.
  destruct (fr_at (c_frame c1)) as [xs l | l from | l [|i rest] j] eqn:Eat1; try discriminate Hp1.
  - destruct (c_fuel c1 =? 0); [destruct (step _ _); discriminate Hp1|].
    destruct (find_block _ _); [|discriminate Hp1].
    destruct (phis_tenv _ _ _); [|discriminate Hp1].
    destruct (step _ _); discriminate Hp1.
  - destruct j as [t | v t1 t2 | v | vs | | ]; cbn [jump_tstep] in Hp1; try discriminate Hp1.
    + destruct (step _ _); discriminate Hp1.
    + destruct (value_t _ W v) as [[tv| |]|]; try discriminate Hp1.
      destruct (t_branch tv); [discriminate Hp1|].
      destruct (step _ _); discriminate Hp1.
    + destruct (fn_ret _); try discriminate Hp1.
      destruct (value_t _ _ v); [|discriminate Hp1].
      unfold return_tstep in Hp1; destruct (ps_callers ps) as [|[? r] ?];
        [destruct (step _ _); discriminate Hp1 | destruct (returned_tenv _ _ _); [destruct (step _ _) |]; discriminate Hp1].
    + destruct (fn_ret _); try discriminate Hp1.
      unfold return_tstep in Hp1; destruct (ps_callers ps) as [|[? r] ?];
        [destruct (step _ _); discriminate Hp1 | destruct (returned_tenv _ _ _); [destruct (step _ _) |]; discriminate Hp1].
    + destruct (step _ _); discriminate Hp1.
  - (* Exec l (i :: rest) j *)
    destruct i as [d k o args | d o args lw | w off v av | off v av es | r cl args | r cl args | x sz | file line | tq];
      cbn [inst_tstep] in Hp1; try discriminate Hp1;
      try solve [
        repeat (cbv zeta in Hp1;
          match type of Hp1 with
          | context [match ?x with _ => _ end] =>
              lazymatch x with
              | step _ _ => destruct x; discriminate Hp1
              | context [match _ with _ => _ end] => fail
              | _ => destruct x; try discriminate Hp1
              end
          end)].
    + (* Let: only Alloc produces TFresh *)
      unfold let_tstep, check_ptr_bounds_taint in Hp1.
      destruct (is_zero_idiom o k args) eqn:Ez; [destruct (step _ _); discriminate Hp1|].
      destruct o; try discriminate Hp1;
        try solve [
          repeat (cbv zeta in Hp1;
            match type of Hp1 with
            | context [match ?x with _ => _ end] =>
                lazymatch x with
                | step _ _ => destruct x; discriminate Hp1
                | context [match _ with _ => _ end] => fail
                | _ => destruct x; try discriminate Hp1
                end
            end)].
      (* Alloc align *)
      rename align into al.
      destruct args as [|v [|]]; try discriminate Hp1.
      destruct (value_x ge (fr_env (c_frame c1)) L v) as [[sz| |]|] eqn:Ev1; try discriminate Hp1.
      destruct (value_t (ps_tenv ps) L v) as [[tsz| |]|] eqn:Evt; try discriminate Hp1.
      destruct (t_branch tsz) eqn:Etb; [discriminate Hp1|].
      destruct (t_index tsz) eqn:Eti; [discriminate Hp1|].
      destruct (max_allocation_size <? sz) eqn:Ebig; [destruct (step _ _); discriminate Hp1|].
      destruct (value_rel ge _ _ _ L v (WInt sz) (WTInt tsz) Henv Ev1 Evt) as ([sz2| |] & Ev2 & Hsz);
        try contradiction Hsz.
      assert (sz = sz2) by (destruct (Z.eq_dec sz sz2); [auto | exfalso; pose proof (Hsz n) as ->; discriminate Etb]).
      subst sz2.
      unfold step in Hp1; rewrite Eat1, Hd1 in Hp1; cbn [or_stuck] in Hp1.
      rewrite inst_step_let in Hp1 by reflexivity; cbn [op_arg_classes map2_option] in Hp1.
      rewrite Ev1 in Hp1; cbn beta iota zeta in Hp1.
      assert (Eop_al1 : op_res (Alloc al) k [WInt sz] (c_mem c1) = op_res_int (Alloc al) k [WInt sz] (c_mem c1))
        by (destruct k; reflexivity).
      assert (Ed_al : forall ge0 fr0 m0 out0, fr_doomed fr0 = None ->
                doomed_result ge0 fr0 m0 (Let d k (Alloc al) [v]) out0 = Some (out0, None))
        by (intros ? ? ? [|[]| | |] H0; unfold doomed_result; rewrite H0; destruct k; reflexivity).
      rewrite Eop_al1 in Hp1; cbn [op_res_int] in Hp1; rewrite Ebig in Hp1; cbn beta iota zeta in Hp1;
        rewrite (Ed_al _ _ _ _ Hd1) in Hp1; cbn in Hp1.
      injection Hp1 as <- <-.
      split; [unfold leak_of; rewrite Eat1, <- Hat; cbn; rewrite Ev1, Ev2; reflexivity|].
      unfold tstep, step; rewrite Hd2, <- Hat; cbn [inst_tstep or_stuck]; unfold let_tstep.
      replace (is_zero_idiom (Alloc al) k [v]) with false by (destruct k; reflexivity).
      cbn [pure_scalar_op]; rewrite Ev2, Evt, Etb, Eti, Ebig.
      rewrite inst_step_let by reflexivity; cbn [op_arg_classes map2_option]; rewrite Ev2; cbn beta iota zeta.
      assert (Eop_al2 : op_res (Alloc al) k [WInt sz] (c_mem c2) = op_res_int (Alloc al) k [WInt sz] (c_mem c2))
        by (destruct k; reflexivity).
      rewrite Eop_al2; cbn [op_res_int]; rewrite Ebig; cbn beta iota zeta; rewrite (Ed_al _ _ _ _ Hd2); cbn.
      eexists; split; [reflexivity|].
      intros base; cbn [fst snd]; split; [reflexivity|].
      intros Hfresh_eq.
      unfold ct_rel; cbn -[put]; repeat split; auto; try congruence.
      * apply env_rel_put; [exact Henv | cbn; split; intros Hne; congruence].
      * intros a Hne; unfold unpoison_range.
        destruct ((base <=? a) && (a <? base + (sz + 15) / 16 * 16)) eqn:Ein.
        -- exfalso; apply andb_true_iff in Ein as [E1 E2]; apply Z.leb_le in E1; apply Z.ltb_lt in E2.
           destruct (Hfresh_eq a (conj E1 E2)) as [Eb _]; exact (Hne Eb).
        -- exact (Hmem a Hne).
      * intros a Hne; unfold unpoison_aux.
        destruct ((base <=? a) && (a <? base + (sz + 15) / 16 * 16)) eqn:Ein.
        -- exfalso; apply andb_true_iff in Ein as [E1 E2]; apply Z.leb_le in E1; apply Z.ltb_lt in E2.
           destruct (Hfresh_eq a (conj E1 E2)) as [_ Ea]; exact (Hne Ea).
        -- exact (Haux a Hne).
    + (* LocalAlloc x sz *)
      unfold step in Hp1; rewrite Eat1, Hd1 in Hp1; cbn [or_stuck inst_step] in Hp1.
      destruct (lookup x (fr_locals (c_frame c1))) as [[|]|] eqn:Eloc1;
        cbn in Hp1; rewrite ?Hd1 in Hp1; try discriminate Hp1.
      injection Hp1 as <- <-.
      split; [unfold leak_of; rewrite Eat1, <- Hat; reflexivity|].
      unfold tstep, step; rewrite Hd2, <- Hat; cbn [inst_tstep or_stuck inst_step].
      rewrite <- Hloc, Eloc1; cbn; rewrite Hd2; cbn.
      eexists; split; [reflexivity|].
      intros base; cbn [fst snd]; split; [reflexivity|].
      intros Hfresh_eq.
      unfold ct_rel; cbn -[put]; repeat split; auto; try congruence.
      * intros a Hne; unfold unpoison_range.
        destruct ((base <=? a) && (a <? base + sz)) eqn:Ein.
        -- exfalso; apply andb_true_iff in Ein as [E1 E2]; apply Z.leb_le in E1; apply Z.ltb_lt in E2.
           destruct (Hfresh_eq a (conj E1 E2)) as [Eb _]; exact (Hne Eb).
        -- exact (Hmem a Hne).
      * intros a Hne; unfold unpoison_aux.
        destruct ((base <=? a) && (a <? base + sz)) eqn:Ein.
        -- exfalso; apply andb_true_iff in Ein as [E1 E2]; apply Z.leb_le in E1; apply Z.ltb_lt in E2.
           destruct (Hfresh_eq a (conj E1 E2)) as [_ Ea]; exact (Hne Ea).
        -- exact (Haux a Hne).
Qed.

(** Corollary of [pstep_ct_fresh] when `base` is [fresh] in both `c1`
    and `c2` (so both memories hold `0` and `CNone` on `[base, base + req_extent q)`). *)
Lemma pstep_ct_fresh_alloc : forall pol ge c1 c2 ps q k1 base,
  pol_check_branches pol = true ->
  ct_rel c1 c2 ps ->
  pstep pol ge c1 ps = PFresh q k1 ->
  fresh (c_mem c1) q base ->
  fresh (c_mem c2) q base ->
  exists k2,
    pstep pol ge c2 ps = PFresh q k2 /\
    snd (k1 base) = snd (k2 base) /\
    ct_rel (fst (k1 base)) (fst (k2 base)) (snd (k1 base)).
Proof.
  intros pol ge c1 c2 ps q k1 base Hcb Hrel Hp1 Hf1 Hf2.
  destruct (pstep_ct_fresh pol ge c1 c2 ps q k1 Hcb Hrel Hp1) as (_ & k2 & Hp2 & Hk).
  destruct (Hk base) as [Hsnd Hrel'].
  exists k2; split; [exact Hp2 | split; [exact Hsnd | apply Hrel']].
  intros a Ha.
  destruct Hf1 as (_ & _ & _ & _ & _ & Hz1).
  destruct Hf2 as (_ & _ & _ & _ & _ & Hz2).
  destruct (Hz1 a Ha) as [Eb1 Ea1]; destruct (Hz2 a Ha) as [Eb2 Ea2].
  split; congruence.
Qed.

(** Deterministic runtime-allocated poisoned execution, extending
    Run.v's [Driver] with [pstep] and [leak_of] traces so constant-time
    theorems cover heap-allocating programs (`Alloc`, `LocalAlloc`,
    `free`, loops, `Select` and direct calls). *)
Module PoisonDriver (R : Runtime).

(** Outcome of up to `steps` deterministic poisoned transitions under R. *)
Inductive pdriver_result : Type :=
| PDriverNext (c : config) (ps : pstate) (rt : R.state)
| PDriverDone (o : outcome) (ots : list word_taint)
| PDriverTrap (why : poison_reason)
| PDriverBad (why : string).

(** Run up to [steps] transitions with R's [alloc] choosing fresh bases. *)
Fixpoint pdriver_run (pol : poison_policy) (ge : genv) (steps : nat)
    (c : config) (ps : pstate) (rt : R.state) : pdriver_result :=
  match steps with
  | O => PDriverNext c ps rt
  | S n =>
      match pstep pol ge c ps with
      | PNext c' ps' => pdriver_run pol ge n c' ps' rt
      | PDone o ots => PDriverDone o ots
      | PFresh q k =>
          if req_extent q <? 0 then PDriverBad "neg_alloc"
          else match R.alloc rt q with
               | Some (base, rt') =>
                   let '(c', ps') := k base in
                   pdriver_run pol ge n c' ps' rt'
               | None => PDriverDone (Trap OutOfMemory) []
               end
      | PTrap why => PDriverTrap why
      | PStuck why => PDriverBad why
      end
  end.

(** Leakage trace collected along [pdriver_run]. *)
Fixpoint pdriver_trace (pol : poison_policy) (ge : genv) (steps : nat)
    (c : config) (ps : pstate) (rt : R.state) : option (list leak_event) :=
  match steps with
  | O => Some []
  | S n =>
      let ev := leak_of pol ge c in
      match pstep pol ge c ps with
      | PNext c' ps' =>
          let* rest := pdriver_trace pol ge n c' ps' rt in
          Some (ev :: rest)
      | PDone _ _ => Some [ev]
      | PFresh q k =>
          if req_extent q <? 0 then None
          else match R.alloc rt q with
               | Some (base, rt') =>
                   let '(c', ps') := k base in
                   let* rest := pdriver_trace pol ge n c' ps' rt' in
                   Some (ev :: rest)
               | None => Some [ev]
               end
      | PTrap _ | PStuck _ => None
      end
  end.

(** Any clean [pdriver_run] result (`PDriverNext` or `PDriverDone`)
    produces a `Some tr` leakage trace. *)
Lemma pdriver_run_has_trace : forall pol ge steps c ps rt,
  (match pdriver_run pol ge steps c ps rt with
   | PDriverNext _ _ _ | PDriverDone _ _ => True
   | PDriverTrap _ | PDriverBad _ => False
   end) ->
  exists tr, pdriver_trace pol ge steps c ps rt = Some tr.
Proof.
  intros pol ge steps; induction steps as [|n IH]; intros c ps rt Hok; cbn in *.
  - exists []; reflexivity.
  - destruct (pstep pol ge c ps) as [c' ps' | o ots | q k | why | why] eqn:Ep; try contradiction Hok.
    + destruct (IH c' ps' rt Hok) as [rest ->]; eexists; reflexivity.
    + eexists; reflexivity.
    + destruct (req_extent q <? 0); [contradiction Hok|].
      destruct (R.alloc rt q) as [[base rt']|]; [|eexists; reflexivity].
      destruct (k base) as [c' ps'].
      destruct (IH c' ps' rt' Hok) as [rest ->]; eexists; reflexivity.
Qed.

(** Two-run constant-time noninterference for heap-allocating programs
    under [PoisonDriver]: if `(c1, ps0)` and `(c2, ps0)` start [ct_rel]
    in ready runtime state [rt], and `(c1, ps0)` runs up to [steps]
    transitions without any [PDriverTrap], [PDriverBad] or [failure]
    ending, then `(c2, ps0)` emits the exact same leakage trace `tr`
    (and related return value when returning). *)
Theorem pdriver_ct_sound : forall pol ge steps c1 c2 ps rt tr,
  pol_check_branches pol = true ->
  ge_free ge = free_res ->
  R.ready rt (c_mem c1) ->
  R.ready rt (c_mem c2) ->
  ct_rel c1 c2 ps ->
  (match pdriver_run pol ge steps c1 ps rt with
   | PDriverNext _ _ _ => True
   | PDriverDone o _ => ~ failure o
   | PDriverTrap _ | PDriverBad _ => False
   end) ->
  pdriver_trace pol ge steps c1 ps rt = Some tr ->
  pdriver_trace pol ge steps c2 ps rt = Some tr /\
  match pdriver_run pol ge steps c1 ps rt, pdriver_run pol ge steps c2 ps rt with
  | PDriverDone o1 ots1, PDriverDone o2 ots2 =>
      ots1 = ots2 /\ ~ failure o2 /\
      (forall w1 wt, o1 = Ret w1 -> ots1 = [wt] -> exists w2, o2 = Ret w2 /\ word_rel wt w1 w2)
  | PDriverNext c1' ps1' rt1', PDriverNext c2' ps2' rt2' =>
      ps1' = ps2' /\ rt1' = rt2' /\ ct_rel c1' c2' ps1'
  | _, _ => False
  end.
Proof.
  intros pol ge steps; induction steps as [|n IH];
    intros c1 c2 ps rt tr Hcb Hfree Hr1 Hr2 Hrel Hok Htr; cbn -[pstep leak_of R.alloc req_extent] in *.
  - injection Htr as <-; split; [reflexivity | split; [reflexivity | split; [reflexivity | exact Hrel]]].
  - destruct (pstep pol ge c1 ps) as [c1' ps' | o1 ots | q k1 | why | why] eqn:Ep1;
      try (exfalso; exact Hok).
    + (* PNext *)
      destruct (pdriver_trace pol ge n c1' ps' rt) as [rest|] eqn:Etr1; [|discriminate Htr].
      injection Htr as <-.
      destruct (pstep_ct_sound pol ge c1 c2 ps c1' ps' Hcb Hfree Hrel Ep1) as (Eleak & c2' & Ep2 & Hrel').
      pose proof (pstep_erases pol ge c1 ps) as Es1; rewrite Ep1 in Es1.
      pose proof (pstep_erases pol ge c2 ps) as Es2; rewrite Ep2 in Es2.
      assert (Hfk : free_keeps (ge_free ge)) by (rewrite Hfree; exact free_res_keeps).
      pose proof (R.ready_kept _ _ _ Hr1 (step_next_kept _ _ _ Hfk Es1)) as Hr1'.
      pose proof (R.ready_kept _ _ _ Hr2 (step_next_kept _ _ _ Hfk Es2)) as Hr2'.
      destruct (IH c1' c2' ps' rt rest Hcb Hfree Hr1' Hr2' Hrel' Hok Etr1) as [Etr2 Hpost].
      rewrite Ep2, Etr2; cbn -[leak_of]; rewrite <- Eleak; split; [reflexivity | exact Hpost].
    + (* PDone *)
      injection Htr as <-.
      pose proof (pstep_done_nofail_cases pol ge c1 ps o1 ots Hfree Hok Ep1) as Hcases.
      destruct (pstep_ct_done_nofail pol ge c1 c2 ps o1 ots Hcb Hfree Hrel Hcases Ep1)
        as (Eleak & o2 & Ep2 & Hnf2 & Hret).
      rewrite Ep2; cbn -[leak_of failure]; rewrite <- Eleak; split; [reflexivity | split; [reflexivity | split; [exact Hnf2 | exact Hret]]].
    + (* PFresh *)
      destruct (req_extent q <? 0) eqn:Eneg; [exfalso; exact Hok|].
      apply Z.ltb_ge in Eneg.
      destruct (pstep_ct_fresh pol ge c1 c2 ps q k1 Hcb Hrel Ep1) as (Eleak & k2 & Ep2 & Hk).
      pose proof (pstep_erases pol ge c1 ps) as Es1; rewrite Ep1 in Es1.
      destruct Es1 as (k1_0 & Es1 & Hk1_0).
      pose proof (pstep_erases pol ge c2 ps) as Es2; rewrite Ep2 in Es2.
      destruct Es2 as (k2_0 & Es2 & Hk2_0).
      destruct (step_fresh_kept _ _ _ _ Es1) as [Halign Hkept1].
      destruct (step_fresh_kept _ _ _ _ Es2) as [_ Hkept2].
      rewrite Ep2, (proj2 (Z.ltb_ge _ _) Eneg); cbn -[leak_of R.alloc].
      destruct (R.alloc rt q) as [[base rt']|] eqn:Ealloc.
      * destruct (R.fresh_allocation _ _ _ _ _ Hr1 Halign Eneg Ealloc) as [Hf1 Hra1].
        destruct (R.fresh_allocation _ _ _ _ _ Hr2 Halign Eneg Ealloc) as [Hf2 Hra2].
        destruct (Hk base) as [Hsnd Hrel_k].
        assert (Hfeq : forall a, base <= a < base + req_extent q ->
                  m_bytes (c_mem c1) a = m_bytes (c_mem c2) a /\
                  m_aux (c_mem c1) a = m_aux (c_mem c2) a).
        { intros a Ha.
          destruct Hf1 as (_ & _ & _ & _ & _ & Hz1); destruct Hf2 as (_ & _ & _ & _ & _ & Hz2).
          destruct (Hz1 a Ha) as [Eb1 Ea1]; destruct (Hz2 a Ha) as [Eb2 Ea2]; split; congruence. }
        pose proof (Hrel_k Hfeq) as Hrel'.
        destruct (k1 base) as [c1' ps1'] eqn:Ek1; destruct (k2 base) as [c2' ps2'] eqn:Ek2.
        cbn [fst snd] in Hsnd, Hrel'; subst ps2'.
        assert (Hc1' : c1' = k1_0 base) by (pose proof (Hk1_0 base) as H0; rewrite Ek1 in H0; exact H0).
        assert (Hc2' : c2' = k2_0 base) by (pose proof (Hk2_0 base) as H0; rewrite Ek2 in H0; exact H0).
        pose proof (R.ready_kept _ _ _ Hra1 (eq_ind_r (fun x => kept _ (c_mem x)) (Hkept1 base) Hc1')) as Hr1'.
        pose proof (R.ready_kept _ _ _ Hra2 (eq_ind_r (fun x => kept _ (c_mem x)) (Hkept2 base) Hc2')) as Hr2'.
        destruct (pdriver_trace pol ge n c1' ps1' rt') as [rest|] eqn:Etr1; [|discriminate Htr].
        injection Htr as <-.
        destruct (IH c1' c2' ps1' rt' rest Hcb Hfree Hr1' Hr2' Hrel' Hok Etr1) as [Etr2 Hpost].
        rewrite Etr2; cbn -[leak_of]; rewrite <- Eleak; split; [reflexivity | exact Hpost].
      * injection Htr as <-; cbn -[leak_of]; rewrite <- Eleak; split; [reflexivity|].
        split; [reflexivity | split; [cbn; unfold refusal; intros Hnr; apply Hnr; left; reflexivity | intros ? ? H; discriminate H]].
Qed.

End PoisonDriver.
