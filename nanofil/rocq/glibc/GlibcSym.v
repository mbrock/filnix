(** A block proof today steps one instruction at a time, and at every
    load or check the author names the ownership facts the rule needs
    and proves the same address arithmetic again. This module replaces
    that work for straight-line code with a symbolic executor written
    as an ordinary Rocq function. The function reads a description of
    the environment and of the owned memory, runs every instruction of
    a block, and returns what holds at the block's end together with
    the arithmetic conditions it could not settle itself.

    One theorem, [sym_sound], states that the function's answer is a
    valid proof step: if the conditions hold and the description was
    true of the real state, the block's [[weakest-precondition]] holds.
    The theorem is proved once from the existing instruction rules, so
    running the executor inside a proof costs one computation instead
    of a tactic step per instruction.

    The description is syntax with a valuation. Integers, pointers and
    object regions that the executor cannot see inside are numbered
    variables, and the valuation supplies their values. Anything in the
    proof context that the executor does not recognise stays in the
    context untouched, so it acts as the frame of the [[separation-logic]]
    step. This is the first stage of the executor: lets, flights,
    checks, and loads and stores at a constant offset, in one block. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run
  Machine Pieces Heap Language Logic ExternalCalls StepRules.
From Glibc Require Import Fix GlibcTactics.
Import ListNotations LG0 LG0.L.
Open Scope Z_scope.

(** ## Symbolic integers, capabilities and words

    A temporary in a block holds an integer or a pointer whose parts
    are known only as expressions over the proof's variables. These
    types describe such values, and the valuation gives each variable
    the value it has in the proof. *)

(** An integer expression is built from constants, integer variables,
    the address of a pointer variable, the end of a region variable,
    sums, differences, remainders by a constant, and comparisons. The
    comparison [ZCmp] c k a b is one when a and b of class k satisfy c,
    and zero otherwise, as the IR's `cmp` instruction computes. *)
Inductive zexp : Type :=
  | ZK (z : Z)
  | ZV (n : nat)
  | ZAddr (n : nat)
  | ZEnd (n : nat)
  | ZAdd (a b : zexp)
  | ZSub (a b : zexp)
  | ZMod (a : zexp) (m : Z)
  | ZCmp (c : cond) (k : class) (a b : zexp).

(** A capability is absent, a writable or read-only object at a base
    address, or the unknown capability of a pointer variable. *)
Inductive scap : Type :=
  | SCNone
  | SCObj (b : zexp)
  | SCRo (b : zexp)
  | SCOf (n : nat).

(** A symbolic word is an integer or a pointer made of an address and
    a capability. A pointer variable p is described as [SWPtr] with
    address [ZAddr] and capability [SCOf] of the same number. *)
Inductive sword : Type :=
  | SWInt (x : zexp)
  | SWPtr (a : zexp) (c : scap).

(** The valuation gives the integer variables, the pointer variables
    and the region variables their values in the proof. *)
Record valuation : Type := mkVal { vz : list Z; vp : list ptr; vr : list region }.

(** The value of an integer expression. A variable outside the
    valuation reads as zero, and so does a comparison whose class the
    model rejects; the executor never produces either. *)
Fixpoint zden (ρ : valuation) (x : zexp) : Z :=
  match x with
  | ZK z => z
  | ZV n => nth n (vz ρ) 0
  | ZAddr n => match nth_error (vp ρ) n with Some p => ptr_addr p | None => 0 end
  | ZEnd n => match nth_error (vr ρ) n with Some r => r_end r | None => 0 end
  | ZAdd a b => zden ρ a + zden ρ b
  | ZSub a b => zden ρ a - zden ρ b
  | ZMod a m => zden ρ a mod m
  | ZCmp c k a b => match cond_bit c k (zden ρ a) (zden ρ b) with Some v => v | None => 0 end
  end.

(** The value of a symbolic capability. *)
Definition cden (ρ : valuation) (c : scap) : cap :=
  match c with
  | SCNone => CNone
  | SCObj b => Obj (zden ρ b)
  | SCRo b => Ro (zden ρ b)
  | SCOf n => match nth_error (vp ρ) n with Some p => ptr_cap p | None => CNone end
  end.

(** The value of a symbolic word. *)
Definition wden (ρ : valuation) (w : sword) : word :=
  match w with
  | SWInt x => WInt (zden ρ x)
  | SWPtr a c => WPtr (mkPtr (zden ρ a) (cden ρ c))
  end.

(** ## What the executor may assume

    The executor removes a wrap such as x mod 2^64 when it knows that
    x already lies in range, and it treats two capabilities as equal
    when the proof says they are. These facts come from the proof's
    hypotheses, and [sym_sound] asks for them to hold. *)

(** A bound says that lo ≤ x < hi for the integer expression x. *)
Record bound : Type := mkBound { bd_exp : zexp; bd_lo : Z; bd_hi : Z }.

(** The facts are a list of bounds and a list of capability equations. *)
Record facts : Type := mkFacts { f_bounds : list bound; f_caps : list (scap * scap) }.

(** The facts hold under ρ when every bound and every equation does. *)
Definition facts_hold (ρ : valuation) (fs : facts) : Prop :=
  Forall (fun bd => bd_lo bd <= zden ρ (bd_exp bd) < bd_hi bd) (f_bounds fs) /\
  Forall (fun ce => cden ρ (fst ce) = cden ρ (snd ce)) (f_caps fs).

(** ## The environment

    The executor knows the values of some temporaries as symbolic
    words, and it records each temporary that a block assigns. The
    real environment after the block is the starting environment with
    those assignments applied in order, which is the chain of [put]
    calls that the step tactics produce today. *)

(** A symbolic environment lists the known temporaries with their values. *)
Definition senv : Type := list (name * sword).

(** A real environment e matches se under ρ when every listed
    temporary has the listed value in e. Other temporaries may hold
    anything. *)
Definition env_models (ρ : valuation) (se : senv) (e : env) : Prop :=
  Forall (fun nw => lookup (fst nw) e = Some (wden ρ (snd nw))) se.

(** The environment after a block applies its assignments, the first
    one innermost. *)
Definition apply_ups (ρ : valuation) (ups : list (name * sword)) (e : env) : env :=
  fold_left (fun e u => put (fst u) (wden ρ (snd u)) e) ups e.

(** ## Owned memory

    The executor reads and changes only the ownership facts it is
    given, each described as an atom. An atom names the same resource
    as one of the logic's assertions, so the real proof context and
    the description can be exchanged by computation. *)

(** [ALive] b r is the lifetime [live] of the object at b with region
    variable r. [ACell] b o v is the integer cell [icell] at offset o.
    [APCell] b o a c is the pointer cell [pcell] holding the pointer
    with address a and capability c. [ALiveCap] c r is [live_cap], the
    target lifetime that a pointer load needs. *)
Inductive atom : Type :=
  | ALive (b : zexp) (r : nat)
  | ACell (b o v : zexp)
  | APCell (b o a : zexp) (c : scap)
  | ALiveCap (c : scap) (r : nat).

(** ## What the executor returns

    The executor runs until the block's jump, or until an instruction
    it cannot handle. It returns the state at that point, the
    conditions it left for the proof, and how the block continues. *)

(** A condition left for the proof: an inequality or equation between
    integer expressions, or the world condition of a store, which says
    that the external world's interpretation survives writing the new
    value. A store of an integer cell carries its old and new values,
    and a store of a pointer cell its old and new pointers. *)
Inductive ob : Type :=
  | OLe (a b : zexp)
  | OLt (a b : zexp)
  | OEq (a b : zexp)
  | OStoreW (b o : zexp) (r : nat) (old new : zexp)
  | OStoreP (b o : zexp) (r : nat) (old new : sword).

(** The reason an execution stopped before the block's jump. Each
    reason names what was missing, in terms an author can act on: the
    lifetime of object b, the cell at b plus o, the target lifetime of
    a loaded pointer, a capability that is not a known object, a
    temporary the executor does not know, or an instruction outside
    the executor's fragment. *)
Inductive stop_reason : Type :=
  | NoLive (b : zexp)
  | NoCell (b o : zexp)
  | NoLiveCap (c : scap)
  | NotObject (c : scap)
  | UnknownTmp (n : name)
  | Unsupported (i : inst)
  | NotYet.

(** The state at the end of an execution: the known temporaries, the
    assignments made in order, the atoms owned now, and the conditions
    left for the proof. *)
Record sstate : Type := mkSState {
  st_env : senv; st_ups : list (name * sword); st_heap : list atom; st_obs : list ob }.

(** An execution ends at a jump to a target, at a branch on a symbolic
    condition, or stopped before the instructions rest and the jump j. *)
Inductive leaf : Type :=
  | LGoto (t : target) (s : sstate)
  | LBranch (c : zexp) (t1 t2 : target) (s : sstate)
  | LStop (why : stop_reason) (rest : list inst) (j : jump) (s : sstate).

(** ## The executor

    The executor walks the block's instructions with the facts, the
    known environment and the owned atoms. It is defined here as a
    stub that stops at once, so that the statements below are fixed
    before the implementation is written. *)

(** [sym_block] ge fs se h l insts j runs the instructions insts and the
    jump j of the block labelled l, starting from the known environment
    se and the atoms h. The implementation must handle general lets of
    [Add], [Sub], [Ptoi], [Copy] and [Cmp], flights, [Check] and
    [HalfCheck] with [Obj] capabilities, [RawLoad] of a 64-bit integer,
    [RawLoadPointer], [RawStore] of a 64-bit integer and
    [RawStorePointer]. It finds an atom by comparing base expressions
    and offsets after removing wraps that the bounds make redundant,
    settles comparisons between constants itself, and leaves every
    other condition as an [ob]. *)
Definition sym_block (ge : genv) (fs : facts) (se : senv) (h : list atom)
    (l : name) (insts : list inst) (j : jump) : leaf :=
  LStop NotYet insts j (mkSState se [] h []).

(** ## Soundness

    The meaning of an atom is the logic's assertion it names, and the
    meaning of a leaf is what the proof must still show. The theorem
    [sym_sound] then says that showing the leaf proves the block. *)

Section sound.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context {world : Type} (registry : name -> option (contract world))
  (wi : mem -> world -> gmap piece pval -> Prop) `{!SafepointStable wi} (ge : genv).
Local Instance sym_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry wi ge.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** An atom means the assertion it names. A region variable outside
    the valuation makes the atom false. *)
Definition atom_den (ρ : valuation) (a : atom) : iProp Σ :=
  match a with
  | ALive b r => match nth_error (vr ρ) r with Some reg => live (zden ρ b) reg | None => False end
  | ACell b o v => icell (zden ρ b) (zden ρ o) (zden ρ v)
  | APCell b o a c => pcell (zden ρ b) (zden ρ o) (mkPtr (zden ρ a) (cden ρ c))
  | ALiveCap c r => match nth_error (vr ρ) r with Some reg => live_cap (cden ρ c) reg | None => False end
  end.

(** A list of atoms means their separating conjunction, written so that
    it computes to the nested form that the proof mode combines. *)
Fixpoint heap_den (ρ : valuation) (h : list atom) : iProp Σ :=
  match h with
  | [] => emp
  | a :: h => atom_den ρ a ∗ heap_den ρ h
  end.

(** The pieces an integer cell or a pointer cell owns, with the object's
    lifetime first, as the store rules state their world condition. *)
Definition cell_pieces (b o : Z) (reg : region) (w : word) : list (piece * pval) :=
  match w with
  | WInt v => [(PLive b, VLive reg)] ++ cell b o v
  | WPtr x => [(PLive b, VLive reg)] ++ (PAux b o, VAux (ptr_cap x)) :: cell b o (ptr_addr x)
  | WLimit _ _ => []
  end.

(** A condition means the corresponding proposition. The world
    condition of a store is the premise that [wp_raw_store] and
    [wp_raw_store_pointer] take. *)
Definition ob_den (ρ : valuation) (o : ob) : Prop :=
  match o with
  | OLe a b => zden ρ a <= zden ρ b
  | OLt a b => zden ρ a < zden ρ b
  | OEq a b => zden ρ a = zden ρ b
  | OStoreW b o r old new =>
      exists reg, nth_error (vr ρ) r = Some reg /\
      let b' := zden ρ b in let o' := zden ρ o in
      forall m wd h,
        (forall l v, (l, v) ∈ cell_pieces b' o' reg (WInt (zden ρ old)) -> h !! l = Some v) ->
        wi m wd h ->
        wi (store_bytes m (b' + o') 8 (zden ρ new)) wd
           (overwrite (cell_pieces b' o' reg (WInt (zden ρ new))) h)
  | OStoreP b o r old new =>
      exists reg, nth_error (vr ρ) r = Some reg /\
      match wden ρ old, wden ρ new with
      | WPtr x, WPtr xp =>
          let b' := zden ρ b in let o' := zden ρ o in
          forall m wd h,
            (forall l v, (l, v) ∈ cell_pieces b' o' reg (WPtr x) -> h !! l = Some v) ->
            wi m wd h ->
            wi (store_bytes (store_aux m (b' + o') (ptr_cap xp)) (b' + o') 8 (ptr_addr xp)) wd
               (overwrite (cell_pieces b' o' reg (WPtr xp)) h)
      | _, _ => False
      end
  end.

(** All conditions of a list hold. *)
Definition obs_den (ρ : valuation) (os : list ob) : Prop := Forall (ob_den ρ) os.

(** What the proof must show for a leaf. After a jump or a branch the
    rest of the proof comes after at least one step, so it may use
    hypotheses guarded by a [[later-modality]]. The new atoms and the
    facts about the new environment are handed to it as premises. A
    stopped execution returns the remaining instructions to the
    ordinary step tactics. *)
Definition leaf_den (ρ : valuation) (f : func) (e : env) (ls : list (name * option Z))
    (l : name) (Φ : val (nanofil_lang registry ge) -> iProp Σ) (lf : leaf) : iProp Σ :=
  match lf with
  | LGoto t s =>
      let e' := apply_ups ρ (st_ups s) e in
      ⌜obs_den ρ (st_obs s)⌝ ∗
      ▷ (heap_den ρ (st_heap s) -∗ ⌜env_models ρ (st_env s) e'⌝ -∗
         WP (ERun (mkFrame f e' ls None (Enter (edge_label t) (Some l))) : gexpr) {{ Φ }})
  | LBranch c t1 t2 s =>
      let e' := apply_ups ρ (st_ups s) e in
      ⌜obs_den ρ (st_obs s)⌝ ∗
      ▷ (heap_den ρ (st_heap s) -∗ ⌜env_models ρ (st_env s) e'⌝ -∗
         WP (ERun (mkFrame f e' ls None
              (Enter (edge_label (if zden ρ c =? 0 then t2 else t1)) (Some l))) : gexpr) {{ Φ }})
  | LStop _ rest j s =>
      let e' := apply_ups ρ (st_ups s) e in
      ⌜obs_den ρ (st_obs s)⌝ ∗
      (heap_den ρ (st_heap s) -∗ ⌜env_models ρ (st_env s) e'⌝ -∗
       WP (ERun (mkFrame f e' ls None (Exec l rest j)) : gexpr) {{ Φ }})
  end.

(** Running the executor on a block is a valid proof step: when the
    facts hold and the known environment and the atoms describe the
    real state, the leaf's requirement proves the block. *)
Theorem sym_sound fs se h f e ls l insts j ρ Φ :
  facts_hold ρ fs -> env_models ρ se e ->
  heap_den ρ h -∗ leaf_den ρ f e ls l Φ (sym_block ge fs se h l insts j) -∗
  WP (ERun (mkFrame f e ls None (Exec l insts j)) : gexpr) {{ Φ }}.
Proof. Admitted.

End sound.
