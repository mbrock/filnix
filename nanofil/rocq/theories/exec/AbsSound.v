(** The checker of [AbsRun](AbsRun.v) and [AbsInfer](AbsInfer.v) answers
    yes or no for one function and one specification. This module says
    what a yes means in the program logic, so that the answer can be
    used as a proof. It states the theorem that a function which
    passes [verify] satisfies its specification as a function triple.
    The meaning of abstract values and states comes from
    [AbsDen](AbsDen.v), and this module adds the ownership of memory.

    This file holds the definitions and the statement. The proof of the
    statement is being written, so the statement is recorded as a
    proposition and no theorem here claims it yet. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics
  Pieces Heap Language Logic StringLogic MemLogic ExternalCalls AbsRun AbsInfer AbsDen.
Import ListNotations.
Open Scope Z_scope.

(** * The world invariant

    The program logic carries an invariant about the world outside the
    program, and every rule for a store or an allocation asks that the
    invariant survives the update. The checker can only promise this
    for an invariant that does not depend on the bytes of the program's
    objects. The class [StoreStable] states that property. A store
    keeps every region, and the invariant may only look at lifetimes.
    An allocation adds one object at an unused address. *)

Class StoreStable {world : Type} (wi : mem -> world -> gmap piece pval -> Prop) : Prop := {
  wi_store : forall m m' w h ps,
    m_regions m' = m_regions m ->
    (forall l v, (l, v) ∈ ps -> match l with PLive _ => h !! l = Some v | _ => True end) ->
    wi m w h -> wi m' w (overwrite ps h);
  wi_alloc : forall m w h q base,
    Memory.fresh m q base -> wi m w h -> wi (allocated m q base) w (overwrite (obj_ps base q) h)
}.

(** * Owned memory and the theorem *)

Module AbsSoundOn (R : Runtime) (LG0 : LogicSig R).
Module ML := MemLogicOn R LG0.
Import LG0 LG0.L.

Section sound.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context {world : Type} (registry : name -> option (contract world))
  (wi : mem -> world -> gmap piece pval -> Prop) `{!SafepointStable wi, !StoreStable wi} (ge : genv).
Local Instance abs_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry wi ge.
Local Notation aexpr := (language.expr (nanofil_lang registry ge)).

(** The checker is run with these five parameters, and the proposition
    [guard] gives its guard a meaning. *)
Variable guard : Prop.
Variable builtin : hook.
Variable gobjs : list name.
Variable fnames : list (name * (list class * ret_type)).
Variable specs : name -> list fspec.

(** An object with contents is owned whole: its lifetime, all its
    bytes and all its shadow slots. *)
Definition own_obj (pl : place) (xs : list Z) (cs : list cap) : iProp Σ :=
  pts (block_ps (pl_base pl) (pl_reg pl) 0 xs cs).

(** The contents of a state are owned one object at a time, each at
    the place with its number. *)
Definition own (B : list place) (X : cont) : iProp Σ :=
  [∗ list] i ↦ x ∈ X,
    match x with
    | Some (xs, cs) => ∃ pl, ⌜nth_error B i = Some pl⌝ ∗ own_obj pl xs cs
    | None => True
    end.

(** A state describes a real frame when some list of places and some
    contents make it true and the contents are owned. The list [B0]
    holds the places the function started with, which stay in front.
    The pairs of [vs] and [ws] are operands that an instruction has
    already read. *)
Definition dstate (B0 : list place) (st : astate) (e : env) (vs : list aval) (ws : list word) : iProp Σ :=
  ∃ B X, ⌜(exists B1, B = B0 ++ B1) /\ D guard ge gobjs B st e X vs ws⌝ ∗ own B X.

(** An object that a specification names is owned whole, and its
    contents are the ones the specification describes. A specification
    mentions no symbol, so its objects are read under the valuation
    that sends every symbol to zero, after [open_obj] has forgotten any
    byte that names one. *)
Definition dcobjs (B : list place) (os : list (option aobj)) : iProp Σ :=
  [∗ list] i ↦ o ∈ os,
    match o with
    | Some ob => ∃ pl xs cs, ⌜nth_error B i = Some pl /\ obj_ok guard (fun _ => 0) B pl (open_obj ob) xs cs⌝ ∗
                             own_obj pl xs cs
    | None => True
    end.

(** A function satisfies a triple when a call with these argument words
    and this precondition runs without a panic and returns only
    outcomes that satisfy the postcondition. This is the triple of the
    glibc proofs, stated here for any instance of the logic. *)
Definition fn_triple (g : name) (xs : list word) (P : iProp Σ) (Q : outcome -> iProp Σ) : Prop :=
  exists gf, find_fn ge g = Some (Defined gf) /\ is_Some (call_frame gf xs) /\
    forall fr Φ, call_frame gf xs = Some fr ->
      ⊢ P -∗ (∀ r, Q r -∗ Φ r) -∗ WP (ERun fr : aexpr) {{ Φ }}.

(** A function satisfies a specification when the triple holds for
    every list of places that begins with the globals and for all
    argument words that the specification's arguments describe. The
    precondition owns the objects the specification names, and the
    postcondition returns them at the same places. *)
Definition spec_holds (g : name) (sp : fspec) : Prop :=
  forall B ws,
    length B = length (sp_pre sp) -> Forall place_ok B -> globals_ok ge gobjs B ->
    Forall2 (dcval ge B) (sp_args sp) ws ->
    (sp_guard sp = true -> guard) ->
    fn_triple g ws (dcobjs B (sp_pre sp))
      (fun out => ⌜dret ge B (sp_ret sp) out⌝ ∗ ⌜sp_guard' sp = true -> guard⌝ ∗ dcobjs B (sp_post sp))%I.

(** The hook is sound when each of its answers is a valid step of the
    program logic. The hook has been given the classes of the call's
    arguments and the values [xs] that the checker read for them in
    the state [st]. If it answers with the state [st'], then the call
    runs without a panic from any real state that [st] describes, and
    it ends in a real state that [st'] describes. *)
Definition builtin_holds : Prop :=
  forall B0 g r xs st st' f e l args rest j ws Φ,
    builtin g r (arg_classes args) xs st = Some (Some st') ->
    map_option (arg_x ge e) args = Some ws ->
    ⊢ dstate B0 st e xs ws -∗
    ▷ (∀ e', dstate B0 st' e' [] [] -∗
         WP (ERun (mkFrame f e' [] None (Exec l rest j)) : aexpr) {{ Φ }}) -∗
    WP (ERun (mkFrame f e [] None (Exec l (Call r (Global g) args :: rest) j)) : aexpr) {{ Φ }}.

(** The checker is sound when every function that passes [verify] for
    a specification and a list of cut invariants satisfies that
    specification. The statement assumes three things. The names in
    [fnames] are functions of the program with the signatures given,
    the hook is sound, and every specification that the function's
    callees are matched against holds. *)
Definition verify_sound_statement : Prop :=
  forall g f sp inv cuts fuel,
    find_fn ge g = Some (Defined f) ->
    verify builtin gobjs fnames specs f cuts fuel sp inv = true ->
    fnames_ok ge fnames -> builtin_holds ->
    (forall g' sp', In sp' (specs g') -> spec_holds g' sp') ->
    spec_holds g sp.

End sound.
End AbsSoundOn.
