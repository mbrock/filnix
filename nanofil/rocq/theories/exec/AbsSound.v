(** The checker of [AbsRun](AbsRun.v) and [AbsInfer](AbsInfer.v) answers
    yes or no for one function and one specification. This module says
    what a yes means in the program logic, so that the answer can be
    used as a proof. It states the theorem that a function which
    passes [verify] satisfies its specification as a function triple.
    The meaning of abstract values and states comes from
    [AbsDen](AbsDen.v), and this module adds the ownership of memory.

    The proof has three parts. The first part shows that each
    instruction the checker accepts runs safely while the frame owns
    the memory that the checker's state describes. The second part
    follows the checker through the blocks of a function, up to a
    return or to the head of a loop. The third part handles loops: a
    loop is safe however many times it runs, because its body was
    checked once from an invariant that every pass re-establishes.
    The theorem is at the end of the file. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics
  Pieces Heap Language Logic StringLogic MemLogic ExternalCalls AbsRun AbsInfer AbsDen AbsMem AbsStep
  AbsCall AbsOwn.
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
    bytes and all its shadow slots. The pieces are listed by
    [place_ps] in [AbsOwn](AbsOwn.v). *)
Definition own_obj (pl : place) (xs : list Z) (cs : list cap) : iProp Σ := pts (place_ps pl xs cs).

(** The contents of a state are owned together, as the pieces of every
    object that has contents. *)
Definition own (B : list place) (X : cont) : iProp Σ := pts (all_ps B X).

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

(** * Ownership of single objects *)

Lemma list_set_twice {A : Type} o (x y : A) : forall l, list_set o y (list_set o x l) = list_set o y l.
Proof using Type. induction o as [|o IH]; intros [|z l]; cbn [list_set]; try reflexivity. by rewrite IH. Qed.

(** One object is taken out of the contents of a state, and the state
    then holds nothing at its number. *)
Lemma own_take B X o pl xs cs :
  nth_error B o = Some pl -> nth_error X o = Some (Some (xs, cs)) ->
  own B X ⊣⊢ own_obj pl xs cs ∗ own B (list_set o None X).
Proof using Type.
  rewrite /own /own_obj. revert X o. induction B as [|pl0 B IH]; intros X o Hp Hx; [by destruct o|].
  destruct X as [|x X]; [by destruct o|]. destruct o as [|o]; cbn [nth_error list_set] in *.
  - injection Hp as ->. injection Hx as ->. cbn [all_ps]. by rewrite pts_app.
  - cbn [all_ps]. destruct x as [[xs0 cs0]|]; rewrite ?pts_app (IH X o Hp Hx); [|done].
    iSplit; iIntros "(H1 & H2 & H3)"; iFrame.
Qed.

(** An object is put into the contents of a state at its number. *)
Lemma own_put B X o pl xs cs :
  nth_error B o = Some pl -> (o < length X)%nat ->
  own_obj pl xs cs -∗ own B X -∗ own B (list_set o (Some (xs, cs)) X).
Proof using Type.
  rewrite /own /own_obj. revert X o. induction B as [|pl0 B IH]; intros X o Hp Hx; [by destruct o|].
  destruct X as [|x X]; [cbn [length] in Hx; lia|]. destruct o as [|o]; cbn [nth_error list_set length] in *.
  - injection Hp as ->. cbn [all_ps]. rewrite pts_app. iIntros "Ho HX". iFrame.
    destruct x as [[xs0 cs0]|]; [rewrite pts_app; iDestruct "HX" as "[_ $]" | iFrame].
  - cbn [all_ps]. iIntros "Ho HX". destruct x as [[xs0 cs0]|]; rewrite ?pts_app.
    + iDestruct "HX" as "[$ HX]". iApply (IH X o Hp with "Ho HX"). lia.
    + iApply (IH X o Hp with "Ho HX"). lia.
Qed.

(** The state of the frame between two instructions has read no
    operand. *)
Definition dst (B0 : list place) (st : astate) (e : env) : iProp Σ := dstate B0 st e [] [].

Lemma dst_intro B0 B1 ρ st e X :
  M guard ge gobjs ρ (B0 ++ B1) st e X -> own (B0 ++ B1) X -∗ dst B0 st e.
Proof using Type.
  intros HM. iIntros "Hown". iExists (B0 ++ B1), X. iFrame. iPureIntro. split; [by exists B1|].
  exists ρ. split; [exact HM|]. split; constructor.
Qed.

(** * Single instructions

    The checker trusts three things that it cannot see for itself.
    It is told which names are functions and what their signatures
    are. It asks a hook about calls to functions without a body. It
    uses a specification for every other callee. The proof assumes
    that all three are right, and the theorem states the same
    assumptions. *)
Section proof.
Hypothesis Hfn : fnames_ok ge fnames.
Hypothesis Hbuiltin : builtin_holds.
Hypothesis Hspecs : forall g' sp', In sp' (specs g') -> spec_holds g' sp'.

Local Notation ainst := (ainst builtin gobjs fnames specs).

(** An instruction that leaves memory alone runs while the frame owns
    the contents of its state, and the contents stay owned. *)
Lemma wp_abs_read B0 i st st' f e l rest j Φ :
  reads i = true -> ainst i st = Some st' ->
  dst B0 st e -∗
  ▷ (∀ e', dst B0 st' e' -∗ WP (ERun (mkFrame f e' [] None (Exec l rest j)) : aexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e [] None (Exec l (i :: rest) j)) : aexpr) {{ Φ }}.
Proof using Type* Hfn.
  intros Hr Ha. iIntros "(%B & %X & [[%B1 ->] (%ρ & %HM & _ & _)] & Hown) HK".
  destruct (ainst_read_sound guard ge builtin gobjs fnames specs Hfn ρ _ st e X i st' HM Hr Ha)
    as (e' & Hstep & ρ' & HM').
  iApply (wp_read registry wi ge (all_ps (B0 ++ B1) X) with "Hown").
  - intros m fuel Hf. apply Hstep. apply all_ps_mholds. exact (proj1 Hf).
  - iNext. iIntros "Hown". iApply "HK". by iApply (dst_intro with "Hown").
Qed.

(** A store changes the contents of one object. The frame gives up
    that object for the step and takes it back with its new contents. *)
Lemma place_ps_live pl xs cs b v :
  (PLive b, v) ∈ place_ps pl xs cs -> (PLive b, v) = (PLive (pl_base pl), VLive (pl_reg pl)).
Proof using Type.
  rewrite /place_ps /block_ps. intros Hin. apply elem_of_cons in Hin as [Hin|Hin]; [exact Hin|].
  apply elem_of_app in Hin as [Hin|Hin].
  - apply byte_ps_elem in Hin as (i & x & _ & [=] & _).
  - apply aux_ps_elem in Hin as (i & c & _ & [=] & _).
Qed.

Lemma wp_abs_write B0 i st st' f e l rest j Φ :
  is_store i = true -> ainst i st = Some st' ->
  dst B0 st e -∗
  ▷ (∀ e', dst B0 st' e' -∗ WP (ERun (mkFrame f e' [] None (Exec l rest j)) : aexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e [] None (Exec l (i :: rest) j)) : aexpr) {{ Φ }}.
Proof using Type* Hfn.
  intros Hs Ha. iIntros "(%B & %X & [[%B1 ->] (%ρ & %HM & _ & _)] & Hown) HK".
  destruct (ainst_write_sound guard ge builtin gobjs fnames specs Hfn ρ _ st e X i st' HM Hs Ha)
    as (o & pl & xs & cs & xs' & cs' & Hp & Hx & Lx & Lc & (upd & Hreg & Hst) & ρ' & HM').
  rewrite (own_take _ X o pl xs cs Hp Hx). iDestruct "Hown" as "[Ho Hrest]".
  iApply (wp_write registry wi ge (place_ps pl xs cs) (place_ps pl xs' cs') _ _ [] upd with "Ho").
  - by apply block_ps_keys.
  - intros m fuel (Hagree & Hd & _). pose proof (place_ps_holds m pl xs cs Hagree) as Hh.
    destruct (Hst f [] l rest j [] m fuel Hh) as [Hstep Hw]. split; [exact Hstep|]. split; [apply Hreg|].
    exact (writes_facts m (upd m) pl xs cs xs' cs' Hd Hh Lx Lc Hw).
  - intros m w h Hl Hwi. apply (wi_store m (upd m) w h); [apply Hreg | | exact Hwi].
    intros l0 v Hin. destruct l0 as [b| | |]; try exact I. apply Hl.
    apply place_ps_live in Hin. rewrite Hin. rewrite /place_ps /block_ps. apply elem_of_cons. by left.
  - iNext. iIntros "Ho". iApply "HK". iApply (dst_intro _ _ ρ' with "[Ho Hrest]"); [exact HM'|].
    iPoseProof (own_put _ _ o pl xs' cs' Hp with "Ho Hrest") as "H".
    { rewrite length_list_set. apply nth_error_Some. by rewrite Hx. }
    by rewrite list_set_twice.
Qed.

(** An allocation gives the frame a new object, which joins the
    contents of the state at the next free number. *)
Lemma wp_abs_alloc B0 d k al args st st' f e l rest j Φ :
  ainst (Let d k (Alloc al) args) st = Some st' ->
  dst B0 st e -∗
  ▷ (∀ e', dst B0 st' e' -∗ WP (ERun (mkFrame f e' [] None (Exec l rest j)) : aexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e [] None (Exec l (Let d k (Alloc al) args :: rest) j)) : aexpr) {{ Φ }}.
Proof using Type* Hfn.
  intros Ha. iIntros "(%B & %X & [[%B1 ->] (%ρ & %HM & _ & _)] & Hown) HK".
  destruct (ainst_alloc_sound guard ge builtin gobjs fnames specs Hfn ρ _ st e X d k al args st' HM Ha)
    as (n & Hx & [Hn0 Hn1] & Hpost).
  iApply (wp_alloc registry wi ge f e [] l d k al args rest j n with "[Hown HK]");
    [exact Hx | exact Hn0 | exact Hn1 | |].
  - intros m wd h base Hf Hwi. by apply wi_alloc.
  - iNext. iIntros (base) "(%Hb & %Hmod & %Hend) Hobj". cbn [heap_req req_align req_extent] in Hmod, Hend.
    destruct (Hpost base Hb Hmod Hend) as (ρ' & HM'). iApply "HK".
    assert (LX : length X = length (B0 ++ B1)) by (destruct HM as (_ & _ & _ & _ & _ & (_ & L2 & _)); exact L2).
    rewrite -app_assoc in HM'. iApply (dst_intro _ _ ρ' with "[Hown Hobj]"); [exact HM'|].
    rewrite /own app_assoc (all_ps_app _ _ _ _ LX) pts_app. iFrame. cbn [all_ps]. rewrite app_nil_r.
    by rewrite /obj (alloc_place_ps al n base Hn0).
Qed.

(** * Calls

    At a call the frame hands the callee the objects that its
    precondition names, and it takes back the objects of the
    postcondition. The two lemmas below follow [take_objs] and
    [give_objs] one object at a time. The objects of a specification
    are counted from the position [i0], so that the lemmas can go
    through the list. *)
Definition dcobjs_at (i0 : nat) (B : list place) (os : list (option aobj)) : iProp Σ :=
  [∗ list] k ↦ o ∈ os,
    match o with
    | Some ob => ∃ pl xs cs, ⌜nth_error B (i0 + k) = Some pl /\ obj_ok guard (fun _ => 0) B pl (open_obj ob) xs cs⌝ ∗
                             own_obj pl xs cs
    | None => True
    end.

Lemma dcobjs_at_cons i0 B o os :
  dcobjs_at i0 B (o :: os) ⊣⊢
  match o with
  | Some ob => ∃ pl xs cs, ⌜nth_error B i0 = Some pl /\ obj_ok guard (fun _ => 0) B pl (open_obj ob) xs cs⌝ ∗
                           own_obj pl xs cs
  | None => True
  end ∗ dcobjs_at (Datatypes.S i0) B os.
Proof using Type.
  rewrite /dcobjs_at big_sepL_cons Nat.add_0_r. apply bi.sep_proper; [done|]. apply big_sepL_proper.
  intros k y _. by rewrite Nat.add_succ_r.
Qed.

Lemma own_take_objs ρ B B' e xs : places_for gobjs B xs B' -> forall pre i st X st1,
  take_objs gobjs st xs i pre = Some st1 -> M guard ge gobjs ρ B st e X ->
  own B X -∗ ∃ X1, ⌜M guard ge gobjs ρ B st1 e X1⌝ ∗ own B X1 ∗ dcobjs_at i B' pre.
Proof using Type.
  intros HP. induction pre as [|[t|] pre IH]; intros i st X st1 Ht HM; cbn [take_objs] in Ht.
  - injection Ht as <-. iIntros "H". iExists X. iFrame. iSplit; [done|]. by rewrite /dcobjs_at.
  - destruct (arg_obj gobjs st xs i) as [o|] eqn:Ea; [|done]. destruct (get_obj st o) as [ob|] eqn:Eg; [|done].
    cbn in Ht. destruct (obj_le st ob t && forallb (aux_global gobjs) (o_aux t)) eqn:Ec; [|done].
    apply andb_prop in Ec as [Hle Hgl].
    destruct (take_one_sound guard ge gobjs ρ B B' st e X xs i t o ob HP HM Ea Eg Hle Hgl)
      as (pl & ys & cs & Hp & Hx & Hp' & Hok & HM1).
    iIntros "H". rewrite (own_take B X o pl ys cs Hp Hx). iDestruct "H" as "[Ho H]".
    iDestruct (IH (Datatypes.S i) _ _ st1 Ht HM1 with "H") as (X1) "(% & H & Hpre)". iExists X1. iFrame "H".
    iSplit; [done|]. rewrite dcobjs_at_cons. iFrame "Hpre". iExists pl, ys, cs. by iFrame.
  - iIntros "H". iDestruct (IH (Datatypes.S i) _ _ st1 Ht HM with "H") as (X1) "(% & H & Hpre)". iExists X1.
    iFrame "H". iSplit; [done|]. rewrite dcobjs_at_cons. by iFrame.
Qed.

Lemma own_give_objs ρ B B' e xs : places_for gobjs B xs B' -> forall post i st X st2,
  give_objs gobjs st xs i post = Some st2 -> M guard ge gobjs ρ B st e X ->
  own B X -∗ dcobjs_at i B' post -∗ ∃ X2, ⌜M guard ge gobjs ρ B st2 e X2⌝ ∗ own B X2.
Proof using Type.
  intros HP. induction post as [|[t|] post IH]; intros i st X st2 Hg HM; cbn [give_objs] in Hg.
  - injection Hg as <-. iIntros "H _". iExists X. by iFrame.
  - destruct (arg_obj gobjs st xs i) as [o|] eqn:Ea; [|done]. cbn beta iota in Hg.
    destruct (Nat.ltb o (length (st_objs st)) && forallb (aux_global gobjs) (o_aux t)) eqn:Ec; [|done].
    apply andb_prop in Ec as [Hlt Hgl]. apply Nat.ltb_lt in Hlt.
    iIntros "H Hpost". rewrite dcobjs_at_cons.
    iDestruct "Hpost" as "[(%pl & %ys & %cs & [%Hp' %Hok] & Ho) Hpost]".
    destruct (give_one_sound guard ge gobjs ρ B B' st e X xs i t o pl ys cs HP HM Ea Hlt Hgl Hp' Hok) as [Hp HM1].
    iPoseProof (own_put B X o pl ys cs Hp with "Ho H") as "H".
    { destruct HM as (_ & _ & _ & _ & _ & (L1 & L2 & _)). lia. }
    iApply (IH (Datatypes.S i) _ _ st2 Hg HM1 with "H Hpost").
  - iIntros "H Hpost". rewrite dcobjs_at_cons. iDestruct "Hpost" as "[_ Hpost]".
    iApply (IH (Datatypes.S i) _ _ st2 Hg HM with "H Hpost").
Qed.

Lemma dcobjs_at_0 B os : dcobjs_at 0 B os ⊣⊢ dcobjs B os.
Proof using Type. done. Qed.

(** A call that matches a specification of the callee runs the callee
    under that specification. The frame keeps the objects that the
    specification does not name, and after the return it owns the
    contents of the checker's next state. *)
Lemma call_core B0 B1 ρ st e X r g xs ws st' :
  M guard ge gobjs ρ (B0 ++ B1) st e X -> Forall (wf_val (length (st_bnd st))) xs ->
  Forall2 (dval ge ρ (B0 ++ B1)) xs ws -> first_spec gobjs r xs st (specs g) = Some st' ->
  exists gf callee, find_fn ge g = Some (Defined gf) /\ call_frame gf ws = Some callee /\
    forall Ψ, ⊢ own (B0 ++ B1) X -∗
      (∀ out e', ⌜returned_env r out e = Some e'⌝ -∗ dst B0 st' e' -∗ Ψ out) -∗
      WP (ERun callee : aexpr) {{ Ψ }}.
Proof using Type* Hspecs.
  intros HM Wx Dx Hf. set (B := B0 ++ B1) in *.
  destruct (first_spec_In gobjs r xs st _ st' Hf) as (sp & Hin & Hc). unfold call_spec in Hc.
  destruct (args_le gobjs st 0 xs (sp_args sp) && implb (sp_guard sp) (st_guard st) && spec_ok gobjs sp) eqn:Ec;
    [|done].
  apply andb_prop in Ec as [Ec Hok]. apply andb_prop in Ec as [Hargs Hg].
  destruct (take_objs gobjs st xs 0 (sp_pre sp)) as [sa|] eqn:Et; [|done].
  destruct (give_objs gobjs sa xs 0 (sp_post sp)) as [sb|] eqn:Eg; [|done].
  pose proof HM as (HB & HG & Hs & _).
  destruct (callee_places_ok ge gobjs B xs HB HG) as (HP & LB' & HB' & HG').
  set (B' := callee_places gobjs B xs) in *.
  assert (Hcargs : Forall2 (dcval ge B') (sp_args sp) ws).
  { apply (args_le_sound guard ge gobjs ρ B B' st xs Hs HP xs (sp_args sp) ws 0%nat);
      [intros k v H; exact H | exact Wx | exact Dx | exact Hargs]. }
  destruct (spec_ok_inv gobjs sp Hok) as (Lpre & _).
  assert (LB : length B' = length (sp_pre sp)).
  { pose proof (Forall2_length Dx) as L1. pose proof (Forall2_length Hcargs) as L2. lia. }
  assert (Hguard : sp_guard sp = true -> guard).
  { intros E. rewrite E in Hg. exact (proj2 (proj2 (proj2 Hs)) Hg). }
  destruct (Hspecs g sp Hin B' ws LB HB' HG' Hcargs Hguard) as (gf & Hfind & [callee Hcf] & Htriple).
  exists gf, callee. split; [done|]. split; [done|]. intros Ψ. iIntros "Hown HK".
  iDestruct (own_take_objs ρ B B' e xs HP _ 0%nat st X sa Et HM with "Hown") as (X1) "(%HM1 & Hown & Hpre)".
  iApply (Htriple callee Ψ Hcf with "[Hpre]"); [by rewrite dcobjs_at_0|].
  iIntros (out) "(%Hret & %Hg' & Hpost)".
  iDestruct (own_give_objs ρ B B' e xs HP _ 0%nat sa X1 sb Eg HM1 with "Hown [Hpost]") as (X2) "[%HM2 Hown]";
    [by rewrite dcobjs_at_0|].
  assert (HM3 : M guard ge gobjs ρ B (set_guard sb (st_guard sb || sp_guard' sp)) e X2).
  { apply M_set_guard; [exact HM2|]. intros E. apply orb_prop in E as [E|E]; [|exact (Hg' E)].
    exact (proj2 (proj2 (proj2 (M_sat guard ge gobjs ρ B sb e X2 HM2))) E). }
  destruct (bind_result_sound guard ge gobjs ρ B B' _ e X2 xs r (sp_ret sp) out st' HP HM3 Hret Hc)
    as (e' & ρ' & He' & HM').
  iApply ("HK" $! out e' with "[//]"). by iApply (dst_intro _ _ ρ' with "Hown").
Qed.

Lemma wp_abs_call B0 r g args st st' f e l rest j Φ :
  acall builtin gobjs fnames specs r g args st = Some st' ->
  dst B0 st e -∗
  ▷ (∀ e', dst B0 st' e' -∗ WP (ERun (mkFrame f e' [] None (Exec l rest j)) : aexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e [] None (Exec l (Call r (Global g) args :: rest) j)) : aexpr) {{ Φ }}.
Proof using Type* Hfn Hbuiltin Hspecs.
  rewrite /acall. intros Ha.
  destruct (avalues gobjs fnames (arg_classes args) (arg_values args) st) as [[xs st1]|] eqn:Ev; [|done].
  iIntros "(%B & %X & [[%B1 ->] (%ρ & %HM & _ & _)] & Hown) HK".
  destruct (avalues_sound guard ge gobjs fnames Hfn ρ _ st e X _ _ xs st1 HM Ev)
    as (ws & Hws & ρ1 & HM1 & _ & Wx & Dx).
  rewrite -args_x_split in Hws.
  destruct (builtin g r (arg_classes args) xs st1) as [res|] eqn:Eb.
  - subst res. iApply (Hbuiltin B0 g r xs st1 st' f e l args rest j ws Φ Eb Hws with "[Hown] HK").
    iExists (B0 ++ B1), X. iFrame. iPureIntro. split; [by exists B1|]. by exists ρ1.
  - destruct (call_core B0 B1 ρ1 st1 e X r g xs ws st' HM1 Wx Dx Ha) as (gf & callee & Hfind & Hcf & Hcore).
    iApply (wp_call_bind registry wi ge f e [] l r g args rest j ws gf callee with "[Hown HK]"); [done | done | done |].
    iNext. iApply (Hcore with "Hown"). iIntros (out e' Hret) "Hd". iExists _. iSplit.
    + iPureIntro. rewrite /resume. cbn. rewrite Hret. done.
    + iNext. iApply ("HK" with "Hd").
Qed.

(** An indirect call goes to a function whose name the checker knows,
    with arguments of the classes that the function declares, so the
    machine converts nothing and the call is like a direct one. *)
Lemma wp_abs_raw_call B0 r callee args st st' f e l rest j Φ :
  ainst (RawCall r callee args) st = Some st' ->
  dst B0 st e -∗
  ▷ (∀ e', dst B0 st' e' -∗ WP (ERun (mkFrame f e' [] None (Exec l rest j)) : aexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e [] None (Exec l (RawCall r callee args :: rest) j)) : aexpr) {{ Φ }}.
Proof using Type* Hfn Hspecs.
  cbn [AbsRun.ainst]. intros Ha.
  destruct (avalue gobjs fnames F callee st) as [[c st1]|] eqn:Ec; [|done].
  destruct c as [| | | | | |g]; try done.
  destruct (lookup g fnames) as [[ks rt]|] eqn:El; [|done]. cbn [fst snd] in Ha.
  destruct (all2 class_eqb (arg_classes args) ks && forallb class_plain ks
            && same_words (result_words r) (return_words rt)) eqn:Ek; [|done].
  apply andb_prop in Ek as [Ek Hw]. apply andb_prop in Ek as [Hc Hp].
  destruct (avalues gobjs fnames (arg_classes args) (arg_values args) st1) as [[xs st2]|] eqn:Ev; [|done].
  iIntros "(%B & %X & [[%B1 ->] (%ρ & %HM & _ & _)] & Hown) HK".
  destruct (avalue_sound guard ge gobjs fnames Hfn ρ _ st e X F callee _ st1 HM Ec)
    as (wc & Hwc & ρ1 & HM1 & _ & _ & Dc).
  destruct Dc as (p & -> & Hlk & Hcap).
  destruct (avalues_sound guard ge gobjs fnames Hfn ρ1 _ st1 e X _ _ xs st2 HM1 Ev)
    as (ws & Hws & ρ2 & HM2 & _ & Wx & Dx).
  rewrite -args_x_split in Hws.
  destruct (call_core B0 B1 ρ2 st2 e X r g xs ws st' HM2 Wx Dx Ha) as (gf & fr & Hfind & Hcf & Hcore).
  destruct (Hfn g ks rt El) as [_ Hsig]. destruct (Hsig gf Hfind) as (Hks & Hrt & Hvar). subst ks rt.
  iApply (wp_raw_call_bind registry wi ge f e [] l r callee args rest j p g ws gf ws None fr with "[Hown HK]").
  - exact Hwc.
  - exact Hcap.
  - exact (fn_check ge g p Hlk Hcap).
  - exact Hws.
  - exact Hfind.
  - exact (conv_same ge gf r args ws e Hc Hp Hw Hws).
  - rewrite Hvar app_nil_r. exact Hcf.
  - iNext. iApply (Hcore with "Hown"). iIntros (out e' Hret) "Hd". iExists _. iSplit.
    + iPureIntro. rewrite /resume. cbn. rewrite Hret. done.
    + iNext. iApply ("HK" with "Hd").
Qed.

(** Every instruction that the checker accepts is one of the kinds
    above, so one rule covers a step of the checker. *)
Lemma wp_abs_inst B0 i st st' f e l rest j Φ :
  ainst i st = Some st' ->
  dst B0 st e -∗
  ▷ (∀ e', dst B0 st' e' -∗ WP (ERun (mkFrame f e' [] None (Exec l rest j)) : aexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e [] None (Exec l (i :: rest) j)) : aexpr) {{ Φ }}.
Proof using Type* Hfn Hbuiltin Hspecs.
  intros Ha. destruct (reads i) eqn:Er; [by apply wp_abs_read|].
  destruct (is_store i) eqn:Es; [by apply wp_abs_write|].
  destruct i; try discriminate Er; try discriminate Es; try discriminate Ha.
  - destruct o; try discriminate Er. by apply wp_abs_alloc.
  - destruct callee; try discriminate Ha. by apply wp_abs_call.
  - by apply wp_abs_raw_call.
Qed.

(** The instructions of a block run one after another, each from the
    state that the checker reached before it. *)
Lemma wp_abs_insts B0 f l j Φ : forall ins st st1 last e,
  ainsts builtin gobjs fnames specs ins st = (Some st1, last) ->
  dst B0 st e -∗
  (∀ e', dst B0 st1 e' -∗ WP (ERun (mkFrame f e' [] None (Exec l [] j)) : aexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e [] None (Exec l ins j)) : aexpr) {{ Φ }}.
Proof using Type* Hfn Hbuiltin Hspecs.
  induction ins as [|i ins IH]; intros st st1 last e Ha; cbn [ainsts] in Ha.
  - injection Ha as <- _. iIntros "Hd HK". iApply ("HK" with "Hd").
  - destruct (ainst i st) as [st2|] eqn:Ei; [|done]. iIntros "Hd HK".
    iApply (wp_abs_inst B0 i st st2 with "Hd"); [exact Ei|]. iNext. iIntros (e') "Hd".
    iApply (IH st2 st1 last e' Ha with "Hd HK").
Qed.

(** * Objects of a specification

    A specification's objects are owned one by one, and the contents
    of a state are owned as one list of pieces. The two lemmas below
    go between the two forms, at the entry of a function and at its
    return. *)
Lemma own_dcobjs_at B B0 : forall post i0 X,
  (forall k t, nth_error post k = Some (Some t) ->
     exists pl xs cs, nth_error B (i0 + k) = Some pl /\ nth_error B0 (i0 + k) = Some pl /\
       nth_error X (i0 + k) = Some (Some (xs, cs)) /\ obj_ok guard (fun _ => 0) B0 pl (open_obj t) xs cs) ->
  own B X -∗ dcobjs_at i0 B0 post.
Proof using Type.
  induction post as [|o post IH]; intros i0 X H; iIntros "Hown"; [by rewrite /dcobjs_at|].
  rewrite dcobjs_at_cons.
  assert (Hrest : forall X', (forall i, i <> i0 -> nth_error X' i = nth_error X i) ->
            forall k t, nth_error post k = Some (Some t) ->
              exists pl xs cs, nth_error B (Datatypes.S i0 + k) = Some pl /\ nth_error B0 (Datatypes.S i0 + k) = Some pl /\
                nth_error X' (Datatypes.S i0 + k) = Some (Some (xs, cs)) /\
                obj_ok guard (fun _ => 0) B0 pl (open_obj t) xs cs).
  { intros X' HX' k t Hk. destruct (H (Datatypes.S k) t Hk) as (pl & xs & cs & H1 & H2 & H3 & H4).
    rewrite Nat.add_succ_r in H1 H2 H3. exists pl, xs, cs. rewrite HX'; [done | lia]. }
  destruct o as [t|].
  - destruct (H 0%nat t eq_refl) as (pl & xs & cs & Hp & Hp0 & Hx & Hok). rewrite Nat.add_0_r in Hp Hp0 Hx.
    rewrite (own_take B X i0 pl xs cs Hp Hx). iDestruct "Hown" as "[Ho Hown]". iSplitL "Ho".
    + iExists pl, xs, cs. by iFrame.
    + iApply (IH (Datatypes.S i0) with "Hown"). apply Hrest. intros i Hi.
      rewrite nth_error_list_set. by rewrite (proj2 (Nat.eqb_neq i i0) Hi).
  - iSplit; [done|]. iApply (IH (Datatypes.S i0) with "Hown"). by apply Hrest.
Qed.

Lemma dcobjs_at_own B0 : forall pre Bs i0,
  length Bs = length pre -> (forall k, (k < length pre)%nat -> nth_error Bs k = nth_error B0 (i0 + k)) ->
  dcobjs_at i0 B0 pre -∗
  ∃ X, ⌜length X = length pre /\ forall k t, nth_error pre k = Some (Some t) ->
          exists pl xs cs, nth_error Bs k = Some pl /\ nth_error X k = Some (Some (xs, cs)) /\
            obj_ok guard (fun _ => 0) B0 pl (open_obj t) xs cs⌝ ∗ own Bs X.
Proof using Type.
  induction pre as [|o pre IH]; intros [|pl0 Bs] i0 HL Hnth; try discriminate.
  - iIntros "_". iExists []. iSplit; [|by rewrite /own /pts]. iPureIntro. split; [done|]. by intros [|k] t Hk.
  - rewrite dcobjs_at_cons. iIntros "[Ho Hpre]". injection HL as HL.
    iDestruct (IH Bs (Datatypes.S i0) HL with "Hpre") as (X) "[[%LX %HX] Hown]".
    { intros k Hk. pose proof (Hnth (Datatypes.S k)) as E. rewrite Nat.add_succ_r in E. apply E. cbn [length]. lia. }
    destruct o as [t|].
    + iDestruct "Ho" as (pl xs cs) "[[%Hp %Hok] Ho]".
      pose proof (Hnth 0%nat ltac:(cbn [length]; lia)) as E. rewrite Nat.add_0_r Hp in E. injection E as ->.
      iExists (Some (xs, cs) :: X). iSplit.
      * iPureIntro. split; [cbn [length]; lia|]. intros [|k] t' Hk; [|exact (HX k t' Hk)].
        injection Hk as <-. by exists pl, xs, cs.
      * rewrite /own. cbn [all_ps]. rewrite pts_app. iFrame.
    + iExists (None :: X). iSplit; [|done]. iPureIntro. split; [cbn [length]; lia|].
      intros [|k] t' Hk; [done | exact (HX k t' Hk)].
Qed.

(** * Blocks and cut points

    A function returns with the postcondition of its specification:
    the result is one that the specification describes, the guard
    holds if the specification promises it, and the objects of the
    postcondition are owned at the caller's places. *)
Definition post (B0 : list place) (sp : fspec) : outcome -> iProp Σ :=
  fun out => (⌜dret ge B0 (sp_ret sp) out⌝ ∗ ⌜sp_guard' sp = true -> guard⌝ ∗ dcobjs B0 (sp_post sp))%I.

(** Every cut invariant is a triple for the block it belongs to. From
    any frame that the opened invariant describes, the block runs
    without a panic and the function returns with its postcondition. *)
Definition cuts_hold (f : func) (B0 : list place) (sp : fspec) (inv : list (name * cstate)) : iProp Σ :=
  (□ ∀ l t b e, ⌜In (l, t) inv /\ find_block l (fn_blocks f) = Some b⌝ -∗ dst B0 (open_state t) e -∗
       WP (ERun (mkFrame f e [] None (Exec l (b_insts b) (b_jump b))) : aexpr) {{ post B0 sp }})%I.

(** A state that is true of the first places and contents of a frame
    describes the frame, and the objects beyond them are given up. *)
Lemma dst_cut B0 B1 ρ st e X n :
  (length B0 <= n)%nat -> M guard ge gobjs ρ (firstn n (B0 ++ B1)) st e (firstn n X) ->
  own (B0 ++ B1) X -∗ dst B0 st e.
Proof using Type.
  intros Hn HM. iIntros "Hown". iExists (firstn n (B0 ++ B1)), (firstn n X). iSplit.
  { iPureIntro. split; [|exists ρ; split; [exact HM | split; constructor]].
    exists (firstn (n - length B0) B1). rewrite firstn_app firstn_all2; [done | lia]. }
  rewrite /own (all_ps_firstn n (B0 ++ B1) X) pts_app. iDestruct "Hown" as "[$ _]".
Qed.

Lemma post_objs B0 B1 X sp :
  (forall i t, nth_error (sp_post sp) i = Some (Some t) ->
     exists pl xs cs, nth_error B0 i = Some pl /\ nth_error X i = Some (Some (xs, cs)) /\
                      obj_ok guard (fun _ => 0) B0 pl (open_obj t) xs cs) ->
  own (B0 ++ B1) X -∗ dcobjs B0 (sp_post sp).
Proof using Type.
  intros H. rewrite -dcobjs_at_0. apply own_dcobjs_at. intros k t Hk.
  destruct (H k t Hk) as (pl & xs & cs & H1 & H2 & H3). exists pl, xs, cs. cbn [Nat.add].
  split; [|done]. rewrite nth_error_app1; [done|]. apply nth_error_Some. congruence.
Qed.

Lemma run_no_blocks f cuts fuel l from st sp inv :
  fn_blocks f = [] -> forallb (leaf_ok sp inv) (run builtin gobjs fnames specs f cuts fuel l from st) = false.
Proof using Type. intros E. destruct fuel; cbn [run]; [done|]. rewrite E. done. Qed.

(** The checker explores every path through a function. A path ends
    when the function returns or when a loop comes back to its head.
    The lemma below says that the real machine stays on the paths the
    checker explored. If the checker accepted the end of every path,
    then the machine either returns a result that the specification
    allows or arrives at a loop head in a state that the loop's
    invariant allows. *)
Lemma run_body_sound f cuts sp inv B0 :
  spec_ok gobjs sp = true -> length B0 = length (sp_pre sp) ->
  length (sp_args sp) = length (fn_params f) ->
  forallb (fun lt => cstate_ok (nglob gobjs + length (fn_params f)) (snd lt)) inv = true ->
  forall fuel,
  (forall l from st e,
     forallb (leaf_ok sp inv) (run builtin gobjs fnames specs f cuts fuel l from st) = true ->
     dst B0 st e -∗ ▷ cuts_hold f B0 sp inv -∗
     WP (ERun (mkFrame f e [] None (Enter l from)) : aexpr) {{ post B0 sp }}) /\
  (forall l ins j st e,
     forallb (leaf_ok sp inv) (body builtin gobjs fnames specs f cuts fuel l ins j st) = true ->
     dst B0 st e -∗ ▷ cuts_hold f B0 sp inv -∗
     WP (ERun (mkFrame f e [] None (Exec l ins j)) : aexpr) {{ post B0 sp }}).
Proof using Type* Hfn Hbuiltin Hspecs.
  intros Hok LB0 Hlen Hcs. destruct (spec_ok_inv gobjs sp Hok) as (Lpre & _).
  induction fuel as [|fuel [IHrun IHbody]]; [split; intros; discriminate|]. split.
  - intros l from st e. cbn [run].
    destruct (find_block l (fn_blocks f)) as [b|] eqn:Eb; [|discriminate].
    destruct (aphis gobjs fnames (b_phis b) from st) as [st1|] eqn:Ep; [|discriminate].
    intros Hl. iIntros "(%B & %X & [[%B1 ->] (%ρ & %HM & _ & _)] & Hown) #HC".
    destruct (aphis_sound guard ge gobjs fnames Hfn ρ _ st e X _ from st1 HM Ep) as (e' & ρ' & He' & HM').
    iApply (wp_enter registry wi ge f e [] l from b e' with "[Hown]"); [exact Eb | exact He' |]. iNext.
    destruct (mem_name l cuts && match from with Some _ => true | None => false end).
    + cbn [forallb leaf_ok] in Hl. apply andb_prop in Hl as [Hl _].
      apply existsb_exists in Hl as ([l' t] & Hin & Hc). cbn [fst snd] in Hc.
      apply andb_prop in Hc as [Hn Hent]. apply term_eqb_eq in Hn. subst l'.
      rewrite forallb_forall in Hcs. pose proof (Hcs _ Hin) as Hct. cbn [snd] in Hct.
      pose proof (entails_sound guard ge gobjs ρ' (B0 ++ B1) st1 e' X t _ HM' Hent Hct ltac:(lia)) as Hes.
      cbn zeta in Hes. destruct Hes as [Hn (ρ2 & HM2)].
      iApply ("HC" $! l t b e' with "[%]"); [done|].
      iApply (dst_cut B0 B1 ρ2 _ e' X (length (cs_objs t)) with "Hown"); [lia | exact HM2].
    + iApply (IHbody l _ _ st1 e' Hl with "[Hown] HC"). by iApply (dst_intro with "Hown").
  - intros l ins j st e. cbn [body].
    destruct (ainsts builtin gobjs fnames specs ins st) as [[st1|] last] eqn:Ea; [|discriminate].
    intros Hl. iIntros "Hd #HC". iApply (wp_abs_insts B0 f l j _ ins st st1 last e Ea with "Hd").
    iIntros (e1) "(%B & %X & [[%B1 ->] (%ρ & %HM & _ & _)] & Hown)".
    destruct j as [t|v t1 t2|v|vs| |]; try discriminate Hl.
    + iApply (wp_goto registry wi ge f e1 [] l t). iNext.
      iApply (IHrun _ _ st1 e1 Hl with "[Hown] HC"). by iApply (dst_intro with "Hown").
    + destruct (avalue gobjs fnames W v st1) as [[x st2]|] eqn:Ev; [|discriminate].
      destruct (abranch x st2) as [[yes no]|] eqn:Eb; [|discriminate].
      rewrite forallb_app in Hl. apply andb_prop in Hl as [Hy Hno].
      destruct (abranch_sound guard ge gobjs fnames Hfn ρ _ st1 e1 X v x st2 yes no HM Ev Eb)
        as (n & Hv & Hnz & Hz).
      iApply (wp_branch registry wi ge f e1 [] l v t1 t2 n); [exact Hv|]. iNext.
      destruct (Z.eqb_spec n 0) as [E|E].
      * destruct (Hz E) as (s & ρ' & -> & HMs).
        iApply (IHrun _ _ s e1 Hno with "[Hown] HC"). by iApply (dst_intro with "Hown").
      * destruct (Hnz E) as (s & ρ' & -> & HMs).
        iApply (IHrun _ _ s e1 Hy with "[Hown] HC"). by iApply (dst_intro with "Hown").
    + destruct (fn_ret f) as [k| |] eqn:Er; try discriminate.
      destruct (avalue gobjs fnames k v st1) as [[x st2]|] eqn:Ev; [|discriminate].
      cbn [forallb leaf_ok] in Hl. apply andb_prop in Hl as [Hl _].
      destruct (avalue_sound guard ge gobjs fnames Hfn ρ _ st1 e1 X k v x st2 HM Ev)
        as (w & Hw & ρ' & HM' & _ & Wx & Dx).
      destruct (ret_ok_sound guard ge gobjs ρ' B0 B1 st2 e1 X sp (Some x) HM' Hok LB0 Hl) as (Hr & Hg & Hpost).
      destruct (sp_ret sp) as [c|] eqn:Es; [|done].
      iApply (wp_ret registry wi ge f e1 l v k w); [exact Er | exact Hw|]. iNext.
      iSplit; [iPureIntro; rewrite Es; exists w; split; [done | exact (Hr w Wx Dx)]|].
      iSplit; [done|]. by iApply (post_objs with "Hown").
    + cbn [forallb leaf_ok] in Hl. apply andb_prop in Hl as [Hl _].
      destruct (ret_ok_sound guard ge gobjs ρ B0 B1 st1 e1 X sp None HM Hok LB0 Hl) as (Hr & Hg & Hpost).
      destruct (sp_ret sp) as [c|] eqn:Es; [done|].
      iApply (wp_ret_void registry wi ge f e1 l). iNext.
      iSplit; [iPureIntro; by rewrite Es|]. iSplit; [done|]. by iApply (post_objs with "Hown").
Qed.

(** * The function

    A function that the checker accepts is safe to call. The call
    starts in a state that the specification allows, so every path
    from the entry is safe. A path that reaches a loop goes around
    the loop, and the loop may run any number of times. The proof
    covers that by induction on the steps of the machine: at least
    one step is taken on each pass around the loop, so the invariant
    of the loop may be assumed for the next pass. *)
Lemma verify_sound_in g f sp inv cuts fuel :
  find_fn ge g = Some (Defined f) -> verify builtin gobjs fnames specs f cuts fuel sp inv = true ->
  spec_holds g sp.
Proof using Type* Hfn Hbuiltin Hspecs.
  intros Hf Hv. unfold verify in Hv.
  apply andb_prop in Hv as [Hv Hcuts]. apply andb_prop in Hv as [Hv Hentry]. apply andb_prop in Hv as [Hv Hcs].
  apply andb_prop in Hv as [Hv Hlen]. apply andb_prop in Hv as [Hv Hok]. apply andb_prop in Hv as [Hloc Hvar].
  apply Nat.eqb_eq in Hlen. apply negb_true_iff in Hvar. unfold run_entry in Hentry.
  destruct (local_objects f) eqn:Eloc; [|discriminate]. clear Hloc.
  assert (Hblocks : fn_blocks f <> []).
  { intros E. rewrite run_no_blocks in Hentry; done. }
  intros B ws LB HB HG Hargs Hg. exists f. split; [exact Hf|].
  pose proof (Forall2_length Hargs) as Lws.
  pose proof (call_frame_entry f ws Eloc Hvar ltac:(lia) Hblocks) as Hcf.
  split; [rewrite Hcf; eauto|]. intros fr Φ Hfr. rewrite Hcf in Hfr. injection Hfr as <-.
  iIntros "Hpre HΦ".
  iApply (wp_wand _ _ _ (post B sp) with "[Hpre]"); [|iIntros (out) "H"; iApply ("HΦ" with "H")].
  iDestruct (dcobjs_at_own B (sp_pre sp) B 0%nat with "[Hpre]") as (X) "[[%LX %HX] Hown]";
    [done | done | by rewrite dcobjs_at_0 |].
  destruct (entry_sound guard ge gobjs B X f sp ws Hok Hlen LB ltac:(lia) HB HG Hargs Hg HX) as (ρ & HM).
  destruct (run_body_sound f cuts sp inv B Hok LB Hlen Hcs fuel) as [Hrun Hbody].
  iApply (Hrun _ None _ _ Hentry with "[Hown]").
  - iApply (dst_intro B [] ρ with "[Hown]"); rewrite app_nil_r; [exact HM | done].
  - iNext. iLöb as "IH". iEval (rewrite /cuts_hold). iModIntro. iIntros (l t b e [Hin Hb]) "Hd".
    rewrite forallb_forall in Hcuts. pose proof (Hcuts _ Hin) as Hc. cbn [fst snd] in Hc.
    unfold run_cut in Hc. rewrite Hb in Hc. iApply (Hbody l _ _ _ e Hc with "Hd IH").
Qed.

End proof.

(** * The theorem *)

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

Theorem verify_sound : verify_sound_statement.
Proof using Type*.
  intros g f sp inv cuts fuel Hf Hv Hfn Hb Hs. exact (verify_sound_in Hfn Hb Hs g f sp inv cuts fuel Hf Hv).
Qed.

End sound.
End AbsSoundOn.
