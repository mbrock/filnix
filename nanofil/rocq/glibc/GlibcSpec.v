(** A caller should use a function's contract without rebuilding its call
    frame. These rules connect named contracts to the [[weakest-precondition]]
    of a call and preserve the caller's continuation. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Glibc Require Import GlibcProgram.
From Nanofil Require Import Term Syntax Values Memory Semantics Pieces Heap ExternalCalls Runtime Logic.
Import Fix.LG0 Fix.LG0.L.

(** A contract groups the logical inputs with their arguments and owned memory.
    Its postcondition describes both the outcome and the memory returned. *)
Record fspec (Σ : gFunctors) := FSpec {
  fs_binder : Type;
  fs_args : fs_binder -> list word;
  fs_pre : fs_binder -> iProp Σ;
  fs_post : fs_binder -> outcome -> iProp Σ
}.
Arguments FSpec {_} _ _ _ _.
Arguments fs_binder {_} _.
Arguments fs_args {_} _ _.
Arguments fs_pre {_} _ _.
Arguments fs_post {_} _ _ _.

(** A function can accept either of two ownership layouts without weakening
    the result promised for either layout. The logical input selects the layout. *)
Definition spec_choice {Σ} (s t : fspec Σ) : fspec Σ :=
  FSpec (fs_binder s + fs_binder t)
    (fun x => match x with inl a => fs_args s a | inr b => fs_args t b end)
    (fun x => match x with inl a => fs_pre s a | inr b => fs_pre t b end)
    (fun x => match x with inl a => fs_post s a | inr b => fs_post t b end).

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context {world : Type} (registry : name -> option (contract world))
  (wi : mem -> world -> gmap piece pval -> Prop) `{!SafepointStable wi} (ge : genv).
Local Instance spec_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry wi ge.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** A function triple includes lookup and argument binding, so a caller
    needs no knowledge of the callee's entry block. *)
Definition fn_triple (g : name) (xs : list word) (P : iProp Σ)
    (Q : outcome -> iProp Σ) : Prop :=
  exists gf, find_fn ge g = Some (Defined gf) /\ is_Some (call_frame gf xs) /\
    forall fr Φ, call_frame gf xs = Some fr ->
      ⊢ P -∗ (∀ r, Q r -∗ Φ r) -∗ WP (ERun fr : gexpr) {{ Φ }}.

(** Proof search selects a contract by the name used at the call site. *)
Class HasSpec (n : name) (s : fspec Σ) : Prop :=
  has_spec : forall x, fn_triple n (fs_args s x) (fs_pre s x) (fs_post s x).
#[global] Hint Mode HasSpec + - : typeclass_instances.

(** The caller resumes with the outcome and resources supplied by its contract. *)
Lemma wp_call_spec n s `{!HasSpec n s} x f e ls lab r args rest j Ψ :
  map_option (arg_x ge e) args = Some (fs_args s x) ->
  fs_pre s x -∗
  (∀ v, fs_post s x v -∗ ∃ cf',
    ⌜resume (mkFrame f e ls None (Exec lab rest j)) (mkPending r None) v = Some cf'⌝ ∗
    ▷ WP (ERun cf' : gexpr) {{ Ψ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec lab (Call r (Global n) args :: rest) j)) : gexpr) {{ Ψ }}.
Proof.
  intros Hx. destruct (has_spec (n := n) (s := s) x) as (gf & Hg & [fr Hfr] & Ht).
  iIntros "HP HK".
  iApply (wp_call_bind with "[HP HK]"); [exact Hx | exact Hg | exact Hfr |]. iNext.
  iApply (Ht fr _ Hfr with "HP"). iIntros (v) "HQ". iApply ("HK" with "HQ").
Qed.

(** A caller can forget guarantees or provide stronger resources without
    reproving execution of the function. *)
Lemma has_spec_weaken n s s' `{!HasSpec n s} :
  (forall y, exists x, fs_args s' y = fs_args s x /\
    (fs_pre s' y ⊢ fs_pre s x ∗ ∀ v, fs_post s x v -∗ fs_post s' y v)) ->
  HasSpec n s'.
Proof.
  intros Hweak y. destruct (Hweak y) as (x & Hargs & Hpre).
  destruct (has_spec (n := n) (s := s) x) as (gf & Hg & Hfr & Ht).
  exists gf. rewrite Hargs. split; [exact Hg |]. split; [exact Hfr |].
  intros fr Φ Hcall. iIntros "HP HK". iDestruct (Hpre with "HP") as "[HP HW]".
  iApply (Ht fr Φ Hcall with "HP"). iIntros (v) "HQ".
  iApply "HK". iApply ("HW" with "HQ").
Qed.

(** Combining proved contracts preserves each alternative's original guarantees. *)
Lemma has_spec_choice n s t `{!HasSpec n s, !HasSpec n t} :
  HasSpec n (spec_choice s t).
Proof.
  intros [x|y]; cbn [fs_args fs_pre fs_post spec_choice].
  - apply (has_spec (s := s)).
  - apply (has_spec (s := t)).
Qed.
End rules.

(** A caller already knows which runtime contracts are linked.
    Only call-spec search uses those ordinary facts as premises. *)
#[global] Hint Extern 0 => assumption : call_specs.

(** Product binders expose argument words while leaving logical inputs for framing. *)
Ltac spec_inputs T :=
  let T' := eval hnf in T in
  lazymatch T' with
  | prod ?A ?B =>
      let a := spec_inputs A in let b := spec_inputs B in constr:((a, b))
  | _ => open_constr:(_ : T)
  end.

(** A bundled caller selects its named contract, supplies owned memory, and
    receives the outcome together with the contract's postcondition. *)
Ltac call_spec_rule :=
  lazymatch goal with
  | P : @GlibcProgram ?hlc ?Σ |-
      context [mkFrame ?f ?e ?ls None (Exec ?lab (Call ?r (Global ?n) ?args :: ?rest) ?j)] =>
      let s := open_constr:(_ : fspec Σ) in
      let H := constr:(ltac:(typeclasses eauto with typeclass_instances call_specs) :
        HasSpec (@program_registry hlc Σ P) (os_wi (@program_world hlc Σ P))
          (@program_ge hlc Σ P) n s) in
      open_constr:(fun x => wp_call_spec (@program_registry hlc Σ P) (os_wi (@program_world hlc Σ P))
        (@program_ge hlc Σ P) n s (HasSpec0 := H) x f e ls lab r args rest j _)
  end.

(** Passing large generated proofs directly to Iris makes calls slow.
    Local proof names avoid that search, while unsolved argument equations and arithmetic premises remain visible. *)
Ltac call_spec_apply rule x :=
  let T := type of (rule x) in
  lazymatch T with
  | ?E -> _ =>
      let Hargs := fresh "Hargs" in assert (Hargs : E);
      [ cbn -[put]; try first [reflexivity | eassumption]
      | let T := type of (rule x Hargs) in
        lazymatch T with
        | ⊢ ?P -∗ ?K -∗ ?Q =>
            let Hcall := fresh "Hcall" in
            pose proof (rule x Hargs) as Hcall;
            let Happly := fresh "Happly" in
            pose proof (bi.wand_elim_r' P K Q
              ltac:(iIntros "HK HP"; iApply (Hcall with "HP HK"))) as Happly;
            iApply Happly; clear Hcall Happly;
            cbn [fs_pre]; iFrame;
            first [iSplitR; [iPureIntro | let v := fresh "v" in iIntros (v) "Hpost"]
                  | let v := fresh "v" in iIntros (v) "Hpost"]
        end ]
  end.

(** Ordinary calls infer their logical inputs from arguments and owned memory. *)
Ltac call_spec :=
  let rule := call_spec_rule in
  let T := type of rule in
  lazymatch T with
  | forall x : ?B, _ =>
      let B' := eval hnf in B in
      lazymatch B' with
      | sum ?A ?C =>
          first [let a := spec_inputs A in let x := open_constr:(inl a) in call_spec_apply rule x
                | let c := spec_inputs C in let x := open_constr:(inr c) in call_spec_apply rule x]
      | _ => let x := spec_inputs B in call_spec_apply rule x
      end
  end.

(** A caller can supply an arithmetic decomposition that argument evaluation cannot infer. *)
Tactic Notation "call_spec" "with" open_constr(x) :=
  let rule := call_spec_rule in call_spec_apply rule x.
