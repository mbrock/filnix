(** A library proof needs to know which function each call runs and
    which OS world its execution preserves. These declarations collect
    that information without changing the interpreter's [[weakest-precondition]]. *)

From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import weakestpre.
From Stdlib Require Import String List.
From Nanofil Require Import Term Syntax Values Memory Semantics Pieces Heap ExternalCalls Runtime Logic.
From Glibc Require Export Fix OsWorld.
Import Fix.LG0 Fix.LG0.L.

(** A named call must resolve to the function whose rule the proof uses. *)
Class Defines (ge : genv) (n : string) (f : func) : Prop :=
  defines : find_fn ge (TAtom n) = Some (Defined f).
#[global] Hint Mode Defines + + - : typeclass_instances.
#[global] Hint Extern 0 (Defines _ _ _) => assumption : typeclass_instances.

(** Caller and callee must agree on the OS state and the meaning of memory
    ownership. This record keeps their program data and [[ghost-state]]
    together, so the execution rules use the same interpretation. *)
Class GlibcProgram {hlc : has_lc} (Σ : gFunctors) := {
  program_world : os_world;
  program_registry : name -> option (contract os_world);
  program_ge : genv;
  program_inv : invGS_gen hlc Σ;
  program_heap : gen_heapGS piece pval Σ
}.
#[global] Existing Instance program_inv.
#[global] Existing Instance program_heap.

(** An old-style caller can package its existing state without adding a premise. *)
Definition program_of `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}
    (w : os_world) (r : name -> option (contract os_world)) (g : genv) :
    GlibcProgram (hlc := hlc) Σ :=
  {| program_world := w; program_registry := r; program_ge := g;
     program_inv := _; program_heap := _ |}.

(** Rules use these short names while sharing the section's program bundle. *)
Module ProgramAbbreviations.
  Notation w0 := program_world.
  Notation registry := program_registry.
  Notation ge := program_ge.
End ProgramAbbreviations.

(** Execution uses the canonical interpretation for the bundled OS world. *)
Definition program_irisGS `{!GlibcProgram (hlc := hlc) Σ} :
    irisGS_gen hlc (nanofil_lang program_registry program_ge) Σ :=
  nanofil_irisGS program_registry (os_wi program_world) program_ge.

#[global] Hint Extern 10 (irisGS_gen ?hlc _ ?Σ) =>
  let P := constr:(ltac:(typeclasses eauto) : GlibcProgram (hlc := hlc) Σ) in
  exact (@program_irisGS hlc Σ P) : typeclass_instances.

(** An existing caller keeps its ordinary world expressions when it uses a
    bundled rule. Reducing the projections avoids changing arithmetic and
    symbolic-execution tactics that inspect those expressions. *)
Notation "'program_call' '(' rule ')'" :=
  (ltac:(let proof := constr:(rule) in
         let T := type of proof in
         let T' := eval cbn [program_of program_world program_registry program_ge
                            program_irisGS program_inv program_heap] in T in
         exact (let result : T' := proof in result)))
  (at level 0, rule at level 200, only parsing).

(** A computed table supplies individual lookup facts without recomputing
    the linked program for every named function. *)
Lemma defines_from_table ge table n f :
  List.Forall (fun '(n, f) => find_fn ge (TAtom n) = Some (Defined f)) table ->
  List.In (n, f) table -> Defines ge n f.
Proof.
  intros H Hin. apply List.Forall_forall with (x := (n, f)) in H; assumption.
Qed.

(** A row number selects a lookup proof without searching through other rows. *)
Lemma defines_from_table_nth ge table i n f :
  List.Forall (fun '(n, f) => find_fn ge (TAtom n) = Some (Defined f)) table ->
  List.nth_error table i = Some (n, f) -> Defines ge n f.
Proof.
  intros H Hnth. eapply defines_from_table; [exact H |].
  eapply List.nth_error_In. exact Hnth.
Qed.

(** A linked program publishes one table whose rows have all been checked. *)
Class ProgramTable (ge : genv) := {
  program_table : list (string * func);
  program_table_correct :
    List.Forall (fun '(n, f) => find_fn ge (TAtom n) = Some (Defined f)) program_table
}.
#[global] Hint Mode ProgramTable + : typeclass_instances.

(** Equality of the lookup and expected-result lists proves every table row.
    The equality can be checked by the virtual machine in one conversion. *)
Lemma defines_table_of_map ge table :
  List.map (fun '(n, _) => find_fn ge (TAtom n)) table =
  List.map (fun '(_, f) => Some (Defined f)) table ->
  List.Forall (fun '(n, f) => find_fn ge (TAtom n) = Some (Defined f)) table.
Proof.
  induction table as [|[n f] table IH]; cbn; intros H; constructor.
  - injection H; auto.
  - apply IH. injection H; auto.
Qed.
