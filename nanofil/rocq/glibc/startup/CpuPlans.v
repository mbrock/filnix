(** CPU feature discovery infers a specification and loop invariants for each
    call. Callers need only the specification. The proofs compare it with
    the inferred one and check the invariants before exporting the call rule. *)

From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import weakestpre.
From Stdlib Require Import String List.
From Nanofil Require Import Term Semantics Pieces Heap AbsRun.
From Glibc Require Import OsWorld OsCpuid CpuSetup CpuSound.

(** A completed call gives back the listed objects and may return a value. *)
Definition cpu_result (sp : fspec) post ret : fspec :=
  mkSpec (sp_args sp) (sp_pre sp) (sp_guard sp) post false ret.

(** A call that changes one global gives back its new contents in the same
    slot. The other globals and the caller’s parameters keep their bounds. *)
Definition post_global (sp : fspec) (g : string) (ob : aobj) :=
  match index_of (TAtom g) gobjs with
  | Some i => list_set i (Some ob) (sp_pre sp)
  | None => sp_pre sp
  end.

(** A certificate fixes the exported specifications and verifies every plan. *)
Definition certifies t f cuts plans (specs : list fspec) :=
  map fst plans = specs /\ forallb (verified t f cuts) plans = true.

Lemma certified_count {t f cuts plans specs} : certifies t f cuts plans specs ->
  length plans = length specs.
Proof. intros [H _]. rewrite <- H, length_map. reflexivity. Qed.

(** Once the verifier accepts the plans, each exported specification holds
    for a call in the linked program. *)
Lemma certified_holds `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ} w0 ge {Hge : CpuImage ge}
    (Hends : ow_leaf4_ends w0 = true) {t g f cuts plans specs} :
  cpu_fn g f -> table_holds w0 ge t -> certifies t f cuts plans specs ->
  forall sp, In sp specs -> holds w0 ge (TAtom g) sp.
Proof.
  intros Hf Ht [<- Hv]. exact (verified_holds w0 ge Hends t g f cuts plans Hf Ht Hv).
Qed.
