(** This file proves that GNU Hello's main function cannot panic when
    linked with userland glibc, under an indexed contract for
    getopt_long. HelloGlibcJoin.v proves the same result under the
    original contract, which accepts any public index and says nothing
    about the parser's private object. That contract cannot be proved
    for glibc, because glibc's parser resumes from the private object,
    and the object must match the argument vector and the index.

    Under the new contract, each call borrows the parser's object in a
    state that suits the current vector and index. The call gives the
    object back in a state that suits the vector and index it leaves.
    So the program must start with the object in such a state. It may
    hold a session that the starting optind continues or restarts, or it
    may hold zeroes, with optind anywhere from zero to argc. Every other
    obligation is the one that the original theorem states. *)

From Glibc Require Import GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Run Machine
  ExternalCalls ExternalMachine Pieces Heap Language Logic MemLogic HelloLeaf HelloMain.
From Glibc Require Import OsWorld OsRegistry AtexitLogic HelloGlibcDebts HelloGlibcLibsT
  HelloGlibcMainLoop HelloGlibcMainFull HelloGetoptState.
From Glibc Require HelloGlibcDebts HelloGlibcMainFull HelloGlibcJoin HelloGetoptState.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Import LG0 LG0.L HelloGlibcDebts.

Section debts.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (ge : genv) (o : hello_objs).

(** The new obligations keep the contract of every other call and
    change only that of getopt_long. The parser keeps its progress in one
    object, whose address and region the record names. Each call borrows
    the object in a state that suits the vector and the index. It returns
    the object suited to the reordered vector and the new index. *)
Record HelloDebtsIx : Type := mkHelloDebtsIx {
  hx_base : HelloCore w0 ge o;
  hx_gb : Z;
  hx_greg : region;
  hx_getopt : forall av ar, loop_getopt w0 ge o hx_base av ar (hello_getopt_state hx_gb hx_greg av ar)
}.

End debts.

(** A proof that uses only the other contracts accepts the indexed record. *)
Coercion hx_base : HelloDebtsIx >-> HelloCore.

(** Every allowed execution avoids panics, stuck steps and contract
    failures. The initial heap supplies what the original theorem asks
    for and, in addition, the parser's object in an admissible state for
    the starting vector and public index. *)
Theorem hello_never_panics_ix Σ {HinvP : invGpreS Σ} {HheapP : gen_heapGpreS piece pval Σ}
    w0 ge o m s w h0 argc av ar p0 ps x y z a i c fuel :
  hello_link ge o -> hello_layout ge o -> hello_os_layout w0 o ->
  argc = Z.of_nat (length (p0 :: ps)) -> 0 <= i <= argc ->
  R.ready s m -> live_disjoint m -> agrees m h0 -> os_wi w0 m w h0 ->
  (forall (HinvG : invGS_gen HasNoLc Σ) (HheapG : gen_heapGS piece pval Σ),
    exists debt : HelloDebtsIx w0 ge o,
    ([∗ map] l ↦ v ∈ h0, pointsto l (DfracOwn 1) v) ⊢
      hello_ro ge o ∗ ([∗ list] q ∈ p0 :: ps, str_ro q) ∗ argv_own av ar (p0 :: ps) ∗
      ncells o x y z ∗ (HelloGlibcJoin.AX.exit_funcs_inv (ho_x o) [] c ∗ HelloGlibcJoin.Libs.exit_lock o) ∗
      hello_stdio w0 ge o ∗ hd_priv w0 ge o debt ∗ getopt_cells o a i ∗
      hello_getopt_state (hx_gb w0 ge o debt) (hx_greg w0 ge o debt) av ar (p0 :: ps) i) ->
  labelled_safe glibc_os_registry ge (invocation main_fn [WInt argc; WPtr (mkPtr av (Obj av))])
    m s w fuel (fun _ => True).
Proof.
  intros Hk Hy Hos -> Hi Hr Hd Ha Hw Hstart.
  apply (heap_labelled_safe Σ glibc_os_registry (os_wi w0) ge _ m s w h0 (fun _ => True) Hr Hd Ha Hw).
  intros HinvG HheapG. destruct (Hstart HinvG HheapG) as [debt Hpre]. rewrite Hpre.
  iIntros "(Hro & Hps & Hav & Hn & HX & Hio & Hpv & Hgo & HS)".
  iApply (HelloGlibcMainFull.main_full_state w0 ge o debt _ _
    (HelloGlibcJoin.Libs.hello_libs w0 ge o Hk Hos debt c) Hy av ar p0 ps x y z a i
    (hello_getopt_state (hx_gb w0 ge o debt) (hx_greg w0 ge o debt) av ar) _ Hi (hx_getopt w0 ge o debt av ar)
    with "Hro Hps Hav Hn HX Hio Hpv Hgo HS").
Qed.
