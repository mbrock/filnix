(** This file proves that GNU Hello's main function cannot panic when
    linked with userland glibc, conditional on the explicit M4 and M6
    obligations in HelloDebts. All other calls use concrete library
    proofs. The theorem names no fixed addresses and assumes no separate
    world-preservation rules.

    The initial heap supplies argv, its strings, the standard streams,
    program-name cells, an empty exit-handler list and the remaining
    callees' private state. Heap adequacy turns the composed program
    triple into labelled safety for every finite execution prefix. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Run Machine
  ExternalCalls ExternalMachine Pieces Heap Language Logic MemLogic HelloLeaf HelloMain.
From Glibc Require Import OsWorld OsRegistry AtexitLogic HelloGlibcDebts HelloGlibcLibsT
  HelloGlibcMainLibs HelloGlibcMainFull.
Import ListNotations.
Open Scope Z_scope.

(** The safety theorem is uniform over every implementation of the runtime. *)
Module HelloGlibcJoin (R : Runtime).
(** All proofs share one logic instance. *)
Module LG0 := Logic R.
(** The composed main proof covers every branch of the function. *)
Module Main := HelloGlibcMainFullOn R LG0.
(** The remaining obligations use the concrete OS world. *)
Module D := Main.D.
(** The registration state belongs to the compiled glibc implementation. *)
Module AX := HelloGlibcAtexitOn R LG0.
(** The completed library record contains no extra call assumptions. *)
Module Libs := HelloGlibcMainLibsOn R LG0 D AX.
Import LG0 LG0.L D.

(** Every allowed execution avoids panics, stuck steps and contract failures.
    The remaining call obligations and their private state are supplied
    together for each ghost-heap instance used by adequacy. *)
Theorem hello_never_panics Σ {HinvP : invGpreS Σ} {HheapP : gen_heapGpreS piece pval Σ}
    w0 ge o m s w h0 argc av ar p0 ps x y z a i c fuel :
  hello_link ge o -> hello_layout ge o -> hello_os_layout w0 o ->
  argc = Z.of_nat (length (p0 :: ps)) -> 0 <= i <= argc ->
  R.ready s m -> live_disjoint m -> agrees m h0 -> os_wi w0 m w h0 ->
  (forall (HinvG : invGS_gen HasNoLc Σ) (HheapG : gen_heapGS piece pval Σ),
    exists debt : D.HelloDebts w0 ge o,
    ([∗ map] l ↦ v ∈ h0, pointsto l (DfracOwn 1) v) ⊢
      D.hello_ro ge o ∗ ([∗ list] q ∈ p0 :: ps, D.str_ro q) ∗ D.argv_own av ar (p0 :: ps) ∗
      D.ncells o x y z ∗ (AX.exit_funcs_inv (ho_x o) [] c ∗ Libs.exit_lock o) ∗
      D.hello_stdio w0 ge o ∗ D.hd_priv w0 ge o debt ∗ D.getopt_cells o a i) ->
  labelled_safe glibc_os_registry ge (invocation main_fn [WInt argc; WPtr (mkPtr av (Obj av))])
    m s w fuel (fun _ => True).
Proof.
  intros Hk Hy Hos -> Hi Hr Hd Ha Hw Hstart.
  apply (heap_labelled_safe Σ glibc_os_registry (os_wi w0) ge _ m s w h0 (fun _ => True) Hr Hd Ha Hw).
  intros HinvG HheapG. destruct (Hstart HinvG HheapG) as [debt Hpre]. rewrite Hpre.
  iIntros "(Hro & Hps & Hav & Hn & HX & Hio & Hpv & Hgo)".
  iApply (Main.main_full w0 ge o debt _ _ (Libs.hello_libs w0 ge o Hk Hos debt c) Hy
    av ar p0 ps x y z a i with "Hro Hps Hav Hn HX Hio Hpv Hgo"). exact Hi.
Qed.
End HelloGlibcJoin.
