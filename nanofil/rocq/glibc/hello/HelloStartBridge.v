(** Hello's safety theorem starts at `c: main`, and its caller must
    describe the memory that main starts with. The proof of glibc's
    startup code ends at the same place, when `c: __libc_start_call_main`
    calls `c: main`. This module gives `c: main` a contract in the form
    that the startup proof calls, so that the startup proof can supply
    main's starting state instead of the caller.

    ## What main needs

    Hello prints, parses its options and exits through code that is
    already proved, and that proof starts from a fixed set of objects:
    the streams, the thread, the names and the arguments. The startup
    proof builds those objects, so it can hand them to main directly.
    Startup supplies the library proofs for that same private state. *)

From Glibc Require Import HelloObjects GlibcTactics GlibcProgram GlibcSpec.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Semantics Pieces Heap Logic Language.
From Glibc Require Import IRFrames HelloBodies OsWorld OsRegistry HelloGlibcDebts HelloGlibcMainLoop
  HelloGlibcMainFull.
Import ListNotations.
Open Scope Z_scope.

Section spec.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (ge : genv) (o : hello_objs) (priv X0 X : iProp Σ)
  (Lb : HelloLibs w0 ge o priv X0 X) (Hy : hello_layout ge o).

(** Main is called with the argument count and the argument vector. The
    binder holds the vector's object, the arguments, the three name
    cells, the parser's cells and the state S that getopt_long keeps
    between calls. *)
Definition hello_main_binder : Type :=
  Z * region * ptr * list ptr * ptr * ptr * ptr * ptr * Z * (list ptr -> Z -> iProp Σ).

(** Main reads its arguments, prints to the streams and calls
    getopt_long in a loop, so it starts owning those objects. The loop
    needs the option parser to keep its promise about the state St
    that it carries between calls, and the parser starts at an index
    between zero and the argument count. *)
Definition hello_main_pre (b : hello_main_binder) : iProp Σ :=
  let '(av, ar, p0, ps, x, y, z, a, i, St) := b in
  ⌜0 <= i <= Z.of_nat (length (p0 :: ps)) /\ loop_getopt w0 ge o priv av ar St⌝ ∗
  hello_ro ge o ∗ ([∗ list] q ∈ p0 :: ps, str_ro q) ∗ argv_own av ar (p0 :: ps) ∗
  ncells o x y z ∗ X0 ∗ hello_stdio w0 ge o ∗ priv ∗ getopt_cells o a i ∗ St (p0 :: ps) i.

(** Main takes `c: argc` and `c: argv` and never returns, because every
    path ends in `c: exit`. *)
Definition hello_main_spec : fspec Σ :=
  FSpec hello_main_binder
    (fun '(av, _, p0, ps, _, _, _, _, _, _) => [WInt (Z.of_nat (length (p0 :: ps))); WPtr (mkPtr av (Obj av))])
    hello_main_pre (fun _ _ => False)%I.

(** When the image's `c: main` is Hello's main function, it keeps this
    contract. *)
Lemma hello_main_has_spec :
  find_fn ge (TAtom "main") = Some (Defined main_fn) ->
  HasSpec glibc_os_registry (os_wi w0) ge (TAtom "main") hello_main_spec.
Proof using Lb Hy.
  intros Hmain [[[[[[[[[av ar] p0] ps] x] y] z] a] i] St].
  exists main_fn. split; [exact Hmain|].
  cbn [fs_args hello_main_spec].
  assert (Hfr : call_frame main_fn [WInt (Z.of_nat (length (p0 :: ps))); WPtr (mkPtr av (Obj av))] =
    Some (invocation main_fn [WInt (Z.of_nat (length (p0 :: ps))); WPtr (mkPtr av (Obj av))]))
    by (rewrite /invocation; reflexivity).
  split; [eexists; exact Hfr|]. intros fr Φ Hf. rewrite Hfr in Hf. injection Hf as <-.
  cbn [fs_pre hello_main_spec hello_main_pre].
  iIntros "([%Hi %Hgr] & #Hro & #Hps & Hav & Hnc & HX0 & Hio & Hpv & Hgo & HS) _".
  iApply (main_full_state w0 ge o priv X0 X Lb Hy av ar p0 ps x y z a i St Φ Hi Hgr
    with "Hro Hps Hav Hnc HX0 Hio Hpv Hgo HS").
Qed.

End spec.
