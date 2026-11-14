(** This file proves the start block of GNU Hello's `main`, linked
    with userland glibc, from `main`'s entry to its option loop at
    `iw_1.L8`.

    Initialization allocates the greeting cell and conversion state,
    sets the program name and locale, and selects the default greeting.
    It also registers the close callback. The locale call remains an
    explicit debt; the other calls use their concrete library proofs. *)

From Glibc Require Import GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic
  HelloModule HelloLeaf HelloMain.
From Glibc Require Import OsWorld OsRegistry WordString FileInv LeavesLogic LibioLogic ExitRunTail
  HelloGlibcProgCells HelloGlibcDebts HelloGlibcMainSteps.
From Glibc Require HelloGlibcDebts HelloGlibcMainSteps.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

(** Main enters its option loop with the argument count and vector,
    the greeting cell, the conversion state and a checked greeting pointer. *)
Definition start_vars (e : env) (argc av b4 b6 : Z) : Prop :=
  lookup (TAtom "v0") e = Some (WInt argc) /\ lookup (TAtom "v2") e = Some (WPtr (mkPtr av (Obj av))) /\
  lookup (TAtom "v4") e = Some (WPtr (mkPtr b4 (Obj b4))) /\
  lookup (TAtom "v6") e = Some (WPtr (mkPtr b6 (Obj b6))) /\
  lookup (TAtom "chk1") e = Some (WPtr (mkPtr b4 (Obj b4))).

(** A fresh object has a positive, sixteen-aligned base and fits in the address space. *)
Definition fresh16 (b : Z) : Prop := 0 < b /\ b mod 16 = 0 /\ b + 16 <= 2 ^ 48.


(** The step module supplies the shared rules and tactics. *)
Import HelloGlibcMainSteps HelloGlibcDebts HelloGlibcDebts.FB HelloGlibcDebts.SW HelloGlibcDebts.SW.FI.ML HelloGlibcDebts.SW.FI.LG HelloGlibcDebts.SW.FI.L HelloGlibcDebts.SW.OW HelloGlibcDebts.SW.FI.

Section start.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (ge : genv) (o : hello_objs) (D : HelloDebts w0 ge o) (X0 X : iProp Σ)
  (Lb : HelloLibs w0 ge o (hd_priv w0 ge o D) X0 X) (Hy : hello_layout ge o).

(** Collector safepoints preserve the concrete OS interpretation. *)
Local Instance start_stable : SafepointStable (os_wi w0) := os_wi_stable w0.
(** The program logic uses glibc's OS registry and concrete world interpretation. *)
Local Instance start_irisGS : irisGS_gen hlc (nanofil_lang glibc_os_registry ge) Σ :=
  nanofil_irisGS glibc_os_registry (os_wi w0) ge.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang glibc_os_registry ge)).

(** A 16-byte heap object of 8 bytes' request, zeroed, with a pointer
    p stored in its first cell, is its [gcell]. *)
Lemma gcell_store b4 :
  obj b4 (heap_req 8 8) ⊢ live b4 (mkRegion b4 (b4 + 16) Heap Live) ∗ pcell b4 0 null ∗
    bytes b4 8 (replicate 8 0) ∗ auxes b4 1 (replicate 15 CNone).
Proof.
  rewrite (obj_zero_block b4 _); [|vm_compute; congruence].
  change (req_extent (heap_req 8 8)) with 16. change (req_kind (heap_req 8 8)) with Heap.
  change (replicate (Z.to_nat 16) 0) with (replicate 8 0 ++ replicate 8 0).
  change (replicate (Z.to_nat 16) CNone) with ([CNone] ++ replicate 15 CNone).
  rewrite bytes_app auxes_app. cbn [length replicate]. iIntros "($ & [H0 $] & [A0 $])".
  iApply zero_pcell. iFrame.
Qed.

(** Initialization supplies the option loop with its greeting cell,
    zeroed conversion state, program names and registered close callback. *)
Lemma main_start av ar p0 ps' x y z Φ :
  let ps := p0 :: ps' in
  hello_ro ge o -∗ ([∗ list] q ∈ ps, str_ro q) -∗ argv_own av ar ps -∗ ncells o x y z -∗ X0 -∗
  hello_stdio w0 ge o -∗ hd_priv w0 ge o D -∗
  ▷ (∀ e b4 b6 pn sn, ⌜start_vars e (Z.of_nat (length ps)) av b4 b6 /\ fresh16 b4 /\ fresh16 b6⌝ -∗
       argv_own av ar ps -∗ ncells o pn pn sn -∗ str_ro pn -∗ str_ro sn -∗ X -∗ hello_stdio w0 ge o -∗
       hd_priv w0 ge o D -∗
       gcell b4 (sym_ptr ge "hello#str.81") -∗ obj b6 (heap_req 4 8) -∗
       WP (ERun (mkFrame main_fn e [] None (Enter (TAtom "iw_1.L8") (Some (TAtom "start")))) : gexpr) {{ Φ }}) -∗
  WP (ERun (invocation main_fn [WInt (Z.of_nat (length ps)); WPtr (mkPtr av (Obj av))]) : gexpr) {{ Φ }}.
Proof.
  intros ps. iIntros "#Hro #Hps Hav Hnc HX0 Hio Hpv HK".
  rewrite main_entry. step.
  (* b4, the greeting's cell. *)
  iApply (wp_alloc _ _ _ _ _ _ _ _ _ _ _ _ _ 8);
    [reflexivity | lia | unfold max_allocation_size; lia | intros m wd h base Hf Hw; exact (os_wi_alloc w0 m wd h _ base Hf Hw) |].
  iNext. iIntros (b4 Hb4) "Hb4".
  (* b6, the conversion state, zeroed by mbszero. *)
  iApply (wp_alloc _ _ _ _ _ _ _ _ _ _ _ _ _ 8);
    [reflexivity | lia | unfold max_allocation_size; lia | intros m wd h base Hf Hw; exact (os_wi_alloc w0 m wd h _ base Hf Hw) |].
  iNext. iIntros (b6 Hb6) "Hb6".
  change (req_align (heap_req 8 8)) with 16 in Hb4. change (req_extent (heap_req 8 8)) with 16 in Hb4.
  change (req_align (heap_req 4 8)) with 16 in Hb6. change (req_extent (heap_req 4 8)) with 16 in Hb6.
  destruct Hb4 as (Hb40 & Hb416 & Hb448). destruct Hb6 as (Hb60 & Hb616 & Hb648).
  iApply (wp_call_void with "Hb6"); [exact (hl_mbszero _ _ _ _ _ _ Lb b6 Hb60 Hb616 Hb648) | reflexivity |].
  iNext. iIntros "Hb6".
  (* argv[0], the program's name. *)
  iDestruct "Hav" as "(%Hav & Hal & Hslots)". pose proof Hav as (Hav0 & Hav8 & H31 & Havend & Har).
  rule1 "Hal" ltac:(eapply wp_check_read; inst;
    [reflexivity | vx | left; reflexivity | arith | cbn [length] in Havend; arith | arith]).
  iApply (wp_argv_load _ _ _ _ _ _ _ _ _ _ av ar ps av 0 with "[Hal Hslots] Hps");
    [reflexivity | lia | cbn; lia | iFrame; iPureIntro; exact Hav |].
  iNext. iIntros "Hav". cbn [nth app].
  iAssert (str_ro p0) as (s0) "#Hs0"; [iApply (big_sepL_elem_of with "Hps"); left|].
  iApply (wp_call_void with "[Hnc]"); [exact (hl_name _ _ _ _ _ _ Lb p0 s0 x y z) | reflexivity |
    iFrame "Hro Hs0 Hnc" |].
  iNext. iIntros "Hnc".
  (* setlocale (LC_ALL, ""). *)
  step_global (hy_lits _ _ Hy "hello#str.80" ltac:(cbn; tauto)).
  iApply (wp_call_ptr w0 ge _ _ _ (fun _ => hello_stdio w0 ge o ∗ hd_priv w0 ge o D)%I with "[Hio Hpv]");
    [exact (hd_setlocale_all _ _ _ D) | reflexivity |
    iSplitR; [iExact "Hro" | iSplitL "Hio"; [iExact "Hio" | iExact "Hpv"]] |].
  iNext. iIntros (q) "[Hio Hpv]".
  (* The default greeting, stored in b4's cell. *)
  step_global (hy_lits _ _ Hy "hello#str.81" ltac:(cbn; tauto)).
  iDestruct (gcell_store with "Hb4") as "(Hl4 & Hp4 & Hy4 & Hc4)".
  rule1 "Hl4" ltac:(eapply wp_check; inst; [reflexivity | vx | reflexivity | arith | cbn [r_end]; arith | arith]).
  rule2 "Hl4" "Hp4" ltac:(eapply wp_raw_store_pointer; inst; [vx | vx | reflexivity | arith | arith | wi_store]).
  (* atexit (close_stdout). *)
  step_global (hy_cp _ _ Hy).
  iApply (wp_call_int with "HX0"); [exact (hl_atexit _ _ _ _ _ _ Lb) | reflexivity |].
  iNext. iIntros (k Hk) "HX". step.
  iApply ("HK" $! _ b4 b6 (ptr_add p0 (Z.of_nat (name_idx s0))) (ptr_add p0 (Z.of_nat (short_idx s0)))
           with "[%] Hav Hnc [] [] HX Hio Hpv [Hl4 Hp4 Hy4 Hc4] Hb6").
  - split; [repeat split; reflexivity|]. split; [split; [lia | split; [exact Hb416 | lia]] |].
    split; [lia | split; [exact Hb616 | lia]].
  - pose proof (name_idx_le s0). pose proof (short_idx_le s0). iApply (str_ro_suffix with "Hs0"). lia.
  - pose proof (short_idx_le s0). iApply (str_ro_suffix with "Hs0"). lia.
  - rewrite /gcell. iFrame.
Qed.

End start.
