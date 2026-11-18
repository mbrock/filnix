(** The first wide write may ask glibc for space twice. The first
    call can allocate both buffers without updating the narrow write
    pointer. Overflow sees that null pointer and calls the narrow
    allocator, which checks whether the stream already has space. *)

From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import Fix FileInv FileIdle LibioLogic LibioCloseSteps LibioPutsInv LibioFflushIdle
  AllocLogic LibioWIdle LibioWXsputnWindow LibioWOverflowDispatch LibioWOverflowSetp LibioWOverflowSetWide
  LibioWOverflowLoan LibioWOverflowBackup CBlocks.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic LibioCloseSteps.
Open Scope Z_scope.
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Abbreviation reg e n x := (lookup (TAtom n) e = Some x).
Local Abbreviation obj b := (mkPtr b (Obj b)).

Definition wo_alloc_tail l := match body_at wfile_overflow_fn l with Exec n (_ :: code) j => Exec n code j | x => x end.
Definition wo_after_walloc := Eval vm_compute in wo_alloc_tail "L34".
Definition wo_after_alloc := Eval vm_compute in wo_alloc_tail "L47".
Definition wo_new_wide wd w := [null;null;null;null;null;null;window_base wd w;wpos wd w (window_size w);null;null;null].

Section setup.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Abbreviation sexpr := (language.expr (nanofil_lang registry ge)).
Local Abbreviation run e at_ := (ERun (mkFrame wfile_overflow_fn e [] None at_) : sexpr).
Local Abbreviation block e l := (run e (body_at wfile_overflow_fn l)).
Local Ltac load_narrow cell := rule3 "Hf" cell "Hnb" ltac:(eapply wp_load_buf_ptr; inst;
  [reflexivity|vx|reflexivity|a2|a2|lia|lia|assumption]).

(** The second allocator has returned. It need not have changed the
    buffer, but the three read cursors must now point at its base. *)
Lemma wp_wo_after_alloc e ch vb fb fr fl f2 nb wd wr w b stop Φ :
  0 < fb -> fb mod 8 = 0 -> fb+224 <= r_end fr -> r_end fr <= 2^63 -> in_buf fb nb b -> wo_setup_regs e fb ch ->
  wo_cells vb fb fr fl f2 nb wd wr w [null;null;null;null;null;null;b;stop] (wo_new_wide wd w) -∗
  (∀ ee, ⌜wo_setup_regs ee fb ch⌝ -∗ wo_cells vb fb fr fl f2 nb wd wr w [b;b;b;null;null;null;b;stop] (wo_new_wide wd w) -∗
    WP (block ee "L49") {{ Φ }}) -∗ WP (run e wo_after_alloc) {{ Φ }}.
Proof using Type.
  intros Fb Fa Fe Fr B (Hfp & Hch & Hck & H7).
  iIntros "(Hf & Hfl & Hf2 & Hfd & Hm & Hvt & Hwd & Hp & Hnb & Hl & Hw & Hwvt & Hb) HK".
  iDestruct "Hp" as "(P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & _)". change (off_ptr 6) with 56.
  change (off_ptr 0) with 8. change (off_ptr 1) with 16. change (off_ptr 2) with 24. unfold wo_after_alloc.
  do 2 step. check "Hf". load_narrow "P6". check "Hf". store "Hf" "P2".
  step. check "Hf". load_narrow "P6". check "Hf". store "Hf" "P0".
  step. check "Hf". load_narrow "P6". check "Hf". store "Hf" "P1". do 2 step.
  iApply ("HK" with "[%] [-]"); [unfold wo_setup_regs; split_and!; lookups; done|]. rewrite /wo_cells /=. by iFrame.
Qed.

Context `{!Defines ge "__GI__IO_free_wbackup_area" wfree_backup_fn} `{!Defines ge "free" free_fn}
  (Hfree : frees_heap (ge_free ge)) (Hfn : find_fn ge zgc_free_name = None) (Hsym : lookup zgc_free_name (ge_globals ge) = None).

(** Overflow discards any characters saved for reading before it sets
    up the new buffer for writing. This stream has no saved characters,
    so that call leaves the new buffer untouched. *)
Lemma wp_wo_after_walloc have e ch vb fb fr fl f2 nb wd wr w rp re rb wb wp we b stop Φ :
  0 < fb -> fb mod 8 = 0 -> fb+224 <= r_end fr -> r_end fr <= 2^63 ->
  0 < wd -> wd mod 8 = 0 -> wd+232 <= r_end wr -> r_end wr <= 2^63 -> Z.land fl 256 = 0 ->
  (if have : bool then in_buf fb nb wb /\ 0 < ptr_addr wb < 2^64 else wb = null) ->
  wo_setup_regs e fb ch -> reg e "v43" (WInt 0) ->
  let cells := wo_cells vb fb fr fl f2 nb wd wr w [rp;re;rb;wb;wp;we;b;stop] (wo_new_wide wd w) in
  cells -∗ (∀ ee, ⌜wo_setup_regs ee fb ch⌝ -∗ cells -∗ WP (block ee (if have then "L49" else "L47")) {{ Φ }}) -∗ WP (run e wo_after_walloc) {{ Φ }}.
Proof using Type*.
  intros Fb Fa Fe Fr Wd Wa We Wr NoBackup B (Hfp & Hch & Hck & H7) Z43. cbn zeta.
  iIntros "(Hf & Hfl & Hf2 & Hfd & Hm & Hvt & Hwd & Hp & Hnb & Hl & Hw & Hwvt & Hb) HK".
  iDestruct "Hp" as "(P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & _)". change (off_ptr 3) with 32.
  iDestruct "Hw" as "(W0 & W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & _)". unfold wo_after_walloc.
  iApply wp_call_bind; [vx|apply defines|reflexivity|]. iNext.
  iApply (wp_wfree_backup Hfree Hfn Hsym _ fb fr fl wd wr with "Hf Hfl Hwd Hl W8 W9 W10"); try assumption; [reflexivity|].
  iNext. iIntros "Hf Hfl Hwd Hl W8 W9 W10". resume. step. check "Hf".
  destruct have; [destruct B as (In & Range); load_narrow "P3"|subst wb; load_null "Hf" "P3"];
    do 2 step; [branch_as true|branch]; step;
    iApply ("HK" with "[%] [-]"); try (unfold wo_setup_regs; split_and!; lookups; done); rewrite /wo_cells /wo_new_wide /=; by iFrame.
Qed.
End setup.
