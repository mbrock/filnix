(** Error prints its program name, error text and newline with __fxprintf.
    This wrapper copies all arguments into a snapshot and passes a cursor
    after the two named arguments to __vfxprintf. It does not select stderr,
    take a lock or change cancellation itself. Those operations, if any,
    belong to the called function, whose contract remains explicit here. *)
From Glibc Require Import Unit_stdioZ2dcommon_fxprintf_os.
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic Identity VariadicLogic.
From Glibc Require Import OsWorld FileInv LibioLogic LibioCloseSteps
  FxprintfStream Fix.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic.
Open Scope Z_scope.
Module NormalVL := VariadicLogicOn R LG0.
Import NormalVL.

Definition fxprintf_normal_frame (fp fmt : ptr) (ys : list word) : frame :=
  mkFrame Unit_stdioZ2dcommon_fxprintf_os.fn___fxprintf
    (put (TAtom "v2") (WPtr fmt) (put (TAtom "v0") (WPtr fp) [])) [] None
    (Snapshot (WPtr fp :: WPtr fmt :: ys) (TAtom "start")).
Lemma fxprintf_normal_call_frame fp fmt ys :
  call_frame Unit_stdioZ2dcommon_fxprintf_os.fn___fxprintf (WPtr fp :: WPtr fmt :: ys) = Some (fxprintf_normal_frame fp fmt ys).
Proof. reflexivity. Qed.

Section wrapper.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Instance normal_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** Null remains the first argument of the snapshot even if the callee
    later selects stderr. The result need not indicate successful output.
    R can lend format and argument shares and mutable errno to the callee;
    E remains untouched. *)
Lemma wp_fxprintf_normal fp fmt ys vfn (vf : ptr -> frame)
    (R E : iProp Σ) (Q : Z -> iProp Σ) Φ :
  forallb snapshot_word ys = true ->
  find_fn ge (TAtom "__vfxprintf") = Some (Defined vfn) ->
  (forall ap, call_frame vfn [WPtr fp;WPtr fmt;WPtr ap;WInt 0] = Some (vf ap)) ->
  (forall ap, ⊢ fx_va ap (WPtr fp :: WPtr fmt :: ys) -∗ R -∗
    WP (ERun (vf ap) : gexpr) {{ v, ∃ r, ⌜v = Ret (WInt r)⌝ ∗ Q r }}) ->
  R -∗ E -∗ ▷ (∀ r, Q r -∗ E -∗ Φ (Ret (WInt (r mod 2 ^ 32)))) -∗
  WP (ERun (fxprintf_normal_frame fp fmt ys) : gexpr) {{ Φ }}.
Proof using Type.
  intros Hys Hfn Hframe Hcall. iIntros "HR HE HK". unfold fxprintf_normal_frame.
  iApply NormalVL.wp_snapshot; [discriminate | cbn; exact Hys |
    intros ? ? ? ? Hf Hw; exact (os_wi_snapshot _ _ _ _ _ _ _ Hf Hw) |].
  iNext. iIntros (sb [Hsb [Hsal Hsend]]) "Hsnap".
  change (sb mod 16 = 0) in Hsal.
  pose proof (heap_req_extent 16 (8 * Z.of_nat (length (WPtr fp :: WPtr fmt :: ys)))) as Hextent.
  step. iApply wp_alloc; [vm_compute; reflexivity | vm_compute; congruence | vm_compute; congruence |
    intros ? ? ? ? Hf Hw; exact (os_wi_alloc w0 _ _ _ _ _ Hf Hw) |].
  iNext. iIntros (cb [Hcb [Hcal Hcend]]) "Hobj".
  change (cb mod 16 = 0) in Hcal. change (cb + 32 <= 2 ^ 48) in Hcend.
  assert (Hc8 : cb mod 8 = 0) by (Z.div_mod_to_equations; lia).
  iDestruct (obj_zero_block with "Hobj") as "(Hcl & Hx & Ha)"; [compute; discriminate |].
  iAssert (live cb (mkRegion cb (cb + 32) Heap Live)) with "Hcl" as "Hcl".
  set (creg := mkRegion cb (cb + 32) Heap Live) in *.
  assert (Hcre : r_end creg = cb + 32) by reflexivity.
  iDestruct (zero_cell_prefix cb 0 24 with "Hx Ha") as "(Hcc & _ & _)".
  iApply NormalVL.wp_va_args; [reflexivity |]. iNext.
  check "Hcl". store "Hcl" "Hcc".
  assert (Hva : (ptr_addr (mkPtr sb (Ro sb)) + 16) mod 2 ^ 64 = sb + 16)
    by (cbn; apply Z.mod_small; lia).
  iEval (rewrite Hva) in "Hcc".
  iAssert (fx_va (mkPtr cb (Obj cb)) (WPtr fp :: WPtr fmt :: ys))
    with "[Hcl Hcc Hsnap]" as "Hva".
  { iExists cb, sb. iSplit; [iPureIntro; split_and!; auto |].
    iSplitR "Hsnap"; [|iExact "Hsnap"].
    replace (va_cursor_ps cb (mkRegion cb (cb + 32) Heap Live) (mkPtr (sb + 16) (Ro sb))) with
      ([(PLive cb, VLive creg)] ++ ((PAux cb 0, VAux (Ro sb)) :: cell cb 0 (sb + 16)))%list by reflexivity.
    rewrite pts_app. iFrame. }
  iApply wp_call_bind; [vx | exact Hfn | apply Hframe |]. iNext.
  iApply (wp_wand with "[Hva HR]"); [iApply (Hcall with "Hva HR") |].
  iIntros (v) "H". iDestruct "H" as (r ->) "HQ". resume.
  iApply wp_ret; [reflexivity | vx |]. iNext.
  rewrite Z.mod_mod; [|lia]. iApply ("HK" with "HQ HE").
Qed.

(** One call rule covers the two one-pointer reports and the argument-free
    newline. Their format pointers and argument lists stay distinct. *)
Lemma wp_call_fxprintf_normal f e ls l d args rest j fp fmt ys vfn (vf : ptr -> frame)
    (R E : iProp Σ) (Q : Z -> iProp Σ) Φ :
  map_option (arg_x ge e) args = Some (WPtr fp :: WPtr fmt :: ys) ->
  find_fn ge (TAtom "__fxprintf") = Some (Defined Unit_stdioZ2dcommon_fxprintf_os.fn___fxprintf) ->
  forallb snapshot_word ys = true ->
  find_fn ge (TAtom "__vfxprintf") = Some (Defined vfn) ->
  (forall ap, call_frame vfn [WPtr fp;WPtr fmt;WPtr ap;WInt 0] = Some (vf ap)) ->
  (forall ap, ⊢ fx_va ap (WPtr fp :: WPtr fmt :: ys) -∗ R -∗
    WP (ERun (vf ap) : gexpr) {{ v, ∃ r, ⌜v = Ret (WInt r)⌝ ∗ Q r }}) ->
  R -∗ E -∗ ▷ (∀ r, Q r -∗ E -∗
    WP (ERun (mkFrame f (put d (WInt (r mod 2 ^ 32)) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
    (Exec l (Call (CResult d W) (Global (TAtom "__fxprintf")) args :: rest) j)) : gexpr) {{ Φ }}.
Proof using Type.
  intros Hargs Hpublic Hys Hfn Hframe Hcall. iIntros "HR HE HK".
  iApply wp_call_bind; [exact Hargs | exact Hpublic | apply fxprintf_normal_call_frame |]. iNext.
  iApply (wp_fxprintf_normal with "HR HE"); try eassumption.
  iNext. iIntros (r) "HQ HE".
  iExists (mkFrame f (put d (WInt ((r mod 2 ^ 32) mod 2 ^ 32)) e) ls None (Exec l rest j)).
  iSplit; [done |]. iNext. rewrite Z.mod_mod; [|lia]. iApply ("HK" with "HQ HE").
Qed.
End wrapper.
