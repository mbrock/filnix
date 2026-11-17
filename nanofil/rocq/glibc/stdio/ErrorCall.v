(** glibc's error wrapper snapshots its arguments and passes a cursor to
    __error_internal. The cursor skips the three named arguments. This
    module proves that wrapper, not the internal reporting function.

    The wrapper delegates printing to another function. The caller must
    prove that function separately before using this rule to prove an
    error report. The captured wrapper does not take a stream lock. *)
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic Identity VariadicLogic.
From Glibc Require Import OsWorld FileInv LibioLogic LibioCloseSteps PrintfStreamInv
  FxprintfStream ErrorCode Fix.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic.
Open Scope Z_scope.
Module ErrorVL := VariadicLogicOn R LG0.
Import ErrorVL.

(** The call frame retains all arguments in its read-only snapshot. *)
Definition error_frame (status errnum : Z) (fmt : ptr) (ys : list word) : frame :=
  mkFrame glibc_error
    (put (TAtom "v4") (WPtr fmt) (put (TAtom "v2") (WInt errnum)
      (put (TAtom "v0") (WInt status) []))) [] None
    (Snapshot (WInt status :: WInt errnum :: WPtr fmt :: ys) (TAtom "start")).

(** Binding the public arguments does not read the mutable errno cell. *)
Lemma error_call_frame status errnum fmt ys :
  call_frame glibc_error (WInt status :: WInt errnum :: WPtr fmt :: ys) =
    Some (error_frame status errnum fmt ys).
Proof. reflexivity. Qed.

(** The public name refers to the captured function in this fixture.
    A larger program may replace it with a different definition. *)
Lemma error_alias_found globals free :
  find_alias (TAtom "error") error_module = Some (TAtom "__error") /\
  find_fn (mkGenv error_module globals free) (TAtom "error") = Some (Defined glibc_error).
Proof. split; reflexivity. Qed.

Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Instance error_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** The cursor owns its cell and the snapshot, including the named words.
    The internal callee may consume this temporary ownership. *)
Definition error_va (ap : ptr) (xs : list word) : iProp Σ :=
  ∃ cb sb, ⌜ap = mkPtr cb (Obj cb) /\ 0 < sb /\ sb mod 16 = 0 /\
      sb + req_extent (fx_req xs) <= 2 ^ 48⌝ ∗
    pts (va_cursor_ps cb (mkRegion cb (cb + 32) Heap Live) (mkPtr (sb + 24) (Ro sb))) ∗
    pts (snapshot_ps xs sb (fx_req xs)).

(** The wrapper calls __error_internal with mode zero. The caller lends
    resources R to that call and receives Q on return. These resources can
    include stderr and the stream list; the wrapper does not duplicate them.
    Resources E remain untouched throughout the call. *)
Lemma wp_error_wrapper status errnum fmt ys
    (internal_frame : ptr -> frame) (R Q E : iProp Σ) Φ :
  forallb snapshot_word ys = true ->
  0 <= status < 2 ^ 32 -> 0 <= errnum < 2 ^ 32 ->
  find_fn ge (TAtom "__error_internal") = Some (Defined glibc_error_internal) ->
  (forall ap, call_frame glibc_error_internal
    [WInt status; WInt errnum; WPtr fmt; WPtr ap; WInt 0] = Some (internal_frame ap)) ->
  (forall ap, ⊢ error_va ap (WInt status :: WInt errnum :: WPtr fmt :: ys) -∗ R -∗
    WP (ERun (internal_frame ap) : gexpr) {{ v, ⌜v = RetVoid⌝ ∗ Q }}) ->
  R -∗ E -∗ ▷ (Q -∗ E -∗ Φ RetVoid) -∗
  WP (ERun (error_frame status errnum fmt ys) : gexpr) {{ Φ }}.
Proof using Type.
  intros Hys Hstatus Herrnum Hfn Hframe Hcall. iIntros "HR HE HK".
  unfold error_frame.
  iApply ErrorVL.wp_snapshot; [discriminate | cbn; exact Hys |
    intros ? ? ? ? Hf Hw; exact (os_wi_snapshot _ _ _ _ _ _ _ Hf Hw) |].
  iNext. iIntros (sb [Hsb [Hsal Hsend]]) "Hsnap".
  change (sb mod 16 = 0) in Hsal.
  pose proof (heap_req_extent 16 (8 * Z.of_nat (length
    (WInt status :: WInt errnum :: WPtr fmt :: ys)))) as Hextent.
  step.
  iApply wp_alloc; [vm_compute; reflexivity | vm_compute; congruence | vm_compute; congruence |
    intros ? ? ? ? Hf Hw; exact (os_wi_alloc w0 _ _ _ _ _ Hf Hw) |].
  iNext. iIntros (cb [Hcb [Hcal Hcend]]) "Hobj".
  change (cb mod 16 = 0) in Hcal. change (cb + 32 <= 2 ^ 48) in Hcend.
  assert (Hc8 : cb mod 8 = 0) by (Z.div_mod_to_equations; lia).
  iDestruct (obj_zero_block with "Hobj") as "(Hcl & Hx & Ha)"; [compute; discriminate |].
  iAssert (live cb (mkRegion cb (cb + 32) Heap Live)) with "Hcl" as "Hcl".
  set (creg := mkRegion cb (cb + 32) Heap Live) in *.
  assert (Hcre : r_end creg = cb + 32) by reflexivity.
  iDestruct (zero_cell_prefix cb 0 24 with "Hx Ha") as "(Hcc & _ & _)".
  iApply ErrorVL.wp_va_args; [reflexivity |]. iNext.
  check "Hcl". store "Hcl" "Hcc".
  assert (Hva : (ptr_addr (mkPtr sb (Ro sb)) + 24) mod 2 ^ 64 = sb + 24)
    by (cbn; apply Z.mod_small; lia).
  iEval (rewrite Hva) in "Hcc".
  iAssert (error_va (mkPtr cb (Obj cb)) (WInt status :: WInt errnum :: WPtr fmt :: ys))
    with "[Hcl Hcc Hsnap]" as "Hva".
  { iExists cb, sb. iSplit; [iPureIntro; split_and!; auto |].
    iSplitR "Hsnap"; [|iExact "Hsnap"].
    replace (va_cursor_ps cb (mkRegion cb (cb + 32) Heap Live) (mkPtr (sb + 24) (Ro sb))) with
      ([(PLive cb, VLive creg)] ++ ((PAux cb 0, VAux (Ro sb)) :: cell cb 0 (sb + 24)))%list by reflexivity.
    rewrite pts_app. iFrame. }
  iApply wp_call_bind; [vx | exact Hfn | |].
  { rewrite (Z.mod_small status _ Hstatus) (Z.mod_small errnum _ Herrnum).
    apply Hframe. }
  iNext.
  iApply (wp_wand with "[Hva HR]"); [iApply (Hcall with "Hva HR") |].
  iIntros (v) "(-> & HQ)". resume. iApply wp_ret_void. iNext. iApply ("HK" with "HQ HE").
Qed.

(** The public name uses the caller's linked lookup, so a strong override
    of the weak alias cannot silently acquire this specification. *)
Lemma wp_call_error_wrapper f e ls l args rest j status errnum fmt ys
    (internal_frame : ptr -> frame) (R Q E : iProp Σ) Φ :
  map_option (arg_x ge e) args = Some (WInt status :: WInt errnum :: WPtr fmt :: ys) ->
  find_fn ge (TAtom "error") = Some (Defined glibc_error) ->
  forallb snapshot_word ys = true ->
  0 <= status < 2 ^ 32 -> 0 <= errnum < 2 ^ 32 ->
  find_fn ge (TAtom "__error_internal") = Some (Defined glibc_error_internal) ->
  (forall ap, call_frame glibc_error_internal
    [WInt status; WInt errnum; WPtr fmt; WPtr ap; WInt 0] = Some (internal_frame ap)) ->
  (forall ap, ⊢ error_va ap (WInt status :: WInt errnum :: WPtr fmt :: ys) -∗ R -∗
    WP (ERun (internal_frame ap) : gexpr) {{ v, ⌜v = RetVoid⌝ ∗ Q }}) ->
  R -∗ E -∗ ▷ (Q -∗ E -∗
    WP (ERun (mkFrame f e ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
    (Exec l (Call CVoid (Global (TAtom "error")) args :: rest) j)) : gexpr) {{ Φ }}.
Proof using Type.
  intros Hargs Hpublic Hys Hstatus Herrnum Hfn Hframe Hcall. iIntros "HR HE HK".
  iApply wp_call_bind; [exact Hargs | exact Hpublic | apply error_call_frame |]. iNext.
  iApply (wp_error_wrapper with "HR HE"); try eassumption.
  iNext. iIntros "HQ HE". iExists (mkFrame f e ls None (Exec l rest j)).
  iSplit; [done |]. iNext. iApply ("HK" with "HQ HE").
Qed.

End rules.
