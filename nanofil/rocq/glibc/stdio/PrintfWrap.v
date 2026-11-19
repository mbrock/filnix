(** A program prints with `c: fprintf` and `c: printf`. Each of the
    two is a few instructions around one call of glibc's formatter,
    `c: __vfprintf_internal`. This module proves that the two compiled
    functions are safe to call, provided the formatter is. A caller of
    `c: fprintf` or `c: printf` can then use this module and needs no
    fact about the formatter itself. The two statements are the
    contracts [fprintf_spec] and [printf_spec] of
    [PrintfSpec](PrintfSpec.v), and the assumption about the formatter
    is its contract [vfprintf_spec].

    Both functions take a variable number of arguments. On entry such
    a function gets a read-only copy of all its arguments. It
    allocates a small object, the cursor, stores in it a pointer past
    the named arguments in the copy, and hands the cursor to the
    formatter. The proofs follow these steps in order.

    A program calls the two functions on a stream that nobody has
    locked. The formatter may also run on a stream that its caller has
    locked, as it does for the error messages of `c: getopt`. So each
    proof shows before the call that the unlocked stream is one that
    the formatter accepts. After the call it shows that the stream is
    unlocked as before. *)

From Glibc Require Import Unit_stdioZ2dcommon_fprintf_os Unit_stdioZ2dcommon_printf_os.
From Glibc Require Import GlibcProgram GlibcSpec GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic
  VariadicLogic.
From Glibc Require Import Fix OsBlocks OsWorld FileInv FileIdle LibioLogic LibioCloseSteps LibioFputsSpec WordString
  FxprintfStream FileTidy NarrowFormat NarrowArgs PrintfSpec.
Module WrapVL := VariadicLogicOn R LG0.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic
  LibioCloseSteps WrapVL.
Open Scope string_scope.
Open Scope list_scope.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

Section wrap.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context `{Hvf : !HasSpec registry (os_wi w0) ge (TAtom "__vfprintf_internal") vfprintf_spec}.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** ## The argument cursor *)

(** The formatter reads its arguments through a cursor, and its
    contract asks for the cursor in the form of the predicate [va_at].
    Each wrapper builds the cursor in two steps. It allocates an
    object, and it stores a pointer into the entry copy in the object's
    first cell. The lemma [va_at_intro] puts the pieces together. It
    takes the lifetime of the object, that first cell and the copy, and
    it gives [va_at]. The stored pointer is skip bytes past the start
    of the copy, and skip must not exceed the size of the copy. *)
Lemma va_at_intro cb sb skip xs :
  0 < cb /\ cb mod 8 = 0 /\ cb + 32 <= 2 ^ 48 -> 0 < sb /\ sb mod 16 = 0 /\ sb + req_extent (fx_req xs) <= 2 ^ 48 ->
  0 <= skip -> skip <= 8 * Z.of_nat (length xs) ->
  live cb (mkRegion cb (cb + 32) Heap Live) -∗
  pcell cb 0 (mkPtr ((ptr_addr (mkPtr sb (Ro sb)) + skip) mod 2 ^ 64) (ptr_cap (mkPtr sb (Ro sb)))) -∗
  pts (snapshot_ps xs sb (fx_req xs)) -∗
  va_at (mkPtr cb (Obj cb)) skip xs.
Proof using Type.
  intros (Hcb & Hc8 & Hcend) (Hsb & Hmod & Hend) Hs0 Hs1. iIntros "Hcl Hcc Hsnap".
  pose proof (heap_req_extent 16 (8 * Z.of_nat (length xs))) as Hext. unfold fx_req in Hend.
  assert (Hva : (ptr_addr (mkPtr sb (Ro sb)) + skip) mod 2 ^ 64 = sb + skip) by (cbn; apply Z.mod_small; lia).
  rewrite Hva. iExists cb, sb. iSplit; [iPureIntro; split_and!; [reflexivity | first [assumption | lia]..]|].
  iSplitR "Hsnap"; [|iExact "Hsnap"].
  replace (va_cursor_ps cb (mkRegion cb (cb + 32) Heap Live) (mkPtr (sb + skip) (Ro sb))) with
    ([(PLive cb, VLive (mkRegion cb (cb + 32) Heap Live))] ++
     ((PAux cb 0, VAux (Ro sb)) :: cell cb 0 (sb + skip)))%list by reflexivity.
  rewrite pts_app. iFrame "Hcl Hcc".
Qed.

(** The tactic [cursor_alloc] cb runs the allocation of the cursor
    object. It names the object cb and leaves the object's lifetime in
    Hcl and its first cell, which holds null, in Hcc. *)
Ltac cursor_alloc cb :=
  iApply wp_alloc; [vm_compute; reflexivity | vm_compute; congruence | vm_compute; congruence |
    intros ? ? ? ? Hf Hw; exact (os_wi_alloc w0 _ _ _ _ _ Hf Hw) |];
  let H := fresh "Hc" in
  iNext; iIntros (cb H) "Hobj";
  change (0 < cb /\ cb mod 16 = 0 /\ cb + 32 <= 2 ^ 48) in H; destruct H as (Hcb & Hcmod & Hcend);
  assert (Hc8 : cb mod 8 = 0) by (Z.div_mod_to_equations; lia);
  iDestruct (obj_zero_block with "Hobj") as "(Hcl & Hx & Ha)"; [compute; discriminate |];
  iAssert (live cb (mkRegion cb (cb + 32) Heap Live)) with "Hcl" as "Hcl";
  iDestruct (zero_cell_prefix cb 0 24 with "Hx Ha") as "(Hcc & _ & _)".

(** ## The two wrappers *)

(** A caller of `c: fprintf` uses this lemma. The lemma says that the
    compiled function is safe on an idle stream with a format and
    arguments that meet [pf_fits], and that the stream is idle again
    afterwards. The program may know the function under either of its
    two names, so the lemma holds for any name n that the program
    gives this code. *)
Lemma fprintf_has_spec (n : string) `{!Defines ge n Unit_stdioZ2dcommon_fprintf_os.fn___fprintf} :
  HasSpec registry (os_wi w0) ge (TAtom n) fprintf_spec.
Proof using Hvf.
  intros x. exists Unit_stdioZ2dcommon_fprintf_os.fn___fprintf. split; [exact defines|]. split; [eexists; reflexivity|].
  intros fr Φ Hfr. injection Hfr as <-. cbn [fs_pre fs_post fs_args fprintf_spec].
  iIntros "[%Hfit Hpre] HK".
  destruct x as [vb fp fd fmt dq bytes ds ys rest eb]. destruct Hfit as (Hp & Hfits & Hys & Herr & Hfd & Hge).
  unfold pf_pre, pf_post. cbn [pf_vb pf_fp pf_fd pf_fmt pf_dq pf_bytes pf_ds pf_ys pf_rest pf_eb] in *.
  iDestruct "Hpre" as "(Hst & Hf & Hargs & He & #Hro & #Hfro & #Hmro)".
  iApply WrapVL.wp_snapshot; [discriminate | cbn; exact Hys |
    intros ? ? ? ? Hf Hw; exact (os_wi_snapshot _ _ _ _ _ _ _ Hf Hw) |].
  iNext. iIntros (sb Hsnap) "Hsnap".
  step. cursor_alloc cb.
  iApply WrapVL.wp_va_args; [reflexivity |]. iNext. check "Hcl". store "Hcl" "Hcc".
  iDestruct (va_at_intro cb sb 16 (WPtr fp :: WPtr fmt :: ys) with "Hcl Hcc Hsnap") as "Hva";
    [split_and!; assumption | exact Hsnap | lia | cbn [length]; lia |].
  iDestruct (file_idle_tidy with "Hst") as (flags2 Hbits) "Hst".
  iApply (wp_call_spec registry (os_wi w0) ge _ vfprintf_spec
    (VfpIn vb fp fd flags2 None fmt dq bytes ds (mkPtr cb (Obj cb)) 16 (WPtr fp :: WPtr fmt :: ys) rest eb)
    with "[Hst Hf Hva Hargs He]"); [reflexivity | |].
  - cbn [fs_pre vfprintf_spec]. unfold vfp_fits.
    cbn [vi_vb vi_fp vi_fd vi_flags2 vi_held vi_fmt vi_dq vi_bytes vi_ds vi_ap vi_skip vi_xs vi_rest vi_eb].
    change (skipn (Z.to_nat (16 / 8)) (WPtr fp :: WPtr fmt :: ys)) with ys.
    iFrame "Hst Hf Hva Hargs He Hro Hfro Hmro". iPureIntro.
    split_and!; [exact Hp | exact Hfits | lia | reflexivity | exact Herr | exact Hfd | exact Hge].
  - iIntros (v). cbn [fs_post vfprintf_spec vi_vb vi_fp vi_fd vi_flags2 vi_held vi_fmt vi_dq vi_bytes vi_eb].
    iIntros "(%r & [-> %Hr] & Hst & Hf & He)". iExists _. iSplit; [iPureIntro; reflexivity|]. iNext.
    cbn. iApply wp_ret; [reflexivity | vx |]. iNext. iApply "HK".
    iExists r. iSplit; [iPureIntro; split; [rewrite !(Z.mod_small r); [reflexivity | lia..] | lia]|]. iFrame "Hf He".
    iApply file_idle_tidy. iExists flags2. iSplit; [done|]. iExact "Hst".
Qed.

(** A caller of `c: printf` uses this lemma. The compiled function
    reads the global `c: stdout` to find its stream, and then it does
    what `c: fprintf` does. Loading the pointer to the stream needs the
    stream's object to be alive, so the proof borrows the stream's
    lifetime for that one instruction. *)
Lemma printf_has_spec (n : string) `{!Defines ge n Unit_stdioZ2dcommon_printf_os.fn___printf} :
  HasSpec registry (os_wi w0) ge (TAtom n) printf_spec.
Proof using Hvf.
  intros [dqo x]. exists Unit_stdioZ2dcommon_printf_os.fn___printf. split; [exact defines|]. split; [eexists; reflexivity|].
  intros fr Φ Hfr. injection Hfr as <-. cbn [fs_pre fs_post fs_args printf_spec].
  iIntros "(%Hfit & Hso & Hpre) HK".
  destruct x as [vb fp fd fmt dq bytes ds ys rest eb]. destruct Hfit as (Hp & Hfits & Hys & Herr & Hfd & Hge).
  unfold pf_pre, pf_post. cbn [pf_vb pf_fp pf_fd pf_fmt pf_dq pf_bytes pf_ds pf_ys pf_rest pf_eb] in *.
  iDestruct "Hpre" as "(Hst & Hf & Hargs & He & #Hro & #Hfro & #Hmro)".
  iDestruct "Hso" as (so soreg (Hgso & Hso8 & Hsoend)) "[Hsol Hsoc]".
  iApply (wp_live_fit with "Hsol"). iIntros ([Hso0 Hso48]) "Hsol".
  iApply WrapVL.wp_snapshot; [discriminate | cbn; exact Hys |
    intros ? ? ? ? Hf Hw; exact (os_wi_snapshot _ _ _ _ _ _ _ Hf Hw) |].
  iNext. iIntros (sb Hsnap) "Hsnap".
  step. cursor_alloc cb.
  iApply WrapVL.wp_va_args; [reflexivity |]. iNext. check "Hcl". store "Hcl" "Hcc".
  iDestruct (va_at_intro cb sb 8 (WPtr fmt :: ys) with "Hcl Hcc Hsnap") as "Hva";
    [split_and!; assumption | exact Hsnap | lia | cbn [length]; lia |].
  step_global Hgso.
  check_read_dq "Hsol" by a2. iNext. iIntros "Hsol".
  iDestruct (file_idle_tidy with "Hst") as (flags2 Hbits) "Hst".
  iDestruct (file_tidy_live with "Hst") as (fb freg [-> Hfb]) "[Hfl Hclose]".
  iApply (wp_raw_load_pointer_dq with "Hsol Hsoc Hfl"); [reflexivity | vx | left; reflexivity | a2 | a2 | cbn; lia |].
  iNext. iIntros "Hsol Hsoc Hfl". iDestruct ("Hclose" with "Hfl") as "Hst".
  iApply (wp_call_spec registry (os_wi w0) ge _ vfprintf_spec
    (VfpIn vb (mkPtr fb (Obj fb)) fd flags2 None fmt dq bytes ds (mkPtr cb (Obj cb)) 8 (WPtr fmt :: ys) rest eb)
    with "[Hst Hf Hva Hargs He]"); [reflexivity | |].
  - cbn [fs_pre vfprintf_spec]. unfold vfp_fits.
    cbn [vi_vb vi_fp vi_fd vi_flags2 vi_held vi_fmt vi_dq vi_bytes vi_ds vi_ap vi_skip vi_xs vi_rest vi_eb].
    change (skipn (Z.to_nat (8 / 8)) (WPtr fmt :: ys)) with ys.
    iFrame "Hst Hf Hva Hargs He Hro Hfro Hmro". iPureIntro.
    split_and!; [exact Hp | exact Hfits | lia | reflexivity | exact Herr | exact Hfd | exact Hge].
  - iIntros (v). cbn [fs_post vfprintf_spec vi_vb vi_fp vi_fd vi_flags2 vi_held vi_fmt vi_dq vi_bytes vi_eb].
    iIntros "(%r & [-> %Hr] & Hst & Hf & He)". iExists _. iSplit; [iPureIntro; reflexivity|]. iNext.
    cbn. iApply wp_ret; [reflexivity | vx |]. iNext. iApply "HK".
    iSplitL "Hsol Hsoc"; [iExists so, soreg; iFrame "Hsol Hsoc"; done|].
    iExists r. iSplit; [iPureIntro; split; [rewrite !(Z.mod_small r); [reflexivity | lia..] | lia]|]. iFrame "Hf He".
    iApply file_idle_tidy. iExists flags2. iSplit; [done|]. iExact "Hst".
Qed.

End wrap.
