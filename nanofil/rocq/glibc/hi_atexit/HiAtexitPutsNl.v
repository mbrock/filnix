(** Puts adds a newline only after the string write succeeds.
    The newline either fits in stdout's buffer or calls overflow.
    Both paths here preserve the buffer and stream resources that
    the later close callback needs, including when overflow fails. *)

From Glibc Require Import GlibcTactics LibioTactics.
From Glibc Require Import GlibcEnv.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry FileInv LibioLogic SysWrappers LibioCloseSteps
  LibioGenCode LibioPutsCode LibioPutsNl AllocLogic HiAtexitBase HiAtexitGe HiAtexitFns
  HiAtexitAlloc HiAtexitOutputState HiAtexitStdout HiAtexitPutsBuf.
From Glibc Require FileInv LibioCloseSteps LibioDefaultXsputnBuf LibioLogic LibioPutsInv LibioPutsLock LibioXsputnBase LibioXsputnSetp OsWorld SysWrappers.
Import ListNotations.
Open Scope Z_scope.

Import LibioPutsLock.
Import LibioPutsInv LibioCloseSteps SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.
Import LibioXsputnSetp.
Import LibioXsputnBase LibioDefaultXsputnBuf.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Opaque HiAtexitFns.hi_ge.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (dq : dfrac) (mp tc dummy : Z) (mpr tcr dr : region).
Context (Hmp : lookup (TAtom "malloc#mp_") (ge_globals hge) = Some (mkPtr mp (Obj mp)))
  (Htc : lookup (TAtom "tcache") (ge_globals hge) = Some (mkPtr tc (Obj tc))).

(** The newline runs in the linked environment and OS world. *)
Local Instance hi_puts_nl_irisGS : irisGS_gen hlc (nanofil_lang glibc_os_registry hge) Σ :=
  nanofil_irisGS glibc_os_registry (os_wi w0) hge.
Local Notation sexpr := (language.expr (nanofil_lang glibc_os_registry hge)).

(** The final puts composition supplies the linked overflow proof.
    Keeping that large dependency outside this block proof bounds
    its compilation time without assuming an unproved call rule. *)
Context (Hov : forall s fr fp eb vb vreg Φ,
  call_frame glibc___overflow [WPtr fp; WInt 10] = Some fr ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) ->
  vtables_ro hge vb vreg -∗ hi_stdout_after w0 eb vb s fp (Some 0) -∗
  hi_malloc_state dq mp tc dummy mpr tcr dr -∗
  ▷ (∀ r, ⌜r = 10 \/ r = 2 ^ 32 - 1⌝ -∗ hi_stdout_after w0 eb vb s fp (Some 0) -∗
     hi_malloc_state dq mp tc dummy mpr tcr dr -∗ Φ (Ret (WInt r))) -∗
  WP (ERun fr : sexpr) {{ Φ }}).

(** Unlocking can use the same stdout resources after either newline
    path. The branch flag records success, but both success and failure
    return the buffer, stream fields and allocator state. *)
Lemma hi_puts_L180 s e so soreg fb eb vb vreg Φ :
  lookup (TAtom "stdout") (ge_globals hge) = Some (mkPtr so (Obj so)) ->
  so mod 8 = 0 -> so + 8 <= r_end soreg -> ow_errno w0 = Some (mkPtr eb (Obj eb)) ->
  live so soreg -∗ pcell so 0 (mkPtr fb (Obj fb)) -∗
  hi_stdout_after w0 eb vb s (mkPtr fb (Obj fb)) (Some 0) -∗
  (vtables_ro hge vb vreg ∗ hi_malloc_state dq mp tc dummy mpr tcr dr) -∗
  ▷ (∀ e' c, ⌜keeps (atoms ["v0"; "v6"; "v12"; "chk1"]) e e' /\ lookup (TAtom "v208") e' = Some (WInt c)⌝ -∗
     live so soreg -∗ pcell so 0 (mkPtr fb (Obj fb)) -∗
     hi_stdout_after w0 eb vb s (mkPtr fb (Obj fb)) (Some 0) -∗
     (vtables_ro hge vb vreg ∗ hi_malloc_state dq mp tc dummy mpr tcr dr) -∗
     WP (ERun (mkFrame glibc__IO_puts e' [] None (Enter (TAtom "L181") (Some (TAtom "L184")))) : sexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame glibc__IO_puts e [] None (Enter (TAtom "L180") (Some (TAtom "L163")))) : sexpr) {{ Φ }}.
Proof.
  intros Hgso Hsoal Hsoend Heb.
  assert (Hsofixed : so = 70976) by (vm_compute in Hgso; congruence). subst so.
  iIntros "Hso Hsoc Hf [#Hvt HM] HK".
  iDestruct "Hf" as (fb' freg nb wp we lb (Hfp & Hfb & Hal & Hend & Hreg & Hlb & Hprogress))
    "(Hl & Hvtp & Hwb & Hxf & Htail)". injection Hfp as <-.
  iDestruct "Hwb" as "(Hcells & Hwp & Hwe & Hroom)".
  iDestruct (hi_room_bounds with "Hroom") as "[%Hbounds Hroom]".
  destruct Hbounds as [Hwr Her].
  iApply (wp_live_fit1 w0 glibc_os_registry hge with "Hl"). iIntros ([Hf0 Hf48]) "Hl".
  iApply (wp_live_fit1 w0 glibc_os_registry hge with "Hso"). iIntros ([Hso0 Hso48]) "Hso".
  unfold file_size in Hend.
  step. step. check "Hso". load "Hso" "Hsoc" "Hl". step. check "Hl".
  iApply (hi_load_bufptr w0 with "Hl Hwp Hroom"); [reflexivity | vx | reflexivity | a2 | a2 | left; reflexivity |].
  iNext. iIntros "Hl Hwp Hroom".
  step. check "Hso". load "Hso" "Hsoc" "Hl". step. check "Hl".
  iApply (hi_load_bufptr w0 with "Hl Hwe Hroom"); [reflexivity | vx | reflexivity | a2 | a2 | right; reflexivity |].
  iNext. iIntros "Hl Hwe Hroom". step. step. step.
  destruct (Z.ltb_spec (ptr_addr wp) (ptr_addr we)) as [Hlt | Hge].
  - branch_as true. step. step. check "Hso". load "Hso" "Hsoc" "Hl". step. check "Hl".
    iApply (hi_load_bufptr w0 with "Hl Hwp Hroom"); [reflexivity | vx | reflexivity | a2 | a2 | left; reflexivity |].
    iNext. iIntros "Hl Hwp Hroom". step. check "Hl". store "Hl" "Hwp".
    iApply (hi_buf_putc w0 with "Hroom"); [vx | exact Hlt |].
    iNext. iIntros "Hroom". step. step. step. step.
    iApply ("HK" with "[%] Hso Hsoc [Hl Hvtp Hcells Hwp Hwe Hroom Hxf Htail] [$Hvt $HM]").
    + split; [rewrite keeps_forall; cbn [atoms List.map List.In]; intros x Hx; destruct Hx as [<- | [<- | [<- | [<- | []]]]]; lookups; reflexivity | lk_prove].
    + iExists fb, freg, nb, (mkPtr (ptr_addr wp + 1) (ptr_cap wp)), we, lb.
      iSplitR; [iPureIntro; tauto|]. iFrame "Hl Hvtp Hxf Htail".
      unfold wbuf. iFrame "Hcells Hwe Hroom".
      unfold raw_address. unwrap2. done.
  - branch_as false. step. step. check "Hso". load "Hso" "Hsoc" "Hl".
    iApply wp_call_bind; [vx | exact (hi_find___GI___overflow _) | reflexivity |]. iNext.
    iApply (Hov s with
      "Hvt [Hl Hvtp Hcells Hwp Hwe Hroom Hxf Htail] HM"); [reflexivity | exact Heb | |].
    { iExists fb, freg, nb, wp, we, lb. iSplitR; [iPureIntro; unfold file_size; tauto|].
      iFrame "Hl Hvtp Hxf Htail". unfold wbuf. iFrame "Hcells Hwp Hwe Hroom". }
    iNext. iIntros (r Hr) "Hf HM". resume. step. step. step. step.
    iApply ("HK" with "[%] Hso Hsoc Hf [$Hvt $HM]").
    split; [rewrite keeps_forall; cbn [atoms List.map List.In]; intros x Hx; destruct Hx as [<- | [<- | [<- | [<- | []]]]]; lookups; reflexivity | lk_prove].
Qed.

End rules.
