(** The orientation in `c: puts(s)` (LibioPutsCode.v,
    libio/ioputs.c), with stdout's lock held:
    `c: _IO_fwide(stdout, -1)` makes an unoriented stream narrow,
    `c: _mode` 0 becoming -1, and a narrow stream's string is written
    by LibioPutsCall.v's [wp_puts_L162]; a wide stream, `c: _mode` 1,
    skips the write, and block `c: L163` is reached with its flag
    `c: v179` 0 ([wp_puts_L109]). *)

From Glibc Require Import GlibcTactics LibioTactics.
From Glibc Require Import GlibcEnv.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry FileInv LibioLogic SysWrappers LibioCloseSteps
  WordString LibioXsputnCode LibioPutsCode LibioPutsInv LibioPutsLock LibioPutsUnlock LibioPutsCall.
From Glibc Require FileInv LibioCloseSteps LibioLogic LibioPutsCall LibioPutsInv LibioPutsLock LibioPutsUnlock OsWorld SysWrappers.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The mode `c: _IO_fwide(fp, -1)` leaves: -1 for 0, else the same. *)
Definition oriented (mode : Z) : Z := if mode =? 0 then 2 ^ 32 - 1 else mode.


Import LibioPutsCall LibioPutsUnlock LibioPutsLock LibioPutsInv SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic LibioCloseSteps.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
Context (vb : Z) (vreg : region) (Rx : iProp Σ).
Context (F : ptr -> Z -> option Z -> iProp Σ).
Context (G : list Z -> ptr -> Z -> option Z -> iProp Σ).
Context (Hopen : forall fp mode held, F fp mode held ⊢ file_open vb (ow_self w0) F fp mode held).
Context (Hwide : forall s fp held, F fp 1 held ⊢ G s fp 1 held).
Context (Hxs_fn : ge_fn ge "_IO_new_file_xsputn" glibc__IO_new_file_xsputn).
Context (Hxs : xsputn_spec_for w0 registry ge F G Rx).

(** The Iris instance for registry and [os_wi] w0. *)
Local Instance puts_mode_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.

(** Expressions of the language. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** Block `c: L109` of `c: puts`, stdout fb at any mode with its lock
    held once: an unoriented stream's `c: _mode` becomes -1, a narrow
    one's string is written by [wp_puts_L162], and block `c: L163` is
    reached with the stream at its [oriented] mode, its flag
    `c: v179` 0 for a wide stream. *)
Lemma wp_puts_L109_for e p dq s so soreg fb mode Φ :
  let fp := mkPtr fb (Obj fb) in
  lookup (TAtom "v0") e = Some (WPtr p) -> lookup (TAtom "v6") e = Some (WInt (Z.of_nat (length s))) ->
  lookup (TAtom "v12") e = Some (WPtr fp) -> lookup (TAtom "chk1") e = Some (WPtr fp) ->
  lookup (TAtom "stdout") (ge_globals ge) = Some (mkPtr so (Obj so)) -> so mod 8 = 0 -> so + 8 <= r_end soreg ->
  vtables_ro ge vb vreg -∗ live so soreg -∗ pcell so 0 fp -∗
  F fp mode (Some 0) -∗ word_string dq p s -∗ Rx -∗
  ▷ (∀ e' c, ⌜keeps (atoms ["v0"; "v6"; "v12"; "chk1"]) e e' /\ lookup (TAtom "v179") e' = Some (WInt c) /\
              (c <> 0 -> oriented mode = 2 ^ 32 - 1)⌝ -∗
     live so soreg -∗ pcell so 0 fp -∗ G s fp (oriented mode) (Some 0) -∗
     word_string dq p s -∗ Rx -∗
     WP (ERun (mkFrame glibc__IO_puts e' [] None (Exec (TAtom "L163") [] pu_j163)) : sexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame glibc__IO_puts e [] None (Enter (TAtom "L109") (Some (TAtom "L25")))) : sexpr) {{ Φ }}.
Proof.
  intros fp Hv0 Hv6 Hv12 Hc1 Hgso Hsoal Hsoend. subst fp.
  iIntros "#Hvt Hso Hsoc Hf Hstr HRx HK".
  iDestruct (Hopen with "Hf") as (fb' freg fl lb vt) "(%Hp & Hl & Hfl & Hlp & Hlk & Hmd & Hvtp & Hcl)".
  destruct Hp as (Hfp & Hfb & Hfal & Hfend & Hfreg & Hflr & Hul & Hmv). injection Hfp as <-.
  unfold file_size in Hfend.
  iApply (wp_live_fit1 w0 registry ge with "Hl"). iIntros ([Hf0 Hf48]) "Hl".
  iApply (wp_live_fit1 w0 registry ge with "Hso"). iIntros ([Hso0 Hso48]) "Hso".
  iDestruct "Hmd" as "[%Hmr Hmd]".
  (* L109: the mode. *)
  step. step. check "Hso". load "Hso" "Hsoc" "Hl". step. check "Hl". load_s32 "Hl" "Hmd". step.
  destruct Hmv as [[[-> | ->] ->] | [-> ->]].
  - (* Unoriented: L119 makes it -1, and L121 finds it narrow. *)
    branch. step. step. check "Hso". load "Hso" "Hsoc" "Hl". step. check "Hl". store_int "Hl" "Hmd". step.
    step. step. check "Hso". load "Hso" "Hsoc" "Hl". step. check "Hl".
    change (4294967295 mod 2 ^ 32) with (2 ^ 32 - 1). assert (Hm1 : 0 <= 2 ^ 32 - 1 < 2 ^ 32) by lia.
    load_s32 "Hl" "Hmd". step. branch.
    iDestruct ("Hcl" $! (2 ^ 32 - 1) (Some 0) with "[%] Hl Hfl Hlp Hlk [$Hmd //] Hvtp") as "Hf";
      [left; split; [right; reflexivity | reflexivity]|].
    iApply (wp_puts_L162_for w0 registry ge vb vreg Rx F G Hopen Hxs_fn Hxs with "Hvt Hso Hsoc Hf Hstr HRx"); try close_side.
    iNext. iIntros (e' c [Hsame Hc]) "Hso Hsoc Hf Hstr HRx". rewrite keeps_forall in Hsame; cbn [atoms List.map List.In] in Hsame.
    iApply ("HK" with "[%] Hso Hsoc Hf Hstr HRx"). split; [|split; [exact Hc | reflexivity]].
    rewrite keeps_forall; cbn [atoms List.map List.In]; intros x Hx. rewrite (Hsame x Hx). destruct Hx as [<- | [<- | [<- | [<- | []]]]]; lookups; reflexivity.
  - (* Narrow: L121 finds it so. *)
    branch. step. step. check "Hso". load "Hso" "Hsoc" "Hl". step. check "Hl". load_s32 "Hl" "Hmd". step. branch.
    iDestruct ("Hcl" $! (2 ^ 32 - 1) (Some 0) with "[%] Hl Hfl Hlp Hlk [$Hmd //] Hvtp") as "Hf";
      [left; split; [right; reflexivity | reflexivity]|].
    iApply (wp_puts_L162_for w0 registry ge vb vreg Rx F G Hopen Hxs_fn Hxs with "Hvt Hso Hsoc Hf Hstr HRx"); try close_side.
    iNext. iIntros (e' c [Hsame Hc]) "Hso Hsoc Hf Hstr HRx". rewrite keeps_forall in Hsame; cbn [atoms List.map List.In] in Hsame.
    iApply ("HK" with "[%] Hso Hsoc Hf Hstr HRx"). split; [|split; [exact Hc | reflexivity]].
    rewrite keeps_forall; cbn [atoms List.map List.In]; intros x Hx. rewrite (Hsame x Hx). destruct Hx as [<- | [<- | [<- | [<- | []]]]]; lookups; reflexivity.
  - (* Wide: L121 skips the call, the flag 0. *)
    branch. step. step. check "Hso". load "Hso" "Hsoc" "Hl". step. check "Hl". load_s32 "Hl" "Hmd". step. branch.
    iDestruct ("Hcl" $! 1%Z (Some 0) with "[%] Hl Hfl Hlp Hlk [$Hmd //] Hvtp") as "Hf";
      [right; split; reflexivity|].
    iDestruct (Hwide s with "Hf") as "Hf".
    iApply wp_enter; [reflexivity | vx | iNext].
    iApply ("HK" with "[%] Hso Hsoc Hf Hstr HRx").
    split; [rewrite keeps_forall; cbn [atoms List.map List.In]; intros x Hx; destruct Hx as [<- | [<- | [<- | [<- | []]]]]; lookups; reflexivity | split; [lk_prove | done]].
Qed.

End rules.

(** Existing callers can still orient a generic stream before writing
    its string. This rule keeps the original precondition and
    postcondition of that step. *)
Definition wp_puts_L109 `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}
    w0 registry ge vb vreg Rx Hxs_fn (Hxs : xsputn_spec w0 registry ge vb Rx) :=
  wp_puts_L109_for w0 registry ge vb vreg Rx (file_at vb (ow_self w0))
    (fun _ => file_at vb (ow_self w0)) (file_at_open vb (ow_self w0))
    (fun _ _ _ => reflexivity _) Hxs_fn Hxs.

