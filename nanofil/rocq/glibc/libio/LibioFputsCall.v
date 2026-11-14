(** The middle of `c: fputs(s, fp)` (LibioPutsCode.v,
    libio/iofputs.c), with the stream's lock held:

    ```c
    if ((_IO_vtable_offset (fp) != 0 || _IO_fwide (fp, -1) == -1)
        && _IO_sputn (fp, str, len) == len)
      result = 1;
    ```

    `c: _IO_fwide(fp, -1)` makes an unoriented stream narrow, its
    `c: _mode` 0 becoming -1, and a narrow stream's string goes to the
    jump table's `c: _IO_new_file_xsputn` ([wp_fputs_L161]), whose
    triple is LibioPutsInv.v's hypothesis [xsputn_spec]; a wide stream,
    `c: _mode` 1, skips the write ([wp_fputs_L113]). Both reach block
    `c: L162`, whose flag `c: v176` is nonzero only when the call wrote
    the whole string. The code is LibioPutsMode.v's and
    LibioPutsCall.v's for `c: puts`, with the stream the argument
    `c: v2` instead of `c: stdout`'s pointer. *)

From Glibc Require Import GlibcTactics LibioTactics.
From Glibc Require Import GlibcEnv.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry FileInv LibioLogic SysWrappers LibioCloseSteps
  WordString LibioXsputnCode LibioPutsCode LibioPutsInv LibioPutsMode LibioFputsLock LibioFputsUnlock.
From Glibc Require FileInv LibioCloseSteps LibioFputsLock LibioFputsUnlock LibioLogic LibioPutsInv OsWorld SysWrappers.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The jump of block `c: L162` of `c: fputs`, on the flag `c: v176`. *)
Definition fp_j162 : jump := JBranch (Tmp (TAtom "v176")) (To (TAtom "L107")) (To (TAtom "L106")).


Import LibioFputsUnlock LibioFputsLock LibioPutsInv SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic LibioCloseSteps.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
Context (vb : Z) (vreg : region) (Rx : iProp Σ).
Context (Hxs_fn : ge_fn ge "_IO_new_file_xsputn" glibc__IO_new_file_xsputn).
Context (Hxs : xsputn_spec w0 registry ge vb Rx).

(** The Iris instance for registry and [os_wi] w0. *)
Local Instance fputs_call_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.

(** Expressions of the language. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** Block `c: L161` of `c: fputs` on, the stream fb at mode -1 with its
    lock held once: the jump table is checked, its `c: xsputn` slot
    called on the string, and block `c: L162` reached, its flag
    `c: v176` whatever the count makes it. *)
Lemma wp_fputs_L161 e p dq s fb Φ :
  let fp := mkPtr fb (Obj fb) in
  lookup (TAtom "v0") e = Some (WPtr p) -> lookup (TAtom "v6") e = Some (WInt (Z.of_nat (length s))) ->
  lookup (TAtom "v2") e = Some (WPtr fp) -> lookup (TAtom "chk0") e = Some (WPtr fp) ->
  vtables_ro ge vb vreg -∗ file_at vb (ow_self w0) fp (2 ^ 32 - 1) (Some 0) -∗ word_string dq p s -∗ Rx -∗
  ▷ (∀ e' c, ⌜keeps (atoms ["v0"; "v6"; "v2"; "chk0"]) e e' /\ lookup (TAtom "v176") e' = Some (WInt c)⌝ -∗
     file_at vb (ow_self w0) fp (2 ^ 32 - 1) (Some 0) -∗ word_string dq p s -∗ Rx -∗
     WP (ERun (mkFrame glibc__IO_fputs e' [] None (Exec (TAtom "L162") [] fp_j162)) : sexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame glibc__IO_fputs e [] None (Enter (TAtom "L161") (Some (TAtom "L125")))) : sexpr) {{ Φ }}.
Proof.
  intros fp Hv0 Hv6 Hv2 Hc0. subst fp.
  iIntros "#Hvt Hf Hstr HRx HK".
  iDestruct (word_string_len with "Hstr") as %Hlen.
  iDestruct (file_at_open with "Hf") as (fb' freg fl lb vt) "(%Hp & Hl & Hfl & Hlp & Hlk & Hmd & Hvtp & Hcl)".
  destruct Hp as (Hfp & Hfb & Hfal & Hfend & Hfreg & Hflr & Hul & Hmv). injection Hfp as <-.
  unfold file_size in Hfend.
  rewrite (mode_vtable_narrow _ _ Hmv); [|lia].
  iPoseProof (vtables_slot ge vb vreg slot_xsputn "_IO_new_file_xsputn" with "Hvt") as "#Hsx"; [cbn; tauto|].
  iAssert (live_capq DfracDiscarded (ptr_cap (sym_ptr ge "_IO_new_file_xsputn")) vreg) as "Hfc".
  { rewrite (ge_fn_cap _ _ _ Hxs_fn). done. }
  iDestruct "Hvt" as "((%Hvg & %Hvend & %Hval & %Hvb & %Hvreg) & Hvl & Hslots)".
  unfold io_vtables_size in Hvend.
  iApply (wp_live_fit1 w0 registry ge with "Hl"). iIntros ([Hf0 Hf48]) "Hl".
  (* L161: the stream's jump table, within `c: __io_vtables`. *)
  step. step. check "Hl".
  iApply (wp_raw_load_pointer_dq with "Hl Hvtp Hvl");
    [reflexivity | vx | left; reflexivity | a2 | a2 | cbn; unfold vt_file; lia |].
  iNext. iIntros "Hl Hvtp #Hvl'". step. step. step. step. step. branch_as true.
  (* iw_1.join: the `c: xsputn` slot, called on the stream, the string and its length. *)
  step. step.
  iApply (wp_check_read_dq registry (os_wi w0) ge with "Hvl'"); [reflexivity | vx | right; reflexivity | a2 | a2 | a2 |].
  iNext. iIntros "_".
  iApply (wp_raw_load_pointer_dq with "Hvl' Hsx Hfc");
    [reflexivity | vx | right; reflexivity | a2 | a2 | apply (ge_fn_addr _ _ _ Hxs_fn) |].
  iNext. iIntros "_ _ _".
  iApply wp_check_function; [vx | apply (ge_fn_check _ _ _ Hxs_fn) |]. iNext.
  iApply wp_raw_call_bind; [vx | apply (ge_fn_cap _ _ _ Hxs_fn) | apply (ge_fn_check _ _ _ Hxs_fn) | vx |
    apply (ge_fn_find _ _ _ Hxs_fn) | reflexivity | reflexivity |].
  iNext. rewrite (Z.mod_small (Z.of_nat (length s)) (2 ^ 64)); [|lia].
  iDestruct ("Hcl" $! (2 ^ 32 - 1) (Some 0) with "[%] Hl Hfl Hlp Hlk Hmd Hvtp") as "Hf";
    [left; split; [right; reflexivity | reflexivity]|].
  iApply (Hxs with "Hf Hstr HRx"); [reflexivity|].
  iNext. iIntros (r Hr) "Hf Hstr HRx". resume.
  step. step. iApply wp_enter; [reflexivity | vx | iNext].
  iApply ("HK" with "[%] Hf Hstr HRx").
  split; [rewrite keeps_forall; cbn [atoms List.map List.In]; intros x Hx; destruct Hx as [<- | [<- | [<- | [<- | []]]]]; lookups; reflexivity | lk_prove].
Qed.

(** Block `c: L113` of `c: fputs`, the stream fb at any mode with its
    lock held once: an unoriented stream's `c: _mode` becomes -1, a
    narrow one's string is written by [wp_fputs_L161], and block
    `c: L162` is reached with the stream at its [oriented] mode, its
    flag `c: v176` 0 for a wide stream. *)
Lemma wp_fputs_L113 e p dq s fb mode Φ :
  let fp := mkPtr fb (Obj fb) in
  lookup (TAtom "v0") e = Some (WPtr p) -> lookup (TAtom "v6") e = Some (WInt (Z.of_nat (length s))) ->
  lookup (TAtom "v2") e = Some (WPtr fp) -> lookup (TAtom "chk0") e = Some (WPtr fp) ->
  vtables_ro ge vb vreg -∗ file_at vb (ow_self w0) fp mode (Some 0) -∗ word_string dq p s -∗ Rx -∗
  ▷ (∀ e' c, ⌜keeps (atoms ["v0"; "v6"; "v2"; "chk0"]) e e' /\ lookup (TAtom "v176") e' = Some (WInt c)⌝ -∗
     file_at vb (ow_self w0) fp (oriented mode) (Some 0) -∗ word_string dq p s -∗ Rx -∗
     WP (ERun (mkFrame glibc__IO_fputs e' [] None (Exec (TAtom "L162") [] fp_j162)) : sexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame glibc__IO_fputs e [] None (Enter (TAtom "L113") (Some (TAtom "L29")))) : sexpr) {{ Φ }}.
Proof.
  intros fp Hv0 Hv6 Hv2 Hc0. subst fp.
  iIntros "#Hvt Hf Hstr HRx HK".
  iDestruct (file_at_open with "Hf") as (fb' freg fl lb vt) "(%Hp & Hl & Hfl & Hlp & Hlk & Hmd & Hvtp & Hcl)".
  destruct Hp as (Hfp & Hfb & Hfal & Hfend & Hfreg & Hflr & Hul & Hmv). injection Hfp as <-.
  unfold file_size in Hfend.
  iApply (wp_live_fit1 w0 registry ge with "Hl"). iIntros ([Hf0 Hf48]) "Hl".
  iDestruct "Hmd" as "[%Hmr Hmd]".
  (* L113: the mode. *)
  step. step. check "Hl". load_s32 "Hl" "Hmd". step.
  destruct Hmv as [[[-> | ->] ->] | [-> ->]].
  - (* Unoriented: L123 makes it -1, and L125 finds it narrow. *)
    branch. step. step. check "Hl". store_int "Hl" "Hmd". step.
    step. step. change (4294967295 mod 2 ^ 32) with (2 ^ 32 - 1). assert (Hm1 : 0 <= 2 ^ 32 - 1 < 2 ^ 32) by lia.
    load_s32 "Hl" "Hmd". step. branch.
    iDestruct ("Hcl" $! (2 ^ 32 - 1) (Some 0) with "[%] Hl Hfl Hlp Hlk [$Hmd //] Hvtp") as "Hf";
      [left; split; [right; reflexivity | reflexivity]|].
    iApply (wp_fputs_L161 with "Hvt Hf Hstr HRx"); try close_side.
    iNext. iIntros (e' c [Hsame Hc]) "Hf Hstr HRx". rewrite keeps_forall in Hsame; cbn [atoms List.map List.In] in Hsame.
    iApply ("HK" with "[%] Hf Hstr HRx"). split; [|exact Hc].
    rewrite keeps_forall; cbn [atoms List.map List.In]; intros x Hx. rewrite (Hsame x Hx). destruct Hx as [<- | [<- | [<- | [<- | []]]]]; lookups; reflexivity.
  - (* Narrow: L125 finds it so. *)
    branch. step. step. load_s32 "Hl" "Hmd". step. branch.
    iDestruct ("Hcl" $! (2 ^ 32 - 1) (Some 0) with "[%] Hl Hfl Hlp Hlk [$Hmd //] Hvtp") as "Hf";
      [left; split; [right; reflexivity | reflexivity]|].
    iApply (wp_fputs_L161 with "Hvt Hf Hstr HRx"); try close_side.
    iNext. iIntros (e' c [Hsame Hc]) "Hf Hstr HRx". rewrite keeps_forall in Hsame; cbn [atoms List.map List.In] in Hsame.
    iApply ("HK" with "[%] Hf Hstr HRx"). split; [|exact Hc].
    rewrite keeps_forall; cbn [atoms List.map List.In]; intros x Hx. rewrite (Hsame x Hx). destruct Hx as [<- | [<- | [<- | [<- | []]]]]; lookups; reflexivity.
  - (* Wide: L125 skips the call, the flag 0. *)
    branch. step. step. load_s32 "Hl" "Hmd". step. branch.
    iDestruct ("Hcl" $! 1%Z (Some 0) with "[%] Hl Hfl Hlp Hlk [$Hmd //] Hvtp") as "Hf";
      [right; split; reflexivity|].
    iApply wp_enter; [reflexivity | vx | iNext].
    iApply ("HK" with "[%] Hf Hstr HRx").
    split; [rewrite keeps_forall; cbn [atoms List.map List.In]; intros x Hx; destruct Hx as [<- | [<- | [<- | [<- | []]]]]; lookups; reflexivity | lk_prove].
Qed.

End rules.
