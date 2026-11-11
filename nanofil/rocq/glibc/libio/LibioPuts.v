(** The triple of `c: puts(s)` (LibioPutsCode.v, libio/ioputs.c)
    over a string at any share and stdout as LibioPutsInv.v's
    [file_at] has it ([wp_glibc__IO_puts]):

    ```c
    size_t len = strlen (str);
    _IO_acquire_lock (stdout);
    if ((_IO_vtable_offset (stdout) != 0 || _IO_fwide (stdout, -1) == -1)
        && _IO_sputn (stdout, str, len) == len
        && _IO_putc_unlocked ('\n', stdout) != EOF)
      result = MIN (INT_MAX, len + 1);
    _IO_release_lock (stdout);
    return result;
    ```

    Each part of the function is proved in its own file, and this
    file adds the three branches between them and puts the parts
    together. The two calls the function makes through the jump table
    and by name stay hypotheses of LibioPutsInv.v.

    | Part | Blocks | File |
    |---|---|---|
    | the length and the lock | start to `c: L25` | LibioPutsLock.v |
    | the orientation | `c: L109` to `c: L121` | LibioPutsMode.v |
    | the write, `c: _IO_sputn` | `c: L162` | LibioPutsCall.v, over [xsputn_spec] |
    | the newline | `c: L180` to `c: L184` | LibioPutsNl.v, over [overflow_spec] |
    | the count, at most `c: INT_MAX` | `c: L101`, `c: L212` | here |
    | the release | `c: L103` | LibioPutsUnlock.v | *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry FileInv LibioLogic SysWrappers LibioCloseSteps
  WordString StrlenLogic LibioGenCode LibioXsputnCode LibioPutsCode LibioPutsInv LibioPutsLock LibioPutsUnlock
  LibioPutsCall LibioPutsMode LibioPutsBuf LibioPutsNl.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** What `c: puts` returns for a string of length n: the count with
    the newline, at most `c: INT_MAX`, or `c: EOF`. *)
Definition puts_ret (n r : Z) : Prop := r = Z.min (n + 1) 2147483647 \/ r = 2 ^ 32 - 1.

(** The triples over the [[runtime]] R and [LogicSig] LG0. *)
Module LibioPutsOn (R : Runtime) (LG0 : LogicSig R).
Module PN := LibioPutsNlOn R LG0.
Import PN PN.PB PN.PB.PM PN.PB.PM.PC PN.PB.PM.PC.PU PN.PB.PM.PC.PU.PL PN.PB.PM.PC.PU.PL.PI
  PN.PB.PM.PC.PU.PL.PI.CS PN.PB.PM.PC.PU.PL.PI.CS.SW PN.PB.PM.PC.PU.PL.PI.CS.SW.FI.ML
  PN.PB.PM.PC.PU.PL.PI.CS.SW.FI.LG PN.PB.PM.PC.PU.PL.PI.CS.SW.FI.L PN.PB.PM.PC.PU.PL.PI.CS.SW.OW
  PN.PB.PM.PC.PU.PL.PI.CS.SW.FI PN.PB.PM.PC.PU.PL.PI.CS.SW.ST.

(** A lookup of the goal, through its environment's [put]s, of a value
    equal to the one asked for by arithmetic. *)
Ltac lk_val :=
  first [lk_prove | lookups; first [reflexivity | do 2 f_equal; unwrap2; first [reflexivity | lia]]].

(** A branch on an unknown condition, as two goals, H naming whether
    it is 0. *)
Ltac brz H :=
  iApply wp_branch; [vx | iNext];
  lazymatch goal with |- context [edge_label (if ?n =? 0 then _ else _)] =>
    destruct (Z.eqb_spec n 0) as [H | H] end;
  cbn [edge_label].

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
Context (Hreg : holds_os registry) (Hext : sys_external ge).
Context (vb : Z) (vreg : region) (Rx : iProp Σ).
Context (Hxs_fn : ge_fn ge "_IO_new_file_xsputn" glibc__IO_new_file_xsputn).
Context (Hxs : xsputn_spec w0 registry ge vb Rx).
Context (Hov_fn : find_fn ge (TAtom "__GI___overflow") = Some (Defined glibc___overflow)).
Context (Hov : overflow_spec w0 registry ge vb Rx).

(** The Iris instance for registry and [os_wi] w0. *)
Local Instance puts_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.

(** Expressions of the language. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** Block `c: L103` of `c: puts` over a [file_at] stdout whose lock
    is held once: LibioPutsUnlock.v's [wp_puts_unlock], the lock free
    again after it. *)
Lemma wp_puts_L103 e r fb m sb sreg Φ :
  let fp := mkPtr fb (Obj fb) in
  lookup (TAtom "v12") e = Some (WPtr fp) -> lookup (TAtom "chk1") e = Some (WPtr fp) ->
  lookup (TAtom "pr.1") e = Some (WInt r) -> 0 <= r < 2 ^ 32 ->
  single_ro ge sb sreg -∗ file_at vb (ow_self w0) fp m (Some 0) -∗
  ▷ (file_at vb (ow_self w0) fp m None -∗ Φ (Ret (WInt r))) -∗
  WP (ERun (mkFrame glibc__IO_puts e [] None (Exec (TAtom "L103") (b_insts pu_L103) (b_jump pu_L103)))
        : sexpr) {{ Φ }}.
Proof.
  intros fp Hv12 Hc1 Hr Hrr. subst fp. iIntros "#Hs Hf HK".
  iDestruct (file_at_open with "Hf") as (fb' freg fl lb vt) "(%Hp & Hl & Hfl & Hlp & Hlk & Hmd & Hvtp & Hcl)".
  destruct Hp as (Hfp & Hfb & Hfal & Hfend & Hfreg & Hflr & Hul & Hmv). injection Hfp as <-.
  iDestruct "Hlk" as (lb' lreg Hlb) "Hlk". injection Hlb as <-.
  pose proof Hul as Hul'. unfold has, io_user_lock in Hul'. apply negb_false_iff, Z.eqb_eq in Hul'.
  iApply (wp_puts_unlock w0 registry ge with "Hs Hl [$Hfl //] Hlp Hlk"); try eassumption.
  iNext. iIntros "Hl Hfl Hlp Hlk". iApply "HK".
  iApply ("Hcl" with "[//] Hl Hfl Hlp [Hlk] Hmd Hvtp"). iExists lb, lreg. iSplit; done.
Qed.

(** `c: puts(s)`, s at p the string at the share dq and stdout the
    [file_at] stream fp at any mode with its lock free: the string and
    stdout come back, the stream oriented ([oriented]) and its lock
    free, and the result is [puts_ret] of the string's length. *)
Lemma wp_glibc__IO_puts fr p dq s so soreg fp mode sb sreg Φ :
  call_frame glibc__IO_puts [WPtr p] = Some fr ->
  find_fn ge (TAtom "__GI_strlen") = Some (Defined glibc_strlen) ->
  lookup (TAtom "stdout") (ge_globals ge) = Some (mkPtr so (Obj so)) -> so mod 8 = 0 -> so + 8 <= r_end soreg ->
  ptr_addr (ow_self w0) <> 0 ->
  vtables_ro ge vb vreg -∗ single_ro ge sb sreg -∗ word_string dq p s -∗ live so soreg -∗ pcell so 0 fp -∗
  file_at vb (ow_self w0) fp mode None -∗ Rx -∗
  ▷ (∀ r, ⌜puts_ret (Z.of_nat (length s)) r⌝ -∗ word_string dq p s -∗ live so soreg -∗ pcell so 0 fp -∗
     file_at vb (ow_self w0) fp (oriented mode) None -∗ Rx -∗ Φ (Ret (WInt r))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hstr Hgso Hsoal Hsoend Hsz. iIntros "#Hvt #Hs Hstr Hso Hsoc Hf HRx HK".
  iDestruct (word_string_len with "Hstr") as %Hlen.
  iDestruct (file_at_open with "Hf") as (fb freg fl lb vt) "(%Hp & Hl & Hfl & Hlp & Hlk & Hmd & Hvtp & Hcl)".
  destruct Hp as (-> & Hfb & Hfal & Hfend & Hfreg & Hflr & Hul & Hmv).
  iDestruct "Hlk" as (lb' lreg Hlb) "Hlk". injection Hlb as <-.
  pose proof Hul as Hul'. unfold has, io_user_lock in Hul'. apply negb_false_iff, Z.eqb_eq in Hul'.
  (* The string measured and the lock taken. *)
  iApply (wp_puts_start w0 registry ge Hreg Hext with "Hs Hstr Hso Hsoc Hl Hfl Hlp Hlk"); try eassumption.
  iNext. iIntros (e (Hv0 & Hv6 & Hv12 & Hc1)) "Hstr Hso Hsoc Hl Hfl Hlp Hlk".
  iDestruct ("Hcl" $! mode (Some 0) with "[//] Hl Hfl Hlp [Hlk] Hmd Hvtp") as "Hf";
    [iExists lb, lreg; iSplit; done|].
  (* The orientation and the write. *)
  iApply (wp_puts_L109 w0 registry ge vb vreg Rx Hxs_fn Hxs with "Hvt Hso Hsoc Hf Hstr HRx"); try eassumption.
  iNext. iIntros (e1 c (Hsame & Hc & Hco)) "Hso Hsoc Hf Hstr HRx".
  assert (Hv12' : lookup (TAtom "v12") e1 = Some (WPtr (mkPtr fb (Obj fb)))) by (rewrite Hsame; auto).
  assert (Hc1' : lookup (TAtom "chk1") e1 = Some (WPtr (mkPtr fb (Obj fb)))) by (rewrite Hsame; auto).
  assert (Hv6' : lookup (TAtom "v6") e1 = Some (WInt (Z.of_nat (length s)))) by (rewrite Hsame; auto).
  clear Hsame. unfold pu_j163.
  brz Hc0.
  { (* The write fell short: L181, then L103 with `c: EOF`. *)
    fs. fbr. iApply wp_enter; [reflexivity | vx | iNext].
    iApply (wp_puts_L103 _ (2 ^ 32 - 1) with "Hs Hf"); [lk_val | lk_val | lk_val | lia |].
    iNext. iIntros "Hf". iApply ("HK" with "[%] Hstr Hso Hsoc Hf HRx"). right. reflexivity. }
  assert (Hcn : c <> 0) by (intros ->; apply Hc0; reflexivity).
  rewrite (Hco Hcn).
  (* The newline. *)
  iApply (wp_puts_L180 w0 registry ge vb Rx Hov_fn Hov with "Hso Hsoc Hf HRx"); try eassumption.
  iNext. iIntros (e2 c2 [Hsame Hc2]) "Hso Hsoc Hf HRx".
  assert (Hv12'' : lookup (TAtom "v12") e2 = Some (WPtr (mkPtr fb (Obj fb)))) by (rewrite Hsame; auto).
  assert (Hc1'' : lookup (TAtom "chk1") e2 = Some (WPtr (mkPtr fb (Obj fb)))) by (rewrite Hsame; auto).
  assert (Hv6'' : lookup (TAtom "v6") e2 = Some (WInt (Z.of_nat (length s)))) by (rewrite Hsame; auto).
  clear Hsame Hv12' Hc1' Hv6'.
  fs. brz Hc20.
  { (* The newline failed: L103 with `c: EOF`. *)
    iApply wp_enter; [reflexivity | vx | iNext].
    iApply (wp_puts_L103 _ (2 ^ 32 - 1) with "Hs Hf"); [lk_val | lk_val | lk_val | lia |].
    iNext. iIntros "Hf". iApply ("HK" with "[%] Hstr Hso Hsoc Hf HRx"). right. reflexivity. }
  (* L101: the count, at most `c: INT_MAX`. *)
  fs. fs. fs. destruct (Z.leb_spec (Z.of_nat (length s) + 1) 2147483647) as [Hle | Hgt].
  - fbrv true. fs. fs. iApply wp_enter; [reflexivity | vx | iNext].
    iApply (wp_puts_L103 _ (Z.of_nat (length s) + 1) with "Hs Hf"); [lk_val | lk_val | lk_val | lia |].
    iNext. iIntros "Hf". iApply ("HK" with "[%] Hstr Hso Hsoc Hf HRx"). left. lia.
  - fbrv false. iApply wp_enter; [reflexivity | vx | iNext].
    iApply (wp_puts_L103 _ 2147483647 with "Hs Hf"); [lk_val | lk_val | lk_val | lia |].
    iNext. iIntros "Hf". iApply ("HK" with "[%] Hstr Hso Hsoc Hf HRx"). left. lia.
Qed.

End rules.
End LibioPutsOn.
