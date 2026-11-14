(** The newline of `c: puts(s)` (LibioPutsCode.v, libio/ioputs.c),
    block `c: L180` to the end of block `c: L184`, with stdout's lock
    held and the stream narrow ([wp_puts_L180]):

    ```c
    _IO_putc_unlocked ('\n', stdout) != EOF
    ```

    The byte goes straight into the buffer when there is room, that
    is when `c: _IO_write_ptr` is below `c: _IO_write_end`, and the
    write pointer moves past it. Otherwise `c: __overflow(stdout,
    '\n')` flushes the buffer and stores the byte. The flag `c: v208`
    says whether the result was other than `c: EOF`.

    | Case | Block | Proved by |
    |---|---|---|
    | room in the buffer | `c: L183` | LibioPutsBuf.v's [wp_buf_putc] |
    | the buffer full | `c: L182` | LibioPutsInv.v's hypothesis [overflow_spec] | *)

From Glibc Require Import GlibcTactics LibioTactics.
From Glibc Require Import GlibcEnv.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry FileInv LibioLogic SysWrappers LibioCloseSteps
  WordString LibioGenCode LibioXsputnCode LibioPutsCode LibioPutsInv LibioPutsBuf.
From Glibc Require FileInv LibioCloseSteps LibioLogic LibioPutsBuf LibioPutsInv OsWorld SysWrappers.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.


Import LibioPutsBuf LibioPutsInv LibioCloseSteps SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
Context (vb : Z) (Rx : iProp Σ).
Context (Hov_fn : find_fn ge (TAtom "__GI___overflow") = Some (Defined glibc___overflow)).
Context (Hov : overflow_spec w0 registry ge vb Rx).

(** The Iris instance for registry and [os_wi] w0. *)
Local Instance puts_nl_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.

(** Expressions of the language. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** Block `c: L180` of `c: puts` to the end of block `c: L184`, stdout
    fb at mode -1 with its lock held once: `c: '\n'` is stored in the
    buffer or handed to `c: __overflow`, and block `c: L181` is entered
    with the flag `c: v208`. *)
Lemma wp_puts_L180 e so soreg fb Φ :
  let fp := mkPtr fb (Obj fb) in
  lookup (TAtom "stdout") (ge_globals ge) = Some (mkPtr so (Obj so)) -> so mod 8 = 0 -> so + 8 <= r_end soreg ->
  live so soreg -∗ pcell so 0 fp -∗ file_at vb (ow_self w0) fp (2 ^ 32 - 1) (Some 0) -∗ Rx -∗
  ▷ (∀ e' c, ⌜keeps (atoms ["v0"; "v6"; "v12"; "chk1"]) e e' /\ lookup (TAtom "v208") e' = Some (WInt c)⌝ -∗
     live so soreg -∗ pcell so 0 fp -∗ file_at vb (ow_self w0) fp (2 ^ 32 - 1) (Some 0) -∗ Rx -∗
     WP (ERun (mkFrame glibc__IO_puts e' [] None (Enter (TAtom "L181") (Some (TAtom "L184")))) : sexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame glibc__IO_puts e [] None (Enter (TAtom "L180") (Some (TAtom "L163")))) : sexpr) {{ Φ }}.
Proof.
  intros fp Hgso Hsoal Hsoend. subst fp.
  iIntros "Hso Hsoc Hf HRx HK".
  iDestruct (file_at_nl with "Hf") as (fb' freg nb wp we col) "(%Hp & Hl & Hwp & Hwe & Hcol & Hb & Hcl)".
  destruct Hp as (Hfp & Hfb & Hfal & Hfend & Hfreg & Hwin & Hwein & Hcl8). injection Hfp as <-.
  unfold file_size in Hfend.
  iApply (wp_live_fit1 w0 registry ge with "Hl"). iIntros ([Hf0 Hf48]) "Hl".
  iApply (wp_live_fit1 w0 registry ge with "Hso"). iIntros ([Hso0 Hso48]) "Hso".
  iApply (wp_buf_fit w0 registry ge fb with "Hb"); [lia | lia |]. iIntros (Hfit) "Hb".
  pose proof (Hfit _ Hwin) as Hwr. pose proof (Hfit _ Hwein) as Her. clear Hfit.
  (* L180: the write pointer and the write end, compared. *)
  step. step. check "Hso". load "Hso" "Hsoc" "Hl". step. check "Hl".
  iApply (wp_load_bufptr w0 registry ge with "Hl Hwp Hb"); [reflexivity | vx | reflexivity | a2 | a2 | lia
    | exact Hwin |].
  iNext. iIntros "Hl Hwp Hb".
  step. check "Hso". load "Hso" "Hsoc" "Hl". step. check "Hl".
  iApply (wp_load_bufptr w0 registry ge with "Hl Hwe Hb"); [reflexivity | vx | reflexivity | a2 | a2 | lia
    | exact Hwein |].
  iNext. iIntros "Hl Hwe Hb". step. step. step.
  destruct (Z.ltb_spec (ptr_addr wp) (ptr_addr we)) as [Hlt | Hge].
  - (* L183: room in the buffer, the byte stored and the write pointer moved past it. *)
    branch_as true. step. step. check "Hso". load "Hso" "Hsoc" "Hl". step. check "Hl".
    iApply (wp_load_bufptr w0 registry ge with "Hl Hwp Hb"); [reflexivity | vx | reflexivity | a2 | a2 | lia
      | exact Hwin |].
    iNext. iIntros "Hl Hwp Hb". step. check "Hl". store "Hl" "Hwp".
    iApply (wp_buf_putc w0 registry ge with "Hl Hcol Hb");
      [vx | lia | exact Hfal | unfold file_size; lia | lia | exact Hwin | exact Hwein | exact Hlt | exact Hcl8 |].
    iNext. iIntros (col' Hcl') "Hl Hcol Hb". step. step. step. step.
    iApply ("HK" with "[%] Hso Hsoc [Hl Hwp Hwe Hcol Hb Hcl] HRx").
    + split; [rewrite keeps_forall; cbn [atoms List.map List.In]; intros x Hx; destruct Hx as [<- | [<- | [<- | [<- | []]]]]; lookups; reflexivity | lk_prove].
    + iApply ("Hcl" with "[%] Hl Hwp Hwe Hcol Hb"). split; [|exact Hcl'].
      destruct nb as [| |bb sz|bb]; cbn [in_buf] in Hwin, Hwein |- *;
        [subst wp we; cbn in Hlt; lia | | | subst wp we; cbn in Hlt; lia];
        (split; [cbn [ptr_cap]; tauto | cbn [ptr_addr]; unwrap2; lia]).
  - (* L182: the buffer full, `c: __overflow(stdout, '\n')`. *)
    branch_as false. step. step. check "Hso". load "Hso" "Hsoc" "Hl".
    iApply wp_call_bind; [vx | exact Hov_fn | reflexivity |]. iNext.
    iDestruct ("Hcl" with "[%] Hl Hwp Hwe Hcol Hb") as "Hf"; [split; [exact Hwin | exact Hcl8]|].
    iApply (Hov with "Hf HRx"); [reflexivity|].
    iNext. iIntros (r Hr) "Hf HRx". resume. step. step. step. step.
    iApply ("HK" with "[%] Hso Hsoc Hf HRx").
    split; [rewrite keeps_forall; cbn [atoms List.map List.In]; intros x Hx; destruct Hx as [<- | [<- | [<- | [<- | []]]]]; lookups; reflexivity | lk_prove].
Qed.

End rules.
