From Glibc Require Import GlibcProgram.
(** The call of `c: puts(s)` (LibioPutsCode.v, libio/ioputs.c) that
    writes the string, with stdout's lock held and the stream narrow:
    `c: _IO_sputn(stdout, s, len)` through the jump table's
    `c: _IO_new_file_xsputn` ([wp_puts_L162]), whose triple is
    LibioPutsInv.v's hypothesis [xsputn_spec]. LibioPutsMode.v reaches
    it after orienting the stream.

    It ends in block `c: L163`, whose flag `c: v179` is nonzero only
    when the call wrote the whole string. The jump table pointer is
    checked against `c: __io_vtables` as in LibioDoWriteCall.v; a
    narrow stream's is `c: _IO_file_jumps`, which passes. *)

From Glibc Require Import GlibcTactics LibioTactics.
From Glibc Require Import GlibcEnv.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry FileInv LibioLogic SysWrappers LibioCloseSteps
  WordString LibioXsputnCode LibioPutsCode LibioPutsInv LibioPutsLock LibioPutsUnlock.
From Glibc Require FileInv LibioCloseSteps LibioLogic LibioPutsInv LibioPutsLock LibioPutsUnlock OsWorld SysWrappers.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The jump of block `c: L163` of `c: puts`, on the flag `c: v179`. *)
Definition pu_j163 : jump := JBranch (Tmp (TAtom "v179")) (To (TAtom "L180")) (To (TAtom "L181")).


Import LibioPutsUnlock LibioPutsLock LibioPutsInv LibioCloseSteps SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (vb : Z)
  (vreg : region)
  (Rx : iProp Σ).
Context (F : ptr -> Z -> option Z -> iProp Σ).
Context (G : list Z -> ptr -> Z -> option Z -> iProp Σ).
Context (Hopen : forall fp mode held, F fp mode held ⊢ file_open vb (ow_self w0) F fp mode held).
Context (Hxs_fn : ge_fn ge "_IO_new_file_xsputn" glibc__IO_new_file_xsputn).
Context (Hxs : xsputn_spec_for w0 registry ge F G Rx).


(** Expressions of the language. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** Block `c: L162` of `c: puts` on, stdout fb at mode -1 with its lock
    held once: the jump table is checked, its `c: xsputn` slot called
    on the string, and block `c: L163` reached, its flag `c: v179`
    whatever the count makes it. *)
Lemma wp_puts_L162_for e p dq s so soreg fb Φ :
  let fp := mkPtr fb (Obj fb) in
  lookup (TAtom "v0") e = Some (WPtr p) -> lookup (TAtom "v6") e = Some (WInt (Z.of_nat (length s))) ->
  lookup (TAtom "v12") e = Some (WPtr fp) -> lookup (TAtom "chk1") e = Some (WPtr fp) ->
  lookup (TAtom "stdout") (ge_globals ge) = Some (mkPtr so (Obj so)) -> so mod 8 = 0 -> so + 8 <= r_end soreg ->
  vtables_ro ge vb vreg -∗ live so soreg -∗ pcell so 0 fp -∗
  F fp (2 ^ 32 - 1) (Some 0) -∗ word_string dq p s -∗ Rx -∗
  ▷ (∀ e' c, ⌜keeps (atoms ["v0"; "v6"; "v12"; "chk1"]) e e' /\ lookup (TAtom "v179") e' = Some (WInt c)⌝ -∗
     live so soreg -∗ pcell so 0 fp -∗ G s fp (2 ^ 32 - 1) (Some 0) -∗
     word_string dq p s -∗ Rx -∗
     WP (ERun (mkFrame glibc__IO_puts e' [] None (Exec (TAtom "L163") [] pu_j163)) : sexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame glibc__IO_puts e [] None (Enter (TAtom "L162") (Some (TAtom "L121")))) : sexpr) {{ Φ }}.
Proof.
  intros fp Hv0 Hv6 Hv12 Hc1 Hgso Hsoal Hsoend. subst fp.
  iIntros "#Hvt Hso Hsoc Hf Hstr HRx HK".
  iDestruct (word_string_len with "Hstr") as %Hlen.
  iDestruct (Hopen with "Hf") as (fb' freg fl lb vt) "(%Hp & Hl & Hfl & Hlp & Hlk & Hmd & Hvtp & Hcl)".
  destruct Hp as (Hfp & Hfb & Hfal & Hfend & Hfreg & Hflr & Hul & Hmv). injection Hfp as <-.
  unfold file_size in Hfend.
  rewrite (mode_vtable_narrow _ _ Hmv); [|lia].
  iPoseProof (vtables_slot ge vb vreg slot_xsputn "_IO_new_file_xsputn" with "Hvt") as "#Hsx"; [cbn; tauto|].
  iAssert (live_capq DfracDiscarded (ptr_cap (sym_ptr ge "_IO_new_file_xsputn")) vreg) as "Hfc".
  { rewrite (ge_fn_cap _ _ _ Hxs_fn). done. }
  iDestruct "Hvt" as "((%Hvg & %Hvend & %Hval & %Hvb & %Hvreg) & Hvl & Hslots)".
  unfold io_vtables_size in Hvend.
  iApply (wp_live_fit1 with "Hl"). iIntros ([Hf0 Hf48]) "Hl".
  iApply (wp_live_fit1 with "Hso"). iIntros ([Hso0 Hso48]) "Hso".
  (* L162: stdout's jump table, within `c: __io_vtables`. *)
  step. step. check "Hso". load "Hso" "Hsoc" "Hl". step. check "Hl".
  iApply (wp_raw_load_pointer_dq with "Hl Hvtp Hvl");
    [reflexivity | vx | left; reflexivity | a2 | a2 | cbn; unfold vt_file; lia |].
  iNext. iIntros "Hl Hvtp #Hvl'". step. step. step. step. step. branch_as true.
  (* iw_1.join: the `c: xsputn` slot, called on stdout, the string and its length. *)
  step. step.
  check_read_dq "Hvl'" by a2.
  iNext. iIntros "_".
  iApply (wp_raw_load_pointer_dq with "Hvl' Hsx Hfc");
    [reflexivity | vx | right; reflexivity | a2 | a2 | apply (ge_fn_addr _ _ _ Hxs_fn) |].
  iNext. iIntros "_ _ _".
  step. check "Hso". load "Hso" "Hsoc" "Hl".
  iApply wp_check_function; [vx | apply (ge_fn_check _ _ _ Hxs_fn) |]. iNext.
  iApply wp_raw_call_bind; [vx | apply (ge_fn_cap _ _ _ Hxs_fn) | apply (ge_fn_check _ _ _ Hxs_fn) | vx |
    apply (ge_fn_find _ _ _ Hxs_fn) | reflexivity | reflexivity |].
  iNext. rewrite (Z.mod_small (Z.of_nat (length s)) (2 ^ 64)); [|lia].
  iDestruct ("Hcl" $! (2 ^ 32 - 1) (Some 0) with "[%] Hl Hfl Hlp Hlk Hmd Hvtp") as "Hf";
    [left; split; [right; reflexivity | reflexivity]|].
  iApply (Hxs with "Hf Hstr HRx"); [reflexivity|].
  iNext. iIntros (r Hr) "Hf Hstr HRx". resume.
  step. step. iApply wp_enter; [reflexivity | vx | iNext].
  iApply ("HK" with "[%] Hso Hsoc Hf Hstr HRx").
  split; [rewrite keeps_forall; cbn [atoms List.map List.In]; intros x Hx; destruct Hx as [<- | [<- | [<- | [<- | []]]]]; lookups; reflexivity | lk_prove].
Qed.

End rules.

(** Generic streams use the same call proof without adding stdout's
    stronger buffer and flag requirements to their predicate. *)
Definition wp_puts_L162 `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}
    w0 registry ge vb vreg Rx Hxs_fn (Hxs : xsputn_spec w0 registry ge vb Rx) :=
  program_call(wp_puts_L162_for (glibc_program := program_of w0 registry ge) vb vreg Rx (file_at vb (ow_self w0))
    (fun _ => file_at vb (ow_self w0)) (file_at_open vb (ow_self w0)) Hxs_fn Hxs).

