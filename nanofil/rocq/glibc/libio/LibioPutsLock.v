From Glibc Require Import GlibcProgram.
(** The puts function measures its input string before taking stdout's lock.
    This proof covers the single-threaded path, where the lock is initially free.
    The resulting lock has count zero and records the current thread as owner.

    The global stdout pointer can change between accesses, so puts reads it each time.
    The proof retains that pointer cell together with the stream's fields throughout the lock operation. *)

From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsThread OsRegistry FileInv LibioLogic SysWrappers LibioCloseSteps
  WordString StrlenLogic StrlenWord LibioPutsCode LibioPutsInv.
From Glibc Require FileInv LibioCloseSteps LibioLogic LibioPutsInv OsThread OsWorld StrlenWord SysWrappers.
From Glibc Require Import Fix.
From Glibc Require Import GlibcSpec.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.


Import LibioPutsInv LibioCloseSteps SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (Hreg : holds_os registry)
  (Hext : sys_external ge).


(** The expression type uses this caller's linked program and registry. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** The thread-cookie call requires an external name and its registry contract. *)
Ltac self_side := first [apply (reg_of registry Hreg); reflexivity | apply (ext_fn ge Hext); cbn; tauto
                        | apply (ext_data ge Hext); cbn; tauto].

(** The thread-cookie rule returns a nonnull identifier when the caller supplies that guarantee. *)
Ltac self H := iApply (OsThread.wp_zthread_self_cookie); try self_side; [exact H|]; iNext.

(** The puts prefix measures a shared string and acquires stdout's initially free lock.
    The next block receives the string pointer, its length, and the stream pointer in its environment. *)
Lemma wp_puts_start fr p dq s so soreg fb freg fl lb lbreg sb sreg Φ :
  let fp := mkPtr fb (Obj fb) in
  call_frame glibc__IO_puts [WPtr p] = Some fr ->
  find_fn ge (TAtom "__GI_strlen") = Some (Defined glibc_strlen) ->
  lookup (TAtom "stdout") (ge_globals ge) = Some (mkPtr so (Obj so)) -> so mod 8 = 0 -> so + 8 <= r_end soreg ->
  ptr_addr (ow_self w0) <> 0 ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  0 <= fl < 2 ^ 32 -> Z.land fl 32768 = 0 ->
  single_ro ge sb sreg -∗ word_string dq p s -∗ live so soreg -∗ pcell so 0 fp -∗
  live fb freg -∗ int_cell fb off_flags fl -∗ pcell fb off_lock (mkPtr lb (Obj lb)) -∗
  lock_state lb lbreg 0 0 null -∗
  ▷ (∀ e, ⌜lookup (TAtom "v0") e = Some (WPtr p) /\ lookup (TAtom "v6") e = Some (WInt (Z.of_nat (length s))) /\
           lookup (TAtom "v12") e = Some (WPtr fp) /\ lookup (TAtom "chk1") e = Some (WPtr fp)⌝ -∗
     word_string dq p s -∗ live so soreg -∗ pcell so 0 fp -∗
     live fb freg -∗ int_cell fb off_flags fl -∗ pcell fb off_lock (mkPtr lb (Obj lb)) -∗
     lock_state lb lbreg 1 0 (ow_self w0) -∗
     WP (ERun (mkFrame glibc__IO_puts e [] None (Enter (TAtom "L109") (Some (TAtom "L25")))) : sexpr) {{ Φ }}) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros fp Hfr Hstr Hgso Hsoal Hsoend Hsz Hfb Hfal Hfend Hfreg Hfl Hul. injection Hfr as <-. subst fp.
  unfold file_size in Hfend. assert (0 <= Z.land fl 32768 < 2 ^ 32) by (rewrite Hul; lia).
  iIntros "#Hs Hstr Hso Hsoc Hl [_ Hfl] Hlp Hlb HK".
  iPoseProof "Hs" as "(%Hs' & Hsl & Hsb)". destruct Hs' as (Hgs & Hsend).
  iDestruct "Hlb" as "(%Hb & Hbl & [%Hb0r Hb0] & [%Hb4r Hb4] & Hbo)". destruct Hb as (Hbal & Hbend & Hbreg).
  iApply (wp_live_fit1 with "Hl"). iIntros ([Hf0 Hf48]) "Hl".
  iApply (wp_live_fit1 with "Hbl"). iIntros ([Hlb0 Hlb48]) "Hbl".
  iApply (wp_live_fit1 with "Hso"). iIntros ([Hso0 Hso48]) "Hso".
  iApply (wp_live_fit with "Hsl"). iIntros ([Hsb0 Hsb48]) "_".
  iDestruct (word_string_len with "Hstr") as %Hlen.
  (* start: the length, stdout, and `c: _IO_USER_LOCK` clear. *)
  step. assert (Hstrlen : Defines ge "__GI_strlen" glibc_strlen) by exact Hstr.
  call_spec with (dq, p, s).
  iDestruct "Hpost" as "[-> Hstr]". resume.
  cbn [fr_fn fr_env fr_locals fr_doomed fr_at].
  step. check "Hso". load "Hso" "Hsoc" "Hl". check "Hl". load_s32 "Hl" "Hfl". step. step. branch_as false.
  (* L20, L31, L32: single threaded, the owner null. *)
  step. self Hsz. step. check_persistent "Hsl". load_byte_persistent "Hsl Hsb". step. branch.
  step. step. check "Hl". load "Hl" "Hlp" "Hbl". step. check "Hbl". load_null "Hbl" "Hbo". step. step. step. step. step. branch.
  (* L25: the lock word 1, the owner the cookie. *)
  step. step. check "Hl". load "Hl" "Hlp" "Hbl". check "Hbl". store_int "Hbl" "Hb0". load "Hl" "Hlp" "Hbl". step.
  check "Hbl". store "Hbl" "Hbo". step.
  iApply ("HK" with "[%] Hstr Hso Hsoc Hl [Hfl] Hlp [Hbl Hb0 Hb4 Hbo]").
  - split_and!; try lk_prove. lookups. rewrite Z.mod_small; [reflexivity | lia].
  - iSplit; [done | iExact "Hfl"].
  - iFrame. iPureIntro. unfold int_bytes. split_and!; lia.
Qed.

End rules.
