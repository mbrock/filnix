(** A zero-length call to `c: _IO_new_file_xsputn` returns zero before
    reading the stream or source. This proof follows the actual decoded
    entry block and its early return in [LibioXsputnCode](LibioXsputnCode.v).
    It preserves arbitrary caller resources without requiring a usable
    stream buffer or an operating-system write contract. *)

From Glibc Require Import GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics
  ExternalCalls Pieces Heap Language Logic.
From Glibc Require Import LibioXsputnCode.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.


Module LG := LG0.
Import LG LG.L.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context {world : Type} (registry : name -> option (contract world))
  (wi : mem -> world -> gmap piece pval -> Prop) `{!SafepointStable wi} (ge : genv).

(** The state interpretation is the one supplied by the caller. *)
Local Instance zero_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry wi ge.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** The call reads neither pointer and preserves every caller resource.
    Its [[frame]] binds the stream, source and zero byte count. *)
Lemma wp_xsputn_zero fr fp src (P : iProp Σ) Φ :
  call_frame glibc__IO_new_file_xsputn [WPtr fp; WPtr src; WInt 0] = Some fr ->
  P -∗ ▷ (P -∗ Φ (Ret (WInt 0))) -∗ WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr. injection Hfr as <-. iIntros "HP HK".
  iApply wp_enter; [reflexivity | reflexivity |]. iNext.
  cbn [b_insts b_jump].
  iApply wp_let; [reflexivity | reflexivity | reflexivity | intros; reflexivity |].
  iNext. iApply wp_branch; [reflexivity |]. iNext.
  iApply wp_enter; [reflexivity | reflexivity |]. iNext.
  cbn [b_insts b_jump].
  iApply wp_ret; [reflexivity | reflexivity |]. iNext.
  iApply ("HK" with "HP").
Qed.

(** The direct return form records both the zero result and unchanged resources. *)
Lemma wp_xsputn_zero_returns fr fp src (P : iProp Σ) :
  call_frame glibc__IO_new_file_xsputn [WPtr fp; WPtr src; WInt 0] = Some fr ->
  P -∗ WP (ERun fr : sexpr) {{ r, ⌜r = Ret (WInt 0)⌝ ∗ P }}.
Proof.
  intros Hfr. iIntros "HP".
  iApply (wp_xsputn_zero fr fp src P with "HP []"); [exact Hfr |].
  iNext. iIntros "HP". iFrame "HP". done.
Qed.
End rules.
