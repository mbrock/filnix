(** The wide stream writer borrows characters from the caller's staging
    buffer and returns the number it accepted. *)

From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import Fix GlibcProgram LibioWIdle Unit_libio_wfileops_os.
Import ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0 Fix.LG0.L.
Open Scope Z_scope.

Definition wprintf_xsputn_fn := Unit_libio_wfileops_os.fn___GI__IO_wfile_xsputn.

Section write.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Abbreviation sexpr := (language.expr (nanofil_lang registry ge)).
Context (vb : Z) (self : ptr) (E : iProp Σ).

(** The stream borrows the staged characters without taking ownership of
    the rest of the array. It may accept fewer characters than requested. *)
Definition wprintf_xsputn_call_spec : Prop := forall fr fp bb breg dq cs Φ,
  0 < bb -> bb mod 8 = 0 -> bb + 560 <= r_end breg -> r_end breg <= 2 ^ 63 ->
  Z.of_nat (length cs) <= 128 -> Forall (fun c => 0 <= c < 2 ^ 32) cs ->
  call_frame wprintf_xsputn_fn
    [WPtr fp; WPtr (mkPtr (bb + 48) (Obj bb)); WInt (Z.of_nat (length cs))] = Some fr ->
  file_wide ge vb self fp 1 -∗ E -∗ liveq dq bb breg -∗ bytesq dq bb 48 (flat_map (fun c => le_bytes c 4) cs) -∗
  ▷ (∀ r, ⌜0 <= r <= Z.of_nat (length cs)⌝ -∗ file_wide ge vb self fp 1 -∗ E -∗
    liveq dq bb breg -∗ bytesq dq bb 48 (flat_map (fun c => le_bytes c 4) cs) -∗ Φ (Ret (WInt r))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.

End write.
