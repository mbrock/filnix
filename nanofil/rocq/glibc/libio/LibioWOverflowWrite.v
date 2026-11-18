(** The wide writers flush the part of the buffer between the write base
    and the cursor. They pass the base itself and a count in characters,
    not bytes. When a full buffer flush succeeds, overflow needs to know
    that the cursor is back at the base before it stores another character. *)

From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import CodePrelude HelloImageCode133 Fix OsWorld FileInv LibioLogic
  LibioWIdle LibioWXsputnWindow LibioWXsputnRoom.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic.
Open Scope Z_scope.

Definition wdo_write_fn := Eval vm_compute in
  code_function (code_module (TApp "module" [TList hello_image_items_133])) "__GI__IO_wdo_write".

Section write.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Abbreviation sexpr := (language.expr (nanofil_lang registry ge)).

(** Even when conversion fails, the caller gets a wide stream back.
    Success leaves the same buffer empty, so the caller can use the
    space it just made. Neither case takes ownership of the stream. *)
Definition wdo_pending_spec vb self fd (E : iProp Σ) : Prop := forall frame fp wd w i Φ,
  call_frame wdo_write_fn [WPtr fp; WPtr (window_base wd w); WInt i] = Some frame ->
  file_pending ge vb self fp fd wd w i -∗ E -∗
  ▷ (∀ ok : bool, (if ok then file_pending ge vb self fp fd wd w 0 else file_wide ge vb self fp fd) -∗
    E -∗ Φ (Ret (WInt (if ok then 0 else 2^32-1)))) -∗ WP (ERun frame : sexpr) {{ Φ }}.
End write.

Lemma wpos_zero wd w : wpos wd w 0 = window_base wd w.
Proof. unfold wpos. destruct (window_base wd w). simpl. f_equal. lia. Qed.

(** The compiler subtracts byte addresses and uses signed division.
    The buffer holds whole characters and is smaller than half the
    address space, so the quotient is exactly the cursor index. *)
Lemma wflush_count b i : 0 <= b -> 0 <= i -> b+4*i <= 2^63 -> 4*i < 2^63 ->
  (if sign_extension (2^64) (2^63) (4 mod 2^64) =? 0 then 0 else
    (sign_extension (2^64) (2^63) ((((b+4*i) mod 2^64 - b mod 2^64) mod 2^64) mod 2^64)
     ÷ sign_extension (2^64) (2^63) (4 mod 2^64)) mod 2^64) = i.
Proof.
  intros. change (sign_extension (2^64) (2^63) (4 mod 2^64)) with 4. change (4 =? 0) with false. cbn iota.
  rewrite (Z.mod_small (b+4*i) (2^64)); [|lia]. rewrite (Z.mod_small b (2^64)); [|lia].
  rewrite Z.mod_mod; [|lia]. replace (b+4*i-b) with (i*4) by lia.
  rewrite wpos_signed; [|lia]. rewrite Z.quot_mul; [|lia]. apply Z.mod_small. lia.
Qed.
