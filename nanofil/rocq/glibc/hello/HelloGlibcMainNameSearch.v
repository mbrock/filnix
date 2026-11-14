From Glibc Require Import GlibcProgram.
(** This file packages the two proved searches needed by set_program_name.
    Sealing these results avoids substituting their internal proof modules
    when the name-call bridge is compiled. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Run Machine
  ExternalCalls Pieces Heap Language Logic MemLogic.
From Glibc Require Import OsWorld WordString MemchrLast StrrchrLogic MemrchrBits MemrchrCode MemrchrLogic MemcmpCode MemcmpLogic.
From Glibc Require MemcmpLogic MemrchrLogic OsWorld.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

(** The interface states only the observable search triples. *)
Import ProgramAbbreviations.
Module Type HelloNameSearchSig.
Import LG0 LG0.L.
(** The memory predicates share the caller's logic instance. *)
Module ML := MemLogicOn R LG0.
Import ML.
Section spec.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
(** Reverse search returns the last matching byte while preserving the string. *)
Parameter name_memrchr : find_fn ge (TAtom "__GI___memrchr") = Some (Defined glibc_memrchr) ->
  exists F, find_fn ge (TAtom "__GI___memrchr") = Some (Defined F) /\
  (forall p c n, is_Some (call_frame F [WPtr p; WInt c; WInt n])) /\
  forall fr dq p s c Φ, 0 <= c < 2 ^ 32 ->
  call_frame F [WPtr p; WInt c; WInt (Z.of_nat (length s) + 1)] = Some fr ->
  ⊢ word_string dq p s -∗
    (word_string dq p s -∗ Φ (Ret (WPtr (hit_ptr p (last_byte (c mod 256) (s ++ [0])))))) -∗
    WP (ERun fr : language.expr (nanofil_lang registry ge)) {{ Φ }}.
(** Byte comparison returns zero exactly for equal small byte sequences. *)
Parameter name_memcmp : find_fn ge (TAtom "memcmp") = Some (Defined glibc_memcmp) ->
  exists F, find_fn ge (TAtom "memcmp") = Some (Defined F) /\
  (forall p q n, is_Some (call_frame F [WPtr p; WPtr q; WInt n])) /\
  forall fr dq1 dq2 b reg o c xs b' reg' o' c' ys Φ,
  call_frame F [WPtr (mkPtr (b + o) c); WPtr (mkPtr (b' + o') c'); WInt (Z.of_nat (length xs))] = Some fr ->
  (length xs < 16)%nat -> (c = Obj b \/ c = Ro b) -> (c' = Obj b' \/ c' = Ro b') -> length ys = length xs ->
  0 <= o -> 0 <= o' -> b + o + Z.of_nat (length xs) <= r_end reg ->
  b' + o' + Z.of_nat (length xs) <= r_end reg' -> r_end reg <= 2 ^ 48 -> r_end reg' <= 2 ^ 48 ->
  Forall (fun x => 0 <= x < 256) xs -> Forall (fun x => 0 <= x < 256) ys ->
  ⊢ liveq dq1 b reg -∗ bytesq dq1 b o xs -∗ liveq dq2 b' reg' -∗ bytesq dq2 b' o' ys -∗
    (∀ k, ⌜k mod 2 ^ 32 = 0 <-> xs = ys⌝ -∗ liveq dq1 b reg -∗ bytesq dq1 b o xs -∗
      liveq dq2 b' reg' -∗ bytesq dq2 b' o' ys -∗ Φ (Ret (WInt k))) -∗
    WP (ERun fr : language.expr (nanofil_lang registry ge)) {{ Φ }}.
End spec.
End HelloNameSearchSig.

(** The implementation exports existing proofs without new assumptions. *)
Module HelloGlibcMainNameSearchOn : HelloNameSearchSig.
Import LG0 LG0.L.
(** The memory predicates share the caller's logic instance. *)
Module ML := MemLogicOn R LG0.
(** The reverse-search proof handles every byte of a word string. *)
Module MR := MemrchrLogic.
(** The comparison proof handles the short directory-name comparison. *)
Module MC := MemcmpLogic.
(** The OS interpretation supplies the required safepoint instance. *)
Module OW := OsWorld.
Section results.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
(** Collector safepoints preserve the concrete interpretation. *)
Local Instance search_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
(** Reverse search returns the last matching byte while preserving the string. *)
Definition name_memrchr := MemrchrLogic.glibc_memrchr_spec registry (os_wi w0) ge.
(** Byte comparison returns zero exactly for equal small byte sequences. *)
Definition name_memcmp := MemcmpLogic.glibc_memcmp_small registry (os_wi w0) ge.
End results.
End HelloGlibcMainNameSearchOn.
