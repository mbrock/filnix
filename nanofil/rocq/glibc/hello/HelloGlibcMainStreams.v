(** This file exposes the concrete stream resources used at Hello's exit.
    The resource definitions remain visible, but the flush proofs do not
    enter every later functor substitution. This keeps the application
    proofs small without weakening their stream contracts. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From Stdlib Require Import ZArith List.
From Nanofil Require Import Values Memory Runtime Pieces Heap Logic MemLogic.
From Glibc Require Import FileInv LibioFlushBody OsWorld.
From Glibc Require FileInv LibioFlushBody OsWorld.
From Glibc Require Import Fix.
Open Scope Z_scope.
Import ListNotations.

(** The OS interface exports the safepoint rule without the syscall proof tree. *)
Module Type HelloWorldSig.
(** Collector safepoints preserve the concrete OS interpretation. *)
Parameter os_wi_stable : forall w0, LG0.SafepointStable (os_wi w0).
End HelloWorldSig.

(** The existing OS proof implements the safepoint interface. *)
Module HelloGlibcWorldOn : HelloWorldSig.
Include OsWorld.
End HelloGlibcWorldOn.

(** The interface defines stream ownership without exporting flush proofs. *)
Module Type HelloStreamsSig.
(** The file invariants share the caller's logic instance. *)
Module FI := FileInv.
Import LG0 LG0.L FileInv FileInv.ML.
Section resources.
Context `{!gen_heapGS piece pval Σ}.
(** The stream owns a live, aligned file object. *)
Definition stream_life (g : ptr) : iProp Σ :=
  ∃ gb greg, ⌜g = mkPtr gb (Obj gb) /\ 0 < gb /\ gb mod 8 = 0 /\ gb + file_size <= r_end greg /\
              r_end greg <= 2 ^ 63⌝ ∗ live gb greg.
(** The narrow stream has no pending output and owns an unlocked lock. *)
Definition exit_stream (done : bool) (g : ptr) : iProp Σ :=
  ∃ fb fl f2 fd md lb lbreg c breg arp are awb awp,
    ⌜g = mkPtr fb (Obj fb) /\ 0 <= fl < 2 ^ 32 /\ Z.land fl 32768 = 0 /\ Z.land f2 32 = 0 /\ fd < 2 ^ 31 /\
     0 <= awp <= awb /\ awb < 2 ^ 64 /\ 0 <= are <= arp /\ arp < 2 ^ 64 /\
     (if done then md = 2 ^ 32 - 1
      else (md = 0 \/ md = 2 ^ 32 - 1) /\ (Z.land fl io_unbuffered <> 0 \/ md = 0))⌝ ∗
    int_cell fb off_flags fl ∗ int_cell fb off_flags2 f2 ∗ int_cell fb off_fileno fd ∗ int_cell fb off_mode md ∗
    pcell fb off_lock (mkPtr lb (Obj lb)) ∗ lock_state lb lbreg 0 0 null ∗
    pcell fb 8 (mkPtr arp c) ∗ pcell fb 16 (mkPtr are c) ∗ pcell fb 32 (mkPtr awb c) ∗
    pcell fb 40 (mkPtr awp c) ∗ live_cap c breg ∗ pcell fb 80 null.
End resources.
End HelloStreamsSig.

(** The existing flush proof implements these exact resource definitions. *)
Module HelloGlibcMainStreamsOn : HelloStreamsSig.
(** The file invariants share the caller's logic instance. *)
Module FI := FileInv.
(** The flush proof supplies both resource definitions. *)
Module F := LibioFlushBody.
(** The stream owns a live, aligned file object. *)
Definition stream_life := @LibioFlushBody.stream_life.
(** The narrow stream has no pending output and owns an unlocked lock. *)
Definition exit_stream := @LibioFlushBody.exit_stream.
End HelloGlibcMainStreamsOn.
