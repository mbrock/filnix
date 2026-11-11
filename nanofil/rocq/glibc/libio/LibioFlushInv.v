(** Exit cleanup needs ownership of streams even when it does not need
    the proofs of the flush loop. This module defines that ownership
    independently of the loop's call rules. A stream's object token and
    its idle narrow fields can therefore be used by smaller clients. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From Stdlib Require Import ZArith.
From Nanofil Require Import Values Memory Runtime Pieces Heap Logic.
From Glibc Require Import FileInv.
Open Scope Z_scope.

(** The predicates use the caller's runtime and shared memory logic. *)
Module LibioFlushInvOn (R : Runtime) (LG0 : LogicSig R).
Module FI := FileInvOn R LG0.
Import FI FI.LG.

Section preds.
Context `{!gen_heapGS piece pval Σ}.

(** Every stream access needs ownership of its complete FILE object. *)
Definition stream_life (g : ptr) : iProp Σ :=
  ∃ gb greg, ⌜g = mkPtr gb (Obj gb) /\ 0 < gb /\ gb mod 8 = 0 /\ gb + file_size <= r_end greg /\
              r_end greg <= 2 ^ 63⌝ ∗ live gb greg.

(** Cleanup reads the narrow fields and free lock of a stream with
    nothing pending. The read and write pointers share a capability
    whose object remains owned, and the backup base is null. Before
    unbuffering, the mode is zero unless the stream is unbuffered;
    afterward, it is minus one. These conditions let cleanup retain
    the buffer without calling a stream's write or allocation methods. *)
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

End preds.
End LibioFlushInvOn.
