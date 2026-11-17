(** A byte of memory has one owner. The proof of Hello's startup
    owns many bytes of the program's initial memory, and it gets them
    from several lists. So it must know that no byte, and no object,
    is in two of the lists. This module checks that for Hello, as
    [StartImageDisjoint](../startup/StartImageDisjoint.v) does for
    hi_atexit.

    Before `c: main` runs, glibc reads the processor's features and
    runs three constructors. The function that reads the features
    takes eighteen globals, and one list holds them. The constructors
    link the standard streams and record the program's arguments, and
    a second list holds the globals that they read. Those two lists
    are the ones that exist for Hello so far. *)

From Stdlib Require Import String ZArith List.
From stdpp Require Import list.
From Nanofil Require Import Term Syntax Values Memory Pieces Heap.
From Glibc Require Import StartImageUnique HelloImageCtors HelloImageCpu.
Import ListNotations.

(** No object and no byte occurs twice in the two lists taken
    together. *)
Lemma hello_start_nodup : NoDup (hello_cpu_globals_ps ++ hello_ctor_ps).*1.
Proof. apply pieces_unique_sound. vm_cast_no_check (eq_refl true). Qed.
