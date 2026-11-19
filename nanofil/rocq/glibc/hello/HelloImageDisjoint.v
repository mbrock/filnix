(** A byte of memory has one owner. The proof of Hello's startup
    owns many bytes of the program's initial memory, and it gets them
    from several lists. So it must know that no byte, and no object,
    is in two of the lists. This module checks that for Hello, as
    [StartImageDisjoint](../hi_atexit/StartImageDisjoint.v) does for
    hi_atexit.

    Before `c: main` runs, glibc reads the processor's features, sets
    up the allocator and the character tables, and runs three
    constructors. Each of these steps takes some globals, and a list
    holds what it takes. One list holds the eighteen globals of the
    feature code. One holds the globals of early initialization, and
    one holds the table of the constructor runner. One holds the
    globals that the constructors read, which are the streams and the
    program's arguments. The last list is the kept frame of
    [HelloStartKept](HelloStartKept.v). It holds the memory that no
    startup call touches and that `c: main` needs. *)

From Stdlib Require Import String ZArith List.
From stdpp Require Import list.
From Nanofil Require Import Term Syntax Values Memory Pieces Heap.
From Glibc Require Import StartImageUnique HelloImageCtors HelloImageCpu HelloImageEarly HelloStartKept.
Import ListNotations.

(** No object and no byte occurs twice in the five lists taken
    together. *)
Lemma hello_start_nodup :
  NoDup (hello_cpu_globals_ps ++ hello_early_ps ++ hello_runner_ps ++ hello_ctor_ps ++ hello_start_kept_ps).*1.
Proof. apply pieces_unique_sound. vm_cast_no_check (eq_refl true). Qed.
