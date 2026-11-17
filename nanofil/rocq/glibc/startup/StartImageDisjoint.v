(** A byte of memory has one owner. The proof of hi_atexit's startup
    owns many bytes of the program's initial memory, and it gets them
    from several lists. So it must know that no byte, and no object,
    is in two of the lists. This module checks that.

    There are seven lists. Six of them hold what the calls of startup
    take: the globals of `c: init_cpu_features`, the globals of early
    initialization, the table of the constructor runner, the streams
    and their list, the globals of `c: _init_first`, and the table
    pointers of the streams. The seventh holds what no call of startup
    touches and `c: main` needs. *)

From Stdlib Require Import String ZArith List.
From stdpp Require Import list.
From Nanofil Require Import Term Syntax Values Memory Pieces Heap.
From Glibc Require Import HiAtexitInitial HiAtexitInitialList StartInitFirstImage StartImageUnique StartImageCpu
  StartVtablesImage StartImageEarly HiAtexitStartBridge.
Import ListNotations.

(** No object and no byte occurs twice in the seven lists taken
    together. The check sorts the entries, as
    [StartImageUnique](StartImageUnique.v) explains. *)
Lemma hi_start_nodup :
  NoDup (hi_cpu_globals_ps ++ hi_early_ps ++ hi_runner_ps ++ hi_initial_list_ps ++ hi_init_first_ps ++
         hi_vtables_ps ++ hi_start_kept_ps).*1.
Proof. apply pieces_unique_sound. vm_cast_no_check (eq_refl true). Qed.
