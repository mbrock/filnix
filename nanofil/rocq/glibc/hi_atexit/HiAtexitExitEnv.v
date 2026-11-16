(** Registration and exit use the linked program's static handler
    objects. This file records their addresses and checks their layout
    and global bindings. Execution can use these facts independently
    of the proof that the loader image owns the initial fields. *)

From Glibc Require Import GlibcTactics.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Values Memory.
From Glibc Require Import AtexitLogic HiAtexitGe.
Open Scope Z_scope.

(** The registration lock, completion flag, counter, list head and
    handler array occupy these linked static objects. *)
Definition hi_exit_objs : exit_objs :=
  mkExitObjs 69296 (mkRegion 69296 69304 GlobalData Live)
    76128 (mkRegion 76128 76136 GlobalData Live)
    69328 (mkRegion 69328 69336 GlobalData Live)
    69264 (mkRegion 69264 69272 GlobalData Live)
    69360 (mkRegion 69360 70400 GlobalData Live).

(** Every registration access fits its actual static object. *)
Lemma hi_exit_layout : exit_layout hi_exit_objs.
Proof. vm_compute. intuition congruence. Qed.

(** Registration uses the linked program's actual globals. *)
Lemma hi_exit_globals : exit_globals hge hi_exit_objs.
Proof. vm_compute. repeat split; reflexivity. Qed.
