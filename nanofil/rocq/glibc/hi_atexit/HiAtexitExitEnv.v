(** Registration and exit use the linked program's static handler
    objects. This file records their addresses and checks their layout
    and global bindings. Execution can use these facts independently
    of the proof that the loader image owns the initial fields. *)

From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Values Memory.
From Glibc Require Import AtexitLogic HiAtexitGe.
Open Scope Z_scope.

(** The registration lock, completion flag, counter, list head and
    handler array occupy these linked static objects. *)
Definition hi_exit_objs : exit_objs :=
  mkExitObjs 66864 (mkRegion 66864 66872 GlobalData Live)
    73696 (mkRegion 73696 73704 GlobalData Live)
    66896 (mkRegion 66896 66904 GlobalData Live)
    66832 (mkRegion 66832 66840 GlobalData Live)
    66928 (mkRegion 66928 67968 GlobalData Live).

(** Every registration access fits its actual static object. *)
Lemma hi_exit_layout : exit_layout hi_exit_objs.
Proof. vm_compute. intuition congruence. Qed.

(** Registration uses the linked program's actual globals. *)
Lemma hi_exit_globals : exit_globals hge hi_exit_objs.
Proof. vm_compute. repeat split; reflexivity. Qed.
