(** This file names the one runtime and logic instance used by the glibc proofs.
    Each proof imports these modules instead of creating its own logic instance. *)
From Nanofil Require Import Runtime Logic.
Module R : Runtime := InterpRuntime.
Module LG0 := Logic R.

(** A memory rule must use the caller's description of the world. This mode
    waits until that description is known before choosing a safepoint rule.
    Without it, [wp_read_with] in LibioDoAllocBase.v picks [no_world_stable]
    too early instead of the caller's [os_wi]. *)
#[export] Hint Mode LG0.SafepointStable + ! : typeclass_instances.
