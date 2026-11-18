(** The interpreter can start the linked Hello image in a state that meets
    every premise of [hello_never_panics]. From that one state, the safety
    theorem rules out both a panic and a normal return to the runtime for
    every [[fuel]] budget. *)
From Nanofil Require Import Runtime HelloLeaf.
From Glibc Require Import Fix StartState HelloImageModule OsRegistry StartLibcStartMain
  HelloStartWitness HelloStartNeverPanics.

Corollary hello_interp_never_panics :
  exists w0 m s w xs,
    start_state hello_image_module w0 m w xs /\ InterpRuntime.ready s m /\
    forall fuel, LG0.L.labelled_safe glibc_os_registry hello_start_ge
      (invocation start_libc_start_main_fn xs) m s w fuel (fun _ => False).
Proof.
  destruct hello_start_witness as (w0 & m & s & w & xs & Hst & Hr & H1 & H2 & Hloc & Hleaf).
  exists w0, m, s, w, xs. split; [exact Hst|]. split; [exact Hr|].
  intro fuel. exact (hello_never_panics w0 m s w xs fuel Hst H1 H2 Hloc Hleaf Hr).
Qed.
