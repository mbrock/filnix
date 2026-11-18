(** Cooperative sentence cancellation across the server and Rocq domains.

    Rocq's own interrupt flag is not polled inside kernel reduction such as
    [vm_compute] or [lazy], whereas OCaml delivers [SIGINT] as [Sys.Break] at
    every safe point. This module coordinates [SIGINT] between the two domains
    so that:
    - the socket server domain blocks [SIGINT] on its OS thread and never sees
      [Sys.Break] in its event loop;
    - [SIGINT] raises only while a Rocq sentence is actively running inside
      [with_armed] and cancellation has been requested;
    - a cancel request arriving between sentences is caught before the next
      sentence begins, and a late signal arriving after a job finishes is
      harmlessly ignored. *)

exception Cancelled

val install_rocq_handler : unit -> unit
(** Install the [SIGINT] handler on the main (Rocq) domain. Call this after
    [Coqinit] has finished installing its own signal handler. *)

val block_in_current_thread : unit -> unit
(** Block [SIGINT] on the calling thread so process-directed signals land on
    the main Rocq domain instead. *)

val reset_for_job : unit -> unit
(** Clear any cancellation request left over from a previous job. *)

val is_requested : unit -> bool
(** Report whether cancellation has been requested for the current job. *)

val request_cancel : unit -> unit
(** Request cancellation of the running job and, if Rocq is currently inside
    [with_armed], send [SIGINT] to interrupt execution. *)

val with_armed : (unit -> 'a) -> 'a
(** Execute [f ()] with [SIGINT] translation armed, converting [Sys.Break] into
    [Cancelled]. Raises [Cancelled] immediately if [is_requested ()] is already
    true. *)
