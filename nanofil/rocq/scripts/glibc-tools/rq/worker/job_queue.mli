(** Cross-domain FIFO job queue with cooperative withdrawal.

    The socket server domain submits, withdraws, and completes jobs, while the
    main Rocq domain pulls jobs one at a time via [take_next] and marks them
    finished via [finish_running]. Atomic counters track queue depth and the
    active job ID without locking across domains. *)

type state =
  | Queued
  | Running
  | Withdrawn
  | Finished

val state_name : state -> string

type ('req, 'reply) job

val id : (_, _) job -> int
val cmd : (_, _) job -> string
val request : ('req, _) job -> 'req
val state : (_, _) job -> state
val await_reply : (_, 'reply) job -> 'reply

type ('req, 'reply) t

val create : unit -> ('req, 'reply) t

val submit : ('req, 'reply) t -> cmd:string -> 'req -> ('req, 'reply) job * int
(** Enqueue a new job on the server domain and return [(job, jobs_ahead)], where
    [jobs_ahead] is the number of unfinished jobs (queued or running) ahead of
    this one. *)

val withdraw : ('req, 'reply) t -> int -> state
(** Attempt to transition job [id] from [Queued] to [Withdrawn], returning the
    job's resulting state (or [Finished] if [id] is already completed). *)

val complete : ('req, 'reply) t -> ('req, 'reply) job -> 'reply -> unit
(** Remove [job] from the server domain's active-job table and resolve its reply
    promise. Call this after persisting the job's result to disk so waiting
    clients never observe a missing [job-N.json]. *)

val running_job_id : (_, _) t -> int
(** ID of the job currently executing on the worker domain, or [0] when idle. *)

val queued_count : (_, _) t -> int
(** Number of unfinished jobs waiting in line behind any running job. *)

val take_next :
  ('req, 'reply) t ->
  [ `Run of ('req, 'reply) job | `Withdrawn of ('req, 'reply) job ]
(** Block on the worker domain until the next submitted job arrives. Atomically
    transitions a [Queued] job to [Running] and sets [running_job_id], or
    returns [`Withdrawn job] if the client already withdrew it. *)

val finish_running : ('req, 'reply) t -> ('req, 'reply) job -> unit
(** Mark a [Running] job as [Finished] on the worker domain and clear
    [running_job_id]. *)
