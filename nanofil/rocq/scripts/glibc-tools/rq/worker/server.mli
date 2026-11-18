(** Unix-socket server and session-directory event follower.

    Runs in its own OCaml domain so [status], [cancel], and [withdraw] requests
    are answered immediately while the main domain is blocked inside Rocq. A
    single daemon fiber ([follow_events]) consumes [worker_event]s in order and
    is the sole writer of [Session_dir] files. *)

open Eio.Std

type job = (Session.request, Yojson.Safe.t) Job_queue.job
type queue = (Session.request, Yojson.Safe.t) Job_queue.t

type worker_event =
  | Ready
  | Startup_failed of string
  | Job_started of int
  | Job_finished of {
      job : job;
      reply : Yojson.Safe.t;
      nodes : int;
    }
  | Session_event of Session.event

val run :
  net:[> [> `Generic ] Eio.Net.ty ] r ->
  fs:Eio.Fs.dir_ty Eio.Path.t ->
  clock:float Eio.Time.clock_ty r ->
  dir:string ->
  queue:queue ->
  events:worker_event Eio.Stream.t ->
  unit ->
  'a
(** Bind [dir/sock], start following [events] into [dir]'s status and log files,
    and serve client connections until a [Stop] request arrives, then mark the
    session stopped and exit the worker process cleanly. *)
