(** On-disk file layout of an [rq] session directory.

    A session directory holds the Unix socket alongside status and history files
    that [rq ls], [rq status], [rq log], and [rq wait] inspect directly:
    - [sock]: Unix-domain stream socket accepting client requests;
    - [status.json]: current worker state, active job, and active sentence;
    - [job-N.json] and [last-job]: finished job replies for detached or
      reconnected [rq wait] callers;
    - [log]: append-only stream of Rocq messages and errors;
    - [transcript.v]: append-only record of committed scratch sentences;
    - [dropped.v]: scratch sentences discarded by the most recent [reload]. *)

type t

val of_path : _ Eio.Path.t -> t

val socket_native_path : t -> string
(** Native filesystem path of [sock] for [Eio.Net.listen]. *)

val remove_socket : t -> unit
(** Unlink [sock] if present. *)

val write_status : t -> Protocol.worker_status -> unit
(** Atomically replace [status.json]. *)

val write_job_result : t -> job_id:int -> Yojson.Safe.t -> unit
(** Atomically write [job-N.json] and update [last-job]. *)

val append_log : t -> string -> unit
(** Append a line to [log], adding a trailing newline if absent. *)

val append_transcript : t -> string -> unit
(** Append committed scratch text to [transcript.v]. *)

val write_dropped : t -> string -> unit
(** Atomically replace [dropped.v] with discarded scratch sentences. *)
