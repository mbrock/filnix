(** Wire protocol between the [rq] CLI and [rq-worker].

    Every JSON schema spoken over the session socket or persisted in
    [status.json] and [job-N.json] lives in this module. Domain modules
    ([Session], [Rocq_goals], [Rocq_engine], [History], [Job_queue]) exchange
    typed OCaml values and never construct JSON directly.

    Each socket connection carries one JSON request line:
    - Control requests ([Status], [Cancel], [Withdraw], [Stop]) receive one
      immediate JSON reply line, even while Rocq is busy.
    - Session job requests ([Enqueue]) receive an immediate acknowledgement line
      giving the assigned job ID and queue depth, followed (unless [detach] is
      true) by a second JSON line containing the completed job result. *)

type job_request = {
  cmd : string;
  request : Session.request;
  detach : bool;
}

type client_msg =
  | Status
  | Cancel of int option
  | Withdraw of int
  | Stop
  | Enqueue of job_request

type worker_state =
  | Starting
  | Idle
  | Busy
  | Failed
  | Stopped

val worker_state_name : worker_state -> string

type active_sentence = {
  origin : string;
  line : int;
  text : string;
  started : float;
}

type worker_status = {
  state : worker_state;
  pid : int;
  running_job : int;
  job_started : float;
  nodes : int;
  queued : int;
  updated : float;
  sentence : active_sentence option;
}

val decode_client_msg : string -> (client_msg, string) result
(** Parse a single JSON request line from a connected client. *)

val encode_error : string -> Yojson.Safe.t
val encode_status : worker_status -> Yojson.Safe.t
val encode_ack : job_id:int -> queued:int -> starting:bool -> Yojson.Safe.t
val encode_cancelled : cancelled:int option -> running:int -> Yojson.Safe.t
val encode_withdrawn_status : job_id:int -> state:string -> Yojson.Safe.t
val encode_stopped : unit -> Yojson.Safe.t

val encode_job_withdrawn : job_id:int -> cmd:string -> Yojson.Safe.t
val encode_job_startup_error :
  job_id:int -> cmd:string -> seconds:float -> string -> Yojson.Safe.t

val encode_job_reply :
  job_id:int ->
  cmd:string ->
  seconds:float ->
  nodes:int ->
  Session.reply ->
  Yojson.Safe.t
