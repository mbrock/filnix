(** Stateful proof-session operations built on [Rocq_engine] and [History].

    A [Session.t] manages one proof file's committed sentence history, scratch
    steps, speculative trials, and incremental reloads. It speaks purely in
    typed OCaml requests, events, and replies, with no knowledge of sockets,
    session-directory files, or JSON encoding. *)

type event =
  | Sentence of { origin : string; line : int; text : string }
      (** A sentence is about to execute. *)
  | Log of string
      (** A formatted feedback or error line for the session log. *)
  | Transcript of string
      (** A non-file sentence was committed to the session transcript. *)
  | Dropped of string
      (** Committed scratch sentences that a [Load] discarded. *)

type request =
  | Load of Rocq_engine.target
  | Step of { origin : string; text : string }
  | Try of { candidates : string list; commit : bool }
  | Check
  | Back of int
  | Goals
  | Nodes

type node = Rocq_engine.snapshot History.entry

type run_report = {
  committed : node list;
  stop : Rocq_engine.stop;
  messages : Rocq_engine.message list;
  goals : Rocq_goals.t option;
}

type candidate_report = {
  candidate : string;
  ok : bool;
  report : run_report;
}

type reply =
  | Restart_needed of string list
  | Loaded of {
      reused : int;
      dropped_scratch : int;
      report : run_report;
    }
  | Stepped of run_report
  | Tried of {
      results : candidate_report list;
      committed_candidate : bool;
      interrupted : bool;
    }
  | Checked of {
      ok : bool;
      goals_before : Rocq_goals.t option;
      committed : node list;
      stop : Rocq_engine.stop;
      messages : Rocq_engine.message list;
    }
  | Backed_up of {
      dropped : int;
      goals : Rocq_goals.t option;
    }
  | Goals_view of Rocq_goals.t option
  | Nodes_list of node list
  | Interrupted
  | Failed_with_exn of string

type t

val create : file:string -> args:string list -> emit:(event -> unit) -> t
(** Initialize Rocq with [args] and open a fresh session for proof file [file]. *)

val node_count : t -> int
(** Number of currently committed sentences in the session. *)

val handle : t -> request -> reply
(** Execute [request] against [t], restoring Rocq's global state to the
    session's committed tip before returning even if execution fails or is
    interrupted. *)
