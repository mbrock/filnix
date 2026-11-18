(** Low-level driver around Rocq's initialization, parser, and interpreter.

    Rocq keeps its environment, notations, and proof state in process-wide
    mutable globals, and [Pp.string_of_ppcmds] uses [Format.str_formatter],
    which is bound to the main OCaml domain. Every function in this module must
    therefore run on the main domain.

    Proof states are exposed outside this module as abstract [snapshot] values
    so higher-level session code treats states as immutable checkpoints rather
    than juggling [Vernacstate.unfreeze_full_state] directly. *)

type t
type snapshot

type target =
  | End
  | Line of int
  | Theorem of string

type message = {
  level : string;
  text : string;
}

type failure_kind =
  | Syntax
  | Tactic_or_cmd
  | Interrupted

type stop =
  | Done
  | Reached of string
  | Failed of {
      kind : failure_kind;
      text : string;
      span : Source.span;
      message : string;
    }

type outcome = {
  committed : snapshot History.entry list;
  stop : stop;
  messages : message list;
}

type callbacks = {
  on_sentence : origin:string -> line:int -> text:string -> unit;
  on_log : string -> unit;
}

val create : args:string list -> callbacks -> t
(** Initialize the Rocq runtime with CLI [args], attach feedback listeners for
    messages and loaded [.vo] files, and capture the empty library snapshot. *)

val initial_snapshot : t -> snapshot
(** The snapshot captured right after Rocq initialized, before any sentence ran. *)

val restore : snapshot -> unit
(** Make [snapshot] the active global Rocq state. *)

val goals : detail:Rocq_goals.detail -> snapshot -> Rocq_goals.t option
(** Inspect the proof obligations of [snapshot]. *)

val changed_imports : t -> string list
(** Return the paths of any [.vo] files loaded by [Require] whose modification
    times on disk have changed since they were loaded. *)

val run :
  ?file:string ->
  ?keep_queries:bool ->
  t ->
  origin:string ->
  target:target ->
  snapshot ->
  Source.t ->
  offset:int ->
  outcome
(** Parse and execute sentences from [source] starting at byte [offset] from
    [snapshot] until [source] ends, [target] is reached, a sentence fails, or
    cancellation is requested.

    Because commands can extend Rocq's grammar or open proof mode, each sentence
    is parsed in the state produced by the sentence before it. Query commands
    keep their feedback messages in [outcome.messages] without adding an entry
    to [outcome.committed] unless [keep_queries] is true. *)
