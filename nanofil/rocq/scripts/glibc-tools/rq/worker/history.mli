(** Chronological history of committed sentences and incremental reload planning.

    Parametric over the snapshot type ['st] so history manipulation and reload
    diffing remain independent of Rocq internals and directly unit-testable. *)

type 'st entry = {
  origin : string;  (** ["file"] for file-backed sentences, or a step/try label *)
  text : string;
  span : Source.span;
  state : 'st;
  ms : float;
  is_query : bool;
  defined_names : string list;
}

type 'st t
(** An ordered history of committed entries alongside the initial snapshot that
    precedes the first entry. *)

val empty : initial:'st -> 'st t
val length : 'st t -> int

val tip : 'st t -> 'st
(** The snapshot after the most recently committed entry, or [initial] when empty. *)

val entries : 'st t -> 'st entry list
(** All committed entries in chronological (oldest-first) order. *)

val append : 'st t -> 'st entry list -> 'st t
(** Append chronological [entries] to the end of [t]. *)

val drop_last : int -> 'st t -> int * 'st t
(** [drop_last n t] removes up to [n] most-recent entries and returns
    [(dropped_count, remaining_history)]. *)

type 'st reload_plan = {
  kept : 'st t;
  reused_count : int;
  resume_offset : int;
  dropped_scratch : 'st entry list;  (** Chronological order. *)
}

val plan_reload :
  'st t ->
  first_diff:int ->
  target_end_offset:int ->
  reopen_theorem:string option ->
  'st reload_plan
(** Compute which prefix of file entries in [t] remains valid after an edit at
    byte [first_diff].

    - Non-file ("scratch") entries are separated into [dropped_scratch].
    - File entries are kept only while [entry.span.ep < first_diff] and
      [entry.span.ep <= target_end_offset]. The strict [< first_diff] ensures a
      sentence whose terminating dot sits adjacent to the edit is re-parsed in
      case the dot became a projection [a.b].
    - When [reopen_theorem] is [Some name] and [name] was already declared in
      the kept prefix, the prefix is truncated to right before that declaration
      so re-execution stops at [name]'s open proof again. *)
