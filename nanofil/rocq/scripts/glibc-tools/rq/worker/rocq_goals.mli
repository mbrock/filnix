(** Structured proof-goal extraction from a Rocq state snapshot.

    Goals are returned as plain OCaml records without JSON formatting so callers
    and protocol encoders remain decoupled from [Evd] and [Printer]. *)

type hyp = {
  name : string;
  ty : string;
  body : string option;
}

type goal = {
  id : string;
  hyps : hyp list;  (** Ordered oldest-first, matching Rocq's goal display. *)
  concl : string;
}

type t = {
  proof_name : string;
  focused_count : int;
  focused : goal list;
  unfocused_count : int;
  shelved_count : int;
  shelved : goal list;
  given_up_count : int;
}

type detail = [ `Summary | `Full ]
(** [`Summary] formats at most the first focused goal and omits shelved goal
    bodies; [`Full] formats every focused and shelved goal. *)

val has_open_proof : Vernacstate.t -> bool
(** Report whether [st] has an open proof on the lemma stack. *)

val inspect : detail:detail -> Vernacstate.t -> t option
(** Extract the open proof obligations of [st], or [None] when no proof is open.
    Unfreezes [st] into Rocq's global environment when a proof is present so
    term printing sees the environment of [st]. *)
