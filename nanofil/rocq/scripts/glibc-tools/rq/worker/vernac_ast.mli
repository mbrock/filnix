(** Structural classification of parsed Rocq vernacular commands.

    Inspecting [Vernacexpr.vernac_control] directly avoids brittle text regexes
    over attributes, comments, universe binders, and [Time] prefixes. *)

val is_query : Vernacexpr.vernac_control -> bool
(** True for read-only inspection or assertion commands such as [Show], [Check],
    [Print], [About], [Search], [Locate], [Compute], [Eval], [Fail], and
    [Succeed] that should not be recorded as committed history steps. *)

val is_proof_header : Vernacexpr.vernac_control -> bool
(** True for [Proof.], [Proof using ...], and [Proof with ...]. *)

val defined_names : Vernacexpr.vernac_control -> string list
(** Identifiers declared by a theorem, lemma, definition, instance, or fixpoint
    sentence, used to match [--theorem NAME] targets. *)
