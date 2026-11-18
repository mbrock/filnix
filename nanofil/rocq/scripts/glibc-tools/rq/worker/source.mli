(** Source buffers with fast byte-offset to line-and-column mapping.

    Rocq's parser reports locations as 0-based byte offsets into a text
    buffer, while the protocol and CLI work in 1-based lines and columns.
    [Source.t] indexes newline offsets once so span construction and
    [--line] boundary lookups do not rescan the buffer per sentence. *)

type t
(** An immutable text buffer paired with its line-start offset index. *)

type pos = {
  line : int;  (** 1-based line number *)
  col : int;   (** 1-based byte column within the line *)
}

type span = {
  bp : int;         (** 0-based start byte offset *)
  ep : int;         (** 0-based end byte offset (exclusive) *)
  start_pos : pos;
  end_pos : pos;
}

val of_string : string -> t
val text : t -> string
val length : t -> int

val sub : t -> bp:int -> ep:int -> string
(** Extract the substring in [[bp, ep)], clamping both bounds to [[0, length t]]. *)

val pos_of_offset : t -> int -> pos
(** Clamp an offset to [[0, length t]] and return its 1-based line and column. *)

val line_start_offset : t -> int -> int
(** Return the 0-based byte offset where the line containing [offset] begins. *)

val span : t -> bp:int -> ep:int -> span
(** Build a located span for byte range [[bp, ep)] in [t]. *)

val end_of_line : t -> int -> int
(** Return the byte offset of the newline ending 1-based line [n], or
    [length t] when [t] has fewer than [n] lines or lacks a trailing newline. *)

val first_diff_offset : string -> string -> int
(** Return the first byte offset at which two strings differ, or the shorter
    string's length when one is a prefix of the other. *)
