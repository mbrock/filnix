(** A captured C record carries its name, size, alignment, and fields.
    These projections give each fixture the tables its proofs use to look up named records and fields. *)

From Stdlib Require Import String ZArith List.

(** The compiler supplies the byte offset, type size, and type alignment of each field.
    Flexible arrays have size zero, and bit-fields retain the size and alignment of their declared type. *)
Record record_layout := mkRecordLayout {
  layout_tag : string;
  layout_size : Z;
  layout_alignment : Z;
  layout_members : list (string * Z * Z * Z);
}.

(** The record table pairs each tag with its size and alignment. *)
Definition layout_records (layouts : list record_layout) : list (string * (Z * Z)) :=
  map (fun layout => (layout_tag layout, (layout_size layout, layout_alignment layout))) layouts.

(** The field table associates each field with the tag that declares it. *)
Definition layout_fields (layouts : list record_layout) : list (string * string * Z * Z * Z) :=
  flat_map (fun layout =>
    map (fun field => let '(name, offset, size, alignment) := field in
                      (layout_tag layout, name, offset, size, alignment))
        (layout_members layout)) layouts.

(** The lookup returns the first matching field's offset if one exists. *)
Definition layout_field_offset (fields : list (string * string * Z * Z * Z))
    (tag field : string) : option Z :=
  option_map (fun entry => let '(_, _, offset, _, _) := entry in offset)
    (find (fun entry => let '(t, f, _, _, _) := entry in
      andb (String.eqb t tag) (String.eqb f field)) fields).

(** A proof can name a layout constant without computing a table lookup each time it uses the constant.
    The tactic computes the value during elaboration and fails if the table lacks the entry. *)
Ltac layout_constant entry :=
  let value := eval vm_compute in entry in
  lazymatch value with
  | Some ?constant => exact constant
  | None => fail "Missing captured C layout entry:" entry
  end.
