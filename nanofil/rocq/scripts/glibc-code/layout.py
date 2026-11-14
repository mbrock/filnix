"""Print completed record layouts as advisory Gallina tables."""
import runpy
from pathlib import Path

helpers = runpy.run_path(str(Path(__file__).with_name('source.py')))
string, listing = helpers['string'], helpers['listing']


def layout_tables(name, rows):
    records = {}
    for row in rows:
        if row.get('missing', False):
            continue
        tag = row['tag']
        if tag in records and records[tag] != row:
            raise ValueError(f"inconsistent layouts for {tag} in {name}")
        records[tag] = row
    missing = sorted({row['tag'] for row in rows if row.get('missing', False)} - records.keys())
    sizes, fields = [], []
    for tag, row in sorted(records.items()):
        sizes.append(f'({string(tag)}, ({row["size"]}, {row["align"]}))')
        for field, offset, size, align in row['fields']:
            fields.append(f'({string(tag)}, {string(field)}, {offset}, {size}, {align})')
    return f'''(** These tables record the C layouts used by this fixture's functions.
    The compiler supplies field offsets, sizes and type alignments from its completed layouts.
    Offset checks compare hand-written constants against these tables without changing existing proofs.
    Layouts remain advisory data, not premises of soundness theorems.
    The code generator reproduces this file from the capture; do not edit it. *)

From Stdlib Require Import String ZArith List.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Module {name}Layout.

(** Each named record has its complete size and record alignment in bytes. *)
Definition records : list (string * (Z * Z)) :=
  {listing(sizes)}.

(** These used tags have only forward declarations in the captured units. *)
Definition unavailable : list string := {listing(string(tag) for tag in missing)}.

(** Each field has a tag, name, byte offset, type size and type alignment.
    Flexible arrays have zero size; bit-fields retain their declared type's size and alignment. *)
Definition fields : list (string * string * Z * Z * Z) :=
  {listing(fields)}.

(** Missing fields return [None], so an offset check cannot accept an invented entry. *)
Definition field_offset (tag field : string) : option Z :=
  option_map (fun entry => let '(_, _, offset, _, _) := entry in offset)
    (find (fun entry => let '(t, f, _, _, _) := entry in
      andb (String.eqb t tag) (String.eqb f field)) fields).

End {name}Layout.
'''
