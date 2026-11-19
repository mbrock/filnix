"""Write shared captured records and each fixture's view of them."""
from collections import defaultdict
from hashlib import sha256
import runpy
from pathlib import Path

helpers = runpy.run_path(str(Path(__file__).with_name('source.py')))
string, listing = helpers['string'], helpers['listing']
identifier = runpy.run_path(str(Path(__file__).with_name('typed.py')))['file_identifier']

SHARED = Path('layouts')
IMPORTS = '''From Stdlib Require Import String ZArith List.
From Glibc Require Import LayoutTables.
'''
SCOPES = '''Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
'''


def fixture_layout(name, rows):
    records = {}
    missing = set()
    for row in rows:
        tag = row['tag']
        if row.get('missing', False):
            missing.add(tag)
            continue
        record = (tag, row['size'], row['align'], tuple(map(tuple, row['fields'])))
        if records.setdefault(tag, record) != record:
            raise ValueError(f"inconsistent layouts for {tag} in {name}")
    return sorted(records.values()), sorted(missing - records.keys())


def gallina_record(record):
    tag, size, align, fields = record
    entries = listing(f'({string(field)}, {offset}, {width}, {alignment})'
                      for field, offset, width, alignment in fields)
    return f'(mkRecordLayout {string(tag)} {size} {align} {entries})'


def layout_tables(fixtures):
    """Return paths and contents for the complete set of layout files."""
    users = defaultdict(list)
    for path, (records, _) in sorted(fixtures.items()):
        for record in records:
            users[record].append(path)
    # Records with the same set of users can share a file without widening
    # any fixture's dependencies.
    groups = defaultdict(list)
    for record, paths in users.items():
        if len(paths) > 1:
            groups[tuple(paths)].append(record)

    files, refs = {}, {}
    for records in groups.values():
        header = '''(** Multiple fixtures use these captured C layouts.
    Each fixture refers to the records that its functions use.
    The code generator reproduces this file from the capture. Do not edit. *)

'''
        names = {record: 'layout_' + identifier(record[0]) for record in sorted(records)}
        definitions = [f'Definition {name} : record_layout :=\n  {gallina_record(record)}.\n'
                       for record, name in names.items()]
        source = header + IMPORTS + SCOPES + '\n' + '\n'.join(definitions)
        # Keep old definitions available until every referencing view has been updated.
        module = 'CapturedLayouts_' + sha256(source.encode()).hexdigest()[:16]
        files[SHARED / (module + '.v')] = source
        refs.update({record: (module, name) for record, name in names.items()})

    for path, (records, missing) in sorted(fixtures.items()):
        imports = sorted({refs[r][0] for r in records if r in refs})
        requirements = f'From Glibc Require {" ".join(imports)}.\n' if imports else ''
        entries = [('.'.join(refs[record]) if record in refs else gallina_record(record))
                   for record in records]
        layouts = ';\n   '.join(entries)
        files[path] = f'''(** These tables record the C layouts used by this fixture's functions.
    The compiler supplies field offsets, sizes and type alignments from its completed layouts.
    The code generator reproduces this file from the capture. Do not edit. *)

{IMPORTS}{requirements}{SCOPES}
Module {path.stem}.

Local Definition layouts : list record_layout :=
  [{layouts}].

(** Each named record has its complete size and record alignment in bytes. *)
Definition records := layout_records layouts.

(** These used tags have only forward declarations in the captured units. *)
Definition unavailable : list string := {listing(string(tag) for tag in missing)}.

(** Each field has a tag, name, byte offset, type size and type alignment. *)
Definition fields := layout_fields layouts.

(** The lookup returns [None] if the fixture has no matching field. *)
Definition field_offset := layout_field_offset fields.

End {path.stem}.
'''
    return files
