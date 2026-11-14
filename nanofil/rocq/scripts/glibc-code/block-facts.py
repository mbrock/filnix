"""Print advisory block facts without adding executable IR or proof premises."""
from pathlib import Path
import runpy

helpers = runpy.run_path(str(Path(__file__).with_name('source.py')))
string, atom, listing = (helpers[n] for n in ('string', 'atom', 'listing'))


def block_definitions(functions):
    groups = {}
    for row in functions:
        fn = row['function']
        text = ''
        for field in ('live_in', 'live_out'):
            values = listing(f'({atom(b["label"])}, {listing(atom(t) for t in b[field])})'
                             for b in row['blocks'])
            text += f'\nDefinition {field} : list (name * list name) :=\n  {values}.\n'
        blocks = []
        for block in row['blocks']:
            accesses = []
            for access in block['footprint']:
                address = access['address']
                a = ('(TInt (' + str(address['name']) + '))' if address['kind'] == 'const' else
                     f'(TApp {string(address["kind"])} [{atom(address["name"])}])')
                root = 'None' if access['root'] is None else f'(Some {atom(access["root"])})'
                width = 'None' if access['width'] is None else f'(Some {access["width"]})'
                distance = 'None' if access['root_offset'] is None else f'(Some ({access["root_offset"]}))'
                reads, writes = str(access['read']).lower(), str(access['write']).lower()
                accesses.append(f'({access["index"]}%N, {a}, ({access["offset"]}), {width}, '
                                f'{reads}, {writes}, {root}, {distance}, {string(access["path"])})')
            blocks.append(f'({atom(block["label"])}, {listing(accesses)})')
        text += f'''
(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  {listing(blocks)}.

'''
        groups[fn] = text
    return groups
