"""Print source hints as two-way notations that name temporaries after the C expression they hold."""
from pathlib import Path
import re
import runpy

string = runpy.run_path(str(Path(__file__).with_name('source.py')))['string']

COMPARE = {'eq': '==', 'ne': '!=', 'slt': '<', 'sle': '<=', 'sgt': '>', 'sge': '>=',
           'ult': '<u', 'ule': '<=u', 'ugt': '>u', 'uge': '>=u'}
# A name is one notation token between single guillemets. Rocq's other tools
# read a comment at "(*", so a name never holds one, and it holds no space,
# quote or guillemet.
TOKEN = re.compile(r'[!-~]+')
FORBIDDEN = ('(*', '*)', '"', "'")
DEPTH = 12


def offset(text, k):
    return text if k == 0 else f'{text}{"+" if k > 0 else "-"}{abs(k)}'


def expressions(shapes, paths):
    """Give each temporary the text of its C expression, or None without one.

    A named temporary is its variable, and an address hint or a global is & and
    the name. A constant pointer addition is BASE+K. A check is chk(BASE), the
    address of a pointer as an integer is addr(BASE), and a comparison joins its
    operands with the C operator. A load is the field path of its footprint row
    when the layouts name one, and [ADDRESS] otherwise. A direct call's result is
    FUNCTION(). Every other temporary, and any expression that rests on one, has
    no text.
    """
    shape = {t: (l, i, s) for t, l, i, s in shapes}
    memo = {}

    def text(t, depth):
        if t in memo:
            return memo[t]
        if t not in shape or depth > DEPTH:
            return None
        label, index, s = shape[t]
        kind, result = s[0], None
        if kind == 'named':
            result = s[1]
        elif kind in ('address', 'global'):
            result = '&' + s[1]
        elif kind == 'same':
            result = text(s[1], depth + 1)
        elif kind == 'add':
            base = text(s[1], depth + 1)
            result = base and offset(base, s[2])
        elif kind in ('check', 'addr'):
            base = text(s[1], depth + 1)
            result = base and f'{"chk" if kind == "check" else "addr"}({base})'
        elif kind == 'load':
            path = paths.get((label, index), 'opaque')
            # A path through a promoted local, pr.N, names no C variable.
            if path != 'opaque' and not path.startswith('pr.'):
                result = path
            else:
                base = text(s[1], depth + 1)
                # The check on the address is not part of the C expression.
                result = base and '[' + offset(re.sub(r'^chk\((.*)\)$', r'\1', base), s[2]) + ']'
        elif kind == 'cmp':
            sides = [str(v) if k == 'const' else text(v, depth + 1) for k, v in s[2:]]
            result = all(sides) and sides[0] + COMPARE.get(s[1], s[1]) + sides[1] or None
        elif kind == 'call':
            result = s[1] + '()'
        if result is not None and (not TOKEN.fullmatch(result) or any(f in result for f in FORBIDDEN)):
            result = None
        memo[t] = result
        return result

    return [(t, label, s[0], text(t, 0)) for t, label, _, s in shapes]


def function_names(shapes, paths):
    """Name the temporaries of one function, and count them by kind.

    The first temporary that holds an expression takes the expression as its
    name. The compiler computes one C expression again in later blocks, so a
    later temporary with the same expression gets @ and the label of its block,
    and .N for the Nth such temporary of one block. Only these ambiguous names
    carry a suffix. The suffixes follow the compiler's label numbering, so a
    recompile that renumbers labels changes them.
    """
    used, rows = set(), []
    count = dict(named=0, derived=0, raw=0, suffixed=0)
    for t, label, kind, text in expressions(shapes, paths):
        if text is None:
            count['raw'] += 1
            continue
        count['named' if kind in ('named', 'address', 'global') else 'derived'] += 1
        name, n = text, 1
        while name in used:
            n += 1
            name = f'{text}@{label}' if n == 2 else f'{text}@{label}.{n - 1}'
        if name != text:
            count['suffixed'] += 1
        used.add(name)
        rows.append((t, name))
    return rows, count


def name_tables(name, facts, block_facts):
    """Return the text of NAMENames.v and the counts of each function."""
    footprints = {r['function']: {(b['label'], a['index']): a['path']
                                  for b in r['blocks'] for a in b['footprint']} for r in block_facts}
    text = f'''(** These notations name the temporaries of compiled functions after the C expression each one holds.
    A proof imports the module of its own function, and then writes and reads a temporary by that name.
    Every name is one token between single guillemets, so it cannot be read as a term about proof variables.
    A name with @ and a label belongs to a later temporary that holds the same expression.
    These names are notations for the temporaries' own names; they add no premise.
    The code generator reproduces this file from the capture; do not edit it. *)

From Stdlib Require Import String.
From Nanofil Require Import Term.
Open Scope string_scope.

Module {name}Names.
'''
    counts, identifiers = {}, set()
    for row in facts:
        fn = row['function']
        ident = 'fn_' + re.sub('[^a-zA-Z0-9_]', '_', fn)
        if ident in identifiers:
            raise ValueError(f"name table identifier collision: {fn}")
        identifiers.add(ident)
        rows, counts[fn] = function_names(row['temp_shapes'], footprints.get(fn, {}))
        lines = ''.join(f'''Notation "'\u2039{n}\u203a'" := (TAtom {string(t)}).\n''' for t, n in rows)
        text += f'\nModule {ident}.\n{lines}End {ident}.\n'
    return text + f'\nEnd {name}Names.\n', counts
