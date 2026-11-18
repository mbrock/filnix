#!/usr/bin/env python3
"""Count every premise of hello_never_panics, including start_state.

The theorem has six data parameters and states its hypotheses as arrows,
outside a Rocq section. Refuse another header rather than overlook a binder
or a section hypothesis. An unrecognized premise still counts, in full.
"""
import re
from pathlib import Path

THEOREM = Path(__file__).resolve().parents[1] / 'rocq/glibc/hello/HelloStartNeverPanics.v'

# hello_start_witness satisfies these together, with InterpRuntime for R.ready.
KNOWN = {
    'start_state hello_image_module w0 m w xs': 'start state',
    'In 1 (ow_fds w0)': 'runtime/OS',
    'In 2 (ow_fds w0)': 'runtime/OS',
    'start_c_locale m xs': 'environment',
    'ow_leaf4_ends w0 = true': 'CPU',
    'R.ready s m': 'adequacy',
}


def premises(source):
    # Strip nested Rocq comments before looking for the declaration.
    comment = r'\(\*(?:(?!\(\*|\*\)).)*\*\)'
    while re.search(comment, source, re.S):
        source = re.sub(comment, ' ', source, flags=re.S)
    m = re.search(r'\bTheorem hello_never_panics\s+w0\s+m\s+s\s+w\s+xs\s+fuel\s*:(.*?)\.\s*Proof\.', source, re.S)
    if not m or re.search(r'\b(?:Section|Context|Variables?|Hypothes[ie]s)\b', source[:m.start()]):
        raise SystemExit('hello_premises: expected six data binders and an explicit, non-section statement')
    body = m[1]
    depth = start = 0
    result = []
    for token in re.finditer(r'"(?:[^"]|"")*"|[()\[\]{}]|->|→', body):
        if token[0] in ('(', '[', '{'):
            depth += 1
        elif token[0] in (')', ']', '}'):
            depth -= 1
        elif token[0] in ('->', '→') and depth == 0:
            result.append(' '.join(body[start:token.start()].split()))
            start = token.end()
    if depth or not body[start:].lstrip().startswith('labelled_safe '):
        raise SystemExit('hello_premises: expected a labelled_safe conclusion')
    return result


if __name__ == '__main__':
    ps = premises(THEOREM.read_text())
    for n, p in enumerate(ps, 1):
        print(f'{n:3d}. [{KNOWN.get(p, "unknown")}] {p}')
    unknown = sum(p not in KNOWN for p in ps)
    starts = sum(KNOWN.get(p) == 'start state' for p in ps)
    print(f'theorem premises: {len(ps)}')
    print(f'  start state: {starts}')
    print(f'  machine, OS, runtime and environment assumptions: {len(ps) - starts - unknown}')
    print(f'  proof debts or unclassified premises: {unknown}')
    print(f'not known satisfiable: {unknown} (known premises witnessed by hello_start_witness for InterpRuntime)')
