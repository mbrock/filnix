#!/usr/bin/env python3
"""List the open premises of Hello's safety theorem and count them.

The theorem is hello_never_panics in rocq/glibc/hello/HelloStartNeverPanics.v,
which starts where the runtime calls __libc_start_main. This script reads
its statement from the source and splits it at the top-level arrows. Each
arrow's left side is one premise, except:

- the start_state premise says which states the theorem covers, like the
  binders, so it is not counted;
- hello_link ge o and hello_layout ge o count once per field of their
  records, which are read from their Record definitions;
- the last premise, which describes the initial heap for every ghost
  state, counts once per conjunct, plus once per field of the HelloCore
  record it chooses. The field hd_priv is the callees' private state,
  which the caller picks rather than proves, so it is not counted.
  Its body, hello_tb_contracts in HelloStartWp.v, counts three
  obligations, each with its own label: the printer of getopt's
  warnings, the printer of its long-option warnings, and the build of
  hd_priv from the objects that startup leaves. Its other conjuncts
  only say how the printers borrow their state, so they are not counted.

A section hypothesis that the proof uses (`Proof using H`) is a premise
of the closed theorem even though the statement does not show it, so it
counts once, with the label from SECTION_LABELS. Premises in
PREMISE_LABELS, such as runtime contracts, print with their label.

Each premise also carries a tag from TAGS, naming the work that
discharges it, and the script prints how many premises each tag has
under the total. A premise that no tag matches is tagged untagged.

The binders (addresses, regions, argv) are not premises. The conclusion
is not counted. The script exits 1 if it cannot find the statement.
"""
import re
import sys
from pathlib import Path

GLIBC = Path(__file__).resolve().parent.parent / 'rocq' / 'glibc'
THEOREM = GLIBC / 'hello' / 'HelloStartNeverPanics.v'
CONTRACTS = GLIBC / 'hello' / 'HelloStartWp.v'
RECORDS = {
    'hello_link': GLIBC / 'hello' / 'HelloGlibcLibsT.v',
    'hello_layout': GLIBC / 'hello' / 'HelloGlibcDebts.v',
    'HelloCore': GLIBC / 'hello' / 'HelloGlibcDebts.v',
}
NOT_PREMISES = {'hd_priv'}
SECTION_LABELS = {}
# The first pattern that a premise's text matches gives its tag.
TAGS = [
    (r'^In [12] |frees_heap', 'runtime/OS'),
    (r'start_c_locale', 'environment'),
    (r'ow_leaf4_ends', 'CPU'),
    (r'^R\.ready', 'adequacy'),
    (r'hd_setlocale_|hd_mbsrtowcs', 'locale'),
    (r'hd_version_etc|hd_print|hd_emit_bug|hd_error_|hd_wprintf', 'printf'),
    (r'hd_close_stdout', 'close_stdout'),
    (r'getopt_l?diag_rule|build hd_priv', 'getopt'),
]
PREMISE_LABELS = {
    'ow_leaf4_ends': 'CPU hypothesis: the processor reports its caches in the way glibc reads them',
    'frees_heap': "runtime contract: the environment's free frees heap objects",
    'start_c_locale': 'environment: the process environment selects the C locale',
}


def uncomment(text):
    out, depth, i = [], 0, 0
    while i < len(text):
        if text.startswith('(*', i):
            depth, i = depth + 1, i + 2
        elif depth and text.startswith('*)', i):
            depth, i = depth - 1, i + 2
        else:
            if not depth:
                out.append(text[i])
            i += 1
    return ''.join(out)


def split_top(text, sep):
    """Split text at sep where no bracket is open."""
    parts, depth, start, i = [], 0, 0, 0
    while i < len(text):
        c = text[i]
        if c in '([{':
            depth += 1
        elif c in ')]}':
            depth -= 1
        elif depth == 0 and text.startswith(sep, i):
            parts.append(text[start:i])
            i += len(sep)
            start = i
            continue
        i += 1
    parts.append(text[start:])
    return [' '.join(p.split()) for p in parts]


def record_fields(name):
    text = uncomment(RECORDS[name].read_text())
    m = re.search(rf'Record {name}\b[^{{]*{{(.*?)\n}}\.', text, re.S)
    if not m:
        sys.exit(f'hello_premises: Record {name} not found')
    return [f.split(' :', 1)[0].strip() for f in split_top(m[1], ';')]


def strip_parens(s):
    while s.startswith('(') and s.endswith(')') and len(split_top(s[1:-1], ')')) == 1:
        s = s[1:-1].strip()
    return s


def tb_contracts():
    """The obligations inside hello_tb_contracts, one per counted conjunct."""
    text = uncomment(CONTRACTS.read_text())
    m = re.search(r'Definition hello_tb_contracts\b.*?:=(.*?)\.\n', text, re.S)
    if not m:
        sys.exit('hello_premises: Definition hello_tb_contracts not found')
    body = re.split(r'\sin\s', m[1])[-1]
    out = []
    for c in split_top(body, '/\\'):
        c = strip_parens(c)
        if c.startswith('getopt_diag_rule'):
            out.append(f"contract: getopt's warning printer ({c})")
        elif c.startswith('getopt_ldiag_rule'):
            out.append(f"contract: getopt's long-option warning printer ({c})")
        elif c.endswith('hd_priv (final_world w0 tb) hge o (debt tb)') and '==∗' in c:
            out.append(f"contract: build hd_priv from the objects startup leaves ({c})")
    if len(out) != 3:
        sys.exit(f'hello_premises: expected 3 counted conjuncts in hello_tb_contracts, found {len(out)}')
    return out


def tag(p):
    return next((t for pat, t in TAGS if re.search(pat, p)), 'untagged')


def premises():
    text = uncomment(THEOREM.read_text())
    m = re.search(r'Theorem hello_never_panics\b(.*?)\nProof\b([^.]*)\.', text, re.S)
    if not m:
        sys.exit('hello_premises: Theorem hello_never_panics not found')
    statement = split_top(m[1], ':')
    arrows = split_top(':'.join(statement[1:]), '->')[:-1]
    out = []
    for p in arrows[:-1]:
        head = p.split()
        if p.startswith('start_state '):
            continue
        if p.split()[0] in PREMISE_LABELS:
            out.append(f'{PREMISE_LABELS[p.split()[0]]} ({p})')
            continue
        if p in ('hello_link ge o', 'hello_layout ge o'):
            out += [f'{head[0]}.{f}' for f in record_fields(head[0])]
        else:
            out.append(p)
    # The heap premise: forall ghost state, exists choices, [let ... in] body.
    heap = strip_parens(arrows[-1])
    _, rest = heap.split(',', 1) if heap.startswith('forall') else ('', heap)
    choices, body = split_top(rest.strip(), ',')[0], ','.join(split_top(rest.strip(), ',')[1:])
    if 'HelloCore' in choices:
        out += [f'HelloCore.{f}' for f in record_fields('HelloCore') if f not in NOT_PREMISES]
    body = split_top(body.strip(), ' in ')[-1]
    for c in split_top(body, '/\\'):
        if 'hello_tb_contracts' in c:
            out += tb_contracts()
        else:
            out.append(c)
    used = m[2].split()
    if used[:1] == ['using']:
        for h in used[1:]:
            if re.search(rf'Context \({h}\b', text):
                out.append(f'{SECTION_LABELS.get(h, "section hypothesis")} [{h}]')
    return out


if __name__ == '__main__':
    ps = premises()
    for n, p in enumerate(ps, 1):
        line = f'[{tag(p)}] {p}'
        print(f'{n:3d}. {line if len(line) <= 110 else line[:107] + "..."}')
    print(f'open premises: {len(ps)}')
    counts = {}
    for p in ps:
        counts[tag(p)] = counts.get(tag(p), 0) + 1
    for t, c in sorted(counts.items(), key=lambda tc: (-tc[1], tc[0])):
        print(f'  {t}: {c}')
