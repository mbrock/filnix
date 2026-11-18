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
  which the caller picks rather than proves, so it is not counted, and
  neither is hd_wide, the state of stdout once it is wide.
  Its body, hello_tb_contracts in HelloStartWp.v, counts two
  obligations, each with its own label: the contract of glibc's
  formatter (vfprintf_has_spec) and the contract of fputs
  (fputs_has_spec).
  The conjunct that fixes hd_priv's shape only says which state the
  caller picks, so it is not counted. Its components are concrete and
  hello_priv_build proves that startup's objects build them.

A section hypothesis that the proof uses (`Proof using H`) is a premise
of the closed theorem even though the statement does not show it, so it
counts once, with the label from SECTION_LABELS. Premises in
PREMISE_LABELS, such as runtime contracts, print with their label.

Each premise also carries a tag from TAGS, naming the work that
discharges it, and the script prints how many premises each tag has
under the total. A premise that no tag matches is tagged untagged.

The tags fall into two kinds, listed in ASSUMPTION_TAGS. An assumption
describes the machine, the operating system, the runtime or the launch
environment that the theorem is about, so it stays in the final theorem.
A proof debt is a contract of glibc code that the proof still has to
discharge from the code itself, so it should reach zero. The script
prints the two kinds separately. The runtime's axioms and the system-call
contracts are not premises of the statement and are not counted here;
runtime-axioms.md lists them.

Each premise also has a status from STATUS, kept by hand: satisfiable,
or unsatisfiable with the reason. An unsatisfiable premise makes the
theorem vacuous, so the script prints how many there are. A premise that
no STATUS entry matches prints as unknown.

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
NOT_PREMISES = {'hd_priv', 'hd_wide'}
SECTION_LABELS = {}
# The first pattern that a premise's text matches gives its tag.
TAGS = [
    (r'^In [12] ', 'runtime/OS'),
    (r'start_c_locale', 'environment'),
    (r'ow_leaf4_ends', 'CPU'),
    (r'^R\.ready', 'adequacy'),
    (r'hd_setlocale_', 'locale'),
    (r'hd_wprintf', 'wprintf (gap W)'),
    (r'hd_close_stdout', 'close_stdout'),
    (r'vfprintf_has_spec', 'printf'),
    (r'fputs_has_spec', 'libio'),
]
# Kept by hand from the satisfiability audit and the fixes after it.
# The first pattern that a premise's text matches gives its status.
SAT = 'satisfiable'
# hello_start_witness exhibits one start state that meets these premises together.
WITNESSED = SAT + ' (checked: hello_start_witness in HelloStartWitness.v)'
STATUS = [
    (r'^In [12] |start_c_locale|ow_leaf4_ends', WITNESSED),
    (r'^R\.ready', SAT + ' for the interpreter\'s runtime, InterpRuntime.ready (checked: hello_start_witness)'),
    (r'hd_setlocale_all', 'unknown: locale_c (HelloLocaleState.v) holds every cell setlocale writes and the constants it '
                          'reads, and the lock is reachable by opening the getopt state with hello_stdio (hello_hd_lend); not yet proved'),
    (r'hd_wprintf', 'unknown: the private state holds the conversion constants and __gconv_lock; not yet checked against a proof'),
    (r'hd_close_stdout', 'unsatisfiable: the failure branch reaches strerror and dcgettext, whose locale state '
                         'no start list owns'),
    (r'vfprintf_has_spec|fputs_has_spec', SAT),
]
# These tags describe the world the theorem is about and stay; every
# other tag is a proof debt that should reach zero.
ASSUMPTION_TAGS = {'runtime/OS', 'environment', 'CPU', 'adequacy'}
PREMISE_LABELS = {
    'ow_leaf4_ends': 'CPU hypothesis: the processor reports its caches in the way glibc reads them',
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
        if c.startswith('HasSpec') and '__vfprintf_internal' in c:
            out.append(f"contract: glibc's formatter, vfprintf_has_spec ({c})")
        elif c.startswith('HasSpec') and '"fputs"' in c:
            out.append(f"contract: glibc's fputs, fputs_has_spec ({c})")
    if len(out) != 2:
        sys.exit(f'hello_premises: expected 2 counted conjuncts in hello_tb_contracts, found {len(out)}')
    return out


def tag(p):
    return next((t for pat, t in TAGS if re.search(pat, p)), 'untagged')


def status(p):
    return next((st for pat, st in STATUS if re.search(pat, p)), 'unknown')


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
        print(f'       status: {status(p)}')
    print(f'open premises: {len(ps)}')
    counts = {}
    for p in ps:
        counts[tag(p)] = counts.get(tag(p), 0) + 1
    for title, stays in (('assumptions about the machine, OS, runtime and environment (these stay)', True),
                         ('proof debts: glibc contracts still to prove (these should reach 0)', False)):
        group = {t: c for t, c in counts.items() if (t in ASSUMPTION_TAGS) == stays}
        print(f'  {title}: {sum(group.values())}')
        for t, c in sorted(group.items(), key=lambda tc: (-tc[1], tc[0])):
            print(f'    {t}: {c}')
    bad = [p for p in ps if not status(p).startswith(SAT)]
    print(f'not known satisfiable: {len(bad)} (the theorem is vacuous while any is unsatisfiable)')
