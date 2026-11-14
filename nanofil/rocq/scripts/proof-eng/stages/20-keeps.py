#!/usr/bin/env python3
"""Share finite environment frames, after flattening, without file snapshots."""
import pathlib
import re
import os
import shutil
import subprocess
import sys
import tempfile

checking = sys.argv[1:2] == ['--check']
root = pathlib.Path(sys.argv[2] if checking else sys.argv[1]).resolve()
ident = r"[A-Za-z_][A-Za-z_0-9']*"
# The complete proposition is matched: neither adjacent pure facts nor the
# order of the source and destination environments may change.
frame = re.compile(
    rf'\(forall (?P<x>{ident}),\s*'
    r'(?P<names>(?:[A-Za-z_][A-Za-z_0-9\x27]* = TAtom "[^"]+"\s*\\/\s*)+'
    r'[A-Za-z_][A-Za-z_0-9\x27]* = TAtom "[^"]+")\s*->\s*'
    rf'lookup (?P=x) (?P<dst>{ident}) = lookup (?P=x) (?P<src>{ident})\)'
)
moved = ('keeps', 'avoids', 'keeps_refl', 'keeps_put', 'keeps_trans',
         'keeps_put_avoid', 'keeps_app', 'keeps_in')
declaration = re.compile(
    r'(?:\(\*\*[^*]*(?:\*(?!\))[^*]*)*\*\)\s*)?'
    r'(?:(?:Definition (?:keeps|avoids)\b)[^.]*\.'
    r'|Lemma keeps_(?:refl|put|trans|put_avoid|app|in)\b.*?Qed\.)\s*',
    re.S,
)
lemma = re.compile(r'\b(?:Lemma|Theorem|Corollary) (' + ident
                   + r')\b(?P<statement>.*?)\bProof\.(?P<body>.*?)\bQed\.', re.S)


def replace_frame(match):
    names = re.findall(rf'({ident}) = TAtom ("[^"]+")', match['names'])
    if any(x != match['x'] for x, _ in names):
        raise ValueError('inconsistent disjunction binder: ' + match[0])
    return ('keeps (atoms [' + '; '.join(s for _, s in names)
            + f"]) {match['src']} {match['dst']}")


def signature(text):
    text = re.sub(r'\(\*.*?\*\)', '', text, flags=re.S)
    return ' '.join(text.split('Proof.')[0].split())


here = pathlib.Path(__file__).resolve().parent.parent
manifest = here / 'check/expected-statement-changes/20-keeps.txt'
expected = {}
for line in manifest.read_text().splitlines():
    if line.startswith('# frame\t'):
        _, file, name, before, after = line.split('\t')
        key = (file, name)
        if key in expected:
            raise ValueError(f'{manifest}: duplicate frame {key}')
        expected[key] = (before, after)
if not expected:
    raise ValueError(f'{manifest}: no expected frames')

# The checked propositions must use the exact old and new name sets from
# the source guards, not a second independently editable collection.
equivalence = manifest.with_suffix('.equivalence.v')
proofs = equivalence.read_text()
proof_statements = {}
for match in lemma.finditer(proofs):
    proof_statements[match[1]] = signature(match['statement']).rstrip('.')
required_proofs = {}
for (file, name), (before, after) in expected.items():
    old = frame.fullmatch(before)
    if old is None or signature(replace_frame(old)) != after:
        raise ValueError(f'{manifest}: invalid frame guard for {file}:{name}')
    names = re.search(r'atoms (\[.*?\])', after)[1]
    proof_name = pathlib.Path(file).stem + '_' + name + '_names'
    required_proofs[proof_name] = signature(
        f'(x : name) : List.In x (atoms {names}) <-> ({old["names"]})')
if proof_statements != required_proofs:
    raise SystemExit('keeps: equivalence statements differ from reviewed source guards')
if checking:
    # Rocq requires a legal basename, so compile a temporary copy rather than
    # leaving build products beside the review packet.
    with tempfile.TemporaryDirectory(prefix='keeps-equivalence-') as directory:
        source = pathlib.Path(directory) / 'KeepsEquivalence.v'
        shutil.copyfile(equivalence, source)
        subprocess.run(['rocq', 'c', '-q', '-R', os.environ['PE_MODEL'], 'Nanofil',
                        '-R', str(root), 'Glibc', str(source)], check=True)
    print(f'keeps: checked {len(required_proofs)} finite-name equivalences')
    raise SystemExit(0)

# Preflight the complete tree before writing any file. New lane statements
# need review even when their syntax already matches the converter.
header = re.compile(r'^[ \t]*(?:(?:Lemma|Theorem|Corollary|Definition)\s+('
                    + ident + r')\b|Context\s+\((' + ident + r')\s*:)', re.M)
actual, already = {}, {}
converted = set()
for path in sorted(root.rglob('*.v')):
    code = re.sub(r'\(\*.*?\*\)', '', path.read_text(), flags=re.S)
    headers = list(header.finditer(code))
    file = str(path.relative_to(root))
    for match in frame.finditer(code):
        owner = next((h for h in reversed(headers) if h.start() < match.start()), None)
        if owner is None or 'Proof.' in code[owner.start():match.start()]:
            raise ValueError(f'{path}: frame outside a recognized statement: {match[0]}')
        name = owner[1] or owner[2]
        if name in {'hello_never_panics', 'hi_atexit_never_panics', 'pieces_never_panics'}:
            raise ValueError(f'{path}: refusing to rewrite an audited theorem')
        key = (file, name)
        if key in actual:
            raise ValueError(f'{path}: multiple frame replacements in {name}')
        actual[key] = (signature(match[0]), signature(replace_frame(match)))
        if owner[1]:
            converted.add(name)
    for i, owner in enumerate(headers):
        key = (file, owner[1] or owner[2])
        end = headers[i + 1].start() if i + 1 < len(headers) else len(code)
        statement = signature(code[owner.start():end])
        if key in expected and key not in actual and expected[key][1] in statement:
            already[key] = expected[key]
observed = actual | already
if observed != expected or (actual and already):
    extra = sorted(observed.keys() - expected.keys())
    missing = sorted(expected.keys() - observed.keys())
    changed = sorted(k for k in expected.keys() & observed.keys() if expected[k] != observed[k])
    raise SystemExit(f'keeps: statement manifest mismatch: extra={extra}, missing={missing}, '
                     f'changed={changed}, partially_converted={bool(actual and already)}; '
                     f'review {manifest}')
print(f'keeps: matched {len(expected)} reviewed statement replacements')

shared = here / 'overlay/GlibcEnv.v'
signatures = {signature(m[0]) for m in declaration.finditer(shared.read_text())}
total = 0
for path in sorted(root.rglob('*.v')):
    if path.name == 'GlibcEnv.v':
        continue
    original = path.read_text()
    for match in declaration.finditer(original):
        if signature(match[0]) not in signatures:
            raise ValueError(f'{path}: moved declaration has changed: {signature(match[0])}')
    text = declaration.sub('', original)
    text = re.sub(r'\b(?:GetoptInitialize|GetoptExchange)\.('
                  + '|'.join(moved) + r')\b', r'GlibcEnv.\1', text)

    text, count = frame.subn(replace_frame, text)
    total += count

    def proof(match):
        body = match[0]
        producer = re.compile(
            rf'intros (?P<x>{ident}) (?P<h>{ident})(?P<middle>.*?)'
            r'destruct (?P=h) as (?P<cases>\[->(?:\s*\|\s*\[->)*\s*\|\s*->\]+)',
            re.S)
        # Restrict adaptation to a converted lemma or a direct caller of one.
        # Similar-looking quantifiers in other developments are not frames.
        if not count and match[1] not in converted and not any(
                re.search(r'\b' + re.escape(name) + r'\b', match['body'])
                for name in converted):
            return body
        # Existing consumers use the preservation hypothesis either as a
        # rewrite rule or as a function at one name. Expose List.In once.
        consumers = set(re.findall(
            rf'\b({ident}) \(TAtom "[^"]+"\) ltac:\(auto\)', body))
        consumers.update(re.findall(rf'rewrite ({ident}); auto', body))
        for introduction in producer.finditer(body):
            consumers.update(re.findall(
                rf'\(({ident}) {introduction["x"]} {introduction["h"]}\)',
                introduction['middle']))
        for hyp in sorted(consumers):
            binder = re.compile(r'(iIntros [^\n]*\b' + re.escape(hyp)
                                + r'\b[^\n]*"[^"\n]*"\.)')
            body = binder.sub(r'\1 rewrite keeps_forall in ' + hyp
                              + '; cbn [atoms List.map List.In] in ' + hyp + '.', body)
        # A finite disjunction proof already does the right case analysis.
        # List.In reverses each equality and adds a final impossible case.
        if match[1] in converted:
            def cases(m):
                n = m['cases'].count('->')
                return ('rewrite keeps_forall; cbn [atoms List.map List.In]; intros '
                        + m['x'] + ' ' + m['h'] + m['middle']
                        + 'destruct ' + m['h'] + ' as '
                        + '[<- | ' * n + '[]' + ']' * n)
            body = producer.sub(cases, body)
        return body

    # Proof bodies, not declarations: top-level theorem statements stay intact.
    text = lemma.sub(proof, text)
    code = re.sub(r'\(\*.*?\*\)', '', text, flags=re.S)
    if text != original or re.search(r'\b(?:' + '|'.join(moved) + r')\b', code):
        if 'From Glibc Require Import GlibcEnv.' not in text:
            pos = re.search(r'^From ', text, re.M)
            if pos is None:
                raise ValueError(f'{path}: no import location')
            text = text[:pos.start()] + 'From Glibc Require Import GlibcEnv.\n' + text[pos.start():]
    if text != original:
        path.write_text(text)
    if count:
        print(f'keeps: {path.relative_to(root)}: {count} finite frames')
    for match in re.finditer(
            rf'lookup \(TAtom ("[^"]+")\) ({ident}) = '
            rf'lookup \(TAtom \1\) ({ident})', code):
        print(f'keeps: left separate lookup fact in {path.relative_to(root)}: {match[0]}')
    for match in re.finditer(
            rf'(?:forall|∀) (?P<x>{ident}),\s*'
            r'(?P<condition>(?:(?!\.\s|⌝).)*?)\s*(?:->|→)\s*'
            rf'lookup (?P=x) {ident} = lookup (?P=x) {ident}', code, re.S):
        kind = ('complement-of-write-set frame' if 'existsb' in match['condition']
                else 'unconverted quantified frame')
        print(f'keeps: left {kind} in {path.relative_to(root)}: {match[0].strip()}')
project = root / '_RocqProject'
if project.exists():
    lines = project.read_text().splitlines()
    if 'GlibcEnv.v' not in lines:
        first = next((i for i, line in enumerate(lines) if line.endswith('.v')), len(lines))
        lines.insert(first, 'GlibcEnv.v')
        project.write_text('\n'.join(lines) + '\n')
print(f'keeps: converted {total} finite frames')
