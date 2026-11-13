#!/usr/bin/env python3
"""Generate a scratch class-based theory tree without changing input comments."""
import pathlib
import os
import re
import sys

src, dst = map(pathlib.Path, sys.argv[1:])
dst.mkdir(parents=True, exist_ok=True)

def comment_spans(s):
    depth, start, quoted, i = 0, 0, False, 0
    while i < len(s):
        if not depth and s[i] == '"':
            quoted = not quoted
        if not quoted and s[i:i+2] == '(*':
            if not depth: start = i
            depth += 1; i += 2; continue
        if depth and s[i:i+2] == '*)':
            depth -= 1; i += 2
            if not depth: yield start, i
            continue
        i += 1
    assert depth == 0

def comments(s):
    return [s[a:b] for a, b in comment_spans(s)]

def code_map(s, fn):
    out, start = [], 0
    for a, b in comment_spans(s):
        out += [fn(s[start:a]), s[a:b]]
        start = b
    return ''.join(out) + fn(s[start:])

runtime = (src / 'core/Runtime.v').read_text()
body = runtime.split('Module Type Runtime.')[1].split('End Runtime.')[0]
lemmas = re.findall(r'  Lemma .*?Qed\.', body, re.S)
fields = re.findall(r'\b(?:Parameter|Axiom) (\w+)\s*:', body)
body = re.sub(r'  Lemma .*?Qed\.', '', body, flags=re.S)
body = code_map(body, lambda s: re.sub(r'\b(?:Parameter|Axiom) ', '', s).replace('.\n', ';\n'))
extra = '\nModule R.\nClass RuntimeClass := {\n' + body.rstrip().rstrip(';') + '\n}.\n'
extra += 'Section Laws.\nContext `{rt : RuntimeClass}.\n' + '\n'.join(lemmas) + '\nEnd Laws.\nEnd R.\n'
extra += 'Definition interp_runtime : R.RuntimeClass := {|\n'
extra += ';\n'.join('  R.' + f + ' := InterpRuntime.' + f for f in fields)
extra += '\n|}.\n'
extra += 'Module ClassOf (X : Runtime).\nDefinition instance : R.RuntimeClass := {|\n'
extra += ';\n'.join('  R.' + f + ' := X.' + f for f in fields)
extra += '\n|}.\nEnd ClassOf.\n'
signatures = set()
for path in src.rglob('*.v'):
    signatures.update(re.findall(r'Module Type (\w+) \(R : Runtime\)', path.read_text()))

for path in src.rglob('*.v'):
    s = path.read_text()
    if path.name == 'Runtime.v':
        s += extra
    else:
        # Keep namespaces, replace functor binders by section variables.
        wrappers = re.findall(r'^Module (\w+) \(R : Runtime\)', s, re.M)
        for name in wrappers:
            pattern = r'Module ' + name + r' \(R : Runtime\)(?: \(LG0 : LogicSig R\))?([^\n]*?)\.(.*?)End ' + name + r'\.'
            def wrap(m):
                b = m.group(2)
                runtime_binder = 'runtime_class' if re.search(
                    r'^(?:Lemma|Theorem|Definition)\s+\w+[^:.]*\brt\b', b, re.M) else 'rt'
                aliases = re.findall(r'^(?:Module|Include) .*?\.\s*$', b, re.M)
                b = re.sub(r'^(?:Module|Include) .*?\.\s*$', '', b, flags=re.M)
                arguments = re.findall(r'^Arguments .*?\.$', b, re.M)
                if name == 'ExternalMachine':
                    arguments = [a.replace(' {world}', ' {rt world}')
                                 if not a.startswith('Arguments admissible ') else a
                                 for a in arguments]
                elif name == 'Language':
                    arguments = [a.replace(' {world}', ' {rt world}') for a in arguments]
                else:
                    arguments = []
                if name == 'Logic':
                    arguments += ['#[export] Existing Instance no_world_stable.',
                                  '#[export] Existing Instance closed_irisGS.']
                    if os.environ.get('PE_CLASS_MODE', '1') == '1':
                        arguments += ['#[export] Hint Mode SafepointStable + + ! : typeclass_instances.']
                return ('Module ' + name + m.group(1) + '.\n' + '\n'.join(aliases) +
                        '\nSection RuntimeSection.\nContext `{' + runtime_binder + ' : R.RuntimeClass}.\n' + b +
                        'End RuntimeSection.\n' + '\n'.join(arguments) + '\nEnd ' + name + '.')
            s = re.sub(pattern, wrap, s, flags=re.S)
        s = code_map(s, lambda t: re.sub(r'(Module (?:Export )?\w+ := [\w.]+|Include [\w.]+) R(?: LG0)?\.(?!\w)', r'\1.', t))
        s = code_map(s, lambda t: t.replace('Module LG := LG0.', 'Module LG := Logic.'))
        s = code_map(s, lambda t: re.sub(r'(' + '|'.join(sorted(signatures)) + r') R\b', r'\1', t))
        s = code_map(s, lambda t: re.sub(r'(Module Type \w+) \(R : Runtime\)', r'\1', t))
        s = code_map(s, lambda t: re.sub(r'(Module \w+ := [\w.]+|Include [\w.]+) R ', r'\1 ', t))
        s = code_map(s, lambda t: re.sub(r'(?<![\w.])LG0\.', 'Logic.', t))
        s = code_map(s, lambda t: re.sub(r'Module (\w+) := (\w+) InterpRuntime\.',
            r'Local Instance concrete_runtime_\1 : R.RuntimeClass := interp_runtime.\nModule \1 := \2.', t))
        if path.name == 'LibcCallFixtures.v':
            s = code_map(s, lambda t: t.replace('InterpStrings.c_string_length ',
                'InterpStrings.c_string_length (rt := interp_runtime) '))
            before = ('split; apply InterpExternal.malloc_refused.\n'
                      '  all: try solve [split; [left; reflexivity|eexists; reflexivity]].\n'
                      '  all: try solve [vm_compute; intuition congruence].')
            assert s.count(before) == 1
            s = s.replace(before, before.replace('vm_compute; intuition congruence',
                'cbn; intuition congruence | lia'))
    out = dst / path.relative_to(src)
    out.parent.mkdir(parents=True, exist_ok=True)
    original_comments = comments(path.read_text())
    assert comments(s)[:len(original_comments)] == original_comments, path
    if not out.exists() or out.read_text() != s:
        out.write_text(s)
print(f'{len(fields)} runtime fields; {len(lemmas)} derived laws; {len(list(src.rglob("*.v")))} files copied')
