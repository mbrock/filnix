#!/usr/bin/env python3
"""Compare elaborated statements of two compiled trees.

Missing objects, unsupported module applications and compiler errors fail closed.
Reports retain raw qualified statements as well as path-normalized statements.
"""
import argparse
import concurrent.futures
from functools import lru_cache
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
import textwrap

from expectations import Expectations

HERE = Path(__file__).resolve().parent
IDENT = r"[\w']+"
PATH = rf"{IDENT}(?:\.{IDENT})*"


def uncomment(s):
    # Preserve offsets, including UTF-8 byte offsets used in .glob.
    result, depth, i, quoted = [], 0, 0, False
    while i < len(s):
        pair = s[i:i + 2]
        if not quoted and pair == '(*':
            depth += 1
            result.extend('  ')
            i += 2
        elif depth and pair == '*)':
            depth -= 1
            result.extend('  ')
            i += 2
        else:
            ch = s[i]
            if not depth and ch == '"':
                quoted = not quoted
            result.append(ch if not depth or ch == '\n' else ' ')
            i += 1
    if depth:
        raise ValueError('unterminated comment')
    return ''.join(result)


def sentences(s):
    # A sentence terminator is not a qualified-name dot or a dot in a string.
    start, quoted = 0, False
    for i, ch in enumerate(s):
        if ch == '"':
            quoted = not quoted
        if ch == '.' and not quoted and (i + 1 == len(s) or s[i + 1].isspace()):
            yield s[start:i].strip()
            start = i + 1


class Tree:
    def __init__(self, root):
        self.root = Path(root).resolve()
        self.files = {str(p.relative_to(self.root)): p for p in self.root.rglob('*.v')}
        self.modules = {}
        self.aliases = {}
        self.functors = {}
        self.flattened = set()
        self.module_types = {}
        self.signatures = {}
        self.abstract_runtimes = set()
        self.scopes = {}
        for rel, path in self.files.items():
            base = 'Glibc.' + rel[:-2].replace('/', '.')
            self.modules[path.stem] = base
            self.scopes[rel] = base
            stack = []
            for sentence in sentences(uncomment(path.read_text())):
                declared = re.fullmatch(rf'Declare Module\s+({IDENT})\s*:\s*Runtime', sentence)
                if declared:
                    self.abstract_runtimes.add('.'.join([base] + stack + [declared[1]]))
                m = re.match(rf'Module\s+(?:(Type|Export|Import)\s+)?({IDENT})(.*)', sentence, re.S)
                if m:
                    kind, name, tail = m.groups()
                    full = '.'.join([base] + stack + [name])
                    if ':=' in tail:
                        self.aliases[full] = ('.'.join([base] + stack), tail.split(':=', 1)[1].strip())
                    else:
                        params = re.findall(rf'\(\s*({IDENT})\s*:\s*([^()]*)\)', tail)
                        if kind == 'Type':
                            self.module_types[name] = full
                            self.signatures[full] = params
                        if params and kind != 'Type':
                            self.functors[full] = params
                            if re.fullmatch(r'\s*\(R : Runtime\)(?: \(LG0 : LogicSig R\))?', tail):
                                self.flattened.add(full)
                        stack.append(name)
                elif re.match(rf'End\s+{IDENT}$', sentence):
                    name = sentence.split()[1]
                    if stack and stack[-1] == name:
                        stack.pop()

    def declarations(self, rel, extra=()):
        path = self.files[rel]
        source = uncomment(path.read_text())
        expected = re.findall(rf'\b(?:Lemma|Theorem|Corollary)\s+({IDENT})', source)
        specs = {m[1] for sentence in sentences(source)
                 if (m := re.search(rf'\bDefinition\s+({IDENT})\b.*?:\s*Prop\s*:=', sentence, re.S))}
        glob = path.with_suffix('.glob')
        if not path.with_suffix('.vo').exists() or not glob.exists():
            raise ValueError('missing .vo/.glob (file did not compile)')
        digest = re.search(r'^DIGEST (\w+)', glob.read_text())
        if not digest or digest[1] != hashlib.md5(path.read_bytes()).hexdigest():
            raise ValueError('stale .glob: source digest differs')
        found = []
        for m in re.finditer(r'^(prf|def|var|ax) \d+:\d+ (\S+) (\S+)$', glob.read_text(), re.M):
            kind, scope, name = m.groups()
            if kind in ('var', 'ax'):
                # .glob includes the enclosing Section in a signature's
                # Parameter scope; the exported module field does not.
                full = self.scopes[rel] + '.' + scope
                owners = [s for s in self.signatures if full == s or full.startswith(s + '.')]
                if owners:
                    scope = max(owners, key=len)[len(self.scopes[rel]) + 1:]
            explicit = name in extra or (scope + '.' + name) in extra
            if (kind in ('prf', 'def') and (name in expected or name in specs)) or explicit:
                spec = True if name in specs else 'auto' if kind == 'def' and explicit else False
                found.append((name, '' if scope == '<>' else scope, spec))
        missing = set(expected) - {n for n, _, _ in found}
        if missing:
            raise ValueError('declarations absent from .glob: ' + ', '.join(sorted(missing)))
        return found

    def probe(self, rel, decls, concrete=False):
        base = self.scopes[rel]
        setup = ['From Nanofil Require Import Runtime Logic.',
                 f'Require {base}.',
                 'Module PER := InterpRuntime.' if concrete else 'Declare Module PER : Runtime.',
                 'Module PELG := Logic PER.']
        roots = {}
        names = {}
        for name, scope, spec in decls:
            full = base + ('.' + scope if scope else '')
            if full in self.functors or full in self.signatures:
                if full not in roots:
                    params = self.functors.get(full, self.signatures.get(full))
                    if sum(typ.strip() == 'Runtime' for _, typ in params) > 1:
                        raise ValueError(f'multiple runtime parameters require a probe recipe: {full}')
                    args = []
                    bindings = {}
                    for param, typ in params:
                        if typ.strip() == 'Runtime':
                            arg = 'PER'
                        elif typ.strip() in ('LogicSig R', 'LogicSig InterpRuntime'):
                            arg = 'PELG'
                        else:
                            typ = re.sub(PATH, lambda m: bindings.get(m[0], self.module_types.get(m[0], m[0])), typ)
                            arg = f'PEArg{len(roots)}_{len(args)}'
                            setup.append(f'Declare Module {arg} : {typ}.')
                        args.append(arg)
                        bindings[param] = arg
                    instance = 'PE' + str(len(roots))
                    roots[full] = instance
                    if full in self.signatures:
                        setup.append(f'Declare Module {instance} : {full} {" ".join(args)}.')
                    else:
                        setup.append(f'Module {instance} := {full} {" ".join(args)}.')
                q = roots[full] + '.' + name
            else:
                q = full + '.' + name
            key = name if full in self.functors or not scope else scope + '.' + name
            if key in names:
                raise ValueError('duplicate declaration identity: ' + key)
            names[key] = (q, spec)
        return setup, names, {v: k for k, v in roots.items()}

    def normalize(self, text, instances, concrete=False):
        # Resolve only known module aliases. Never remove arbitrary qualifiers.
        aliases = dict(self.aliases)
        for instance, full in instances.items():
            aliases['PECheck.' + instance] = ('', full)
        aliases['PECheck.PELG'] = ('', '@LogicConcrete' if concrete else '@LogicAbstract')
        aliases['PECheck.PER'] = ('', 'Nanofil.core.Runtime.InterpRuntime' if concrete else '@RuntimeAbstract')
        alias_order = sorted(aliases, key=len, reverse=True)
        functor_order = sorted(self.functors, key=len, reverse=True)
        def runtime(context, name, seen=()):
            if name in ('InterpRuntime', 'Nanofil.core.Runtime.InterpRuntime'):
                return 'Nanofil.core.Runtime.InterpRuntime'
            if name in dict(self.functors.get(context, [])) and dict(self.functors[context])[name] == 'Runtime':
                return '@RuntimeAbstract'
            full = context + '.' + name
            if name.startswith('Glibc.'):
                full = name
            elif full not in aliases and full not in self.abstract_runtimes and name == 'R' and 'Fix' in self.modules:
                full = self.modules['Fix'] + '.R'
            if full in self.abstract_runtimes:
                return '@RuntimeAbstract' if full == self.modules.get('Fix', '') + '.R' else full
            if full in aliases and full not in seen:
                scope, rhs = aliases[full]
                return runtime(scope, rhs, seen + (full,))
            return full
        @lru_cache(maxsize=None)
        def expand(token, seen=()):
            if not token.startswith(('Glibc.', 'PECheck.')):
                return token
            if token in seen:
                raise ValueError('cyclic alias: ' + token)
            for prefix in alias_order:
                if token == prefix or token.startswith(prefix + '.'):
                    context, rhs = aliases[prefix]
                    words = rhs.split()
                    head = words[0]
                    if head in ('LG0', 'LG') and len(words) == 1:
                        # Resolve a local alias first; only module parameters
                        # are identified with the chosen concrete instance.
                        target = context + '.' + head
                        if target not in aliases:
                            if head in dict(self.functors.get(context, [])):
                                head = '@LogicConcrete' if concrete else '@LogicAbstract'
                            elif 'Fix' in self.modules:
                                head = self.modules['Fix'] + '.LG0'
                            else:
                                return token
                    if head == 'R':
                        head = runtime(context, head)
                    if head == 'InterpRuntime':
                        head = 'Nanofil.core.Runtime.InterpRuntime'
                    if words[0] == 'Logic' and len(words) == 2:
                        rt = runtime(context, words[1])
                        head = '@LogicConcrete' if rt == 'Nanofil.core.Runtime.InterpRuntime' else (
                            '@LogicAbstract' if rt == '@RuntimeAbstract' else '@Logic[' + rt + ']')
                    if not head.startswith('@') and head != 'Nanofil.core.Runtime.InterpRuntime':
                        candidate = context + '.' + head if context else head
                        matches = [f for f in self.functors if f.endswith('.' + head)]
                        if any(candidate == a or candidate.startswith(a + '.') for a in aliases) or candidate in self.functors:
                            head = candidate
                        elif len(words) > 1 and len(matches) == 1:
                            head = matches[0]
                        elif head.split('.')[0] in self.modules:
                            first, *rest = head.split('.')
                            head = '.'.join([self.modules[first]] + rest)
                        else:
                            if len(matches) == 1:
                                head = matches[0]
                            elif not head.startswith(('Glibc.', 'Nanofil.')):
                                # An unresolved imported alias is not evidence
                                # that two different file-local names coincide.
                                return token
                    suffix = token[len(prefix):]
                    if len(words) > 1 and words[0] != 'Logic' and head not in self.functors:
                        # External functors remain distinguished by their
                        # constructor and supplied concrete module arguments.
                        head = '@Apply[' + ','.join(words) + ']'
                    return expand(head + suffix, seen + (token,))
            for full in functor_order:
                if token.startswith(full + '.'):
                    rest = token[len(full) + 1:]
                    if rest.startswith('LG0.'):
                        return ('@LogicConcrete.' if concrete else '@LogicAbstract.') + rest[4:]
                    if rest.startswith('R.'):
                        return ('Nanofil.core.Runtime.InterpRuntime.' if concrete else '@RuntimeAbstract.') + rest[2:]
                    # Sealed and extra-parameter modules remain modules in the
                    # flat layout. Erase only the wrappers stage 10 removes.
                    if full in self.flattened:
                        return full.rsplit('.', 1)[0] + '.' + rest
                    return token
            for full in self.abstract_runtimes:
                if full == self.modules.get('Fix', '') + '.R' and token.startswith(full + '.'):
                    return '@RuntimeAbstract.' + token[len(full) + 1:]
            return token
        # Strings are Gallina literals, not paths (even when they contain dots).
        chunks = re.split(r'("(?:[^"]|"")*")', text)
        for i in range(0, len(chunks), 2):
            chunks[i] = re.sub(PATH, lambda m: expand(m[0]), chunks[i])
            chunks[i] = re.sub(r'\s+', ' ', chunks[i])
        return ''.join(chunks).strip()


def run_probe(tree, rel, decls, out, plugin, inside=False):
    setup, names, instances = tree.probe(rel, decls)
    commands = setup + [f'Declare ML Module "{plugin.name}".',
                        'Set Printing All.', 'Set Printing Universes.', 'Set Printing Width 1000000.',
                        'Set Printing Depth 1000000.']
    def query(index, q, spec):
        lines = [f'Goal True. idtac "PE_BEGIN_{index}". Abort.', f'Check @{q}.']
        if spec == 'auto':
            # A Definition can be a proof alias rather than a predicate.
            # Ask Rocq for its type's sort before trying to unfold its body.
            lines.append(f'Goal True. let T := type of (@{q}) in let S := type of T in '
                         f'lazymatch S with Prop => idtac "PE_PROOF_{index}" '
                         f'| _ => idtac "PE_DATA_{index}" end. Abort.')
        elif spec:
            lines.append(f'Eval unfold {q} in @{q}.')
        lines.append(f'Goal True. idtac "PE_END_{index}". Abort.')
        return lines
    for index, (name, (q, spec)) in enumerate(names.items()):
        commands.extend(query(index, q, spec))
    out.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='probe-', dir=out) as tmp:
        script = Path(tmp) / 'PECheck.v'
        script.write_text('\n'.join(commands) + '\n')
        extra = []
        if inside:
            # Sealed functors hide implementation lemmas. Ask the kernel before
            # sealing, after their sections have generalized all hypotheses.
            source = tree.files[rel].read_text()
            inserts = {}
            for index, (name, scope, spec) in enumerate(decls):
                inserts.setdefault(scope, []).extend(query(index, name, spec))
            for scope, queries in inserts.items():
                block = '\n'.join(queries) + '\n'
                if scope:
                    ending = re.compile(r'^End\s+' + re.escape(scope.split('.')[-1]) + r'\.', re.M)
                    if len(ending.findall(source)) != 1:
                        raise ValueError('ambiguous sealed module end: ' + scope)
                    source = ending.sub(lambda m: block + m[0], source)
                else:
                    source += '\n' + block
            settings = commands[len(setup):len(setup) + 5]
            script = Path(tmp) / rel
            script.parent.mkdir(parents=True, exist_ok=True)
            script.write_text('\n'.join(settings) + '\n' + source)
            extra = ['-R', tmp, 'Glibc']
            instances = {}
        env = dict(os.environ)
        env['OCAMLPATH'] = str(plugin.parent) + ':' + env.get('OCAMLPATH', '')
        cmd = ['rocq', 'c', '-q', '-R', os.environ['PE_MODEL'], 'Nanofil',
               '-R', str(tree.root), 'Glibc'] + extra + [str(script)]
        p = subprocess.run(cmd, text=True, stdout=subprocess.PIPE,
                           stderr=subprocess.STDOUT, env=env, timeout=180)
        (out / (rel.replace('/', '__') + '.log')).write_text(p.stdout)
        if p.returncode:
            if not inside and 'was not found in the current environment' in p.stdout:
                return run_probe(tree, rel, decls, out, plugin, inside=True)
            raise ValueError(f'probe compiler exited {p.returncode}: {p.stdout[-1200:]}')
    if any(spec == 'auto' for _, _, spec in decls):
        classified = []
        for index, (name, scope, spec) in enumerate(decls):
            if spec == 'auto':
                proof = f'PE_PROOF_{index}' in p.stdout.splitlines()
                data = f'PE_DATA_{index}' in p.stdout.splitlines()
                if proof == data:
                    raise ValueError('missing or ambiguous sort classification: ' + name)
                spec = data
            classified.append((name, scope, spec))
        return run_probe(tree, rel, classified, out, plugin, inside=inside)
    result = {}
    for index, name in enumerate(names):
        match = re.search(rf'PE_BEGIN_{index}\n(.*?)PE_END_{index}', p.stdout, re.S)
        if not match:
            raise ValueError('missing output marker for ' + name)
        raw = match[1].strip()
        if re.search(r'\.\.\.|…', raw):
            raise ValueError('truncated printed statement: ' + name)
        raw = raw.split('\n     :', 1)[1].strip() if '\n     :' in raw else raw.split(' : ', 1)[1].strip()
        result[name] = {'raw': raw, 'normalized': tree.normalize(raw, instances)}
        q = names[name][0]
        instance = q.split('.')[0]
        params = tree.functors.get(instances.get(instance), [])
        result[name]['module_parameters'] = params
    return result


def compare(args):
    before, after = Tree(args.before), Tree(args.after)
    rules = Expectations(args.expectations)
    out = Path(args.output).resolve()
    plugin = Path(args.plugin).resolve()
    out.mkdir(parents=True, exist_ok=True)
    files = sorted(set(before.files) | set(after.files))
    if args.files:
        unknown = set(args.files) - set(files)
        if unknown:
            raise ValueError('requested files not found: ' + ', '.join(sorted(unknown)))
        files = [f for f in files if f in args.files]
    if not files:
        raise ValueError('no files selected')
    results = {'mode': args.mode, 'files': {}, 'errors': [], 'differences': []}
    def check_file(rel):
        sides = []
        errors = []
        for label, tree in [('before', before), ('after', after)]:
            if rel not in tree.files:
                sides.append({})
                continue
            try:
                decls = tree.declarations(rel, rules.names(rel))
                sides.append(run_probe(tree, rel, decls, out / label, plugin) if decls else {})
            except (ValueError, subprocess.TimeoutExpired, OSError) as e:
                errors.append(f'{label}/{rel}: {e}')
                sides.append(None)
        return rel, sides, errors
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        for rel, sides, errors in pool.map(check_file, files):
            results['files'][rel] = sides
            results['errors'].extend(errors)
    inventories = [{}, {}]
    blocked = [set(), set()]
    origins = {}
    for rel, sides in results['files'].items():
        for i, side in enumerate(sides):
            if side is None:
                blocked[i].add(rel)
                continue
            for name, entry in side.items():
                entry['normalized'] = rules.canonical(entry['normalized'])
                key = rules.identity((rel, name))
                if key in inventories[i]:
                    results['errors'].append(f'duplicate canonical declaration: {key}')
                inventories[i][key] = entry
                if i == 0:
                    origins[key] = (rel, name)
    left, right = inventories
    protected = {name for group in json.loads((HERE / 'audit-contracts.json').read_text()).values() for name in group}
    observed = set()
    for key in sorted(set(left) | set(right)):
        rel, name = key
        origin = origins.get(key, key)
        if origin[0] in blocked[0] or rel in blocked[1]:
            continue
        a, b = left.get(key), right.get(key)
        moved = origin != key and a is not None and b is not None
        if a is None or b is None or a['normalized'] != b['normalized'] or moved:
            d = {'file': rel, 'name': name,
                 'kind': 'added' if a is None else 'removed' if b is None else 'moved' if moved else 'changed',
                 'before': a, 'after': b, 'origin': list(origin)}
            d['accepted'] = rules.accepts(d) and name not in protected
            results['differences'].append(d)
            observed.add(key)
    for key in set(rules.rows) - observed:
        if key[0] in files:
            results['errors'].append(f'expected change was not observed: {key[0]}:{key[1]}')
    (out / 'report.json').write_text(json.dumps(results, indent=2) + '\n')
    lines = []
    for d in results['differences']:
        lines += [f"{'ACCEPTED' if d['accepted'] else 'UNEXPECTED'} {d['kind'].upper()} {d['file']}:{d['name']}"]
        for side in ['before', 'after']:
            value = d[side]
            lines += [f"  {side}:", textwrap.fill(value['normalized'] if value else '<absent>',
                                                 width=110, initial_indent='    ', subsequent_indent='    ')]
    lines += ['ERROR ' + e for e in results['errors']]
    accepted = sum(d['accepted'] for d in results['differences'])
    unexpected = len(results['differences']) - accepted
    summary = f"{args.mode}: {len(files)} files; {accepted} accepted; {unexpected} unexpected differences; {len(results['errors'])} errors"
    lines.append(summary)
    (out / 'report.txt').write_text('\n'.join(lines) + '\n')
    print(summary)
    for d in results['differences']:
        if d['accepted']:
            print(f"ACCEPTED {d['kind']} {d['file']}:{d['name']}")
    print('FAIL' if unexpected or results['errors'] else 'PASS')
    return bool(unexpected or results['errors'])


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('mode', choices=['statements'])
    p.add_argument('before')
    p.add_argument('after')
    p.add_argument('--plugin', required=True)
    p.add_argument('--output', required=True)
    p.add_argument('--expectations', default=str(HERE / 'expected-statement-changes'))
    p.add_argument('--jobs', type=int, default=4)
    p.add_argument('--files', nargs='+')
    raise SystemExit(compare(p.parse_args()))
