#!/usr/bin/env python3
"""Remove the functor wrappers from the glibc proof tree TREE, in place.

    python3 -I 10-flatten.py TREE

Every `Module XOn (R : Runtime) (LG0 : LogicSig R). ... End XOn.` wrapper goes, and so
does every alias `Module A := YOn R LG0.` of a glibc functor. Each path through such
aliases (`A.B.C.name`) becomes the file module that defines the name (`FileOfC.name`),
and the file gets the `From Glibc Require` line that the path needs. Fix.v fixes the
one runtime and logic instance."""
import argparse
import json
import re, sys, os, glob
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('tree')
parser.add_argument('--sealed', action='store_true',
                    default=os.environ.get('PE_SEALED') == '1')
parser.add_argument('--runtime', choices=('interp', 'abstract'),
                    default=os.environ.get('PE_RUNTIME', 'interp'))
parser.add_argument('--name-report', help='write the duplicate-name and unqualified-use audit as JSON')
parser.add_argument('--notation-report', help='write imported notation-string collisions as JSON')
parser.add_argument('--comment-report', help='write the removed functor comments as JSON')
parser.add_argument('--comment-table', default=os.path.join(os.path.dirname(__file__), '..', 'flatten-comments.json'),
                    help='exact-match replacements for substantive functor comments')
args = parser.parse_args()
src = dst = args.tree
files = sorted(glob.glob('**/*.v', root_dir=src, recursive=True))
mod = {f: os.path.basename(f)[:-2] for f in files}
if len(set(mod.values())) != len(files):
    raise ValueError('two proof files share a base name')
text = {f: open(os.path.join(src, f)).read() for f in files}
with open(args.comment_table) as table:
    comment_table = {row['file']: row for row in json.load(table)}
for f, row in comment_table.items():
    if text.get(f, '').count(row['original']) != 1:
        raise ValueError(f'{f}: expected exactly one original comment from {args.comment_table}')
HDR = re.compile(r'^[ \t]*Module ([A-Za-z0-9_]+) \(R : Runtime\)(?: \(LG0 : LogicSig R\))?\.[ \t]*\n', re.M)
functor_file = {}
for f in files:
    for m in HDR.finditer(text[f]): functor_file[m.group(1)] = f
ALIAS = re.compile(r'^[ \t]*Module ([A-Za-z0-9_]+) := ([A-Za-z0-9_]+)(?: R LG0| InterpRuntime [A-Za-z0-9_]+| R LG| InterpRuntime)?\.[ \t]*\n', re.M)
PATHALIAS = re.compile(r'^[ \t]*Module ([A-Za-z0-9_]+) := ([A-Za-z0-9_]+(?:\.[A-Za-z0-9_]+)+)\.[ \t]*\n', re.M)
ns = {f: {} for f in files}          # file -> alias name -> target file
for f in files:
    for m in ALIAS.finditer(text[f]):
        if m.group(2) in functor_file: ns[f][m.group(1)] = functor_file[m.group(2)]
glob_alias = {}
TOPALIAS = re.compile(r'^Module ([A-Za-z0-9_]+) := ([A-Za-z0-9_]+) InterpRuntime(?: [A-Za-z0-9_]+)?\.', re.M)
for f in files:
    for m in TOPALIAS.finditer(text[f]):
        if m.group(2) in functor_file: glob_alias.setdefault(m.group(1), set()).add(functor_file[m.group(2)])
local_mods = {f: set(re.findall(r'^[ \t]*Module (?:Type )?([A-Za-z0-9_]+)', text[f], re.M)) for f in files}
file_by_mod = {mod[f]: f for f in files}
imports = {f: [] for f in files}
def lookup(cur, c):
    """Alias c as seen in file cur: its own aliases, then those of files it imports (transitively)."""
    seen, todo = set(), [cur]
    while todo:
        x = todo.pop(0)
        if x in seen: continue
        seen.add(x)
        if c in ns[x]: return ns[x][c]
        todo += imports[x]
    return None
def resolve(f, comps):
    """Resolve a dotted path seen in file f. Returns (new comps, target file or None if untouched)."""
    cur, prefix, i = f, None, 0
    while i < len(comps):
        c = comps[i]
        if lookup(cur, c) is not None and not (prefix is None and c in local_mods[f] and c not in ns[f]): cur = lookup(cur, c); prefix = [mod[cur]]; i += 1
        elif prefix is None and c not in local_mods[f] and c in file_by_mod and i + 1 < len(comps): cur = file_by_mod[c]; prefix = [mod[cur]]; i += 1
        elif prefix is None and c not in local_mods[f] and c in glob_alias and len(glob_alias[c]) == 1:
            cur = next(iter(glob_alias[c])); prefix = [mod[cur]]; i += 1
        else: break
    if prefix is None: return comps, None
    return prefix + comps[i:], cur
# path aliases: `Module A := X.Y.Z.` that resolve to exactly a file become aliases too (fixpoint)
changed = True
while changed:
    changed = False
    for f in files:
        for m in PATHALIAS.finditer(text[f]):
            if m.group(1) in ns[f]: continue
            new, tgt = resolve(f, m.group(2).split('.'))
            if tgt is not None and len(new) == 1: ns[f][m.group(1)] = tgt; changed = True
T_ = r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*"
IMP = re.compile(r'^([ \t]*)(Import|Export)\s+(' + T_ + r'(?:\s+' + T_ + r')*)\.[ \t]*$', re.M)
changed = True
while changed:
    changed = False
    for f in files:
        for m in PATHALIAS.finditer(text[f]):
            if m[1] in ns[f]: continue
            new, tgt = resolve(f, m[2].split('.'))
            if tgt is not None and len(new) == 1:
                ns[f][m[1]] = tgt
                changed = True
        for m in IMP.finditer(text[f]):
            for w in m.group(3).split():
                new, tgt = resolve(f, w.split('.'))
                if tgt is not None and len(new) == 1 and tgt != f and tgt not in imports[f]:
                    imports[f].append(tgt)
                    changed = True
TOK = re.compile(r"(?<![A-Za-z0-9_.'])([A-Z][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_']*)+)")
PARAM = re.compile(r' \(R : Runtime\)(?: \(LG0 : LogicSig R\))?')
specialized = set()
for s in text.values():
    specialized.update(re.findall(r'^Module (?:Type )?(\w+) \(R : Runtime\)', s, re.M))
# Importing a lifted module also opens the file's former outer declarations.
# Order imports to preserve every colliding name, without rewriting binders.
DECL = re.compile(r'^[ \t]*(?:#\[[^\n]*?\]\s*)*(?:(?:Local|Global|Polymorphic|Monomorphic|Program)\s+)*(?:Ltac|Definition|Lemma|Theorem|Corollary|Proposition|Fact|Remark|Fixpoint|CoFixpoint|Inductive|CoInductive|Record|Class|Instance|Example|Notation)\s+([A-Za-z_][A-Za-z0-9_\']*)', re.M)
def code_only(s, comments=None, strings=True):
    """Mask nested comments and strings without moving source positions."""
    out, i, depth = list(s), 0, 0
    while i < len(s):
        if s.startswith('(*', i):
            if depth == 0: comment_start = i
            depth += 1
            out[i:i+2] = '  '
            i += 2
        elif depth and s.startswith('*)', i):
            depth -= 1
            out[i:i+2] = '  '
            i += 2
            if depth == 0 and comments is not None and s.startswith('(**', comment_start):
                comments.append((comment_start, i))
        elif depth:
            if s[i] != '\n': out[i] = ' '
            i += 1
        elif s[i] == '"':
            if strings: out[i] = ' '
            i += 1
            while i < len(s):
                c = s[i]
                if strings: out[i] = '\n' if c == '\n' else ' '
                i += 1
                if c == '"':
                    if i < len(s) and s[i] == '"':
                        if strings: out[i] = ' '
                        i += 1
                    else: break
        else: i += 1
    return ''.join(out)
codes = {f: code_only(s) for f, s in text.items()}
members, outer, owners = {}, {}, {}
notation_owners = {}
for f in files:
    ranges = []
    for h in HDR.finditer(codes[f]):
        end = re.search(r'^End ' + h[1] + r'\.', codes[f][h.end():], re.M)
        if end is None: raise ValueError(f'{f}: unclosed module {h[1]}')
        ranges.append((h.end(), h.end() + end.start()))
    members[f], outer[f] = set(), set()
    for d in DECL.finditer(codes[f]):
        if re.search(r'\bLocal\s', d[0]) or d[1] == '_': continue
        (members[f] if any(a <= d.start() < b for a, b in ranges) else outer[f]).add(d[1])
        owners.setdefault(d[1], set()).add(f)
    for n in re.finditer(r'^[ \t]*(?:#\[[^\n]*?\]\s*)*(?:(?:Local|Global)\s+)?(?:Tactic Notation|Notation)\s+("(?:[^"]|"")*")',
                         code_only(text[f], strings=False), re.M):
        if re.search(r'\bLocal\s', n[0]): continue
        notation_owners.setdefault(n[1], set()).add(f)
duplicates = {n for n, fs in owners.items() if len(fs) > 1}
notation_collisions = []
removed_comments = []
for f in files:
    s = text[f]; used = set()
    visible = {}
    comments = []
    code = code_only(s, comments)
    referenced = {n for n in duplicates if re.search(r"(?<![\w.'])" + n + r"(?![\w'])", code)}
    for req in re.finditer(r'From Glibc Require Import\s+([^.]*)\.', code):
        for w in req[1].split():
            if w in file_by_mod:
                for name in outer[file_by_mod[w]] & referenced:
                    visible[name] = w
    # A real nested namespace or a sealed interface still exports its
    # aliases as fields. Keep those shallow aliases, pointing at flat files.
    retained_aliases = set()
    lifted = {h[1] for h in HDR.finditer(s)}
    for h in re.finditer(r'^Module (?:Type )?(\w+)([^\n]*)', code, re.M):
        if h[1] in lifted or ':=' in h[2]: continue
        end = re.search(r'^End ' + h[1] + r'\.', code[h.end():], re.M)
        if end is None: raise ValueError(f'{f}: unclosed module {h[1]}')
        body = code[h.end():h.end() + end.start()]
        retained_aliases.update(m[1] for m in ALIAS.finditer(body))
        retained_aliases.update(m[1] for m in PATHALIAS.finditer(body))
    def alias_line(m):
        if m.group(1) in ns[f] and m.group(1) not in retained_aliases: return ''
        return m.group(0)
    remove = []
    for h in HDR.finditer(code):
        before = [(a, b) for a, b in comments if b <= h.start()]
        if before:
            a, b = before[-1]
            if not s[b:h.start()].strip():
                row = comment_table.get(f)
                replacement = row['replacement'] if row and s[a:b] == row['original'] else ''
                remove.append((a, b, replacement))
                if not replacement:
                    removed_comments.append({'file': f, 'module': h[1], 'comment': s[a:b]})
    for a, b, replacement in reversed(remove): s = s[:a] + replacement + s[b:]
    hdr_names = [m.group(1) for m in HDR.finditer(s)]
    s = HDR.sub('From Glibc Require Import Fix.\n', s, count=1)
    for h in hdr_names: s = re.sub(r'^[ \t]*End ' + h + r'\.[ \t]*\n', '', s, flags=re.M)
    s = ALIAS.sub(alias_line, s); s = PATHALIAS.sub(alias_line, s)
    def imp(m):
        out = []
        for w in m.group(3).split():
            new, tgt = resolve(f, w.split('.'))
            if tgt is not None and w.split('.')[0] not in file_by_mod: used.add(mod[tgt])
            w2 = '.'.join(new)
            if w2 == mod[f]: continue           # an import of this file itself
            out.append(w2)
            if tgt is not None and len(new) == 1:
                for name in members[tgt] & duplicates:
                    visible[name] = mod[tgt]
            elif w in file_by_mod:
                for name in outer[file_by_mod[w]] & duplicates:
                    visible[name] = w
        out = list(dict.fromkeys(out))
        edges = {w: set() for w in out}
        for name, owner in visible.items():
            if name not in referenced: continue
            if owner not in edges: continue
            for w in out:
                if w in file_by_mod and w != owner:
                    t = file_by_mod[w]
                    if name in members[t] | outer[t]: edges[owner].add(w)
        ordered = []
        while edges:
            ready = next((w for w, deps in edges.items() if not deps), None)
            if ready is None:
                raise ValueError(f'{f}: conflicting import order for {visible}: {edges}')
            ordered.append(ready)
            del edges[ready]
            for deps in edges.values(): deps.discard(ready)
        return f"{m.group(1)}{m.group(2)} {' '.join(ordered)}." if ordered else ''
    s = IMP.sub(imp, s)
    def tok(m):
        comps = m.group(1).split('.')
        new, tgt = resolve(f, comps)
        if tgt is None: return m.group(0)
        if new[0] == mod[f]: new = new[1:]      # a name of this file
        elif comps[0] not in file_by_mod: used.add(new[0])
        return '.'.join(new) if new else m.group(0)
    s = TOK.sub(tok, s)
    def retained_alias(m):
        target = functor_file.get(m[2])
        if target is None: return m[0]
        used.add(mod[target])
        return 'Module ' + m[1] + ' := ' + mod[target] + '.\n'
    s = ALIAS.sub(retained_alias, s)
    def module_args(m):
        def arg(a):
            name = a[0]
            if name not in ns[f] or name in retained_aliases: return name
            target = mod[ns[f][name]]
            used.add(target)
            return target
        return m[1] + re.sub(r"(?<![\w.'])\w+(?![\w.'])", arg, m[2]) + '.'
    s = re.sub(r'^(Module \w+ := )(.+)\.$', module_args, s, flags=re.M)
    def include(m):
        target = functor_file.get(m[1])
        if target is None: return m[0]
        used.add(mod[target])
        return 'Include ' + mod[target] + '.'
    s = re.sub(r'^Include (\w+) R LG0\.', include, s, flags=re.M)
    if PARAM.search(s):
        s = 'From Glibc Require Import Fix.\n' + PARAM.sub('', s)
    for name in sorted(specialized - functor_file.keys(), key=len, reverse=True):
        s = re.sub(r'\b' + name + r' R LG0\b', name, s)
    logic_alias = re.compile(r'^Module (\w+) := Logic (?:R|InterpRuntime)\.', re.M)
    if logic_alias.search(s):
        prefix = '' if 'From Glibc Require Import Fix.' in s else 'From Glibc Require Import Fix.\n'
        s = logic_alias.sub(lambda m: prefix + ('' if m[1] == 'LG0' else 'Module ' + m[1] + ' := LG0.'), s)
    if re.search(r'^Module (?:Type )?\w+\s+\(R\s*:', code_only(s), re.M):
        raise ValueError(f'{f}: runtime parameter was not specialized')
    if 'InterpRuntime' in code_only(s) and 'InterpRuntime' not in code:
        raise ValueError(f'{f}: conversion introduced an interpreter dependency')
    used.discard(mod[f])
    generated = ''
    if used:
        generated = 'From Glibc Require ' + ' '.join(sorted(used)) + '.\n'
    fix_import = re.compile(r'^From Glibc Require Import Fix\.[ \t]*\n', re.M)
    if fix_import.search(s):
        s = fix_import.sub('', s)
        generated += 'From Glibc Require Import Fix.\n'
    if generated:
        requires = list(re.finditer(
            r'^[ \t]*(?:From [\w.]+ Require|Require)(?: Import| Export)?\s+[^.]*\.[ \t]*\n',
            code_only(s), re.M))
        if not requires: raise ValueError(f'{f}: no initial import block')
        end = requires[0].end()
        for req in requires[1:]:
            if code_only(s[end:req.start()]).strip(): break
            end = req.end()
        s = s[:end] + generated + s[end:]
    opened = set()
    for req in re.finditer(r'From Glibc Require Import\s+([^.]*)\.', code_only(s)):
        opened.update(file_by_mod[w] for w in req[1].split() if w in file_by_mod)
    for imp_line in IMP.finditer(code_only(s)):
        opened.update(file_by_mod[w] for w in imp_line[3].split() if w in file_by_mod)
    for notation, defining_files in notation_owners.items():
        collision = sorted(opened & defining_files)
        if len(collision) > 1:
            notation_collisions.append({'file': f, 'notation': notation, 'defined_in': collision})
            print(f'@@proof-eng {f}: imported notation {notation} from {collision}', file=sys.stderr)
    os.makedirs(os.path.dirname(os.path.join(dst, f)), exist_ok=True)
    o = os.path.join(dst, f)
    if not os.path.exists(o) or open(o).read() != s: open(o, 'w').write(s)
open(os.path.join(dst, 'Fix.v'), 'w').write(
    "(** This file names the one runtime and logic instance used by the glibc proofs.\n"
    "    Each proof imports these modules instead of creating its own logic instance.\n\n"
    "    Instance search must know the world interpretation before choosing its safepoint rules.\n"
    "    The [Hint Mode] declaration prevents it from choosing [no_world] for an unknown interpretation. *)\n"
    "From Nanofil Require Import Runtime Logic.\n"
    + ("Declare Module R : Runtime.\n" if args.runtime == 'abstract' else "Module R := InterpRuntime.\n")
    + "Module LG0" + (" : LogicSig R" if args.sealed else "") + " := Logic R.\n"
    + "#[export] Hint Mode LG0.SafepointStable + ! : typeclass_instances.\n")
project = os.path.join(dst, '_RocqProject')
if os.path.exists(project):
    s = open(project).read()
    paths = dict(mod)
    paths['Fix.v'] = 'Fix'
    by_name = {n: p for p, n in paths.items()}
    deps = {}
    for p in paths:
        code = code_only(open(os.path.join(dst, p)).read())
        deps[p] = {by_name[n] for r in re.finditer(
            r'From Glibc Require\s+(?:(?:Import|Export)\s+)?([^.]*)\.', code)
            for n in r[1].split()}
    ordered = []
    while deps:
        ready = sorted(p for p, ds in deps.items() if not ds)
        if not ready: raise ValueError(f'cyclic file imports: {deps}')
        ordered.extend(ready)
        for p in ready: del deps[p]
        for ds in deps.values(): ds.difference_update(ready)
    directives = [line for line in s.splitlines() if not line.endswith('.v')]
    open(project, 'w').write('\n'.join(directives + ordered) + '\n')
build = os.path.join(dst, 'build.sh')
if os.path.exists(build):
    s = open(build).read()
    old = "xargs -0 grep -nwE 'Admitted|Axiom|Axioms|Parameter|Conjecture'"
    new = """xargs -0 awk '
  skip == "" && /^Module Type [A-Za-z0-9_]/ { skip = $3; sub(/[ .(].*/, "", skip); next }
  skip != "" { if ($0 ~ "^End " skip "\\\\.") skip = ""; next }
  { print FILENAME ":" FNR ": " $0 }' |
  grep -wE 'Admitted|Axiom|Axioms|Parameter|Conjecture'"""
    if old not in s: raise ValueError('unrecognized build.sh assumption audit')
    open(build, 'w').write(s.replace(old, new))
if args.name_report:
    report = {}
    uses = {f: DECL.sub('', codes[f]) for f in files}
    for name in sorted(duplicates):
        users = [f for f in files if re.search(
            r"(?<![\w.'])" + name + r"(?![\w'])", uses[f])]
        if users:
            report[name] = {'defined_in': sorted(owners[name]), 'used_unqualified_in': users}
    with open(args.name_report, 'w') as out:
        json.dump(report, out, indent=2)
        out.write('\n')
if args.notation_report:
    with open(args.notation_report, 'w') as out:
        json.dump(notation_collisions, out, indent=2)
        out.write('\n')
print(f'@@proof-eng removed {len(removed_comments)} functor-header comments', file=sys.stderr)
if args.comment_report:
    with open(args.comment_report, 'w') as out:
        json.dump(removed_comments, out, indent=2)
        out.write('\n')
