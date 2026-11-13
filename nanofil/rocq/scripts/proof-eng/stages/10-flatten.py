#!/usr/bin/env python3
"""Remove the functor wrappers from the glibc proof tree TREE, in place.

    python3 -I 10-flatten.py TREE

Every `Module XOn (R : Runtime) (LG0 : LogicSig R). ... End XOn.` wrapper goes, and so
does every alias `Module A := YOn R LG0.` of a glibc functor. Each path through such
aliases (`A.B.C.name`) becomes the file module that defines the name (`FileOfC.name`),
and the file gets the `From Glibc Require` line that the path needs. Fix.v fixes the
one runtime and logic instance."""
import re, sys, os, glob
src = dst = sys.argv[1]
files = sorted(glob.glob('**/*.v', root_dir=src, recursive=True))
mod = {f: os.path.basename(f)[:-2] for f in files}
text = {f: open(os.path.join(src, f)).read() for f in files}
HDR = re.compile(r'^[ \t]*Module ([A-Za-z0-9_]+) \(R : Runtime\) \(LG0 : LogicSig R\)\.[ \t]*\n', re.M)
functor_file = {}
for f in files:
    for m in HDR.finditer(text[f]): functor_file[m.group(1)] = f
ALIAS = re.compile(r'^[ \t]*Module ([A-Za-z0-9_]+) := ([A-Za-z0-9_]+)(?: R LG0| InterpRuntime HLG| R LG)?\.[ \t]*\n', re.M)
PATHALIAS = re.compile(r'^[ \t]*Module ([A-Za-z0-9_]+) := ([A-Za-z0-9_]+(?:\.[A-Za-z0-9_]+)+)\.[ \t]*\n', re.M)
ns = {f: {} for f in files}          # file -> alias name -> target file
for f in files:
    for m in ALIAS.finditer(text[f]):
        if m.group(2) in functor_file: ns[f][m.group(1)] = functor_file[m.group(2)]
glob_alias = {}
TOPALIAS = re.compile(r'^Module ([A-Za-z0-9_]+) := ([A-Za-z0-9_]+) InterpRuntime HLG\.', re.M)
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
IMP0 = re.compile(r'^[ \t]*(?:Import|Export)\s+([^.\n]*(?:\.[A-Za-z_][^.\n]*)*)\.[ \t]*$', re.M)
for _ in range(4):
    for f in files:
        for m in IMP0.finditer(text[f]):
            for w in m.group(1).split():
                new, tgt = resolve(f, w.split('.'))
                if tgt is not None and len(new) == 1 and tgt != f and tgt not in imports[f]: imports[f].append(tgt)
TOK = re.compile(r"(?<![A-Za-z0-9_.'])([A-Z][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_']*)+)")
T_ = r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*"
IMP = re.compile(r'^([ \t]*)(Import|Export)\s+(' + T_ + r'(?:\s+' + T_ + r')*)\.[ \t]*$', re.M)
for f in files:
    s = text[f]; used = set()
    def alias_line(m):
        if m.group(1) in ns[f]: return ''
        return m.group(0)
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
            if w2 not in out: out.append(w2)
        return f"{m.group(1)}{m.group(2)} {' '.join(out)}." if out else ''
    s = IMP.sub(imp, s)
    def tok(m):
        comps = m.group(1).split('.')
        new, tgt = resolve(f, comps)
        if tgt is None: return m.group(0)
        if new[0] == mod[f]: new = new[1:]      # a name of this file
        elif comps[0] not in file_by_mod: used.add(new[0])
        return '.'.join(new) if new else m.group(0)
    s = TOK.sub(tok, s)
    s = s.replace('Module HLG := Logic InterpRuntime.', 'From Glibc Require Import Fix.\nModule HLG := LG0.')
    used.discard(mod[f])
    if used:
        req = 'From Glibc Require ' + ' '.join(sorted(used)) + '.\n'
        k = s.find('From Glibc Require Import Fix.\n')
        s = s[:k] + req + s[k:] if k >= 0 else req + s
    os.makedirs(os.path.dirname(os.path.join(dst, f)), exist_ok=True)
    o = os.path.join(dst, f)
    if not os.path.exists(o) or open(o).read() != s: open(o, 'w').write(s)
if not os.path.exists(os.path.join(dst, 'Fix.v')): open(os.path.join(dst, 'Fix.v'), 'w').write(
    "(** Experiment: the one runtime and logic instance every glibc file uses. *)\n"
    "From Nanofil Require Import Runtime Logic.\nModule R := InterpRuntime.\nModule LG0 := Logic InterpRuntime.\n")
