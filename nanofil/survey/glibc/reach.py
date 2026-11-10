#!/usr/bin/env python3
"""What a set of libc functions reaches in user glibc (docs/zsys.md).

  uv run --with pyelftools python3 nanofil/survey/glibc/reach.py \
      LIBC_A ROOT... [--each] [--why NAME] [--units UNITS_TSV]

LIBC_A is the staging toolchain's static user glibc,
$(nix build --print-out-paths .#filcc-staging.components.filc-glibc)/lib/libc.a.
The graph is function-level: a node is an ELF symbol of one member
(function or data, local or global) and an edge goes from the symbol
whose bytes hold a relocation to the relocation's target; a reference to
a section resolves to the symbol covering that offset, and global names
link members. Fil-C names a function's entry pizlonated_NAME, and a
call goes through a per-member forwarder pizlonatedFI<sig>_NAME, which
is an edge like any other.

Prints the libpizlo names reached, the pizlonated_ names that no member
of libc.a defines (zsys_ calls and the rest of libpizlo's API). It
over-approximates: a function whose address is stored anywhere reached
(libio's vtables) counts as called, and libc.a is the static library, so
libc.so's differences and dlopen'd modules (gconv) are not followed.

--each prints one line per root instead; --why NAME prints one shortest
path to the libpizlo name NAME; --units prints, for each member that
defines a reached function, whether run.py compiled its unit to IR.
"""

import argparse, bisect, collections, os, subprocess, sys, tempfile
from elftools.elf.elffile import ELFFile
from elftools.elf.relocation import RelocationSection
from elftools.elf.sections import SymbolTableSection

PRE = "pizlonated_"


def load(objdir):
    edges = collections.defaultdict(set)
    gdef = collections.defaultdict(set)
    undef = set()
    for fn in sorted(os.listdir(objdir)):
        with open(os.path.join(objdir, fn), "rb") as fh:
            elf = ELFFile(fh)
            st = elf.get_section_by_name(".symtab")
            if not isinstance(st, SymbolTableSection):
                continue
            syms = list(st.iter_symbols())
            bysec = collections.defaultdict(list)
            for s in syms:
                sh = s["st_shndx"]
                if (isinstance(sh, int) and s.name
                        and s["st_info"]["type"] in ("STT_FUNC", "STT_OBJECT", "STT_NOTYPE")):
                    bysec[sh].append((s["st_value"], max(s["st_size"], 1), s.name))
                    if s["st_info"]["bind"] != "STB_LOCAL":
                        gdef[s.name].add((fn, s.name))
                elif sh == "SHN_UNDEF" and s.name:
                    undef.add(s.name)
            for v in bysec.values():
                v.sort()
            starts = {k: [a for (a, _, _) in v] for k, v in bysec.items()}

            def cover(sec, off):
                v = bysec.get(sec)
                if not v:
                    return None
                i = bisect.bisect_right(starts[sec], off) - 1
                while i >= 0:
                    a, sz, nm = v[i]
                    if a <= off < a + sz:
                        return nm
                    if a < off - 65536:
                        break
                    i -= 1
                return None

            for sec in elf.iter_sections():
                if not isinstance(sec, RelocationSection):
                    continue
                tsec = sec["sh_info"]
                for r in sec.iter_relocations():
                    src = cover(tsec, r["r_offset"]) or "<section %d>" % tsec
                    s = syms[r["r_info_sym"]]
                    if s["st_info"]["type"] == "STT_SECTION":
                        add = r["r_addend"] if r.is_RELA() else 0
                        dst = (cover(s["st_shndx"], s["st_value"] + add)
                               or cover(s["st_shndx"], s["st_value"] + add + 4)
                               or "<section %s>" % s["st_shndx"])
                        edges[(fn, src)].add(("L", fn, dst))
                    elif s["st_shndx"] != "SHN_UNDEF" and s["st_info"]["bind"] == "STB_LOCAL":
                        edges[(fn, src)].add(("L", fn, s.name))
                    else:
                        edges[(fn, src)].add(("G", s.name))
    external = {n for n in undef if n.startswith(PRE) and n not in gdef}
    return edges, gdef, external


def reach(graph, roots, why=None):
    edges, gdef, external = graph
    start = [d for r in roots for d in gdef.get(PRE + r, ())]
    parent = {n: None for n in start}
    ext, hit = set(), None
    work = collections.deque(start)
    while work:
        n = work.popleft()
        for e in edges.get(n, ()):
            targets = [(e[1], e[2])] if e[0] == "L" else sorted(gdef.get(e[1], ()))
            if e[0] == "G" and not targets:
                if e[1] in external:
                    ext.add(e[1][len(PRE):])
                    if why and e[1] == PRE + why and hit is None:
                        hit = n
                continue
            for m in targets:
                if m not in parent:
                    parent[m] = n
                    work.append(m)
    path = []
    while hit is not None:
        path.append("%s:%s" % hit)
        hit = parent[hit]
    fns = {n for n in parent if n[1].startswith(PRE)}
    return fns, sorted(ext), path


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("libc_a")
    ap.add_argument("roots", nargs="+")
    ap.add_argument("--each", action="store_true")
    ap.add_argument("--why")
    ap.add_argument("--units")
    a = ap.parse_args()
    with tempfile.TemporaryDirectory() as tmp:
        subprocess.run(["ar", "x", os.path.abspath(a.libc_a)], cwd=tmp, check=True)
        graph = load(tmp)
    if a.each:
        for r in a.roots:
            fns, ext, _ = reach(graph, [r])
            print("%s\t%d\t%s" % (r, len(fns), " ".join(ext)))
        return
    fns, ext, path = reach(graph, a.roots, a.why)
    print("# %d pizlonated_ symbols in %d members; %d of the %d libpizlo names libc.a calls"
          % (len(fns), len({n[0] for n in fns}), len(ext), len(graph[2])))
    for n in ext:
        print(n)
    if a.why:
        print("why %s: %s" % (a.why, " <- ".join(path) or "not reached"))
    if a.units:
        status = {}
        with open(a.units) as fh:
            next(fh)
            for line in fh:
                f = line.split("\t")
                status[os.path.basename(f[0])[:-len(".os")]] = (f[0], f[2], f[5].strip())
        members = sorted({n[0] for n in fns})
        counts = collections.Counter()
        for m in members:
            unit, st, msg = status.get(m[:-len(".o")], ("?", "no unit", ""))
            counts[st] += 1
            print("unit\t%s\t%s\t%s\t%s" % (m, unit, st, msg[:120]))
        print("# members by unit status: %s" % dict(counts))


if __name__ == "__main__":
    main()
