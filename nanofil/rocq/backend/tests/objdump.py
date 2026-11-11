#!/usr/bin/env python3
"""objdump.py FILE.o: an ELF relocatable object as the text that
`nanofil-backend object-allocated` prints for the object it encodes
(Encode.v's [dump_parts]), so the gate (encode.sh) compares the two
with cmp.

The text has what an object means to a linker and leaves out how GNU
as lays out the file:

  section NAME TYPE FLAGS ALIGN SIZE      one per section with bytes
  bytes HEX                                32 bytes a line
  reloc SECTION OFFSET TYPE SYMBOL ADDEND  by section, then offset
  symbol NAME BIND TYPE VIS SECTION VALUE SIZE

Sections come in order of name. The symbol table, string tables and
relocation sections are not printed as sections, and neither is an
empty section other than .note.GNU-stack. A relocation against a
section's symbol names the section. Named symbols come in order of
name; section and file symbols are left out. Numbers are decimal,
FLAGS is readelf's letters (or -)."""
import struct
import sys

SHT = {1: "PROGBITS", 8: "NOBITS", 14: "INIT_ARRAY", 15: "FINI_ARRAY"}
STB = {0: "LOCAL", 1: "GLOBAL", 2: "WEAK"}
STT = {0: "NOTYPE", 1: "OBJECT", 2: "FUNC", 3: "SECTION", 4: "FILE", 6: "TLS"}
STV = {0: "DEFAULT", 1: "INTERNAL", 2: "HIDDEN", 3: "PROTECTED"}


def flags(f):
    s = "".join(c for bit, c in ((1, "W"), (2, "A"), (4, "X"), (0x400, "T")) if f & bit)
    return s or "-"


def main(path):
    data = open(path, "rb").read()
    shoff, = struct.unpack_from("<Q", data, 0x28)
    shentsize, shnum, shstrndx = struct.unpack_from("<HHH", data, 0x3A)
    shdrs = [struct.unpack_from("<IIQQQQIIQQ", data, shoff + i * shentsize) for i in range(shnum)]

    def cstr(off):
        return data[off:data.index(b"\0", off)].decode("latin-1")

    names = [cstr(shdrs[shstrndx][4] + h[0]) for h in shdrs]
    symtab = next(i for i, h in enumerate(shdrs) if h[1] == 2)
    st = shdrs[symtab]
    strtab = shdrs[st[6]][4]
    syms = []
    for i in range(st[5] // 24):
        name, info, other, shndx, value, size = struct.unpack_from("<IBBHQQ", data, st[4] + i * 24)
        syms.append((cstr(strtab + name), info >> 4, info & 15, other & 3, shndx, value, size))

    def secname(shndx):
        return {0: "UND", 0xFFF1: "ABS", 0xFFF2: "COM"}.get(shndx) or names[shndx]

    out = []
    for i in sorted(range(1, shnum), key=lambda i: names[i]):
        name, typ, fl, _, off, size, _, _, align, _ = shdrs[i]
        if typ not in SHT or (size == 0 and names[i] != ".note.GNU-stack"):
            continue
        out.append(f"section {names[i]} {SHT[typ]} {flags(fl)} {align} {size}")
        if typ != 8:
            body = data[off:off + size]
            for at in range(0, size, 32):
                out.append("bytes " + body[at:at + 32].hex())
    relocs = []
    for i, h in enumerate(shdrs):
        if h[1] != 4:
            continue
        target = names[h[7]]
        for k in range(h[5] // 24):
            off, info, addend = struct.unpack_from("<QQq", data, h[4] + k * 24)
            s = syms[info >> 32]
            sym = secname(s[4]) if s[2] == 3 else s[0]
            relocs.append((target, off, info & 0xFFFFFFFF, sym, addend))
    for target, off, typ, sym, addend in sorted(relocs):
        out.append(f"reloc {target} {off} {typ} {sym} {addend}")
    for name, bind, typ, vis, shndx, value, size in sorted(s for s in syms if s[0] and s[2] not in (3, 4)):
        out.append(f"symbol {name} {STB[bind]} {STT[typ]} {STV[vis]} {secname(shndx)} {value} {size}")
    sys.stdout.write("\n".join(out) + "\n")


if __name__ == "__main__":
    main(sys.argv[1])
