#!/usr/bin/env python3
"""Generate the typed-syscall tables for a pizlonated SerenityOS userland.

The script reads two files from a SerenityOS checkout:

  Kernel/API/Syscall.h   the syscall list and the SC_*_params structs
  Kernel/Tasks/Process.h the kernel's typed sys$foo(...) declarations

and writes into generated/:

  SyscallParams.h      one F(kind, type, name, extent, init...) X-macro per
                       params struct, plus ENUMERATE_PARAMS_STRUCTS
  SyscallSignatures.h  one row per syscall with its argument types and the
                       marshalling kind of each argument, plus its class
  Syscall.h            Kernel/API/Syscall.h with the hand-written params
                       structs replaced by expansions of SyscallParams.h
                       (not committed; Syscall.h.diff is the same change)
  layout_check.cpp     static_asserts that the expanded structs match the
                       originals
  report.md            coverage numbers and the syscalls that need hand work

Usage: gen.py SERENITY_CHECKOUT OUTDIR
"""

import re
import sys
from pathlib import Path

serenity = Path(sys.argv[1])
outdir = Path(sys.argv[2])
outdir.mkdir(parents=True, exist_ok=True)

syscall_h = (serenity / "Kernel/API/Syscall.h").read_text()
process_h = (serenity / "Kernel/Tasks/Process.h").read_text()

# ---------------------------------------------------------------------------
# The syscall list.

enum_block = re.search(r"#define ENUMERATE_SYSCALLS\(S\)(.*?)\n\n", syscall_h, re.S).group(1)
syscalls = re.findall(r"S\((\w+),", enum_block)

# ---------------------------------------------------------------------------
# Params structs: parse fields, infer a marshalling kind for each.

# Field relationships that the struct text does not state. Each entry gives
# (kind, extent): the extent is a C expression over p, the runtime's copy of
# the struct, that bounds a pointer field (p->nfds, 0x80), or _ for none.
# These are the "buffer/length annotations" of the design.
FIELD_OVERRIDES = {
    ("SC_mmap_params", "addr"): ("ADDRESS", "p->size"),
    ("SC_mremap_params", "old_address"): ("ADDRESS", "p->old_size"),
    ("SC_set_mmap_name_params", "addr"): ("ADDRESS", "p->size"),
    ("SC_poll_params", "fds"): ("INOUT_ARRAY", "p->nfds"),
    ("SC_poll_params", "sigmask"): ("IN_PTR", "_"),
    ("SC_accept4_params", "addr"): ("OUT_BYTES_INDIRECT", "p->addrlen"),
    ("SC_accept4_params", "addrlen"): ("INOUT_PTR", "_"),
    ("SC_getsockname_params", "addr"): ("OUT_BYTES_INDIRECT", "p->addrlen"),
    ("SC_getsockname_params", "addrlen"): ("INOUT_PTR", "_"),
    ("SC_getpeername_params", "addr"): ("OUT_BYTES_INDIRECT", "p->addrlen"),
    ("SC_getpeername_params", "addrlen"): ("INOUT_PTR", "_"),
    ("SC_getsockopt_params", "value"): ("OUT_BYTES_INDIRECT", "p->value_size"),
    ("SC_getsockopt_params", "value_size"): ("INOUT_PTR", "_"),
    ("SC_setsockopt_params", "value"): ("IN_BYTES", "p->value_size"),
    ("SC_socketpair_params", "sv"): ("OUT_ARRAY", "2"),
    ("SC_futex_params", "userspace_address"): ("ATOMIC_U32", "_"),
    ("SC_futex_params", "userspace_address2"): ("ATOMIC_U32", "_"),
    ("SC_create_thread_params", "stack_location"): ("ADDRESS", "p->stack_size"),
    ("SC_create_thread_params", "entry"): ("CODE", "_"),
    ("SC_create_thread_params", "entry_argument"): ("OPAQUE_PTR", "_"),
    ("SC_create_thread_params", "tls_pointer"): ("ADDRESS", "_"),
    ("SC_posix_spawn_params", "attr_data"): ("IN_BYTES", "p->attr_data_size"),
    ("SC_posix_spawn_params", "serialized_file_actions_data"): ("IN_BYTES", "p->serialized_file_actions_data_size"),
    ("SC_ptrace_params", "addr"): ("ADDRESS", "_"),  # an address in the tracee
    ("SC_ptrace_params", "data"): ("SCALAR_OR_PTR", "_"),
}
for keymap in ("map", "shift_map", "alt_map", "altgr_map", "shift_altgr_map"):
    FIELD_OVERRIDES[("SC_setkeymap_params", keymap)] = ("IN_ARRAY", "0x80")
    FIELD_OVERRIDES[("SC_getkeymap_params", keymap)] = ("OUT_ARRAY", "0x80")


def infer_kind(struct, name, ctype):
    if (struct, name) in FIELD_OVERRIDES:
        return FIELD_OVERRIDES[(struct, name)]
    t = ctype.replace("struct ", "").strip()
    if t == "StringArgument":
        return ("STRING", "_")
    if t == "StringListArgument":
        return ("STRING_LIST", "_")
    if t.startswith("MutableBufferArgument"):
        return ("OUT_BUFFER", "_")
    if t.startswith("union"):
        return ("FUTEX_TIMEOUT", "_")
    if "(*)" in t:
        return ("CODE", "_")
    if t.endswith("*"):
        if re.search(r"\bconst\s*\*$", t) or t.startswith("const "):
            return ("IN_PTR", "_")
        return ("OUT_PTR", "_")
    return ("SCALAR", "_")


def c_type_spelling(ctype):
    """Rewrite C++-only types so the descriptor also parses as C."""
    m = re.fullmatch(r"MutableBufferArgument<(\w+), (\w+)>", ctype)
    if m:
        return f"SC_MUTABLE_BUFFER({m.group(1)}, {m.group(2)})"
    m = re.fullmatch(r"Userspace<(.+)>", ctype)
    if m:
        return f"SC_USERSPACE({m.group(1)})"
    return ctype


def parse_fields(body):
    body = re.sub(r"//[^\n]*", "", body)
    fields = []
    # Pull out an anonymous union as one field.
    union = re.search(r"union\s*\{(.*?)\};", body, re.S)
    if union:
        members = " ".join(x.strip() + ";" for x in union.group(1).split(";") if x.strip())
        body = body.replace(union.group(0), "@UNION@;")
    for decl in body.split(";"):
        decl = " ".join(decl.split())
        if not decl:
            continue
        if decl == "@UNION@":
            fields.append((f"union {{ {members} }}", "", None))
            continue
        init = None
        m = re.match(r"(.*?)\s*=\s*(.+)$", decl)
        if m:
            decl, init = m.group(1), m.group(2)
        m = re.match(r"(.*?)\s*\{\s*(.*?)\s*\}$", decl)
        if m:
            decl, init = m.group(1), m.group(2)
        m = re.fullmatch(r"void\* \(\*(\w+)\)\(void\*\)", decl)
        if m:
            fields.append(("SC_THREAD_ENTRY", m.group(1), init))
            continue
        m = re.fullmatch(r"(.*?[\s\*&>])(\w+)", decl)
        fields.append((m.group(1).strip(), m.group(2), init))
    return fields


struct_re = re.compile(r"struct (SC_\w+_params) \{\n(.*?)\n\};\n", re.S)
structs = []
for m in struct_re.finditer(syscall_h):
    name, body = m.group(1), m.group(2)
    fields = []
    for ctype, fname, init in parse_fields(body):
        kind, extent = infer_kind(name, fname, ctype if ctype != "SC_THREAD_ENTRY" else "(*)")
        fields.append((kind, c_type_spelling(ctype), fname, extent, init))
    structs.append((name, fields, m.group(0)))

# ---------------------------------------------------------------------------
# SyscallParams.h

out = []
out.append("// Generated by experiments/serenity-syscalls/gen.py from Kernel/API/Syscall.h.")
out.append("// Each SC_foo_params struct is described once, field by field, as")
out.append("//   F(kind, type, name, extent, default_initializer...)")
out.append("// Expansions of these X-macros produce the struct itself (Syscall.h), the")
out.append("// trusted marshaller in libpizlo, and the layout checks. The kind says how")
out.append("// the runtime must check a field; extent names the field or constant that")
out.append("// bounds a pointer field, or _ when there is none.")
out.append("#pragma once")
out.append("")
for name, fields, _ in structs:
    out.append(f"#define {name[:-len('_params')]}_FIELDS(F) \\")
    for kind, ctype, fname, extent, init in fields:
        tail = f", {init}" if init is not None else ""
        out.append(f"    F({kind}, {ctype}, {fname}, {extent}{tail}) \\")
    out[-1] = out[-1].rstrip(" \\")
    out.append("")
# Structs the generic marshaller can handle: no field whose meaning depends on
# something other than the struct itself (addresses, code, unions, ...).
SPECIAL_KINDS = {"ADDRESS", "CODE", "OPAQUE_PTR", "FUTEX_TIMEOUT", "SCALAR_OR_PTR", "ATOMIC_U32"}
generic = [n for n, f, _ in structs if not any(k in SPECIAL_KINDS for k, *_ in f)]
out.append("// Params structs whose fields the generic marshaller in libpizlo can check;")
out.append("// the rest have address, code or union fields and need hand-written code.")
out.append("#define ENUMERATE_GENERIC_PARAMS_STRUCTS(P) \\")
for name in generic:
    out.append(f"    P({name[3:-len('_params')]}) \\")
out[-1] = out[-1].rstrip(" \\")
out.append("")
out.append("#define ENUMERATE_PARAMS_STRUCTS(P) \\")
for name, _, _ in structs:
    out.append(f"    P({name[3:-len('_params')]}) \\")
out[-1] = out[-1].rstrip(" \\")
out.append("")
(outdir / "SyscallParams.h").write_text("\n".join(out) + "\n")

# ---------------------------------------------------------------------------
# Syscall.h with the params structs replaced by expansions.

expansion_a = """// Expansion A: the params structs, generated from SyscallParams.h. The layout
// is identical to the hand-written structs these replace (see layout_check.cpp).
#    define SC_MUTABLE_BUFFER(T, S) MutableBufferArgument<T, S>
#    define SC_USERSPACE(T) Userspace<T>
#    define SC_THREAD_ENTRY void* (*entry)(void*)
#    define __SC_FIELD_DECL(kind, type, name, extent, ...) type name __VA_OPT__(= __VA_ARGS__);
#    define __SC_PARAMS_STRUCT(sc) \\
        struct SC_##sc##_params {  \\
            SC_##sc##_FIELDS(__SC_FIELD_DECL) \\
        };
"""
patched = syscall_h
first = True
for name, fields, text in structs:
    if first:
        patched = patched.replace(text, "@PARAMS@\n", 1)
        first = False
    else:
        patched = patched.replace(text, "", 1)
# SC_create_thread_params has a function-pointer field whose declarator wraps
# the name, so it cannot be "type name;". Spell it with SC_THREAD_ENTRY whose
# expansion is the whole declarator and an empty name.
params_block = expansion_a + "ENUMERATE_PARAMS_STRUCTS(__SC_PARAMS_STRUCT)\n"
patched = patched.replace("@PARAMS@\n", params_block)
patched = patched.replace(
    "#include <Kernel/API/POSIX/sched.h>\n",
    "#include <Kernel/API/POSIX/sched.h>\n#include <Kernel/API/SyscallParams.h>\n",
)
# SchedulerParametersMode is used by a params struct, so it moves above them.
sched_enum = "enum class SchedulerParametersMode : bool {\n    Process,\n    Thread,\n};\n\n"
patched = patched.replace(sched_enum, "")
patched = patched.replace("struct StringListArgument {", sched_enum + "struct StringListArgument {")
(outdir / "Syscall.h").write_text(patched)
import difflib
(outdir / "Syscall.h.diff").write_text("".join(difflib.unified_diff(
    syscall_h.splitlines(True), patched.splitlines(True),
    "a/Kernel/API/Syscall.h", "b/Kernel/API/Syscall.h")))

# The thread entry field needs its declarator in the type slot; fix the
# descriptor row so the field expands to "void* (*entry)(void*) ;".
sp = (outdir / "SyscallParams.h").read_text()
sp = sp.replace("F(CODE, SC_THREAD_ENTRY, entry, _)", "F(CODE, SC_THREAD_ENTRY, , _)")
(outdir / "SyscallParams.h").write_text(sp)

# ---------------------------------------------------------------------------
# layout_check.cpp: expand the descriptor into namespace Check and compare it
# with the original hand-written structs, field by field.

lc = []
lc.append("// Generated by experiments/serenity-syscalls/gen.py. Compile against an")
lc.append("// unmodified Kernel/API/Syscall.h: every params struct expanded from")
lc.append("// SyscallParams.h must match the hand-written one in size, alignment, field")
lc.append("// offsets, field types and default member initializers.")
lc.append("#include <AK/Types.h>")
lc.append("#include <Kernel/API/Syscall.h>")
lc.append('#include "SyscallParams.h"')
lc.append("#include <stddef.h>")
lc.append("")
lc.append("namespace Check {")
lc.append("using namespace Kernel::Syscall;")
lc.append(expansion_a.replace("#    define", "#define").split("\n", 2)[2])
lc.append("ENUMERATE_PARAMS_STRUCTS(__SC_PARAMS_STRUCT)")
lc.append("}")
lc.append("")
lc.append("template<typename A, typename B> constexpr bool same = false;")
lc.append("template<typename A> constexpr bool same<A, A> = true;")
lc.append("")
nchecks = 0
for name, fields, _ in structs:
    n, o = f"Check::{name}", f"Kernel::Syscall::{name}"
    lc.append(f"static_assert(sizeof({n}) == sizeof({o}));")
    lc.append(f"static_assert(alignof({n}) == alignof({o}));")
    nchecks += 2
    for kind, ctype, fname, extent, init in fields:
        members = [fname] if fname else (["timeout", "val2"] if kind == "FUTEX_TIMEOUT" else ["entry"])
        for f in members:
            lc.append(f"static_assert(offsetof({n}, {f}) == offsetof({o}, {f}));")
            lc.append(f"static_assert(same<decltype({n}::{f}), decltype({o}::{f})>);")
            nchecks += 2
        if init is not None:
            lc.append(f"static_assert({n} {{}}.{fname} == {o} {{}}.{fname});")
            nchecks += 1
lc.append("")
lc.append(f"// {nchecks} assertions.")
(outdir / "layout_check.cpp").write_text("\n".join(lc) + "\n")

# ---------------------------------------------------------------------------
# Signatures from Process.h.

decls = dict()
for m in re.finditer(r"(?:ErrorOr<FlatPtr>|\[\[noreturn\]\] void) sys\$(\w+)\((.*?)\);", process_h):
    decls[m.group(1)] = m.group(2)

TYPE_MAP = {
    "UserID": "uid_t",
    "GroupID": "gid_t",
    "ProcessID": "pid_t",
    "FlatPtr": "uintptr_t",
}

# Syscalls the runtime must own: they take code or address arguments, or
# change the thread or address-space state libpizlo itself manages.
RUNTIME_OWNED = {
    "mmap": "maps memory; libpizlo must own the address space (as zsys_mmap does on Linux)",
    "mremap": "moves mappings",
    "munmap": "unmaps memory",
    "mprotect": "changes protections of memory libpizlo tracks",
    "madvise": "address range",
    "msync": "address range",
    "set_mmap_name": "address range",
    "annotate_mapping": "address",
    "create_thread": "takes a code pointer and a stack; threads are created by libpizlo",
    "exit_thread": "unmaps the thread's stack",
    "join_thread": "returns a void* exit value that must carry a capability",
    "sigaction": "installs code pointers as handlers; libpizlo runs handlers",
    "sigreturn": "restores machine state",
    "sigaltstack": "points the kernel at a stack",
    "fork": "libpizlo must stop its GC threads around fork",
    "execve": "libpizlo must tear down before exec",
    "posix_spawn": "serialized attrs/file actions are opaque byte blobs",
    "ptrace": "addresses in another process",
    "exit": "libpizlo runs its exit path",
    "futex": "timeout field is a pointer or an integer depending on futex_op",
    "map_time_page": "returns a pointer to a kernel page; needs a capability minted by the runtime",
    "get_stack_bounds": "libpizlo owns stacks",
    "profiling_enable": "kernel profiling buffer",
    "perf_event": "polymorphic arguments",
    "perf_register_string": "registers a string for perf; harmless but kernel-tracing",
    "dump_backtrace": "unwinds the native stack",
}
VARIADIC = {
    "ioctl": "arg is an int or a pointer depending on request",
    "fcntl": "extra_arg is an int or a pointer depending on cmd",
    "prctl": "arg1..3 depend on option",
    "archctl": "arg1..3 depend on option",
}


def classify_args(name, raw):
    raw = raw.strip()
    if not raw:
        return []
    args = []
    for a in [x.strip() for x in raw.split(",")]:
        if a.startswith("RegisterState&"):
            continue
        m = re.fullmatch(r"Userspace<(.*)>\s*(\w*)", a)
        is_user = bool(m)
        if m:
            t = m.group(1).strip()
        else:
            m2 = re.fullmatch(r"(.*?[\s\*&>])(\w+)", a)
            if a.startswith("void* (*)"):
                t = "void* (*)(void*)"
            elif m2 and m2.group(2) not in ("int", "long", "unsigned", "char", "short"):
                t = m2.group(1).strip()
            else:
                t = a
        # POSIX names like sigaction are both a function and a struct, so the
        # pizlonated prototypes keep the elaborated "struct X" spelling.
        if re.fullmatch(r"(const )?(sigaction|stat|statvfs|rusage|utsname|tms|timeval|timespec|sockaddr|msghdr|iovec|utimbuf)\b.*", t):
            t = "struct " + t
        t = TYPE_MAP.get(t, t)
        for k, v in TYPE_MAP.items():
            t = re.sub(rf"\b{k}\b", v, t)
        args.append([t, is_user or t.endswith("*")])
    # Infer kinds and extents.
    out = []
    for i, (t, is_ptr) in enumerate(args):
        kind, extent = "SCALAR", "_"
        if t == "void* (*)(void*)":
            kind = "CODE"
        elif is_ptr:
            base = re.sub(r"\b(const|struct)\b", "", t.rstrip("*")).strip()
            const = "const" in t
            nxt = args[i + 1][0] if i + 1 < len(args) else None
            prv = args[i - 1][0] if i > 0 else None
            if base in ("u8", "void", "char") and nxt in ("size_t",):
                kind = "IN_BYTES" if const else "OUT_BYTES"
                extent = f"arg{i + 1}"
                if base == "u8":
                    t = "void const*" if const else "void*"
            elif base == "iovec" and nxt == "int":
                kind = "IN_IOVEC" if name == "pwritev" else "OUT_IOVEC"
                extent = f"arg{i + 1}"
            elif prv == "size_t" and base == "gid_t":
                kind = "IN_ARRAY" if const else "OUT_ARRAY"
                extent = f"arg{i - 1}"
            elif base == "msghdr":
                kind = "IN_MSGHDR" if const else "INOUT_MSGHDR"
            elif base.startswith("SC_") or base.startswith("Syscall::SC_"):
                kind = "PARAMS"
                t = t.replace("Syscall::", "")
            elif t == "void**":
                kind = "OUT_PTR_PTR"
            else:
                kind = "IN_PTR" if const else "OUT_PTR"
        out.append((kind, t, extent))
    return out


rows = []
missing = []
for sc in syscalls:
    if sc not in decls:
        missing.append(sc)
        continue
    args = classify_args(sc, decls[sc])
    if sc in RUNTIME_OWNED:
        cls = "RUNTIME_OWNED"
    elif sc in VARIADIC:
        cls = "VARIADIC"
    elif any(k == "PARAMS" for k, _, _ in args):
        cls = "PARAMS"
    elif any(k not in ("SCALAR",) for k, _, _ in args):
        cls = "POINTERS"
    else:
        cls = "SCALARS"
    rows.append((sc, cls, args))

sig = []
sig.append("// Generated by experiments/serenity-syscalls/gen.py from Kernel/Tasks/Process.h.")
sig.append("// One row per syscall: S(name, class, A(kind, type, extent)...).")
sig.append("// Userspace<T> becomes T; UserID/GroupID/ProcessID become uid_t/gid_t/pid_t;")
sig.append("// RegisterState& is dropped. extent names the argument (argN) that bounds a")
sig.append("// pointer argument. class is SCALARS, POINTERS, PARAMS, VARIADIC or")
sig.append("// RUNTIME_OWNED (libpizlo implements it itself rather than marshalling).")
sig.append("#pragma once")
sig.append("#define ENUMERATE_SYSCALL_SIGNATURES(S, A) \\")
for sc, cls, args in rows:
    a = ", ".join(f"A({k}, {t}, {e})" for k, t, e in args)
    sig.append(f"    S({sc}, {cls}{', ' if a else ''}{a}) \\")
sig[-1] = sig[-1].rstrip(" \\")
(outdir / "SyscallSignatures.h").write_text("\n".join(sig) + "\n")

# ---------------------------------------------------------------------------
# Report.

from collections import Counter

cls_count = Counter(cls for _, cls, _ in rows)
kind_count = Counter(k for _, f, _ in structs for k, *_ in f)
rep = []
rep.append(f"- syscalls in ENUMERATE_SYSCALLS: {len(syscalls)}")
rep.append(f"- with a sys$ declaration in Process.h: {len(rows)}")
rep.append(f"- without one: {', '.join(missing) or 'none'}")
extra = sorted(set(decls) - set(syscalls))
rep.append(f"- sys$ declarations that are not syscalls: {', '.join(extra) or 'none'}")
rep.append(f"- params structs: {len(structs)}, of which the generic marshaller covers {len(generic)}")
rep.append(f"- params structs needing hand-written marshalling: {', '.join(n for n, *_ in structs if n not in generic)}")
rep.append("")
rep.append("| class | syscalls |")
rep.append("|---|---|")
for c in ("SCALARS", "POINTERS", "PARAMS", "VARIADIC", "RUNTIME_OWNED"):
    rep.append(f"| {c} | {cls_count[c]} |")
rep.append("")
rep.append("| params field kind | fields |")
rep.append("|---|---|")
for k, n in sorted(kind_count.items(), key=lambda x: -x[1]):
    rep.append(f"| {k} | {n} |")
rep.append("")
rep.append("Pointer arguments of POINTERS syscalls, by inferred kind:")
rep.append("")
pk = Counter(k for _, cls, args in rows if cls == "POINTERS" for k, _, _ in args if k != "SCALAR")
for k, n in sorted(pk.items(), key=lambda x: -x[1]):
    rep.append(f"- {k}: {n}")
(outdir / "report.md").write_text("\n".join(rep) + "\n")
print("\n".join(rep))
