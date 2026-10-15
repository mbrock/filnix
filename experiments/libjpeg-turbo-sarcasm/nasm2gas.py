#!/usr/bin/env python3
"""Convert libjpeg-turbo's NASM-preprocessed x86-64 SIMD into GNU as Intel
syntax with SaRCAsm annotations.

usage: nasm2gas.py INPUT.pre SIGNATURES.txt > OUTPUT.s

SIGNATURES.txt maps function names to Fil-C signatures, one per line:
    jsimd_idct_islow_avx2 void(ptr, ptr, ptr, unsigned)
"""
import re
import sys

src, sigfile = sys.argv[1], sys.argv[2]
stackbufs = {}
import os
_sb = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'stackbufs.txt')
for line in open(_sb):
    if line.strip() and not line.startswith('#'):
        f, reg, off, size = line.split()
        stackbufs[f] = (reg, int(off), int(size))
sigs = {}
for line in open(sigfile):
    line = line.strip()
    if line and not line.startswith('#'):
        name, sig = line.split(None, 1)
        sigs[name] = sig

out = ['\t.intel_syntax noprefix']
func = None          # current function, for local-label scoping
absolute = None      # [struct name, offset] inside an [absolute 0] block
AVX_TWO_OPERAND = {'vmovd', 'vmovq', 'vmovdqa', 'vmovdqu', 'vmovntdq',
                   'vpabsw', 'vpmovzxbw'}
RES_SIZE = {'resb': 1, 'resw': 2, 'resd': 4, 'resq': 8}
section = None
labels_seen = set()


def local(name):
    # NASM .label is scoped to the previous non-local label.
    return '.L%s_%s' % (func or 'file', name[1:])


def fix_operands(s):
    s = re.sub(r'\[\s*rel\s+', '[rip + ', s)
    s = re.sub(r'\b(byte|word|dword|qword|xmmword|ymmword|tword)\s*\[',
               lambda m: m.group(1) + ' ptr [', s)
    # Size keywords on immediates (`sub rsp, byte 16`) are encoding hints.
    s = re.sub(r',\s*(byte|word|dword|qword)\s+(?![\[p])', ', ', s)
    s = re.sub(r'\b(near|short)\s+', '', s)
    s = re.sub(r'(?<![\w.])(\.[A-Za-z_][\w]*)', lambda m: local(m.group(1)), s)
    s = s.replace('$$', '0')
    # Displacement-size hints inside brackets: [dword rdi - 2]
    s = re.sub(r'\[\s*(?:byte|dword)\s+', '[', s)
    # NASM binary literals: 11001001b
    s = re.sub(r'\b([01]+)b\b', r'0b\1', s)
    # NASM accepts two-operand AVX forms meaning "dst = dst op src".
    m = re.match(r'(v\w+)\s+(.*)$', s)
    if m and m.group(1) not in AVX_TWO_OPERAND:
        ops = [o.strip() for o in split_operands(m.group(2))]
        if len(ops) == 2:
            s = '%s %s, %s, %s' % (m.group(1), ops[0], ops[0], ops[1])
    return s


REGS = set()
for r in ['ax', 'bx', 'cx', 'dx', 'si', 'di', 'bp', 'sp']:
    REGS |= {'r' + r, 'e' + r, r}
for i in range(8, 16):
    REGS |= {'r%d' % i, 'r%dd' % i, 'r%dw' % i, 'r%db' % i}
REGS |= {'al', 'bl', 'cl', 'dl', 'sil', 'dil', 'rip'}
REGS |= {'%smm%d' % (p, i) for p in 'xyz' for i in range(32)}
REGS |= {'mm%d' % i for i in range(8)}
consts = {}
data_offset = {}     # section -> current byte offset of emitted data
label_at = {}        # data label -> (section, offset)
DATA_SIZE = {'db': 1, 'dw': 2, 'dd': 4, 'dq': 8}


class Lin:
    """A linear combination of symbols (registers, labels) plus a constant."""

    def __init__(self, terms=None, c=0):
        self.terms, self.c = dict(terms or {}), c

    @staticmethod
    def of(x):
        return x if isinstance(x, Lin) else Lin({}, x)

    def __add__(self, o):
        o = Lin.of(o)
        t = dict(self.terms)
        for k, v in o.terms.items():
            t[k] = t.get(k, 0) + v
        return Lin({k: v for k, v in t.items() if v}, self.c + o.c)
    __radd__ = __add__

    def __neg__(self):
        return Lin({k: -v for k, v in self.terms.items()}, -self.c)

    def __sub__(self, o):
        return self + -Lin.of(o)

    def __rsub__(self, o):
        return Lin.of(o) - self

    def __mul__(self, o):
        if isinstance(o, Lin):
            if o.terms and self.terms:
                raise ValueError('nonlinear')
            if not o.terms:
                o = o.c
            else:
                return o * self.c
        return Lin({k: v * o for k, v in self.terms.items()}, self.c * o)
    __rmul__ = __mul__

    def __floordiv__(self, o):
        if self.terms or isinstance(o, Lin):
            raise ValueError('symbolic division')
        return self.c // o


def evaluate(expr):
    e = re.sub(r'\b0x([0-9a-fA-F]+)\b', lambda m: str(int(m.group(1), 16)), expr)
    e = re.sub(r'\b0b([01]+)\b', lambda m: str(int(m.group(1), 2)), e)
    e = re.sub(r'\b([0-9a-fA-F]+)h\b', lambda m: str(int(m.group(1), 16)), e)
    e = e.replace('/', '//')
    names = {}
    for n in set(re.findall(r'[A-Za-z_.][\w.]*', e)):
        if n in consts:
            names[n] = consts[n]
        else:
            names[n] = Lin({n: 1})
    # Dotted names are not Python identifiers; rename them.
    mapping = {}
    for i, n in enumerate(sorted(names, key=len, reverse=True)):
        mapping['__n%d' % i] = names[n]
        e = re.sub(r'(?<![\w.])' + re.escape(n) + r'(?![\w.])', '__n%d' % i, e)
    v = eval(e, {'__builtins__': {}}, mapping)
    if isinstance(v, Lin):
        pos = [k for k, c in v.terms.items() if c == 1 and k in label_at]
        neg = [k for k, c in v.terms.items() if c == -1 and k in label_at]
        if len(pos) == 1 and len(neg) == 1 and label_at[pos[0]][0] == label_at[neg[0]][0]:
            t = {k: c for k, c in v.terms.items() if k not in (pos[0], neg[0])}
            v = Lin(t, v.c + label_at[pos[0]][1] - label_at[neg[0]][1])
    return v


def fold_operand(op):
    op = op.strip()
    m = re.match(r'^(.*?\bptr\s*)?\[(.*)\]$', op)
    if m:
        prefix, inner = m.group(1) or '', m.group(2)
        v = Lin.of(evaluate(inner))
        regs = [(k, c) for k, c in v.terms.items() if k in REGS]
        syms = [(k, c) for k, c in v.terms.items() if k not in REGS]
        base = [k for k, c in regs if c == 1]
        idx = [(k, c) for k, c in regs if c != 1]
        # [rcx * 3] is encoded as [rcx + rcx * 2]
        if not base and len(idx) == 1 and idx[0][1] in (3, 5, 9):
            base = [idx[0][0]]
            idx = [(idx[0][0], idx[0][1] - 1)]
        parts = []
        if len(base) == 2 and not idx:
            parts = [base[0], base[1]]
        elif len(base) == 1 and len(idx) <= 1:
            parts = [base[0]] + ['%s * %d' % (k, c) for k, c in idx]
        elif not base and len(idx) == 1:
            parts = ['%s * %d' % idx[0]]
        elif regs:
            raise ValueError('bad address: ' + op)
        for k, c in syms:
            if c not in (1, -1):
                raise ValueError('scaled symbol: ' + op)
            parts.append(k if c == 1 else '-' + k)
        if v.c or not parts:
            parts.append(str(v.c))
        out = ' + '.join(parts).replace('+ -', '- ')
        if out.startswith('-'):
            raise ValueError('negative leading term: ' + op)
        return '%s[%s]' % (prefix, out)
    if re.search(r'[()+*<>-]|\b0b|\b\d', op) and not re.fullmatch(r'[\w.]+', op):
        v = evaluate(op)
        if isinstance(v, Lin):
            if v.terms:
                return op
            v = v.c
        return str(v)
    m = re.fullmatch(r'0b([01]+)', op)
    if m:
        return str(int(m.group(1), 2))
    return op


def fold(s):
    m = re.match(r'(\S+)(\s+)(.*)$', s)
    if not m:
        return s
    ops = [fold_operand(o) for o in split_operands(m.group(3))]
    return m.group(1) + ' ' + ', '.join(ops)


def split_operands(s):
    out, depth, cur = [], 0, ''
    for c in s:
        if c == '[':
            depth += 1
        elif c == ']':
            depth -= 1
        if c == ',' and depth == 0:
            out.append(cur)
            cur = ''
        else:
            cur += c
    out.append(cur)
    return out


def data(kind, args):
    d = {'db': '.byte', 'dw': '.short', 'dd': '.long', 'dq': '.quad'}[kind]
    if kind == 'dd' and re.search(r'\d\.\d', args):
        d = '.float'
    if d != '.float':
        args = ', '.join(str(Lin.of(evaluate(a)).c) for a in split_operands(args))
    return '\t%s %s' % (d, args), DATA_SIZE[kind] * len(split_operands(args))


for raw in open(src):
    line = raw.rstrip('\n')
    if line.startswith('%line') or not line.strip():
        continue
    line = line.split(';', 1)[0].rstrip()
    if not line.strip():
        continue
    s = line.strip()
    # NASM macro-local labels: ..@9..ELOAD15
    s = re.sub(r'\.\.@(\d+)\.\.?(\w+)', r'Lm\1_\2', s)

    if absolute is not None:
        m = re.match(r'(\.?[\w.]+):?\s+(resb|resw|resd|resq)\s+(\d+)$', s)
        if m:
            consts[absolute[0] + m.group(1)] = absolute[1]
            absolute[1] += RES_SIZE[m.group(2)] * int(m.group(3))
            continue
        m = re.match(r'(\w+):$', s)
        if m:
            absolute[0] = m.group(1)
            absolute[1] = 0
            continue
        m = re.match(r'(\w+)\s+equ\s+\(\$-(\w+)\)$', s)
        if m:
            consts[m.group(1)] = absolute[1]
            continue
        absolute = None
    if s == '[absolute 0]':
        absolute = ['', 0]
        continue
    m = re.match(r'\[section\s+(\S+)', s)
    if m:
        name = m.group(1)
        section = name
        if name == '.note.GNU-stack':
            out.append('\t.section .note.GNU-stack,"",@progbits')
        elif name == '.text':
            out.append('\t.text')
        else:
            out.append('\t.section %s,"a"' % name)
        continue
    if re.match(r'\[(bits|sectalign|warning)\b', s):
        continue
    m = re.match(r'\[global\s+(\w+):(function|data)\s+hidden\]', s)
    if m:
        name, kind = m.groups()
        out.append('\t.globl %s\n\t.hidden %s\n\t.type %s,@%s' %
                   (name, name, name, 'function' if kind == 'function' else 'object'))
        continue
    # Alignment padding: times (((32) - (($-$$) % (32))) % (32)) db 0 / nop
    m = re.match(r'times\s+\(\(\((\d+)\).*\)\s+(db 0|nop)$', s)
    if m:
        a = int(m.group(1))
        off = data_offset.get(section, 0)
        data_offset[section] = (off + a - 1) // a * a
        out.append('\t.p2align %d' % (int(m.group(1)).bit_length() - 1))
        continue
    m = re.match(r'(\w+)\s+equ\s+(.*)$', s)
    if m:
        consts[m.group(1)] = Lin.of(evaluate(m.group(2))).c
        continue
    # [label] [times N] dX args
    m = re.match(r'(?:(\w+)\s+)?(?:times\s+(.+?)\s+)?(db|dw|dd|dq)\s+(.*)$', s)
    if m and section != '.text':
        label, count, kind, args = m.groups()
        off = data_offset.get(section, 0)
        if label:
            out.append('%s:' % label)
            label_at[label] = (section, off)
        text, size = data(kind, args)
        n = Lin.of(evaluate(count)).c if count else 1
        # SaRCAsm's data parser does not understand .rept; expand it.
        d, vals = text.split(None, 1)
        vals = ', '.join([vals] * n)
        out.append('\t%s %s' % (d, vals))
        data_offset[section] = off + size * n
        continue
    m = re.match(r'(\.?\w+):$', s)
    if m:
        name = m.group(1)
        if section != '.text':
            label_at[name] = (section, data_offset.get(section, 0))
        if name.startswith('.'):
            out.append('%s:' % local(name))
        else:
            if section == '.text' and not re.match(r'Lm\d+_', name):
                func = name
            sig = sigs.get(name)
            out.append('%s:%s' % (name, ' #! ' + sig if sig else ''))
        continue
    m = re.match(r'times\s+(\d+)\s+nop$', s)
    if m:
        out.append('\t.rept %s\n\tnop\n\t.endr' % m.group(1))
        continue
    m = re.match(r'FILC_ALLOCA\s+(.*)$', s)
    if m:
        size, align, reg = [o.strip() for o in split_operands(m.group(1))]
        out.append('\t.alloca %d, %d, %s' % (Lin.of(evaluate(size)).c,
                                             Lin.of(evaluate(align)).c, reg))
        continue
    # An instruction.
    ins = fold(fix_operands(s))
    out.append('\t' + ins)

ARG_REGS = {'rdi', 'rsi', 'rdx', 'rcx', 'r8', 'r9'}


def is_prologue(ins):
    """Instructions SaRCAsm models as function prologue."""
    if re.match(r'(push \w+|endbr64|mov rbp, rsp|and rsp, -\d+|sub rsp, \d+)$', ins):
        return True
    if re.match(r'mov (r1[0-5]|rax), rsp$', ins) or re.match(r'lea rsp, \[', ins):
        return True
    m = re.match(r'mov (r1[0-5]), (\w+)$', ins)
    return bool(m and m.group(2) in ARG_REGS)


def annotate(lines):
    """Per function: turn transient push/pop into pseudo-register moves, mark
    pointer-sized GPR loads/stores, and annotate calls with signatures."""
    res = []
    prologue = False
    depth = 0
    buf = None       # (name, frame reg, offset, size) for this function
    bufregs = set()  # registers holding an address inside the buffer
    rsp_rel = None   # rsp minus the frame register, when known
    buf_decl = None
    for line in lines:
        st = line.strip()
        m = re.match(r'([A-Za-z_]\w*):( #!.*)?$', st)
        if m and m.group(2):
            prologue, depth = True, 0
            buf = None
            bufregs = set()
            rsp_rel = None
            if m.group(1) in stackbufs:
                reg, off, size = stackbufs[m.group(1)]
                buf = ('ws_' + m.group(1), reg, off, size)
            res.append(line)
            continue
        if not line.startswith('\t') or st.startswith('.'):
            res.append(line)
            continue
        if prologue and not is_prologue(st):
            prologue = False
        if not prologue:
            m = re.match(r'push (\w+)$', st)
            if m:
                res.append('\tmov %%fil_s%d, %s' % (depth, m.group(1)))
                depth += 1
                continue
            m = re.match(r'pop (\w+)$', st)
            if m and depth > 0:
                depth -= 1
                res.append('\tmov %s, %%fil_s%d' % (m.group(1), depth))
                continue
        if buf:
            name, base, off, size = buf
            # Track rsp relative to the frame register (r15) for base r15.
            m = re.match(r'lea rsp, \[%s - (\d+)\]$' % base, st)
            if m:
                rsp_rel = -int(m.group(1))
            elif rsp_rel is not None and re.match(r'push \w+$', st) and prologue:
                rsp_rel -= 8
            target = None
            m = re.match(r'lea (\w+), \[%s - %d\]$' % (base, -off), st)
            if base != 'rsp' and m and m.group(1) != 'rsp' and rsp_rel is not None:
                target, k = m.group(1), off - rsp_rel
            m = re.match(r'mov (\w+), rsp$', st)
            if base == 'rsp' and m and not prologue:
                target, k = m.group(1), 0
            if target:
                bufregs.add(target)
                buf_decl = '%s, %%rsp + %d, %%rsp + %d' % (name, k, k + size)
                res.append('\tlea %s, [rsp + %d]' % (target, k))
                continue
            m = re.match(r'(mov|lea|xor|pop|movzx|movsx) (\w+),', st)
            if m and m.group(2) in bufregs and not re.search(r'\[%s\b' % m.group(2), st):
                bufregs.discard(m.group(2))
            m = re.search(r'\[(\w+)( [+-] \d+)?\]', st)
            if m and m.group(1) in bufregs and not st.startswith(('prefetch', 'lea')):
                res.append(line + ' #! stack buffer (%s)' % buf_decl)
                continue
        # Taking the frame's address with `mov reg, rsp` is not seen as an
        # escape; the lea spelling makes SaRCAsm promote the frame to a
        # GC allocation so a callee can read it.
        m = re.match(r'mov (\w+), rsp$', st)
        if m and not prologue and not buf:
            res.append('\tlea %s, [rsp]' % m.group(1))
            continue
        if re.match(r'mov r(\w+), qword ptr \[', st):
            line += ' #! load ptr'
        elif re.match(r'mov qword ptr \[[^]]*\], r\w+$', st):
            line += ' #! store ptr'
        m = re.match(r'call (\w+)$', st)
        if m and m.group(1) in sigs:
            line += ' #! ' + sigs[m.group(1)]
        res.append(line)
    return res


print('\n'.join(annotate(out)))
