/* Prototype: replay sljit LIR (dumped from a native PCRE2 JIT compile of the
   same pattern) into LLVM IR, compile it with the Fil-C LLVM JIT, and run it
   against Fil-C PCRE2 data structures.  This stands in for an sljit "LLVM
   backend": the lowering below is what such a backend's sljit_emit_* functions
   would do.

   Lowering rules:
   - every sljit register is an alloca of `ptr`; machine words are `ptr` so
     that Fil-C capabilities survive moves and stores to the backtrack stack;
   - word loads/stores are `ptr` loads/stores, narrow ones are integers;
   - add/sub are GEPs on the first operand, other arithmetic goes through
     ptrtoint/inttoptr;
   - flags are three hidden i64 slots (result, lhs, rhs) recomputed at the use;
   - labels are basic blocks; fast_call/fast_return/mov_addr/ijump use small
     integer "addresses" and a switch;
   - immediates that are host addresses become GEPs on extern globals bound
     with FilLLVMJIT_SetGlobalMapping. */
#include "config.h"
#define PCRE2_CODE_UNIT_WIDTH 8
#include "pcre2_internal.h"
#include <filc_llvm_jit.h>
#include <stdbool.h>
#include <stdfil.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <sys/wait.h>
#include <unistd.h>

#include "pats.h"

static double now(void)
{
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

#define DIE(...) (fprintf(stderr, __VA_ARGS__), fprintf(stderr, "\n"), exit(1))

/* ---- copies of the JIT-side structs (pcre2_jit_compile.c, sljitLir.h) ---- */

struct sljit_stack {
    uint8_t *top, *end, *start, *min_start;
};

typedef struct jit_arguments {
    struct sljit_stack *stack;
    PCRE2_SPTR str;
    PCRE2_SPTR begin;
    PCRE2_SPTR end;
    pcre2_match_data *match_data;
    PCRE2_SPTR startchar_ptr;
    PCRE2_UCHAR *mark_ptr;
    int (*callout)(pcre2_callout_block *, void *);
    void *callout_data;
    size_t offset_limit;
    uint32_t limit_match;
    uint32_t oveccount;
    uint32_t options;
} jit_arguments;

typedef int (*jit_function)(jit_arguments *);

static void *stack_resize(void *stackp, void *new_start)
{
    struct sljit_stack *stack = stackp;
    if ((uint8_t *)new_start < stack->min_start || (uint8_t *)new_start > stack->end)
        return NULL;
    stack->start = new_start;
    return new_start;
}

static void *unsupported_call(void *a, void *b)
{
    DIE("unsupported icall");
    return NULL;
}

/* ---- symbols for host addresses ---- */

typedef struct {
    char name[40];
    uint64_t base, size;
    int64_t bias;
    void *host;
    bool is_fn;
    LLVMValueRef g;
} sym;

static sym syms[64];
static int nsyms;

/* ---- translator state ---- */

enum { R_SP = 10, NREGS = 10 };
typedef enum { O_NONE, O_REG, O_IMM, O_MEM } okind;
typedef struct {
    okind k;
    int reg;       /* O_REG */
    int64_t imm;   /* O_IMM value, O_MEM displacement */
    int base;      /* O_MEM */
    int index;     /* O_MEM, -1 if none */
    int scale;
} opnd;

static LLVMContextRef C;
static LLVMModuleRef M;
static LLVMBuilderRef B;
static LLVMTypeRef i8, i16, i32, i64, ptr;
static LLVMValueRef F, regs[NREGS], locals, flag_res, flag_a, flag_b, retaddr;

#define MAXL 4096
static LLVMBasicBlockRef label_bb[MAXL];
static bool label_placed[MAXL];
static int jump_target[MAXL], addr_target[MAXL];

static LLVMValueRef switches[MAXL];
static int nswitches;
static LLVMBasicBlockRef cases[MAXL];
static int ncases;

static LLVMValueRef K(int64_t v) { return LLVMConstInt(i64, (unsigned long long)v, true); }

static void fresh(void)
{
    LLVMPositionBuilderAtEnd(B, LLVMAppendBasicBlockInContext(C, F, ""));
}

static LLVMBasicBlockRef get_label(int id)
{
    if (id < 0 || id >= MAXL)
        DIE("label id %d", id);
    if (!label_bb[id])
        label_bb[id] = LLVMAppendBasicBlockInContext(C, F, "L");
    return label_bb[id];
}

static bool is_host_addr(int64_t v) { return v > ((int64_t)1 << 40); }

static sym *find_sym(uint64_t v)
{
    sym *best = NULL;
    for (int i = 0; i < nsyms; i++) {
        sym *s = &syms[i];
        if (s->is_fn) {
            if (v == s->base)
                return s;
            continue;
        }
        if (s->size ? (v >= s->base && v <= s->base + s->size) : v >= s->base)
            if (!best || s->base > best->base)
                best = s;
    }
    if (!best || v - best->base > (1 << 20))
        DIE("unknown host address %lu", (unsigned long)v);
    return best;
}

static LLVMValueRef host_ptr(int64_t v)
{
    sym *s = find_sym((uint64_t)v);
    if (!s->g)
        s->g = LLVMAddGlobal(M, i8, s->name);
    LLVMValueRef off = K((int64_t)((uint64_t)v - s->base) + s->bias);
    return LLVMBuildGEP2(B, i8, s->g, &off, 1, "");
}

static opnd parse_opnd(const char *s)
{
    opnd o = { O_NONE, 0, 0, -1, -1, 1 };
    while (*s == ' ')
        s++;
    if (!strncmp(s, "unset", 5))
        return o;
    if (*s == '#') {
        o.k = O_IMM;
        o.imm = (int64_t)strtoull(s + 1, NULL, 10);
        if (s[1] == '-')
            o.imm = strtoll(s + 1, NULL, 10);
        return o;
    }
    if ((*s == 'r' || *s == 's') && s[1] >= '0' && s[1] <= '9') {
        o.k = O_REG;
        o.reg = (*s == 's' ? 5 : 0) + (s[1] - '0');
        if (s[1] > '4')
            DIE("register %s", s);
        return o;
    }
    if (*s == '[') {
        o.k = O_MEM;
        s++;
        if (!strncmp(s, "sp", 2))
            o.base = R_SP;
        else if ((*s == 'r' || *s == 's') && s[1] >= '0' && s[1] <= '4')
            o.base = (*s == 's' ? 5 : 0) + (s[1] - '0');
        else
            DIE("mem base %s", s);
        s += 2;
        if (!strncmp(s, " + ", 3)) {
            s += 3;
            if (*s == 'r' || *s == 's') {
                o.index = (*s == 's' ? 5 : 0) + (s[1] - '0');
                s += 2;
                if (!strncmp(s, " * ", 3))
                    o.scale = atoi(s + 3);
            } else if (*s == '-')
                o.imm = strtoll(s, NULL, 10);
            else
                o.imm = (int64_t)strtoull(s, NULL, 10);
        }
        return o;
    }
    DIE("operand %s", s);
    return o;
}

static LLVMValueRef reg_ptr(int r) { return LLVMBuildLoad2(B, ptr, regs[r], ""); }
static LLVMValueRef reg_int(int r) { return LLVMBuildPtrToInt(B, reg_ptr(r), i64, ""); }

static LLVMValueRef mem_addr(opnd o)
{
    LLVMValueRef idx;
    if (o.base == R_SP) {
        idx = K(o.imm);
        return LLVMBuildGEP2(B, i8, locals, &idx, 1, "");
    }
    if (o.index >= 0) {
        idx = LLVMBuildMul(B, reg_int(o.index), K(o.scale), "");
        return LLVMBuildGEP2(B, i8, reg_ptr(o.base), &idx, 1, "");
    }
    if (is_host_addr(o.imm)) {
        idx = reg_int(o.base);
        return LLVMBuildGEP2(B, i8, host_ptr(o.imm), &idx, 1, "");
    }
    idx = K(o.imm);
    return LLVMBuildGEP2(B, i8, reg_ptr(o.base), &idx, 1, "");
}

static LLVMValueRef opnd_ptr(opnd o)
{
    switch (o.k) {
    case O_REG: return reg_ptr(o.reg);
    case O_IMM: return is_host_addr(o.imm) ? host_ptr(o.imm) : LLVMConstIntToPtr(K(o.imm), ptr);
    case O_MEM: return LLVMBuildLoad2(B, ptr, mem_addr(o), "");
    default: DIE("opnd_ptr");
    }
    return NULL;
}

static LLVMValueRef opnd_int(opnd o)
{
    switch (o.k) {
    case O_REG: return reg_int(o.reg);
    case O_IMM: return is_host_addr(o.imm) ? LLVMBuildPtrToInt(B, host_ptr(o.imm), i64, "") : K(o.imm);
    case O_MEM: return LLVMBuildLoad2(B, i64, mem_addr(o), "");
    default: DIE("opnd_int");
    }
    return NULL;
}

static LLVMValueRef opnd_int32(opnd o)
{
    if (o.k == O_MEM)
        return LLVMBuildLoad2(B, i32, mem_addr(o), "");
    return LLVMBuildTrunc(B, opnd_int(o), i32, "");
}

static void store_word(opnd o, LLVMValueRef p)
{
    if (o.k == O_REG)
        LLVMBuildStore(B, p, regs[o.reg]);
    else if (o.k == O_MEM)
        LLVMBuildStore(B, p, mem_addr(o));
    else
        DIE("store_word");
}

static void store_int(opnd o, LLVMValueRef v) { store_word(o, LLVMBuildIntToPtr(B, v, ptr, "")); }

static LLVMValueRef flag_cond(const char *c)
{
    static const struct { const char *name; LLVMIntPredicate p; } preds[] = {
        { "less", LLVMIntULT }, { "greater_equal", LLVMIntUGE }, { "greater", LLVMIntUGT },
        { "less_equal", LLVMIntULE }, { "sig_less", LLVMIntSLT }, { "sig_greater_equal", LLVMIntSGE },
        { "sig_greater", LLVMIntSGT }, { "sig_less_equal", LLVMIntSLE },
    };
    if (!strcmp(c, "equal") || !strcmp(c, "not_equal"))
        return LLVMBuildICmp(B, c[0] == 'e' ? LLVMIntEQ : LLVMIntNE, LLVMBuildLoad2(B, i64, flag_res, ""), K(0), "");
    for (unsigned i = 0; i < sizeof(preds) / sizeof(preds[0]); i++)
        if (!strcmp(c, preds[i].name))
            return LLVMBuildICmp(B, preds[i].p, LLVMBuildLoad2(B, i64, flag_a, ""),
                                 LLVMBuildLoad2(B, i64, flag_b, ""), "");
    DIE("condition %s", c);
    return NULL;
}

static LLVMValueRef cmp_cond(const char *c, LLVMValueRef a, LLVMValueRef b)
{
    static const struct { const char *name; LLVMIntPredicate p; } preds[] = {
        { "equal", LLVMIntEQ }, { "not_equal", LLVMIntNE },
        { "less", LLVMIntULT }, { "greater_equal", LLVMIntUGE }, { "greater", LLVMIntUGT },
        { "less_equal", LLVMIntULE }, { "sig_less", LLVMIntSLT }, { "sig_greater_equal", LLVMIntSGE },
        { "sig_greater", LLVMIntSGT }, { "sig_less_equal", LLVMIntSLE },
    };
    for (unsigned i = 0; i < sizeof(preds) / sizeof(preds[0]); i++)
        if (!strcmp(c, preds[i].name))
            return LLVMBuildICmp(B, preds[i].p, a, b, "");
    DIE("condition %s", c);
    return NULL;
}

static void set_flags(LLVMValueRef res, LLVMValueRef a, LLVMValueRef b)
{
    LLVMBuildStore(B, res, flag_res);
    LLVMBuildStore(B, a, flag_a);
    LLVMBuildStore(B, b, flag_b);
}

static int new_address(LLVMBasicBlockRef bb)
{
    cases[ncases++] = bb;
    return ncases; /* 1-based */
}

static void dispatch(LLVMValueRef v)
{
    LLVMBasicBlockRef trap = LLVMAppendBasicBlockInContext(C, F, "badaddr");
    switches[nswitches++] = LLVMBuildSwitch(B, v, trap, 8);
    LLVMPositionBuilderAtEnd(B, trap);
    LLVMBuildUnreachable(B);
    fresh();
}

static int split_args(char *s, char **args)
{
    int n = 0;
    while (*s == ' ')
        s++;
    if (!*s)
        return 0;
    args[n++] = s;
    for (char *p = s; *p; p++)
        if (p[0] == ',' && p[1] == ' ') {
            *p = 0;
            args[n++] = p + 2;
        }
    return n;
}

static unsigned translate(char **lines, int nlines)
{
    /* Pre-pass: jump targets. */
    for (int i = 0; i < nlines; i++) {
        unsigned long j, l;
        if (sscanf(lines[i], " @J%lu->L%lu", &j, &l) == 2) {
            if (j >= 1000000)
                addr_target[j - 1000000] = (int)l;
            else
                jump_target[j] = (int)l;
        }
    }

    for (int i = 0; i < nlines; i++) {
        char buf[512];
        char *line = lines[i];
        while (*line == ' ')
            line++;
        if (!*line || !strncmp(line, "SYM", 3) || !strncmp(line, "RODATA", 6) || line[0] == '@')
            continue;
        if (!strncmp(line, "label:", 6))
            continue;
        if (line[0] == '=' && line[1] == 'L') {
            int id = atoi(line + 2);
            LLVMBasicBlockRef bb = get_label(id);
            if (!label_placed[id]) {
                LLVMBuildBr(B, bb);
                LLVMPositionBuilderAtEnd(B, bb);
                label_placed[id] = true;
            }
            continue;
        }
        if (line[0] == '=')
            DIE("stray %s", line);
        snprintf(buf, sizeof buf, "%s", line);
        char *sp = strchr(buf, ' ');
        char *rest = sp ? sp + 1 : buf + strlen(buf);
        if (sp)
            *sp = 0;
        char *args[8];
        char *suffix = strchr(buf, '.');
        if (suffix)
            *suffix++ = 0;
        const char *op = buf;

        /* Jump id on the following line, if any. */
        long jid = -1;
        if (i + 1 < nlines && sscanf(lines[i + 1], " =J%ld", &jid) == 1)
            i++;

        if (!strcmp(op, "enter")) {
            char *ls = strstr(rest, "local_size:");
            int local_size = atoi(ls + 11);
            LLVMTypeRef fty = LLVMFunctionType(i32, &ptr, 1, false);
            F = LLVMAddFunction(M, "match", fty);
            LLVMPositionBuilderAtEnd(B, LLVMAppendBasicBlockInContext(C, F, "entry"));
            for (int r = 0; r < NREGS; r++)
                regs[r] = LLVMBuildAlloca(B, ptr, "reg");
            locals = LLVMBuildAlloca(B, LLVMArrayType(i64, (unsigned)(local_size + 7) / 8), "locals");
            flag_res = LLVMBuildAlloca(B, i64, "flag_res");
            flag_a = LLVMBuildAlloca(B, i64, "flag_a");
            flag_b = LLVMBuildAlloca(B, i64, "flag_b");
            retaddr = LLVMBuildAlloca(B, i64, "retaddr");
            LLVMBuildStore(B, LLVMGetParam(F, 0), regs[5]);
            continue;
        }
        if (!strcmp(op, "endbr") || !strcmp(op, "skip_frames_before_return"))
            continue;

        int n = split_args(rest, args);

        if (!strcmp(op, "mov")) {
            opnd dst = parse_opnd(args[0]), src = parse_opnd(args[1]);
            if (!suffix) {
                store_word(dst, opnd_ptr(src));
                continue;
            }
            bool sign = suffix[0] == 's';
            int bits = atoi(suffix + 1);
            LLVMTypeRef ty = bits == 8 ? i8 : bits == 16 ? i16 : bits == 32 ? i32 : NULL;
            if (!ty)
                DIE("mov.%s", suffix);
            LLVMValueRef v;
            if (src.k == O_MEM) {
                v = LLVMBuildLoad2(B, ty, mem_addr(src), "");
                LLVMSetAlignment(v, 1);
            } else
                v = LLVMBuildTrunc(B, opnd_int(src), ty, "");
            if (dst.k == O_MEM)
                LLVMSetAlignment(LLVMBuildStore(B, v, mem_addr(dst)), 1);
            else
                store_int(dst, sign ? LLVMBuildSExt(B, v, i64, "") : LLVMBuildZExt(B, v, i64, ""));
            continue;
        }

        bool is32 = false;
        char opn[32];
        snprintf(opn, sizeof opn, "%s", op);
        size_t ol = strlen(opn);
        if (ol > 2 && !strcmp(opn + ol - 2, "32")) {
            is32 = true;
            opn[ol - 2] = 0;
        }
        LLVMOpcode code = !strcmp(opn, "add") ? LLVMAdd : !strcmp(opn, "sub") ? LLVMSub
            : !strcmp(opn, "and") ? LLVMAnd : !strcmp(opn, "or") ? LLVMOr : !strcmp(opn, "xor") ? LLVMXor
            : !strcmp(opn, "shl") ? LLVMShl : !strcmp(opn, "lshr") ? LLVMLShr : !strcmp(opn, "ashr") ? LLVMAShr : 0;
        if (code) {
            opnd dst = parse_opnd(args[0]), a = parse_opnd(args[1]), b = parse_opnd(args[2]);
            if (suffix && !strncmp(suffix, "shl_imm", 7)) {
                /* dst = a + (b << imm) */
                opnd sh = parse_opnd(args[3]);
                LLVMValueRef idx = LLVMBuildShl(B, opnd_int(b), K(sh.imm), "");
                store_word(dst, LLVMBuildGEP2(B, i8, opnd_ptr(a), &idx, 1, ""));
                continue;
            }
            if ((code == LLVMAdd || code == LLVMSub) && !is32) {
                if (code == LLVMAdd && b.k != O_IMM && a.k == O_IMM && !is_host_addr(a.imm)) {
                    opnd t = a; a = b; b = t;
                }
                if (code == LLVMAdd && b.k == O_IMM && is_host_addr(b.imm)) {
                    opnd t = a; a = b; b = t;
                }
                LLVMValueRef ap = opnd_ptr(a), bi = opnd_int(b);
                LLVMValueRef idx = code == LLVMAdd ? bi : LLVMBuildNeg(B, bi, "");
                LLVMValueRef rp = LLVMBuildGEP2(B, i8, ap, &idx, 1, "");
                if (suffix) {
                    LLVMValueRef ai = LLVMBuildPtrToInt(B, ap, i64, "");
                    set_flags(LLVMBuildBinOp(B, code, ai, bi, ""), ai, bi);
                }
                if (dst.k != O_NONE)
                    store_word(dst, rp);
                continue;
            }
            LLVMValueRef ai = is32 ? opnd_int32(a) : opnd_int(a), bi = is32 ? opnd_int32(b) : opnd_int(b);
            LLVMValueRef r = LLVMBuildBinOp(B, code, ai, bi, "");
            if (is32) {
                r = LLVMBuildZExt(B, r, i64, "");
                ai = LLVMBuildZExt(B, ai, i64, "");
                bi = LLVMBuildZExt(B, bi, i64, "");
            }
            if (suffix)
                set_flags(r, ai, bi);
            if (dst.k != O_NONE)
                store_int(dst, r);
            continue;
        }

        if (!strcmp(op, "cmp")) {
            if (jid < 0)
                DIE("cmp without jump id");
            LLVMValueRef c = cmp_cond(args[0], opnd_int(parse_opnd(args[1])), opnd_int(parse_opnd(args[2])));
            LLVMBasicBlockRef next = LLVMAppendBasicBlockInContext(C, F, "");
            LLVMBuildCondBr(B, c, get_label(jump_target[jid]), next);
            LLVMPositionBuilderAtEnd(B, next);
            continue;
        }
        if (!strcmp(op, "jump")) {
            if (jid < 0)
                DIE("jump without jump id");
            LLVMBasicBlockRef target = get_label(jump_target[jid]);
            if (!strcmp(args[0], "jump")) {
                LLVMBuildBr(B, target);
                fresh();
            } else if (!strcmp(args[0], "fast_call")) {
                LLVMBasicBlockRef cont = LLVMAppendBasicBlockInContext(C, F, "cont");
                LLVMBuildStore(B, K(new_address(cont)), retaddr);
                LLVMBuildBr(B, target);
                LLVMPositionBuilderAtEnd(B, cont);
            } else {
                LLVMBasicBlockRef next = LLVMAppendBasicBlockInContext(C, F, "");
                LLVMBuildCondBr(B, flag_cond(args[0]), target, next);
                LLVMPositionBuilderAtEnd(B, next);
            }
            continue;
        }
        if (!strcmp(op, "fast_enter")) {
            store_int(parse_opnd(args[0]), LLVMBuildLoad2(B, i64, retaddr, ""));
            continue;
        }
        if (!strcmp(op, "fast_return") || !strcmp(op, "ijump")) {
            dispatch(opnd_int(parse_opnd(args[0])));
            continue;
        }
        if (!strcmp(op, "mov_addr")) {
            if (jid < 1000000)
                DIE("mov_addr without jump id");
            store_int(parse_opnd(args[0]), K(new_address(get_label(addr_target[jid - 1000000]))));
            continue;
        }
        if (!strcmp(op, "local_base")) {
            LLVMValueRef idx = K(parse_opnd(args[1]).imm);
            store_word(parse_opnd(args[0]), LLVMBuildGEP2(B, i8, locals, &idx, 1, ""));
            continue;
        }
        if (!strcmp(op, "icall")) {
            int nargs = 1;
            for (char *p = strchr(args[1], '['); *p; p++)
                if (*p == ',')
                    nargs++;
            opnd target = parse_opnd(args[n - 1]);
            if (target.k != O_IMM)
                DIE("icall target");
            sym *s = find_sym((uint64_t)target.imm);
            LLVMTypeRef params[4] = { ptr, ptr, ptr, ptr };
            LLVMTypeRef fty = LLVMFunctionType(ptr, params, (unsigned)nargs, false);
            if (!s->g)
                s->g = LLVMAddFunction(M, s->name, fty);
            LLVMValueRef argv[4];
            for (int k = 0; k < nargs; k++)
                argv[k] = reg_ptr(k);
            LLVMBuildStore(B, LLVMBuildCall2(B, fty, s->g, argv, (unsigned)nargs, ""), regs[0]);
            continue;
        }
        if (!strcmp(op, "return")) {
            LLVMBuildRet(B, LLVMBuildTrunc(B, opnd_int(parse_opnd(args[0])), i32, ""));
            fresh();
            continue;
        }
        DIE("unhandled LIR op: %s (line %d: %s)", op, i + 1, lines[i]);
    }

    for (int s = 0; s < nswitches; s++)
        for (int k = 0; k < ncases; k++)
            LLVMAddCase(switches[s], K(k + 1), cases[k]);

    unsigned count = 0;
    for (LLVMBasicBlockRef bb = LLVMGetFirstBasicBlock(F); bb; bb = LLVMGetNextBasicBlock(bb)) {
        if (!LLVMGetBasicBlockTerminator(bb)) {
            LLVMPositionBuilderAtEnd(B, bb);
            LLVMBuildUnreachable(B);
        }
        for (LLVMValueRef in = LLVMGetFirstInstruction(bb); in; in = LLVMGetNextInstruction(in))
            count++;
    }
    return count;
}

/* ---- running the compiled matcher: mirrors pcre2_jit_match ---- */

static int replay_match(jit_function fn, struct sljit_stack *stack, const pcre2_code *code, PCRE2_SPTR subject,
                        PCRE2_SIZE length, PCRE2_SIZE start_offset, uint32_t options, pcre2_match_data *md)
{
    pcre2_real_code *re = (pcre2_real_code *)code;
#ifdef STATIC_ARGS
    static jit_arguments a;
#else
    jit_arguments a;
#endif
    uint32_t oveccount = md->oveccount, max_oveccount = re->top_bracket + 1;
    a.str = subject + start_offset;
    a.begin = subject;
    a.end = subject + length;
    a.match_data = md;
    a.startchar_ptr = subject;
    a.mark_ptr = NULL;
    a.options = options;
    a.callout = NULL;
    a.callout_data = NULL;
    a.offset_limit = PCRE2_UNSET;
    a.limit_match = MATCH_LIMIT < re->limit_match ? MATCH_LIMIT : re->limit_match;
    if (oveccount > max_oveccount)
        oveccount = max_oveccount;
    a.oveccount = oveccount << 1;
    stack->start = stack->min_start;
    stack->top = stack->end;
    a.stack = stack;
    int rc = fn(&a);
    if (rc > (int)oveccount)
        rc = 0;
    md->code = re;
    md->subject = subject;
    md->subject_length = length;
    md->start_offset = start_offset;
    md->rc = rc;
    md->startchar = (PCRE2_SIZE)(a.startchar_ptr - subject);
    md->mark = a.mark_ptr;
    md->options = options;
    return rc;
}

static bool trace;
typedef struct { unsigned long calls, matches, sum, passes; double ns_per_call; } result;

static result bench(jit_function fn, struct sljit_stack *stack, pcre2_code *re, const char *subj, size_t len,
                    pcre2_match_data *md, double budget)
{
    result r = { 0, 0, 0, 0, 0 };
    double t0 = now(), t1;
    do {
        for (int it = 0; it < 20; it++) {
            size_t off = 0;
            r.passes++;
            for (;;) {
                int rc = fn ? replay_match(fn, stack, re, (PCRE2_SPTR)subj, len, off, 0, md)
                            : pcre2_match(re, (PCRE2_SPTR)subj, len, off, 0, md, NULL);
                r.calls++;
                if (trace && r.passes == 1 && r.calls < 6)
                    fprintf(stderr, "%s off=%zu rc=%d ov=%zu,%zu\n", fn ? "jit" : "interp", off, rc,
                            pcre2_get_ovector_pointer(md)[0], pcre2_get_ovector_pointer(md)[1]);
                if (rc < 0)
                    break;
                PCRE2_SIZE *ov = pcre2_get_ovector_pointer(md);
                r.matches++;
                r.sum += ov[0] * 31 + ov[1];
                off = ov[1] > ov[0] ? ov[1] : ov[1] + 1;
                if (off > len)
                    break;
            }
        }
        t1 = now();
    } while (t1 - t0 < budget);
    r.ns_per_call = (t1 - t0) * 1e9 / (double)r.calls;
    return r;
}

static jit_function build_and_compile(char **lines, int nlines, const char *opt, int argc, char **argv,
                                      unsigned *instsp, double *build_ms, double *compile_ms)
{
    double t0 = now();
    C = LLVMContextCreate();
    M = LLVMModuleCreateWithNameInContext("pcre2", C);
    B = LLVMCreateBuilderInContext(C);
    i8 = LLVMInt8TypeInContext(C);
    i16 = LLVMInt16TypeInContext(C);
    i32 = LLVMInt32TypeInContext(C);
    i64 = LLVMInt64TypeInContext(C);
    ptr = LLVMPointerTypeInContext(C, 0);
    unsigned insts = translate(lines, nlines);
    *instsp = insts;
    double t1 = now();
    if (argc > 4 && !strcmp(argv[4], "dump"))
        LLVMDumpModule(M);

    FilLLVMJITRef jit = FilLLVMJIT_Create();
    FilLLVMJIT_SetOption(jit, "opt-level", opt);
    for (int i = 5; i < argc; i++) {
        char *eq = strchr(argv[i], '=');
        if (eq) {
            *eq = 0;
            FilLLVMJIT_SetOption(jit, argv[i], eq + 1);
        }
    }
    for (int i = 0; i < nsyms; i++)
        if (syms[i].g)
            FilLLVMJIT_SetGlobalMapping(jit, syms[i].name, syms[i].host);
    FilLLVMJITModuleRef compiled = FilLLVMJIT_CompileModule(jit, M);
    if (!compiled)
        DIE("JIT compile failed");
    jit_function fn = (jit_function)FilLLVMJIT_GetPointerToGlobal(compiled, "match");
    double t2 = now();
    ZASSERT(fn);

    *build_ms = (t1 - t0) * 1e3;
    *compile_ms = (t2 - t1) * 1e3;
    return fn;
}

int main(int argc, char **argv)
{
    if (argc < 2)
        DIE("usage: replay PATTERN-NAME [opt-level] [budget] [dump] [KEY=VALUE jit options...]");
    const char *want = argv[1];
    trace = getenv("REPLAY_TRACE") != NULL;
    const char *opt = argc > 2 ? argv[2] : "2";
    double budget = argc > 3 ? atof(argv[3]) : 0.3;

    size_t reps = 8, hl = sizeof(html) - 1;
    char *big = malloc(hl * reps + 1);
    for (size_t i = 0; i < reps; i++)
        memcpy(big + i * hl, html, hl);
    big[hl * reps] = 0;

    const struct pat *pat = NULL;
    for (size_t p = 0; p < sizeof(pats) / sizeof(pats[0]); p++)
        if (!strcmp(pats[p].name, want))
            pat = &pats[p];
    if (!pat)
        DIE("no pattern %s", want);

    int err;
    PCRE2_SIZE eo;
    pcre2_code *code = pcre2_compile((PCRE2_SPTR)pat->re, PCRE2_ZERO_TERMINATED, pat->opts, &err, &eo, NULL);
    ZASSERT(code);
    pcre2_real_code *re = (pcre2_real_code *)code;

    /* Read the LIR dump. */
    char path[256];
    snprintf(path, sizeof path, "lir/%s.txt", want);
    FILE *f = fopen(path, "r");
    if (!f)
        DIE("cannot open %s", path);
    static char *lines[20000];
    int nlines = 0;
    char lb[4096];
    while (fgets(lb, sizeof lb, f)) {
        lb[strcspn(lb, "\n")] = 0;
        lines[nlines++] = strdup(lb);
    }
    fclose(f);

    for (int i = 0; i < nlines; i++) {
        char name[40];
        unsigned long base, size;
        if (sscanf(lines[i], "SYM %39s %lu %lu", name, &base, &size) == 3) {
            sym *s = &syms[nsyms++];
            memset(s, 0, sizeof *s);
            snprintf(s->name, sizeof s->name, "%s", name);
            s->base = base;
            s->size = size;
            if (!strcmp(name, "re")) {
                if (size != re->blocksize)
                    DIE("pattern block size differs: native %lu, here %zu", size, re->blocksize);
                s->host = re;
            } else if (!strcmp(name, "tables"))
                s->host = (void *)re->tables;
            else if (!strcmp(name, "ucd_stage1"))
                s->host = (void *)PRIV(ucd_stage1);
            else if (!strcmp(name, "ucd_stage2"))
                s->host = (void *)PRIV(ucd_stage2);
            else if (!strcmp(name, "ucd_records"))
                s->host = (void *)PRIV(ucd_records);
            else if (!strcmp(name, "ucd_caseless_sets"))
                s->host = (void *)PRIV(ucd_caseless_sets);
            else if (!strcmp(name, "ucd_boolprop_sets"))
                s->host = (void *)PRIV(ucd_boolprop_sets);
            else if (!strcmp(name, "ucd_script_sets"))
                s->host = (void *)PRIV(ucd_script_sets);
            else if (!strcmp(name, "utf8_table4_m0xc0")) {
                s->host = (void *)PRIV(utf8_table4);
                s->bias = -0xc0;
            } else if (!strcmp(name, "fn_stack_resize")) {
                s->host = stack_resize;
                s->is_fn = true;
            } else if (!strncmp(name, "fn_", 3)) {
                s->host = unsupported_call;
                s->is_fn = true;
            } else if (!strncmp(name, "rodata", 6))
                s->host = malloc(size);
            else
                DIE("symbol %s", name);
        }
        char hex[2100];
        if (sscanf(lines[i], "RODATA %39s %2099s", name, hex) == 2)
            for (int k = 0; k < nsyms; k++)
                if (!strcmp(syms[k].name, name))
                    for (size_t b = 0; b < syms[k].size; b++) {
                        unsigned v;
                        sscanf(hex + 2 * b, "%2x", &v);
                        ((uint8_t *)syms[k].host)[b] = (uint8_t)v;
                    }
    }

    unsigned insts;
    double build_ms, compile_ms;
    if (getenv("REPLAY_CACHE")) {
        /* A forked sibling compiles first; this process should then link its object. */
        ZASSERT(!FilLLVMJIT_EnableSharedObjectCache((size_t)64 << 20));
        pid_t pid = fork();
        if (!pid) {
            build_and_compile(lines, nlines, opt, argc, argv, &insts, &build_ms, &compile_ms);
            _exit(0);
        }
        int status;
        waitpid(pid, &status, 0);
        ZASSERT(WIFEXITED(status) && !WEXITSTATUS(status));
    }
    jit_function fn = build_and_compile(lines, nlines, opt, argc, argv, &insts, &build_ms, &compile_ms);
    if (getenv("REPLAY_CACHE"))
        printf("shared object cache hits: %llu\n", FilLLVMJIT_SharedObjectCacheHits());

    struct sljit_stack stack;
    size_t stack_size = 32768;
    stack.min_start = malloc(stack_size);
    stack.start = stack.min_start;
    stack.end = stack.top = stack.min_start + stack_size;

    const char *subj = pat->subject ? pat->subject : big;
    size_t len = strlen(subj);
    pcre2_match_data *md = pcre2_match_data_create_from_pattern(code, NULL);
    result interp = bench(NULL, NULL, code, subj, len, md, budget);
    result jitted = bench(fn, &stack, code, subj, len, md, budget);
    bool same = interp.calls / interp.passes == jitted.calls / jitted.passes
        && interp.sum / interp.passes == jitted.sum / jitted.passes;
    printf("%-10s O%s lir_lines=%-4d ir_insts=%-5u build_ms=%-6.2f compile_ms=%-7.1f interp_ns=%-9.1f jit_ns=%-9.1f "
           "speedup=%-5.2f calls/pass=%lu sum=%lu %s\n",
           want, opt, nlines, insts, build_ms, compile_ms, interp.ns_per_call, jitted.ns_per_call,
           interp.ns_per_call / jitted.ns_per_call, jitted.calls / jitted.passes, jitted.sum / jitted.passes,
           same ? "RESULTS-MATCH" : "RESULTS-DIFFER");
    if (!same)
        printf("  interp: calls/pass=%lu sum=%lu\n", interp.calls / interp.passes, interp.sum / interp.passes);
    return same ? 0 : 2;
}
