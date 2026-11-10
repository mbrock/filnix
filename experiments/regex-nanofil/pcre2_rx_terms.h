/* What rx.pl reads, as Prolog terms: the opcode numbering of the PCRE2
   this is compiled with, and what pcre2_compile made of one pattern.

       ops([end, bol, x('\\G'), ...]).
       rx(NAME, [groups(N), dollar(eol), unsupported([]), start(S)], [BYTE, ...]).

   ops/1 names opcode 0, 1, 2, ... in rx.pl's terms, with x(NAME) for the
   ones rx.pl does not compile, so rx.pl holds no opcode numbers and
   follows whatever PCRE2 release this is built with. rx/3 carries what
   the matcher needs from pcre2_real_code, with the option and flag bits
   already read, and the bytecode.

   Include it after pcre2_internal.h. dump.c prints these terms for the
   test patterns; pcre2_rx_inc.h, inside libpcre2, writes them for the
   pattern pcre2_jit_compile was given. Nothing here keeps state, so
   threads may write terms at the same time. */
#include <stdio.h>

static const char *const rx_display[] = { OP_NAME_LIST };

/* The name of an opcode in rx.pl's terms. */
static void rx_write_op(FILE *f, int op)
{
    /* The thirteen repeats of a single character, in the order every set
       of them has. `n` is a count that follows the opcode. */
    static const char *const kinds[13] = {
        "0,inf,greedy", "0,inf,lazy", "1,inf,greedy",     "1,inf,lazy",       "0,1,greedy",     "0,1,lazy",      "0,n,greedy",
        "0,n,lazy",     "n,n,greedy", "0,inf,possessive", "1,inf,possessive", "0,1,possessive", "0,n,possessive",
    };
    static const struct {
        int first;
        const char *set;
    } sets[5] = {
        { OP_STAR, "char" }, { OP_STARI, "chari" }, { OP_NOTSTAR, "not" }, { OP_NOTSTARI, "noti" }, { OP_TYPESTAR, "type" },
    };
    static const struct {
        int op;
        const char *name;
    } ops[] = {
        { OP_END, "end" },
        { OP_SOD, "bol" },
        { OP_CIRC, "bol" },
        { OP_CIRCM, "mbol" },
        { OP_DOLL, "doll" },
        { OP_EODN, "eol" },
        { OP_EOD, "eod" },
        { OP_DOLLM, "meol" },
        { OP_NOT_WORD_BOUNDARY, "wordb(no)" },
        { OP_WORD_BOUNDARY, "wordb(yes)" },
        { OP_NOT_DIGIT, "type(digit,no)" },
        { OP_DIGIT, "type(digit,yes)" },
        { OP_NOT_WHITESPACE, "type(space,no)" },
        { OP_WHITESPACE, "type(space,yes)" },
        { OP_NOT_WORDCHAR, "type(word,no)" },
        { OP_WORDCHAR, "type(word,yes)" },
        { OP_ANY, "type(newline,no)" },
        { OP_ALLANY, "type(none,no)" },
        { OP_FAIL, "type(none,yes)" },
        { OP_CHAR, "char" },
        { OP_CHARI, "chari" },
        { OP_NOT, "not" },
        { OP_NOTI, "noti" },
        { OP_CLASS, "class" },
        { OP_NCLASS, "class" },
        { OP_CRSTAR, "crep(0,inf,greedy)" },
        { OP_CRMINSTAR, "crep(0,inf,lazy)" },
        { OP_CRPLUS, "crep(1,inf,greedy)" },
        { OP_CRMINPLUS, "crep(1,inf,lazy)" },
        { OP_CRQUERY, "crep(0,1,greedy)" },
        { OP_CRMINQUERY, "crep(0,1,lazy)" },
        { OP_CRRANGE, "crange(greedy)" },
        { OP_CRMINRANGE, "crange(lazy)" },
        { OP_CRPOSSTAR, "crep(0,inf,possessive)" },
        { OP_CRPOSPLUS, "crep(1,inf,possessive)" },
        { OP_CRPOSQUERY, "crep(0,1,possessive)" },
        { OP_CRPOSRANGE, "crange(possessive)" },
        { OP_ALT, "alt" },
        { OP_KET, "ket(single)" },
        { OP_KETRMAX, "ket(greedy)" },
        { OP_KETRMIN, "ket(lazy)" },
        { OP_KETRPOS, "ket(possessive)" },
        { OP_REVERSE, "reverse" },
        { OP_ASSERT, "bra(look(pos))" },
        { OP_ASSERT_NOT, "bra(look(neg))" },
        { OP_ASSERTBACK, "bra(look(pos))" },
        { OP_ASSERTBACK_NOT, "bra(look(neg))" },
        { OP_ONCE, "bra(once)" },
        { OP_BRA, "bra(plain)" },
        { OP_SBRA, "bra(plain)" },
        { OP_BRAPOS, "bra(plain)" },
        { OP_SBRAPOS, "bra(plain)" },
        { OP_CBRA, "bra(capture)" },
        { OP_SCBRA, "bra(capture)" },
        { OP_CBRAPOS, "bra(capture)" },
        { OP_SCBRAPOS, "bra(capture)" },
        { OP_BRAZERO, "zero(greedy)" },
        { OP_BRAMINZERO, "zero(lazy)" },
        { OP_BRAPOSZERO, "zero(possessive)" },
        { OP_SKIPZERO, "zero(skip)" },
    };
    for (int s = 0; s < 5; s++)
        if (op >= sets[s].first && op < sets[s].first + 13) {
            fprintf(f, "rep(%s,%s)", sets[s].set, kinds[op - sets[s].first]);
            return;
        }
    for (size_t i = 0; i < sizeof ops / sizeof ops[0]; i++)
        if (ops[i].op == op) {
            fputs(ops[i].name, f);
            return;
        }
    /* The rest are x('NAME'), with the name pcre2test -b prints. */
    fputs("x('", f);
    for (const char *c = rx_display[op]; *c; c++) {
        if (*c == '\\' || *c == '\'')
            fputc('\\', f);
        fputc(*c, f);
    }
    fputs("')", f);
}

static void rx_write_ops(FILE *f)
{
    fputs("ops([", f);
    for (int i = 0; i < OP_TABLE_LENGTH; i++) {
        if (i)
            fputs(", ", f);
        rx_write_op(f, i);
    }
    fputs("]).\n", f);
}

/* The options and flags that change what the bytecode means in ways
   rx.pl does not implement: how many are set. With a stream, their
   names, separated by commas. */
static int rx_unsupported(FILE *f, const pcre2_real_code *re)
{
    static const struct {
        uint32_t bit;
        const char *name;
    } options[] = {
        { PCRE2_UTF, "utf" },
        { PCRE2_UCP, "ucp" },
        { PCRE2_FIRSTLINE, "firstline" },
        { PCRE2_ENDANCHORED, "endanchored" },
        { PCRE2_ALT_CIRCUMFLEX, "alt_circumflex" },
        { PCRE2_MATCH_INVALID_UTF, "match_invalid_utf" },
    }, flags[] = {
        { PCRE2_NOTEMPTY_SET, "notempty" },
        { PCRE2_NE_ATST_SET, "notempty_atstart" },
    };
    const char *found[16];
    int n = 0;
    for (size_t i = 0; i < sizeof options / sizeof options[0]; i++)
        if (re->overall_options & options[i].bit)
            found[n++] = options[i].name;
    for (size_t i = 0; i < sizeof flags / sizeof flags[0]; i++)
        if (re->flags & flags[i].bit)
            found[n++] = flags[i].name;
    if (re->newline_convention != PCRE2_NEWLINE_LF)
        found[n++] = "newline";
    if (re->tables != PRIV(default_tables))
        found[n++] = "tables";
    if (LINK_SIZE != 2)
        found[n++] = "link_size";
    for (int i = 0; f && i < n; i++)
        fprintf(f, "%s%s", i ? "," : "", found[i]);
    return n;
}

static void rx_write_pattern(FILE *f, const char *name, const pcre2_real_code *re)
{
    const uint8_t *bytes = (const uint8_t *)re + re->code_start;
    size_t n = re->blocksize - re->code_start;
    fprintf(f, "rx(%s, [groups(%u), dollar(%s), unsupported([", name, re->top_bracket,
            re->overall_options & PCRE2_DOLLAR_ENDONLY ? "eod" : "eol");
    rx_unsupported(f, re);
    /* Where a match can start, as pcre2_match reads it. */
    fputs("]), start(", f);
    if (re->overall_options & PCRE2_ANCHORED)
        fputs("anchored", f);
    else if (re->flags & PCRE2_FIRSTSET)
        fprintf(f, "first(%u,%s)", re->first_codeunit, re->flags & PCRE2_FIRSTCASELESS ? "caseless" : "exact");
    else if (re->flags & PCRE2_FIRSTMAPSET) {
        fputs("bitmap([", f);
        for (int i = 0; i < 32; i++)
            fprintf(f, "%s%u", i ? "," : "", re->start_bitmap[i]);
        fputs("])", f);
    } else
        fputs("any", f);
    fputs(")], [", f);
    for (size_t i = 0; i < n; i++)
        fprintf(f, "%s%u", i ? "," : "", bytes[i]);
    fputs("]).\n", f);
}
