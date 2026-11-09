/* Print what rx.pl reads, as Prolog terms: the opcode numbering of the
   PCRE2 this is compiled against, then for each pattern of pats.h and
   more.h what pcre2_compile made of it.

       ops([end, bol, x('\\G'), ...]).
       rx(NAME, [groups(N), dollar(eol), unsupported([]), start(S)], [BYTE, ...]).

   ops/1 names opcode 0, 1, 2, ... in rx.pl's terms, with x(NAME) for the
   ones rx.pl does not compile, so rx.pl holds no opcode numbers and
   follows whatever PCRE2 release this is built with. rx/3 carries what
   the matcher needs from pcre2_real_code, with the option and flag bits
   already read, and the bytecode.

   This stands in for the few lines inside libpcre2 that would hand a
   compiled pattern to the regex compiler. */
#include "config.h"
#define PCRE2_CODE_UNIT_WIDTH 8
#include "pcre2_internal.h"
#include <stdio.h>
#include <string.h>

#include "pats.h"

#include "more.h"

static const char *const display[] = { OP_NAME_LIST };
static const char *names[OP_TABLE_LENGTH];
static char repeats[5 * 13][40];
static char others[OP_TABLE_LENGTH][40];

/* The thirteen repeats of a single character, in the order every set of
   them has. `n` is a count that follows the opcode. */
static const char *const kinds[13] = {
    "0,inf,greedy", "0,inf,lazy", "1,inf,greedy", "1,inf,lazy",   "0,1,greedy",     "0,1,lazy",     "0,n,greedy",
    "0,n,lazy",     "n,n,greedy", "0,inf,possessive", "1,inf,possessive", "0,1,possessive", "0,n,possessive",
};

static void name_ops(void)
{
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
    /* The rest are x('NAME'), with the name pcre2test -b prints. */
    for (int i = 0; i < OP_TABLE_LENGTH; i++) {
        char *o = others[i];
        o += sprintf(o, "x('");
        for (const char *c = display[i]; *c && o < others[i] + sizeof others[i] - 5; c++) {
            if (*c == '\\' || *c == '\'')
                *o++ = '\\';
            *o++ = *c;
        }
        strcpy(o, "')");
        names[i] = others[i];
    }
    for (size_t i = 0; i < sizeof ops / sizeof ops[0]; i++)
        names[ops[i].op] = ops[i].name;
    for (int s = 0; s < 5; s++)
        for (int k = 0; k < 13; k++) {
            char *name = repeats[s * 13 + k];
            snprintf(name, sizeof repeats[0], "rep(%s,%s)", sets[s].set, kinds[k]);
            names[sets[s].first + k] = name;
        }
}

/* The options and flags that change what the bytecode means in ways
   rx.pl does not implement. */
static void unsupported(const pcre2_real_code *re)
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
    const char *sep = "";
    for (size_t i = 0; i < sizeof options / sizeof options[0]; i++)
        if (re->overall_options & options[i].bit)
            printf("%s%s", sep, options[i].name), sep = ",";
    for (size_t i = 0; i < sizeof flags / sizeof flags[0]; i++)
        if (re->flags & flags[i].bit)
            printf("%s%s", sep, flags[i].name), sep = ",";
    if (re->newline_convention != PCRE2_NEWLINE_LF)
        printf("%snewline", sep), sep = ",";
    if (re->tables != PRIV(default_tables))
        printf("%stables", sep), sep = ",";
    if (LINK_SIZE != 2)
        printf("%slink_size", sep);
}

static void dump(const struct pat *p)
{
    int err;
    PCRE2_SIZE eo;
    pcre2_code *code = pcre2_compile((PCRE2_SPTR)p->re, PCRE2_ZERO_TERMINATED, p->opts, &err, &eo, NULL);
    if (!code) {
        printf("%% %s: does not compile\n", p->name);
        return;
    }
    const pcre2_real_code *re = (const pcre2_real_code *)code;
    const uint8_t *bytes = (const uint8_t *)re + re->code_start;
    size_t n = re->blocksize - re->code_start;
    printf("rx(%s, [groups(%u), dollar(%s), unsupported([", p->name, re->top_bracket,
           re->overall_options & PCRE2_DOLLAR_ENDONLY ? "eod" : "eol");
    unsupported(re);
    /* Where a match can start, as pcre2_match reads it. */
    printf("]), start(");
    if (re->overall_options & PCRE2_ANCHORED)
        printf("anchored");
    else if (re->flags & PCRE2_FIRSTSET)
        printf("first(%u,%s)", re->first_codeunit, re->flags & PCRE2_FIRSTCASELESS ? "caseless" : "exact");
    else if (re->flags & PCRE2_FIRSTMAPSET) {
        printf("bitmap([");
        for (int i = 0; i < 32; i++)
            printf("%s%u", i ? "," : "", re->start_bitmap[i]);
        printf("])");
    } else
        printf("any");
    printf(")], [");
    for (size_t i = 0; i < n; i++)
        printf("%s%u", i ? "," : "", bytes[i]);
    printf("]).\n");
    pcre2_code_free(code);
}

int main(void)
{
    name_ops();
    printf("ops([");
    for (int i = 0; i < OP_TABLE_LENGTH; i++)
        printf("%s%s", i ? ", " : "", names[i]);
    printf("]).\n");
    for (size_t i = 0; i < sizeof pats / sizeof pats[0]; i++)
        dump(&pats[i]);
    for (size_t i = 0; i < sizeof more / sizeof more[0]; i++)
        dump(&more[i]);
}
