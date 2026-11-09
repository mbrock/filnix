/* Patterns that bench.c only checks against PCRE2's interpreter. They
   cover what pcre2_compile emits beyond the ten of pats.h: atomic and
   possessive groups, lookbehind, multiline and dotall, counted and lazy
   group loops, loops whose body can match nothing, captures that
   backtracking must undo, and inline options. */
static const char letters[] = "abcd abd aab b abcabcd ac aaab aac b xyz abab cab bcd d\nab\n\nabd\n";

static const struct pat more[] = {
    { "once", "<(?>[a-z]+|/)(\\s|>)", 0, NULL },
    { "once2", "(?>ab|a)(?>b?)c", 0, letters },
    { "behind", "(?<=<)\\w+", 0, NULL },
    { "behind2", "(?<![\\w.])(?<!ab|x)\\d+(?!\\d)", 0, NULL },
    { "mline", "^<(\\w+)|;$", PCRE2_MULTILINE, NULL },
    { "mline2", "^(a?b)*$", PCRE2_MULTILINE, letters },
    { "dotall", "<!--.*?-->", PCRE2_DOTALL, NULL },
    { "dot", "s.c.*", 0, NULL },
    { "ends", "\\A<div|\\d\\Z|\\n\\z", 0, NULL },
    { "lazygrp", "<p(?:\\s\\w+=\"[^\"]*\")+?>|(?:\\w+ )+?the", 0, NULL },
    { "lazygrp2", "(?:(a)|b)*?c(d)?", 0, letters },
    { "emptyit", "(\\w*)*>|(?:\\d*|x)+;", 0, NULL },
    { "emptyit2", "(a*)*b|(?:a|())+?c|(?:b?)*?d", 0, letters },
    { "posgrp", "(?:\\w+\\s)*+\\w+;|(\\d+,)++\\d", 0, NULL },
    { "posgrp2", "(?:a|ab)*+c|(b|a)++d", 0, letters },
    { "counted", "(\\d{1,3},){2}\\d+|(?:[a-z]+ ){2,4}fox|x(?:yz){0}\\w", 0, NULL },
    { "counted2", "(a|ab){1,3}(c|bcd){0,2}?(d*)", 0, letters },
    { "optgrp", "(https?://)?((\\w+)\\.)+(com|jpg)", 0, NULL },
    { "nocase", "LOREM\\s+I+PSUM|[^A]+?B|X{0}D{1,2}?O", PCRE2_CASELESS, NULL },
    { "ranges", "[a-f0-9]{2,4}?\\b|[0-9]{3,}+|[^<]{3,5}?<|a{2}b{0,2}+", 0, NULL },
    { "topalt", "fox|dog|<img|", 0, NULL },
    { "nested", "((a|b)(c)?)+d|((a)|(b))+\\s", 0, letters },
    { "fail", "a(?!)|b(?=c)|\\Bc\\b", 0, letters },
    { "neglook", "(?!(a)b)\\w|a(b)", 0, letters },
    { "poslook", "(?=(a))ab(?!c)|a(b)c", 0, letters },
    { "inline", "(?<w>a(?i)B)C|(?s:d.a)|(?m:^a)b", 0, letters },
    { "endonly", "\\n$|^a", PCRE2_DOLLAR_ENDONLY, letters },
    { "backref", "(a)\\1", 0, letters },
};
