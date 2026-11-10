#!/usr/bin/env python3
"""cases.py OUTDIR: write the adversarial IR texts into OUTDIR/NAME.ir.

Most cases are one clause `context(a, X).` with the form under test as
X; the others are whole files. tests/read.sh holds the reader
(IrText.v) to Prolog on them, and refused.txt names the ones the
reader refuses and Prolog reads."""
import os, sys

out = sys.argv[1]
os.makedirs(out, exist_ok=True)

cases = []


def b(x):
    return x if isinstance(x, bytes) else x.encode("utf-8")


def arg(name, x):
    """X as the second argument of a context/2 clause."""
    cases.append((name, b"context(a, " + b(x) + b").\n"))


def whole(name, x):
    cases.append((name, b(x)))


# --- escapes, in a quoted atom and in a string
for e, n in [("a", "a"), ("b", "b"), ("f", "f"), ("n", "n"), ("r", "r"), ("t", "t"), ("v", "v"),
             ("\\", "backslash"), ("'", "squote"), ('"', "dquote"), ("`", "backquote"),
             ("e", "e"), ("s", "s"), ("z", "z"), ("0", "0-alone"), (" ", "space"), ("\n", "newline"),
             ("c", "c"), ("d", "d"), ("u0041", "u4"), ("U00000041", "u8"), ("8\\", "8"), ("9", "9"),
             ("0\\", "oct0"), ("1\\", "oct1"), ("101\\", "oct101"), ("00000101\\", "oct8digits"),
             ("000000101\\", "oct9digits"), ("777\\", "oct777"), ("18\\", "oct18"),
             ("4177777\\", "oct-max"), ("4200000\\", "oct-over"), ("101", "oct-unclosed"),
             ("x41\\", "hex41"), ("x00000041\\", "hex8digits"), ("x000000041\\", "hex9digits"),
             ("xe9\\", "hex-e9"), ("xE9\\", "hex-E9"), ("x80\\", "hex80"), ("xff\\", "hexff"),
             ("x0\\", "hex0"), ("x7f\\", "hex7f"), ("x1\\", "hex1"), ("x1b\\", "hex1b"),
             ("x100\\", "hex100"), ("x7FF\\", "hex7ff"), ("x800\\", "hex800"),
             ("xFFFD\\", "hexfffd"), ("xFFFE\\", "hexfffe"), ("xFFFF\\", "hexffff"),
             ("x10000\\", "hex10000"), ("x1F600\\", "hex1f600"), ("x10FFFF\\", "hex10ffff"),
             ("x110000\\", "hex110000"), ("xD7FF\\", "hexd7ff"), ("xD800\\", "hexd800"),
             ("xDFFF\\", "hexdfff"), ("xE000\\", "hexe000"), ("x\\", "hex-empty"),
             ("x41", "hex-unclosed"), ("x4G\\", "hex-bad"), ("x41g\\", "hex-bad2"),
             ("xFFFFFFFF\\", "hex-ffffffff"), ("x200B\\", "hex200b"), ("x85\\", "hex85"),
             ("xAD\\", "hexad"), ("x2028\\", "hex2028"), ("xFEFF\\", "hexfeff"),
             ("x300\\", "hex300"), ("xA0\\", "hexa0")]:
    arg("esc-atom-" + n, "'p\\" + e + "q'")
    arg("esc-str-" + n, '"p\\' + e + 'q"')

# --- quotes
for n, x in [("dq-atom", "'a''b'"), ("dq-str", '"a""b"'), ("dq-atom-only", "''''"), ("dq-str-only", '""""'),
             ("empty-atom", "''"), ("empty-str", '""'), ("dquote-in-atom", "'\"'"), ("squote-in-str", '"\'"'),
             ("backquote-in-atom", "'`'"), ("backquote-in-str", '"`"'), ("dq-atom-end", "'a'''"),
             ("dq-atom-start", "'''a'"), ("two-dq-in-atom", "'\"\"'"), ("two-sq-in-str", '"\'\'"'),
             ("nl-in-atom", "'a\nb'"), ("nl-in-str", '"a\nb"'), ("tab-in-atom", "'a\tb'"),
             ("tab-in-str", '"a\tb"'), ("cr-in-atom", "'a\rb'"), ("del-in-atom", "'a\x7fb'"),
             ("ctl-in-atom", "'a\x01b'"), ("ctl-in-str", '"a\x01b"'), ("nul-in-atom", "'a\x00b'"),
             ("stop-in-atom", "'a. b'"), ("stop-end-atom", "'a.'"), ("stop-in-str", '"a. b"'),
             ("stop-nl-in-str", '"a.\\n"'), ("percent-in-atom", "'a%b'"), ("comment-in-atom", "'a/*b*/c'"),
             ("percent-in-str", '"a%b"'), ("all-printing-atom", "'" + "".join(chr(c) for c in range(32, 127) if chr(c) not in "'\\") + "'"),
             ("all-printing-str", '"' + "".join(chr(c) for c in range(32, 127) if chr(c) not in '"\\') + '"'),
             ("unclosed-atom", "'abc"), ("unclosed-str", '"abc'), ("backquoted", "`abc`"),
             ("atom-atom", "'a' 'b'"), ("atom-name", "'a'b"), ("name-atom", "a'b'"), ("name-str", 'a"b"'),
             ("str-str", '"a" "b"'), ("str-app", '"ab"(c)'), ("atom-app", "'f'(a)"), ("atom-sp-app", "'f' (a)"),
             ("atom-upper", "'A'"), ("atom-upper-app", "'Abc'(x)"), ("atom-underscore", "'_'"),
             ("atom-digits", "'123'"), ("atom-neg", "'-1'"), ("str-digits", '"12"'), ("str-space", '" "'),
             ("atom-space", "' '"), ("atom-brackets", "'[]'"), ("atom-brackets-app", "'[]'(a)"),
             ("atom-braces", "'{}'"), ("atom-braces-app", "'{}'(a)"), ("atom-bar", "'[|]'"),
             ("atom-bar-app", "'[|]'(a, b)"), ("atom-bar-app-list", "'[|]'(a, [])"), ("atom-dot", "'.'"),
             ("atom-dot-app", "'.'(a, b)"), ("atom-dot-app1", "'.'(a)"), ("atom-var", "'$VAR'(1)"),
             ("atom-var-name", "'$VAR'('X')"), ("atom-var-atom", "'$VAR'"), ("atom-eof", "'end_of_file'"),
             ("eof-arg", "end_of_file"), ("atom-comma", "','"), ("atom-comma-app", "','(a, b)"),
             ("atom-bar1", "'|'"), ("atom-bar1-app", "'|'(a, b)"), ("atom-minus-app", "'-'(a, b)"),
             ("atom-minus-app1", "'-'(1)"), ("atom-minus", "'-'"), ("atom-empty-app", "''(a)"),
             ("atom-dict", "'dict'(a, b)"), ("atom-nl-name", "'\\n'(a)")]:
    arg("quote-" + n, x)

# --- UTF-8
for n, x in [("atom-2", "'é'"), ("str-2", '"é"'), ("atom-3", "'€'"), ("str-3", '"€"'), ("atom-4", "'😀'"),
             ("str-4", '"😀"'), ("str-mixed", '"aéb€c😀d"'), ("atom-mixed", "'aéb€c😀d'"),
             ("atom-app", "'é'(a)"), ("str-combining", '"e\u0301"'), ("str-u80", '"\u0080"'),
             ("str-u85", '"\u0085"'), ("str-ua0", '"\u00a0"'), ("str-uad", '"\u00ad"'), ("str-u7ff", '"\u07ff"'),
             ("str-u800", '"\u0800"'), ("str-u200b", '"\u200b"'), ("str-u2028", '"\u2028"'),
             ("str-ud7ff", '"\ud7ff"'), ("str-ue000", '"\ue000"'), ("str-ufeff", '"\ufeff"'),
             ("str-ufffd", '"\ufffd"'), ("str-ufffe", '"\ufffe"'), ("str-uffff", '"\uffff"'),
             ("str-u10000", '"\U00010000"'), ("str-u10ffff", '"\U0010ffff"'), ("str-u1fffe", '"\U0001fffe"'),
             ("bad-lone-cont", b'"\x80"'), ("bad-lone-lead", b'"\xc3"'), ("bad-lead-ascii", b'"\xc3a"'),
             ("bad-overlong2", b'"\xc0\x80"'), ("bad-overlong2b", b'"\xc1\xbf"'),
             ("bad-overlong3", b'"\xe0\x80\x80"'), ("bad-overlong3b", b'"\xe0\x9f\xbf"'),
             ("bad-surrogate", b'"\xed\xa0\x80"'), ("bad-surrogate2", b'"\xed\xbf\xbf"'),
             ("bad-overlong4", b'"\xf0\x80\x80\x80"'), ("bad-overlong4b", b'"\xf0\x8f\xbf\xbf"'),
             ("bad-above", b'"\xf4\x90\x80\x80"'), ("bad-f5", b'"\xf5\x80\x80\x80"'),
             ("bad-f8", b'"\xf8\x88\x80\x80\x80"'), ("bad-ff", b'"\xff"'), ("bad-fe", b'"\xfe"'),
             ("bad-trunc3", b'"\xe2\x82"'), ("bad-trunc4", b'"\xf0\x9f\x98"'),
             ("bad-trunc3-ascii", b'"\xe2\x82a"'), ("bad-extra-cont", b'"\xc3\xa9\xa9"'),
             ("bad-atom-lone", b"'\x80'"), ("bad-atom-overlong", b"'\xc0\xaf'"),
             ("outside", "é"), ("outside-name", "aé"), ("outside-name2", "éa"), ("outside-app", "é(a)"),
             ("outside-upper", "Éa"), ("outside-nbsp", "\u00a0a"), ("outside-after", "a\u00a0"),
             ("outside-greek", "αβγ"), ("outside-symbol", "×"), ("outside-arrow", "→"),
             ("outside-bad", b"\xff"), ("outside-cont", b"a\x80"), ("name-then-emoji", "a😀")]:
    arg("utf8-" + n, x)
whole("utf8-bom", b"\xef\xbb\xbfcontext(a, b).\n")
whole("utf8-comment", "% é\ncontext(a, b).\n")
whole("utf8-block-comment", "/* é */\ncontext(a, b).\n")
whole("utf8-bad-comment", b"% \xff\ncontext(a, b).\n")
whole("utf8-bad-block-comment", b"/* \xc3 */\ncontext(a, b).\n")

# --- numbers
for n, x in [("zero", "0"), ("zeros", "007"), ("neg-zero", "-0"), ("neg-zeros", "-007"), ("neg", "-1"),
             ("big", "123456789012345678901234567890"), ("neg-big", "-123456789012345678901234567890"),
             ("max64", "9223372036854775807"), ("min64", "-9223372036854775808"),
             ("over64", "9223372036854775808"), ("hex", "0x10"), ("hex-upper", "0XFF"), ("oct", "0o17"),
             ("bin", "0b101"), ("char", "0'a"), ("char-quote", "0''"), ("char-dquote", "0'''"),
             ("char-esc", "0'\\n"), ("char-space", "0' "), ("char-utf8", "0'é"), ("group", "1_000"),
             ("group-space", "1 000"), ("group-nl", "1_\n000"), ("float", "1.5"), ("float-e", "1.0e5"),
             ("int-e", "1e5"), ("int-E", "1E5"), ("inf", "1.0Inf"), ("nan", "1.5NaN"), ("rational", "1r3"),
             ("rational-upper", "1R3"), ("radix", "16'ff"), ("radix2", "2'101"), ("minus-space", "- 1"),
             ("minus-paren", "-(1)"), ("minus-space-paren", "- (1)"), ("plus", "+1"), ("plus-space", "+ 1"),
             ("plus-paren", "+(1)"), ("minus-minus", "--1"), ("minus-space-minus", "- -1"),
             ("minus-minus-paren", "-(-1)"), ("minus-paren-paren", "-(-(1))"), ("then-name", "1a"),
             ("then-upper", "1A"), ("then-underscore", "1_"), ("then-quote", "12'"), ("then-quoted", "1'a'"),
             ("then-str", '1"a"'), ("then-paren", "1(a)"), ("then-dot", "1.\n"), ("then-dot-name", "1.a"),
             ("neg-hex", "-0x10"), ("neg-char", "-0'a"), ("neg-float", "-1.5"), ("neg-space-float", "- 1.5"),
             ("neg-group", "-1_000"), ("neg-e", "-1e5"), ("neg-then-name", "-1a"), ("neg-paren", "-1(a)"),
             ("minus-name", "-a"), ("minus-space-name", "- a"), ("minus-app", "-(a)"),
             ("minus-app2", "-(a, b)"), ("minus-alone", "-"), ("minus-nl-digit", "-\n1"),
             ("minus-comment-digit", "-/**/1"), ("neg-in-list", "[-1, - 1]"), ("neg-list", "[-1,-2,-3]"),
             ("neg-app", "f(-1,-2)"), ("neg-after-comment", "/*c*/-1"), ("digit-comment", "1/*c*/"),
             ("digit-percent", "1%c\n"), ("special-inf", "inf"), ("special-nan", "nan"),
             ("float-neg-exp", "1.0e-5"), ("dot-digit", ".5"), ("int-dot-dot", "1..2")]:
    arg("num-" + n, x)

# --- the infix minus
prefix_ops = ["discontiguous", "dynamic", "initialization", "meta_predicate", "module_transparent",
              "multifile", "public", "table", "thread_initialization", "thread_local", "volatile"]
infix_ops = ["as", "div", "is", "mod", "rdiv", "rem", "xor"]
for n, x in [("plain", "a-b"), ("spaces", "a - b"), ("space-left", "a -b"), ("space-right", "a- b"),
             ("phi", "[start-const(0), loop-tmp(i1)]"), ("digit", "a-1"), ("space-digit", "a -1"),
             ("digit-space", "a- 1"), ("neg-digit", "a - -1"), ("list-neg", "[a,-1]"),
             ("app-space-neg", "f(a -1)"), ("app-neg-neg", "f(a- -1)"), ("chain", "a-b-c"),
             ("chain-spaces", "a - b - c"), ("chain-app", "a-b(c)-d"), ("chain-list", "a-[b]-c"),
             ("paren-right", "a-(b)"), ("paren-left", "(a)-b"), ("paren-both", "(a-b)"),
             ("paren-nested", "a-(b-c)"), ("str-right", 'a-"bc"'), ("str-left", '"ab"-c'),
             ("int-left", "1-a"), ("neg-left", "-1-a"), ("neg-left-space", "-1 - a"), ("list-both", "[a]-[b]"),
             ("braces-left", "{}-a"), ("braces-right", "a-{}"), ("nil-right", "a-[]"), ("nil-left", "[]-a"),
             ("qnil-left", "'[]'-[]"), ("bang-right", "a-!"), ("bang-left", "!-a"), ("semi-right", "a-;"),
             ("semi-left", ";-a"), ("plus-left", "+-a"), ("plus-sp-left", "+ -a"), ("plus-sp-left2", "+ - a"),
             ("plus-right", "a-+"), ("arrow", "a->b"), ("minus-minus", "a--b"), ("minus-sp-minus", "a- -b"),
             ("minus-minus-sp", "a - - b"), ("nl-right", "a-\nb"), ("nl-left", "a\n-b"), ("crlf", "a\r\n-\r\nb"),
             ("tab", "a\t-\tb"), ("comment-right", "a-%c\nb"), ("block-right", "a-/*c*/b"),
             ("block-right-sp", "a- /*c*/b"), ("block-left", "a/*c*/-b"), ("percent-left", "a%c\n-b"),
             ("quoted-right", "a-'b'"), ("quoted-both", "'a'-'b'"), ("quoted-app-right", "a-'b'(c)"),
             ("quoted-app-left", "'a b'(c)-d"), ("nested", "a-b(c-d)"), ("lists", "[a-b, c-d]-[e-f]"),
             ("var-right", "a-B"), ("var-right2", "a-_"), ("var-right3", "a-_x"), ("var-left", "A-b"),
             ("qminus-left", "'-'-a"), ("qminus-right", "a-'-'"), ("qplus-left", "'+'-a"),
             ("qprefix-left", "'dynamic'-a"), ("qprefix-right", "a-'dynamic'"), ("app-left", "-(1)-a"),
             ("prefix-app-left", "dynamic(a)-x"), ("prefix-app-right", "x-dynamic(a)"),
             ("prefix-right-comma", "f(a-dynamic, b)"), ("prefix-right-list", "[a-table]"),
             ("prefix-right-term", "a-dynamic b"), ("prefix-right-chain", "a-dynamic-b"),
             ("dot", "a-b.c"), ("colon", "a-b:c"), ("star", "a-b*c"), ("star-left", "a*b-c"),
             ("plus", "a+b"), ("equals", "a=b"), ("colon-only", "a:b"), ("slash", "a/b"), ("is", "a is b"),
             ("mod", "a mod b"), ("minus-end", "a-"), ("minus-sp-end", "a- "), ("minus-b-minus", "a-b-"),
             ("minus-stop", "a-."), ("minus-char", "a-0'a"), ("minus-brace", "a-{b}"), ("minus-upper", "a-B(c)"),
             ("neg-minus", "-a-b"), ("neg-sp", "- a-b"), ("not", "\\+a"), ("minus-app-left", "-(a)-b"),
             ("minus-digit-app", "a-1(b)"), ("int-int", "1-2"), ("int-neg", "1 -2"), ("neg-int-neg", "-1-2"),
             ("list-digit", "[a]-1"), ("app-digit", "f(a)-1"), ("str-digit", '"a"-1'),
             ("backslash-right", "a-\\x"), ("minus-bar", "a-|"), ("minus-comma", "f(a-,b)"),
             ("minus-close", "f(a-)"), ("minus-quote-sp", "a - 'b c'"), ("minus-list-sp", "a - [b, c]"),
             ("minus-empty-atom", "a-''"), ("empty-atom-minus", "''-a"), ("deep", "f(g(a-b)-h(c-d))"),
             ("in-phi-list", "[a-b,c-d,e-f]")]:
    arg("minus-" + n, x)
for op in prefix_ops + infix_ops:
    arg("minus-op-left-" + op, op + "-a")
    arg("minus-op-left-sp-" + op, op + " - a")
    arg("minus-op-right-" + op, "a-" + op)
    arg("minus-op-right-comma-" + op, "f(a-" + op + ", b)")
    arg("minus-op-right-list-" + op, "[a-" + op + "]")
    arg("minus-op-right-app-" + op, "a-" + op + "(b)")
    arg("minus-op-left-app-" + op, op + "(b)-a")
    arg("op-atom-" + op, op)
    arg("op-list-" + op, "[" + op + ", " + op + "]")
    arg("op-app-" + op, op + "(a)")
    arg("op-app2-" + op, op + "(a, b)")
    arg("op-prefix-" + op, op + " a")
    arg("op-infix-" + op, "a " + op + " b")
whole("minus-clause", "a-b.\n")
whole("minus-first-arg", "context(a-b, c-d).\n")
whole("minus-func", "func(f, export, w, [], [\n    block(start, [\n        phi(tmp(i), w, [start-const(0), "
      "loop-tmp(i1)])\n    ], [], ret(tmp(i)))\n]).\n")

# --- symbol atoms
for ch in "#$&*+-/:<=>?@\\^~":
    arg("sym-%02x" % ord(ch), ch)
    arg("sym-app-%02x" % ord(ch), ch + "(a)")
    arg("sym-app2-%02x" % ord(ch), ch + "(a, b)")
    arg("sym-list-%02x" % ord(ch), "[" + ch + ", " + ch + "]")
    arg("sym-prefix-%02x" % ord(ch), ch + "a")
    arg("sym-prefix-sp-%02x" % ord(ch), ch + " a")
    arg("sym-quoted-%02x" % ord(ch), "'" + ch.replace("\\", "\\\\") + "'")
for n, x in [("neck", ":-"), ("dcg", "-->"), ("query", "?-"), ("not", "\\+"), ("univ", "=.."), ("le", "=<"),
             ("pow", "**"), ("arrow", "->"), ("soft", "*->"), ("assign", ":="), ("dict", ">:<"),
             ("two-backslash", "\\\\"), ("div", "//"), ("and", "/\\"), ("or", "\\/"), ("close-comment", "*/"),
             ("open-comment", "/*"), ("plus-comment", "+/*c*/"), ("plus-percent", "+%c\n"),
             ("slash-comment", "//*c*/"), ("bar", "|"), ("bars", "||"), ("bang", "!"), ("semi", ";"),
             ("bang-app", "!(a)"), ("semi-app", ";(a, b)"), ("bangs", "!!"), ("semis", ";;"),
             ("semi-minus", ";-"), ("bang-sym", "!+"), ("sym-bang", "+!"), ("sym-semi", "+;"),
             ("comma-atom", ","), ("neck-app", ":-(a)"), ("neck-app2", ":-(a, b)"), ("dcg-app", "-->(a, b)"),
             ("not-app", "\\+(a)"), ("long", "#$&*+-/:<=>?@\\^~"), ("plus-stop", "+."), ("stop", "."),
             ("stop-app", ".(a, b)"), ("dots", "..."), ("plus-space-app", "+ (a)"), ("plus-list", "+[a]"),
             ("plus-str", '+"a"'), ("plus-quoted", "+'a'"), ("plus-digit", "+1"), ("plus-upper", "+A"),
             ("list-syms", "[+, -, *, /, =]"), ("app-syms", "f(+, -, *)"), ("minus-comma", "f(- , a)"),
             ("sym-sym", "+ -"), ("eq-app", "=(a, b)"), ("backquote", "`"), ("at", "@"), ("caret-app", "^(a, b)"),
             ("dollar-name", "$a"), ("dollar-app", "$(a)"), ("hash-app", "#(a)"), ("as-pattern", "a@b"),
             ("lt-gt", "<>"), ("tilde-gt", "~>"), ("eqeq", "=="), ("neq", "\\=="), ("colon-colon", "::")]:
    arg("symbol-" + n, x)

# --- lists, compounds, names, variables
for n, x in [("nil", "[]"), ("nil-space", "[ ]"), ("nil-nl", "[\n]"), ("nil-block", "[/*c*/]"),
             ("nil-percent", "[%c\n]"), ("nil-nil", "[[]]"), ("nils", "[[], []]"), ("nested", "[[[a]]]"),
             ("deep", "[" * 300 + "a" + "]" * 300), ("bar", "[a|b]"), ("bar-list", "[a|[b]]"),
             ("bar-nil", "[a|[]]"), ("trailing-comma", "[a,]"), ("leading-comma", "[,a]"),
             ("double-comma", "[a,,b]"), ("no-comma", "[a b]"), ("unclosed", "[a"), ("mismatch", "[a)"),
             ("mismatch2", "f(a]"), ("nil-app", "[](a)"), ("list-app", "[a](b)"), ("nil-nil-adj", "[][]"),
             ("spaces", "[ a , b ]"), ("nl", "[\n  a,\n  b\n]"), ("comments", "[a/*1*/,/*2*/b%3\n]"),
             ("str-elems", '["ab", "", "c"]'), ("mixed", "[1, a, 'B', \"s\", [x], f(y), -2, {}]"),
             ("long", "[" + ", ".join(str(i) for i in range(2000)) + "]")]:
    arg("list-" + n, x)
for n, x in [("empty-args", "f()"), ("trailing-comma", "f(a,)"), ("leading-comma", "f(,a)"),
             ("space", "f (a)"), ("nl", "f\n(a)"), ("comment", "f/*c*/(a)"), ("app-app", "f(a)(b)"),
             ("spaces", "f( a , b )"), ("nl-inside", "f(\na\n)"), ("unclosed", "f(a"), ("deep", "f(" * 300 + "a" + ")" * 300),
             ("paren", "(a)"), ("paren-empty", "()"), ("paren-comma", "(a, b)"), ("brace", "{a}"),
             ("braces", "{}"), ("braces-space", "{ }"), ("braces-app", "{}(a)"), ("brace-open", "{"),
             ("dict", "a{b: c}"), ("dict-empty", "_{}"), ("name-mixed", "aB_1"), ("name-digit", "a1"),
             ("name-under", "a_"), ("name-unders", "a__b"), ("name-long", "a" * 5000), ("upper", "A"),
             ("upper-name", "Abc"), ("upper-app", "Abc(a)"), ("under", "_"), ("under-name", "_abc"),
             ("under-upper", "_Abc"), ("under-digit", "_1"), ("var-in-list", "[a, B]"), ("var-in-app", "f(a, B)"),
             ("var-tail", "[H|T]"), ("name-names", "a b"), ("name-digit-sp", "a 1"), ("name-list", "a[b]"),
             ("name-brace", "a{}"), ("name-dot-name", "a.b"), ("name-colon", "a:b:c"), ("comma-term", "a, b"),
             ("many-args", "f(" + ", ".join("a%d" % i for i in range(300)) + ")"),
             ("block", "block(start, [], [\n        let(tmp(r), w, add, [tmp(a), tmp(b)])\n    ], ret(tmp(r)))"),
             ("str-item", 'item(b, str("hi\\n"))'), ("form-feed", "a\x0cb"), ("form-feed-sp", "\x0ca"),
             ("vtab", "\x0ba"), ("nul", "\x00a"), ("del", "\x7fa"), ("esc", "\x1ba"), ("backslash-nl", "a\\\nb")]:
    arg("term-" + n, x)

# --- clauses, comments, the end of the text
for n, x in [("empty", ""), ("space", " "), ("newlines", "\n\n\n"), ("comment-only", "% only a comment\n"),
             ("comment-no-nl", "% only a comment"), ("block-only", "/* only */"), ("block-only-nl", "/* only */\n"),
             ("block-unclosed", "/* never closed"), ("block-unclosed-after", "context(a, b).\n/* never closed"),
             ("block-unclosed-star", "context(a, b).\n/* never closed *"), ("block-nested", "/* a /* b */ context(a, b).\n"),
             ("block-nested2", "/* a /* b */ c */ context(a, b).\n"), ("block-empty", "/**/context(a, b).\n"),
             ("block-stars", "/***/context(a, b).\n"), ("block-many-stars", "/****/ context(a, b). /** x **/\n"),
             ("block-slash", "/*/ context(a, b). /*/\n"), ("block-slash2", "/*/ */ context(a, b).\n"),
             ("block-star-slash", "/* * / */ context(a, b).\n"), ("block-percent", "/* % */ context(a, b).\n"),
             ("percent-block", "% /* \ncontext(a, b).\n"), ("percent-block2", "% /* \ncontext(a, b). % */\n"),
             ("block-quotes", "/* ' \" */ context(a, b).\n"), ("percent-quotes", "% ' \"\ncontext(a, b).\n"),
             ("block-multi", "/* a\n   b.\n   c */\ncontext(a, b).\n"), ("percent-stop", "% a comment. \ncontext(a, b).\n"),
             ("percent-cr", "% c\rcontext(a, b).\ncontext(c, d).\n"), ("percent-crlf", "% c\r\ncontext(a, b).\r\n"),
             ("block-inside", "context(/*1*/a/*2*/,/*3*/b/*4*/)/*5*/.\n"), ("percent-inside", "context(%1\na%2\n,%3\nb%4\n)%5\n.\n"),
             ("slash-star-atom", "context(a, /).\n"), ("slash-eof", "context(a, b).\n/"), ("star-slash", "*/ context(a, b).\n"),
             ("no-stop", "context(a, b)"), ("no-stop-nl", "context(a, b)\n"), ("no-stop-second", "context(a, b).\ncontext(c, d)"),
             ("no-stop-comment", "context(a, b) % .\n"), ("stop-eof", "context(a, b)."), ("stop-space", "context(a, b). "),
             ("stop-tab", "context(a, b).\t"), ("stop-cr", "context(a, b).\r"), ("stop-crlf", "context(a, b).\r\n"),
             ("stop-ff", "context(a, b).\x0c"), ("stop-vt", "context(a, b).\x0b"), ("stop-nul", "context(a, b).\x00"),
             ("stop-percent", "context(a, b).%c"), ("stop-percent-nl", "context(a, b).%c\ncontext(c, d).\n"),
             ("stop-block", "context(a, b)./*c*/\n"), ("stop-block-sp", "context(a, b). /*c*/\n"),
             ("space-stop", "context(a, b) .\n"), ("nl-stop", "context(a, b)\n.\n"), ("block-stop", "context(a, b)/*c*/.\n"),
             ("percent-nl-stop", "context(a, b)%c\n.\n"), ("two-stops", "context(a, b)..\n"), ("stop-stop", "context(a, b). .\n"),
             ("lone-stop", ".\n"), ("two-one-line", "context(a, b). context(c, d).\n"),
             ("two-no-space", "context(a, b).context(c, d).\n"), ("two-lines", "context(a, b).\ncontext(c, d).\n"),
             ("stop-name", "context(a, b).x\n"), ("stop-quote", "context(a, b).'x'\n"), ("stop-paren", "context(a, b).(\n"),
             ("stop-inside", "context(a.\n b).\n"), ("stop-inside-list", "context(a, [b.\n c]).\n"),
             ("stop-after-comma", "context(a,.\n b).\n"), ("crlf-file", "% c\r\ncontext(a, b).\r\ncontext(c,\r\n d).\r\n"),
             ("tabs", "\tcontext(\ta,\tb\t)\t.\t\n"), ("eof-clause", "end_of_file.\n garbage ( .\n"),
             ("eof-clause-after", "context(a, b).\nend_of_file.\n garbage ( .\n"),
             ("eof-clause-quoted", "context(a, b).\n'end_of_file'.\n garbage ( .\n"),
             ("eof-clause-no-stop", "context(a, b).\nend_of_file"), ("eof-clause-eof", "context(a, b).\nend_of_file."),
             ("eof-clause-app", "context(a, b).\nend_of_file(a).\n"), ("eof-clause-then-items", "end_of_file.\ncontext(a, b).\n"),
             ("eof-clause-then-bad", "end_of_file.\nfoo.\nX.\n"), ("eof-after-bad", "foo.\nend_of_file.\n"),
             ("eof-after-var", "context(a, X).\nend_of_file.\n"), ("eof-clause-esc", "'end\\x5f\\of_file'.\ncontext(\n"),
             ("run", "run(f, [1, 2]).\ncontext(a, b).\n"), ("run-only", "run(f, [1, 2]).\n"),
             ("run-many", "run(f, []).\ncontext(a, b).\nrun(g, [3]).\ncontext(c, d).\nrun(f, [-1]).\n"),
             ("run-1", "run(f).\n"), ("run-0", "run.\n"), ("run-3", "run(f, [], x).\n"), ("run-quoted", "'run'(f, []).\n"),
             ("run-var", "run(F, []).\n"), ("run-any", "run(1, 2).\ncontext(a, b).\n"), ("run-minus", "run(a-b, c-d).\n"),
             ("item-func", "func(a, b, c, d, e).\n"), ("item-data", "data(a, b, c, d).\n"), ("item-alias", "alias(a, b, c).\n"),
             ("item-context", "context(a, b).\n"), ("item-all", "func(a, b, c, d, e).\ndata(a, b, c, d).\nalias(a, b, c).\ncontext(a, b).\n"),
             ("item-func-4", "func(a, b, c, d).\n"), ("item-func-6", "func(a, b, c, d, e, f).\n"), ("item-data-3", "data(a, b, c).\n"),
             ("item-data-5", "data(a, b, c, d, e).\n"), ("item-alias-2", "alias(a, b).\n"), ("item-alias-4", "alias(a, b, c, d).\n"),
             ("item-context-1", "context(a).\n"), ("item-context-3", "context(a, b, c).\n"), ("item-atom", "func.\n"),
             ("item-quoted", "'context'(a, b).\n"), ("item-module", "module([]).\n"), ("item-foo", "foo(a).\n"),
             ("item-atom-a", "a.\n"), ("item-list", "[a].\n"), ("item-nil", "[].\n"), ("item-int", "1.\n"),
             ("item-neg", "-1.\n"), ("item-str", '"s".\n'), ("item-braces", "{}.\n"), ("item-directive", ":- foo.\n"),
             ("item-rule", "context(a, b) :- c.\n"), ("item-var", "X.\n"), ("item-good-bad", "context(a, b).\nfoo(a).\n"),
             ("item-bad-good", "foo(a).\ncontext(a, b).\n"), ("item-good-syntax", "context(a, b).\ncontext(a, (.\n"),
             ("item-good-var", "context(a, b).\ncontext(a, X).\n"), ("item-func-phi", "func(f, export, w, [param(w, tmp(a))], [\n"
              "    block(start, [], [], jmp(loop)),\n    block(loop, [\n        phi(tmp(i), w, [start-const(0), loop-tmp(i1)])\n"
              "    ], [\n        let(tmp(i1), w, add, [tmp(i), const(-1)])\n    ], jnz(tmp(i1), loop, done)),\n"
              "    block(done, [], [], ret(tmp(i)))\n]).\n"),
             ("header-example", "run(addw, [3, 4]).\nfunc(addw, export, w, [param(w, tmp(a)), param(w, tmp(b))], [\n"
              "    block(start, [], [\n        let(tmp(r), w, add, [tmp(a), tmp(b)])\n    ], ret(tmp(r)))\n]).\n"
              'data(msg, local, 1, [item(b, str("hi\\n")), item(b, const(0))]).\n')]:
    whole("text-" + n, x)

seen = set()
for i, (name, data) in enumerate(cases):
    assert name not in seen, name
    seen.add(name)
    with open(os.path.join(out, name + ".ir"), "wb") as f:
        f.write(data)
