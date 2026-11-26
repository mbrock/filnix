#!/usr/bin/env bash
# Byte-for-byte differential check of nanofil-frontend (CLex.v + CParse.v +
# CCanon.v + CPp.v) against SWI-Prolog (nanofil/src/c_lex.pl + c_types.pl +
# c_parse.pl + c_pp.pl) across all C test fixtures, C23 fixtures, and
# preprocessor torture tests.
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
frontend=$(cd "$here/.." && pwd)
nanofil=$(cd "$frontend/../.." && pwd)
swipl=${SWIPL:-swipl}
fe=${NANOFIL_FRONTEND:-$frontend/nanofil-frontend}

python3 - "$nanofil" "$swipl" "$fe" <<'PY'
import glob, os, subprocess, sys, tempfile

nanofil, swipl, fe = sys.argv[1:4]
cfiles = sorted(glob.glob(os.path.join(nanofil, 'tests', '**', '*.c'), recursive=True))
if not cfiles:
    sys.exit("diff.sh: no .c files found under nanofil/tests")

with tempfile.TemporaryDirectory() as td:
    files_pl = os.path.join(td, 'files.pl')
    with open(files_pl, 'w') as f:
        f.write('test_files([\n')
        for i, p in enumerate(cfiles):
            comma = ',' if i + 1 < len(cfiles) else ''
            f.write(f"  '{p}'{comma}\n")
        f.write(']).\n')

    pl_script = os.path.join(td, 'dump.pl')
    with open(pl_script, 'w') as f:
        f.write(f"""
:- use_module('{nanofil}/src/c_lex').
:- use_module('{nanofil}/src/c_types').
:- use_module('{nanofil}/src/c_parse').
:- consult('{files_pl}').

run_all(LexOut, ParseOut) :-
    test_files(Files),
    open(LexOut, write, SL),
    open(ParseOut, write, SP),
    process(Files, SL, SP),
    close(SL),
    close(SP).

process([], _, _).
process([F|Fs], SL, SP) :-
    ( catch(c_lex:i_file_tokens(F, Toks), E, (
          format(SL, '=== ~w ===~nERR~n', [F]),
          format(SP, '=== ~w ===~nLEX_ERR~n', [F]),
          Toks = error(E)
      ))
    ),
    ( Toks = error(_) -> true
    ; format(SL, '=== ~w ===~n', [F]),
      write_canonical(SL, Toks), write(SL, '.'), nl(SL),
      ( catch(c_parse:c_parse(Toks, Ast), _E2, Ast = parse_err) ->
          ( Ast == parse_err ->
              format(SP, '=== ~w ===~nERR~n', [F])
          ; format(SP, '=== ~w ===~n', [F]),
            write_canonical(SP, Ast), write(SP, '.'), nl(SP)
          )
      ; format(SP, '=== ~w ===~nERR~n', [F])
      )
    ),
    process(Fs, SL, SP).
""")

    swi_lex = os.path.join(td, 'swi_lex.txt')
    swi_parse = os.path.join(td, 'swi_parse.txt')
    subprocess.run(
        [swipl, '-q', '-s', os.path.join(nanofil, 'src', 'swi', 'compat.pl'),
         '-s', pl_script, '-g', f"run_all('{swi_lex}','{swi_parse}')", '-t', 'halt'],
        check=True)

    def load_sections(path):
        d = {}
        cur = None
        buf = []
        with open(path, 'rb') as f:
            for line in f:
                if line.startswith(b'=== ') and line.endswith(b' ===\n'):
                    if cur is not None:
                        d[cur] = b''.join(buf).strip()
                    cur = line[4:-5].decode('utf-8')
                    buf = []
                else:
                    buf.append(line)
            if cur is not None:
                d[cur] = b''.join(buf).strip()
        return d

    swi_l = load_sections(swi_lex)
    swi_p = load_sections(swi_parse)

    lex_ok = lex_err = lex_diff = 0
    parse_ok = parse_err = parse_diff = 0
    for cf in cfiles:
        rl = subprocess.run([fe, 'lex', cf], capture_output=True)
        sl = swi_l[cf]
        if rl.returncode != 0:
            if sl == b'ERR':
                lex_err += 1
            else:
                lex_diff += 1
                if lex_diff <= 5:
                    print(f"LEX DIFF (err) {cf}: {rl.stderr.decode(errors='replace').strip()}", file=sys.stderr)
            continue
        ol = rl.stdout.strip()
        if ol == sl:
            lex_ok += 1
        else:
            lex_diff += 1
            if lex_diff <= 5:
                print(f"LEX DIFF {cf}", file=sys.stderr)
            continue

        rp = subprocess.run([fe, 'parse', cf], capture_output=True)
        sp = swi_p[cf]
        if rp.returncode != 0:
            if sp == b'ERR':
                parse_err += 1
            else:
                parse_diff += 1
                if parse_diff <= 5:
                    print(f"PARSE DIFF (err) {cf}: {rp.stderr.decode(errors='replace').strip()}", file=sys.stderr)
        else:
            op = rp.stdout.strip()
            if op == sp:
                parse_ok += 1
            else:
                parse_diff += 1
                if parse_diff <= 5:
                    print(f"PARSE DIFF {cf}", file=sys.stderr)

    print(f"lex:   {lex_ok} ok + {lex_err} err = {lex_ok + lex_err}/{len(cfiles)}, diffs={lex_diff}")
    print(f"parse: {parse_ok} ok + {parse_err} err = {parse_ok + parse_err}/{lex_ok}, diffs={parse_diff}")

    c23_files = sorted(glob.glob(os.path.join(nanofil, 'tests', 'c', '**', '*c23*.c'), recursive=True))
    c23_diffs = 0
    for cf in c23_files:
        ro = subprocess.run([fe, '--c23', 'parse', cf], capture_output=True)
        rs = subprocess.run(
            [swipl, '-q', '-s', os.path.join(nanofil, 'src', 'swi', 'compat.pl'), '-g',
             f"use_module('{nanofil}/src/c_lex'), use_module('{nanofil}/src/c_types'), "
             f"use_module('{nanofil}/src/c_parse'), "
             f"(catch((c_lex:i_file_tokens('{cf}', T0), c_lex:c23_tokens(T0, T), "
             f"c_parse:c_parse(T, A)), _, fail) -> write_canonical(A), write('.'), nl ; halt(1))",
             '-t', 'halt'],
            capture_output=True)
        if (ro.returncode == 0) != (rs.returncode == 0) or (
                ro.returncode == 0 and ro.stdout.strip() != rs.stdout.strip()):
            c23_diffs += 1
            print(f"C23 DIFF {cf}: rc {ro.returncode} vs {rs.returncode}", file=sys.stderr)
    print(f"c23:   {len(c23_files) - c23_diffs}/{len(c23_files)} exact, diffs={c23_diffs}")

    # Preprocessor torture tests (hermetic: no external clang required).
    pp_dir = os.path.join(td, 'pp')
    inc1 = os.path.join(pp_dir, 'inc1')
    inc2 = os.path.join(pp_dir, 'inc2')
    os.makedirs(inc1)
    os.makedirs(inc2)
    with open(os.path.join(inc1, 'stdio.h'), 'w') as f:
        f.write('int fake_stdio;\n')
    with open(os.path.join(inc1, 'chain.h'), 'w') as f:
        f.write('int from_inc1;\n#include_next <chain.h>\n')
    with open(os.path.join(inc2, 'chain.h'), 'w') as f:
        f.write('int from_inc2;\n')
    with open(os.path.join(pp_dir, 'once.h'), 'w') as f:
        f.write('#pragma once\nint included_once;\n')
    with open(os.path.join(pp_dir, 'macros.c'), 'w') as f:
        f.write(r'''#define OBJ 27
#define ADD(a,b) ((a)+(b))
#define STR(x) #x
#define CAT(a,b) a##b
#define EXPAND_CAT(a,b) CAT(a,b)
#define VAR(a,...) a(__VA_ARGS__)
#define ALL(...) __VA_ARGS__
#define NAMED(args...) args
#define SELF SELF
#define ONE TWO
#define TWO ONE
#define CALL ADD
#define EMPTY()
#include "once.h"
#include "once.h"
#define HEADER "once.h"
#include HEADER
#include "./once.h"
#include <chain.h>
#pragma ignored
#pragma weak alias_fn = target_fn
#pragma pack(push, 2)
struct packed_s { char a; int b; };
#pragma pack(pop)
OBJ ADD(OBJ, ADD(1,2)) VAR(ADD,3,4) CALL(2,3)
ALL() ALL(1,2,(3,4)) NAMED(5,6) STR()
STR(OBJ   + /* comment */ "quoted\\text")
STR(ADD(1,2)) CAT(OB,J) EXPAND_CAT(OB,J)
CAT(,OBJ) CAT(OBJ,) CAT(,) EMPTY() SELF ONE
ADD(
  3,
  4)
#undef OBJ
#ifdef OBJ
#error undef failed
#elif defined(SELF) && !defined missing && (2+3*4==14) && ((8>>2)==2)
int conditional;
#else
#error condition failed
#endif
#if 0
#if 1/0
#error inactive
#endif
#elif (1 || 1/0) && (0 ? 1/0 : 1)
int short_circuit;
#endif
#if __has_include("once.h") && __has_include(<stdio.h>) && !__has_include(<missing_nanofil.h>)
int has_include;
#endif
#if (-1 < 1U) || (~0U >> 63) != 1 || (18446744073709551615ULL + 1) != 0
#error uintmax conversion failed
#endif
#if (9007199254740993LL / 3) != 3002399751580331LL || (-7/3) != -2 || (-7%3) != -1
#error integer division failed
#endif
#if (1 ? -1 : 0U) < 0
#error conditional conversions failed
#endif
#if L'\0' - 1 < 0 && ('a' == 97) && (1 | 2 ^ 3 & 4) == 3 && L'\xff' == 255 \
    && ((1 == 1) << 40) == 1099511627776
int character_condition;
#endif
#define MULTI(a) a + \
  2
MULTI(1)
__LINE__ __FILE__
#define OBJECT_PASTE 1##2
OBJECT_PASTE
CAT(L,'x') CAT(L,"wide")
STR(ADD())
#define RECUR(x) RECUR(x)
RECUR(RECUR(3))
#define x 3
#define f(a) f(x * (a))
#undef x
#define x 2
#define g f
#define z z[0]
#define h g(~
#define m(a) a(w)
#define w 0,1
#define t(a) a
f(y+1) + f(f(z)) % t(t(g)(0) + t)(1);
g(x + (3,4) - w) | h 5) & m(f) ^ m(m);
''')
    with open(os.path.join(pp_dir, 'locations.c'), 'w') as f:
        f.write('#define DECL int\n// a physical source line\nDECL source_line; \\\nint continued_line;\n#include "once.h"\n')
    with open(os.path.join(pp_dir, 'line-pragma.c'), 'w') as f:
        f.write('''#define line 1000
#line line "virtual/source.c"
__LINE__ __FILE__
#if __LINE__ != 1001 || !__has_include("once.h")
#error logical line or physical include directory lost
#endif
#include "once.h"
#line \\
2000
__LINE__ __FILE__
#define COMMENT /* a comment may span
physical lines without ending a directive */ 7
COMMENT __LINE__
#define push_macro ignored
#define pop_macro ignored
#pragma push_macro("SAVED")
#define SAVED 111
#pragma push_macro("SAVED")
#undef SAVED
#define SAVED 222
SAVED
#pragma pop_macro("SAVED")
SAVED
#pragma pop_macro("SAVED")
#ifdef SAVED
#error an undefined macro was not restored
#endif
#define FN(x) ((x)+3)
#pragma push_macro("FN")
#undef FN
#define FN 5
FN
#pragma pop_macro("FN")
FN(4)
''')
    with open(os.path.join(pp_dir, 'error.c'), 'w') as f:
        f.write('#error intentional\n')

    pp_cases = [os.path.join(pp_dir, name) for name in ('macros.c', 'locations.c', 'line-pragma.c')]
    pp_diffs = 0
    for cf in pp_cases:
        ro = subprocess.run([fe, '--no-profile', '-I', inc1, '-I', inc2, 'pp', cf], capture_output=True)
        rs = subprocess.run(
            [swipl, '-q', '-s', os.path.join(nanofil, 'src', 'swi', 'compat.pl'), '-g',
             f"asserta(user:file_search_path(library, '{nanofil}/src')), "
             f"use_module(library(assoc)), use_module(library(c_types)), use_module(library(c_pp)), "
             f"empty_assoc(E), pp_file('{cf}', profile(E, ['{inc1}', '{inc2}'], features(none, [])), Ts), "
             f"write_canonical(Ts), write('.'), nl",
             '-t', 'halt'],
            capture_output=True)
        if ro.returncode != 0 or rs.returncode != 0 or ro.stdout.strip() != rs.stdout.strip():
            pp_diffs += 1
            print(f"PP DIFF {os.path.basename(cf)}: rc {ro.returncode} vs {rs.returncode}", file=sys.stderr)
            if ro.stderr:
                print(ro.stderr.decode(errors='replace'), file=sys.stderr)
    re_err = subprocess.run([fe, '--no-profile', 'pp', os.path.join(pp_dir, 'error.c')], capture_output=True)
    if re_err.returncode == 0 or b'error_directive' not in re_err.stderr:
        pp_diffs += 1
        print("PP DIFF error.c: expected error_directive failure", file=sys.stderr)
    print(f"pp:    {len(pp_cases) + 1 - pp_diffs}/{len(pp_cases) + 1} torture cases exact, diffs={pp_diffs}")

    # IEEE 754 binary32/binary64/x87-80 parity against ieee.pl.
    ieee_queries = []
    for k in ('s', 'd', 'x'):
        for lit in ('0', '-0.0', '1.5', '0.1', '3.14159265358979323846264338327950288',
                    '1e-45', '4.9406564584124654e-324', '3.64519953188247460253e-4951',
                    '1.7976931348623157e308', '1e5000', '0x1.fp-1', '-0x1.8p+1', 'bad'):
            ieee_queries.append(('parse', k, lit))
        for n in (0, -1, 16777217, (1 << 53) + 1, -(1 << 63), (1 << 64) - 1):
            ieee_queries.append(('from_int', k, str(n)))
    ieee_pats = {
        's': [0, 0x80000000, 1, 0x3f800000, 0xbf800000, 0x7f800000, 0xff800000, 0x7fc00001, 0x7f800001],
        'd': [0, 1 << 63, 1, 0x3ff0000000000000, 0x7ff0000000000000, 0xfff0000000000000, 0x7ff8000000000001],
        'x': [0, 1 << 79, 1, (16383 << 64) | (1 << 63), (32767 << 64) | (1 << 63),
              (32767 << 64) | (3 << 62) | 5, (32767 << 64) | (1 << 63) | 7],
    }
    for k, ps in ieee_pats.items():
        for a in ps:
            ieee_queries.append(('neg', k, str(a)))
            ieee_queries.append(('sqrt', k, str(a)))
            ieee_queries.append(('to_int', k, str(a)))
            ieee_queries.append(('decimal', k, str(a)))
            for to in ('s', 'd', 'x'):
                ieee_queries.append(('convert', k, to, str(a)))
            for b in ps:
                for op in ('add', 'sub', 'mul', 'div'):
                    ieee_queries.append(('binary', k, op, str(a), str(b)))
                for cond in ('eq', 'ne', 'lt', 'le', 'gt', 'ge', 'o', 'uo'):
                    ieee_queries.append(('compare', k, cond, str(a), str(b)))
    ro_i = subprocess.run([fe, 'ieee-batch'],
                          input='\n'.join(' '.join(q) for q in ieee_queries) + '\n',
                          text=True, capture_output=True, check=True)
    ieee_pl = os.path.join(td, 'ieee.pl')
    with open(ieee_pl, 'w') as f:
        f.write(f":- use_module('{nanofil}/src/ieee').\n")
        f.write("run_q(parse(K, S)) :- (ieee_parse(K, S, R) -> format('ok ~d~n', [R]) ; writeln(fail)).\n")
        f.write("run_q(decimal(K, B)) :- (ieee_decimal(K, B, Cs) -> atom_chars(A, Cs), format('ok ~w~n', [A]) ; writeln(fail)).\n")
        f.write("run_q(from_int(K, N)) :- ieee_from_int(K, N, R), format('ok ~d~n', [R]).\n")
        f.write("run_q(to_int(K, B)) :- (ieee_to_int(K, B, R) -> format('ok ~d~n', [R]) ; writeln(fail)).\n")
        f.write("run_q(neg(K, A)) :- ieee_neg(K, A, R), format('ok ~d~n', [R]).\n")
        f.write("run_q(sqrt(K, A)) :- ieee_sqrt(K, A, R), format('ok ~d~n', [R]).\n")
        f.write("run_q(convert(F, T, A)) :- ieee_convert(F, T, A, R), format('ok ~d~n', [R]).\n")
        f.write("run_q(binary(K, Op, A, B)) :- ieee_binary(K, Op, A, B, R), format('ok ~d~n', [R]).\n")
        f.write("run_q(compare(K, C, A, B)) :- ieee_compare(K, C, A, B, R), format('ok ~d~n', [R]).\n")
        f.write("run_all :- forall(q(Q), run_q(Q)).\n")
        for q in ieee_queries:
            if q[0] == 'parse':
                f.write(f'q(parse({q[1]}, "{q[2]}")).\n')
            else:
                f.write(f"q({q[0]}({', '.join(q[1:])})).\n")
    rs_i = subprocess.run([swipl, '-q', '-s', os.path.join(nanofil, 'src', 'swi', 'compat.pl'),
                           '-s', ieee_pl, '-g', 'run_all', '-t', 'halt'],
                          text=True, capture_output=True, check=True)
    o_lines = ro_i.stdout.splitlines()
    s_lines = rs_i.stdout.splitlines()
    ieee_diffs = sum(1 for a, b in zip(o_lines, s_lines) if a != b) + abs(len(o_lines) - len(s_lines))
    print(f"ieee:  {len(ieee_queries) - ieee_diffs}/{len(ieee_queries)} exact, diffs={ieee_diffs}")

    # Semantic type-checker parity against c_types.pl across all standalone C fixtures.
    tc_pl = os.path.join(td, 'typecheck.pl')
    tc_src = r"""
:- use_module(library(lists)).
:- use_module(library(assoc)).
:- use_module('__NANOFIL__/src/c_lex').
:- use_module('__NANOFIL__/src/c_types').
:- use_module('__NANOFIL__/src/c_parse').
:- consult('__FILES_PL__').

bind_top_decl(d(Nm, Ty, Stg, _, _), Env0, Env) :-
    ( Stg == typedef -> Env = Env0
    ; Ty = func(_, _, _) -> bind_ordinary(Nm, fn(Ty, Nm, external), Env0, Env)
    ; bind_ordinary(Nm, gvar(Ty, Nm, external, false), Env0, Env)
    ).
bind_local_decl(d(Nm, Ty, Stg, _, _), Env0, Env) :-
    ( Stg == typedef -> Env = Env0
    ; Ty = func(_, _, _) -> bind_ordinary(Nm, fn(Ty, Nm, external), Env0, Env)
    ; bind_ordinary(Nm, var(none, Ty), Env0, Env)
    ).
load_builtin_item(decl(_, Specs, Inits), Env0, Env) :- !,
    ( catch(decl_types(Specs, Inits, Decls, Env0, Env1), _, fail) ->
        foldl(bind_top_decl, Decls, Env1, Env)
    ; Env = Env0
    ).
load_builtin_item(_, Env, Env).
emit_err(S, Tag, Err) :-
    ( Err = not_constant -> T = not_constant
    ; Err = bad(W) -> T = bad(W)
    ; Err = nanofil_error(M) -> T = sema(M)
    ; T = sema(Err)
    ),
    Term =.. [Tag, T],
    write_canonical(S, Term), nl(S).
check_expr_rec(S, E, Env0, Env) :-
    ( expression_tags(E, Env0, Env) -> true ; Env = Env0 ),
    catch(
      ( elaborate(E, Env, X) ->
          value(X, XV),
          ( folded(XV, Env, CV) -> F = some(CV) ; F = none ),
          write_canonical(S, expr(X, F)), nl(S)
      ; ( c_types:fault(E, Env, Fmt, Args) ->
            format(atom(Msg), Fmt, Args),
            write_canonical(S, expr_fault(Msg)), nl(S)
        ; write(S, 'expr_none'), nl(S)
        )
      ),
      Err,
      emit_err(S, expr_err, Err)
    ).
check_init_rec(S, list(Es), Env0, Env) :- !, foldl(check_init_entry(S), Es, Env0, Env).
check_init_rec(S, E, Env0, Env) :- check_expr_rec(S, E, Env0, Env).
check_init_entry(S, entry(_, Ini), Env0, Env) :- check_init_rec(S, Ini, Env0, Env).
collect_labels(at(_, label(Nm, Body)), L0, L) :- !, collect_labels(Body, [Nm|L0], L).
collect_labels(at(_, block(Items)), L0, L) :- !, foldl(collect_bi_labels, Items, L0, L).
collect_labels(at(_, if(_, T, OE)), L0, L) :- !,
    collect_labels(T, L0, L1), ( OE == none -> L = L1 ; collect_labels(OE, L1, L) ).
collect_labels(at(_, while(_, B)), L0, L) :- !, collect_labels(B, L0, L).
collect_labels(at(_, do(B, _)), L0, L) :- !, collect_labels(B, L0, L).
collect_labels(at(_, for(_, _, _, B)), L0, L) :- !, collect_labels(B, L0, L).
collect_labels(at(_, switch(_, B)), L0, L) :- !, collect_labels(B, L0, L).
collect_labels(at(_, case(_, B)), L0, L) :- !, collect_labels(B, L0, L).
collect_labels(at(_, default(B)), L0, L) :- !, collect_labels(B, L0, L).
collect_labels(_, L, L).
collect_bi_labels(at(L, St), L0, Out) :- !, collect_labels(at(L, St), L0, Out).
collect_bi_labels(_, L, L).
bind_func_labels(Body, Env0, Env) :-
    collect_labels(Body, [], Rev), reverse(Rev, Lbls), bind_lbls(Lbls, 1, Env0, Env).
bind_lbls([], _, Env, Env).
bind_lbls([Nm|Rest], I, Env0, Env) :-
    ( lookup_ordinary(Env0, label_addr(Nm), _) -> bind_lbls(Rest, I, Env0, Env)
    ; bind_ordinary(label_addr(Nm), I, Env0, Env1), I1 is I + 1, bind_lbls(Rest, I1, Env1, Env)
    ).
check_local_decl(S, Specs, Inits, Env0, Env) :-
    catch((decl_types(Specs, Inits, Ds, Env0, Env1), foldl(check_one_local_decl(S), Ds, Env1, Env)),
          Err, (emit_err(S, decl_err, Err), Env = Env0)).
check_one_local_decl(S, D, Env0, Env) :-
    D = d(Nm, Ty, Stg, _, OInit),
    write_canonical(S, local_decl(Nm, Ty, Stg)), nl(S),
    bind_local_decl(D, Env0, Env1),
    ( OInit == none -> Env = Env1 ; check_init_rec(S, OInit, Env1, Env) ).
check_stmt_rec(S, at(_, St), Env0, Env) :- !, check_stmt_body(S, St, Env0, Env).
check_stmt_rec(_, _, Env, Env).
check_stmt_body(_, null, Env, Env) :- !.
check_stmt_body(_, break, Env, Env) :- !.
check_stmt_body(_, continue, Env, Env) :- !.
check_stmt_body(_, goto(_), Env, Env) :- !.
check_stmt_body(_, asm(_, _, _, _, _), Env, Env) :- !.
check_stmt_body(_, asm(_, _, _, _), Env, Env) :- !.
check_stmt_body(_, asm_unsupported(_), Env, Env) :- !.
check_stmt_body(S, expr(E), Env0, Env) :- !, check_expr_rec(S, E, Env0, Env).
check_stmt_body(S, computed_goto(E), Env0, Env) :- !, check_expr_rec(S, E, Env0, Env).
check_stmt_body(S, return(OE), Env0, Env) :- !,
    ( OE == none -> Env = Env0 ; check_expr_rec(S, OE, Env0, Env) ).
check_stmt_body(S, if(C, T, OE), Env0, Env) :- !,
    check_expr_rec(S, C, Env0, Env1), check_stmt_rec(S, T, Env1, Env2),
    ( OE == none -> Env = Env2 ; check_stmt_rec(S, OE, Env2, Env) ).
check_stmt_body(S, while(C, B), Env0, Env) :- !,
    check_expr_rec(S, C, Env0, Env1), check_stmt_rec(S, B, Env1, Env).
check_stmt_body(S, do(B, C), Env0, Env) :- !,
    check_stmt_rec(S, B, Env0, Env1), check_expr_rec(S, C, Env1, Env).
check_stmt_body(S, for(FI, FC, FS, B), Env0, Env) :- !,
    Env0 = e(Ords0, Tags0, _, _),
    ( FI == none -> Env1 = Env0
    ; FI = expr(E) -> check_expr_rec(S, E, Env0, Env1)
    ; FI = decl(_, Specs, Inits) -> check_local_decl(S, Specs, Inits, Env0, Env1)
    ; Env1 = Env0
    ),
    ( FC == none -> Env2 = Env1 ; check_expr_rec(S, FC, Env1, Env2) ),
    ( FS == none -> Env3 = Env2 ; check_expr_rec(S, FS, Env2, Env3) ),
    check_stmt_rec(S, B, Env3, e(_, _, Defs4, Next4)),
    Env = e(Ords0, Tags0, Defs4, Next4).
check_stmt_body(S, switch(C, B), Env0, Env) :- !,
    check_expr_rec(S, C, Env0, Env1), check_stmt_rec(S, B, Env1, Env).
check_stmt_body(S, case(range(Lo, Hi), B), Env0, Env) :- !,
    check_expr_rec(S, Lo, Env0, Env1), check_expr_rec(S, Hi, Env1, Env2),
    check_stmt_rec(S, B, Env2, Env).
check_stmt_body(S, case(E, B), Env0, Env) :- !,
    check_expr_rec(S, E, Env0, Env1), check_stmt_rec(S, B, Env1, Env).
check_stmt_body(S, default(B), Env0, Env) :- !, check_stmt_rec(S, B, Env0, Env).
check_stmt_body(S, label(_, B), Env0, Env) :- !, check_stmt_rec(S, B, Env0, Env).
check_stmt_body(S, block(Items), Env0, Env) :- !,
    Env0 = e(Ords0, Tags0, _, _),
    foldl(check_bi(S), Items, Env0, e(_, _, Defs1, Next1)),
    Env = e(Ords0, Tags0, Defs1, Next1).
check_stmt_body(_, _, Env, Env).
check_bi(S, at(L, St), Env0, Env) :- !, check_stmt_rec(S, at(L, St), Env0, Env).
check_bi(S, decl(_, Specs, Inits), Env0, Env) :- !, check_local_decl(S, Specs, Inits, Env0, Env).
check_bi(S, static_assert(_, E, _), Env0, Env) :- !, check_expr_rec(S, E, Env0, Env).
check_bi(_, _, Env, Env).
bind_param_list(func(_, params(Ps, _)), Pts, Env0, Env) :- !, bind_ps(Ps, Pts, Env0, Env).
bind_param_list(_, _, Env, Env).
bind_ps([param(_, dcl(some(Nm), _, _))|Ra], [Pt|Rb], Env0, Env) :- !,
    bind_ordinary(Nm, var(none, Pt), Env0, Env1), bind_ps(Ra, Rb, Env1, Env).
bind_ps([_|Ra], [_|Rb], Env0, Env) :- !, bind_ps(Ra, Rb, Env0, Env).
bind_ps(_, _, Env, Env).
check_top_item(S, decl(_, Specs, Inits), Env0, Env) :- !,
    catch((decl_types(Specs, Inits, Ds, Env0, Env1), foldl(check_one_top_decl(S), Ds, Env1, Env)),
          Err, (emit_err(S, decl_err, Err), Env = Env0)).
check_top_item(S, fundef(Loc, Specs, dcl(some(Nm), Syn0, _), Body), Env0, Env) :- !,
    ( lookup_ordinary(Env0, Nm, fn(func(_, Ps0, _), _, _)), is_list(Ps0) -> Prot = true ; Prot = false ),
    catch(
      ( ( Syn0 = func(Inner, knr(Ns, Ds)) ->
            knr_definition(Loc, knr(Ns, Ds), Prot, Env0, Ps1, KnrLocs), Syn = func(Inner, Ps1)
        ; Syn = Syn0, KnrLocs = []
        ),
        specs_type(Specs, Base, Env0, Env1),
        apply_declarator(Syn, Base, FnTy, Env1, Env2),
        reflect_type(type(Specs, Syn), FnTy, Env2, Refl),
        write_canonical(S, top_func(Nm, FnTy, Refl)), nl(S),
        bind_ordinary(Nm, fn(FnTy, Nm, external), Env2, Env3a),
        bind_ordinary(qtype(Nm), Refl, Env3a, Env3),
        Env3 = e(Ords3, Tags3, _, _),
        bind_ordinary(enclosing(function), Nm, Env3, Env4),
        ( FnTy = func(_, Pts, _), is_list(Pts) ->
            bind_param_list(Syn, Pts, Env4, Env5a), reflect_params(Syn, Pts, Env5a, Env5)
        ; Env5 = Env4
        ),
        bind_func_labels(Body, Env5, Env6),
        ( KnrLocs == [] -> BodyFull = Body
        ; ( Body = at(L, block(Bs)) -> append(KnrLocs, Bs, AllBs), BodyFull = at(L, block(AllBs))
          ; append(KnrLocs, [Body], AllBs), BodyFull = at(Loc, block(AllBs))
          )
        ),
        check_stmt_rec(S, BodyFull, Env6, e(_, _, Defs7, Next7)),
        Env = e(Ords3, Tags3, Defs7, Next7)
      ),
      Err,
      ( emit_err(S, func_err, Err), Env = Env0 )
    ).
check_top_item(S, static_assert(_, E, _), Env0, Env) :- !, check_expr_rec(S, E, Env0, Env).
check_top_item(_, _, Env, Env).
check_one_top_decl(S, D, Env0, Env) :-
    D = d(Nm, Ty, Stg, _, OInit),
    write_canonical(S, top_decl(Nm, Ty, Stg)), nl(S),
    bind_top_decl(D, Env0, Env1),
    ( OInit == none -> Env = Env1 ; check_init_rec(S, OInit, Env1, Env) ).
emit_all_sus(S, I, Next, Defs) :-
    ( I >= Next -> true
    ; ( get_assoc(I, Defs, Def) -> write_canonical(S, su_def(I, Def)), nl(S) ; true ),
      I1 is I + 1, emit_all_sus(S, I1, Next, Defs)
    ).
run_all(OutFile) :-
    test_files(Files), open(OutFile, write, S), process(Files, S), close(S).
process([], _).
process([F|Fs], S) :-
    ( catch((c_lex:i_file_tokens(F, Toks), c_parse:c_parse(Toks, Items)), _, fail) ->
        format(S, '=== ~w ===~n', [F]),
        empty_env(E0), builtin_declarations(Bs),
        foldl(load_builtin_item, Bs, E0, E1),
        foldl(check_top_item(S), Items, E1, EFin),
        EFin = e(_, _, Defs, Next),
        emit_all_sus(S, 0, Next, Defs)
    ; format(S, '=== ~w ===~nPARSE_ERR~n', [F])
    ),
    process(Fs, S).
""".replace('__NANOFIL__', nanofil).replace('__FILES_PL__', files_pl)
    with open(tc_pl, 'w') as f:
        f.write(tc_src)
    swi_tc = os.path.join(td, 'swi_tc.txt')
    subprocess.run(
        [swipl, '-q', '-s', os.path.join(nanofil, 'src', 'swi', 'compat.pl'),
         '-s', tc_pl, '-g', f"run_all('{swi_tc}')", '-t', 'halt'],
        check=True)
    swi_t = load_sections(swi_tc)
    tc_ok = tc_diff = 0
    for cf in cfiles:
        st = swi_t[cf]
        if st == b'PARSE_ERR':
            continue
        rt = subprocess.run([fe, 'typecheck', cf], capture_output=True)
        if rt.returncode != 0 or rt.stdout.strip() != st:
            tc_diff += 1
            if tc_diff <= 5:
                print(f"TYPECHECK DIFF {cf} (rc={rt.returncode})", file=sys.stderr)
        else:
            tc_ok += 1
    print(f"types: {tc_ok}/{tc_ok + tc_diff} exact, diffs={tc_diff}")

    # Differential check of full C lowering (cc-ir) and record layouts (cc-layouts)
    # against SWI-Prolog (c_lower.pl + launder.pl + c_layouts.pl + ir_text.pl).
    lower_pl = os.path.join(td, 'lower.pl')
    with open(lower_pl, 'w') as f:
        f.write(f"""
:- use_module('{nanofil}/src/c_lex').
:- use_module('{nanofil}/src/c_types').
:- use_module('{nanofil}/src/c_parse').
:- use_module('{nanofil}/src/c_lower').
:- use_module('{nanofil}/src/c_layouts').
:- use_module('{nanofil}/src/ir_text').
:- consult('{files_pl}').

run_all(IrOut, LayOut) :-
    test_files(Files),
    open(IrOut, write, SI),
    open(LayOut, write, SL),
    process(Files, SI, SL),
    close(SI), close(SL).

process([], _, _).
process([F|Fs], SI, SL) :-
    ( catch((c_lex:i_file_tokens(F, Toks), c_parse:c_parse(Toks, Ast)), _, fail) ->
        ( catch(once(c_lower:c_module(Ast, Mod, _, Env)), _E, Mod = err) ->
            ( Mod == err ->
                format(SI, '=== ~w ===~nERR~n', [F]),
                format(SL, '=== ~w ===~nERR~n', [F])
            ; format(SI, '=== ~w ===~n', [F]),
              with_output_to(SI, ir_text:print_module(Mod)),
              c_layouts:module_layouts(Env, Mod, Lays),
              format(SL, '=== ~w ===~n', [F]),
              write_canonical(SL, Lays), write(SL, '.'), nl(SL)
            )
        ; format(SI, '=== ~w ===~nERR~n', [F]),
          format(SL, '=== ~w ===~nERR~n', [F])
        )
    ; format(SI, '=== ~w ===~nSKIP~n', [F]),
      format(SL, '=== ~w ===~nSKIP~n', [F])
    ),
    process(Fs, SI, SL).
""")
    swi_ir = os.path.join(td, 'swi_ir.txt')
    swi_lay = os.path.join(td, 'swi_lay.txt')
    subprocess.run(
        [swipl, '-q', '-s', os.path.join(nanofil, 'src', 'swi', 'compat.pl'),
         '-s', lower_pl, '-g', f"run_all('{swi_ir}','{swi_lay}')", '-t', 'halt'],
        check=True)

    def load_sections_raw(path):
        d = {}
        cur = None
        buf = []
        with open(path, 'rb') as f:
            for line in f:
                if line.startswith(b'=== ') and line.endswith(b' ===\n'):
                    if cur is not None:
                        d[cur] = b''.join(buf)
                    cur = line[4:-5].decode('utf-8')
                    buf = []
                else:
                    buf.append(line)
            if cur is not None:
                d[cur] = b''.join(buf)
        return d

    swi_ir_map = load_sections_raw(swi_ir)
    swi_lay_map = load_sections_raw(swi_lay)
    ir_ok = ir_err = ir_diff = 0
    lay_ok = lay_err = lay_diff = 0
    for cf in cfiles:
        si = swi_ir_map[cf]
        if si.strip() == b'SKIP':
            continue
        ri = subprocess.run([fe, 'cc-ir', cf], capture_output=True)
        if ri.returncode != 0:
            if si.strip() == b'ERR':
                ir_err += 1
            else:
                ir_diff += 1
                if ir_diff <= 5:
                    print(f"CC-IR DIFF (err) {cf}: {ri.stderr.decode(errors='replace').strip()}", file=sys.stderr)
        elif si.strip() == b'ERR' or ri.stdout != si:
            ir_diff += 1
            if ir_diff <= 5:
                print(f"CC-IR DIFF {cf}", file=sys.stderr)
        else:
            ir_ok += 1

        sl = swi_lay_map[cf]
        rl = subprocess.run([fe, 'cc-layouts', cf], capture_output=True)
        if rl.returncode != 0:
            if sl.strip() == b'ERR':
                lay_err += 1
            else:
                lay_diff += 1
                if lay_diff <= 5:
                    print(f"CC-LAYOUTS DIFF (err) {cf}: {rl.stderr.decode(errors='replace').strip()}", file=sys.stderr)
        elif sl.strip() == b'ERR' or rl.stdout != sl:
            lay_diff += 1
            if lay_diff <= 5:
                print(f"CC-LAYOUTS DIFF {cf}", file=sys.stderr)
        else:
            lay_ok += 1

    print(f"cc-ir: {ir_ok} ok + {ir_err} err = {ir_ok + ir_err}/{ir_ok + ir_err + ir_diff}, diffs={ir_diff}")
    print(f"layouts: {lay_ok} ok + {lay_err} err = {lay_ok + lay_err}/{lay_ok + lay_err + lay_diff}, diffs={lay_diff}")

    # Differential check of middle-end optimizer passes (Opt.*) against
    # SWI-Prolog (opt.pl, provenance.pl, promote.pl, copy.pl, alias.pl,
    # simplify.pl, inline.pl, local_storage.pl) on all .ir fixtures and
    # lowered standalone .c modules (including context/2 and cm_attrs).
    irfiles = sorted(glob.glob(os.path.join(nanofil, 'tests', '**', '*.ir'), recursive=True))
    opt_passes = [
        ("promote", ["--pass=promote"], "promote"),
        ("copy", ["--pass=copy"], "copy"),
        ("simplify", ["--pass=simplify"], "simplify"),
        ("inline", ["--pass=inline"], "inline"),
        ("inline_simplified", ["--pass=inline_simplified"], "inline_simplified"),
        ("inline_wide", ["--pass=inline_wide"], "inline_wide(plain, [])"),
        ("inline_wide_simplified", ["--pass=inline_wide_simplified"], "inline_wide(simplified, [])"),
        ("local_storage", ["--pass=local_storage"], "local_storage"),
        ("o1", ["--opt=o1"], "opt(o1)"),
        ("o1_small", ["--opt=o1-small"], "opt(o1(small))"),
        ("o1_none_full", ["-O", "--inline=none", "--simplify=full"], "opt(o1(none, full))"),
        ("o1_small_full", ["-O", "--inline=small", "--simplify=full"], "opt(o1(small, full))"),
        ("o1_wide_full", ["-O", "--inline=wide", "--simplify=full"], "opt(o1(wide([]), full))"),
    ]
    opt_pl = os.path.join(td, 'opt_diff.pl')
    with open(opt_pl, 'w') as f:
        f.write(f"""
:- use_module(library(assoc)).
:- use_module('{nanofil}/src/ir_text').
:- use_module('{nanofil}/src/opt').
:- use_module('{nanofil}/src/alias').
:- use_module('{nanofil}/src/provenance').
:- use_module('{nanofil}/src/c_lex').
:- use_module('{nanofil}/src/c_types').
:- use_module('{nanofil}/src/c_parse').
:- use_module('{nanofil}/src/c_lower').
:- consult('{files_pl}').

run_pass(opt(Opt), M0, M) :- !, opt:optimize(Opt, M0, M).
run_pass(Pass, M0, M) :- opt:optimize_pass(Pass, M0, M).

do_ir(F, OutDir) :-
    ir_text:read_ir_file(F, M0, _),
    M0 = module(Items),
    atom_concat(OutDir, '/alias.txt', AF),
    open(AF, write, SA),
    forall(member(Fn, Items), (
        Fn = func(Name, _, _, _, _) ->
            alias:alias_facts(Fn, Facts),
            assoc_to_list(Facts, Pairs),
            with_output_to(SA, (write_term(Name, [quoted(true)]), write(': '),
                                write_term(Pairs, [quoted(true)]), nl))
        ; true
    )),
    close(SA),
    atom_concat(OutDir, '/vc.txt', VF),
    open(VF, write, SV),
    ( provenance:valid_contexts(Items) -> writeln(SV, ok) ; writeln(SV, invalid) ),
    close(SV),
    forall(pass_spec(Tag, Spec), (
        format(atom(PF), '~w/~w.ir', [OutDir, Tag]),
        open(PF, write, SP),
        once(run_pass(Spec, M0, M)),
        with_output_to(SP, ir_text:print_module(M)),
        close(SP)
    )).

do_c_opt([], _, _).
do_c_opt([F|Fs], Idx, OutDir) :-
    ( catch((c_lex:i_file_tokens(F, Toks), c_parse:c_parse(Toks, Ast),
             once(c_lower:c_module(Ast, Mod, Attrs, _)),
             once(opt:optimize(o1(wide(Attrs), full), Mod, OptMod))), _, fail) ->
        format(atom(OF), '~w/c_~d.ir', [OutDir, Idx]),
        open(OF, write, S),
        with_output_to(S, ir_text:print_module(OptMod)),
        close(S)
    ; true
    ),
    Idx1 is Idx + 1,
    do_c_opt(Fs, Idx1, OutDir).

run_irs([]).
run_irs([F-D|R]) :- do_ir(F, D), run_irs(R).

run_opt_all(IrPairs, COutDir) :-
    run_irs(IrPairs),
    test_files(Fs),
    do_c_opt(Fs, 0, COutDir).
""")
        for tag, _, pl_spec in opt_passes:
            f.write(f"pass_spec('{tag}', {pl_spec}).\n")

    ir_dirs = {}
    ir_pairs = []
    for idx, irf in enumerate(irfiles):
        d = os.path.join(td, f'opt_ir_{idx}')
        os.makedirs(d)
        ir_dirs[irf] = d
        ir_pairs.append(f"'{irf}'-'{d}'")
    c_opt_dir = os.path.join(td, 'opt_c')
    os.makedirs(c_opt_dir)
    subprocess.run(
        [swipl, '-q', '-s', os.path.join(nanofil, 'src', 'swi', 'compat.pl'),
         '-s', opt_pl, '-g',
         f"run_opt_all([{','.join(ir_pairs)}], '{c_opt_dir}')", '-t', 'halt'],
        check=True)

    opt_ok = opt_diff = 0
    for irf in irfiles:
        d = ir_dirs[irf]
        ra = subprocess.run([fe, 'alias', irf], capture_output=True, text=True)
        sa = open(os.path.join(d, 'alias.txt')).read()
        if ra.returncode == 0 and ra.stdout.replace(', ', ',') == sa:
            opt_ok += 1
        else:
            opt_diff += 1
            if opt_diff <= 5:
                print(f"OPT ALIAS DIFF {irf}", file=sys.stderr)
        rv = subprocess.run([fe, 'valid-contexts', irf], capture_output=True)
        sv = open(os.path.join(d, 'vc.txt'), 'rb').read().strip()
        if rv.stdout.strip() == sv and ((sv == b'ok') == (rv.returncode == 0)):
            opt_ok += 1
        else:
            opt_diff += 1
            if opt_diff <= 5:
                print(f"OPT VC DIFF {irf}", file=sys.stderr)
        for tag, flags, _ in opt_passes:
            so = open(os.path.join(d, f'{tag}.ir'), 'rb').read()
            ro = subprocess.run([fe] + flags + ['opt', irf], capture_output=True)
            if ro.returncode == 0 and ro.stdout == so:
                opt_ok += 1
            else:
                opt_diff += 1
                if opt_diff <= 5:
                    print(f"OPT IR DIFF [{tag}] {irf} (rc={ro.returncode})", file=sys.stderr)

    for idx, cf in enumerate(cfiles):
        sof = os.path.join(c_opt_dir, f'c_{idx}.ir')
        if not os.path.exists(sof):
            continue
        so = open(sof, 'rb').read()
        ro = subprocess.run([fe, '-O', '--inline=wide', '--simplify=full', 'cc-ir', cf],
                            capture_output=True)
        if ro.returncode == 0 and ro.stdout == so:
            opt_ok += 1
        else:
            opt_diff += 1
            if opt_diff <= 5:
                print(f"OPT CC-IR DIFF {cf} (rc={ro.returncode})", file=sys.stderr)

    print(f"opt:   {opt_ok}/{opt_ok + opt_diff} exact, diffs={opt_diff}")

    if lex_diff or parse_diff or c23_diffs or pp_diffs or ieee_diffs or tc_diff or ir_diff or lay_diff or opt_diff:
        sys.exit(1)
PY
