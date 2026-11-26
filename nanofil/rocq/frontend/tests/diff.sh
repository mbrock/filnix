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

    if lex_diff or parse_diff or c23_diffs or pp_diffs:
        sys.exit(1)
PY
