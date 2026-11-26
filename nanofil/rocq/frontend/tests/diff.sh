#!/usr/bin/env bash
# Byte-for-byte differential check of nanofil-frontend (CLex.v + CParse.v +
# CCanon.v) against SWI-Prolog (nanofil/src/c_lex.pl + c_types.pl + c_parse.pl)
# across all C test fixtures and C23 fixtures.
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

    if lex_diff or parse_diff or c23_diffs:
        sys.exit(1)
PY
