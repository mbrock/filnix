#!/usr/bin/env python3
"""Check typed fixture generation against the Rocq decoder, including the layout step."""
from dataclasses import replace
import json
import os
from pathlib import Path
import runpy
import shutil
import subprocess
import sys
import tempfile

ROCQ = Path(__file__).resolve().parents[1]
typed = runpy.run_path(str(ROCQ / 'scripts/glibc-code/typed.py'))
model = os.environ['MODEL']
theories = Path(sys.argv[1]).resolve()

# Asymmetric fields expose swapped signedness, offsets or pointer effects.
# Two large blocks force separately compiled block definitions. The first
# function must use separate block files.
instructions = [
    'let(tmp(a),l,raw_load(sw,-3),[tmp(p)])',
    'let(tmp(b),p,raw_load_pointer(5,[aux_read,address_read]),[tmp(q)])',
    'loc(source(unit,7),98765432109876543210)',
    'let(tmp(va),l,va_args,[])',
    'let(tmp(sel),w,select,[tmp(a),const(2),const(3)])',
    'call(void,global(direct),[])',
    'raw_call(void,tmp(indirect),[])',
    'raw_call(result(tmp(r),p),tmp(indirect),[])',
    'local_alloc(stack,16)',
    'raw_store_pointer(-4,tmp(src),tmp(addr),[aux_ensure,lower_barrier,rooted_reload,lower_write,address_write])',
    'raw_store_pointer(8,tmp(other),tmp(addr),[lower_write,address_write])',
    'flight(tmp(p),add,[address(tmp(a)),const(7)],lower(tmp(other)))',
]
block = 'block(start,[phi(tmp(loop),p,[-(start,tmp(q))])],[' + ','.join(instructions * 6) + '],branch(tmp(a),poll(start),done))'
bytes_ = ','.join([r"'\x80\'", r"'\n'", "'\"'"] * 64)
items = [
    f"func('unit#f.test',export,w,[param(p,tmp(q))],[{block},{block}])",
    "context('unit#f.test',ignored)",
    "func(empty,local,void,[],[block(z,[],[],ret),block(u,[],[],unreachable)])",
    "func(mixed,local,void,[],[block(a,[],[raw_store_pointer(3,tmp(v),tmp(p),[lower_write]),"
    "raw_call(void,tmp(fn),[])],goto(poll(a)))])",
    "func(compound_param,local,void,[param(w,tmp(compound(2)))],[block(z,[],[],ret)])",
    "data(ascii,local,1,[item(b,str([a,b,c])),zero(1)])",
    f"data(d,ro(export),16,[item(b,str([{bytes_}])),zero(17),item(p,sym(d,-2)),opaque(7)])",
    "func(outside,export,vector,[],[block(entry,[],[opaque([3,4])],ret)])",
    "alias(alias,weak,'unit#f.test')",
    "alias(another,export,outside)",
    "data(fixture_roots,ro(export),8,[item(p,sym(d,0))])",
] + [f'alias(n{i},weak,d)' for i in range(65)]
source = 'module([' + ','.join(items) + ']).\n'


def run(*args, **kwargs):
    return subprocess.run(args, text=True, check=True, **kwargs)


with tempfile.TemporaryDirectory() as tmp:
    root = Path(tmp)
    for name in ("IRNotation.v", "IRBytes.v"):
        shutil.copy(ROCQ / "glibc" / name, root)
    records = run(model, '--gallina', input=source, capture_output=True).stdout
    assert all(case in records for case in ('LdNarrow Sw', 'RawLoadPointer', 'IOutside', 'func_raw'))
    code = typed['TypedCode'](budget=1200)
    unit = Path('SharedUnit')
    private, group = Path('PrivateUnit'), Path('ImageObjects')
    records = list(typed['records'](records))
    refs = []
    for record in records:
        if record.symbol == b'fixture_roots':
            refs.append((None, record))
        elif record.symbol == b'ascii':
            refs.append(code.add(private, 'Private test object.', record, group=group))
        else:
            refs.append(code.add(unit, 'Shared test object.', record))
    code.add(unit, 'Shared test object.', records[0])
    assert len(code.units[unit]) == len(records) - 2
    try:
        code.add(unit, 'Shared test object.', replace(records[0], body='changed'))
    except ValueError as error:
        assert 'linked copies' in str(error)
    else:
        raise AssertionError('accepted a conflicting copy from the same object')
    ascii_record = next(iter(code.units[private].values()))
    try:
        code.add(private, 'Private test object.', ascii_record)
    except ValueError as error:
        assert 'only one fixture' in str(error)
    else:
        raise AssertionError('accepted use of a grouped object from another fixture')
    code.write_units(root, {Path('.')})
    code.write_view(root, Path('FirstCode'), 'first_image', refs)
    code.write_view(root, Path('SecondCode'), 'second_image', [refs[2], refs[0]])
    assert list(root.glob('*Blocks*.v')) and not list(root.glob('*CodeItems*.v'))
    assert 'Local Definition first_image_items_02' in (root / 'FirstCode.v').read_text()
    assert not (root / 'PrivateUnit.v').exists()
    assert 'Module PrivateUnit.' in (root / 'ImageObjects.v').read_text()
    swipl = os.environ.get('SWIPL', 'swipl')
    raw = run(swipl, ROCQ / 'scripts/gallina.pl', '--chunk',
              'sample', 'typed image test', input=source, capture_output=True).stdout
    (root / 'Reference.v').write_text(raw + """
From Nanofil Require Import Syntax Transport.
From Glibc Require Import FirstCode SecondCode SharedUnit.
Example printer_agrees : decode_module sample_term = Some first_image.
Proof. vm_compute. reflexivity. Qed.
Example selection_reuses_bodies :
  second_image = [IFunc fn_mixed; IFunc fn_unit'23f'2etest] := eq_refl.
""")
    left = root / 'left.term'
    left.write_text("module([data(public,ro(export),8,[item(p,sym(private,0))]),"
                    "data(private,local,8,[]),data(dead,local,8,[]),data(winner,weak,8,[])]).")
    right = root / 'right.term'
    right.write_text("module([data(winner,export,8,[]),alias(entry,export,public)]).")
    origins = root / 'origins.json'
    link = [swipl, ROCQ / 'scripts/link.pl']
    specs = ['entry,winner', f'left={left}', f'right={right}']
    plain = run(*link, *specs, capture_output=True).stdout
    tracked = run(*link, '--origins', origins, *specs, capture_output=True).stdout
    assert plain == tracked
    assert json.loads(origins.read_text()) == [
        [str(left), 'public'], [str(left), 'left#private'], [str(right), 'winner'], [str(right), 'entry'],
    ]
    flags = ['-R', str(theories), 'Nanofil', '-R', '.', 'Glibc']
    sources = {p.name for p in root.glob('*.v')}
    order = run('rocq', 'dep', '-sort', *flags, *sorted(sources),
                cwd=root, stdout=subprocess.PIPE).stdout.split()
    for filename in order:
        if filename in sources:
            run('rocq', 'c', '-q', *flags, filename, cwd=root)
    assert (root / 'Reference.vo').is_file()
    # Reparse Rocq's own output. An unfamiliar store must keep its effect list
    # while the surrounding function, call and polling edge still use SSA.
    imports = '''From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
From Glibc Require Import IRNotation SharedUnit.
'''
    symbol = 'fn_mixed'
    (root / 'Display.v').write_text(imports + f'Redirect "display" Print {symbol}.\n')
    run('rocq', 'c', '-q', '-output-directory', '.', *flags, 'Display.v', cwd=root)
    printed = (root / 'display.out').read_text().split('=', 1)[1].rsplit(': func', 1)[0].strip()
    for spelling in ('ir_fn{', '@"a"', 'RawStorePointer', 'LowerWrite', 'rawcall', 'goto poll'):
        assert spelling in printed, printed
    (root / 'RoundTrip.v').write_text(imports + f'Definition reparsed : func := {printed}.\n'
                                      f'Example same : reparsed = {symbol} := eq_refl.\n')
    run('rocq', 'c', '-q', *flags, 'RoundTrip.v', cwd=root)

    projected = run(model, '--placement', 'unit#f.test', 'alias', 'ascii', input=source, capture_output=True)
    assert projected.stdout.splitlines() == ['("unit#f.test", 65536, 65536)', '("alias", 65536, 65536)',
                                             '("ascii", 65600, 65608)']
    missing = subprocess.run([model, '--placement', 'missing'], input=source, text=True, capture_output=True)
    assert missing.returncode != 0 and 'missing symbol' in missing.stderr
    for mode in ('--gallina', '--placement'):
        for invalid in ('module([bad]).', 'module([]). module([]).'):
            failed = subprocess.run([model, mode], input=invalid, text=True, capture_output=True)
            assert failed.returncode != 0 and not failed.stdout, failed
print('Rocq checked both typed views and the extracted decoder’s Gallina output.')
