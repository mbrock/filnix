#!/usr/bin/env python3
"""Check typed fixture generation against the Rocq decoder, including the layout step."""
import os
from pathlib import Path
import runpy
import shutil
import subprocess
import sys
import tempfile

ROCQ = Path(__file__).resolve().parents[1]
typed_image = runpy.run_path(str(ROCQ / 'scripts/glibc-code/typed.py'))['typed_image']
model = os.environ['MODEL']
theories = Path(sys.argv[1]).resolve()

# Asymmetric fields expose swapped signedness, offsets or pointer effects.
# Two large blocks force separately compiled block definitions. The repeated
# symbol and the compound name must still occupy distinct list positions.
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
    "func(compound(2),local,void,[],[block(z,[],[],goto(poll(z)))])",
    "data(ascii,local,1,[item(b,str([a,b,c])),zero(1)])",
    f"data(d,ro(export),16,[item(b,str([{bytes_}])),zero(17),item(p,sym(d,-2)),opaque(7)])",
    "func(outside,export,vector,[],[block(entry,[],[opaque([3,4])],ret)])",
    "alias(alias,weak,'unit#f.test')",
    "alias(d,export,outside)",
    "alias(compound(1),other,d)",
] + [f'alias(n{i},weak,d)' for i in range(65)]
source = 'module([' + ','.join(items) + ']).\n'


def run(*args, **kwargs):
    return subprocess.run(args, text=True, check=True, **kwargs)


with tempfile.TemporaryDirectory() as tmp:
    root = Path(tmp)
    for name in ("IRNotation.v", "IRBytes.v"):
        shutil.copy(ROCQ / "glibc" / name, root)
    records = run(model, '--gallina', input=source, capture_output=True).stdout
    assert 'LdNarrow Sw' in records and 'RawLoadPointer' in records and 'IOutside' in records
    typed_image(root, 'HiAtexit', records, budget=1200)
    assert list(root.glob('*Blocks*.v')) and (root / 'HiAtexitTypedItems02.v').is_file()
    raw = run(os.environ.get('SWIPL', 'swipl'), ROCQ / 'scripts/gallina.pl', '--constructors', '--chunk',
              'sample', 'typed image test', input=source, capture_output=True).stdout
    captured = run(os.environ.get('SWIPL', 'swipl'), ROCQ / 'scripts/gallina.pl',
                   '--chunk', 'captured', 'transport notation test', input=source, capture_output=True).stdout
    (root / 'Captured.v').write_text(captured)
    (root / 'Reference.v').write_text(raw + '''
From Nanofil Require Import Transport.
From Glibc Require Import HiAtexitCode Captured.
Example transport_agrees : captured_term = sample_term := eq_refl.
Example printer_agrees : decode_module sample_term = Some hi_decoded.
Proof. vm_compute. reflexivity. Qed.
''')
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
From Glibc Require Import IRNotation HiAtexitTypedMI.
'''
    symbol = 'hi_fn_mixed'
    (root / 'Display.v').write_text(imports + f'Redirect "display" Print {symbol}.\n')
    run('rocq', 'c', '-q', '-output-directory', '.', *flags, 'Display.v', cwd=root)
    printed = (root / 'display.out').read_text().split('=', 1)[1].rsplit(': func', 1)[0].strip()
    for spelling in ('ir_fn{', '@"a"', 'RawStorePointer', 'LowerWrite', 'rawcall', 'goto poll'):
        assert spelling in printed, printed
    (root / 'RoundTrip.v').write_text(imports + f'Definition reparsed : func := {printed}.\n'
                                      f'Example same : reparsed = {symbol} := eq_refl.\n')
    run('rocq', 'c', '-q', *flags, 'RoundTrip.v', cwd=root)

    for invalid in ('module([bad]).', 'module([]). module([]).'):
        failed = subprocess.run([model, '--gallina'], input=invalid, text=True, capture_output=True)
        assert failed.returncode != 0 and not failed.stdout, failed
print('Rocq checked the printed AST against decode_module.')
