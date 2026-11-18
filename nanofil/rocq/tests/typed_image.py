#!/usr/bin/env python3
"""Check typed fixture generation against the Rocq decoder, including the layout step."""
import os
from pathlib import Path
import runpy
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
]
block = 'block(start,[],[' + ','.join(instructions * 5) + '],ret(tmp(a)))'
bytes_ = ','.join([r"'\x80\'", r"'\n'", "'\"'"] * 64)
items = [
    f"func('unit#f.test',export,w,[param(p,tmp(q))],[{block},{block}])",
    "context('unit#f.test',ignored)",
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
    records = run(model, '--gallina', input=source, capture_output=True).stdout
    assert 'LdNarrow Sw' in records and 'RawLoadPointer' in records and 'IOutside' in records
    typed_image(root, 'HiAtexit', records, budget=1200)
    assert list(root.glob('*Blocks*.v')) and (root / 'HiAtexitTypedItems02.v').is_file()
    raw = run(os.environ.get('SWIPL', 'swipl'), ROCQ / 'scripts/gallina.pl', '--chunk',
              'sample', 'typed image test', input=source, capture_output=True).stdout
    (root / 'Reference.v').write_text(raw + '''
From Nanofil Require Import Transport.
From Glibc Require Import HiAtexitCode.
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
    for invalid in ('module([bad]).', 'module([]). module([]).'):
        failed = subprocess.run([model, '--gallina'], input=invalid, text=True, capture_output=True)
        assert failed.returncode != 0 and not failed.stdout, failed
print('Rocq checked the printed AST against decode_module.')
