#!/usr/bin/env python3
"""Pin the ports tree and hash its native Projeny tool without building Fil-C."""
import argparse
import json
from pathlib import Path
import subprocess
import tempfile

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--repo', type=Path, default=Path.home() / 'fil-c')
parser.add_argument('--rev', required=True)
args = parser.parse_args()
rev = subprocess.check_output(['git', '-C', str(args.repo), 'rev-parse', '--verify',
                               args.rev + '^{commit}'], text=True).strip()
with tempfile.TemporaryDirectory(prefix='filnix-ports-pin-') as tmp:
    root = Path(tmp)
    archive = root / 'source.tar'
    with archive.open('wb') as out:
        subprocess.run(['git', '-C', str(args.repo), 'archive', rev, 'projects/projeny'],
                       stdout=out, check=True)
    source = root / 'source'
    source.mkdir()
    subprocess.run(['tar', 'xf', str(archive), '-C', str(source)], check=True)
    if not (source / 'projects/projeny/Makefile').is_file():
        raise SystemExit('Selected revision does not contain Projeny')
    hash_value = subprocess.check_output(['nix', 'hash', 'path', str(source)], text=True).strip()
pin = Path(__file__).resolve().parents[1] / 'ports/upstream.json'
new = dict(portsRev=rev, projenyHash=hash_value)
with tempfile.NamedTemporaryFile(mode='w', dir=pin.parent, delete=False) as out:
    json.dump(new, out, indent=2)
    out.write('\n')
    temporary = Path(out.name)
try:
    temporary.chmod(0o644)
    temporary.replace(pin)
finally:
    temporary.unlink(missing_ok=True)
print(json.dumps(new, indent=2))
