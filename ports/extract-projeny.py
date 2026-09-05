#!/usr/bin/env python3
"""Materialize a pinned Projeny port, then reuse the ordinary patch filters."""
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


def run(*args, **kwargs):
    return subprocess.run(args, check=True, **kwargs)


def extract(descriptor, repo, output, rev):
    script = Path(__file__).with_name('extract-patch.sh').resolve()
    repo, output = Path(repo).resolve(), Path(output).resolve()
    projeny = shutil.which(os.environ.get('PROJENY', 'projeny'))
    if not projeny:
        raise SystemExit('Projeny is required: run this importer with nix develop -c make -C ports')
    def blob(name):
        return subprocess.check_output(['git', '-C', str(repo), 'show', f'{rev}:projects/{name}'])
    data = blob(descriptor)
    fields = {}
    for line in data.decode().splitlines():
        if line.startswith('diff --git '):
            break
        for key in ('Archive', 'Origname', 'Name'):
            if line.startswith(key + ': '):
                fields[key] = line[len(key) + 2:]
    for key in ('Archive', 'Origname', 'Name'):
        value = fields.get(key, '')
        if not value or '/' in value or value.startswith('.'):
            raise ValueError(f'Unsupported {key}: {value!r}')
    project = fields['Origname']
    with tempfile.TemporaryDirectory(prefix='filnix-projeny-') as tmp:
        root = Path(tmp)
        (root / descriptor).write_bytes(data)
        (root / fields['Archive']).write_bytes(blob(fields['Archive']))
        original = root / 'original'
        original.mkdir()
        run('tar', 'xf', str(root / fields['Archive']), '-C', str(original))
        reconstructed = root / 'ported'
        run(projeny, 'extract', str(root / descriptor), str(reconstructed))
        history = root / 'history'
        (history / 'projects').mkdir(parents=True)
        target = history / 'projects' / project
        shutil.move(original / project, target)
        env = dict(os.environ, GIT_AUTHOR_NAME='Filnix importer', GIT_AUTHOR_EMAIL='import@invalid',
                   GIT_COMMITTER_NAME='Filnix importer', GIT_COMMITTER_EMAIL='import@invalid')
        def git(*args):
            run('git', '-C', str(history), *args, env=env, stdout=subprocess.DEVNULL)
        git('init', '-q')
        git('add', '-f', '.')
        git('-c', 'commit.gpgsign=false', 'commit', '-qm', 'Original release')
        shutil.rmtree(target)
        shutil.move(reconstructed, target)
        git('add', '-f', '-A')
        git('-c', 'commit.gpgsign=false', 'commit', '--allow-empty', '-qm', 'Projeny port')
        review = root / 'patches'
        run(str(script), project, str(history), str(review), 'HEAD')
        patch = review / (project + '.patch')
        output.mkdir(parents=True, exist_ok=True)
        destination = output / patch.name
        if not patch.exists():
            destination.unlink(missing_ok=True)
        else:
            if any(line.startswith(b'Binary files ') for line in patch.read_bytes().splitlines()):
                raise SystemExit('Binary changes cannot be applied by the Nix patch phase; use the materialized Projeny source')
            with tempfile.NamedTemporaryFile(dir=output, delete=False) as out:
                temporary = Path(out.name)
                out.write(patch.read_bytes())
            try:
                temporary.chmod(0o644)
                temporary.replace(destination)
            finally:
                temporary.unlink(missing_ok=True)


if __name__ == '__main__':
    extract(*sys.argv[1:])
