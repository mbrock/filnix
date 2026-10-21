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


def download(projeny, directory, urls):
    """Fetch the first mirror whose download matches its hash, as Projeny's
    setup does, and return the archive's file name."""
    for url, digest in urls:
        name = url.split('#', 1)[0].split('?', 1)[0].rstrip('/').rsplit('/', 1)[-1]
        if not name or name.startswith('.'):
            raise ValueError(f'Unsupported URL: {url!r}')
        if subprocess.run([projeny, 'download', url, digest], cwd=directory).returncode == 0:
            return name
        print(f'{url}: download failed, trying the next mirror', file=sys.stderr)
    raise SystemExit('No URL: mirror yielded the archive')


def extract(descriptor, repo, output, rev):
    script = Path(__file__).with_name('extract-patch.sh').resolve()
    repo, output = Path(repo).resolve(), Path(output).resolve()
    local_patches = (script.parent.parent / 'patches').resolve()
    if output == local_patches or local_patches in output.parents:
        raise SystemExit('patches/ contains local patches; extract into ports/patch/ or a review directory')
    projeny = shutil.which(os.environ.get('PROJENY', 'projeny'))
    if not projeny:
        raise SystemExit('Projeny is required: run this importer with nix develop -c make -C ports')
    def blob(name):
        return subprocess.check_output(['git', '-C', str(repo), 'show', f'{rev}:projects/{name}'])
    data = blob(descriptor)
    fields, urls = {}, []
    for line in data.decode().splitlines():
        if not line:
            break  # Headers end at the first blank line.
        if line.startswith('URL: '):
            url, _, digest = line[5:].partition(' ')
            urls.append((url, digest))
        for key in ('Archive', 'Origname', 'Name'):
            if line.startswith(key + ': '):
                fields[key] = line[len(key) + 2:]
    # A project names a tarball checked in beside it, or mirrors to download
    # it from, each with the blake3 hash Projeny verifies.
    if bool(urls) == ('Archive' in fields):
        raise ValueError(f'{descriptor} needs exactly one of Archive: or URL:')
    for key in ('Origname', 'Name') + (() if urls else ('Archive',)):
        value = fields.get(key, '')
        if not value or '/' in value or value.startswith('.'):
            raise ValueError(f'Unsupported {key}: {value!r}')
    project = fields['Origname']
    # Upstream may keep a directory port of the same release beside the
    # Projeny port (projects/openssl-3.6.4/ uses SaRCAsm, openssl.projeny
    # zunsafe forwarders). Name this patch apart rather than overwrite it.
    kind = subprocess.run(['git', '-C', str(repo), 'cat-file', '-t', f'{rev}:projects/{project}'],
                          capture_output=True, text=True).stdout.strip()
    name = project + ('-projeny' if kind == 'tree' else '') + '.patch'
    with tempfile.TemporaryDirectory(prefix='filnix-projeny-') as tmp:
        root = Path(tmp)
        (root / descriptor).write_bytes(data)
        if urls:
            fields['Archive'] = download(projeny, root, urls)
        else:
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
        destination = output / name
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
