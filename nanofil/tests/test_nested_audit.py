import json
import subprocess
import tempfile
import time
from pathlib import Path

root = Path(__file__).resolve().parent
cases = {
    'Bad': 'Module Type S. Parameter p : False. End S. Module Bad : S. Axiom hidden : False. Lemma helper : False. Proof. exact hidden. Qed. Lemma p : False. Proof. exact helper. Qed. End Bad.',
    'Clean': 'Module Type S. Parameter p : True. End S. Module Good : S. Lemma helper : True. Proof. exact I. Qed. Lemma p : True. Proof. exact helper. Qed. End Good.',
    'Data': 'Definition data := 1.',
    'Nested': 'Module Outer. Module Inner. Lemma p : True. Proof. exact I. Qed. End Inner. End Outer.',
    'DefinitionProof': 'Definition p : True. Proof. exact I. Defined.',
    'BracedProof': 'Lemma p : True. Proof. { exact I. } Qed.',
}
start = time.monotonic()
scratch = tempfile.TemporaryDirectory()
for name, text in cases.items():
    work = Path(scratch.name) / name
    (work / 'glibc').mkdir(parents=True, exist_ok=True)
    (work / 'theories').mkdir(exist_ok=True)
    source = work / 'glibc' / f'{name}.v'
    source.write_text(text)
    subprocess.run(['rocq', 'c', '-q', '-R', 'glibc', 'Glibc', str(source)], cwd=work, check=True)
    command = ['python3', str(root / 'rocq_runtime_audit.py'), str(source), str(source.with_suffix('.glob')), str(work / 'audit')]
    result = subprocess.run(command, cwd=work, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if name == 'Bad':
        assert result.returncode != 0 and 'unexpected assumptions' in result.stdout and '.hidden' in result.stdout, result.stdout
    else:
        assert result.returncode == 0, result.stdout
        coverage = json.loads((work / 'audit/coverage.json').read_text())
        expected = 0 if name == 'Data' else 2 if name == 'Clean' else 1
        assert coverage['source_count'] == expected, coverage
        assert len(coverage['queried']) == (0 if name == 'Data' else 1), coverage
        assert len(coverage['covered_through_users']) == (1 if name == 'Clean' else 0), coverage
    print(name, result.stdout.strip())
    if name == 'Nested':
        glob = source.with_suffix('.glob')
        original = glob.read_text()
        glob.write_text('\n'.join(line for line in original.splitlines() if not line.startswith('prf ')))
        result = subprocess.run(command, cwd=work, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        assert result.returncode != 0 and 'absent from glob' in result.stdout, result.stdout
        print('Missing nested entry rejected:', result.stdout.strip())
        glob.write_text(original)
scratch.cleanup()
print(f'elapsed={time.monotonic()-start:.3f}s')
