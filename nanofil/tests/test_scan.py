import re
import subprocess
import tempfile
from pathlib import Path
from assumption_scan import PARAMETERS, scan

bad = {
    **{word: f'Module Bad. {word} hidden : False. End Bad.' for word in
       'Axiom Axioms Parameter Parameters Conjecture Conjectures Variable Variables Hypothesis Hypotheses'.split()},
    'admitted': 'Lemma bad : False. Admitted.',
    'admit': 'Lemma bad : False. Proof. admit. Qed.',
    'top-level declared module': 'Module Type S. Parameter p : False. End S. Declare Module X : S.',
    'plain-module declared module': 'Module Type S. Parameter p : False. End S. Module Bad. Declare Module X : S. End Bad.',
    'after nested signature': 'Module Type S. Module Type T. Parameter p : False. End T. End S. Declare Module X : S.',
    'wrapped end fails closed': 'Module Type S. Parameter p : False. Time End S. Axiom hidden : False.',
    'signature admission': 'Module Type S. Lemma p : False. Admitted. End S.',
    'inline signature': 'Module Type S. Parameter p : False. End S. Module Bad : S. Axiom hidden : False. Lemma p : False. Proof. exact hidden. Qed. End Bad.',
    'hidden later axiom': 'Module Type S. Parameter p : False. End S. Module Bad : S. Axiom hidden : False. Lemma helper : False. Proof. exact hidden. Qed. Lemma p : False. Proof. exact helper. Qed. End Bad.',
    'unlisted signature': 'Module Type S. Parameter p : False. End S.',
    'unlisted signature submodule': 'Module Type T. Declare Module X : S. End T.',
    'nested signature submodule': 'Module Outer. Module Type T. Module Type U. Declare Module X : S. End U. End T. End Outer.',
    'legacy comments': '(* Axiom x : False. (* Admitted. *) *)',
    'legacy strings': 'Definition s := "Axiom x : False. Admitted.".',
}
good = {
    'inline signature': 'Module Type S. Definition p := True. End S.',
    'nested signature': 'Module Type S. Module Type T. Definition p := True. End T. End S.',
    'section': 'Section S. Variables A : Type. Hypotheses p : A. End S.',
    'End hypothesis name': 'Lemma p : True. Proof. pose proof I as End. exact End. Qed.',
    'proved sealed': 'Module Type S. Definition p := True. End S. Module Good : S. Definition p := True. Lemma helper : True. Proof. exact I. Qed. End Good.',
}
with tempfile.TemporaryDirectory() as d:
    p = Path(d) / 'Fixture.v'
    for expected, cases in [(True, bad), (False, good)]:
        for name, text in cases.items():
            p.write_text(text)
            findings = scan(p)
            assert bool(findings) == expected, (name, findings)
            print(f'PASS {name}: {len(findings)} findings')
    old_awk = r'''skip == "" && /^Module Type [A-Za-z0-9_]/ { skip = $3; sub(/[ .(].*/, "", skip); next }
skip != "" { if ($0 ~ "^End " skip "\\.") skip = ""; next }
{ print }'''
    for namespace in ['theories', 'glibc']:
        p = Path(d) / namespace / 'Fixture.v'
        p.parent.mkdir(exist_ok=True)
        for name, text in {**bad, **good}.items():
            p.write_text(text)
            filtered = subprocess.check_output(['awk', old_awk, str(p)], text=True) if namespace == 'glibc' else text
            old_rejected = bool(re.search(r'\b(?:Admitted|Axiom|Axioms|Parameter|Conjecture)\b', filtered))
            assert not old_rejected or scan(p), (namespace, name)
    p = Path(d) / 'glibc/Fixture.v'
    p.write_text('Module Type S. Axiom p : False. End S.\nModule Bad : S.\nAxiom hidden : False.\nEnd Bad.')
    assert not subprocess.check_output(['awk', old_awk, str(p)], text=True).strip()
    assert any(':3: forbidden Axiom' in e for e in scan(p)), scan(p)
    print('PASS old-filter rejection containment and inline skip fail-first control')
    p.write_text('Declare Module R : Runtime.')
    assert not scan(p, abstract_fix=p)
    assert scan(p, abstract_fix=Path(d) / 'different.v')
    p.write_text('Axiom hidden : False.')
    assert scan(p, abstract_fix=p)
    print('PASS generated-path exemption is exact and only permits Declare Module')
    for (file, signature), fields in PARAMETERS.items():
        p = Path(d) / 'glibc' / file
        p.parent.mkdir(parents=True, exist_ok=True)
        for field in fields:
            p.write_text(f'Module Type {signature}. Parameter {field} : True. End {signature}.')
            assert not scan(p), (p, scan(p))
        p.write_text(f'Module Type {signature}. Parameter new_field : True. End {signature}.')
        assert scan(p)
    p = Path(d) / 'theories/core/Runtime.v'
    p.parent.mkdir(parents=True)
    p.write_text('Module Type Runtime.\nParameter state : Type.\nEnd Runtime.')
    assert not scan(p)
    p.write_text('Module Type Other.\nParameter state : Type.\nEnd Other.')
    assert scan(p)
    p = Path(d) / 'glibc/hello/HelloGlibcMainLibsCalls.v'
    for field, sig in [('ST', 'HelloLibsStrSig'), ('NM', 'HelloLibsNameSig')]:
        p.write_text(f'Module Type HelloLibsCallsSig. Declare Module {field} : {sig} D. End HelloLibsCallsSig.')
        assert not scan(p), scan(p)
        p.write_text(f'Module Type Other. Declare Module {field} : {sig} D. End Other.')
        assert scan(p)
    print('PASS exact Runtime, 16 fields, and two submodule sites; new sites refused')
print(f'{len(bad)} negative and {len(good)} positive scanner fixtures passed')
