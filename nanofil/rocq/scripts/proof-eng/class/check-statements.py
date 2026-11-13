#!/usr/bin/env python3
"""Check headline source statements, modulo module qualification."""
import pathlib
import re
import sys

original, generated = map(pathlib.Path, sys.argv[1:])
for path, names in [
    ('hello/HelloGlibcJoin.v', ['hello_never_panics']),
    ('hi_atexit/HiAtexitSafe.v', ['hi_atexit_initialized_entry', 'hi_atexit_never_panics']),
]:
    for name in names:
        statements = []
        for root in (original, generated):
            source = (root / path).read_text()
            statement = re.search(r'(?:Theorem|Lemma) ' + name + r'\b.*?(?=Proof\.)', source, re.S)[0]
            statement = re.sub(r'\(rt := interp_runtime\)', '', statement)
            statement = re.sub(r'\b(?:[A-Z]\w*\.)+', '', statement)
            statements.append(re.sub(r'\s+', '', statement))
        assert statements[0] == statements[1], name
        print(name + ': unchanged modulo module paths and explicit interpreter instance')
