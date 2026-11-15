#!/usr/bin/env python3
"""Refuse unauthorized assumptions with token scopes and legacy line filters."""
import re
import sys
import time
import argparse
from pathlib import Path

DECL = set('Axiom Axioms Parameter Parameters Conjecture Conjectures'.split())
LOCAL = set('Variable Variables Hypothesis Hypotheses Context'.split())
WORD = re.compile(r"[A-Za-z_][\w']*|:=")
PARAMETERS = {
    ('hello/HelloGlibcLibsCleanup.v', 'HelloLibsCleanupSig'): {'libs_cleanup'},
    ('hello/HelloGlibcLibsExit.v', 'HelloLibsExitSig'): {'libs_exit'},
    ('hello/HelloGlibcLibsName.v', 'HelloLibsNameSig'): {'libs_name'},
    ('hello/HelloGlibcLibsStr.v', 'HelloLibsStrSig'): {'libs_mbszero', 'libs_strlen', 'libs_strncmp', 'libs_errno'},
    ('hello/HelloGlibcLibsSys.v', 'HelloLibsSysSig'): {'libs_xmalloc', 'libs_free', 'libs_atexit', 'libs_ignores'},
    ('hello/HelloGlibcMainLibs.v', 'HelloMainLibsSig'): {'hello_libs'},
    ('hello/HelloGlibcMainNameSearch.v', 'HelloNameSearchSig'): {'name_memrchr', 'name_memcmp'},
    ('hello/HelloGlibcMainStreams.v', 'HelloWorldSig'): {'os_wi_stable'},
    ('hi_atexit/HiAtexitCleanup.v', 'HiCleanupSig'): {'hi_cleanup_rule'},
}
# Under theories, only these module types may declare assumptions. InterpRuntime
# supplies Runtime's fields; HelloMain and HelloJoin supply their bases' fields
# when they include their proof phases.
THEORY_SIGNATURES = {
    ('theories', 'core', 'Runtime.v'): 'Runtime',
    ('theories', 'hello_contracts', 'HelloMainInterface.v'): 'HelloMainBase',
    ('theories', 'hello_contracts', 'HelloJoinInterface.v'): 'HelloJoinBase',
}

def tokens(text):
    i, line, depth = 0, 1, 0
    while i < len(text):
        if text.startswith('(*', i):
            depth += 1
            i += 2
        elif depth and text.startswith('*)', i):
            depth -= 1
            i += 2
        elif depth:
            line += text[i] == '\n'
            i += 1
        elif text[i] == '"':
            i += 1
            while i < len(text):
                if text.startswith('""', i):
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    line += text[i] == '\n'
                    i += 1
            yield '<string>', line
        else:
            m = WORD.match(text, i)
            if m:
                yield m[0], line
                i += len(m[0])
            else:
                c = text[i]
                if c == '.' and (i + 1 == len(text) or text[i+1].isspace() or text.startswith('(*', i+1)):
                    yield '<end>', line
                elif not c.isspace():
                    yield c, line
                line += c == '\n'
                i += 1
    if depth:
        raise ValueError('unterminated comment')

def scan(path, abstract_fix=None):
    stack, command, errors = [], [], []
    parts = path.resolve().parts
    namespace = next((p for p in reversed(parts[:-1]) if p in {'theories', 'glibc'}), 'glibc')
    text = path.read_text()
    # Preserve the old line filters' rejections, including comments and strings.
    skip = None
    for line, raw in enumerate(text.splitlines(), 1):
        if namespace == 'glibc':
            opening = re.match(r'^Module Type [A-Za-z0-9_]', raw)
            if skip is None and opening:
                skip = re.split(r'[ .(]', raw.split()[2], maxsplit=1)[0]
                continue
            if skip is not None:
                if raw.startswith(f'End {skip}.'):
                    skip = None
                continue
        else:
            if re.search(r'\bAdmitted\b', raw):
                errors.append(f'{path}:{line}: legacy filter forbids Admitted')
            allowed = THEORY_SIGNATURES.get(parts[-3:])
            if allowed:
                if re.match(rf'Module Type {allowed}\b', raw):
                    skip = allowed
                if skip:
                    if raw.startswith(f'End {skip}.'):
                        skip = None
                    continue
        if re.search(r'\b(?:Admitted|Axiom|Axioms|Parameter|Conjecture)\b', raw):
            errors.append(f'{path}:{line}: legacy assumption filter rejection')
    def inspect(cmd):
        words = [w for w, _ in cmd]
        if not words:
            return
        signature = any(k == 'signature' for k, _ in stack)
        signatures = [n for k, n in stack if k == 'signature']
        theory_signature = parts[-3:] in THEORY_SIGNATURES and signatures == [THEORY_SIGNATURES[parts[-3:]]]
        section = any(k == 'section' for k, _ in stack)
        for i in range(len(words) - 1):
            if words[i:i+2] == ['Declare', 'Module']:
                named_site = (
                    parts[-3:] == ('glibc', 'hello', 'HelloGlibcMainLibsCalls.v')
                    and signatures == ['HelloLibsCallsSig']
                    and words[i:] in [
                        ['Declare', 'Module', 'ST', ':', 'HelloLibsStrSig', 'D'],
                        ['Declare', 'Module', 'NM', ':', 'HelloLibsNameSig', 'D'],
                    ]
                )
                if not named_site and not theory_signature and (abstract_fix is None or path.resolve() != Path(abstract_fix).resolve()):
                    errors.append(f'{path}:{cmd[i][1]}: forbidden Declare Module')
        for i, (w, line) in enumerate(cmd):
            declaration_allowed = theory_signature if namespace == 'theories' else signature
            if w in {'Parameter', 'Parameters'}:
                fields = words[i+1:words.index(':', i+1)] if ':' in words[i+1:] else []
                listed = PARAMETERS.get(('/'.join(parts[-2:]), signatures[0]), set()) if len(signatures) == 1 and parts[-3] == 'glibc' else set()
                declaration_allowed = theory_signature or bool(fields) and set(fields) <= listed
            if w in {'admit', 'Admitted'} or (w in DECL and not declaration_allowed) or (w in LOCAL and not signature and not section):
                errors.append(f'{path}:{line}: forbidden {w}')
        # Do not let an unsupported wrapper leave the scope stack stale.
        if words[0] in {'Time', 'Timeout', 'Redirect', 'Fail', 'Succeed', 'Local', 'Global', '#'} and any(w in {'Module', 'End', 'Section'} for w in words):
            errors.append(f'{path}:{cmd[0][1]}: unsupported wrapped scope command')
        if words[0] == 'Section':
            stack.append(('section', words[1]))
        elif words[:2] == ['Module', 'Type'] and ':=' not in words:
            stack.append(('signature', words[2]))
        elif words[0] == 'Module' and ':=' not in words:
            j = 2 if words[1] in {'Import', 'Export'} else 1
            stack.append(('module', words[j]))
        elif words[0] == 'End':
            if not stack or stack[-1][1] != words[1]:
                errors.append(f'{path}:{cmd[0][1]}: unmatched End {words[1]}')
            else:
                stack.pop()
    for token in tokens(text):
        if token[0] == '<end>':
            inspect(command)
            command = []
        else:
            command.append(token)
    inspect(command)
    if stack:
        errors.append(f'{path}: unclosed scopes: {stack}')
    return errors

if __name__ == '__main__':
    start = time.monotonic()
    parser = argparse.ArgumentParser()
    parser.add_argument('--abstract-fix', type=Path)
    parser.add_argument('paths', nargs='+', type=Path)
    args = parser.parse_args()
    paths = sorted({p for arg in args.paths for p in (arg.rglob('*.v') if arg.is_dir() else [arg])})
    errors = [e for path in paths for e in scan(path, args.abstract_fix)]
    print('\n'.join(errors))
    print(f'{len(paths)} files; {len(errors)} findings; {time.monotonic()-start:.3f}s', file=sys.stderr)
    sys.exit(bool(errors))
