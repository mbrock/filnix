#!/usr/bin/env python3
"""Migrate OS program contexts using argument metadata from compiled Rocq files.

The forty reviewed intermediate audits use bundled statements under their
original names. check/audit-changes.json identifies those exact declarations.
Other audited public names retain their interfaces; any necessary wrapper
uses an implementation named FILE_NAME_program, with the suffix _program.

PE_PROGRAM_TARGETS can name .vo targets for a partial audit. Only their Rocq
dependency closure is compiled and converted; normal runs process the full tree.
An in-place run retains the compiled input in TREE.program/before.

After cutover, edit a program table and run --refresh-tables TREE to regenerate
its indexed instances. Existing exported names remain; a new row needs no
hand-written instance. Compile the tree again to check its certificate.
"""
from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, field
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import time


HERE = Path(__file__).resolve().parents[1]
PROTECTED = {name for group in json.loads((HERE / 'check/audit-contracts.json').read_text()).values() for name in group}


def reviewed_audit(file, name):
    review = json.loads((HERE / 'check/audit-changes.json').read_text())
    if review['version'] != 1 or review['stage'] != '50-program':
        raise ValueError('50-program: unsupported audit review')
    return any(d['file'] == str(file) and d['name'] == name for d in review['declarations'])


def protected_name(name):
    # The audit-layout generator prefixes query-local declarations to avoid
    # namespace collisions. Their contracts remain protected after renaming.
    leaf = name.split('.')[-1]
    return any(leaf == target or leaf.endswith('_' + target) for target in PROTECTED)


@dataclass
class Token:
    text: str
    start: int
    end: int


def tokens(source: str) -> list[Token]:
    """Lex Gallina/Ltac without losing source positions or reading comments."""
    result = []
    i = 0
    while i < len(source):
        if source[i].isspace():
            i += 1
            continue
        start = i
        if source.startswith('(*', i):
            depth = 1
            i += 2
            while depth and i < len(source):
                if source.startswith('(*', i):
                    depth += 1
                    i += 2
                elif source.startswith('*)', i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            if depth:
                raise ValueError('unterminated comment')
            continue
        if source[i] == '"':
            i += 1
            while i < len(source):
                if source[i] == '"':
                    i += 1
                    if i < len(source) and source[i] == '"':
                        i += 1
                        continue
                    break
                i += 1
        elif source[i].isalpha() or source[i] == '_':
            i += 1
            while i < len(source):
                if source[i].isalnum() or source[i] in "_'":
                    i += 1
                elif source[i] == '.' and i + 1 < len(source) and (source[i+1].isalpha() or source[i+1] == '_'):
                    i += 1
                else:
                    break
        elif source[i].isdigit() or (source[i] == '.' and i + 1 < len(source) and source[i+1].isdigit()):
            i += 1
            while i < len(source) and source[i].isdigit():
                i += 1
        else:
            operator = next((op for op in (':=', '->', '<-', '=>', '-∗', '|-', '::', '/\\', '\\/', '<=', '>=', '<>') if source.startswith(op, i)), None)
            i += len(operator) if operator else 1
        result.append(Token(source[start:i], start, i))
    return result


def sentences(ts: list[Token]) -> list[list[Token]]:
    result = []
    start = 0
    for i, t in enumerate(ts):
        if t.text == '.' and (i + 1 == len(ts) or t.end < ts[i+1].start):
            result.append(ts[start:i+1])
            start = i + 1
    if start != len(ts):
        raise ValueError('source does not end in a sentence')
    return result


def normalized(ts: list[Token]) -> str:
    return ' '.join(t.text for t in ts)


@dataclass
class Section:
    name: str
    start: int
    end: int = 0
    contexts: list[list[Token]] = field(default_factory=list)
    declarations: list[str] = field(default_factory=list)
    iris: list[Token] | None = None
    canonical: bool = False
    reason: str = ''
    scope: tuple[str, ...] = ()


@dataclass
class Source:
    path: Path
    text: str
    ts: list[Token]
    sections: list[Section]
    declarations: dict[str, list[Token]]
    references: dict[int, str] = field(default_factory=dict)


def groups(ts: list[Token], start: int = 0):
    pairs = {'(': ')', '[': ']', '{': '}'}
    i = start
    while i < len(ts):
        if ts[i].text not in pairs:
            yield i, i + 1
            i += 1
            continue
        begin = i
        stack = [pairs[ts[i].text]]
        i += 1
        while stack and i < len(ts):
            if ts[i].text in pairs:
                stack.append(pairs[ts[i].text])
            elif ts[i].text == stack[-1]:
                stack.pop()
            i += 1
        if stack:
            raise ValueError(f'unbalanced group at character {ts[begin].start}')
        yield begin, i


def context_bindings(source: Source, section: Section) -> dict[str, tuple[str, bool]]:
    bindings = {}
    for sentence in section.contexts:
        normalized_sentence = normalized(sentence)
        if 'invGS_gen hlc Σ' in normalized_sentence and 'gen_heapGS piece pval Σ' in normalized_sentence:
            bindings.update(hlc=('has_lc', True), Σ=('gFunctors', True),
                            invGS_gen0=('invGS_gen hlc Σ', True),
                            gen_heapGS0=('gen_heapGS piece pval Σ', True))
            continue
        for begin, end in groups(sentence, 1):
            group = sentence[begin:end]
            if group[0].text in ('`', '.'):
                continue
            if group[0].text not in ('(', '{') or ':' not in [t.text for t in group]:
                fail(source, group[0], 'unsupported section binder')
            colon = next(i for i, t in enumerate(group) if t.text == ':')
            typ = source.text[group[colon+1].start:group[-2].end]
            for name in group[1:colon]:
                bindings[name.text] = (typ, group[0].text == '{')
    return bindings


def fail(source: Source, token: Token, message: str):
    line = source.text.count('\n', 0, token.start) + 1
    raise ValueError(f'{source.path}:{line}: {message}')


def defines_type(typ: str) -> str | None:
    match = re.fullmatch(r'find_fn\s+ge\s+\(TAtom\s+("(?:[^"]|"")*")\)\s*=\s*Some\s+\(Defined\s+([\w.]+)\)', typ, re.S)
    return f'Defines ge {match[1]} {match[2]}' if match else None


def generalized_arguments(entry: dict) -> list[dict]:
    exported, local = entry['arguments'], entry['local_arguments']
    n = len(exported) - len(local)
    if n < 0 or [a['name'] for a in exported[n:]] != [a['name'] for a in local]:
        raise ValueError(f'Rocq local/exported Arguments do not share a suffix: {entry}')
    return exported[:n]


@dataclass
class Conversion:
    source: Source
    section: Section
    name: str
    metadata: dict
    lookup_names: set[str]
    retained: bool = False

    @property
    def wrapped(self):
        return not self.retained and protected_name(self.name) and not reviewed_audit(self.metadata['file'], self.name)

    @property
    def implementation(self):
        return implementation_name(self.source.path, self.name) if self.wrapped else self.name


def implementation_name(path, name):
    *scope, leaf = name.split('.')
    return '.'.join([*scope, Path(path).stem + '_' + leaf + '_program'])


def declaration_end(source: Source, declaration: list[Token]) -> int:
    words = [t.text for t in declaration]
    kind = next(w for w in words if w in DECLARATIONS)
    if kind in ('Definition', 'Fixpoint', 'Instance') and ':=' in words:
        return declaration[-1].end
    for sentence in sentences(source.ts):
        if sentence[0].start > declaration[0].start and sentence[0].text in ('Qed', 'Defined'):
            return sentence[-1].end
    fail(source, declaration[0], 'cannot locate declaration proof terminator')


def inferred_body(declaration):
    words = [t.text for t in declaration]
    if words[0] != 'Definition' or ':=' not in words:
        return None
    top = list(groups(declaration, 2))
    assignment = next((a for a, b in top if b == a+1 and words[a] == ':='), None)
    if assignment is None or any(words[a] == ':' for a, b in top if a < assignment):
        return None
    return declaration[assignment+1].start, declaration[-1].start


def legacy_instance(conversion):
    words = [t.text for t in conversion.section.iris]
    name = words[words.index('Instance')+1]
    return name, '.'.join([conversion.source.path.stem, *conversion.section.scope, name])


def section_edits(source: Source, metadata: dict, calls=()):
    edits = []
    conversions = {}

    def legacy_text(start, end):
        text = source.text[start:end]
        for a, b, replacement in sorted(calls, reverse=True):
            dependency = conversions.get(source.references.get(a))
            if dependency and dependency.retained and start <= a <= b <= end:
                text = text[:a-start] + replacement + text[b-start:]
        return text

    for section in source.sections:
        if not section.canonical:
            continue
        bindings = context_bindings(source, section)
        lookup_names = {name for name, (typ, _) in bindings.items() if defines_type(typ)}
        for sentence in section.contexts:
            if 'invGS_gen hlc Σ' in normalized(sentence) and 'gen_heapGS piece pval Σ' in normalized(sentence):
                replacement = 'Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.'
            else:
                replacement = []
                for begin, end in groups(sentence, 1):
                    group = sentence[begin:end]
                    if group[0].text in ('`', '.'):
                        continue
                    colon = next(i for i, t in enumerate(group) if t.text == ':')
                    names = [t.text for t in group[1:colon] if t.text not in ('w0', 'registry', 'ge')]
                    if names:
                        name = names[0]
                        typ, implicit = bindings[name]
                        defined = defines_type(typ)
                        if defined:
                            replacement.extend(f'`{{{n} : !{defined}}}' for n in names)
                        else:
                            start, end = group[colon+1].start, group[-2].end
                            typ = source.text[start:end]
                            for a, b, text in sorted(calls, reverse=True):
                                if start <= a <= b <= end:
                                    typ = typ[:a-start] + text + typ[b-start:]
                            left, right = ('{', '}') if implicit else ('(', ')')
                            replacement.append(f'{left}{" ".join(names)} : {typ}{right}')
                replacement = 'Context ' + '\n  '.join(replacement) + '.' if replacement else ''
            edits.append((sentence[0].start, sentence[-1].end, replacement))
        start = section.iris[0].start
        previous = max((t.end for t in source.ts if t.end <= start), default=0)
        gap = source.text[previous:start]
        if gap.strip().startswith('(**') and gap.strip().endswith('*)'):
            start = previous + gap.index('(**')
        edits.append((start, section.iris[-1].end, ''))
        lifted = []
        wrappers = []
        for name in section.declarations:
            key = source.path.stem + '.' + name
            entry = metadata[key]
            prefix = generalized_arguments(entry)
            names = {a['name'] for a in prefix}
            if {'hlc', 'Σ', 'invGS_gen0', 'gen_heapGS0', 'w0', 'registry', 'ge'} <= names and entry['sort'] == 'Prop':
                conversion = Conversion(source, section, name, entry, lookup_names & names)
                conversions[key] = conversion
                if conversion.wrapped:
                    declaration = source.declarations[name]
                    if declaration[0].text not in ('Lemma', 'Theorem', 'Corollary', 'Fact', 'Remark', 'Proposition'):
                        fail(source, declaration[0], 'audited implementation needs an explicit proposition')
                    edits.append((declaration[1].start, declaration[1].end, conversion.implementation.split('.')[-1]))
                    signature = legacy_text(declaration[0].start, declaration[-1].end)
                    header_names = []
                    for a, b in groups(declaration, 2):
                        part = [t.text for t in declaration[a:b]]
                        if part == [':']:
                            break
                        if part[0] in ('(', '{'):
                            part = part[1:part.index(':')] if ':' in part else part[1:-1]
                        if not all(re.fullmatch(r"[^\W\d][\w']*", n) for n in part):
                            fail(source, declaration[a], 'unsupported audited lemma binder')
                        header_names.extend(n for n in part if n != '_')
                    revert = ' '.join(f'revert {n};' for n in reversed(header_names))
                    packed = '(@program_of hlc Σ invGS_gen0 gen_heapGS0 w0 registry ge)'
                    remaining = ' '.join(a['name'] for a in prefix if a['name'] not in
                                         {'hlc', 'Σ', 'invGS_gen0', 'gen_heapGS0', 'w0', 'registry', 'ge'})
                    wrappers.append(signature + f'\nProof. {revert}\n  exact (@{conversion.implementation.split(".")[-1]} hlc Σ {packed} {remaining}). Qed.')
            else:
                # Predicates needing only heap state must not acquire an
                # unrelated world or invariant instance. Keep their original
                # section context in a preceding section of values.
                declaration = source.declarations[name]
                end = declaration_end(source, declaration)
                lifted.append(source.text[declaration[0].start:end])
                edits.append((declaration[0].start, end, ''))
                conversions[key] = Conversion(source, section, name, entry, set(), retained=True)
        if lifted or wrappers:
            needed = {a['name'] for c in conversions.values() if c.section is section and c.retained
                      for a in generalized_arguments(c.metadata)}
            if wrappers:
                needed.update({'hlc', 'Σ', 'invGS_gen0', 'gen_heapGS0', 'w0', 'registry', 'ge'})
            setup = []
            for name, (typ, implicit) in bindings.items():
                if name not in needed:
                    continue
                left, right = ('{', '}') if implicit else ('(', ')')
                setup.append(f'{left}{name} : {typ}{right}')
            setup = ['Context ' + '\n  '.join(setup) + '.'] if setup else []
            setup.extend(f'Existing Instance {name}.' for name in ('invGS_gen0', 'gen_heapGS0') if name in needed)
            if {'hlc', 'Σ', 'invGS_gen0', 'gen_heapGS0', 'w0', 'registry', 'ge'} <= needed:
                setup.append(source.text[section.iris[0].start:section.iris[-1].end])
                setup.extend(source.text[s[0].start:s[-1].end] for s in sentences(source.ts)
                             if section.start < s[0].start < section.end and
                             [t.text for t in s[:2]] == ['Local', 'Notation'])
            text = '\n'.join([f'Section {section.name}_values.', *setup, *lifted,
                              f'End {section.name}_values.\n'])
            edits.append((section.start, section.start, text))
        if wrappers:
            iris_words = [t.text for t in section.iris]
            iris_name = iris_words[iris_words.index('Instance') + 1]
            context = [legacy_text(s[0].start, s[-1].end) for s in section.contexts]
            notations = [source.text[s[0].start:s[-1].end] for s in sentences(source.ts)
                         if section.start < s[0].start < section.end and
                         [t.text for t in s[:2]] == ['Local', 'Notation']]
            hint = ('Local Hint Extern 0 (irisGS_gen _ (nanofil_lang registry ge) _) =>\n'
                    f'  exact (@{iris_name} hlc Σ invGS_gen0 gen_heapGS0 w0 registry ge) : typeclass_instances.')
            text = '\n'.join(['', f'Section {section.name}_public.', *context, hint, *notations,
                              *wrappers, f'End {section.name}_public.\n'])
            edits.append((section.end, section.end, text))
    return edits, conversions


TERM_STOPS = {'with', 'as', 'in', 'return', 'then', 'else', 'end', 'by', 'where',
              'fun', 'forall', 'match', 'let', 'if', 'at', 'using'}


def application(source: Source, index: int):
    """Parse the atom arguments of an application, independently of its tactic."""
    ts = source.ts
    args = []
    j = index + 1
    while j < len(ts):
        t = ts[j]
        if t.text in TERM_STOPS:
            break
        if t.text in ('(', '[', '{'):
            try:
                _, end = next(groups(ts, j))
            except ValueError as error:
                fail(source, t, str(error))
        elif t.text == '@':
            if j + 1 >= len(ts) or not re.fullmatch(r'[\w.\']+', ts[j+1].text):
                fail(source, t, 'invalid explicit application argument')
            end = j + 2
        elif t.text.startswith('"') or re.fullmatch(r'[\w.\']+', t.text) and t.text != '.':
            end = j + 1
        else:
            break
        if end + 1 < len(ts) and ts[end].text == '%':
            end += 2
        args.append((j, end))
        j = end
    return args


def resolve(source: Source, index: int, conversions: dict) -> str | None:
    reference = source.references.get(source.ts[index].start)
    if reference in conversions:
        return reference
    if reference and '.' in source.ts[index].text:
        alias, name = source.ts[index].text.split('.', 1)
        for sentence in reversed(sentences(source.ts)):
            if sentence[0].start >= source.ts[index].start:
                continue
            words = [t.text for t in sentence]
            if words[:3] == ['Module', alias, ':='] and len(words) == 5:
                target = words[3] + '.' + name
                matches = [key for key in conversions if key == target or key.endswith('.' + target)]
                if len(matches) == 1:
                    return matches[0]
                if matches:
                    fail(source, source.ts[index], 'ambiguous module alias target')
                break
    return None


def load_references(source: Source):
    glob = source.path.with_suffix('.glob').read_text()
    digest = re.search(r'^DIGEST (\w+)', glob)
    if not digest or digest[1] != hashlib.md5(source.text.encode()).hexdigest():
        raise ValueError(f'{source.path}: missing or stale compiler reference map')
    offsets = {}
    byte = 0
    for index, ch in enumerate(source.text):
        offsets[byte] = index
        byte += len(ch.encode())
    for match in re.finditer(r'^R(\d+):\d+ (\S+) (\S+) (\S+) (\S+)$', glob, re.M):
        offset, module, scope, name, kind = match.groups()
        if kind not in ('thm', 'def', 'inst', 'defax') or not module.startswith('Glibc.'):
            continue
        key = '.'.join([module.split('.')[-1], *([] if scope == '<>' else [scope]), name])
        source.references[offsets[int(offset)]] = key


def rewrite_calls(source: Source, conversions: dict, reserved: list[tuple], call_report: list, table_instances=()):
    edits = []
    declarations = {ts[next(i for i, t in enumerate(ts) if t.text in DECLARATIONS)+1].start for ts in source.declarations.values()}
    for index, token in enumerate(source.ts):
        if token.start in declarations or any(start <= token.start < end for start, end, _ in reserved):
            continue
        key = resolve(source, index, conversions)
        if not key:
            continue
        before = []
        for t in reversed(source.ts[:index]):
            if t.text in ('.', ';', ')', '('):
                break
            before.append(t.text)
        if 'unfold' in before or '[' in before and any(t in before for t in ('cbn', 'simpl', 'cbv')):
            continue
        conversion = conversions[key]
        current = next((s for s in source.sections if s.canonical and s.start < token.start < s.end), None)
        if conversion.wrapped and not current:
            count = len(application(source, index))
            call_report.append({'file': str(source.path), 'line': source.text.count('\n', 0, token.start)+1,
                                'declaration': key, 'before': count, 'after': count,
                                'bundle_argument': False, 'public_wrapper': True})
            continue
        callee = token.text
        if conversion.wrapped:
            callee = (conversion.implementation.split('.')[-1]
                      if conversion.source.path == source.path and current.scope == conversion.section.scope
                      else conversion.source.path.stem + '.' + conversion.implementation)
        local = source.path == conversion.source.path and conversion.section.start < token.start < conversion.section.end
        entry = conversion.metadata
        if conversion.retained:
            if local:
                prefix = generalized_arguments(entry)
                supplied = ' '.join(a['name'] for a in prefix if not a['implicit'])
                if supplied:
                    edits.append((token.start, token.end, '(' + token.text + ' ' + supplied + ')'))
            continue
        binders = entry['local_arguments'] if local else entry['arguments']
        explicit = index > 0 and source.ts[index-1].text == '@'
        positional = binders if explicit else [a for a in binders if not a['implicit']]
        args = application(source, index)
        if not args:
            if not local and current:
                if callee != token.text:
                    edits.append((token.start, token.end, callee))
            elif not local:
                section = next((s for s in source.sections if s.iris and s.start < token.start < s.end), None)
                if section:
                    setup = re.search(r'nanofil_irisGS (\w+) \( os_wi (\w+) \) (\w+) \.', normalized(section.iris))
                    if not setup:
                        fail(source, token, 'cannot recover caller program from its Iris instance')
                    registry, world, ge = setup.groups()
                    edits.append((token.start, token.end, 'program_call(' + callee +
                                  f' (glibc_program := program_of {world} {registry} {ge}))'))
            elif callee != token.text:
                edits.append((token.start, token.end, callee))
            continue
        if callee != token.text:
            edits.append((token.start, token.end, callee))
        mapped = []
        cursor = 0
        for begin, end in args:
            group = source.ts[begin:end]
            if len(group) >= 5 and group[0].text == '(' and group[2].text == ':=':
                name = group[1].text
                if name not in {a['name'] for a in binders}:
                    fail(source, token, f'unknown named argument {name} of {key}')
                mapped.append((name, begin, end, source.text[group[3].start:group[-2].end]))
                continue
            if cursor >= len(positional):
                # Lemmas ending in a quantified BI assertion can be applied
                # to further Gallina arguments; leave these unmapped tails.
                fail(source, token, f'{key}: {len(args)} application arguments exceed Rocq metadata ({len(positional)})')
            mapped.append((positional[cursor]['name'], begin, end, source.text[group[0].start:group[-1].end]))
            cursor += 1
        removed = conversion.lookup_names if not local else set()
        removed = removed | ({'w0', 'registry', 'ge', 'invGS_gen0', 'gen_heapGS0'} if not local else set())
        values = {name: text for name, _, _, text in mapped}
        supplied_program = {'w0', 'registry', 'ge'} & values.keys()
        extra = ''
        if not local and supplied_program:
            if supplied_program != {'w0', 'registry', 'ge'}:
                fail(source, token, f'partial program application of {key}: {sorted(supplied_program)}')
            same_program = current and all(values[n] == n for n in ('w0', 'registry', 'ge')) and not explicit
            if not same_program:
                if explicit:
                    required = ('hlc', 'Σ', 'invGS_gen0', 'gen_heapGS0', 'w0', 'registry', 'ge')
                    if not all(n in values for n in required):
                        fail(source, token, f'explicit application of {key} does not provide the canonical ghost instances')
                    packed = '@program_of ' + ' '.join(term_argument(values[n]) for n in required)
                else:
                    packed = 'program_of ' + ' '.join(term_argument(values[n]) for n in ('w0', 'registry', 'ge'))
                extra = f' (glibc_program := {packed})'
        if not any(name in removed for name, *_ in mapped):
            continue
        if explicit:
            edits.append((source.ts[index-1].start, source.ts[index-1].end, ''))
        if extra:
            edits.append((token.end, token.end, extra))
        count = 0
        for name, begin, end, text in mapped:
            if name in removed:
                replacement = ''
                proof_tokens = tokens(text)
                proof_head = next((t.text for t in proof_tokens if t.text not in ('(', '@')), '')
                if not current and name in conversion.lookup_names and proof_head.split('.')[-1] not in table_instances:
                    replacement = f'({name} := {text})'
                edits.append((source.ts[begin].start, source.ts[end-1].end, replacement))
                count += not replacement
            elif explicit and next(a for a in binders if a['name'] == name)['implicit']:
                edits.append((source.ts[begin].start, source.ts[end-1].end, f'({name} := {text})'))
        call_report.append({'file': str(source.path), 'line': source.text.count('\n', 0, token.start)+1,
                            'declaration': key, 'before': len(mapped), 'after': len(mapped)-count+bool(extra),
                            'bundle_argument': bool(extra), 'position': token.start,
                            'program_values': {n: values[n] for n in ('w0', 'registry', 'ge') if n in values}})
    return edits


def term_argument(text: str) -> str:
    ts = tokens(text)
    return text if len(ts) == 1 or (ts[0].text == '(' and list(groups(ts)) == [(0, len(ts))]) else '(' + text + ')'


def apply_edits(source: Source, edits: list[tuple[int, int, str]]) -> str:
    # Remove the whitespace belonging to deleted arguments, not unrelated
    # indentation, strings or comments. Join adjacent deletions first.
    deletions = []
    for start, end, replacement in sorted(set(edits)):
        if replacement or start == end:
            continue
        if deletions and not source.text[deletions[-1][1]:start].strip():
            deletions[-1] = (deletions[-1][0], end)
        else:
            deletions.append((start, end))
    edits = [(a, b, t) for a, b, t in edits if t or a == b]
    for start, end in deletions:
        replacement = ''
        line = source.text.rfind('\n', 0, start) + 1
        after = source.text.find('\n', end)
        after = len(source.text) if after < 0 else after
        if not source.text[line:start].strip() and not source.text[end:after].strip():
            start, end = line, min(after + 1, len(source.text))
        else:
            multiline = '\n' in source.text[start:end]
            original_start, original_end = start, end
            while start > line and source.text[start-1] in ' \t':
                start -= 1
            while end < len(source.text) and source.text[end] in ' \t':
                end += 1
            if multiline:
                if end < len(source.text) and source.text[end] not in '\n.,)':
                    last_line = source.text.rfind('\n', 0, end) + 1
                    indent = re.match(r'[ \t]*', source.text[last_line:]).group()
                    replacement = '\n' + indent
            elif ((start != original_start or end != original_end) and
                  end < len(source.text) and source.text[end] not in '\n.,)'):
                replacement = source.text[line:original_start] if start == line else ' '
            if start == line and start and end < len(source.text) and source.text[end] in '.,)':
                start -= 1
        edits.append((start, end, replacement))
    edits = sorted(set(edits), reverse=True)
    result = source.text
    previous = len(result) + 1
    for start, end, replacement in edits:
        if end > previous:
            fail(source, Token('', start, end), 'overlapping application rewrites')
        result = result[:start] + replacement + result[end:]
        previous = start
    return result


def table_instance(name, ge, table, index, symbol, fn):
    return f'''Lemma {name} : Defines {ge} {symbol} {fn}.
Proof. exact (defines_from_table_nth {ge} {table} {index} {symbol} {fn} {table}_correct eq_refl). Qed.
#[global] Existing Instance {name}.'''


def refresh_tables(tree: Path):
    """Regenerate indexed instances from the generated table's actual rows."""
    planned = {}
    count = 0
    for path in sorted(tree.rglob('*.v')):
        source = read_source(path)
        ss = sentences(source.ts)
        edits = []
        for sentence in ss:
            match = re.fullmatch(r'Definition (\w+_program_table) : list \( string \* func \) := (.*) \.', normalized(sentence))
            if not match:
                continue
            table, body = match.groups()
            row_pattern = r'\( ("[^"]+") , ([\w.]+) \) :: '
            rows = re.findall(row_pattern, body)
            if not rows or re.sub(row_pattern, '', body) != 'nil':
                fail(source, sentence[0], 'unsupported program-table row')
            if len({symbol for symbol, _ in rows}) != len(rows):
                fail(source, sentence[0], 'duplicate program-table symbol')
            certificate = next((s for s in ss if [t.text for t in s[:2]] == ['Lemma', table + '_correct']), None)
            ge_match = re.search(r'find_fn (\w+) \( TAtom n \)', normalized(certificate)) if certificate else None
            if not ge_match:
                fail(source, sentence[0], 'missing program-table certificate')
            ge = ge_match[1]
            present = set()
            insertion = None
            for i, declaration in enumerate(ss):
                instance = re.fullmatch(r'Lemma (\w+) : Defines ' + re.escape(ge) + r' ("[^"]+") ([\w.]+) \.', normalized(declaration))
                if not instance:
                    continue
                end = next((j for j in range(i+1, len(ss)) if ss[j][0].text in ('Qed', 'Defined', 'Abort')), None)
                if end is None or table not in [t.text for s in ss[i+1:end] for t in s]:
                    continue
                name, symbol, _ = instance.groups()
                if symbol not in dict(rows):
                    fail(source, declaration[0], f'table row removal would remove exported instance {name}')
                if end+1 >= len(ss) or normalized(ss[end+1]) != f'# [ global ] Existing Instance {name} .':
                    fail(source, declaration[0], 'generated instance registration is missing')
                index = next(j for j, row in enumerate(rows) if row[0] == symbol)
                replacement = table_instance(name, ge, table, index, symbol, rows[index][1])
                insertion = ss[end+1][-1].end
                edits.append((declaration[0].start, insertion, replacement))
                present.add(symbol)
            if insertion is None:
                fail(source, sentence[0], 'no generated instances anchor this table')
            additions = []
            for i, (symbol, fn) in enumerate(rows):
                if symbol not in present:
                    name = table + '_defines_' + symbol[1:-1].encode('utf8').hex()
                    additions.append(table_instance(name, ge, table, i, symbol, fn))
            if additions:
                edits.append((insertion, insertion, '\n' + '\n'.join(additions)))
            count += len(rows)
        if edits:
            planned[path] = apply_edits(source, edits)
    for path, text in planned.items():
        path.write_text(text)
    print(f'program: refreshed {count} indexed instances in {len(planned)} files; compile their certificates next')


def table_edits(source: Source):
    """Collect concrete lookup proofs into one certificate per environment."""
    found = {}
    ss = sentences(source.ts)
    for i, sentence in enumerate(ss):
        match = re.fullmatch(
            r'Lemma (\w+) : find_fn (\w+) \( TAtom ("[^"]+") \) = Some \( Defined ([\w.]+) \) \.',
            normalized(sentence))
        if not match:
            continue
        name, ge, symbol, fn = match.groups()
        if ge == 'ge':
            continue
        end = next((j for j in range(i+1, len(ss)) if ss[j][0].text in ('Qed', 'Defined', 'Abort')), None)
        if end is None or ss[end][0].text == 'Abort':
            fail(source, sentence[0], 'unterminated concrete lookup proof')
        body = normalized([t for row in ss[i+1:end] for t in row])
        if not ('vm_compute' in body or 'vm_cast_no_check' in body):
            continue
        found.setdefault(ge, []).append((name, symbol, fn, sentence[0].start, ss[end][-1].end))
    edits = []
    for ge, rows in found.items():
        if len(rows) < 2:
            continue
        table = source.path.stem + '_' + ge + '_program_table'
        cert = table + '_correct'
        text = f'Definition {table} : list (string * func) :=\n  '
        text += ' ::\n  '.join(f'({symbol}, {fn})' for _, symbol, fn, _, _ in rows) + ' :: nil.\n'
        text += f'''Lemma {cert} :
  List.Forall (fun '(n, f) => find_fn {ge} (TAtom n) = Some (Defined f)) {table}.
Proof.
  apply defines_table_of_map.
  vm_cast_no_check (eq_refl (List.map (fun '(_, f) => Some (Defined f)) {table})).
Qed.
#[global] Instance {table}_instance : ProgramTable {ge} :=
  {{| program_table := {table}; program_table_correct := {cert} |}}.
'''
        edits.append((rows[0][3], rows[0][3], text))
        for index, (name, symbol, fn, start, end) in enumerate(rows):
            replacement = table_instance(name, ge, table, index, symbol, fn)
            edits.append((start, end, replacement))
    return edits


DECLARATIONS = {'Lemma', 'Theorem', 'Corollary', 'Proposition', 'Fact', 'Remark', 'Definition', 'Fixpoint', 'Instance', 'Parameter'}


def read_source(path: Path) -> Source:
    text = path.read_text()
    ts = tokens(text)
    sections = []
    stack = []
    modules = []
    declarations = {}
    for sentence in sentences(ts):
        words = [t.text for t in sentence]
        if words[0] == 'Module' and ':=' not in words:
            offset = 2 if words[1] in ('Type', 'Export', 'Import') else 1
            modules.append(words[offset])
        elif words[0] == 'End' and modules and words[1] == modules[-1]:
            modules.pop()
        elif words[0] == 'Section':
            section = Section(words[1], sentence[0].start, scope=tuple(modules))
            sections.append(section)
            stack.append(section)
        elif words[0] == 'End' and stack and words[1] == stack[-1].name:
            stack.pop().end = sentence[-1].end
        elif words[0] in ('Context', 'Variable', 'Variables', 'Hypothesis', 'Hypotheses') and stack:
            stack[-1].contexts.append(sentence)
        else:
            k = next((i for i, word in enumerate(words[:8]) if word in DECLARATIONS), None)
            if 'Existing' in words[:8]:
                continue
            if k is not None and k + 1 < len(words):
                name = '.'.join([*modules, words[k+1]])
                if 'Local' not in words[:k] and not ('local' in words[:k]):
                    declarations[name] = sentence
                    if stack:
                        stack[-1].declarations.append(name)
                if 'Instance' in words[:k+1] and stack and 'nanofil_irisGS' in words:
                    stack[-1].iris = sentence
    for section in sections:
        if not section.iris:
            section.reason = 'no local nanofil_irisGS setup'
            continue
        setup = normalized(section.iris)
        ctx = ' '.join(normalized(s) for s in section.contexts)
        if 'nanofil_irisGS registry ( os_wi w0 ) ge .' not in setup:
            section.reason = 'noncanonical world, registry or environment'
        elif not all(x in ctx for x in ('invGS_gen hlc Σ', 'gen_heapGS piece pval Σ', 'w0 : os_world', 'registry : name', 'ge : genv')):
            section.reason = 'canonical setup inherits part of its context'
        else:
            section.canonical = True
    return Source(path, text, ts, sections, declarations)


@dataclass
class Argument:
    name: str
    implicit: bool


def arguments(line: str) -> list[Argument]:
    """Read Rocq's Arguments command, including scope annotations and groups."""
    ts = tokens(line)
    result = []
    implicit = False
    i = 2
    while i < len(ts):
        s = ts[i].text
        if s in ('{', '['):
            implicit = True
        elif s in ('}', ']'):
            implicit = False
        elif s == '%':
            i += 1
        elif s not in ('(', ')', '.', '/', ':', '!'):
            result.append(Argument(s, implicit))
        i += 1
    return result


def dump_metadata(tree: Path, sources: list[Source], out: Path) -> dict:
    out.mkdir(parents=True, exist_ok=True)
    model = os.environ['PE_MODEL']

    def dump(source):
        name = source.path.stem
        query = out / f'{name}.v'
        signatures = [s[2].text for s in sentences(source.ts)
                      if [t.text for t in s[:2]] == ['Module', 'Type'] and len(s) == 4]
        setup = ''.join(f'Declare Module PE_{sig} : {name}.{sig}.\n' for sig in signatures)
        def reference(decl):
            for sig in signatures:
                if decl.startswith(sig + '.'):
                    return 'PE_' + decl
            return name + '.' + decl
        query.write_text(f'From Glibc Require Import {name}.\nSet Printing Width 1000000.\nSet Printing Depth 10000.\n' +
                         setup + ''.join(f'Goal True. idtac "PE-ABOUT: {name}.{decl}". Abort.\nAbout {reference(decl)}.\n'
                         f'Goal True. let T := type of @{reference(decl)} in let K := type of T in idtac "PE-SORT: {name}.{decl}" K. Abort.\n'
                         for decl in source.declarations))
        cmd = ['rocq', 'c', '-q', '-R', model, 'Nanofil', '-R', str(tree), 'Glibc', str(query)]
        run = subprocess.run(cmd, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (out / f'{name}.log').write_text(run.stdout)
        if run.returncode:
            raise RuntimeError(f'About failed for {source.path}: {out / (name + ".log")}')
        local_dir = out / 'local'
        local_dir.mkdir(exist_ok=True)
        local_path = local_dir / f'{name}.v'
        pending = None
        inserts = []
        by_start = {ts[0].start: decl for decl, ts in source.declarations.items()}
        for sentence in sentences(source.ts):
            if sentence[0].start in by_start:
                pending = by_start[sentence[0].start]
                # A lemma's proposition can itself contain let-bindings.
                # Only a declaration body ends without a proof terminator.
                kind = next(t.text for t in sentence if t.text in DECLARATIONS)
                if kind != 'Parameter' and (kind not in ('Definition', 'Fixpoint', 'Instance') or ':=' not in [t.text for t in sentence]):
                    continue
            elif sentence[0].text not in ('Qed', 'Defined'):
                continue
            if pending:
                inserts.append((sentence[-1].end, f'\nSet Printing Width 1000000.\nGoal True. idtac "PE-ABOUT: {name}.{pending}". Abort.\nAbout {pending.split(".")[-1]}.\n'))
                pending = None
        local_source = source.text
        for offset, insertion in reversed(inserts):
            local_source = local_source[:offset] + insertion + local_source[offset:]
        local_path.write_text(local_source)
        local_run = subprocess.run([*cmd[:-1], str(local_path)], text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (local_dir / f'{name}.log').write_text(local_run.stdout)
        if local_run.returncode:
            raise RuntimeError(f'local About failed for {source.path}: {local_dir / (name + ".log")}')
        entries = {}
        for declaration in source.declarations:
            output = run.stdout.split(f'PE-ABOUT: {name}.{declaration}\n', 1)[1].split('PE-ABOUT:', 1)[0]
            match = re.search(r'^Arguments \S+(?:[^\n]*)$', output, re.M)
            if match:
                entries[f'{name}.{declaration}'] = {
                    'file': str(source.path.relative_to(tree)),
                    'arguments': [vars(a) for a in arguments(match[0])],
                    'about_arguments': match[0],
                }
            elif re.search(r'^\S+\s*:', output, re.M) and 'not a defined object' not in output:
                entries[f'{name}.{declaration}'] = {'file': str(source.path.relative_to(tree)), 'arguments': [], 'about_arguments': ''}
            else:
                raise RuntimeError(f'{source.path}: About did not identify {declaration}')
            marker = f'PE-ABOUT: {name}.{declaration}\n'
            local_output = local_run.stdout.split(marker, 1)[1].split('PE-ABOUT:', 1)[0]
            local_match = re.search(r'^Arguments \S+(?:[^\n]*)$', local_output, re.M)
            if local_match:
                local_arguments = [vars(a) for a in arguments(local_match[0])]
            else:
                # About omits Arguments for all-anonymous explicit binders.
                # Its section-variable list identifies the exported prefix.
                used = re.search(r'uses section variables ([^.]+)\.', local_output)
                prefix = used[1].split() if used else []
                exported = entries[f'{name}.{declaration}']['arguments']
                if [a['name'] for a in exported[:len(prefix)]] != prefix:
                    raise RuntimeError(f'{source.path}: inconsistent About section variables for {declaration}')
                local_arguments = exported[len(prefix):]
                if any(a['name'] != '_' or a['implicit'] for a in local_arguments):
                    raise RuntimeError(f'{source.path}: missing local Arguments for {declaration}')
            entries[f'{name}.{declaration}']['local_arguments'] = local_arguments
            entries[f'{name}.{declaration}']['local_about_arguments'] = local_match[0] if local_match else ''
            sort = re.search(r'PE-SORT: ' + re.escape(name + '.' + declaration) + r'\s+(\S+)', output)
            if not sort or sort[1] not in ('Prop', 'Set', 'Type'):
                raise ValueError(f'{source.path}: missing compiler sort for {declaration}')
            entries[f'{name}.{declaration}']['sort'] = sort[1]
        return entries

    result = {}
    with ThreadPoolExecutor(max_workers=8) as pool:
        for entries in pool.map(dump, sources):
            result.update(entries)
    (out / 'arguments.json').write_text(json.dumps(result, ensure_ascii=False, indent=2) + '\n')
    return result


def source_digest(path: Path):
    return hashlib.sha256(normalized(tokens(path.read_text())).encode()).hexdigest()


def evidence_types(before: Path, after: Path, metadata: dict, changes: list[dict], plugin: Path, out: Path):
    """Print compact types, then kernel-check that printing preserved each type."""
    sources = {str(p.relative_to(before)): read_source(p) for p in before.rglob('*.v')}
    conversions = {}
    for source in sources.values():
        if not any(key.startswith(source.path.stem + '.') for key in metadata):
            continue
        _, entries = section_edits(source, metadata)
        conversions.update(entries)
    modules = {'Glibc.' + rel[:-2].replace('/', '.'): rel for rel in sources}
    by_file = {}
    for change in changes:
        if change['kind'] == 'changed':
            by_file.setdefault(change['file'], {})[change['name']] = change.get('after_name', change['name'])
    def full(rel, name):
        return 'Glibc.' + rel[:-2].replace('/', '.') + '.' + name
    def dependencies(rel):
        seen, todo = set(), [rel]
        while todo:
            path = todo.pop()
            if path in seen:
                continue
            seen.add(path)
            glob = (before / path).with_suffix('.glob').read_text()
            todo.extend(modules[m] for m in re.findall(r'^R\d+:\d+ (\S+) <> <> lib$', glob, re.M) if m in modules)
        return seen
    def query(job):
        side, rel = job
        tree = before if side == 'before' else after
        work = out / side
        work.mkdir(parents=True, exist_ok=True)
        target = work / (Path(rel).stem + '.v')
        setup = [f'Require Import Glibc.{rel[:-2].replace("/", ".")}.',
                 f'Declare ML Module "{plugin.name}".', 'Set Printing Implicit.',
                 'Set Printing Coercions.', 'Set Printing Width 1000000.', 'Set Printing Depth 1000000.']
        aliases, unfold = {}, []
        for dep in sorted(dependencies(rel)):
            src = sources[dep]
            for sentence in sentences(src.ts):
                if [t.text for t in sentence[:2]] == ['Module', 'Type'] and len(sentence) == 4:
                    original = full(dep, sentence[2].text)
                    alias = 'PE_' + src.path.stem + '_' + sentence[2].text
                    aliases[original] = alias
                    setup.append(f'Declare Module {alias} : {original}.')
            if side == 'before':
                for section in src.sections:
                    if section.canonical and section.iris:
                        words = [t.text for t in section.iris]
                        unfold.append(full(dep, '.'.join([*section.scope, words[words.index('Instance')+1]])))
            for name, ts in src.declarations.items():
                entry = conversions.get(src.path.stem + '.' + name)
                if entry and not entry.retained and entry.metadata['sort'] != 'Prop' and ts[0].text == 'Definition':
                    unfold.append(full(dep, name))
        def reference(name):
            for original, alias in aliases.items():
                if name.startswith(original + '.'):
                    return alias + name[len(original):]
            return name
        unfold = [reference(n) for n in unfold]
        if side == 'after':
            unfold += ['GlibcProgram.' + n for n in ('Defines', 'program_of', 'program_world', 'program_registry',
                       'program_ge', 'program_inv', 'program_heap', 'program_irisGS')]
        reduction = 'cbv beta iota zeta' + (' delta [' + ' '.join(sorted(set(unfold))) + ']' if unfold else '')
        commands = list(setup)
        for i, name in enumerate(by_file[rel]):
            q = reference(full(rel, by_file[rel][name] if side == 'after' else name))
            commands += [f'Goal True. let T := type of @{q} in let K := type of T in idtac "KIND_{i}" K "END_KIND_{i}". Abort.',
                         f'Goal True. let T := type of @{q} in let T := eval {reduction} in T in idtac "TYPE_{i}" T "END_TYPE_{i}". Abort.']
            if sources[rel].declarations[name][0].text == 'Definition':
                body_reduction = 'cbv beta iota zeta delta [' + ' '.join(sorted(set([*unfold, q]))) + ']'
                commands += [f'Goal True. let T := type of @{q} in let K := type of T in lazymatch K with Prop => idtac | _ => let v := eval {body_reduction} in @{q} in idtac "BODY_{i}" v "END_BODY_{i}" end. Abort.']
        target.write_text('\n'.join(commands) + '\n')
        env = dict(os.environ)
        env['OCAMLPATH'] = str(plugin.parent) + ':' + env.get('OCAMLPATH', '')
        cmd = ['rocq', 'c', '-q', '-R', os.environ['PE_MODEL'], 'Nanofil', '-R', str(tree), 'Glibc', str(target)]
        run = subprocess.run(cmd, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=180)
        target.with_suffix('.log').write_text(run.stdout)
        if run.returncode:
            raise ValueError(f'evidence query failed: {target.with_suffix(".log")}')
        # Signature probes introduce a local module. Expand its transparent
        # data aliases so the evidence does not depend on that module's axioms.
        local_data = sorted(set(re.findall(r'\b\w+\.PE_\w+(?:\.\w+)+', run.stdout)))
        if local_data:
            previous = reduction
            unfold += local_data
            reduction = 'cbv beta iota zeta delta [' + ' '.join(sorted(set(unfold))) + ']'
            commands = [command.replace(previous, reduction) for command in commands]
            target.write_text('\n'.join(commands) + '\n')
            run = subprocess.run(cmd, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=180)
            target.with_suffix('.log').write_text(run.stdout)
            if run.returncode:
                raise ValueError(f'signature data normalization failed: {target.with_suffix(".log")}')
        result, roundtrips = {}, list(setup)
        for i, name in enumerate(by_file[rel]):
            q = reference(full(rel, by_file[rel][name] if side == 'after' else name))
            def extract(tag):
                match = re.search(rf'{tag}_{i}\s+(.*?)\s+END_{tag}_{i}', run.stdout, re.S)
                if not match or '...' in match[1] or '…' in match[1]:
                    raise ValueError(f'missing or truncated {tag}: {rel}:{name}')
                return match[1].strip()
            typ, kind = extract('TYPE'), extract('KIND')
            body = extract('BODY') if sources[rel].declarations[name][0].text == 'Definition' and kind != 'Prop' else None
            result[name] = {'type': typ, 'body': body, 'kind': kind}
            roundtrips.append(f'Definition printed_type_{i} := {typ}.')
            roundtrips.append(f'Definition roundtrip_type_{i} : ltac:(let T := type of @{q} in let T := eval {reduction} in T in exact (T = printed_type_{i})) := eq_refl.')
            if body:
                body_reduction = 'cbv beta iota zeta delta [' + ' '.join(sorted(set([*unfold, q]))) + ']'
                roundtrips.append(f'Definition printed_body_{i} := {body}.')
                roundtrips.append(f'Definition roundtrip_body_{i} : ltac:(let v := eval {body_reduction} in @{q} in exact (v = printed_body_{i})) := eq_refl.')
        target.write_text('\n'.join(roundtrips) + '\n')
        run = subprocess.run(cmd, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=180)
        target.with_suffix('.roundtrip.log').write_text(run.stdout)
        if run.returncode:
            raise ValueError(f'printed evidence lost binding information: {target.with_suffix(".roundtrip.log")}')
        target.with_suffix('.json').write_text(json.dumps(result, ensure_ascii=False, indent=2) + '\n')
        return side, rel, result
    result = {'before': {}, 'after': {}}
    with ThreadPoolExecutor(max_workers=4) as pool:
        for side, rel, entries in pool.map(query, [(s, f) for f in by_file for s in result]):
            result[side][rel] = entries
    return result, conversions


def statement_candidates(before: Path, after: Path, destination: Path):
    rows = []
    for path in sorted(after.rglob('*.v')):
        rel = path.relative_to(after)
        original = before / rel
        if original.exists() and original.read_bytes() == path.read_bytes():
            continue
        old = read_source(original).declarations if original.exists() else {}
        new = read_source(path).declarations
        for name in sorted(old.keys() | new.keys()):
            kind = 'changed' if name in old and name in new else ('added' if name in new else 'removed')
            rows.append(f'{kind}\t{rel}\t{name}')
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text('# Discovery candidates, not approval of any statement change.\n' + '\n'.join(rows) + '\n')
    print(f'program: wrote {len(rows)} statement-discovery candidates to {destination}')


def emit_evidence(before: Path, after: Path, metadata: dict, report_path: Path, plugin: Path):
    report = json.loads(report_path.read_text())
    if report['errors']:
        raise ValueError('50-program: cannot certify an incomplete statement comparison')
    changes = sorted(report['differences'], key=lambda d: (d['file'], d['name']))
    if any(c['kind'] not in ('changed', 'added') for c in changes):
        raise ValueError('50-program: an exported declaration disappeared')
    if any(protected_name(c['name']) and not reviewed_audit(c['file'], c['name']) for c in changes):
        raise ValueError('50-program: an audited endpoint changed')
    out = after.parent / (after.name + '.program/evidence')
    requests = list(changes)
    implementations = {}
    for change in changes:
        old_file = before / change['file']
        names = read_source(old_file).declarations if change['kind'] == 'added' and old_file.exists() else ()
        original = next((name for name in names if protected_name(name) and implementation_name(change['file'], name) == change['name']), None)
        if change['kind'] == 'added' and original:
            implementations[(change['file'], change['name'])] = original
            requests.append(dict(change, kind='changed', name=original, after_name=change['name']))
    types, conversions = evidence_types(before, after, metadata, requests, plugin.resolve(), out)
    manifest = after.parent / (after.name + '.program/50-program.txt')
    proof = manifest.with_suffix('.equivalence.v')
    pins = manifest.with_suffix('.elaborated.json')
    rows = ['# Stage 50 bundles exactly the existing world, environment, registry and ghost instances.',
            '# Every changed statement has two kernel-checked adapters; predicate definitions have pointwise equality proofs.',
            '# Compact statements are re-elaborated and checked against the actual compiler types before emission.']
    files = sorted({c['file'] for c in requests if c['kind'] == 'changed'})
    proofs = ['(** The adapters preserve each rule in both directions. Predicate equalities also preserve resource ownership. *)',
              'From Glibc Require Import GlibcProgram.',
              *['Require Import Glibc.' + f[:-2].replace('/', '.') + '.' for f in files]]
    record = '{| program_world := w; program_registry := r; program_ge := g; program_inv := inv; program_heap := heap |}'
    reviewed = {(d['file'], d['name']): d for d in json.loads((HERE / 'check/audit-changes.json').read_text())['declarations']}
    for i, c in enumerate(changes):
        rel, name = c['file'], c['name']
        rows.append(f'{c["kind"]}\t{rel}\t{name}')
        original = implementations.get((rel, name), name)
        if original != name:
            rows.append(f'# wrapper\t{rel}\t{original}\t{name}')
        if c['kind'] != 'changed' and original == name:
            continue
        old, new = types['before'][rel][original], types['after'][rel][original]
        approval = reviewed.get((rel, original))
        if approval:
            if normalized(tokens(old['type'])) != normalized(tokens(approval['before'])):
                raise ValueError(f'50-program: reviewed original statement changed: {rel}:{original}')
            i = approval['reviewed_adapters'][0].removeprefix('program_old_to_new_')
        else:
            i = 'auto_' + str(i)
        for side, value in [('before', old), ('after', new)]:
            rows.append(f'# {side}\t{rel}\t{name}\t' + ' '.join(value['type'].split()))
        conv = conversions.get(Path(rel).stem + '.' + original)
        bundled = conv is not None and not conv.retained
        old_name, new_name = f'program_before_{i}', f'program_after_{i}'
        forward, reverse = f'program_old_to_new_{i}', f'program_new_to_old_{i}'
        rows.append(f'# equivalence\t{rel}\t{name}\t{forward}\t{reverse}')
        body = old['body'] is not None
        if body != (new['body'] is not None):
            raise ValueError(f'50-program: declaration changed between a proposition and a predicate: {rel}:{name}')
        left, right = (old['body'], new['body']) if body else (old['type'], new['type'])
        if re.search(r'\bPE_\w+\.', left + right):
            raise ValueError(f'50-program: query-local module escaped into evidence: {rel}:{name}')
        proofs += [f'(* {rel}: {name}. *)', f'Definition {old_name} := {left}.', f'Definition {new_name} := {right}.']
        if body and bundled:
            proofs += [f'Lemma {forward} : forall hlc Σ inv heap w r g, @{old_name} hlc Σ inv heap w r g = @{new_name} hlc Σ {record}.',
                       'Proof. reflexivity. Qed.',
                       f'Lemma {reverse} : forall hlc Σ (P : GlibcProgram (hlc := hlc) Σ), @{new_name} hlc Σ P =',
                       f'  @{old_name} hlc Σ (@program_inv hlc Σ P) (@program_heap hlc Σ P) (@program_world hlc Σ P) (@program_registry hlc Σ P) (@program_ge hlc Σ P).',
                       'Proof. intros hlc Σ P. destruct P. reflexivity. Qed.']
        elif body:
            proofs += [f'Lemma {forward} : {old_name} = {new_name}. Proof. reflexivity. Qed.',
                       f'Lemma {reverse} : {new_name} = {old_name}. Proof. reflexivity. Qed.']
        elif bundled:
            proofs += [f'Lemma {forward} : {old_name} -> {new_name}.',
                       'Proof. intros rule hlc Σ P. destruct P as [w r g inv heap]. exact (@rule hlc Σ inv heap w r g). Qed.',
                       f'Lemma {reverse} : {new_name} -> {old_name}.',
                       f'Proof. intros rule hlc Σ inv heap w r g. exact (@rule hlc Σ {record}). Qed.']
        else:
            proofs += [f'Lemma {forward} : {old_name} -> {new_name}. Proof. exact (fun rule => rule). Qed.',
                       f'Lemma {reverse} : {new_name} -> {old_name}. Proof. exact (fun rule => rule). Qed.']
    for path in sorted(after.rglob('*.v')):
        rel = path.relative_to(after)
        rows.append(f'# inventory\t{rel}')
        # Include unchanged dependencies, especially Fix: a different runtime
        # must not reuse evidence for this source boundary.
        rows.append(f'# output-sha256\t{rel}\t{source_digest(path)}')
    proof.write_text('\n\n'.join(proofs) + '\n')
    manifest.write_text('\n'.join(rows) + '\n')
    subprocess.run([sys.executable, str(HERE / 'check/expectations.py'), 'export', str(manifest), str(report_path)], check=True)
    rows.extend(f'# evidence-sha256\t{path.name}\t{hashlib.sha256(path.read_bytes()).hexdigest()}' for path in (proof, pins))
    manifest.write_text('\n'.join(rows) + '\n')
    print(f'program: emitted {len(changes)} exact statement changes; equivalence compilation is still required')


def prepare_evidence(tree: Path, refresh_review=False):
    """Reproduce the transformation before regenerating its runtime evidence."""
    out = tree.parent / (tree.name + '.program')
    before, metadata_path = out / 'before', out / 'metadata/arguments.json'
    if not before.is_dir() or not metadata_path.exists():
        raise ValueError('50-program: --check needs the before snapshot and metadata retained by apply.sh')
    selected = {str(p.relative_to(before)) for p in before.rglob('*.v') if p.with_suffix('.vo').exists()}
    for rel in selected:
        load_references(read_source(before / rel))
    # Re-running the source transformation ties adapters to actual output,
    # without committing a digest for every campaign file.
    with tempfile.TemporaryDirectory(prefix='expected-', dir=out) as tmp:
        expected = Path(tmp)
        for path in before.rglob('*.v'):
            target = expected / path.relative_to(before)
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(path, target)
        env = dict(os.environ)
        env.pop('PE_PROGRAM_TARGETS', None)
        with (out / 'reproduce.log').open('w') as log:
            subprocess.run([sys.executable, __file__, str(expected), '--source', str(before),
                            '--metadata', str(metadata_path)], env=env,
                           stdout=log, stderr=subprocess.STDOUT, check=True)
        actual_files = {str(p.relative_to(tree)) for p in tree.rglob('*.v')}
        expected_files = {str(p.relative_to(expected)) for p in expected.rglob('*.v')}
        if actual_files != expected_files:
            raise ValueError('50-program: output inventory does not match the transformation')
        for rel in actual_files:
            if source_digest(tree / rel) != source_digest(expected / rel):
                raise ValueError(f'50-program: output differs from the transformation: {rel}')
    selected.add('GlibcProgram.v')
    compile_targets(tree, [f + 'o' for f in sorted(selected)])
    plugin = out / 'plugin'
    subprocess.run(['bash', str(HERE / 'check/plugin.sh'), str(plugin)], check=True)
    candidates = out / 'candidates.txt'
    statement_candidates(before, tree, candidates)
    command = [sys.executable, str(HERE / 'check/check.py'), 'statements', str(before), str(tree),
               '--plugin', str(plugin), '--expectations', str(candidates), '--output', str(out / 'statements'),
               '--discovery', '--files', *sorted(selected)]
    with (out / 'statements.log').open('w') as log:
        run = subprocess.run(command, stdout=log, stderr=subprocess.STDOUT)
    report = out / 'statements/report.json'
    if run.returncode not in (0, 1) or not report.exists() or json.loads(report.read_text())['errors']:
        raise ValueError(f'50-program: incomplete statement comparison: {out / "statements.log"}')
    emit_evidence(before, tree, json.loads(metadata_path.read_text()), report, plugin)
    manifest = out / '50-program.txt'
    actions = sorted(line for line in manifest.read_text().splitlines() if line and not line.startswith('#'))
    review = HERE / 'check/expected-statement-changes/50-program.txt'
    if refresh_review:
        review.write_text('# Reviewed stage-50 declarations; exact types and adapters are generated under TREE.program/.\n' + '\n'.join(actions) + '\n')
    else:
        approved = sorted(line for line in review.read_text().splitlines() if line and not line.startswith('#') and line.split('\t')[1] in selected)
        if actions != approved:
            raise ValueError('50-program: generated declaration set differs from the reviewed list')
    return manifest


def check_evidence(tree: Path, refresh_review=False):
    manifest = prepare_evidence(tree, refresh_review)
    proof = manifest.with_suffix('.equivalence.v')
    pins = manifest.with_suffix('.elaborated.json')
    changed, pairs, guards = set(), {}, {}
    added, wrappers, inventory = set(), set(), set()
    hashes = {}
    abstract = 'Declare Module R : Runtime' in normalized(tokens((tree / 'Fix.v').read_text()))
    abstract_compiled = {str(p.relative_to(tree)) for p in tree.rglob('*.v') if p.with_suffix('.vo').exists()}
    for line in manifest.read_text().splitlines():
        fields = line.split('\t')
        if fields[0] == 'changed':
            changed.add(tuple(fields[1:]))
        elif fields[0] == 'added':
            added.add(tuple(fields[1:]))
        elif fields[0] == '# wrapper':
            if not protected_name(fields[2]) or fields[3] != implementation_name(fields[1], fields[2]):
                raise ValueError('50-program: invalid audited wrapper relationship')
            wrappers.add((fields[1], fields[3]))
        elif fields[0] == '# equivalence':
            pairs[tuple(fields[1:3])] = fields[3:5]
        elif fields[0] == '# output-sha256':
            guards[fields[1]] = fields[2]
        elif fields[0] == '# inventory':
            inventory.add(fields[1])
        elif fields[0] == '# evidence-sha256':
            hashes[fields[1]] = fields[2]
    if not wrappers <= added:
        raise ValueError('50-program: wrapper implementation is absent from the manifest')
    changed |= wrappers
    if not changed or set(pairs) != changed:
        raise ValueError('50-program: every changed declaration needs exactly two adapters')
    if inventory != {str(p.relative_to(tree)) for p in tree.rglob('*.v')}:
        raise ValueError('50-program: source inventory differs from the reviewed transformation')
    if set(guards) != inventory:
        raise ValueError('50-program: every source dependency needs an evidence guard')
    for path, digest in guards.items():
        if source_digest(tree / path) != digest:
            raise ValueError(f'50-program: transformed source guard failed: {path}')
        if not abstract or path in abstract_compiled:
            load_references(read_source(tree / path))
            if not (tree / path).with_suffix('.vo').exists():
                raise ValueError(f'50-program: transformed source has not compiled: {path}')
    if not guards or 'GlibcProgram.v' not in guards:
        raise ValueError('50-program: missing transformed-source or bundle guards')
    for path in (proof, pins):
        if hashes.get(path.name) != hashlib.sha256(path.read_bytes()).hexdigest():
            raise ValueError(f'50-program: evidence differs from its reviewed guard: {path.name}')
    source = proof.read_text()
    actual = re.findall(r'\b(?:Lemma|Theorem|Corollary)\s+(\w+)', normalized(tokens(source)))
    expected = [name for names in pairs.values() for name in names]
    if sorted(actual) != sorted(expected) or len(set(expected)) != len(expected):
        raise ValueError('50-program: equivalence declarations do not match the declaration manifest')
    if any(t.text in ('Admitted', 'Axiom', 'Axioms', 'Parameter', 'Parameters', 'Declare') for t in tokens(source)):
        raise ValueError('50-program: equivalence evidence may not assume its result')
    out = tree.parent / (tree.name + '.program/check')
    selected = abstract_compiled if abstract else None
    evidence = compile_equivalence(tree, source, out, selected)
    count = 2 * len(evidence)
    expected_count = sum(2 for file, name in changed if selected is None or file in selected)
    if count != expected_count:
        raise ValueError('50-program: not every declared direction was compiled and audited')
    result = 'unchanged runtime assumptions' if abstract else 'Closed'
    print(f'program: {expected_count // 2} changed declarations; {count} directions compiled; {result}; source guards match')
    print('program-runtime: ' + ('abstract' if abstract else 'concrete'))
    print('program-assumptions: ' + ('unchanged-runtime' if abstract else 'closed'))
    report = out / 'assumptions.json'
    report.write_text(json.dumps({'runtime': 'abstract' if abstract else 'concrete', 'pairs': evidence}, indent=2) + '\n')
    print(f'program-assumption-evidence: {report.resolve()}')


def compile_equivalence(tree: Path, source: str, out: Path, selected=None):
    """Compile every adapter in bounded independent units, with four workers."""
    started = time.monotonic()
    out.mkdir(parents=True, exist_ok=True)
    markers = list(re.finditer(r"(?m)^\(\* ([\w/]+\.v): [\w.']+\. \*\)$", source))
    if not markers:
        raise ValueError('50-program: missing adapter source boundaries')
    header = source[:markers[0].start()]
    if any(s[0].text not in ('From', 'Require') for s in sentences(tokens(header))):
        raise ValueError('50-program: adapter prelude must contain imports only')
    if selected is not None:
        header = '\n'.join(line for line in header.splitlines() if not line.startswith('Require Import Glibc.') or
                           line[len('Require Import Glibc.'):-1].replace('.', '/') + '.v' in selected) + '\n'
    plugin = out.parent / 'plugin'
    if not (plugin / 'META').exists():
        subprocess.run(['bash', str(HERE / 'check/plugin.sh'), str(plugin)], check=True)
    header = f'Declare ML Module "{plugin.name}".\n' + header
    environment = dict(os.environ)
    environment['OCAMLPATH'] = str(plugin.parent) + ':' + environment.get('OCAMLPATH', '')
    chunks = []
    visited = []
    for i, marker in enumerate(markers):
        body = source[marker.start():markers[i+1].start() if i+1 < len(markers) else len(source)]
        visited.append(body)
        if selected is not None and marker[1] not in selected:
            continue
        # A source file may contain many adapters. Bound each process to
        # sixteen pairs and one MiB, rejecting an oversized individual pair.
        if len(body.encode()) > 1024 * 1024:
            raise ValueError(f'50-program: adapter exceeds one MiB: {marker[1]}')
        directory = str(Path(marker[1]).parent)
        if (not chunks or chunks[-1][0] != directory or chunks[-1][2] == 16 or
                len((chunks[-1][1] + body).encode()) > 1024 * 1024):
            chunks.append([directory, '', 0])
        chunks[-1][1] += body
        chunks[-1][2] += 1
    assert source[:markers[0].start()] + ''.join(visited) == source
    print(f'program: checking {len(chunks)} adapter shards with four workers', flush=True)
    sys.path.insert(0, str(HERE / 'check'))
    from audit import assumption_types

    def compile_one(item):
        i, (rel, body, _) = item
        target = out / f'ProgramEquivalence{i:04d}.v'
        names = re.findall(r"\b(?:Lemma|Theorem|Corollary)\s+([\w']+)", normalized(tokens(header + body)))
        queries = []
        for name in names:
            queries += [f'Goal True. idtac "PE_ASSUMPTIONS_{name}". Abort.', f'Print Assumptions {name}.']
        for number in re.findall(r'Definition program_before_(\w+)\b', body):
            for side in ('before', 'after'):
                name = f'program_{side}_{number}'
                queries += [f'Goal True. idtac "PE_ASSUMPTIONS_{name}". Abort.', f'Print Assumptions {name}.']
        target.write_text(header + body + '\nSet Printing All. Set Printing Depth 1000000. Set Printing Width 1000000.\n' + '\n'.join(queries) + '\n')
        run = subprocess.run(['rocq', 'c', '-q', '-R', os.environ['PE_MODEL'], 'Nanofil',
                              '-R', str(tree), 'Glibc', str(target)], text=True,
                             stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=300, env=environment)
        target.with_suffix('.log').write_text(run.stdout)
        if run.returncode or '...' in run.stdout or '…' in run.stdout:
            raise ValueError(f'50-program: equivalence compilation or Closed audit failed: {target.with_suffix(".log")}')
        parts = re.split(r'PE_ASSUMPTIONS_(\w+)\n', run.stdout)
        facts = {parts[j]: assumption_types(parts[j+1], {}) for j in range(1, len(parts), 2)}
        valid = len(facts) == len(queries) // 2
        runtime_fields = {n for assumptions in facts.values() for n in assumptions}
        if selected is None:
            valid &= not runtime_fields and run.stdout.count('Closed under the global context') == len(facts)
        elif runtime_fields:
            # Ask Rocq about the declared Runtime signature and its actual
            # fields. A similarly named constant outside that module cannot
            # authorize an assumption.
            probe = target.with_name(target.stem + 'Runtime.v')
            field_queries = ['Print Module Type Nanofil.core.Runtime.Runtime.']
            ordered_fields = sorted(runtime_fields)
            for k, n in enumerate(ordered_fields):
                field_queries += [f'Goal True. idtac "PE_FIELD_{k}". Abort.', f'Locate {n}.', f'Print Assumptions {n}.']
            probe.write_text(header + '\nSet Printing All. Set Printing Depth 1000000. Set Printing Width 1000000.\n' + '\n'.join(field_queries))
            checked = subprocess.run(['rocq', 'c', '-q', '-R', os.environ['PE_MODEL'], 'Nanofil',
                                      '-R', str(tree), 'Glibc', str(probe)], text=True,
                                     stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=300, env=environment)
            probe.with_suffix('.log').write_text(checked.stdout)
            segments = re.split(r'PE_FIELD_(\w+)\n', checked.stdout)
            declared = set(re.findall(r'\b(?:Parameter|Axiom)\s+(\w+)\b', segments[0]))
            actual_fields, identities = {}, {}
            for j in range(1, len(segments), 2):
                located = re.search(r'^Constant (Glibc\.Fix\.R\.\w+)\b', segments[j+1], re.M)
                if not located:
                    raise ValueError(f'50-program: assumption is not a declared runtime field: {ordered_fields[int(segments[j])]}')
                identities[ordered_fields[int(segments[j])]] = located[1]
                actual_fields.update(assumption_types(segments[j+1], {}))
            valid &= checked.returncode == 0 and all(n.split('.')[-1] in declared for n in identities.values())
            valid &= all(actual_fields.get(n) == typ for assumptions in facts.values() for n, typ in assumptions.items())
            facts = {name: {identities[n]: typ for n, typ in assumptions.items()} for name, assumptions in facts.items()}
        records = []
        blocks = re.split(r"(?m)^\(\* ([\w/]+\.v): ([\w.']+)\. \*\)$", body)
        for j in range(1, len(blocks), 3):
            file, declaration, text = blocks[j:j+3]
            number = re.search(r'Definition program_before_(\w+)\b', text)[1]
            old, new, forward, reverse = [facts.get(f'program_{side}_{number}') for side in ('before', 'after', 'old_to_new', 'new_to_old')]
            valid &= old is not None and new == old and all(d is not None and d.items() <= old.items() for d in (forward, reverse))
            records.append({'file': file, 'name': declaration,
                            'adapters': [f'program_old_to_new_{number}', f'program_new_to_old_{number}'],
                            'before': old, 'after': new, 'directions': [forward, reverse]})
        if not valid:
            raise ValueError(f'50-program: adapter assumptions changed: {target.with_suffix(".log")}')
        print(f'program: shard {i+1}/{len(chunks)} audited: {rel}', flush=True)
        return records

    with ThreadPoolExecutor(max_workers=4) as pool:
        evidence = [pair for records in pool.map(compile_one, enumerate(chunks)) for pair in records]
    print(f'program: {2 * len(evidence)} directions compiled and audited in {time.monotonic()-started:.2f}s', flush=True)
    return evidence


def compile_targets(tree: Path, targets: list[str]) -> set[str]:
    files = sorted(str(p.relative_to(tree)) for p in tree.rglob('*.v'))
    flags = ['-R', os.environ['PE_MODEL'], 'Nanofil', '-R', '.', 'Glibc']
    dependency = subprocess.run(['rocq', 'dep', *flags, *files], cwd=tree,
                                text=True, stdout=subprocess.PIPE, check=True)
    graph = {}
    for line in dependency.stdout.replace('\\\n', ' ').splitlines():
        left, separator, right = line.partition(':')
        if separator:
            for target in left.split():
                if target.endswith('.vo'):
                    graph[str(Path(target))] = [str(Path(p)) for p in right.split() if p.endswith('.vo')]
    targets = [str(Path(t)) for t in targets]
    if any(t not in graph for t in targets):
        raise ValueError(f'50-program: unknown Rocq targets: {targets}')
    selected, pending = set(), list(targets)
    while pending:
        target = pending.pop()
        if target in selected:
            continue
        selected.add(target)
        pending.extend(p for p in graph[target] if p in graph)
    work = tree.parent / (tree.name + '.program')
    work.mkdir(parents=True, exist_ok=True)
    build_flags = ['-R', os.environ['PE_MODEL'], 'Nanofil', '-R', str(tree.resolve()), 'Glibc']
    build_files = [str((tree / f).resolve()) for f in files]
    build_targets = [str((tree / t).resolve()) for t in targets]
    subprocess.run(['rocq', 'makefile', *build_flags, *build_files, '-o', 'Makefile.program'], cwd=work, check=True)
    subprocess.run(['make', '-j12', '-f', 'Makefile.program', *build_targets], cwd=work, check=True)
    return {t[:-1] for t in selected}


def regenerate(original: Path):
    """Rebuild both runtime boundaries and replace the complete review packet."""
    backup = HERE.parents[3] / '.amp/in/orb-backup'
    backup.mkdir(parents=True, exist_ok=True)
    work = Path(tempfile.mkdtemp(prefix='program-regeneration-', dir=backup))
    print(f'program: retaining regeneration trees and logs in {work}', flush=True)
    def apply(destination, environment):
        with destination.with_suffix('.apply.log').open('w') as log:
            subprocess.run([str(HERE / 'apply.sh'), str(original), str(destination)],
                           env=environment, stdout=log, stderr=subprocess.STDOUT, check=True)
        return destination.parent / (destination.name + '.program/before')

    env = dict(os.environ)
    env.pop('PE_PROGRAM_TARGETS', None)
    env['PE_RUNTIME'] = 'concrete'
    after = work / 'concrete'
    before = apply(after, env)
    subprocess.run([str(HERE / 'build.sh'), str(after), '12'], check=True)
    check_evidence(after, refresh_review=True)

    # Runtime choice comes from the original source, never from transformed
    # imports or a hardcoded list of example programs.
    subprocess.run([sys.executable, str(HERE / 'check/check.py'), 'partition',
                    str(original), '--output', str(work / 'partition')], check=True)
    env['PE_RUNTIME'] = 'abstract'
    env['PE_PROGRAM_TARGETS'] = (work / 'partition/general-targets.txt').read_text().replace('\n', ' ')
    abstract = work / 'abstract'
    abstract_before = apply(abstract, env)
    selected = compile_targets(abstract, env['PE_PROGRAM_TARGETS'].split())
    check_evidence(abstract)
    print(f'program: regenerated and checked all three packet files; retained trees: {work}', flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('tree', type=Path)
    parser.add_argument('--check', action='store_true', help='validate source guards and compile every bidirectional adapter')
    parser.add_argument('--regenerate', action='store_true', help='apply all stages to an original tree and regenerate concrete/abstract evidence')
    parser.add_argument('--refresh-tables', action='store_true', help='regenerate indexed instances after editing program-table rows')
    parser.add_argument('--inspect', action='store_true')
    parser.add_argument('--metadata', type=Path)
    parser.add_argument('--source', type=Path, help='read a compiled pre-stage tree without modifying it')
    parser.add_argument('--candidates', type=Path, help='write statement-discovery candidates comparing --source with tree')
    parser.add_argument('--emit-evidence', type=Path, help='emit the three review files from a complete statement report')
    parser.add_argument('--plugin', type=Path, help='compiled checker printer plugin for evidence queries')
    args = parser.parse_args()
    tree = args.tree.resolve()
    source_tree = args.source.resolve() if args.source else tree
    if args.refresh_tables:
        refresh_tables(tree)
        return
    if args.source and not args.metadata and not args.candidates:
        parser.error('--source requires --metadata from that source tree')
    if 'PE_MODEL' not in os.environ:
        raise SystemExit('50-program: source proof-eng/env.sh before running this stage')
    if args.regenerate:
        regenerate(tree)
        return
    if args.check:
        check_evidence(tree)
        return
    if args.candidates:
        if not args.source:
            parser.error('--candidates requires --source')
        statement_candidates(source_tree, tree, args.candidates)
        return
    if args.emit_evidence:
        if not args.source or not args.metadata or not args.plugin:
            parser.error('--emit-evidence requires --source, --metadata and --plugin')
        emit_evidence(source_tree, tree, json.loads(args.metadata.read_text()), args.emit_evidence, args.plugin)
        return
    if not args.metadata:
        # The tree imports overlay files, and main has earlier versions of
        # them. The overlay's versions must be in place before the sources
        # are read and the pre-stage tree is compiled for About metadata,
        # so that each reference map matches the source it was read with.
        for p in (HERE / 'overlay').rglob('*.v'):
            if p.name != 'GlibcProgram.v':
                destination = tree / p.relative_to(HERE / 'overlay')
                destination.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(p, destination)
    sources = [read_source(p) for p in sorted(source_tree.rglob('*.v'))]
    if args.source and args.metadata:
        sources = [s for s in sources if s.path.with_suffix('.vo').exists()]
    relevant = [s for s in sources if any(x.canonical for x in s.sections)]
    targets = os.environ.get('PE_PROGRAM_TARGETS', '').split()
    if targets and args.metadata:
        parser.error('targeted audits collect fresh compiler metadata; omit --metadata')
    out = tree.parent / (tree.name + '.program')
    out.mkdir(exist_ok=True)
    if args.metadata:
        metadata = json.loads(args.metadata.read_text())
    else:
        if targets:
            selected = compile_targets(tree, targets)
            sources = [s for s in sources if str(s.path.relative_to(tree)) in selected]
            relevant = [s for s in sources if any(x.canonical for x in s.sections)]
            print(f'program: targeted audit, {len(selected)} source files in the compiler dependency closure')
        else:
            subprocess.run([str(HERE / 'build.sh'), str(tree), '12'], check=True)
        metadata = dump_metadata(tree, relevant, out / 'metadata')
    report = [{'file': str(s.path.relative_to(source_tree)), 'section': x.name,
               'canonical': x.canonical, 'reason': x.reason, 'declarations': x.declarations}
              for s in sources for x in s.sections]
    (out / 'sections.json').write_text(json.dumps(report, indent=2) + '\n')
    print(f'program: {sum(x["canonical"] for x in report)} canonical sections; {len(metadata)} declarations inspected')
    for item in report:
        if not item['canonical']:
            print(f'program: retained {item["file"]}:{item["section"]}: {item["reason"]}')
    if args.inspect:
        return
    conversions = {}
    planned = {}
    for source in relevant:
        edits, entries = section_edits(source, metadata)
        planned[source.path] = edits
        conversions.update(entries)
    # Keep only the old instance constants that occur in inferred endpoint
    # types. They remain ordinary definitions, never competing instances.
    legacy = {}
    for source in sources:
        load_references(source)
        for name, declaration in source.declarations.items():
            body = inferred_body(declaration)
            if not protected_name(name) or body is None:
                continue
            for position, reference in source.references.items():
                conversion = conversions.get(reference)
                if (body[0] <= position < body[1] and conversion and
                        not conversion.retained and not conversion.wrapped):
                    legacy[(conversion.source.path, conversion.section.start)] = conversion
    wrapper_pairs = []
    for conversion in conversions.values():
        if conversion.wrapped:
            rel = str(conversion.source.path.relative_to(source_tree))
            wrapper_pairs.append({'file': rel, 'wrapper': conversion.name, 'implementation': conversion.implementation})
            print(f'program: wrapper {rel}:{conversion.name} <- {conversion.implementation}')
    (out / 'wrappers.json').write_text(json.dumps(wrapper_pairs, indent=2) + '\n')
    calls = []
    rewritten = {}
    table_instances = {name for source in sources for _, _, text in table_edits(source)
                       for name in re.findall(r'Lemma (\w+) : Defines', text)}
    for source in sources:
        edits = planned.get(source.path, [])
        context_ranges = {(s[0].start, s[-1].end) for section in source.sections for s in section.contexts}
        reserved = [(a, b, t) for a, b, t in edits if (a, b) not in context_ranges]
        call_edits = rewrite_calls(source, conversions, reserved, calls, table_instances)
        if source.path in planned:
            edits, _ = section_edits(source, metadata, call_edits)
        for (path, position), conversion in legacy.items():
            if path == source.path:
                name, _ = legacy_instance(conversion)
                text = (f'Definition {name} `{{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}}\n'
                        '  (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv) :\n'
                        '  irisGS_gen hlc (nanofil_lang registry ge) Σ :=\n'
                        '  nanofil_irisGS registry (os_wi w0) ge.\n\n')
                edits.append((position, position, text))
        edits += table_edits(source)
        edits += [(a, b, t) for a, b, t in call_edits
                  if not any(x <= a and b <= y for x, y, _ in edits if x != y)]
        for name, declaration in source.declarations.items():
            body = inferred_body(declaration)
            if body is None:
                continue
            start, end = body
            if any(start <= a <= b <= end and 'program_of' in text for a, b, text in call_edits):
                # Keep inferred legacy endpoint types free of bundle projections.
                prefix = 'program_call('
                if protected_name(name):
                    uses = [c for c in calls if c['file'] == str(source.path) and
                            start <= c.get('position', -1) < end and c['bundle_argument']]
                    if len(uses) != 1 or len(uses[0]['program_values']) != 3:
                        fail(source, declaration[0], 'inferred endpoint needs one complete program application')
                    conversion = conversions[uses[0]['declaration']]
                    _, instance = legacy_instance(conversion)
                    values = uses[0]['program_values']
                    arguments = ' '.join(term_argument(values[n]) for n in ('w0', 'registry', 'ge'))
                    prefix = f'program_call_with (@{instance} hlc Σ _ _ {arguments}) ('
                edits.extend([(start, start, prefix), (end, end, ')')])
        if edits:
            edits.append((0, 0, 'From Glibc Require Import GlibcProgram.\n'))
            first = next((section for section in source.sections if section.canonical), None)
            if first:
                position = first.start
                if first.scope:
                    position = next(s[0].start for s in sentences(source.ts)
                                    if s[0].text == 'Module' and first.scope[0] in [t.text for t in s[1:3]])
                edits.append((position, position, 'Import ProgramAbbreviations.\n'))
            rewritten[source.path] = apply_edits(source, edits)
        elif source_tree != tree:
            rewritten[source.path] = source.text
    # Complete all parsing before changing any source file.
    if source_tree == tree:
        snapshot = out / 'before'
        if snapshot.exists():
            shutil.rmtree(snapshot)
        shutil.copytree(tree, snapshot)
    for path, text in rewritten.items():
        destination = tree / path.relative_to(source_tree)
        if not destination.exists() or destination.read_text() != text:
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_text(text)
    library = (HERE / 'overlay/GlibcProgram.v').read_text()
    if not (tree / 'GlibcProgram.v').exists() or (tree / 'GlibcProgram.v').read_text() != library:
        (tree / 'GlibcProgram.v').write_text(library)
    project = tree / '_RocqProject'
    if project.exists():
        lines = (source_tree / '_RocqProject').read_text().splitlines()
        if 'GlibcProgram.v' not in lines:
            lines.insert(lines.index('zsys/OsWorld.v') + 1, 'GlibcProgram.v')
            project.write_text('\n'.join(lines) + '\n')
    (out / 'calls.json').write_text(json.dumps(calls, indent=2) + '\n')
    print(f'program: bundled {sum(not c.retained for c in conversions.values())} declarations; '
          f'retained {sum(c.retained for c in conversions.values())} value or partial interfaces; '
          f'{len(wrapper_pairs)} audited wrappers; recorded {len(calls)} applications')


if __name__ == '__main__':
    main()
