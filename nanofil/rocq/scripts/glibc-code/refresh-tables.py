#!/usr/bin/env python3
"""Regenerate indexed Defines instances after editing a glibc program table."""
import argparse
from dataclasses import dataclass
from pathlib import Path
import re


@dataclass
class Token:
    text: str
    start: int
    end: int


def tokens(source):
    """Read Gallina tokens without losing positions or reading comments."""
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


def sentences(ts):
    result = []
    start = 0
    for i, token in enumerate(ts):
        if token.text == '.' and (i + 1 == len(ts) or token.end < ts[i+1].start):
            result.append(ts[start:i+1])
            start = i + 1
    if start != len(ts):
        raise ValueError('source does not end in a sentence')
    return result


def normalized(ts):
    return ' '.join(t.text for t in ts)


def table_instance(name, ge, table, index, symbol, fn):
    return f'''Lemma {name} : Defines {ge} {symbol} {fn}.
Proof. exact (defines_from_table_nth {ge} {table} {index} {symbol} {fn} {table}_correct eq_refl). Qed.
#[global] Existing Instance {name}.'''


def refresh_tables(tree):
    planned = {}
    count = 0
    for path in sorted(tree.rglob('*.v')):
        text = path.read_text()
        ss = sentences(tokens(text))
        edits = []

        def fail(token, message):
            line = text.count('\n', 0, token.start) + 1
            raise ValueError(f'{path}:{line}: {message}')

        for sentence in ss:
            match = re.fullmatch(r'Definition (\w+_program_table) : list \( string \* func \) := (.*) \.', normalized(sentence))
            if not match:
                continue
            table, body = match.groups()
            row_pattern = r'\( ("[^"]+") , ([\w.]+) \) :: '
            rows = re.findall(row_pattern, body)
            if not rows or re.sub(row_pattern, '', body) != 'nil':
                fail(sentence[0], 'unsupported program-table row')
            if len({symbol for symbol, _ in rows}) != len(rows):
                fail(sentence[0], 'duplicate program-table symbol')
            certificate = next((s for s in ss if [t.text for t in s[:2]] == ['Lemma', table + '_correct']), None)
            ge_match = re.search(r'find_fn (\w+) \( TAtom n \)', normalized(certificate)) if certificate else None
            if not ge_match:
                fail(sentence[0], 'missing program-table certificate')
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
                    fail(declaration[0], f'table row removal would remove exported instance {name}')
                if end+1 >= len(ss) or normalized(ss[end+1]) != f'# [ global ] Existing Instance {name} .':
                    fail(declaration[0], 'generated instance registration is missing')
                index = next(j for j, row in enumerate(rows) if row[0] == symbol)
                replacement = table_instance(name, ge, table, index, symbol, rows[index][1])
                insertion = ss[end+1][-1].end
                edits.append((declaration[0].start, insertion, replacement))
                present.add(symbol)
            if insertion is None:
                fail(sentence[0], 'no generated instances anchor this table')
            additions = []
            for i, (symbol, fn) in enumerate(rows):
                if symbol not in present:
                    name = table + '_defines_' + symbol[1:-1].encode('utf8').hex()
                    additions.append(table_instance(name, ge, table, i, symbol, fn))
            if additions:
                edits.append((insertion, insertion, '\n' + '\n'.join(additions)))
            count += len(rows)
        if edits:
            previous = len(text) + 1
            for start, end, replacement in sorted(set(edits), reverse=True):
                if end > previous:
                    fail(Token('', start, end), 'overlapping instance rewrites')
                text = text[:start] + replacement + text[end:]
                previous = start
            planned[path] = text
    for path, text in planned.items():
        path.write_text(text)
    print(f'program: refreshed {count} indexed instances in {len(planned)} files; compile their certificates next')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('tree', type=Path)
    refresh_tables(parser.parse_args().tree)
