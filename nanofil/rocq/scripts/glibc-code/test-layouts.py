"""Check layout sharing across fixtures with distinct C type environments."""
from pathlib import Path
import runpy

layout = runpy.run_path(str(Path(__file__).with_name('layout.py')))
fixture_layout, layout_tables = layout['fixture_layout'], layout['layout_tables']
shared = layout['SHARED']

first = dict(tag='struct pair', size=8, align=4, fields=[['x', 0, 4, 4], ['y', 4, 4, 4]])
second = dict(first, fields=[['y', 0, 4, 4], ['x', 4, 4, 4]])
private = dict(tag='struct private', size=8, align=8, fields=[['z', 0, 8, 8]])
missing = dict(tag='struct opaque', missing=True)
forward = dict(tag='struct pair', missing=True)
fixtures = {
    Path('a/FirstLayout.v'): fixture_layout('First', [private, missing, first, first, forward]),
    Path('b/SecondLayout.v'): fixture_layout('Second', [first]),
    Path('c/ThirdLayout.v'): fixture_layout('Third', [second]),
    Path('d/FourthLayout.v'): fixture_layout('Fourth', [second]),
}
files = layout_tables(fixtures)
assert files == layout_tables(dict(reversed(list(fixtures.items()))))
definitions = {path.stem: source for path, source in files.items() if path.parent == shared}
assert len(definitions) == 2
first_module, = [name for name, source in definitions.items() if '("x", 0, 4, 4)' in source]
second_module, = [name for name, source in definitions.items() if '("x", 4, 4, 4)' in source]
for path, source in files.items():
    if path.parent == shared:
        continue
    expected = first_module if path.parent.name in ('a', 'b') else second_module
    assert f'{expected}.layout_struct' in source
    assert '(mkRecordLayout "struct pair"' not in source
first_view = files[Path('a/FirstLayout.v')]
assert first_view.index(f'{first_module}.layout_struct') < first_view.index('mkRecordLayout "struct private"')
assert 'Definition unavailable : list string := ["struct opaque"].' in first_view

try:
    fixture_layout('Conflict', [first, second])
except ValueError as error:
    assert str(error) == 'inconsistent layouts for struct pair in Conflict'
else:
    raise AssertionError('conflicting layouts in one fixture were accepted')

print('layouts: shared complete records, distinct layouts with the same tag, and ordered fixture views')
