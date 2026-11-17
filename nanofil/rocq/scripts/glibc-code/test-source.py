"""Check context linking and source-table extraction through their command interfaces."""
import json
import os
from pathlib import Path
import runpy
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
SWIPL = os.environ.get('SWIPL', 'swipl')


def run(script, *args):
    return subprocess.check_output([SWIPL, str(script), *map(str, args)], text=True)


with tempfile.TemporaryDirectory() as tmp:
    tmp = Path(tmp)
    a, b, archive = (tmp / n for n in ('a.term', 'b.term', 'archive.term'))
    a.write_text('''module([
func(main,export,w,[],[block(start,[],[call(none,global(localfn),[])],ret)]),
context(main,[origin(0,at('a.c',7),statement(function),[])]),
func(localfn,local,w,[],[block(start,[],[],ret)]),
context(localfn,[binding(x,localfn,int,none),value(x,named(x,value),[])]),
func(dead,local,w,[],[block(start,[],[],ret)]),context(dead,[]),
func(win,weak,w,[],[block(start,[],[],ret)]),context(win,[loser]),
data(root,export,8,[item(p,sym(win,0)),item(p,sym(main,0))])]).
''')
    b.write_text('''module([func(win,export,w,[],[block(start,[],[],ret)]),
context(win,[winner,origin(0,none,global(archive_only),[])])]).
''')
    archive.write_text('module([func(archive_only,export,w,[],[block(start,[],[],ret)])]).\n')
    specs = ['root', f'a={a}', f'b={b}', '--archive', f'archive={archive}']
    plain = run(HERE.parent / 'link.pl', *specs)
    assert plain == '''module([func(main,export,w,[],[block(start,[],[call(none,global('a#localfn'),[])],ret)]),
func('a#localfn',local,w,[],[block(start,[],[],ret)]),
data(root,export,8,[item(p,sym(win,0)),item(p,sym(main,0))]),
func(win,export,w,[],[block(start,[],[],ret)])]).
''', plain
    kept = run(HERE.parent / 'link.pl', '--context', *specs)
    assert "context('a#localfn',[binding(x,localfn,int,none)" in kept
    assert 'context(dead' not in kept and 'loser' not in kept
    assert 'context(win,[winner' in kept and 'func(archive_only' not in kept

    module = tmp / 'source.term'
    module.write_text('''module([
func(f,export,w,[param(w,tmp(arg))],[
block(start,[],[copy(tmp(v),w,tmp(arg)),let(tmp(c),a,check(0,8,read,8),[tmp(arg)]),
flight(tmp(q),add,[address(tmp(c)),const(8)],lower(tmp(c))),
flight(tmp(r),add,[address(tmp(u)),const(-4)],lower(tmp(u))),
let(tmp(ld),w,raw_load(sw,4),[tmp(c)]),let(tmp(t),w,cmp(ne,w),[tmp(ld),const(0)]),
let(tmp(g),p,copy,[global(null)]),call(result(tmp(k),w),global(callee),[]),
let(tmp(c2),a,check(0,8,read,8),[tmp(arg)])],goto(loop)),
block(loop,[phi(tmp(p),w,[start-tmp(v),loop-tmp(p)])],[],branch(tmp(p),loop,done)),
block(done,[],[],ret(tmp(p))),block(dead,[],[],ret)]),
context(f,[origin(0,at('unit.c',4),statement(function),[]),
origin(1,at('unit.c',20),statement(decl),[]),origin(2,at('unit.c',30),statement(expr),[]),
origin(3,none,generated(pass,test),[1]),
site(inst(start,0),[3]),site(jump(start),[2]),site(phi(p),[1]),
site(jump(loop),[2]),site(jump(done),[2]),
binding(a,'count',int,none),binding(b,'count',int,none),
value(arg,named(a,value),[0]),value(v,named(b,address),[1]),
value(p,named(b,value),[1]),value(retired,named(a,value),[1])]),
func(no_context,export,w,[],[block(start,[],[],ret)])]).
''')
    facts = json.loads(run(HERE / 'source.pl', module))
    assert facts == [dict(function='f', source=['unit.c', 4],
                          block_src=[['start', 'unit.c', 20], ['loop', 'unit.c', 20],
                                     ['done', 'unit.c', 30]],
                          temp_names=[['arg', 'count'], ['p', 'count'], ['retired', 'count']],
                          temp_keys=[['arg', 'arg', 'count', 0], ['c', 'arg', 'count', 0],
                                     ['c2', 'arg', 'count', 0],
                                     ['p', 'p', 'count', 0], ['q', 'arg', 'count', 8],
                                     ['r', 'u', 'u', -4], ['v', 'v', '&count', 0]],
                          key_kinds=dict(current=12, named=2, address=1, derived=3, raw=6),
                          temp_shapes=[['arg', 'start', -1, ['named', 'count']],
                                       ['p', 'loop', -1, ['named', 'count']],
                                       ['c', 'start', 1, ['check', 'arg']],
                                       ['q', 'start', 2, ['add', 'c', 8]],
                                       ['r', 'start', 3, ['add', 'u', -4]],
                                       ['ld', 'start', 4, ['load', 'c', 4]],
                                       ['t', 'start', 5, ['cmp', 'ne', ['tmp', 'ld'], ['const', 0]]],
                                       ['g', 'start', 6, ['global', 'null']],
                                       ['k', 'start', 7, ['call', 'callee']],
                                       ['c2', 'start', 8, ['check', 'arg']]],
                          loop_heads=['loop'], blocks=4, temps=13),
                     dict(function='no_context', source=None, block_src=[],
                          temp_names=[], temp_keys=[],
                          key_kinds=dict(current=0, named=0, address=0, derived=0, raw=0),
                          temp_shapes=[], loop_heads=[], blocks=1, temps=0)], facts

# A name is the C expression of its temporary. A load without a field path is
# written as its address in brackets, and one with a path is the path. Only a
# later temporary with a taken name gets a label suffix. A temporary that rests
# on an unnamed one gets no name, and neither does a name that Rocq could not
# read as one token.
names = runpy.run_path(str(HERE / 'names.py'))
rows, count = names['function_names'](facts[0]['temp_shapes'], {})
assert rows == [('arg', 'count'), ('p', 'count@loop'), ('c', 'chk(count)'), ('q', 'chk(count)+8'),
                ('ld', '[count+4]'), ('t', '[count+4]!=0'), ('g', '&null'), ('k', 'callee()'),
                ('c2', 'chk(count)@start')], rows
assert count == dict(named=3, derived=6, raw=1, suffixed=2), count
rows, _ = names['function_names'](facts[0]['temp_shapes'], {('start', 4): 'count->field'})
assert ('ld', 'count->field') in rows and ('t', 'count->field!=0') in rows, rows
rows, count = names['function_names'](
    [['x', 'start', -1, ['named', 'x']], ['a', 'L1', 0, ['check', 'x']], ['b', 'L1', 1, ['check', 'x']],
     ['c', 'L1', 2, ['check', 'x']], ['d', 'L2', 0, ['add', 'x', -8]], ['e', 'L2', 1, ['named', 'a b']],
     ['f', 'L2', 2, ['load', 'e', 0]], ['g', 'L2', 3, ['named', "it's"]], ['h', 'L2', 4, ['raw']]], {})
assert rows == [('x', 'x'), ('a', 'chk(x)'), ('b', 'chk(x)@L1'), ('c', 'chk(x)@L1.2'), ('d', 'x-8')], rows
assert count == dict(named=1, derived=4, raw=4, suffixed=2), count
text, counts = names['name_tables']('Unit', facts, [dict(function='f', blocks=[])])
assert 'Module UnitNames.\n\nModule fn_f.\nNotation "\'\u2039count\u203a\'" := (TAtom "arg").\n' in text, text
assert 'Notation "\'\u2039chk(count)@start\u203a\'" := (TAtom "c2").\nEnd fn_f.\n\nModule fn_no_context.\nEnd fn_no_context.' in text
assert 'do not edit' in text[:1000].lower() and list(counts) == ['f', 'no_context']
print('source tables: default bytes, local/weak/archive contexts, sites, recorded names, keys, shapes, notation names and loop headers passed')
