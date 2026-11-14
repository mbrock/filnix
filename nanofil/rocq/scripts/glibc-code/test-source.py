"""Check context linking and source-table extraction through their command interfaces."""
import json
import os
from pathlib import Path
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
block(start,[],[copy(tmp(v),w,tmp(arg))],goto(loop)),
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
                          loop_heads=['loop'], blocks=4, temps=4),
                     dict(function='no_context', source=None, block_src=[],
                          temp_names=[], loop_heads=[], blocks=1, temps=0)], facts
print('source tables: default bytes, local/weak/archive contexts, sites, recorded names and loop headers passed')
