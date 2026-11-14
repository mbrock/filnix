"""Check edge liveness and distinguish pointer offsets from capability donors."""
import json
from pathlib import Path
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent

with tempfile.TemporaryDirectory() as tmp:
    path = Path(tmp) / 'blocks.term'
    path.write_text('''module([func(f,export,w,[param(p,tmp(p)),param(l,tmp(delta)),param(w,tmp(c))],[
      block(start,[],[
        flight(tmp(a),add,[address(tmp(p)),const(24)],lower(tmp(p))),
        let(tmp(q),a,check(0,6,read,1),[tmp(a)]),
        let(tmp(v),w,raw_load(uw,2),[tmp(q)]),
        flight(tmp(b),add,[address(tmp(p)),tmp(delta)],lower(tmp(p))),
        let(tmp(r),a,check(0,8,write,8),[tmp(b)]),
        raw_store_pointer(0,tmp(p),tmp(r),[aux_ensure,lower_barrier,rooted_reload,lower_write,address_write])
      ],branch(tmp(c),left,right)),
      block(left,[],[],goto(join)),
      block(right,[],[let(tmp(other),w,copy,[const(7)])],goto(join)),
      block(join,[phi(tmp(z),w,[left-tmp(v),right-tmp(other)])],[],ret(tmp(z))),
      block(local,[],[local_alloc(scratch,16),uses(local_load(tmp(lv),w,uw,scratch,4),[tmp(p)])],ret(tmp(lv)))
    ])]).''')
    result = subprocess.check_output([HERE.parents[2] / 'bin/nanofil', '--script',
                                      HERE / 'block-facts.pl', path, 'f'], text=True)
    rows = json.loads(result)
    all_functions = subprocess.check_output([HERE.parents[2] / 'bin/nanofil', '--script',
                                             HERE / 'block-facts.pl', path], text=True)
    assert json.loads(all_functions) == rows
    blocks = {b['label']: b for b in rows[0]['blocks']}
    assert blocks['start']['live_in'] == ['c', 'delta', 'p']
    assert blocks['left']['live_in'] == ['v']
    assert blocks['right']['live_in'] == []
    assert blocks['join']['live_in'] == []  # The phi defines z; its arguments are edge reads.
    assert blocks['left']['live_out'] == ['v']
    assert blocks['right']['live_out'] == ['other']
    accesses = blocks['start']['footprint']
    assert len(accesses) == 2
    assert accesses[0] == {'index': 2, 'address': {'kind': 'tmp', 'name': 'a'},
                           'offset': 2, 'width': 4, 'read': True, 'write': False,
                           'root': 'p', 'root_offset': 26, 'path': 'opaque'}
    assert accesses[1] == {'index': 5, 'address': {'kind': 'tmp', 'name': 'b'},
                           'offset': 0, 'width': 8, 'read': False, 'write': True,
                           'root': 'p', 'root_offset': None, 'path': 'opaque'}
    assert blocks['local']['footprint'] == [
        {'index': 1, 'address': {'kind': 'local', 'name': 'scratch'},
         'offset': 4, 'width': 4, 'read': True, 'write': False, 'root': None,
         'root_offset': None, 'path': 'opaque'}]

    # Real checked origins include generated children beside typed children.
    source = Path(tmp) / 'paths.c'
    source.write_text('''
struct Lock { int lock; int count; void *owner; };
struct File { int flags; char *write_ptr; struct Lock *lock; struct Lock embedded; };
struct Extended { struct File base; long extra; };
union Choice { int left; int right; };
void paths(struct File *fp, union Choice *u, char *q, long n) {
  fp->write_ptr = q;
  fp->lock->owner = q;
  fp->embedded.owner = q;
  u->right = 7;
  ((char **)fp)[1] = q;
  ((char *)fp)[4] = 0;
  q[n] = 0;
}
char read_data(struct File *fp) { return *fp->write_ptr; }
long read_extra(struct File *fp) { return ((struct Extended *)fp)->extra; }
''')
    nanofil = HERE.parents[2] / 'bin/nanofil'
    ir, code, layouts = (Path(tmp) / n for n in ('paths.ir', 'paths.term', 'layouts.term'))
    ir.write_text(subprocess.check_output([nanofil, '-O', 'cc-ir', source], text=True))
    code.write_text(subprocess.check_output([nanofil, '--script', HERE.parents[2] / 'bench/trap-checked.pl', ir], text=True))
    layouts.write_text(subprocess.check_output([nanofil, 'cc-layouts', source], text=True))
    other, wrong_layouts = (Path(tmp) / n for n in ('other.term', 'wrong-layouts.term'))
    other.write_text(code.read_text().replace(str(source), 'different-unit.c'))
    wrong_layouts.write_text(layouts.read_text().replace('write_ptr', 'wrong_field'))
    command = [nanofil, '--script', HERE / 'block-facts.pl', code, 'paths',
               '--unit', f'other={other}={wrong_layouts}', '--unit', f'actual={code}={layouts}']
    facts = json.loads(subprocess.check_output(command, text=True))
    accesses = [a for b in facts[0]['blocks'] for a in b['footprint']]
    assert [a['path'] for a in accesses] == [
        'fp->write_ptr', 'fp->lock', 'fp->lock->owner', 'fp->embedded.owner',
        'u->right', 'fp->write_ptr', 'opaque', 'opaque'], accesses

    facts = json.loads(subprocess.check_output(command[:5], text=True))
    paths = [a['path'] for b in facts[0]['blocks'] for a in b['footprint']]
    assert paths[:5] == [
        'fp->write_ptr', 'fp->lock', 'fp->lock->owner', 'fp->embedded.owner',
        'u->right'], facts
    assert paths[-2:] == ['opaque', 'opaque'], facts

    data_command = command.copy()
    data_command[data_command.index('paths')] = 'read_data'
    facts = json.loads(subprocess.check_output(data_command, text=True))
    assert [a['path'] for b in facts[0]['blocks'] for a in b['footprint']] == ['fp->write_ptr', 'opaque']

    extra_command = command.copy()
    extra_command[extra_command.index('paths')] = 'read_extra'
    facts = json.loads(subprocess.check_output(extra_command, text=True))
    assert [a['path'] for b in facts[0]['blocks'] for a in b['footprint']] == ['fp->extra'], facts

    # Without a member description, the complete layout can still recover it.
    code.write_text(code.read_text().replace('member(write_ptr)', 'unresolved_member'))
    facts = json.loads(subprocess.check_output(command, text=True))
    accesses = [a for b in facts[0]['blocks'] for a in b['footprint']]
    assert accesses[0]['path'] == 'fp->write_ptr', accesses[0]

    # Unions without a selecting source expression must not choose a member.
    code.write_text(code.read_text().replace('member(right)', 'unresolved_member'))
    facts = json.loads(subprocess.check_output(command, text=True))
    accesses = [a for b in facts[0]['blocks'] for a in b['footprint']]
    assert accesses[4]['path'] == 'opaque', accesses[4]

print('block facts: liveness, widths, roots, typed member paths, scoped layouts and opaque fallbacks passed')
