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
                           'root': 'p', 'root_offset': 26}
    assert accesses[1] == {'index': 5, 'address': {'kind': 'tmp', 'name': 'b'},
                           'offset': 0, 'width': 8, 'read': False, 'write': True,
                           'root': 'p', 'root_offset': None}
    assert blocks['local']['footprint'] == [
        {'index': 1, 'address': {'kind': 'local', 'name': 'scratch'},
         'offset': 4, 'width': 4, 'read': True, 'write': False, 'root': None, 'root_offset': None}]

print('block facts: phi-edge liveness, byte widths, proof operands and constant/dynamic roots passed')
