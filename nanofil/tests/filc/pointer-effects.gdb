# The allocation-root exit wrapper is inlined at the staging pin. Locate
# ensure_aux_ptr_slow_large's actual filc_exit call from disassembly rather
# than breaking on the wrapper's unused exported entry or pinning an offset.
set pagination off
set confirm off
set print thread-events off
set environment FUGC_SCRIBBLE 1
set environment FUGC_VERIFY 1
set environment FUGC_STW 0
start
python
import gdb, re
counts = dict(ensure_exits=0, store_barriers=0)
class Counter(gdb.Breakpoint):
    def __init__(self, spec, key):
        super().__init__(spec, internal=True)
        self.key = key
    def stop(self):
        caller = gdb.newest_frame().older()
        if caller and 'large_store' in (caller.name() or ''):
            counts[self.key] += 1
        return False
dis = gdb.execute('disassemble ensure_aux_ptr_slow_large', to_string=True)
sites = re.findall(r'(0x[0-9a-f]+)\s+<\+\d+>:\s+call\s+.*<filc_exit@plt>', dis)
assert len(sites) == 1, dis
Counter('*' + sites[0], 'ensure_exits')
Counter('filc_store_barrier_for_lower_slow', 'store_barriers')
end
continue
python
assert gdb.parse_and_eval('$_exitcode') == 0, 'inferior did not succeed'
print('pointer-effects helper coverage:', counts)
assert counts['ensure_exits'] == 20, 'not every store took the actual exit'
assert counts['store_barriers'] > 0, 'no lower barrier exercised'
end
