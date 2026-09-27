# jemalloc on Fil-C's allocator

`pkgsFilc.jemalloc` is not jemalloc's allocator. It is jemalloc's API
(`<jemalloc/jemalloc.h>`, `libjemalloc`, `jemalloc.pc`, `jemalloc-config`)
implemented on Fil-C's garbage-collected heap, the same approach as
[boehm-on-fugc.md](boehm-on-fugc.md). The code is in `ports/jemalloc/`, and
`ports/overlay.nix` wires it in.

## Why not port jemalloc itself

Upstream jemalloc 5.3.1 nearly runs under Fil-C. Its tests stop in
`pages_boot` on a raw `syscall(SYS_open)` and in the DSS code on inline
`brk`, but with `JEMALLOC_USE_SYSCALL` and `JEMALLOC_DSS` turned off its
`a0`, `mallctl` and `rtree` unit tests pass. Running it is the problem:

- jemalloc hands out slices of large mmap'd extents, and every slice
  carries the capability of the whole mapping. A program that reads past a
  16-byte `mallocx` object reads its neighbour, and after `dallocx` the
  stale pointer reads whatever jemalloc put there next:

  ```
  p=0x7f3aa6f0a000 q=0x7f3aa6f0a010 usable=16
  p[q-p]=w (reads q through p)
  stale p=reuse r=0x7f0138a8a000
  ```

  Fil-C's own allocator traps on both.
- On Linux jemalloc is built without a symbol prefix, so it replaces
  `malloc`, `free` and the rest for the whole process. Linking a program
  with `-ljemalloc` would turn off heap safety for every allocation in it,
  including those made inside other libraries.
- It would only duplicate work: every Fil-C allocation is already
  collected by FUGC.

So nothing jemalloc does for performance survives, and what it costs is
the point of Fil-C. Consumers only need the API.

## Mapping

| jemalloc                               | Implementation |
|----------------------------------------|----------------|
| `malloc`, `calloc`, `realloc`, `free`, `posix_memalign`, `aligned_alloc`, `memalign`, `valloc`, `pvalloc`, `malloc_usable_size`, `free_sized`, `free_aligned_sized` | not defined; libc's, which forward to `zgc_alloc` and friends |
| `mallocx`                              | `zgc_alloc`, or `zgc_aligned_alloc` for `MALLOCX_ALIGN` above 16. Memory is always zeroed, so `MALLOCX_ZERO` is free. Size 0 allocates 1 byte, as jemalloc does |
| `rallocx`                              | `zgc_realloc` / `zgc_aligned_realloc`; growth is zero-filled |
| `xallocx`                              | cannot grow in place; returns the current size, as jemalloc does when it cannot |
| `sallocx`                              | `zgetupper(p) - p`, which equals `malloc_usable_size` |
| `nallocx`                              | the size rounded up to 16, which is exactly what `zgc_alloc` gives (checked for every size below 70000 and sampled to 3 MB) |
| `dallocx`, `sdallocx`                  | `zgc_free`; later accesses trap |
| `MALLOCX_ARENA`, `MALLOCX_TCACHE*`     | accepted and ignored |
| `mallctl`, `mallctlnametomib`, `mallctlbymib` | a table of the names below |
| `malloc_stats_print`                   | a short report (JSON with `J`) through the callback, `malloc_message` or stderr |
| `malloc_conf`, `malloc_conf_2_conf_harder` | weak definitions; an application's own definition wins. Options are ignored |

### mallctl

The table mimics a jemalloc with one arena, no thread caches and no
profiling. Unknown names return `ENOENT`, writes to read-only names
`EPERM`, and a wrong `*oldlenp` gets jemalloc's partial copy and `EINVAL`.

- `version`, `epoch` (read-write), `background_thread` and
  `max_background_threads` (writes accepted).
- `config.*`: `stats` is true, everything else false. `config.prof` is
  false, so `prof.*` does not exist and callers skip profiling.
- `opt.*`: the common ones, with values describing the shim (`opt.tcache`
  false, `opt.zero` true, `opt.dss` "disabled", `opt.narenas` 1, ...).
- `arenas.create` returns increasing indexes and `arenas.narenas` counts
  them. `arena.<i>.{purge,decay,reset,destroy}` succeed for existing
  indexes, for `MALLCTL_ARENAS_ALL` and for `narenas` (jemalloc's older
  spelling of "all arenas", which Redis uses); `arena.<i>.*_decay_ms` and
  `arenas.*_decay_ms` store the value. `tcache.{create,flush,destroy}`,
  `thread.tcache.*`, `thread.arena` and `thread.idle` are accepted.
- `arenas.page` is 4096 and `arenas.quantum` 16. There is one bin
  (`arenas.nbins` = 1, `arenas.bin.0.size` = 16), so code that walks bins,
  such as Redis's fragmentation estimate, finds valid entries.
- `stats.allocated`, `active`, `resident` and `mapped`, and the per-arena
  `resident`, `mapped`, `small.allocated` and `pactive` of arena 0 (and
  of "all arenas"), report the process's resident memory from
  `/proc/self/statm`. The allocator keeps no accounting of its own.
  Created arenas report 0, so a caller that subtracts one arena's usage
  from the total (Redis does this for Lua) gets the whole. Everything else
  under `stats.` is 0.

A MIB is `{ table index, 0, ..., numeric component, ... }`: numeric
components (arena and bin indexes) sit where jemalloc puts them, so
callers that patch `mib[2]` before `mallctlbymib` work. Partial names are
not supported.

## Tests

`ports/jemalloc/test.c` runs in the check phase. It covers sizes and
alignments against `sallocx`, `nallocx` and `malloc_usable_size`, zeroing
and `rallocx` contents, the mallctl behaviour above and MIB round trips.
It also checks, in forked children, that overflowing into a neighbouring
object and using an object after `dallocx` or `sdallocx` trap.

## Consumers

Of the packages in the nixos-26.05 campaign that were blocked on
jemalloc:

- **Redis 8.8.2** builds against the shim with three changes that belong
  in a Redis port: `OPTIMIZATION=-O2` (no LTO under Fil-C), a
  `REDISMODULE_ATTR_COMMON` that is not `__attribute__((common))` (which
  crashes the compiler, see filc-findings.md), and not building the
  vendored jemalloc that Nixpkgs' system-jemalloc patch still lists as a
  dependency (`CC=cc` too, for its test modules). `INFO memory`,
  `MEMORY STATS`, `MEMORY PURGE`, `MEMORY MALLOC-STATS` and
  `MEMORY USAGE` work. 21 `unit/info` tests, and 141 from
  `unit/memefficiency`, `unit/keyspace`, `unit/type/hash` and
  `unit/type/list` run in parallel, pass before Redis itself traps: its reply buffers store pointers at unaligned
  offsets (`networking.c`), and with jemalloc it `madvise`s heap pages
  after fork (`dismissMemory`), which Fil-C refuses. Those need Redis
  patches; the tests do not reach the allocator shim's limits.
- **BIND 9.20** detects the shim (`Memory allocator: jemalloc`) and builds
  with `--disable-dnstap` (fstrm and protobuf are separate blockers). Its
  tests stop earlier, in liburcu's constructor, which calls the
  unsupported `membarrier` syscall.
- **knot-resolver** needs LuaJIT, and **lwan** fails to configure its
  native tools when cross-compiling, both unrelated to jemalloc.
  MariaDB, Ceph, Firefox and the rest were not tried.
