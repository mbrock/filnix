# PHP 8.5 application benchmark

Measures how much slower Fil-C PHP 8.5 is than native PHP 8.5 on real
applications, and where the time goes. It compares three builds of the same
release (8.5.12):

- `native`: Nixpkgs' PHP 8.5 at the Fil-C build's version, unstripped so
  profiles resolve static functions;
- `filc`: `pkgsFilc.php85`, the release Fil-C toolchain;
- `filc-staging`: `pkgsFilcStaging.php85`, the staging toolchain
  (`lib/filc-staging.json`), which optimization work builds on.

The applications are DokuWiki, MediaWiki (SQLite) and WordPress (SQLite
through the `sqlite-database-integration` drop-in, theme Twenty
Twenty-Five), all from Nixpkgs, plus `Zend/bench.php` for reference.

```sh
nix build .#php-bench
result/bin/php-bench setup        # fixtures in ~/.cache/php-bench (PHP_BENCH_STATE)
result/bin/php-bench run          # counters: native, filc, filc-staging
result/bin/php-bench profile      # perf record, broken down by category
result/bin/php-bench report DIR   # rerender summary.md from results.jsonl
```

`run` and `profile` take `--apps` (`dokuwiki mediawiki wordpress
bench.php`) and `--variants`. Besides the three builds there are allocator
levers (`filc-zendalloc`, `filc-untracked` and their `filc-staging-`
forms: Zend's allocator, or malloc without `memory_limit` tracking; both
weaken Fil-C's per-value bounds, see `docs/php.md`) and native ones
(`native-jit`, `native-nopcrejit`). `NAME=/path/to/bin/php` adds any other
build, such as one from a branch under test:

```sh
php-bench run --variants native filc-staging mine=$(nix build --print-out-paths .#...)/bin/php
```

An unwrapped PHP (`php-…/bin/php` rather than `php-with-extensions-…`)
loads no shared extensions; `NAME=/path/to/bin/php,/path/to/ini-dir` points
it at a wrapped build's `lib` directory with the same PHP release and
configuration, such as `$PHP_BENCH_FILC/lib`.

Results go to `~/.cache/php-bench/results/<timestamp>/` (or `--out`): `results.jsonl`
with every measurement, `summary.md`, and the servers' logs. `profile`
leaves `*.perf.data` for `perf report` alongside `profile.md`.

## What is measured

Each variant serves the application with PHP's built-in server
(`php -S`, one worker), opcache on with production settings and the JIT
off (`INI` in `bench.py`). After `--warmup` passes over the request mix,
every request is repeated `--reps` times. Responses must be 200 or 302,
and their sizes are reported so you can check that the variants rendered
the same pages.

The request mix is meant to resemble a wiki or blog's traffic: page views,
search, history, edit forms, feeds, category and archive listings, CSS and
JS bundles, and a REST/API call. The fixtures are deterministic: 30 wiki
articles with sections, lists, tables, links and (in MediaWiki) a template,
`#expr`, references and categories; 20 WordPress posts with comments,
categories and tags.

The primary metrics are user-mode cycles and instructions, read from
per-thread perf counters on every thread of the server process. Fil-C's
GC marker threads count too, so this is the CPU cost of the work, not just
the request thread's latency. Kernel cycles, task-clock and wall latency
are recorded alongside.

## Load

swa is shared with build-heavy jobs, so:

- variants alternate within each round, reversing order every round, and
  the report gives the median with the min–max of per-round ratios;
- instructions are independent of load. User cycles are not: with the
  machine fully busy, native MediaWiki took 2.5× the cycles it took on a
  quiet machine (SMT siblings and the shared L3). The report therefore
  also gives the ratio of each variant's fewest cycles across rounds
  ("best"), its least disturbed measurement. Wall time is reported only
  as a sanity check;
- every PHP process is pinned with `taskset` to `PHP_BENCH_CPUS`, by
  default `0-7,16-23`. On the 7950X3D those are the CCD with the 96 MB
  V-cache L3; the other CCD's 32 MB L3 would change cycle counts;
- each record holds the load average and the share of the machine that
  was busy during it.

## Profile categories

`profile` records cycles (user and kernel) on the warm server over
`--passes` passes of the mix and assigns each sample's symbol to a
category by DSO and name (`CATEGORIES` in `bench.py`; first match wins):
VM handlers and dispatch, Zend hash tables, strings, values and
refcounting, the cycle collector, other Zend runtime, zend_alloc and the
tracked allocator, PCRE (native's includes its JIT code), SQLite, libc,
Fil-C's allocator (libpas), FUGC, Fil-C memcpy/memmove/memset, other
Fil-C runtime, kernel memory work (faults, zeroing, mmap), other kernel
work (syscalls and I/O), and PHP functions and extensions.

Fil-C's inline bounds and capability checks execute inside the functions
that contain them, so they appear as a larger share for those functions
(and in the instruction ratio), not as a category of their own.
