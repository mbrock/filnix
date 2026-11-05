# PHP 8.5 application benchmark

Measures how much slower Fil-C PHP 8.5 is than native PHP 8.5 on real
applications, and where the time goes. It compares three builds of the same
release (8.5.12):

- `native`: Nixpkgs' PHP 8.5 at the Fil-C build's version, unstripped so
  profiles resolve static functions;
- `filc`: `pkgsFilc.php85`, the release Fil-C toolchain;
- `filc-staging`: `pkgsFilcStaging.php85`, the staging toolchain
  (`lib/filc-staging.json`), which optimization work builds on.

and, with opcache's JIT:

- `native-jit`: native PHP with `opcache.jit=tracing`;
- `filc-staging-jit`: `pkgsFilcStaging.php85-jit` with `opcache.jit=tracing`
  through Fil-C's in-process LLVM JIT (`docs/php.md`);
- `filc-staging-jit-c`: the same build through the C backend, which
  prints C and runs clang, with its persistent object cache;
- `-1235` and `-function` forms of `native-jit` and `filc-staging-jit` for
  the other JIT modes (`function` compiles each file's functions when it
  loads, so it suits only the scripts below).

The applications are DokuWiki, MediaWiki (SQLite) and WordPress (SQLite
through the `sqlite-database-integration` drop-in, theme Twenty
Twenty-Five), all from Nixpkgs, plus two scripts: `Zend/bench.php`, and
`micro.php` (recursive calls, integer and float loops, n-body, `usort`
with a closure, string building).

```sh
nix build .#php-bench
result/bin/php-bench setup        # fixtures in ~/.cache/php-bench (PHP_BENCH_STATE)
result/bin/php-bench run          # counters: native, filc, filc-staging
result/bin/php-bench profile      # perf record, broken down by category
result/bin/php-bench check        # compare responses and error logs across variants
result/bin/php-bench report DIR   # rerender summary.md from results.jsonl
```

`run`, `profile` and `check` take `--apps` (`dokuwiki mediawiki wordpress
bench.php micro.php`) and `--variants`. Besides the three builds there are allocator
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

## HTTP service latency and throughput

`service` answers a different question from the counter comparison: how
long does a complete HTTP response take, and how many requests does a
warmed FPM pool finish per second?

```sh
PHP_BENCH_CPUS=0-3 result/bin/php-bench service \
  --apps mediawiki wordpress \
  --variants native filc filc-staging-jit \
  --workers 2 --concurrency 4 --requests 120 --rounds 3 \
  --out /absolute/path/to/new-results
```

Choose CPUs for the actual host; the counter benchmark's default affinity
is specific to swa. `service` uses the same fixtures and PHP settings, but
starts **native nginx in front of a static PHP-FPM pool**, with no full-page
FastCGI cache. It needs no perf permissions. Run as an ordinary user. The
ports are the fixtures' fixed loopback ports, so the usual benchmark lock
applies. `PHP_BENCH_NGINX` can select another nginx executable.

Each variant/round starts fresh workers. Warm-up is three passes of the
mix per worker, ten for JIT variants, with `--workers` concurrent clients.
The first pass includes cold OPcache/JIT costs and is recorded separately;
it is not counted in steady-state latency. The LLVM shared object cache
stays off unless explicitly enabled in the environment. Do not enable it
without reviewing its security caveat in `docs/upstream-updates.md`.

After warm-up, every URL's body is compared with the first variant using
`check`'s volatility mask; a mismatch fails the run. Then three independent
loads each complete `--requests` requests:

- an ordinary article (`Article_1` / the fixture's chosen WordPress post),
  one client;
- the request mix, one client;
- the same mix, `--concurrency` clients with one request in flight each.

Latency includes HTTP request/response transfer over loopback, nginx,
FastCGI and PHP/database execution. It excludes browser asset fetching,
TLS and Internet latency. Throughput is completed requests divided by the
actual elapsed duration of that load, **not the reciprocal of a sum of
per-URL medians**. Four closed-loop clients demonstrate capacity at that
concurrency, not a sustainable arrival rate with a latency SLA.

`service-meta.json` records binaries, settings, fixture paths, hardware
and affinity. `service.jsonl` records each load's p50/p95 (nearest-rank p95),
all latency samples, elapsed time, throughput, warm-up passes, host busy
share and worker RSS. JIT log line counts before/after each load reveal
whether compilation continued during measurement. It refuses to append
to an existing results file. Subdirectories preserve configs, application
bodies and nginx/FPM/PHP/JIT logs. Variant order reverses each round.

Do not call a run quiet merely because the machine was expected to be idle.
Inspect host busy share and run-to-run spread. Worker RSS contains shared
pages and cannot be summed as unique memory. Small local SQLite fixtures
are not production MySQL sites; report the setup and do not extrapolate
these results to a VM or a plugin-heavy installation without measuring it.

## Counter measurements (`run`)

For `run`, each variant serves the application with PHP's built-in server
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

## JIT variants

A JIT compiles in the requests that make code hot, so JIT variants get
`--jit-warmup` passes (default 10) instead of `--warmup`, and every
warm-up pass is measured: wall time, cycles:u and, for the Fil-C JIT,
the functions and traces compiled and the seconds spent compiling (from
the JIT's log, `PHP_JIT_C_LOG`). The report's "JIT warm-up" table gives
the first pass, the steady state, the pass at which cycles settle within
10% of steady state, and the compiles; the main tables measure only the
steady state. Each round starts a fresh server, so each round compiles
again, except that the C backend's cache (`jit-c-cache` in the results
directory) persists across the rounds of one run: its first server
compiles, later ones load.

The scripts run twice per round. First once from the command line, cold:
with a tracing JIT their sections include the compiles, and their tables
add the compile count and seconds. Then from a fresh `php -S` server, three
requests to warm up and three measured: the "warm" tables give the median
of the measured sections (steady state), the first request's total, and
the compiles. `opcache.jit=function` compiles before the script runs, so
its cold and warm sections agree.

`check` serves the mix with each variant after its warm-up and compares
every response with the first variant's: status, size, and the body with
numbers, hashes and nonces masked. It also reports each variant's error
log and Fil-C or JIT messages in the server log, and exits non-zero on any
difference:

```sh
php-bench check --apps dokuwiki mediawiki wordpress \
  --variants filc-staging filc-staging-jit filc-staging-jit-1235 filc-staging-jit-c
```

Results with these variants, and what they mean, are in
[`the port notes`](../../docs/php-port-notes.md#the-jit-on-real-applications). In short,
in those earlier single-worker experiments all three applications rendered
the same pages with the JIT, CPU-bound scripts ran several times faster
than on Fil-C's interpreter, and page rendering gained at most 16% after
about two minutes of compiling per server. Those are not FPM pool startup
or concurrent throughput measurements.

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
  other work kept busy during it (its own CPU time subtracted).

For a consolidated cycle comparison in a quiet window:

```sh
php-bench quiet mine=/path/to/bin/php other=/path/to/bin/php
php-bench quiet native-jit filc-staging-jit filc-staging-jit-c --rounds 3
```

runs every application with native, filc, filc-staging and the extra
variants (named ones or `NAME=path`) for 10 rounds. Before each measurement it waits until other work
keeps at most `--max-busy` (default 15%) of the CPUs busy, gives up after
`--wait` minutes (default 30), and flags measurements that other work
disturbed anyway; the report counts them. `run --max-busy` does the same
for an ordinary run.

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
